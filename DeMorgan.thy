theory DeMorgan imports Frege begin

function rule_to_taut :: "rule \<Rightarrow> formula" where
  "rule_to_taut \<lparr>prems = [], concl = c\<rparr> = c" |
  "rule_to_taut \<lparr>prems = f # fs, concl = c\<rparr> = 
    Conn ''or'' [Conn ''not'' [f], rule_to_taut \<lparr>prems = fs, concl = c\<rparr>]"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>r. length (prems r))") auto

locale de_morgan_frege =
  fixes F :: frege
  assumes alph: "a = alphabet F" 
  and conns_def: "conns a = {''top'', ''bot'', ''not'', ''or'', ''and''}"
  and conn_evals_def: "conn_evals a = (\<lambda> c. case c of
    ''top'' \<Rightarrow> (\<lambda>_. True)                \<comment> \<open>nullary: ignores input list\<close>
  | ''bot'' \<Rightarrow> (\<lambda>_. False)               \<comment> \<open>nullary\<close>
  | ''not'' \<Rightarrow> (\<lambda>args. case args of [x] \<Rightarrow> \<not> x | _ \<Rightarrow> undefined)
  | ''or''  \<Rightarrow> (\<lambda>args. case args of [x, y] \<Rightarrow> x \<or> y | _ \<Rightarrow> undefined)
  | ''and'' \<Rightarrow> (\<lambda>args. case args of [x, y] \<Rightarrow> x \<and> y | _ \<Rightarrow> undefined)
  | _ \<Rightarrow> undefined)"
  and "frege_system F" and "alphabet F = a"
begin

definition modus_ponens :: rule where
  "modus_ponens = \<lparr> 
    prems = [
      Atom ''P'', 
      Conn ''or'' [Conn ''not'' [Atom ''P''], Atom ''Q'']
    ], 
    concl = Atom ''Q'' 
  \<rparr>"

(*
1. Either one of the premises is false, then the formula is true (\<not>f \<or> ...)
2. Or all of the premises are true and by soundness the conclusion is also true (\<not>f \<or> ... \<or> q)
*)

lemma taut_unfold: "prems r = p # ps \<longrightarrow> eval a val (rule_to_taut r) = ((\<not> eval a val p) \<or> 
                         eval a val (rule_to_taut \<lparr>prems = ps, concl = concl r\<rparr>))"
proof
  assume pr: "prems r = p # ps"

  have r_eq: "r = \<lparr>prems = p # ps, concl = concl r\<rparr>"
    using pr by (cases r) auto

  show "eval a val (rule_to_taut r) =
   ((\<not> eval a val p) \<or> eval a val (rule_to_taut \<lparr>prems = ps, concl = concl r\<rparr>))"
  proof -
    have "eval a val (rule_to_taut r) = eval a val (rule_to_taut \<lparr>prems = p # ps, concl = concl r\<rparr>)"
      using r_eq by simp
    also have "... = eval a val (Conn ''or'' [Conn ''not'' [p],
                            rule_to_taut \<lparr>prems = ps, concl = concl r\<rparr>])"
      by auto
    also have "... = (eval a val (Conn ''not'' [p]) \<or> 
                      eval a val (rule_to_taut \<lparr>prems = ps, concl = concl r\<rparr>))"
      using de_morgan_frege_axioms de_morgan_frege_def by auto
    also have "... = ((\<not> eval a val p) \<or> 
                         eval a val (rule_to_taut \<lparr>prems = ps, concl = concl r\<rparr>))"
      using de_morgan_frege_axioms de_morgan_frege_def by auto
    finally show ?thesis .
  qed
qed

lemma premise_false:
  fixes val :: "string \<Rightarrow> bool"
  and r :: "rule"
assumes "\<exists> f \<in> set (prems r). \<not> eval a val f"
  and "prems r \<noteq> []"
shows "eval a val (rule_to_taut r)"
  using assms
proof (induction "prems r" arbitrary: r)
  case Nil
  thus ?case by auto
next
  case (Cons p ps)
  show ?case
  proof (cases "\<not> eval a val p")
    case True
    show ?thesis using Cons True taut_unfold[of r p ps a val] by auto
  next
    case False
    have "\<exists> g \<in> set (p # ps). \<not> eval a val g" using Cons assms(1) by auto
    hence g: "\<exists> g \<in> set ps. \<not> eval a val g" using False by auto
    hence "ps \<noteq> []" by auto
    hence "eval a val (rule_to_taut \<lparr>prems = ps, concl = concl r\<rparr>)" using g Cons by auto
    thus ?thesis using taut_unfold[of r p ps a val] Cons by auto
  qed
qed

lemma premises_true:
  fixes val :: "string \<Rightarrow> bool"
  and r :: "rule"
assumes "eval a val (concl r)"
shows "eval a val (rule_to_taut r)"
  using assms
proof (induction "prems r" arbitrary: r)
  case Nil
  have "r = \<lparr> prems = [], concl = concl r\<rparr>" using Nil by simp
  hence "eval a val (rule_to_taut r) = eval a val (rule_to_taut \<lparr>prems = [], concl = concl r\<rparr>)" 
    by simp
  also have  "... = eval a val (concl r)" by simp
  finally have "eval a val (rule_to_taut r) = eval a val (concl r)" by simp
  thus ?case using Nil.prems by simp
next
  case (Cons p ps)
  have eq: "eval a val (rule_to_taut r) = ((\<not> eval a val p) \<or> 
                         eval a val (rule_to_taut \<lparr>prems = ps, concl = concl r\<rparr>))"
    using Cons taut_unfold[of r p ps a val] by simp
  have "eval a val (rule_to_taut \<lparr>prems = ps, concl = concl r\<rparr>)" using Cons by simp
  thus ?case using eq by simp
qed


lemma sound_rule_gives_tautology:
  assumes "r \<in> rules F"
shows "\<forall> val. eval a val (rule_to_taut r)"
proof
  fix val
  show "eval a val (rule_to_taut r)"
  proof (cases "\<exists> f \<in> set (prems r). \<not> eval a val f")
    case True
    have "prems r \<noteq> []" using True by auto
    thus ?thesis using True premise_false by simp
  next
    case False
    have all_prems_true: "\<forall> f \<in> set (prems r). eval a val f" using False by simp
    have "sound_rule F r" 
      using assms de_morgan_frege_def de_morgan_frege_axioms frege_system.sound by auto
    hence "eval a val (concl r)" using all_prems_true sound_rule_def[of F r] alph[of a] by simp 
    thus ?thesis using premises_true by simp
  qed
qed

end

locale de_morgan_sim =
  fixes F :: frege and F' :: frege
  assumes dm1: "de_morgan_frege F" and dm2: "de_morgan_frege F'"
begin

(*
This theorem says: take a rule from system F' which has the de_morgan alphabet, flatten it
to a chain of implications, and now it has a proof in a system F which only has modus ponens
as a rule, but uses the same de_morgan alphabet
*)

lemma rule_exists_proof:
  assumes "r \<in> rules F'" and "f_rule = rule_to_taut r"
shows "\<exists> pr. valid_proof F pr \<and>  assumptions pr = {} \<and> thesis pr = f_rule"
proof -
  have "alphabet F = alphabet F'" 
    using de_morgan_sim_def de_morgan_sim_axioms de_morgan_frege.alph by simp
  hence "\<forall> val. (\<forall> f \<in> {}. eval (alphabet F) val f) \<longrightarrow> eval (alphabet F) val f_rule" 
    using de_morgan_frege.sound_rule_gives_tautology[of F' r] assms dm2 by simp
  thus ?thesis using de_morgan_frege_def dm1 frege_system.impl_complete by simp
qed


lemma simulation_de_morgan_right:
  assumes as_frege: "frege_system F1 \<and> frege_system F2"
  and as_de_morgan: "alphabet F1 = a \<and> alphabet F2 = a"
  and as_modus: "rules F1 = {modus_ponens}"
  shows "simulates F1 F2"
  sorry

lemma simulation_de_morgan_left:
  assumes as_frege: "frege_system F1 \<and> frege_system F2"
  and as_de_morgan: "alphabet F1 = a \<and> alphabet F2 = a"
  and as_modus: "rules F1 = {modus_ponens}"
  shows "simulates F2 F1"
  sorry

end
end