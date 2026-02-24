theory DeMorgan imports Frege begin

locale alphabet_de_morgan =
  fixes a :: alphabet
  assumes conns_def: "conns a = {''top'', ''bot'', ''not'', ''or'', ''and''}"
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

function rule_to_taut :: "rule \<Rightarrow> formula" where
  "rule_to_taut \<lparr>prems = [], concl = c\<rparr> = c" |
  "rule_to_taut \<lparr>prems = f # fs, concl = c\<rparr> = 
    Conn ''or'' [Conn ''not'' [f], rule_to_taut \<lparr>prems = fs, concl = c\<rparr>]"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>r. length (prems r))") auto

(*
1. Either one of the premises is false, then the formula is true (\<not>f \<or> ...)
  - rule = \<lparr> prems = f_1 @ [f] @ f_2, concl = c\<rparr>
  - induction on the length of premises
    - either f # fs where f is false, or false in fs and length is smaller
2. Or all of the premises are true and by soundness the conclusion is also true (\<not>f \<or> ... \<or> q)
*)

lemma premise_false:
  fixes val :: "string \<Rightarrow> bool"
  and r :: "rule"
assumes "\<exists> f \<in> set (prems r). \<not> eval F val f"
  and "prems r \<noteq> []"
shows "eval F val (rule_to_taut r)"
  using assms
proof (induction "prems r" arbitrary: r)
  case Nil
  thus ?case by auto
next
  case (Cons p ps)
  show ?case
  proof (cases "\<not> eval F val p")
    case True
    have "r = \<lparr>prems = p # ps, concl = concl r\<rparr>" using Cons.hyps by auto
    hence "eval F val (rule_to_taut r) = eval F val (rule_to_taut \<lparr>prems = p # ps, concl = concl r\<rparr>)" by simp
    also have "... = eval F val (Conn ''or'' [Conn ''not'' [p], rule_to_taut \<lparr>prems = ps, concl = concl r\<rparr>])"
      by auto
    also have "... = (eval F val (Conn ''not'' [p]) \<or> eval F val (rule_to_taut \<lparr>prems = ps, concl = concl r\<rparr>))"
      using alphabet_de_morgan_axioms alphabet_de_morgan_def by auto
    also have "... = ((\<not> eval F val p) \<or> eval F val (rule_to_taut \<lparr>prems = ps, concl = concl r\<rparr>))"
      using alphabet_de_morgan_axioms alphabet_de_morgan_def by auto
    also have "... = True" using True by auto
    finally show ?thesis by auto
  next
    case False

  

lemma sound_rule_gives_tautology:
  assumes "r \<in> rules F"
shows "\<forall> val. eval F val (rule_to_taut r)"
  sorry

lemma rule_exists_proof:
  assumes "r \<in> rules F" and "f_rule = rule_to_taut r"
shows "\<exists> pr. valid_proof F pr \<and>  assumptions pr = {} \<and> thesis pr = f_rule"
proof -
  have "\<forall> val. (\<forall> f \<in> {}. eval F val f) \<longrightarrow> eval F val f_rule" 
    using sound_rule_gives_tautology assms by auto
  thus ?thesis using alphabet_de_morgan_axioms alphabet_de_morgan_def frege_system.impl_complete
    by auto
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