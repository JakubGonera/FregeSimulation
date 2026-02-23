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


fun (sequential) disj_to_set :: "formula \<Rightarrow> formula set" where
  "disj_to_set f = (
    case f of 
      Conn ''or'' [g, h] \<Rightarrow> disj_to_set g \<union> disj_to_set h
    | _ \<Rightarrow> {f}
  )"

lemma disj_true_in_set:
  assumes "frege_system F" and "alphabet F = a"
  shows "f \<in> disj_to_set g \<Longrightarrow> eval F val f \<Longrightarrow> eval F val g"
  using assms
proof (induct g)
  case (Atom x)
  then show ?case by simp
next
  case (Conn c fs)
  then show ?case
  proof (cases "c =''or'' \<and> (\<exists>g1 g2. fs = [g1, g2])")
    case True
    then obtain g1 g2 where g_def: "Conn c fs = Conn ''or'' [g1, g2]" by auto
    have IH1: "f \<in> disj_to_set g1 \<Longrightarrow> eval F val f \<Longrightarrow> eval F val g1" using Conn.hyps assms g_def
      by simp
    have IH2: "f \<in> disj_to_set g2 \<Longrightarrow> eval F val f \<Longrightarrow> eval F val g2" using Conn.hyps assms g_def
      by simp

    from Conn.prems g_def have "f \<in> disj_to_set g1 \<union> disj_to_set g2" by simp
    then consider "f \<in> disj_to_set g1" | "f \<in> disj_to_set g2" by blast
    then show ?thesis
    proof cases
      case 1
      with IH1 Conn.prems(2) have "eval F val g1" by simp
      thus ?thesis using g_def \<open>alphabet F = a\<close> conn_evals_def by (simp add: alphabet_def)
    next
      case 2
      with IH2 Conn.prems(2) have "eval F val g2" by simp
      thus ?thesis using g_def \<open>alphabet F = a\<close> conn_evals_def by (simp add: alphabet_def)
    qed
  next
    case False
    have "disj_to_set (Conn c fs) = {Conn c fs}"
    

    (* Now finish: if f \<in> {Conn c fs}, then f = Conn c fs *)
    with Conn.prems(1) have "f = Conn c fs" by simp
    then show ?thesis using Conn.prems(2) by simp


lemma sound_rule_tautology:
  assumes "frege_system F" and "alphabet F = a"
  and "r \<in> rules F" and "flat = rule_to_taut r"
  shows "\<exists> pr. thesis pr = flat \<and> valid_proof F pr"
proof -
  (* Need to show: this formula is true for each valuation (soundness)
     and from impl_compl there exists a proof
  *)
  fix val :: "string \<Rightarrow> bool"

  consider (case1) "\<exists> p \<in> set (prems r). \<not> eval F val p" | (case2) "\<forall> p \<in> set (prems r). eval F val p"
    by blast

  then have "eval F val flat"
  proof cases
    case case1
    then obtain p where "p \<in> set (prems r)" and p_false: "\<not> eval F val p" by blast
    then have "eval F val (Conn ''not'' [p]) = (conn_evals (a) ''not'') [eval F val p]"
      using assms by (simp)
    also have "... = (case [eval F val p] of [x] \<Rightarrow> \<not> x | _ \<Rightarrow> undefined)"
      by (simp add: conn_evals_def)
    also have "... = (\<not> eval F val p)" by simp
    finally have "eval F val (Conn ''not'' [p])"
      using p_false by simp
    
  

  (*have "\<forall> val. eval F val (flat)"
  proof
    from assms have "sound_rule F r" using frege_system.sound by blast
    hence *)
      



lemma simulation_de_morgan_right:
  assumes as_frege: "frege_system F1 \<and> frege_system F2"
  and as_de_morgan: "alphabet F1 = a \<and> alphabet F2 = a"
  and as_modus: "rules F1 = {modus_ponens}"
  shows "simulates F1 F2"
proof
  sorry






lemma simulation_de_morgan_left:
  assumes as_frege: "frege_system F1 \<and> frege_system F2"
  and as_de_morgan: "alphabet F1 = a \<and> alphabet F2 = a"
  and as_modus: "rules F1 = {modus_ponens}"
  shows "simulates F2 F1"
proof
  sorry

end

end