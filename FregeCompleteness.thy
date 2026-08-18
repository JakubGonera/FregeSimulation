theory FregeCompleteness
  imports
    "Propositional_Proof_Systems.Sema"
    Frege
begin

text \<open>Bridge to the AFP entry \<^session>\<open>Propositional_Proof_Systems\<close>.  Reckhow's theorem
  ASSUMES two Frege systems rather than constructing one, so nothing here needs to build a
  Frege system: proving that a functionally complete alphabet admits one is left to whoever
  instantiates \<^locale>\<open>frege_system\<close>.  What survives is the small amount of machinery
  \<open>SystemTranslation\<close> actually consumes --- the truth-table encoding of a connective as an
  AFP formula, and four substitution/congruence facts on the Frege side.\<close>

subsection \<open>Big conjunction/disjunction over AFP formulas\<close>

fun big_or :: "'a Formulas.formula list \<Rightarrow> 'a Formulas.formula" where
  "big_or [] = Formulas.Bot"
| "big_or (F # Fs) = Formulas.Or F (big_or Fs)"

fun big_and :: "'a Formulas.formula list \<Rightarrow> 'a Formulas.formula" where
  "big_and [] = Formulas.Not Formulas.Bot"
| "big_and (F # Fs) = Formulas.And F (big_and Fs)"

lemma big_or_sema:
  "formula_semantics A (big_or Fs) \<longleftrightarrow> (\<exists>F\<in>set Fs. formula_semantics A F)"
  by (induction Fs) auto

lemma big_and_sema:
  "formula_semantics A (big_and Fs) \<longleftrightarrow> (\<forall>F\<in>set Fs. formula_semantics A F)"
  by (induction Fs) auto

subsection \<open>Truth table of a connective as an AFP formula\<close>

definition lit :: "bool \<Rightarrow> 'a Formulas.formula \<Rightarrow> 'a Formulas.formula" where
  "lit b F = (if b then F else Formulas.Not F)"

lemma lit_sema: "formula_semantics A (lit b F) \<longleftrightarrow> (b = formula_semantics A F)"
  by (auto simp: lit_def)

definition mk_conn :: "(bool list \<Rightarrow> bool) \<Rightarrow> 'a Formulas.formula list \<Rightarrow> 'a Formulas.formula" where
  "mk_conn g args =
     big_or (map (\<lambda>v. big_and (map (\<lambda>i. lit (v ! i) (args ! i)) [0..<length args]))
                 (filter g (List.n_lists (length args) [True, False])))"

lemma mk_conn_sema:
  "formula_semantics A (mk_conn g args) \<longleftrightarrow> g (map (formula_semantics A) args)"
proof -
  let ?n = "length args"
  let ?w = "map (formula_semantics A) args"
  have band: "formula_semantics A (big_and (map (\<lambda>i. lit (v ! i) (args ! i)) [0..<?n])) \<longleftrightarrow> v = ?w"
    if "v \<in> set (List.n_lists ?n [True, False])" for v
  proof -
    from that have lv: "length v = ?n" by (simp add: set_n_lists)
    have "formula_semantics A (big_and (map (\<lambda>i. lit (v ! i) (args ! i)) [0..<?n]))
          \<longleftrightarrow> (\<forall>i<?n. v ! i = formula_semantics A (args ! i))"
      by (auto simp: big_and_sema lit_sema)
    also have "\<dots> \<longleftrightarrow> v = ?w" using lv by (auto intro!: nth_equalityI)
    finally show ?thesis .
  qed
  have "formula_semantics A (mk_conn g args)
        \<longleftrightarrow> (\<exists>v \<in> set (filter g (List.n_lists ?n [True, False])).
              formula_semantics A (big_and (map (\<lambda>i. lit (v ! i) (args ! i)) [0..<?n])))"
    unfolding mk_conn_def by (simp add: big_or_sema)
  also have "\<dots> \<longleftrightarrow> (\<exists>v \<in> set (List.n_lists ?n [True, False]). g v \<and> v = ?w)"
    using band by auto
  also have "\<dots> \<longleftrightarrow> g ?w"
    by (auto simp: set_n_lists)
  finally show ?thesis .
qed

subsection \<open>Substitution semantics (Frege side)\<close>

lemma sub_formula_eval:
  "eval alph val (sub_formula s g) = eval alph (\<lambda>a. eval alph val (s a)) g"
proof (induction g)
  case (Atom a)
  show ?case by simp
next
  case (Conn c gs)
  have m: "map (eval alph val) (map (sub_formula s) gs)
           = map (eval alph (\<lambda>a. eval alph val (s a))) gs"
    by (simp add: Conn.IH)
  have "eval alph val (sub_formula s (Conn c gs))
        = conn_evals alph c (map (eval alph val) (map (sub_formula s) gs))"
    by simp
  also have "\<dots> = conn_evals alph c (map (eval alph (\<lambda>a. eval alph val (s a))) gs)"
    by (simp only: m)
  also have "\<dots> = eval alph (\<lambda>a. eval alph val (s a)) (Conn c gs)" by simp
  finally show ?case .
qed

lemma sub_formula_cong:
  assumes "\<And>v. v \<in> var_set_form f \<Longrightarrow> s1 v = s2 v"
  shows "sub_formula s1 f = sub_formula s2 f"
  using assms by (induction f) auto

lemma var_set_sub:
  "var_set_form (sub_formula s f) = (\<Union>a\<in>var_set_form f. var_set_form (s a))"
  by (induction f) auto


subsection \<open>Evaluation depends only on the variables that occur\<close>

lemma eval_cong:
  assumes "\<And>v. v \<in> var_set_form f \<Longrightarrow> v1 v = v2 v"
  shows "eval al v1 f = eval al v2 f"
  using assms
proof (induction f)
  case (Atom a)
  thus ?case by simp
next
  case (Conn c fs)
  have m: "map (eval al v1) fs = map (eval al v2) fs"
  proof (rule map_cong[OF refl])
    fix x assume x: "x \<in> set fs"
    show "eval al v1 x = eval al v2 x"
    proof (rule Conn.IH[OF x])
      fix v assume "v \<in> var_set_form x"
      thus "v1 v = v2 v" using Conn.prems x by auto
    qed
  qed
  show ?case by (simp only: eval.simps m)
qed

end
