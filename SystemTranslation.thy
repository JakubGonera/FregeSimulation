theory SystemTranslation
  imports Section7
begin

section \<open>Translation between Frege systems over different alphabets\<close>

text \<open>The third leg of Reckhow's construction: a proof whose lines have bounded
      depth in one Frege system is translated into a valid proof in any other
      Frege system, by replacing every connective with a fixed equivalent
      template formula and simulating every rule application through one
      constant-size proof obtained from implicational completeness.  The size
      of the result is polynomial in the source proof once the depth bound is
      logarithmic — which is exactly what @{thm [source] frege_closure.proof_balancing}
      provides.\<close>

subsection \<open>Generic helpers\<close>

lemma finite_var_set_form: "finite (var_set_form f)"
  by (induction f) auto

lemma finite_var_set_rule: "finite (var_set_rule r)"
  by (simp add: finite_var_set_form)

lemma sub_formula_atom_id: "sub_formula Atom f = f"
  by (induction f) (simp_all add: map_idI)

lemma card_var_set_form_le_len: "card (var_set_form f) \<le> len_formula f"
proof (induction f)
  case (Atom v)
  show ?case by simp
next
  case (Conn c fs)
  have "card (\<Union> g \<in> set fs. var_set_form g) \<le> sum_list (map len_formula fs)"
    using Conn.IH
  proof (induction fs)
    case Nil
    show ?case by simp
  next
    case (Cons a as)
    have "card (\<Union> g \<in> set (a # as). var_set_form g)
          = card (var_set_form a \<union> (\<Union> g \<in> set as. var_set_form g))"
      by simp
    also have "\<dots> \<le> card (var_set_form a) + card (\<Union> g \<in> set as. var_set_form g)"
      by (rule card_Un_le)
    also have "\<dots> \<le> len_formula a + sum_list (map len_formula as)"
      using Cons.prems Cons.IH by (intro add_mono) auto
    finally show ?case by simp
  qed
  thus ?case by simp
qed

lemma depth_formula_arg_le:
  assumes "g \<in> set args"
  shows "depth_formula g \<le> depth_formula (Conn c args)"
proof -
  have ne: "args \<noteq> []" using assms by auto
  have "depth_formula g \<le> Max (set (map depth_formula args))"
    using assms by (intro Max_ge) auto
  moreover have "depth_formula (Conn c args) = 1 + Max (set (map depth_formula args))"
    using ne by simp
  ultimately show ?thesis by linarith
qed

lemma len_formula_arg_le:
  assumes "g \<in> set args"
  shows "len_formula g \<le> len_formula (Conn c args)"
proof -
  have "len_formula g \<le> sum_list (map len_formula args)"
    using assms by (intro member_le_sum_list) auto
  thus ?thesis by simp
qed

lemma step_length_le_proof:
  assumes "f \<in> set (steps pr)"
  shows "len_formula f \<le> len_proof pr"
proof -
  have "len_formula f \<in> set (map len_formula (steps pr))"
    using assms by simp
  hence "len_formula f \<le> sum_list (map len_formula (steps pr))"
    by (intro member_le_sum_list) simp_all
  thus ?thesis by simp
qed

lemma steps_count_le_proof_length:
  shows "length (steps pr) \<le> len_proof pr"
proof -
  have "\<forall> f \<in> set (steps pr). (1 :: nat) \<le> len_formula f"
    using len_formula_positive by blast
  hence "sum_list (map (\<lambda>_. 1 :: nat) (steps pr)) \<le> sum_list (map len_formula (steps pr))"
    by (rule sum_list_pointwise_le)
  thus ?thesis by (simp add: sum_list_const_nat)
qed

lemma substitution_value_length:
  assumes "v \<in> var_set_form f"
  shows "len_formula (s v) \<le> len_formula (sub_formula s f)"
  using assms
proof (induction f)
  case (Atom a)
  thus ?case by simp
next
  case (Conn c fs)
  then obtain g where g_in: "g \<in> set fs" and v_in: "v \<in> var_set_form g" by auto
  have IH_g: "len_formula (s v) \<le> len_formula (sub_formula s g)"
    using Conn.IH g_in v_in by blast
  have "len_formula (sub_formula s g) \<in> set (map (\<lambda>h. len_formula (sub_formula s h)) fs)"
    using g_in by auto
  hence "len_formula (sub_formula s g) \<le> sum_list (map (\<lambda>h. len_formula (sub_formula s h)) fs)"
    by (intro member_le_sum_list) simp_all
  moreover have "len_formula (sub_formula s (Conn c fs))
               = 1 + sum_list (map (\<lambda>h. len_formula (sub_formula s h)) fs)"
    by (simp add: comp_def)
  ultimately show ?case using IH_g by linarith
qed

lemma substitution_value_depth:
  assumes "v \<in> var_set_form f"
  shows "depth_formula (s v) \<le> depth_formula (sub_formula s f)"
  using assms
proof (induction f)
  case (Atom a)
  thus ?case by simp
next
  case (Conn c fs)
  then obtain g where g_in: "g \<in> set fs" and v_in: "v \<in> var_set_form g" by auto
  have IH_g: "depth_formula (s v) \<le> depth_formula (sub_formula s g)"
    using Conn.IH g_in v_in by blast
  have ne: "fs \<noteq> []" using g_in by auto
  have "depth_formula (sub_formula s g) \<in> set (map (\<lambda>h. depth_formula (sub_formula s h)) fs)"
    using g_in by auto
  hence "depth_formula (sub_formula s g)
       \<le> Max (set (map (\<lambda>h. depth_formula (sub_formula s h)) fs))"
    by (intro Max_ge) simp
  moreover have "depth_formula (sub_formula s (Conn c fs))
               = 1 + Max (set (map (\<lambda>h. depth_formula (sub_formula s h)) fs))"
    using ne by (simp add: comp_def)
  ultimately show ?case using IH_g by linarith
qed

lemma substitution_value_well_formed:
  assumes "v \<in> var_set_form f"
    and "formula_well_formed alph (sub_formula s f)"
  shows "formula_well_formed alph (s v)"
  using assms
proof (induction f)
  case (Atom a)
  thus ?case by simp
next
  case (Conn c fs)
  then obtain g where g_in: "g \<in> set fs" and v_in: "v \<in> var_set_form g" by auto
  have "formula_well_formed alph (sub_formula s g)"
    using Conn.prems(2) g_in by auto
  thus ?case using Conn.IH g_in v_in by blast
qed

lemma instance_well_formed:
  assumes "formula_well_formed alph (sub_formula s f)"
  shows "formula_well_formed alph f"
  using assms
proof (induction f)
  case (Atom a)
  thus ?case by simp
next
  case (Conn c fs)
  have "length (map (sub_formula s) fs) = arity alph c"
    using Conn.prems by simp
  hence "length fs = arity alph c" by simp
  moreover have "\<forall> g \<in> set fs. formula_well_formed alph g"
    using Conn.IH Conn.prems by auto
  ultimately show ?case by simp
qed

lemma sub_rule_cong:
  assumes "\<And>v. v \<in> var_set_rule r \<Longrightarrow> s1 v = s2 v"
  shows "sub_rule s1 r = sub_rule s2 r"
proof -
  have prems_eq: "map (sub_formula s1) (prems r) = map (sub_formula s2) (prems r)"
  proof (intro map_cong refl)
    fix p assume p_in: "p \<in> set (prems r)"
    have "\<And>v. v \<in> var_set_form p \<Longrightarrow> s1 v = s2 v"
      using assms p_in by fastforce
    thus "sub_formula s1 p = sub_formula s2 p" by (rule sub_formula_cong)
  qed
  have concl_eq: "sub_formula s1 (concl r) = sub_formula s2 (concl r)"
    by (intro sub_formula_cong assms) fastforce
  show ?thesis using prems_eq concl_eq by simp
qed

subsection \<open>Indexed rule application and its canonical choice\<close>

definition derived_with :: "nat \<Rightarrow> 'c frege_proof \<Rightarrow> 'c rule \<Rightarrow> (string \<Rightarrow> 'c formula) \<Rightarrow> bool" where
  "derived_with i pr r s \<longleftrightarrow>
     i < length (steps pr)
     \<and> concl (sub_rule s r) = steps pr ! i
     \<and> (\<forall> p \<in> set (prems (sub_rule s r)). \<exists> q \<in> set (take i (steps pr)). p = q)"

lemma derived_imp_derived_with:
  assumes "derived rs (take i (steps pr)) (steps pr ! i)"
    and "i < length (steps pr)"
  shows "\<exists> r s. r \<in> rs \<and> derived_with i pr r s"
  using assms unfolding derived_def derived_with_def by (auto simp add: Let_def)

lemma derived_with_imp_derived:
  assumes "r \<in> rs" and "derived_with i pr r s"
  shows "derived rs (take i (steps pr)) (steps pr ! i)"
  using assms unfolding derived_def derived_with_def by (auto simp add: Let_def)

lemma restricted_witness:
  assumes "derived_with i pr r s"
  shows "\<exists> s'. derived_with i pr r s' \<and> rule_restricted_sub r s'"
proof -
  define s' where "s' = (\<lambda>v. if v \<in> var_set_rule r then s v else Atom v)"
  have "sub_rule s' r = sub_rule s r"
    by (intro sub_rule_cong) (simp add: s'_def)
  hence "derived_with i pr r s'"
    using assms unfolding derived_with_def by simp
  moreover have "rule_restricted_sub r s'"
    unfolding rule_restricted_sub_def s'_def by simp
  ultimately show ?thesis by blast
qed

definition choose_rule_substitution ::
  "('c rule) set \<Rightarrow> nat \<Rightarrow> 'c frege_proof \<Rightarrow> ('c rule \<times> (string \<Rightarrow> 'c formula))" where
  "choose_rule_substitution rs i pr =
     (SOME (r, s). r \<in> rs \<and> derived_with i pr r s \<and> rule_restricted_sub r s)"

lemma choose_rule_substitution_spec:
  assumes "\<exists> r s. r \<in> rs \<and> derived_with i pr r s"
  shows "fst (choose_rule_substitution rs i pr) \<in> rs
       \<and> derived_with i pr (fst (choose_rule_substitution rs i pr))
                           (snd (choose_rule_substitution rs i pr))
       \<and> rule_restricted_sub (fst (choose_rule_substitution rs i pr))
                             (snd (choose_rule_substitution rs i pr))"
proof -
  obtain r s where r_in: "r \<in> rs" and dw: "derived_with i pr r s"
    using assms by blast
  obtain s' where "derived_with i pr r s'" and "rule_restricted_sub r s'"
    using restricted_witness[OF dw] by blast
  hence ex: "\<exists> p. (\<lambda>(r, s). r \<in> rs \<and> derived_with i pr r s \<and> rule_restricted_sub r s) p"
    using r_in by (intro exI[of _ "(r, s')"]) simp
  have "(\<lambda>(r, s). r \<in> rs \<and> derived_with i pr r s \<and> rule_restricted_sub r s)
          (choose_rule_substitution rs i pr)"
    unfolding choose_rule_substitution_def by (rule someI_ex[OF ex])
  thus ?thesis by (simp add: case_prod_beta)
qed

subsection \<open>Marker variables and the marker substitution\<close>

definition marker_variables :: "nat \<Rightarrow> string list" where
  "marker_variables n = (SOME vs. length vs = n \<and> distinct vs)"

lemma marker_variables_spec:
  "length (marker_variables n) = n \<and> distinct (marker_variables n)"
proof -
  have "\<exists> vs :: string list. length vs = n \<and> distinct vs"
    using fresh_distinct_atoms_exist_general[where avoid = "{}"] by auto
  thus ?thesis
    unfolding marker_variables_def by (rule someI_ex)
qed

definition marker_substitution :: "string list \<Rightarrow> ('c formula) list \<Rightarrow> (string \<Rightarrow> 'c formula)" where
  "marker_substitution names arguments =
     (\<lambda>v. case map_of (zip names arguments) v of Some g \<Rightarrow> g | None \<Rightarrow> Atom v)"

lemma marker_substitution_nth:
  assumes "distinct names" and "length arguments = length names" and "k < length names"
  shows "marker_substitution names arguments (names ! k) = arguments ! k"
  unfolding marker_substitution_def
  using map_of_zip_nth_lookup[OF assms(1) assms(2)[symmetric] assms(3)] by simp

lemma marker_substitution_outside:
  assumes "v \<notin> set names"
  shows "marker_substitution names arguments v = Atom v"
proof -
  have "map_of (zip names arguments) v = None"
    by (rule map_of_zip_None_lookup[OF assms])
  thus ?thesis unfolding marker_substitution_def by simp
qed

lemma marker_substitution_range:
  "marker_substitution names arguments v \<in> set arguments \<union> {Atom v}"
proof (cases "map_of (zip names arguments) v")
  case None
  thus ?thesis unfolding marker_substitution_def by simp
next
  case (Some g)
  have "(v, g) \<in> set (zip names arguments)"
    by (rule map_of_SomeD[OF Some])
  hence "g \<in> set arguments"
    by (rule set_zip_rightD)
  thus ?thesis unfolding marker_substitution_def using Some by simp
qed

subsection \<open>The truth table of a boolean function as a De Morgan formula\<close>

fun de_morgan_of_afp :: "string Formulas.formula \<Rightarrow> dm_conn formula" where
  "de_morgan_of_afp (Formulas.Atom a) = Atom a"
| "de_morgan_of_afp Formulas.Bot = Conn Bot []"
| "de_morgan_of_afp (Formulas.Not G) = Conn Not [de_morgan_of_afp G]"
| "de_morgan_of_afp (Formulas.And G H) = Conn And [de_morgan_of_afp G, de_morgan_of_afp H]"
| "de_morgan_of_afp (Formulas.Or G H) = Conn Or [de_morgan_of_afp G, de_morgan_of_afp H]"
| "de_morgan_of_afp (Formulas.Imp G H) = Conn Or [Conn Not [de_morgan_of_afp G], de_morgan_of_afp H]"

lemma de_morgan_of_afp_eval:
  "eval dm_alphabet val (de_morgan_of_afp G) = formula_semantics val G"
  by (induction G) (simp_all add: dm_alphabet_def)

lemma de_morgan_of_afp_var_set:
  "var_set_form (de_morgan_of_afp G) = atoms G"
  by (induction G) auto

definition truth_table_formula :: "(bool list \<Rightarrow> bool) \<Rightarrow> string list \<Rightarrow> dm_conn formula" where
  "truth_table_formula g names = de_morgan_of_afp (mk_conn g (map Formulas.Atom names))"

lemma truth_table_formula_eval:
  "eval dm_alphabet val (truth_table_formula g names) = g (map val names)"
proof -
  have "eval dm_alphabet val (truth_table_formula g names)
      = formula_semantics val (mk_conn g (map Formulas.Atom names))"
    unfolding truth_table_formula_def by (rule de_morgan_of_afp_eval)
  also have "\<dots> = g (map (formula_semantics val) (map Formulas.Atom names))"
    by (rule mk_conn_sema)
  also have "\<dots> = g (map val names)"
    by (simp add: comp_def)
  finally show ?thesis .
qed

lemma atoms_lit: "atoms (lit b G) = atoms G"
  by (simp add: lit_def)

lemma atoms_big_or: "atoms (big_or Gs) = \<Union> (atoms ` set Gs)"
  by (induction Gs) auto

lemma atoms_big_and: "atoms (big_and Gs) = \<Union> (atoms ` set Gs)"
  by (induction Gs) auto

lemma atoms_mk_conn:
  "atoms (mk_conn g args) \<subseteq> \<Union> (atoms ` set args)"
proof
  fix x assume "x \<in> atoms (mk_conn g args)"
  then obtain v where
    x_in: "x \<in> atoms (big_and (map (\<lambda>i. lit (v ! i) (args ! i)) [0..<length args]))"
    unfolding mk_conn_def by (auto simp add: atoms_big_or)
  from x_in obtain i where i_in: "i \<in> set [0..<length args]"
    and x_lit: "x \<in> atoms (lit (v ! i) (args ! i))"
    by (auto simp add: atoms_big_and)
  have "x \<in> atoms (args ! i)" using x_lit by (simp add: atoms_lit)
  moreover have "args ! i \<in> set args" using i_in by (auto intro: nth_mem)
  ultimately show "x \<in> \<Union> (atoms ` set args)" by auto
qed

lemma truth_table_formula_var_set:
  "var_set_form (truth_table_formula g names) \<subseteq> set names"
proof -
  have "var_set_form (truth_table_formula g names)
      = atoms (mk_conn g (map Formulas.Atom names))"
    unfolding truth_table_formula_def by (rule de_morgan_of_afp_var_set)
  also have "\<dots> \<subseteq> \<Union> (atoms ` set (map Formulas.Atom names))"
    by (rule atoms_mk_conn)
  also have "\<dots> \<subseteq> set names" by auto
  finally show ?thesis .
qed


subsection \<open>Pruning a functional-completeness witness to a well-formed template\<close>

lemma connective_template_pruned:
  fixes alph :: "'c alphabet" and dmf :: "dm_conn formula" and f' :: "'c formula"
  assumes equivalent: "formulas_equiv dmf dm_alphabet f' alph"
      and well_formed: "formula_well_formed alph f'"
      and top_arity: "arity alph topc = 0"
      and top_true: "\<And>val. eval alph val (Conn topc []) = True"
      and vars_dmf: "var_set_form dmf \<subseteq> V"
  shows "\<exists> tmpl. formula_well_formed alph tmpl \<and> var_set_form tmpl \<subseteq> V
              \<and> (\<forall> val. eval alph val tmpl = eval dm_alphabet val dmf)"
proof -
  define prune where "prune = (\<lambda>v. if v \<in> V then Atom v else Conn topc [] :: 'c formula)"
  define tmpl where "tmpl = sub_formula prune f'"
  have prune_wf: "\<And>v. formula_well_formed alph (prune v)"
    unfolding prune_def using top_arity by simp
  have tmpl_wf: "formula_well_formed alph tmpl"
    unfolding tmpl_def using well_formed prune_wf by (rule sub_formula_well_formed)
  have tmpl_vars: "var_set_form tmpl \<subseteq> V"
    unfolding tmpl_def var_set_sub prune_def by (auto split: if_splits)
  have tmpl_eval: "eval alph val tmpl = eval dm_alphabet val dmf" for val
  proof -
    have "eval alph val tmpl = eval alph (\<lambda>a. eval alph val (prune a)) f'"
      unfolding tmpl_def by (rule sub_formula_eval)
    also have "\<dots> = eval dm_alphabet (\<lambda>a. eval alph val (prune a)) dmf"
      using equivalent unfolding formulas_equiv_def by simp
    also have "\<dots> = eval dm_alphabet val dmf"
    proof (rule eval_cong)
      fix v assume "v \<in> var_set_form dmf"
      hence "v \<in> V" using vars_dmf by blast
      thus "eval alph val (prune v) = val v" unfolding prune_def by simp
    qed
    finally show ?thesis .
  qed
  from tmpl_wf tmpl_vars tmpl_eval show ?thesis by blast
qed

subsection \<open>A pair of Frege systems\<close>

locale frege_pair =
  fixes Fone :: "'c1 frege" and Ftwo :: "'c2 frege"
  assumes frege_system_one: "frege_system Fone"
      and frege_system_two: "frege_system Ftwo"

sublocale frege_pair \<subseteq> one: frege_system Fone
  by (rule frege_system_one)

sublocale frege_pair \<subseteq> two: frege_system Ftwo
  by (rule frege_system_two)

context frege_pair
begin

subsection \<open>Extracting the well-formed rules\<close>

definition well_formed_rules :: "('c1 rule) set" where
  "well_formed_rules = {r \<in> rules Fone.
      (\<forall> p \<in> set (prems r). formula_well_formed (alphabet Fone) p)
      \<and> formula_well_formed (alphabet Fone) (concl r)}"

lemma well_formed_rules_subset: "well_formed_rules \<subseteq> rules Fone"
  unfolding well_formed_rules_def by blast

lemma well_formed_rules_finite: "finite well_formed_rules"
  by (rule finite_subset[OF well_formed_rules_subset one.finite])

lemma valid_proof_well_formed_rules:
  assumes valid: "valid_proof Fone pr"
      and wf_steps: "\<forall> st \<in> set (steps pr). formula_well_formed (alphabet Fone) st"
      and i_lt: "i < length (steps pr)"
      and not_assumption: "steps pr ! i \<notin> assumptions pr"
    shows "\<exists> r s. r \<in> well_formed_rules \<and> derived_with i pr r s"
proof -
  have "derived (rules Fone) (take i (steps pr)) (steps pr ! i)"
    using valid i_lt not_assumption unfolding valid_proof_def by blast
  then obtain r s where r_in: "r \<in> rules Fone" and dw: "derived_with i pr r s"
    using derived_imp_derived_with i_lt by blast
  have concl_inst_wf: "formula_well_formed (alphabet Fone) (sub_formula s (concl r))"
  proof -
    have "concl (sub_rule s r) = steps pr ! i"
      using dw unfolding derived_with_def by blast
    moreover have "formula_well_formed (alphabet Fone) (steps pr ! i)"
      using wf_steps i_lt by simp
    ultimately show ?thesis by simp
  qed
  hence concl_wf: "formula_well_formed (alphabet Fone) (concl r)"
    by (rule instance_well_formed)
  have prems_wf: "\<forall> p \<in> set (prems r). formula_well_formed (alphabet Fone) p"
  proof
    fix p assume p_in: "p \<in> set (prems r)"
    have "sub_formula s p \<in> set (prems (sub_rule s r))"
      using p_in by simp
    then obtain q where q_in: "q \<in> set (take i (steps pr))" and q_eq: "sub_formula s p = q"
      using dw unfolding derived_with_def by blast
    have "q \<in> set (steps pr)"
      using q_in by (meson in_set_takeD)
    hence "formula_well_formed (alphabet Fone) (sub_formula s p)"
      using wf_steps q_eq by blast
    thus "formula_well_formed (alphabet Fone) p"
      by (rule instance_well_formed)
  qed
  have "r \<in> well_formed_rules"
    unfolding well_formed_rules_def using r_in concl_wf prems_wf by blast
  thus ?thesis using dw by blast
qed

subsection \<open>Per-connective templates\<close>

definition connective_template :: "'c1 \<Rightarrow> 'c2 formula" where
  "connective_template c = (SOME tmpl.
     formula_well_formed (alphabet Ftwo) tmpl
     \<and> var_set_form tmpl \<subseteq> set (marker_variables (arity (alphabet Fone) c))
     \<and> (\<forall> val. eval (alphabet Ftwo) val tmpl
          = conn_evals (alphabet Fone) c (map val (marker_variables (arity (alphabet Fone) c)))))"

lemma connective_template_exists:
  "\<exists> tmpl. formula_well_formed (alphabet Ftwo) tmpl
     \<and> var_set_form tmpl \<subseteq> set (marker_variables (arity (alphabet Fone) c))
     \<and> (\<forall> val. eval (alphabet Ftwo) val tmpl
          = conn_evals (alphabet Fone) c (map val (marker_variables (arity (alphabet Fone) c))))"
proof -
  define names where "names = marker_variables (arity (alphabet Fone) c)"
  define dmf where "dmf = truth_table_formula (conn_evals (alphabet Fone) c) names"
  obtain f' where f'_wf: "formula_well_formed (alphabet Ftwo) f'"
    and f'_equiv: "formulas_equiv dmf dm_alphabet f' (alphabet Ftwo)"
    using two.func_complete by blast
  obtain topc where top_arity: "arity (alphabet Ftwo) topc = 0"
    and top_true: "\<forall> val. eval (alphabet Ftwo) val (Conn topc []) = True"
    using two.has_top by blast
  have vars_dmf: "var_set_form dmf \<subseteq> set names"
    unfolding dmf_def by (rule truth_table_formula_var_set)
  obtain tmpl where tmpl_wf: "formula_well_formed (alphabet Ftwo) tmpl"
    and tmpl_vars: "var_set_form tmpl \<subseteq> set names"
    and tmpl_eval: "\<forall> val. eval (alphabet Ftwo) val tmpl = eval dm_alphabet val dmf"
    using connective_template_pruned[OF f'_equiv f'_wf top_arity _ vars_dmf] top_true
    by blast
  have "\<forall> val. eval (alphabet Ftwo) val tmpl
      = conn_evals (alphabet Fone) c (map val names)"
    using tmpl_eval unfolding dmf_def by (simp add: truth_table_formula_eval)
  thus ?thesis
    using tmpl_wf tmpl_vars unfolding names_def by blast
qed

lemma connective_template_spec:
  "formula_well_formed (alphabet Ftwo) (connective_template c)
   \<and> var_set_form (connective_template c) \<subseteq> set (marker_variables (arity (alphabet Fone) c))
   \<and> (\<forall> val. eval (alphabet Ftwo) val (connective_template c)
        = conn_evals (alphabet Fone) c (map val (marker_variables (arity (alphabet Fone) c))))"
  unfolding connective_template_def
  by (rule someI_ex[OF connective_template_exists])

definition template_length_bound :: nat where
  "template_length_bound = Max ((\<lambda> c :: 'c1. len_formula (connective_template c)) ` UNIV)"

lemma connective_template_length:
  "len_formula (connective_template c) \<le> template_length_bound"
proof -
  have "finite ((\<lambda> c :: 'c1. len_formula (connective_template c)) ` UNIV)"
    using one.finite_alphabet by simp
  thus ?thesis
    unfolding template_length_bound_def by (intro Max_ge) auto
qed

lemma template_length_bound_positive:
  "1 \<le> template_length_bound"
proof -
  obtain c where c_type: "(c :: 'c1) = c" by blast
  have "1 \<le> len_formula (connective_template c)"
    using len_formula_positive by blast
  also have "\<dots> \<le> template_length_bound"
    by (rule connective_template_length)
  finally show ?thesis .
qed

subsection \<open>The formula translation\<close>

fun translate_formula :: "'c1 formula \<Rightarrow> 'c2 formula" where
  "translate_formula (Atom v) = Atom v"
| "translate_formula (Conn c fs) = sub_formula
     (marker_substitution (marker_variables (arity (alphabet Fone) c))
        (map translate_formula fs))
     (connective_template c)"

lemma translate_formula_well_formed:
  "formula_well_formed (alphabet Ftwo) (translate_formula f)"
proof (induction f)
  case (Atom v)
  show ?case by simp
next
  case (Conn c fs)
  define names where "names = marker_variables (arity (alphabet Fone) c)"
  define sigma where "sigma = marker_substitution names (map translate_formula fs)"
  have tmpl_wf: "formula_well_formed (alphabet Ftwo) (connective_template c)"
    using connective_template_spec by blast
  have sigma_wf: "formula_well_formed (alphabet Ftwo) (sigma v)" for v
  proof -
    have "sigma v \<in> set (map translate_formula fs) \<union> {Atom v}"
      unfolding sigma_def by (rule marker_substitution_range)
    thus ?thesis using Conn.IH by auto
  qed
  have "formula_well_formed (alphabet Ftwo) (sub_formula sigma (connective_template c))"
    by (rule sub_formula_well_formed[OF tmpl_wf sigma_wf])
  thus ?case
    unfolding sigma_def names_def by simp
qed

lemma translate_formula_eval:
  assumes "formula_well_formed (alphabet Fone) f"
  shows "eval (alphabet Ftwo) val (translate_formula f) = eval (alphabet Fone) val f"
  using assms
proof (induction f)
  case (Atom a)
  show ?case by simp
next
  case (Conn c fs)
  define names where "names = marker_variables (arity (alphabet Fone) c)"
  define sigma where "sigma = marker_substitution names (map translate_formula fs)"
  have len_fs: "length fs = arity (alphabet Fone) c"
    using Conn.prems by simp
  have len_names: "length names = arity (alphabet Fone) c" and dist: "distinct names"
    unfolding names_def using marker_variables_spec by blast+
  have inner: "map (\<lambda>v. eval (alphabet Ftwo) val (sigma v)) names
             = map (eval (alphabet Fone) val) fs"
  proof (rule nth_equalityI)
    show "length (map (\<lambda>v. eval (alphabet Ftwo) val (sigma v)) names)
        = length (map (eval (alphabet Fone) val) fs)"
      using len_fs len_names by simp
  next
    fix k assume "k < length (map (\<lambda>v. eval (alphabet Ftwo) val (sigma v)) names)"
    hence k_lt: "k < length names" by simp
    hence k_fs: "k < length fs" using len_fs len_names by simp
    have args_len: "length (map translate_formula fs) = length names"
      using len_fs len_names by simp
    have sigma_k: "sigma (names ! k) = translate_formula (fs ! k)"
      unfolding sigma_def
      using marker_substitution_nth[OF dist args_len k_lt] k_fs by simp
    have fs_k_wf: "formula_well_formed (alphabet Fone) (fs ! k)"
      using Conn.prems k_fs by auto
    have "eval (alphabet Ftwo) val (translate_formula (fs ! k))
        = eval (alphabet Fone) val (fs ! k)"
      using Conn.IH fs_k_wf k_fs nth_mem by blast
    thus "map (\<lambda>v. eval (alphabet Ftwo) val (sigma v)) names ! k
        = map (eval (alphabet Fone) val) fs ! k"
      using sigma_k k_lt k_fs by simp
  qed
  have "eval (alphabet Ftwo) val (translate_formula (Conn c fs))
      = eval (alphabet Ftwo) val (sub_formula sigma (connective_template c))"
    unfolding sigma_def names_def by simp
  also have "\<dots> = eval (alphabet Ftwo) (\<lambda>v. eval (alphabet Ftwo) val (sigma v))
                    (connective_template c)"
    by (rule sub_formula_eval)
  also have "\<dots> = conn_evals (alphabet Fone) c
                    (map (\<lambda>v. eval (alphabet Ftwo) val (sigma v)) names)"
    using connective_template_spec[of c] unfolding names_def by blast
  also have "\<dots> = conn_evals (alphabet Fone) c (map (eval (alphabet Fone) val) fs)"
    using inner by simp
  also have "\<dots> = eval (alphabet Fone) val (Conn c fs)"
    by simp
  finally show ?case .
qed

lemma translate_formula_equiv:
  assumes "formula_well_formed (alphabet Fone) f"
  shows "formulas_equiv f (alphabet Fone) (translate_formula f) (alphabet Ftwo)"
  unfolding formulas_equiv_def using translate_formula_eval[OF assms] by simp

lemma translate_formula_substitution:
  assumes "formula_well_formed (alphabet Fone) f"
  shows "translate_formula (sub_formula s f)
       = sub_formula (\<lambda>u. translate_formula (s u)) (translate_formula f)"
  using assms
proof (induction f)
  case (Atom a)
  show ?case by simp
next
  case (Conn c fs)
  define names where "names = marker_variables (arity (alphabet Fone) c)"
  have len_fs: "length fs = arity (alphabet Fone) c"
    using Conn.prems by simp
  have len_names: "length names = arity (alphabet Fone) c" and dist: "distinct names"
    unfolding names_def using marker_variables_spec by blast+
  have inner_eq: "marker_substitution names (map translate_formula (map (sub_formula s) fs)) v
                = sub_formula (\<lambda>u. translate_formula (s u))
                    (marker_substitution names (map translate_formula fs) v)"
    if v_in: "v \<in> var_set_form (connective_template c)" for v
  proof -
    have "v \<in> set names"
      using v_in connective_template_spec[of c] unfolding names_def by blast
    hence "\<exists> k < length names. names ! k = v"
      by (simp add: in_set_conv_nth)
    then obtain k where k_lt: "k < length names" and "names ! k = v" by blast
    hence v_eq: "v = names ! k" by simp
    have k_fs: "k < length fs" using k_lt len_fs len_names by simp
    have args_len1: "length (map translate_formula (map (sub_formula s) fs)) = length names"
      using len_fs len_names by simp
    have args_len2: "length (map translate_formula fs) = length names"
      using len_fs len_names by simp
    have lhs_val: "marker_substitution names (map translate_formula (map (sub_formula s) fs)) v
                 = translate_formula (sub_formula s (fs ! k))"
      unfolding v_eq
      using marker_substitution_nth[OF dist args_len1 k_lt] k_fs by simp
    have rhs_val: "marker_substitution names (map translate_formula fs) v
                 = translate_formula (fs ! k)"
      unfolding v_eq
      using marker_substitution_nth[OF dist args_len2 k_lt] k_fs by simp
    have fs_k_wf: "formula_well_formed (alphabet Fone) (fs ! k)"
      using Conn.prems k_fs by auto
    have "translate_formula (sub_formula s (fs ! k))
        = sub_formula (\<lambda>u. translate_formula (s u)) (translate_formula (fs ! k))"
      using Conn.IH fs_k_wf k_fs nth_mem by blast
    thus ?thesis using lhs_val rhs_val by simp
  qed
  have "translate_formula (sub_formula s (Conn c fs))
      = sub_formula (marker_substitution names (map translate_formula (map (sub_formula s) fs)))
          (connective_template c)"
    unfolding names_def by simp
  also have "\<dots> = sub_formula (\<lambda>v. sub_formula (\<lambda>u. translate_formula (s u))
                    (marker_substitution names (map translate_formula fs) v))
                    (connective_template c)"
    by (rule sub_formula_cong) (rule inner_eq)
  also have "\<dots> = sub_formula (\<lambda>u. translate_formula (s u))
                    (sub_formula (marker_substitution names (map translate_formula fs))
                       (connective_template c))"
    by (rule sub_formula_comp[symmetric])
  also have "\<dots> = sub_formula (\<lambda>u. translate_formula (s u)) (translate_formula (Conn c fs))"
    unfolding names_def by simp
  finally show ?case .
qed

lemma translate_formula_length:
  assumes "formula_well_formed (alphabet Fone) f"
      and "depth_formula f \<le> d"
  shows "len_formula (translate_formula f) \<le> template_length_bound ^ d * len_formula f"
  using assms
proof (induction f arbitrary: d)
  case (Atom a)
  have "len_formula (translate_formula (Atom a)) = 1" by simp
  also have "\<dots> \<le> template_length_bound ^ d"
    using template_length_bound_positive by simp
  finally show ?case by simp
next
  case (Conn c fs)
  define names where "names = marker_variables (arity (alphabet Fone) c)"
  define sigma where "sigma = marker_substitution names (map translate_formula fs)"
  have len_fs: "length fs = arity (alphabet Fone) c"
    using Conn.prems(1) by simp
  have len_names: "length names = arity (alphabet Fone) c" and dist: "distinct names"
    unfolding names_def using marker_variables_spec by blast+
  have T1: "(1 :: nat) \<le> template_length_bound"
    by (rule template_length_bound_positive)
  have d_pos: "1 \<le> d"
  proof -
    have "1 \<le> depth_formula (Conn c fs)" by simp
    thus ?thesis using Conn.prems(2) by linarith
  qed
  have sigma_outside: "\<forall> v. v \<notin> set names \<longrightarrow> sigma v = Atom v"
    unfolding sigma_def using marker_substitution_outside by blast
  have step_bound: "len_formula (sub_formula sigma (connective_template c))
             \<le> len_formula (connective_template c) * len_sub (set names) sigma"
    using sigma_outside by (intro sub_formula_bound) simp_all
  show ?case
  proof (cases "fs = []")
    case True
    hence "names = []" using len_fs len_names by simp
    hence "len_sub (set names) sigma = 1"
      unfolding len_sub_def by simp
    hence "len_formula (sub_formula sigma (connective_template c))
         \<le> len_formula (connective_template c)"
      using step_bound by simp
    also have "\<dots> \<le> template_length_bound"
      by (rule connective_template_length)
    also have "\<dots> \<le> template_length_bound ^ d"
      using power_increasing[OF d_pos T1] by simp
    finally show ?thesis
      using True unfolding sigma_def names_def by simp
  next
    case False
    obtain g gs where fs_eq: "fs = g # gs" using False by (cases fs) auto
    have "1 \<le> len_formula g" by (rule len_formula_positive)
    hence sum_ge1: "1 \<le> sum_list (map len_formula fs)"
      unfolding fs_eq by simp
    have Td1: "(1 :: nat) \<le> template_length_bound ^ (d - 1)"
      using T1 by simp
    have sigma_nth: "sigma (names ! k) = translate_formula (fs ! k)"
      if k_lt: "k < length names" for k
    proof -
      have args_len: "length (map translate_formula fs) = length names"
        using len_fs len_names by simp
      show ?thesis
        unfolding sigma_def
        using marker_substitution_nth[OF dist args_len k_lt] k_lt len_fs len_names by simp
    qed
    have map_eq: "map (\<lambda>v. len_formula (sigma v)) names
                = map (\<lambda>g. len_formula (translate_formula g)) fs"
    proof (rule nth_equalityI)
      show "length (map (\<lambda>v. len_formula (sigma v)) names)
          = length (map (\<lambda>g. len_formula (translate_formula g)) fs)"
        using len_fs len_names by simp
    next
      fix k assume "k < length (map (\<lambda>v. len_formula (sigma v)) names)"
      hence k_lt: "k < length names" by simp
      hence k_fs: "k < length fs" using len_fs len_names by simp
      show "map (\<lambda>v. len_formula (sigma v)) names ! k
          = map (\<lambda>g. len_formula (translate_formula g)) fs ! k"
        using sigma_nth[OF k_lt] k_lt k_fs by simp
    qed
    have sum_set_eq: "(\<Sum> v \<in> set names. len_formula (sigma v))
                    = sum_list (map (\<lambda>g. len_formula (translate_formula g)) fs)"
    proof -
      have "(\<Sum> v \<in> set names. len_formula (sigma v))
          = sum_list (map (\<lambda>v. len_formula (sigma v)) names)"
        using dist by (simp add: sum_list_distinct_conv_sum_set)
      thus ?thesis using map_eq by simp
    qed
    have children_bound: "sum_list (map (\<lambda>g. len_formula (translate_formula g)) fs)
                        \<le> template_length_bound ^ (d - 1) * sum_list (map len_formula fs)"
    proof -
      have child: "len_formula (translate_formula g)
                 \<le> template_length_bound ^ (d - 1) * len_formula g"
        if g_in: "g \<in> set fs" for g
      proof -
        have g_wf: "formula_well_formed (alphabet Fone) g"
          using Conn.prems(1) g_in by auto
        have "depth_formula g \<le> d - 1"
        proof -
          have "depth_formula (Conn c fs) = 1 + Max (set (map depth_formula fs))"
            using False by simp
          moreover have "depth_formula g \<le> Max (set (map depth_formula fs))"
            using g_in by (intro Max_ge) auto
          ultimately show ?thesis using Conn.prems(2) by linarith
        qed
        thus ?thesis using Conn.IH g_in g_wf by blast
      qed
      have "sum_list (map (\<lambda>g. len_formula (translate_formula g)) fs)
          \<le> sum_list (map (\<lambda>g. template_length_bound ^ (d - 1) * len_formula g) fs)"
        using child by (intro sum_list_pointwise_le) blast
      also have "\<dots> = template_length_bound ^ (d - 1) * sum_list (map len_formula fs)"
        by (simp add: sum_list_const_mult)
      finally show ?thesis .
    qed
    have inner_ge1: "1 \<le> template_length_bound ^ (d - 1) * sum_list (map len_formula fs)"
      using mult_le_mono[OF Td1 sum_ge1] by simp
    have len_sub_bound: "len_sub (set names) sigma
                       \<le> template_length_bound ^ (d - 1) * sum_list (map len_formula fs)"
    proof -
      have "len_sub (set names) sigma
          = max 1 (sum_list (map (\<lambda>g. len_formula (translate_formula g)) fs))"
        unfolding len_sub_def using sum_set_eq by simp
      also have "\<dots> \<le> max 1 (template_length_bound ^ (d - 1) * sum_list (map len_formula fs))"
        using children_bound by simp
      also have "\<dots> = template_length_bound ^ (d - 1) * sum_list (map len_formula fs)"
        using inner_ge1 by simp
      finally show ?thesis .
    qed
    have power_split: "template_length_bound * template_length_bound ^ (d - 1)
                     = template_length_bound ^ d"
      using d_pos by (cases d) simp_all
    have "len_formula (translate_formula (Conn c fs))
        = len_formula (sub_formula sigma (connective_template c))"
      unfolding sigma_def names_def by simp
    also have "\<dots> \<le> len_formula (connective_template c) * len_sub (set names) sigma"
      using step_bound .
    also have "\<dots> \<le> template_length_bound
                  * (template_length_bound ^ (d - 1) * sum_list (map len_formula fs))"
      by (rule mult_le_mono[OF connective_template_length len_sub_bound])
    also have "\<dots> = template_length_bound ^ d * sum_list (map len_formula fs)"
      using power_split by (simp add: mult.assoc)
    also have "\<dots> \<le> template_length_bound ^ d * len_formula (Conn c fs)"
      by (intro mult_le_mono2) simp
    finally show ?thesis .
  qed
qed

definition template_depth_bound :: nat where
  "template_depth_bound = Max ((\<lambda> c :: 'c1. depth_formula (connective_template c)) ` UNIV)"

lemma connective_template_depth:
  "depth_formula (connective_template c) \<le> template_depth_bound"
proof -
  have "finite ((\<lambda> c :: 'c1. depth_formula (connective_template c)) ` UNIV)"
    using one.finite_alphabet by simp
  thus ?thesis
    unfolding template_depth_bound_def by (rule Max_ge) simp
qed

lemma template_depth_bound_positive: "1 \<le> template_depth_bound"
proof -
  have "1 \<le> depth_formula (connective_template undefined)"
    by (cases "connective_template (undefined :: 'c1)") auto
  thus ?thesis using connective_template_depth[of undefined] by linarith
qed

(*
  The depth analogue of translate_formula_length: compositional translation
  multiplies depth by at most the largest template depth.  Together with the
  length bound this is what keeps g = translate o balance polynomial AND
  logarithmic-depth, which is what makes the T ^ D factor of
  translated_proof_simulation polynomial.
*)
lemma translate_formula_depth:
  assumes "formula_well_formed (alphabet Fone) f"
  shows "depth_formula (translate_formula f)
           \<le> depth_formula f * template_depth_bound"
  using assms
proof (induction f)
  case (Atom a)
  show ?case using template_depth_bound_positive by simp
next
  case (Conn c fs)
  have atom_id: "sub_formula Atom (g :: 'c2 formula) = g" for g
    by (induction g) (simp_all add: map_idI)
  define names where "names = marker_variables (arity (alphabet Fone) c)"
  define sigma where "sigma = marker_substitution names (map translate_formula fs)"
  have len_fs: "length fs = arity (alphabet Fone) c"
    using Conn.prems by simp
  have len_names: "length names = arity (alphabet Fone) c" and dist: "distinct names"
    unfolding names_def using marker_variables_spec by blast+
  have TD1: "(1 :: nat) \<le> template_depth_bound"
    by (rule template_depth_bound_positive)
  have sigma_outside: "\<forall> v. v \<notin> set names \<longrightarrow> sigma v = Atom v"
    unfolding sigma_def using marker_substitution_outside by blast
  have step_bound: "depth_formula (sub_formula sigma (connective_template c))
             \<le> depth_formula (connective_template c) + depth_sub (set names) sigma"
    using sigma_outside by (intro sub_formula_depth_bound) simp_all
  have unfold_tr: "depth_formula (translate_formula (Conn c fs))
                 = depth_formula (sub_formula sigma (connective_template c))"
    unfolding sigma_def names_def by simp
  show ?case
  proof (cases "fs = []")
    case True
    hence names_nil: "names = []" using len_fs len_names by simp
    have "sub_formula sigma (connective_template c)
        = sub_formula Atom (connective_template c)"
    proof (rule sub_formula_agree, intro ballI)
      fix v assume "v \<in> var_set_form (connective_template c)"
      hence "v \<in> set names"
        unfolding names_def using connective_template_spec by blast
      thus "sigma v = Atom v" using names_nil by simp
    qed
    hence tid: "sub_formula sigma (connective_template c) = connective_template c"
      using atom_id by simp
    have "depth_formula (translate_formula (Conn c fs))
        = depth_formula (connective_template c)"
      using unfold_tr tid by simp
    also have "\<dots> \<le> template_depth_bound" by (rule connective_template_depth)
    also have "\<dots> \<le> depth_formula (Conn c fs) * template_depth_bound"
      using True by simp
    finally show ?thesis .
  next
    case False
    have sigma_nth: "sigma (names ! k) = translate_formula (fs ! k)"
      if k_lt: "k < length names" for k
    proof -
      have args_len: "length (map translate_formula fs) = length names"
        using len_fs len_names by simp
      show ?thesis
        unfolding sigma_def
        using marker_substitution_nth[OF dist args_len k_lt] k_lt len_fs len_names by simp
    qed
    define M where "M = Max (set (map depth_formula fs))"
    have maxfs: "depth_formula (Conn c fs) = 1 + M"
      using False unfolding M_def by simp
    have M1: "1 \<le> M"
    proof -
      obtain g gs where fs_eq: "fs = g # gs" using False by (cases fs) auto
      have "1 \<le> depth_formula g" by (cases g) auto
      moreover have "depth_formula g \<le> M"
        unfolding M_def using fs_eq by (intro Max_ge) auto
      ultimately show ?thesis by linarith
    qed
    have child_bound: "depth_formula (sigma v) \<le> M * template_depth_bound"
      if v_in: "v \<in> set names" for v
    proof -
      from v_in obtain k where k_lt: "k < length names" and v_eq: "v = names ! k"
        by (metis in_set_conv_nth)
      have k_fs: "k < length fs" using k_lt len_fs len_names by simp
      have g_wf: "formula_well_formed (alphabet Fone) (fs ! k)"
        using Conn.prems k_fs by auto
      have ih: "depth_formula (translate_formula (fs ! k))
                \<le> depth_formula (fs ! k) * template_depth_bound"
        using Conn.IH nth_mem[OF k_fs] g_wf by blast
      have "depth_formula (fs ! k) \<le> M"
        unfolding M_def using k_fs by (intro Max_ge) auto
      hence "depth_formula (fs ! k) * template_depth_bound \<le> M * template_depth_bound"
        by (rule mult_le_mono1)
      from order_trans[OF ih this] show ?thesis
        using sigma_nth[OF k_lt] v_eq by simp
    qed
    have children_bound: "depth_sub (set names) sigma \<le> M * template_depth_bound"
      unfolding depth_sub_def
    proof (rule Max.boundedI)
      show "finite (insert 1 ((\<lambda>v. depth_formula (sigma v)) ` set names))" by simp
      show "insert 1 ((\<lambda>v. depth_formula (sigma v)) ` set names) \<noteq> {}" by simp
      fix x assume "x \<in> insert 1 ((\<lambda>v. depth_formula (sigma v)) ` set names)"
      thus "x \<le> M * template_depth_bound"
      proof
        assume "x = 1"
        thus ?thesis using mult_le_mono[OF M1 TD1] by simp
      next
        assume "x \<in> (\<lambda>v. depth_formula (sigma v)) ` set names"
        then obtain v where "v \<in> set names" and "x = depth_formula (sigma v)" by blast
        thus ?thesis using child_bound by simp
      qed
    qed
    have "depth_formula (translate_formula (Conn c fs))
        \<le> depth_formula (connective_template c) + depth_sub (set names) sigma"
      using unfold_tr step_bound by simp
    also have "\<dots> \<le> template_depth_bound + M * template_depth_bound"
      by (rule add_le_mono[OF connective_template_depth children_bound])
    also have "\<dots> = (1 + M) * template_depth_bound"
      by (simp add: algebra_simps)
    also have "\<dots> = depth_formula (Conn c fs) * template_depth_bound"
      using maxfs by simp
    finally show ?thesis .
  qed
qed

subsection \<open>Simulating one rule application\<close>

lemma proof_exists_for_translated_rule:
  assumes "r \<in> well_formed_rules"
  shows "\<exists> pr2. valid_proof Ftwo pr2
             \<and> assumptions pr2 = translate_formula ` set (prems r)
             \<and> thesis pr2 = translate_formula (concl r)"
proof -
  have r_in: "r \<in> rules Fone"
    using assms well_formed_rules_subset by blast
  have prems_wf: "\<forall> p \<in> set (prems r). formula_well_formed (alphabet Fone) p"
    and concl_wf: "formula_well_formed (alphabet Fone) (concl r)"
    using assms unfolding well_formed_rules_def by blast+
  have rule_sound: "\<forall> val. (\<forall> p \<in> set (prems r). eval (alphabet Fone) val p)
                     \<longrightarrow> eval (alphabet Fone) val (concl r)"
    using one.sound r_in unfolding sound_rule_def by blast
  have entails: "\<forall> val. (\<forall> q \<in> translate_formula ` set (prems r). eval (alphabet Ftwo) val q)
                  \<longrightarrow> eval (alphabet Ftwo) val (translate_formula (concl r))"
  proof (intro allI impI)
    fix val assume A: "\<forall> q \<in> translate_formula ` set (prems r). eval (alphabet Ftwo) val q"
    have "\<forall> p \<in> set (prems r). eval (alphabet Fone) val p"
    proof
      fix p assume p_in: "p \<in> set (prems r)"
      have "eval (alphabet Ftwo) val (translate_formula p)"
        using A p_in by blast
      thus "eval (alphabet Fone) val p"
        using translate_formula_eval prems_wf p_in by blast
    qed
    hence "eval (alphabet Fone) val (concl r)"
      using rule_sound by blast
    thus "eval (alphabet Ftwo) val (translate_formula (concl r))"
      using translate_formula_eval concl_wf by blast
  qed
  have wf2_prems: "\<forall> q \<in> translate_formula ` set (prems r). formula_well_formed (alphabet Ftwo) q"
    using translate_formula_well_formed by blast
  have wf2_concl: "formula_well_formed (alphabet Ftwo) (translate_formula (concl r))"
    by (rule translate_formula_well_formed)
  from two.impl_complete have completeness_instance:
    "\<And> fs th. (\<forall> f \<in> fs. formula_well_formed (alphabet Ftwo) f) \<Longrightarrow>
              formula_well_formed (alphabet Ftwo) th \<Longrightarrow>
              (\<forall> val. (\<forall> f \<in> fs. eval (alphabet Ftwo) val f) \<longrightarrow> eval (alphabet Ftwo) val th) \<Longrightarrow>
              \<exists> pr2. valid_proof Ftwo pr2 \<and> assumptions pr2 = fs \<and> thesis pr2 = th"
    by blast
  show ?thesis
    by (rule completeness_instance[OF wf2_prems wf2_concl entails])
qed

lemma translated_rule_proof_exists:
  "\<exists> pf :: 'c1 rule \<Rightarrow> 'c2 frege_proof. \<forall> r \<in> well_formed_rules.
      valid_proof Ftwo (pf r)
    \<and> assumptions (pf r) = translate_formula ` set (prems r)
    \<and> thesis (pf r) = translate_formula (concl r)"
proof -
  have "\<forall> r \<in> well_formed_rules. \<exists> pr2. valid_proof Ftwo pr2
      \<and> assumptions pr2 = translate_formula ` set (prems r)
      \<and> thesis pr2 = translate_formula (concl r)"
    using proof_exists_for_translated_rule by blast
  thus ?thesis by (rule bchoice)
qed

definition translated_rule_proof :: "'c1 rule \<Rightarrow> 'c2 frege_proof" where
  "translated_rule_proof = (SOME pf. \<forall> r \<in> well_formed_rules.
      valid_proof Ftwo (pf r)
    \<and> assumptions (pf r) = translate_formula ` set (prems r)
    \<and> thesis (pf r) = translate_formula (concl r))"

lemma translated_rule_proof_spec:
  assumes "r \<in> well_formed_rules"
  shows "valid_proof Ftwo (translated_rule_proof r)
       \<and> assumptions (translated_rule_proof r) = translate_formula ` set (prems r)
       \<and> thesis (translated_rule_proof r) = translate_formula (concl r)"
proof -
  have "\<forall> r \<in> well_formed_rules. valid_proof Ftwo (translated_rule_proof r)
      \<and> assumptions (translated_rule_proof r) = translate_formula ` set (prems r)
      \<and> thesis (translated_rule_proof r) = translate_formula (concl r)"
    unfolding translated_rule_proof_def
    by (rule someI_ex[OF translated_rule_proof_exists])
  thus ?thesis using assms by blast
qed

definition translated_step_proof :: "'c1 rule \<Rightarrow> (string \<Rightarrow> 'c1 formula) \<Rightarrow> 'c2 frege_proof" where
  "translated_step_proof r s = sub_proof (\<lambda>u. translate_formula (s u)) (translated_rule_proof r)"

lemma translated_step_proof_proves:
  assumes "r \<in> well_formed_rules"
  shows "valid_proof Ftwo (translated_step_proof r s)
       \<and> assumptions (translated_step_proof r s) = translate_formula ` set (prems (sub_rule s r))
       \<and> thesis (translated_step_proof r s) = translate_formula (concl (sub_rule s r))"
proof -
  have base_valid: "valid_proof Ftwo (translated_rule_proof r)"
    and base_asms: "assumptions (translated_rule_proof r) = translate_formula ` set (prems r)"
    and base_thesis: "thesis (translated_rule_proof r) = translate_formula (concl r)"
    using translated_rule_proof_spec[OF assms] by blast+
  have prems_wf: "\<forall> p \<in> set (prems r). formula_well_formed (alphabet Fone) p"
    and concl_wf: "formula_well_formed (alphabet Fone) (concl r)"
    using assms unfolding well_formed_rules_def by blast+
  have valid2: "valid_proof Ftwo (translated_step_proof r s)"
    unfolding translated_step_proof_def
    by (rule two.proof_substitution[OF base_valid])
  have thesis2: "thesis (translated_step_proof r s) = translate_formula (concl (sub_rule s r))"
  proof -
    have "thesis (translated_step_proof r s)
        = sub_formula (\<lambda>u. translate_formula (s u)) (thesis (translated_rule_proof r))"
      unfolding translated_step_proof_def by simp
    also have "\<dots> = sub_formula (\<lambda>u. translate_formula (s u)) (translate_formula (concl r))"
      using base_thesis by simp
    also have "\<dots> = translate_formula (sub_formula s (concl r))"
      by (rule translate_formula_substitution[OF concl_wf, symmetric])
    also have "\<dots> = translate_formula (concl (sub_rule s r))"
      by simp
    finally show ?thesis .
  qed
  have asms2: "assumptions (translated_step_proof r s)
             = translate_formula ` set (prems (sub_rule s r))"
  proof -
    have pointwise: "sub_formula (\<lambda>u. translate_formula (s u)) (translate_formula p)
                   = translate_formula (sub_formula s p)"
      if p_in: "p \<in> set (prems r)" for p
      using translate_formula_substitution prems_wf p_in by fastforce
    have "assumptions (translated_step_proof r s)
        = (sub_formula (\<lambda>u. translate_formula (s u))) ` assumptions (translated_rule_proof r)"
      unfolding translated_step_proof_def by simp
    also have "\<dots> = (sub_formula (\<lambda>u. translate_formula (s u))) ` translate_formula ` set (prems r)"
      using base_asms by simp
    also have "\<dots> = translate_formula ` sub_formula s ` set (prems r)"
      using pointwise by force
    also have "\<dots> = translate_formula ` set (prems (sub_rule s r))"
      by simp
    finally show ?thesis .
  qed
  show ?thesis using valid2 thesis2 asms2 by blast
qed

subsection \<open>Assembling the simulated proof\<close>

definition simulation_step :: "'c1 frege_proof \<Rightarrow> nat \<Rightarrow> 'c2 frege_proof \<Rightarrow> 'c2 frege_proof" where
  "simulation_step pr i acc =
     (let (r, s) = choose_rule_substitution well_formed_rules i pr
      in combine_proofs acc (translated_step_proof r s))"

definition simulation_proof :: "'c1 frege_proof \<Rightarrow> 'c2 formula \<Rightarrow> 'c2 frege_proof" where
  "simulation_proof pr goal =
     fold (simulation_step pr) [0..<length (steps pr)]
       \<lparr> assumptions = {}, thesis = goal, steps = [] \<rparr>"

lemma simulation_step_progress:
  assumes valid_pr: "valid_proof Fone pr"
      and assm_pr: "assumptions pr = {}"
      and wf_steps: "\<forall> st \<in> set (steps pr). formula_well_formed (alphabet Fone) st"
      and k_lt: "k < length (steps pr)"
      and acc_assm: "assumptions acc = {}"
      and acc_steps: "translate_formula ` set (take k (steps pr)) \<subseteq> set (steps acc)"
      and acc_valid: "k = 0 \<or> valid_proof Ftwo acc"
      and acc0: "k = 0 \<longrightarrow> steps acc = []"
  shows "assumptions (simulation_step pr k acc) = {}
       \<and> valid_proof Ftwo (simulation_step pr k acc)
       \<and> thesis (simulation_step pr k acc) = translate_formula (steps pr ! k)
       \<and> translate_formula ` set (take (Suc k) (steps pr))
           \<subseteq> set (steps (simulation_step pr k acc))"
proof -
  have step_not_assm: "steps pr ! k \<notin> assumptions pr"
    using assm_pr by simp
  have ex_rs: "\<exists> r s. r \<in> well_formed_rules \<and> derived_with k pr r s"
    by (rule valid_proof_well_formed_rules[OF valid_pr wf_steps k_lt step_not_assm])
  define r where "r = fst (choose_rule_substitution well_formed_rules k pr)"
  define s where "s = snd (choose_rule_substitution well_formed_rules k pr)"
  have r_in: "r \<in> well_formed_rules"
    and dchoose: "derived_with k pr r s"
    using choose_rule_substitution_spec[OF ex_rs] unfolding r_def s_def by blast+
  have eq: "simulation_step pr k acc = combine_proofs acc (translated_step_proof r s)"
  proof (cases "choose_rule_substitution well_formed_rules k pr")
    case (Pair r' s')
    thus ?thesis
      unfolding simulation_step_def r_def s_def by simp
  qed
  have sp_valid: "valid_proof Ftwo (translated_step_proof r s)"
    and sp_asms: "assumptions (translated_step_proof r s)
                = translate_formula ` set (prems (sub_rule s r))"
    and sp_thesis: "thesis (translated_step_proof r s)
                  = translate_formula (concl (sub_rule s r))"
    using translated_step_proof_proves[OF r_in] by blast+
  have concl_eq: "concl (sub_rule s r) = steps pr ! k"
    using dchoose unfolding derived_with_def by blast
  have prems_sub: "set (prems (sub_rule s r)) \<subseteq> set (take k (steps pr))"
    using dchoose unfolding derived_with_def by blast
  have prems_seen: "assumptions (translated_step_proof r s) \<subseteq> set (steps acc)"
  proof -
    have "assumptions (translated_step_proof r s)
        \<subseteq> translate_formula ` set (take k (steps pr))"
      using sp_asms prems_sub by blast
    thus ?thesis using acc_steps by blast
  qed
  have valid_next: "valid_proof Ftwo (simulation_step pr k acc)"
  proof (cases "k = 0")
    case True
    have acc_steps0: "steps acc = []"
      using True acc0 by simp
    have comb_eq: "combine_proofs acc (translated_step_proof r s) = translated_step_proof r s"
      using acc_assm acc_steps0 by (cases acc) simp
    show ?thesis
      using eq comb_eq sp_valid by simp
  next
    case False
    hence acc_valid': "valid_proof Ftwo acc"
      using acc_valid by blast
    show ?thesis
      using eq acc_valid' sp_valid two.combining_valid_proofs by blast
  qed
  have assm_next: "assumptions (simulation_step pr k acc) = {}"
    using eq acc_assm prems_seen by auto
  have thesis_next: "thesis (simulation_step pr k acc) = translate_formula (steps pr ! k)"
    using eq sp_thesis concl_eq by simp
  have steps_next: "translate_formula ` set (take (Suc k) (steps pr))
                  \<subseteq> set (steps (simulation_step pr k acc))"
  proof
    fix q assume "q \<in> translate_formula ` set (take (Suc k) (steps pr))"
    then obtain f where f_in: "f \<in> set (take (Suc k) (steps pr))"
      and q_eq: "q = translate_formula f" by blast
    from f_in obtain i where i_lt_take: "i < length (take (Suc k) (steps pr))"
      and fi_take: "take (Suc k) (steps pr) ! i = f"
      by (auto simp add: in_set_conv_nth)
    hence i_lt: "i < Suc k" by simp
    have fi: "f = steps pr ! i"
      using fi_take i_lt k_lt by simp
    consider "i < k" | "i = k" using i_lt by linarith
    thus "q \<in> set (steps (simulation_step pr k acc))"
    proof cases
      case 1
      have "steps pr ! i \<in> set (take k (steps pr))"
        using 1 k_lt by (auto simp add: in_set_conv_nth)
      hence "q \<in> translate_formula ` set (take k (steps pr))"
        using fi q_eq by blast
      hence "q \<in> set (steps acc)"
        using acc_steps by blast
      thus ?thesis using eq by auto
    next
      case 2
      have sp_nonempty: "steps (translated_step_proof r s) \<noteq> []"
        and sp_last: "thesis (translated_step_proof r s)
                    = last (steps (translated_step_proof r s))"
        using sp_valid unfolding valid_proof_def by blast+
      have "thesis (translated_step_proof r s) \<in> set (steps (translated_step_proof r s))"
        using sp_last sp_nonempty by simp
      hence "translate_formula (steps pr ! k) \<in> set (steps (translated_step_proof r s))"
        using sp_thesis concl_eq by simp
      thus ?thesis using 2 fi q_eq eq by auto
    qed
  qed
  show ?thesis
    using assm_next valid_next thesis_next steps_next by simp
qed

lemma simulation_proof_proves:
  assumes valid_pr: "valid_proof Fone pr"
      and assm_pr: "assumptions pr = {}"
      and wf_steps: "\<forall> st \<in> set (steps pr). formula_well_formed (alphabet Fone) st"
      and pr2_eq: "pr2 = simulation_proof pr (translate_formula (thesis pr))"
  shows "valid_proof Ftwo pr2
       \<and> thesis pr2 = translate_formula (thesis pr)
       \<and> assumptions pr2 = {}"
proof -
  let ?init = "\<lparr> assumptions = {}, thesis = translate_formula (thesis pr), steps = [] \<rparr>
                 :: 'c2 frege_proof"
  let ?acc = "\<lambda> k. fold (simulation_step pr) [0..<k] ?init"
  let ?n = "length (steps pr)"
  have prefix_inv:
    "\<forall> k \<le> ?n. assumptions (?acc k) = {}
       \<and> translate_formula ` set (take k (steps pr)) \<subseteq> set (steps (?acc k))
       \<and> (k = 0 \<or> (valid_proof Ftwo (?acc k)
             \<and> thesis (?acc k) = translate_formula (steps pr ! (k - 1))))"
  proof (intro allI impI)
    fix k
    assume k_le: "k \<le> ?n"
    show "assumptions (?acc k) = {}
       \<and> translate_formula ` set (take k (steps pr)) \<subseteq> set (steps (?acc k))
       \<and> (k = 0 \<or> (valid_proof Ftwo (?acc k)
             \<and> thesis (?acc k) = translate_formula (steps pr ! (k - 1))))"
      using k_le
    proof (induction k)
      case 0
      show ?case by simp
    next
      case (Suc k)
      have IH: "assumptions (?acc k) = {}
         \<and> translate_formula ` set (take k (steps pr)) \<subseteq> set (steps (?acc k))
         \<and> (k = 0 \<or> (valid_proof Ftwo (?acc k)
               \<and> thesis (?acc k) = translate_formula (steps pr ! (k - 1))))"
        using Suc.IH Suc.prems by simp
      have k_lt: "k < ?n" using Suc.prems by simp
      have acc0: "k = 0 \<longrightarrow> steps (?acc k) = []"
        by (cases k) simp_all
      have step_prog:
        "assumptions (simulation_step pr k (?acc k)) = {}
       \<and> valid_proof Ftwo (simulation_step pr k (?acc k))
       \<and> thesis (simulation_step pr k (?acc k)) = translate_formula (steps pr ! k)
       \<and> translate_formula ` set (take (Suc k) (steps pr))
           \<subseteq> set (steps (simulation_step pr k (?acc k)))"
        using simulation_step_progress[of pr k "?acc k"]
              valid_pr assm_pr wf_steps k_lt acc0 IH by blast
      show ?case
        using step_prog by simp
    qed
  qed
  have final_assm: "assumptions (?acc ?n) = {}"
    using prefix_inv by simp
  have n_pos: "?n \<noteq> 0"
    using valid_pr unfolding valid_proof_def by auto
  have final_valid: "valid_proof Ftwo (?acc ?n)"
    using prefix_inv n_pos by auto
  have final_thesis: "thesis (?acc ?n) = translate_formula (thesis pr)"
  proof -
    have "thesis (?acc ?n) = translate_formula (steps pr ! (?n - 1))"
      using prefix_inv n_pos by auto
    also have "\<dots> = translate_formula (last (steps pr))"
      using valid_pr unfolding valid_proof_def by (simp add: last_conv_nth)
    also have "\<dots> = translate_formula (thesis pr)"
      using valid_pr unfolding valid_proof_def by simp
    finally show ?thesis .
  qed
  show ?thesis
    using pr2_eq final_assm final_valid final_thesis
    unfolding simulation_proof_def by auto
qed

subsection \<open>Length bounds\<close>

definition rule_simulation_bound :: nat where
  "rule_simulation_bound
     = Max (insert 1 ((\<lambda> r. len_proof (translated_rule_proof r) * (card (var_set_rule r) + 1))
                      ` well_formed_rules))"

lemma rule_simulation_bound_ge:
  assumes "r \<in> well_formed_rules"
  shows "len_proof (translated_rule_proof r) * (card (var_set_rule r) + 1)
       \<le> rule_simulation_bound"
  unfolding rule_simulation_bound_def
  using well_formed_rules_finite assms by (intro Max_ge) auto

lemma rule_simulation_bound_positive:
  "1 \<le> rule_simulation_bound"
  unfolding rule_simulation_bound_def
  using well_formed_rules_finite by (intro Max_ge) auto

lemma translated_substitution_length_bound:
  assumes r_in: "r \<in> well_formed_rules"
      and dw: "derived_with i pr r s"
      and valid: "valid_proof Fone pr"
      and wf_steps: "\<forall> st \<in> set (steps pr). formula_well_formed (alphabet Fone) st"
      and depth_steps: "\<forall> st \<in> set (steps pr). depth_formula st \<le> D"
  shows "len_sub (var_set_rule r) (\<lambda>u. translate_formula (s u))
       \<le> template_length_bound ^ D * ((card (var_set_rule r) + 1) * len_proof pr)"
proof -
  have per_var: "len_formula (translate_formula (s v))
               \<le> template_length_bound ^ D * len_proof pr"
    if v_in: "v \<in> var_set_rule r" for v
  proof -
    have "\<exists> h. (h = concl r \<or> h \<in> set (prems r)) \<and> v \<in> var_set_form h"
      using v_in by auto
    then obtain h where h_cases: "h = concl r \<or> h \<in> set (prems r)"
      and v_h: "v \<in> var_set_form h" by blast
    have inst_in_steps: "sub_formula s h \<in> set (steps pr)"
    proof (cases "h = concl r")
      case True
      have ceq: "concl (sub_rule s r) = steps pr ! i" and ilt: "i < length (steps pr)"
        using dw unfolding derived_with_def by blast+
      have "sub_formula s (concl r) = steps pr ! i"
        using ceq by simp
      hence "sub_formula s (concl r) \<in> set (steps pr)"
        using ilt by simp
      thus ?thesis using True by simp
    next
      case False
      hence h_prem: "h \<in> set (prems r)" using h_cases by blast
      have "sub_formula s h \<in> set (prems (sub_rule s r))"
        using h_prem by simp
      then obtain q where q_in: "q \<in> set (take i (steps pr))"
        and q_eq: "sub_formula s h = q"
        using dw unfolding derived_with_def by blast
      show ?thesis using q_in q_eq by (auto dest: in_set_takeD)
    qed
    have inst_wf: "formula_well_formed (alphabet Fone) (sub_formula s h)"
      using wf_steps inst_in_steps by blast
    have inst_depth: "depth_formula (sub_formula s h) \<le> D"
      using depth_steps inst_in_steps by blast
    have inst_len: "len_formula (sub_formula s h) \<le> len_proof pr"
      using step_length_le_proof inst_in_steps by blast
    have sv_wf: "formula_well_formed (alphabet Fone) (s v)"
      by (rule substitution_value_well_formed[OF v_h inst_wf])
    have sv_depth: "depth_formula (s v) \<le> D"
      using substitution_value_depth[OF v_h] inst_depth by (rule order_trans)
    have sv_len: "len_formula (s v) \<le> len_proof pr"
      using substitution_value_length[OF v_h] inst_len by (rule order_trans)
    have "len_formula (translate_formula (s v))
        \<le> template_length_bound ^ D * len_formula (s v)"
      by (rule translate_formula_length[OF sv_wf sv_depth])
    also have "\<dots> \<le> template_length_bound ^ D * len_proof pr"
      using sv_len by (intro mult_le_mono2)
    finally show ?thesis .
  qed
  have sum_bound: "(\<Sum> v \<in> var_set_rule r. len_formula (translate_formula (s v)))
                 \<le> card (var_set_rule r) * (template_length_bound ^ D * len_proof pr)"
  proof -
    have "(\<Sum> v \<in> var_set_rule r. len_formula (translate_formula (s v)))
        \<le> of_nat (card (var_set_rule r)) * (template_length_bound ^ D * len_proof pr)"
      using per_var by (intro sum_bounded_above) blast
    thus ?thesis by simp
  qed
  have lp1: "1 \<le> len_proof pr"
    by (rule len_proof_positive[OF valid])
  have T1: "(1 :: nat) \<le> template_length_bound ^ D"
    using template_length_bound_positive by (rule one_le_power)
  have TD_lp: "1 \<le> template_length_bound ^ D * len_proof pr"
    using mult_le_mono[OF T1 lp1] by simp
  have first_le: "1 \<le> (card (var_set_rule r) + 1) * (template_length_bound ^ D * len_proof pr)"
  proof -
    have "(1 :: nat) * 1 \<le> (card (var_set_rule r) + 1) * (template_length_bound ^ D * len_proof pr)"
      using TD_lp by (intro mult_le_mono) simp_all
    thus ?thesis by simp
  qed
  have second_le: "card (var_set_rule r) * (template_length_bound ^ D * len_proof pr)
                 \<le> (card (var_set_rule r) + 1) * (template_length_bound ^ D * len_proof pr)"
    by (intro mult_le_mono1) simp
  have "len_sub (var_set_rule r) (\<lambda>u. translate_formula (s u))
      = max 1 (\<Sum> v \<in> var_set_rule r. len_formula (translate_formula (s v)))"
    unfolding len_sub_def ..
  also have "\<dots> \<le> (card (var_set_rule r) + 1) * (template_length_bound ^ D * len_proof pr)"
    using sum_bound first_le second_le by simp
  also have "\<dots> = template_length_bound ^ D * ((card (var_set_rule r) + 1) * len_proof pr)"
    by (simp add: algebra_simps)
  finally show ?thesis .
qed

lemma translated_step_proof_length:
  assumes r_in: "r \<in> well_formed_rules"
      and dw: "derived_with i pr r s"
      and restricted: "rule_restricted_sub r s"
      and valid: "valid_proof Fone pr"
      and wf_steps: "\<forall> st \<in> set (steps pr). formula_well_formed (alphabet Fone) st"
      and depth_steps: "\<forall> st \<in> set (steps pr). depth_formula st \<le> D"
  shows "len_proof (translated_step_proof r s)
       \<le> template_length_bound ^ D * (rule_simulation_bound * len_proof pr)"
proof -
  have sigma_outside: "\<forall> v. v \<notin> var_set_rule r \<longrightarrow> translate_formula (s v) = Atom v"
    using restricted unfolding rule_restricted_sub_def by simp
  have "len_proof (translated_step_proof r s)
      \<le> len_proof (translated_rule_proof r)
        * len_sub (var_set_rule r) (\<lambda>u. translate_formula (s u))"
    unfolding translated_step_proof_def
    using finite_var_set_rule sigma_outside by (intro sub_proof_bound) simp_all
  also have "\<dots> \<le> len_proof (translated_rule_proof r)
                * (template_length_bound ^ D * ((card (var_set_rule r) + 1) * len_proof pr))"
    using translated_substitution_length_bound[OF r_in dw valid wf_steps depth_steps]
    by (intro mult_le_mono2)
  also have "\<dots> = template_length_bound ^ D
                * ((len_proof (translated_rule_proof r) * (card (var_set_rule r) + 1))
                   * len_proof pr)"
    by (simp add: algebra_simps)
  also have "\<dots> \<le> template_length_bound ^ D * (rule_simulation_bound * len_proof pr)"
    using rule_simulation_bound_ge[OF r_in] by (intro mult_le_mono2 mult_le_mono1)
  finally show ?thesis .
qed

lemma simulation_step_length:
  assumes valid: "valid_proof Fone pr"
      and assm_pr: "assumptions pr = {}"
      and wf_steps: "\<forall> st \<in> set (steps pr). formula_well_formed (alphabet Fone) st"
      and depth_steps: "\<forall> st \<in> set (steps pr). depth_formula st \<le> D"
      and k_lt: "k < length (steps pr)"
  shows "len_proof (simulation_step pr k acc)
       \<le> template_length_bound ^ D * (rule_simulation_bound * len_proof pr) + len_proof acc"
proof -
  have step_not_assm: "steps pr ! k \<notin> assumptions pr"
    using assm_pr by simp
  have ex_rs: "\<exists> r s. r \<in> well_formed_rules \<and> derived_with k pr r s"
    by (rule valid_proof_well_formed_rules[OF valid wf_steps k_lt step_not_assm])
  define r where "r = fst (choose_rule_substitution well_formed_rules k pr)"
  define s where "s = snd (choose_rule_substitution well_formed_rules k pr)"
  have r_in: "r \<in> well_formed_rules"
    and dchoose: "derived_with k pr r s"
    and restricted: "rule_restricted_sub r s"
    using choose_rule_substitution_spec[OF ex_rs] unfolding r_def s_def by blast+
  have eq: "simulation_step pr k acc = combine_proofs acc (translated_step_proof r s)"
  proof (cases "choose_rule_substitution well_formed_rules k pr")
    case (Pair r' s')
    thus ?thesis
      unfolding simulation_step_def r_def s_def by simp
  qed
  have "len_proof (simulation_step pr k acc)
      = len_proof acc + len_proof (translated_step_proof r s)"
    using eq by simp
  also have "\<dots> \<le> len_proof acc
                + template_length_bound ^ D * (rule_simulation_bound * len_proof pr)"
    using translated_step_proof_length[OF r_in dchoose restricted valid wf_steps depth_steps]
    by (intro add_left_mono)
  finally show ?thesis by simp
qed

lemma simulation_proof_length:
  assumes valid: "valid_proof Fone pr"
      and assm_pr: "assumptions pr = {}"
      and wf_steps: "\<forall> st \<in> set (steps pr). formula_well_formed (alphabet Fone) st"
      and depth_steps: "\<forall> st \<in> set (steps pr). depth_formula st \<le> D"
  shows "len_proof (simulation_proof pr goal)
       \<le> length (steps pr) * (template_length_bound ^ D * (rule_simulation_bound * len_proof pr))"
proof -
  let ?init = "\<lparr> assumptions = {}, thesis = goal, steps = [] \<rparr> :: 'c2 frege_proof"
  let ?acc = "\<lambda> k. fold (simulation_step pr) [0..<k] ?init"
  let ?stepcost = "template_length_bound ^ D * (rule_simulation_bound * len_proof pr)"
  have prefix_bound: "k \<le> length (steps pr) \<Longrightarrow> len_proof (?acc k) \<le> k * ?stepcost" for k
  proof (induction k)
    case 0
    show ?case by simp
  next
    case (Suc k)
    have k_lt: "k < length (steps pr)" using Suc.prems by simp
    have acc_eq: "?acc (Suc k) = simulation_step pr k (?acc k)"
      by simp
    have "len_proof (simulation_step pr k (?acc k)) \<le> ?stepcost + len_proof (?acc k)"
      by (rule simulation_step_length[OF valid assm_pr wf_steps depth_steps k_lt])
    also have "\<dots> \<le> ?stepcost + k * ?stepcost"
      using Suc.IH Suc.prems by simp
    also have "\<dots> = Suc k * ?stepcost"
      by simp
    finally show ?case using acc_eq by simp
  qed
  have "len_proof (simulation_proof pr goal) = len_proof (?acc (length (steps pr)))"
    unfolding simulation_proof_def by simp
  also have "\<dots> \<le> length (steps pr) * ?stepcost"
    by (rule prefix_bound) simp
  finally show ?thesis .
qed

subsection \<open>The simulation theorem\<close>

theorem translated_proof_simulation:
  shows "\<exists> (szbound :: nat poly) (T :: nat). 1 \<le> T \<and>
     (\<forall> pr D. valid_proof Fone pr \<and> assumptions pr = {}
         \<and> (\<forall> st \<in> set (steps pr). formula_well_formed (alphabet Fone) st)
         \<and> (\<forall> st \<in> set (steps pr). depth_formula st \<le> D)
       \<longrightarrow> (\<exists> pr2. valid_proof Ftwo pr2
             \<and> assumptions pr2 = {}
             \<and> thesis pr2 = translate_formula (thesis pr)
             \<and> len_proof pr2 \<le> T ^ D * poly szbound (len_proof pr)))"
proof -
  define szbound :: "nat poly" where "szbound = monom rule_simulation_bound 2"
  have poly_eval: "poly szbound n = rule_simulation_bound * n ^ 2" for n
    unfolding szbound_def by (simp add: poly_monom)
  have main: "\<forall> pr D. valid_proof Fone pr \<and> assumptions pr = {}
         \<and> (\<forall> st \<in> set (steps pr). formula_well_formed (alphabet Fone) st)
         \<and> (\<forall> st \<in> set (steps pr). depth_formula st \<le> D)
       \<longrightarrow> (\<exists> pr2. valid_proof Ftwo pr2
             \<and> assumptions pr2 = {}
             \<and> thesis pr2 = translate_formula (thesis pr)
             \<and> len_proof pr2 \<le> template_length_bound ^ D * poly szbound (len_proof pr))"
  proof (intro allI impI)
    fix pr :: "'c1 frege_proof" and D :: nat
    assume A: "valid_proof Fone pr \<and> assumptions pr = {}
         \<and> (\<forall> st \<in> set (steps pr). formula_well_formed (alphabet Fone) st)
         \<and> (\<forall> st \<in> set (steps pr). depth_formula st \<le> D)"
    have valid: "valid_proof Fone pr"
      and assm_pr: "assumptions pr = {}"
      and wf_steps: "\<forall> st \<in> set (steps pr). formula_well_formed (alphabet Fone) st"
      and depth_steps: "\<forall> st \<in> set (steps pr). depth_formula st \<le> D"
      using A by blast+
    define pr2 where "pr2 = simulation_proof pr (translate_formula (thesis pr))"
    have props: "valid_proof Ftwo pr2
               \<and> thesis pr2 = translate_formula (thesis pr)
               \<and> assumptions pr2 = {}"
      by (rule simulation_proof_proves[OF valid assm_pr wf_steps pr2_def])
    have "len_proof pr2
        \<le> length (steps pr) * (template_length_bound ^ D * (rule_simulation_bound * len_proof pr))"
      unfolding pr2_def
      by (rule simulation_proof_length[OF valid assm_pr wf_steps depth_steps])
    also have "\<dots> \<le> len_proof pr * (template_length_bound ^ D * (rule_simulation_bound * len_proof pr))"
      using steps_count_le_proof_length by (intro mult_le_mono1)
    also have "\<dots> = template_length_bound ^ D * (rule_simulation_bound * (len_proof pr) ^ 2)"
      by (simp add: power2_eq_square algebra_simps)
    also have "\<dots> = template_length_bound ^ D * poly szbound (len_proof pr)"
      using poly_eval by simp
    finally have len: "len_proof pr2 \<le> template_length_bound ^ D * poly szbound (len_proof pr)" .
    show "\<exists> pr2. valid_proof Ftwo pr2
             \<and> assumptions pr2 = {}
             \<and> thesis pr2 = translate_formula (thesis pr)
             \<and> len_proof pr2 \<le> template_length_bound ^ D * poly szbound (len_proof pr)"
      using props len by blast
  qed
  show ?thesis
  proof (rule exI[where x = szbound], rule exI[where x = template_length_bound], intro conjI)
    show "1 \<le> template_length_bound"
      by (rule template_length_bound_positive)
    show "\<forall> pr D. valid_proof Fone pr \<and> assumptions pr = {}
         \<and> (\<forall> st \<in> set (steps pr). formula_well_formed (alphabet Fone) st)
         \<and> (\<forall> st \<in> set (steps pr). depth_formula st \<le> D)
       \<longrightarrow> (\<exists> pr2. valid_proof Ftwo pr2
             \<and> assumptions pr2 = {}
             \<and> thesis pr2 = translate_formula (thesis pr)
             \<and> len_proof pr2 \<le> template_length_bound ^ D * poly szbound (len_proof pr))"
      by (rule main)
  qed
qed

corollary translated_thesis_length:
  assumes valid: "valid_proof Fone pr"
      and wf_steps: "\<forall> st \<in> set (steps pr). formula_well_formed (alphabet Fone) st"
      and depth_steps: "\<forall> st \<in> set (steps pr). depth_formula st \<le> D"
  shows "len_formula (translate_formula (thesis pr))
       \<le> template_length_bound ^ D * len_formula (thesis pr)"
proof -
  have thesis_in: "thesis pr \<in> set (steps pr)"
    using valid unfolding valid_proof_def by simp
  have "formula_well_formed (alphabet Fone) (thesis pr)"
    using wf_steps thesis_in by blast
  moreover have "depth_formula (thesis pr) \<le> D"
    using depth_steps thesis_in by blast
  ultimately show ?thesis
    by (rule translate_formula_length)
qed

subsection \<open>Phase E: the reverse translation, roundtrip, and final assembly\<close>

text \<open>
  The reverse leg (Ftwo-formula to Fone-formula) is just \<^const>\<open>translate_formula\<close>
  under the SYMMETRIC pair, obtained by locally interpreting frege_pair with the
  two systems swapped.  Everything Phase B proved generically (well-formedness,
  semantic equivalence, the length and depth bounds) becomes available for free
  as \<^text>\<open>rev.translate_formula\<close>, \<^text>\<open>rev.translate_formula_length\<close>, etc.
\<close>

sublocale rev: frege_pair Ftwo Fone
  by unfold_locales

lemma rev_translate_formula_wf:
  "formula_well_formed (alphabet Fone) (rev.translate_formula \<tau>)"
  by (rule rev.translate_formula_well_formed)

lemma rev_translate_formula_equiv:
  assumes "formula_well_formed (alphabet Ftwo) \<tau>"
  shows "formulas_equiv \<tau> (alphabet Ftwo) (rev.translate_formula \<tau>) (alphabet Fone)"
  using rev.translate_formula_equiv[OF assms] .

text \<open>
  \<^text>\<open>frege_closure\<close> needs only \<^text>\<open>frege_system F\<close>: it is a plain extension of
  \<^text>\<open>frege_balancing\<close>, whose sole assumption is \<^text>\<open>frege_system F\<close>.  In
  particular no \<^text>\<open>conn_closed\<close> assumption is involved -- the arity-reducing
  \<^text>\<open>conn_fix\<close> identity is the only part of Section6 that needs closure, and it
  carries \<^text>\<open>conn_closed (alphabet F)\<close> as an explicit hypothesis rather than as a
  locale assumption; the Spira-balancing development itself goes through the
  arity-preserving \<^text>\<open>shc_subst_cons\<close> and \<^text>\<open>collapse_open\<close>.

  Interpreting the FULL closure locale at Ftwo -- and not merely
  \<^text>\<open>frege_balancing\<close> -- is what makes \<^text>\<open>two_bal.transform_commutes_form\<close>
  available here, i.e. an Ftwo-proof of \<open>spira_trans \<tau> \<leftrightarrow> \<tau>\<close>.  Ftwo is an arbitrary
  Frege system, so this is exactly the step that undoes the balancing INSIDE Ftwo and
  lets the last leg of Reckhow's theorem stay there.  Everything the roundtrip
  construction below inherited before -- \<^text>\<open>entails_proof\<close>, \<^text>\<open>iff_form\<close>,
  \<^text>\<open>provable_balanced_iff\<close>, \<^text>\<open>iff_trans\<close>, \<^text>\<open>iff_refl\<close>,
  \<^text>\<open>plug_cong\<close>, \<^text>\<open>conn_slot_cong\<close> -- remains available under the same
  \<^text>\<open>two_bal.\<close> prefix.
\<close>
sublocale two_bal: frege_closure Ftwo
  by unfold_locales

text \<open>
  The same interpretation on the SOURCE side.  Since \<^text>\<open>frege_closure\<close> is
  assumption-free, Fone can be balanced where it stands: the proof to be simulated never
  has to be pushed through a closed extension of Fone and renamed back, which is what the
  original argument did.  In particular \<^text>\<open>one_bal.proof_balancing\<close> applies to an
  arbitrary Fone-proof directly.
\<close>
sublocale one_bal: frege_closure Fone
  by unfold_locales

subsection \<open>The reverse formula translation g and its polynomial size bound\<close>

text \<open>
  The translation \<^text>\<open>rev.translate_formula\<close> replaces each connective by a fixed
  template, so its size bound carries a factor \<^text>\<open>T ^ depth\<close>, which is NOT
  polynomial in the formula size on its own -- exactly Krajicek's nesting example
  (Basic propositional logic, p.48-49: translating a k-fold nesting of \<open>\<equiv>\<close> blows up
  to size \<open>\<Omega>(2\<^sup>k)\<close>).  Balancing the formula FIRST with Spira's transformation makes
  the depth logarithmic (\<^text>\<open>two_bal.trans_c\<close>) while keeping the size polynomial
  (\<^text>\<open>two_bal.trans_b\<close>), and then \<open>T ^ O(log n)\<close> is polynomial -- which is what
  \<^text>\<open>power_ceiling_log_poly_bound\<close> delivers.  This is the reverse leg g required
  by clause (A) of \<^const>\<open>simulates\<close>.
\<close>

definition reverse_translate :: "'c2 formula \<Rightarrow> 'c1 formula" where
  "reverse_translate \<tau> = rev.translate_formula (two_bal.spira_trans \<tau>)"

lemma reverse_translate_well_formed:
  "formula_well_formed (alphabet Fone) (reverse_translate \<tau>)"
  unfolding reverse_translate_def by (rule rev.translate_formula_well_formed)

lemma reverse_translate_equiv:
  assumes wf: "formula_well_formed (alphabet Ftwo) \<tau>"
  shows "formulas_equiv (reverse_translate \<tau>) (alphabet Fone) \<tau> (alphabet Ftwo)"
proof -
  have spira_wf: "formula_well_formed (alphabet Ftwo) (two_bal.spira_trans \<tau>)"
    by (rule two_bal.spira_trans_wf[OF wf])
  have spira_eval: "\<And>val. eval (alphabet Ftwo) val \<tau>
                        = eval (alphabet Ftwo) val (two_bal.spira_trans \<tau>)"
    using two_bal.spira_trans_dom_and_eval[OF wf] by blast
  have tr_eq: "formulas_equiv (two_bal.spira_trans \<tau>) (alphabet Ftwo)
                 (rev.translate_formula (two_bal.spira_trans \<tau>)) (alphabet Fone)"
    by (rule rev.translate_formula_equiv[OF spira_wf])
  show ?thesis
    unfolding reverse_translate_def formulas_equiv_def
    using tr_eq spira_eval unfolding formulas_equiv_def by simp
qed

lemma reverse_translate_length:
  "\<exists> p :: nat poly. \<forall> \<tau>. formula_well_formed (alphabet Ftwo) \<tau>
      \<longrightarrow> len_formula (reverse_translate \<tau>) \<le> poly p (len_formula \<tau>)"
proof -
  define T where "T = rev.template_length_bound"
  have T1: "1 \<le> T" unfolding T_def by (rule rev.template_length_bound_positive)
  \<comment> \<open>Spira: polynomial size, logarithmic depth\<close>
  obtain szp :: "nat poly" where szp:
    "\<And>f. formula_well_formed (alphabet Ftwo) f
         \<Longrightarrow> len_formula (two_bal.spira_trans f) \<le> poly szp (len_formula f)"
    using two_bal.trans_b by blast
  obtain c :: real where c_bound:
    "\<And>f. formula_well_formed (alphabet Ftwo) f
         \<Longrightarrow> real (depth_formula (two_bal.spira_trans f))
             \<le> c * log 2 (real (len_formula f) + 1)"
    using two_bal.trans_c by blast
  define c' :: real where "c' = max c 0"
  have c'_nn: "0 \<le> c'" unfolding c'_def by simp
  have c'_bound: "\<And>f. formula_well_formed (alphabet Ftwo) f
         \<Longrightarrow> real (depth_formula (two_bal.spira_trans f))
             \<le> c' * log 2 (real (len_formula f) + 1)"
  proof -
    fix f assume wf: "formula_well_formed (alphabet Ftwo) f"
    have log_nn: "0 \<le> log 2 (real (len_formula f) + 1)" by simp
    have "c * log 2 (real (len_formula f) + 1) \<le> c' * log 2 (real (len_formula f) + 1)"
      unfolding c'_def using log_nn by (intro mult_right_mono) simp_all
    thus "real (depth_formula (two_bal.spira_trans f))
          \<le> c' * log 2 (real (len_formula f) + 1)"
      using c_bound[OF wf] by linarith
  qed
  \<comment> \<open>T ^ (logarithmic depth) is polynomial\<close>
  obtain dp :: "nat poly" where dp:
    "\<And>n :: nat. T ^ (nat \<lceil>0 + c' * log 2 (real n + 1)\<rceil>) \<le> T ^ (nat \<lceil>0::real\<rceil> + 1) * poly dp n"
    using power_ceiling_log_poly_bound[OF T1 _ c'_nn, of 0] by auto
  define p :: "nat poly" where "p = [:T:] * dp * szp"
  have poly_p: "\<And>n. poly p n = T * poly dp n * poly szp n"
    unfolding p_def by simp
  show ?thesis
  proof (rule exI[of _ p], intro allI impI)
    fix \<tau> :: "'c2 formula"
    assume wf: "formula_well_formed (alphabet Ftwo) \<tau>"
    define L where "L = len_formula \<tau>"
    define s where "s = two_bal.spira_trans \<tau>"
    have s_wf: "formula_well_formed (alphabet Ftwo) s"
      unfolding s_def by (rule two_bal.spira_trans_wf[OF wf])
    have s_len: "len_formula s \<le> poly szp L"
      unfolding s_def L_def by (rule szp[OF wf])
    \<comment> \<open>the translation's own bound, at the depth of the balanced formula\<close>
    have step1: "len_formula (reverse_translate \<tau>) \<le> T ^ (depth_formula s) * len_formula s"
      unfolding reverse_translate_def s_def T_def
      by (rule rev.translate_formula_length[OF s_wf[unfolded s_def] order.refl])
    \<comment> \<open>the depth is at most the ceiling of the logarithmic bound\<close>
    have dep_le: "depth_formula s \<le> nat \<lceil>0 + c' * log 2 (real L + 1)\<rceil>"
    proof -
      have "real (depth_formula s) \<le> c' * log 2 (real L + 1)"
        unfolding s_def L_def using c'_bound[OF wf] .
      hence "real (depth_formula s) \<le> real_of_int \<lceil>0 + c' * log 2 (real L + 1)\<rceil>"
        by linarith
      thus ?thesis by linarith
    qed
    have pow_le: "T ^ (depth_formula s) \<le> T ^ (nat \<lceil>0 + c' * log 2 (real L + 1)\<rceil>)"
      by (rule power_increasing[OF dep_le T1])
    have pow_poly: "T ^ (nat \<lceil>0 + c' * log 2 (real L + 1)\<rceil>) \<le> T * poly dp L"
      using dp[of L] by simp
    have "len_formula (reverse_translate \<tau>) \<le> T ^ (depth_formula s) * len_formula s"
      by (rule step1)
    also have "\<dots> \<le> (T * poly dp L) * poly szp L"
      using pow_le pow_poly s_len by (intro mult_mono) simp_all
    also have "\<dots> = poly p L"
      using poly_p by simp
    finally show "len_formula (reverse_translate \<tau>) \<le> poly p (len_formula \<tau>)"
      unfolding L_def .
  qed
qed

subsection \<open>Modus ponens conversion inside Ftwo\<close>

text \<open>
  Section7's \<^text>\<open>iff_elimination\<close> lives in \<^text>\<open>frege_closure\<close>, but its proof
  only ever uses \<^text>\<open>frege_balancing\<close>-level material (\<^text>\<open>entails_proof\<close>,
  \<^text>\<open>iff_form\<close>, the two fresh symmetry atoms, and \<^text>\<open>proof_substitution\<close>).
  Ftwo is an arbitrary Frege system and need not be closed, so the converter is
  rebuilt here over \<^text>\<open>two_bal\<close>.  The base proof is taken over two ATOMS, so its
  size is a constant of Ftwo; instantiating it by substitution is what keeps the size
  of the conversion linear in \<^term>\<open>len_formula A + len_formula B\<close>.
\<close>

definition two_mp_base :: "'c2 frege_proof" where
  "two_mp_base = two_bal.entails_proof
       {Atom two_bal.sym_atom_x,
        two_bal.iff_form (Atom two_bal.sym_atom_x) (Atom two_bal.sym_atom_y)}
       (Atom two_bal.sym_atom_y)"

lemma two_mp_base_spec:
  "valid_proof Ftwo two_mp_base
   \<and> assumptions two_mp_base
       = {Atom two_bal.sym_atom_x,
          two_bal.iff_form (Atom two_bal.sym_atom_x) (Atom two_bal.sym_atom_y)}
   \<and> thesis two_mp_base = Atom two_bal.sym_atom_y
   \<and> (\<forall>st \<in> set (steps two_mp_base). formula_well_formed (alphabet Ftwo) st)"
proof -
  have sem: "\<forall>val. (\<forall>f \<in> {Atom two_bal.sym_atom_x,
                    two_bal.iff_form (Atom two_bal.sym_atom_x) (Atom two_bal.sym_atom_y)}.
                eval (alphabet Ftwo) val f)
              \<longrightarrow> eval (alphabet Ftwo) val (Atom two_bal.sym_atom_y)"
    using two_bal.iff_form_eval by auto
  have wf_fs: "\<forall>f \<in> {Atom two_bal.sym_atom_x,
                     two_bal.iff_form (Atom two_bal.sym_atom_x) (Atom two_bal.sym_atom_y)}.
                 formula_well_formed (alphabet Ftwo) f"
    by (auto intro: two_bal.iff_form_wf)
  have wf_th: "formula_well_formed (alphabet Ftwo) (Atom two_bal.sym_atom_y)" by simp
  show ?thesis
    unfolding two_mp_base_def
    using two_bal.entails_proof_spec[OF wf_fs wf_th sem] .
qed

lemma two_iff_elimination:
  assumes vA: "valid_proof Ftwo pa" and aA: "assumptions pa = {}" and tA: "thesis pa = A"
      and vI: "valid_proof Ftwo pii" and aI: "assumptions pii = {}"
      and tI: "thesis pii = two_bal.iff_form A B"
    shows "\<exists> pr. valid_proof Ftwo pr \<and> assumptions pr = {} \<and> thesis pr = B
              \<and> len_proof pr \<le> len_proof pa + len_proof pii
                  + len_proof two_mp_base * max 1 (len_formula A + len_formula B)"
proof -
  let ?x = "two_bal.sym_atom_x" and ?y = "two_bal.sym_atom_y"
  let ?sub = "\<lambda>w. if w = ?x then A else if w = ?y then B else Atom w"
  have neq: "?x \<noteq> ?y" using two_bal.sym_atoms_spec by blast
  have sub_conn_iff:
    "\<And>w. w \<in> var_set_form two_bal.conn_iff \<Longrightarrow> w \<noteq> ''a'' \<Longrightarrow> w \<noteq> ''b'' \<Longrightarrow> ?sub w = Atom w"
  proof -
    fix w assume w_ci: "w \<in> var_set_form two_bal.conn_iff" and "w \<noteq> ''a''" and "w \<noteq> ''b''"
    have "w \<in> two_bal.avoid_atoms" using w_ci unfolding two_bal.avoid_atoms_def by blast
    hence "w \<noteq> ?x \<and> w \<noteq> ?y" using two_bal.sym_atoms_spec by blast
    thus "?sub w = Atom w" by simp
  qed
  define mi where mi_def: "mi = sub_proof ?sub two_mp_base"
  have valid_mi: "valid_proof Ftwo mi"
    unfolding mi_def using two.proof_substitution two_mp_base_spec by blast
  have mi_thesis: "thesis mi = B"
  proof -
    have "thesis mi = sub_formula ?sub (Atom ?y)"
      unfolding mi_def using two_mp_base_spec by simp
    thus ?thesis using neq by simp
  qed
  have sub_iff: "sub_formula ?sub (two_bal.iff_form (Atom ?x) (Atom ?y))
               = two_bal.iff_form A B"
  proof -
    have "sub_formula ?sub (two_bal.iff_form (Atom ?x) (Atom ?y))
        = two_bal.iff_form (sub_formula ?sub (Atom ?x)) (sub_formula ?sub (Atom ?y))"
      by (rule two_bal.sub_formula_iff_form[OF sub_conn_iff])
    also have "\<dots> = two_bal.iff_form A B" using neq by simp
    finally show ?thesis .
  qed
  have mi_asm: "assumptions mi = {A, two_bal.iff_form A B}"
  proof -
    have "assumptions mi = (sub_formula ?sub) ` (assumptions two_mp_base)"
      unfolding mi_def by simp
    also have "\<dots> = (sub_formula ?sub) `
         {Atom ?x, two_bal.iff_form (Atom ?x) (Atom ?y)}"
      using two_mp_base_spec by simp
    also have "\<dots> = {A, two_bal.iff_form A B}" using sub_iff by simp
    finally show ?thesis .
  qed
  \<comment> \<open>glue the two premise proofs together, then discharge both assumptions of mi\<close>
  define pre where pre_def: "pre = combine_proofs pa pii"
  have valid_pre: "valid_proof Ftwo pre"
    unfolding pre_def using two.combining_valid_proofs vA vI by blast
  have pre_asm: "assumptions pre = {}"
    unfolding pre_def using aA aI by simp
  have pre_steps: "steps pre = steps pa @ steps pii"
    unfolding pre_def by simp
  have A_in: "A \<in> set (steps pre)"
  proof -
    have "thesis pa \<in> set (steps pa)" using vA unfolding valid_proof_def by simp
    thus ?thesis using tA pre_steps by simp
  qed
  have I_in: "two_bal.iff_form A B \<in> set (steps pre)"
  proof -
    have "thesis pii \<in> set (steps pii)" using vI unfolding valid_proof_def by simp
    thus ?thesis using tI pre_steps by simp
  qed
  define pr where pr_def: "pr = combine_proofs pre mi"
  have valid_pr: "valid_proof Ftwo pr"
    unfolding pr_def using two.combining_valid_proofs valid_pre valid_mi by blast
  have pr_asm: "assumptions pr = {}"
  proof -
    have "assumptions pr = assumptions pre \<union> (assumptions mi - set (steps pre))"
      unfolding pr_def by simp
    also have "\<dots> = {} \<union> ({A, two_bal.iff_form A B} - set (steps pre))"
      using pre_asm mi_asm by simp
    also have "\<dots> = {}" using A_in I_in by blast
    finally show ?thesis .
  qed
  have pr_thesis: "thesis pr = B"
    unfolding pr_def using mi_thesis by simp
  have len_mi: "len_proof mi \<le> len_proof two_mp_base * max 1 (len_formula A + len_formula B)"
  proof -
    have fin: "finite {?x, ?y}" by simp
    have outside: "\<forall>v. v \<notin> {?x, ?y} \<longrightarrow> ?sub v = Atom v" by auto
    have "len_proof (sub_proof ?sub two_mp_base)
        \<le> len_proof two_mp_base * len_sub {?x, ?y} ?sub"
      by (rule sub_proof_bound[OF fin outside])
    moreover have "len_sub {?x, ?y} ?sub = max 1 (len_formula A + len_formula B)"
      unfolding len_sub_def using neq by simp
    ultimately show ?thesis unfolding mi_def by simp
  qed
  have len_pr: "len_proof pr = len_proof pa + len_proof pii + len_proof mi"
    unfolding pr_def pre_def by simp
  show ?thesis
    using valid_pr pr_asm pr_thesis len_pr len_mi by force
qed

subsection \<open>The roundtrip templates and their per-connective base equivalences\<close>

text \<open>
  Composing the two per-connective translations gives a map from Ftwo-formulas to
  Ftwo-formulas.  Each Ftwo-connective c thereby acquires an Ftwo-template
  \<^text>\<open>roundtrip_template\<close>, which satisfies exactly the same specification an
  Ftwo-template would: well-formed, and evaluating to c's own truth function applied
  to the marker variables.  Since the alphabet is finite, the equivalence between the
  template and the bare connective has a proof of CONSTANT size, and taking the
  maximum over the (finitely many) connectives gives a single uniform bound.  These
  are the base cases of the roundtrip induction.
\<close>

definition roundtrip_template :: "'c2 \<Rightarrow> 'c2 formula" where
  "roundtrip_template c = translate_formula (rev.connective_template c)"

lemma roundtrip_template_wf:
  "formula_well_formed (alphabet Ftwo) (roundtrip_template c)"
  unfolding roundtrip_template_def by (rule translate_formula_well_formed)

lemma roundtrip_template_eval:
  "eval (alphabet Ftwo) val (roundtrip_template c)
   = conn_evals (alphabet Ftwo) c (map val (marker_variables (arity (alphabet Ftwo) c)))"
proof -
  have wf: "formula_well_formed (alphabet Fone) (rev.connective_template c)"
    using rev.connective_template_spec by blast
  have "eval (alphabet Ftwo) val (roundtrip_template c)
      = eval (alphabet Fone) val (rev.connective_template c)"
    unfolding roundtrip_template_def by (rule translate_formula_eval[OF wf])
  also have "\<dots> = conn_evals (alphabet Ftwo) c
                    (map val (marker_variables (arity (alphabet Ftwo) c)))"
    using rev.connective_template_spec by blast
  finally show ?thesis .
qed

definition roundtrip_base_proof :: "'c2 \<Rightarrow> 'c2 frege_proof" where
  "roundtrip_base_proof c =
     two_bal.entails_proof {}
       (two_bal.iff_form (roundtrip_template c)
          (Conn c (map Atom (marker_variables (arity (alphabet Ftwo) c)))))"

lemma roundtrip_base_proof_spec:
  "valid_proof Ftwo (roundtrip_base_proof c)
   \<and> assumptions (roundtrip_base_proof c) = {}
   \<and> thesis (roundtrip_base_proof c)
       = two_bal.iff_form (roundtrip_template c)
           (Conn c (map Atom (marker_variables (arity (alphabet Ftwo) c))))
   \<and> (\<forall> st \<in> set (steps (roundtrip_base_proof c)).
        formula_well_formed (alphabet Ftwo) st)"
proof -
  define names where "names = marker_variables (arity (alphabet Ftwo) c)"
  have len_names: "length names = arity (alphabet Ftwo) c"
    unfolding names_def using marker_variables_spec by blast
  have wf_rhs: "formula_well_formed (alphabet Ftwo) (Conn c (map Atom names))"
    using len_names by simp
  have wf_lhs: "formula_well_formed (alphabet Ftwo) (roundtrip_template c)"
    by (rule roundtrip_template_wf)
  have eval_rhs: "\<And>val. eval (alphabet Ftwo) val (Conn c (map Atom names))
                        = conn_evals (alphabet Ftwo) c (map val names)"
    by (simp add: comp_def)
  have wf_fs: "\<forall> f \<in> {}. formula_well_formed (alphabet Ftwo) f" by simp
  have wf_th: "formula_well_formed (alphabet Ftwo)
                 (two_bal.iff_form (roundtrip_template c) (Conn c (map Atom names)))"
    by (rule two_bal.iff_form_wf[OF wf_lhs wf_rhs])
  have sem: "\<forall> val. (\<forall> f \<in> {}. eval (alphabet Ftwo) val f)
             \<longrightarrow> eval (alphabet Ftwo) val
                  (two_bal.iff_form (roundtrip_template c) (Conn c (map Atom names)))"
  proof (intro allI impI)
    fix val
    have "eval (alphabet Ftwo) val (roundtrip_template c)
        = conn_evals (alphabet Ftwo) c (map val names)"
      unfolding names_def by (rule roundtrip_template_eval)
    also have "\<dots> = eval (alphabet Ftwo) val (Conn c (map Atom names))"
      using eval_rhs by simp
    finally show "eval (alphabet Ftwo) val
                    (two_bal.iff_form (roundtrip_template c) (Conn c (map Atom names)))"
      using two_bal.iff_form_eval by simp
  qed
  show ?thesis
    unfolding roundtrip_base_proof_def names_def[symmetric]
    using two_bal.entails_proof_spec[OF wf_fs wf_th sem] by simp
qed

definition roundtrip_base_bound :: nat where
  "roundtrip_base_bound = Max ((\<lambda> c :: 'c2. len_proof (roundtrip_base_proof c)) ` UNIV)"

lemma roundtrip_base_bound_ge:
  "len_proof (roundtrip_base_proof c) \<le> roundtrip_base_bound"
  unfolding roundtrip_base_bound_def
  using two.finite_alphabet by (intro Max_ge) auto

text \<open>
  The well-formedness hypothesis below is REQUIRED, not cosmetic: without it the arity
  and the argument list can disagree, \<^text>\<open>marker_substitution\<close> then falls through
  to \<^term>\<open>Atom v\<close> for a FRESH marker v, and that v is not among the variables of the
  source formula -- so the inclusion would fail.
\<close>

lemma translate_formula_var_set:
  assumes "formula_well_formed (alphabet Fone) f"
  shows "var_set_form (translate_formula f) \<subseteq> var_set_form f"
  using assms
proof (induction f)
  case (Atom a)
  show ?case by simp
next
  case (Conn c fs)
  define names where "names = marker_variables (arity (alphabet Fone) c)"
  define sigma where "sigma = marker_substitution names (map translate_formula fs)"
  have len_fs: "length fs = arity (alphabet Fone) c" using Conn.prems by simp
  have len_names: "length names = arity (alphabet Fone) c" and dist: "distinct names"
    unfolding names_def using marker_variables_spec by blast+
  have args_len: "length (map translate_formula fs) = length names"
    using len_fs len_names by simp
  have tmpl_vars: "var_set_form (connective_template c) \<subseteq> set names"
    unfolding names_def using connective_template_spec by blast
  have sig_sub: "var_set_form (sigma v) \<subseteq> var_set_form (Conn c fs)" if v_in: "v \<in> set names" for v
  proof -
    obtain k where k_lt: "k < length names" and v_eq: "v = names ! k"
      using v_in by (metis in_set_conv_nth)
    have k_fs: "k < length fs" using k_lt len_fs len_names by simp
    have "sigma v = (map translate_formula fs) ! k"
      unfolding sigma_def v_eq by (rule marker_substitution_nth[OF dist args_len k_lt])
    also have "\<dots> = translate_formula (fs ! k)" using k_fs by simp
    finally have sv: "sigma v = translate_formula (fs ! k)" .
    have wf_k: "formula_well_formed (alphabet Fone) (fs ! k)"
      using Conn.prems k_fs by auto
    have "var_set_form (translate_formula (fs ! k)) \<subseteq> var_set_form (fs ! k)"
      using Conn.IH k_fs wf_k nth_mem by blast
    moreover have "var_set_form (fs ! k) \<subseteq> var_set_form (Conn c fs)"
      using nth_mem[OF k_fs] by auto
    ultimately show ?thesis using sv by simp
  qed
  have "var_set_form (translate_formula (Conn c fs))
      = (\<Union>v \<in> var_set_form (connective_template c). var_set_form (sigma v))"
    unfolding sigma_def names_def by (simp add: var_set_sub)
  also have "\<dots> \<subseteq> var_set_form (Conn c fs)"
    using tmpl_vars sig_sub by blast
  finally show ?case .
qed

text \<open>
  The composite of the two template translations is itself a template translation of
  Ftwo into itself, with \<^text>\<open>roundtrip_template\<close> as its per-connective template.
  This is the structural identity the roundtrip induction runs on.
\<close>

lemma roundtrip_unfold:
  assumes wf: "formula_well_formed (alphabet Ftwo) (Conn c args)"
  shows "translate_formula (rev.translate_formula (Conn c args))
       = sub_formula
           (marker_substitution (marker_variables (arity (alphabet Ftwo) c))
              (map (\<lambda>g. translate_formula (rev.translate_formula g)) args))
           (roundtrip_template c)"
proof -
  define names where "names = marker_variables (arity (alphabet Ftwo) c)"
  define rho where "rho = marker_substitution names (map rev.translate_formula args)"
  have len_args: "length args = arity (alphabet Ftwo) c" using wf by simp
  have len_names: "length names = arity (alphabet Ftwo) c" and dist: "distinct names"
    unfolding names_def using marker_variables_spec by blast+
  have tmpl_wf: "formula_well_formed (alphabet Fone) (rev.connective_template c)"
    using rev.connective_template_spec by blast
  have tmpl_vars: "var_set_form (rev.connective_template c) \<subseteq> set names"
    unfolding names_def using rev.connective_template_spec by blast
  \<comment> \<open>push the outer translation through the substitution\<close>
  have step: "translate_formula (sub_formula rho (rev.connective_template c))
            = sub_formula (\<lambda>u. translate_formula (rho u)) (roundtrip_template c)"
    unfolding roundtrip_template_def
    by (rule translate_formula_substitution[OF tmpl_wf])
  \<comment> \<open>the pushed substitution is the marker substitution of the translated arguments\<close>
  have agree: "translate_formula (rho u)
             = marker_substitution names
                 (map (\<lambda>g. translate_formula (rev.translate_formula g)) args) u"
    if u_in: "u \<in> var_set_form (roundtrip_template c)" for u
  proof -
    have u_names: "u \<in> set names"
    proof -
      have "var_set_form (roundtrip_template c) \<subseteq> var_set_form (rev.connective_template c)"
        unfolding roundtrip_template_def by (rule translate_formula_var_set[OF tmpl_wf])
      thus ?thesis using u_in tmpl_vars by blast
    qed
    obtain k where k_lt: "k < length names" and u_eq: "u = names ! k"
      using u_names by (metis in_set_conv_nth)
    have k_args: "k < length args" using k_lt len_args len_names by simp
    have l1: "length (map rev.translate_formula args) = length names"
      using len_args len_names by simp
    have l2: "length (map (\<lambda>g. translate_formula (rev.translate_formula g)) args)
            = length names"
      using len_args len_names by simp
    have "rho u = (map rev.translate_formula args) ! k"
      unfolding rho_def u_eq by (rule marker_substitution_nth[OF dist l1 k_lt])
    hence "translate_formula (rho u) = translate_formula (rev.translate_formula (args ! k))"
      using k_args by simp
    moreover have "marker_substitution names
                     (map (\<lambda>g. translate_formula (rev.translate_formula g)) args) u
                 = translate_formula (rev.translate_formula (args ! k))"
      unfolding u_eq
      using marker_substitution_nth[OF dist l2 k_lt] k_args by simp
    ultimately show ?thesis by simp
  qed
  have "translate_formula (rev.translate_formula (Conn c args))
      = translate_formula (sub_formula rho (rev.connective_template c))"
    unfolding rho_def names_def by simp
  also have "\<dots> = sub_formula (\<lambda>u. translate_formula (rho u)) (roundtrip_template c)"
    by (rule step)
  also have "\<dots> = sub_formula
                   (marker_substitution names
                      (map (\<lambda>g. translate_formula (rev.translate_formula g)) args))
                   (roundtrip_template c)"
    by (rule sub_formula_cong) (rule agree)
  finally show ?thesis unfolding names_def .
qed

subsection \<open>A size-tracked provable equivalence for Ftwo\<close>

text \<open>
  \<^text>\<open>provable_balanced_iff\<close> tracks lines, step size and step depth separately,
  which is what the Spira argument needs.  The roundtrip only ever needs the total
  proof SIZE, so this lighter predicate keeps the induction's bookkeeping to a single
  number.  Reflexivity and transitivity are obtained the same way the modus ponens
  converter was: a base proof over FRESH ATOMS (hence of constant size) instantiated by
  substitution, so the cost stays linear in the formulas involved.
\<close>

definition two_prov_iff :: "'c2 formula \<Rightarrow> 'c2 formula \<Rightarrow> nat \<Rightarrow> bool" where
  "two_prov_iff A B n \<longleftrightarrow>
     (\<exists> pr. valid_proof Ftwo pr \<and> assumptions pr = {}
          \<and> thesis pr = two_bal.iff_form A B
          \<and> len_proof pr \<le> n
          \<and> (\<forall> st \<in> set (steps pr). formula_well_formed (alphabet Ftwo) st))"

definition two_refl_base :: "'c2 frege_proof" where
  "two_refl_base = two_bal.entails_proof {}
      (two_bal.iff_form (Atom two_bal.trans_atom_x) (Atom two_bal.trans_atom_x))"

lemma two_refl_base_spec:
  "valid_proof Ftwo two_refl_base \<and> assumptions two_refl_base = {}
   \<and> thesis two_refl_base
       = two_bal.iff_form (Atom two_bal.trans_atom_x) (Atom two_bal.trans_atom_x)
   \<and> (\<forall> st \<in> set (steps two_refl_base). formula_well_formed (alphabet Ftwo) st)"
proof -
  have wf_fs: "\<forall> f \<in> {}. formula_well_formed (alphabet Ftwo) f" by simp
  have wf_th: "formula_well_formed (alphabet Ftwo)
                 (two_bal.iff_form (Atom two_bal.trans_atom_x) (Atom two_bal.trans_atom_x))"
    by (intro two_bal.iff_form_wf) auto
  have sem: "\<forall> val. (\<forall> f \<in> {}. eval (alphabet Ftwo) val f)
              \<longrightarrow> eval (alphabet Ftwo) val
                   (two_bal.iff_form (Atom two_bal.trans_atom_x) (Atom two_bal.trans_atom_x))"
    using two_bal.iff_form_eval by simp
  show ?thesis
    unfolding two_refl_base_def
    using two_bal.entails_proof_spec[OF wf_fs wf_th sem] .
qed

lemma two_prov_iff_refl:
  assumes wfA: "formula_well_formed (alphabet Ftwo) A"
  shows "two_prov_iff A A (len_proof two_refl_base * max 1 (len_formula A))"
proof -
  let ?x = "two_bal.trans_atom_x"
  let ?sub = "\<lambda>w. if w = ?x then A else Atom w"
  have x_avoid: "?x \<notin> two_bal.avoid_atoms" using two_bal.trans_atoms_spec by blast
  have sub_conn_iff:
    "\<And>w. w \<in> var_set_form two_bal.conn_iff \<Longrightarrow> w \<noteq> ''a'' \<Longrightarrow> w \<noteq> ''b'' \<Longrightarrow> ?sub w = Atom w"
  proof -
    fix w assume w_ci: "w \<in> var_set_form two_bal.conn_iff" and "w \<noteq> ''a''" and "w \<noteq> ''b''"
    have "w \<in> two_bal.avoid_atoms" using w_ci unfolding two_bal.avoid_atoms_def by blast
    thus "?sub w = Atom w" using x_avoid by auto
  qed
  define pr where pr_def: "pr = sub_proof ?sub two_refl_base"
  have valid: "valid_proof Ftwo pr"
    unfolding pr_def using two.proof_substitution two_refl_base_spec by blast
  have asm: "assumptions pr = {}"
    unfolding pr_def using two_refl_base_spec by simp
  have th: "thesis pr = two_bal.iff_form A A"
  proof -
    have "thesis pr = sub_formula ?sub (two_bal.iff_form (Atom ?x) (Atom ?x))"
      unfolding pr_def using two_refl_base_spec by simp
    also have "\<dots> = two_bal.iff_form (sub_formula ?sub (Atom ?x)) (sub_formula ?sub (Atom ?x))"
      by (rule two_bal.sub_formula_iff_form[OF sub_conn_iff])
    also have "\<dots> = two_bal.iff_form A A" by simp
    finally show ?thesis .
  qed
  have wf_steps: "\<forall> st \<in> set (steps pr). formula_well_formed (alphabet Ftwo) st"
  proof
    fix st assume "st \<in> set (steps pr)"
    then obtain s0 where s0: "s0 \<in> set (steps two_refl_base)"
      and st_eq: "st = sub_formula ?sub s0"
      unfolding pr_def by auto
    have wf0: "formula_well_formed (alphabet Ftwo) s0" using two_refl_base_spec s0 by blast
    have wfsub: "\<And>v. formula_well_formed (alphabet Ftwo) (?sub v)" using wfA by simp
    show "formula_well_formed (alphabet Ftwo) st"
      using st_eq sub_formula_well_formed[OF wf0 wfsub] by simp
  qed
  have len: "len_proof pr \<le> len_proof two_refl_base * max 1 (len_formula A)"
  proof -
    have fin: "finite {?x}" by simp
    have outside: "\<forall>v. v \<notin> {?x} \<longrightarrow> ?sub v = Atom v" by simp
    have "len_proof (sub_proof ?sub two_refl_base)
        \<le> len_proof two_refl_base * len_sub {?x} ?sub"
      by (rule sub_proof_bound[OF fin outside])
    moreover have "len_sub {?x} ?sub = max 1 (len_formula A)"
      unfolding len_sub_def by simp
    ultimately show ?thesis unfolding pr_def by simp
  qed
  show ?thesis
    unfolding two_prov_iff_def using valid asm th len wf_steps by blast
qed

lemma two_prov_iff_mono:
  assumes "two_prov_iff A B m" and "m \<le> n"
  shows "two_prov_iff A B n"
  using assms unfolding two_prov_iff_def by force

lemma two_prov_iff_trans:
  assumes ab: "two_prov_iff A B m" and bc: "two_prov_iff B C n"
      and wfA: "formula_well_formed (alphabet Ftwo) A"
      and wfB: "formula_well_formed (alphabet Ftwo) B"
      and wfC: "formula_well_formed (alphabet Ftwo) C"
  shows "two_prov_iff A C
           (m + n + len_proof two_bal.trans_base_proof
                      * max 1 (len_formula A + len_formula B + len_formula C))"
proof -
  let ?x = "two_bal.trans_atom_x" and ?y = "two_bal.trans_atom_y"
    and ?z = "two_bal.trans_atom_z"
  let ?sub = "\<lambda>w. if w = ?x then A else if w = ?y then B else if w = ?z then C else Atom w"
  have neq: "?x \<noteq> ?y" "?x \<noteq> ?z" "?y \<noteq> ?z" using two_bal.trans_atoms_spec by blast+
  have sub_conn_iff:
    "\<And>w. w \<in> var_set_form two_bal.conn_iff \<Longrightarrow> w \<noteq> ''a'' \<Longrightarrow> w \<noteq> ''b'' \<Longrightarrow> ?sub w = Atom w"
  proof -
    fix w assume w_ci: "w \<in> var_set_form two_bal.conn_iff" and "w \<noteq> ''a''" and "w \<noteq> ''b''"
    have "w \<in> two_bal.avoid_atoms" using w_ci unfolding two_bal.avoid_atoms_def by blast
    hence "w \<noteq> ?x \<and> w \<noteq> ?y \<and> w \<noteq> ?z" using two_bal.trans_atoms_spec by blast
    thus "?sub w = Atom w" by simp
  qed
  obtain pAB where pAB: "valid_proof Ftwo pAB" "assumptions pAB = {}"
    "frege_proof.thesis pAB = two_bal.iff_form A B" "len_proof pAB \<le> m"
    "\<forall> st \<in> set (steps pAB). formula_well_formed (alphabet Ftwo) st"
    using ab unfolding two_prov_iff_def by blast
  obtain pBC where pBC: "valid_proof Ftwo pBC" "assumptions pBC = {}"
    "frege_proof.thesis pBC = two_bal.iff_form B C" "len_proof pBC \<le> n"
    "\<forall> st \<in> set (steps pBC). formula_well_formed (alphabet Ftwo) st"
    using bc unfolding two_prov_iff_def by blast
  define ti where ti_def: "ti = sub_proof ?sub two_bal.trans_base_proof"
  have valid_ti: "valid_proof Ftwo ti"
    unfolding ti_def using two.proof_substitution two_bal.trans_base_proof_spec by blast
  have sub_xy: "sub_formula ?sub (two_bal.iff_form (Atom ?x) (Atom ?y))
              = two_bal.iff_form A B"
  proof -
    have "sub_formula ?sub (two_bal.iff_form (Atom ?x) (Atom ?y))
        = two_bal.iff_form (sub_formula ?sub (Atom ?x)) (sub_formula ?sub (Atom ?y))"
      by (rule two_bal.sub_formula_iff_form[OF sub_conn_iff])
    also have "\<dots> = two_bal.iff_form A B" using neq by simp
    finally show ?thesis .
  qed
  have sub_yz: "sub_formula ?sub (two_bal.iff_form (Atom ?y) (Atom ?z))
              = two_bal.iff_form B C"
  proof -
    have "sub_formula ?sub (two_bal.iff_form (Atom ?y) (Atom ?z))
        = two_bal.iff_form (sub_formula ?sub (Atom ?y)) (sub_formula ?sub (Atom ?z))"
      by (rule two_bal.sub_formula_iff_form[OF sub_conn_iff])
    also have "\<dots> = two_bal.iff_form B C" using neq by simp
    finally show ?thesis .
  qed
  have sub_xz: "sub_formula ?sub (two_bal.iff_form (Atom ?x) (Atom ?z))
              = two_bal.iff_form A C"
  proof -
    have "sub_formula ?sub (two_bal.iff_form (Atom ?x) (Atom ?z))
        = two_bal.iff_form (sub_formula ?sub (Atom ?x)) (sub_formula ?sub (Atom ?z))"
      by (rule two_bal.sub_formula_iff_form[OF sub_conn_iff])
    also have "\<dots> = two_bal.iff_form A C" using neq by simp
    finally show ?thesis .
  qed
  have ti_asm: "assumptions ti = {two_bal.iff_form A B, two_bal.iff_form B C}"
  proof -
    have "assumptions ti = (sub_formula ?sub) ` (assumptions two_bal.trans_base_proof)"
      unfolding ti_def by simp
    also have "\<dots> = (sub_formula ?sub) `
        {two_bal.iff_form (Atom ?x) (Atom ?y), two_bal.iff_form (Atom ?y) (Atom ?z)}"
      using two_bal.trans_base_proof_spec by simp
    also have "\<dots> = {two_bal.iff_form A B, two_bal.iff_form B C}"
      using sub_xy sub_yz by simp
    finally show ?thesis .
  qed
  have ti_thesis: "thesis ti = two_bal.iff_form A C"
  proof -
    have "thesis ti = sub_formula ?sub (two_bal.iff_form (Atom ?x) (Atom ?z))"
      unfolding ti_def using two_bal.trans_base_proof_spec by simp
    thus ?thesis using sub_xz by simp
  qed
  have ti_wf: "\<forall> st \<in> set (steps ti). formula_well_formed (alphabet Ftwo) st"
  proof
    fix st assume "st \<in> set (steps ti)"
    then obtain s0 where s0: "s0 \<in> set (steps two_bal.trans_base_proof)"
      and st_eq: "st = sub_formula ?sub s0"
      unfolding ti_def by auto
    have wf0: "formula_well_formed (alphabet Ftwo) s0"
      using two_bal.trans_base_proof_spec s0 by blast
    have wfsub: "\<And>v. formula_well_formed (alphabet Ftwo) (?sub v)"
      using wfA wfB wfC by simp
    show "formula_well_formed (alphabet Ftwo) st"
      using st_eq sub_formula_well_formed[OF wf0 wfsub] by simp
  qed
  have ti_len: "len_proof ti \<le> len_proof two_bal.trans_base_proof
                  * max 1 (len_formula A + len_formula B + len_formula C)"
  proof -
    have fin: "finite {?x, ?y, ?z}" by simp
    have outside: "\<forall>v. v \<notin> {?x, ?y, ?z} \<longrightarrow> ?sub v = Atom v" by auto
    have "len_proof (sub_proof ?sub two_bal.trans_base_proof)
        \<le> len_proof two_bal.trans_base_proof * len_sub {?x, ?y, ?z} ?sub"
      by (rule sub_proof_bound[OF fin outside])
    moreover have "len_sub {?x, ?y, ?z} ?sub
                 = max 1 (len_formula A + len_formula B + len_formula C)"
      unfolding len_sub_def using neq by simp
    ultimately show ?thesis unfolding ti_def by simp
  qed
  \<comment> \<open>glue: the two premise proofs, then the substituted transitivity instance\<close>
  define pre where pre_def: "pre = combine_proofs pAB pBC"
  have valid_pre: "valid_proof Ftwo pre"
    unfolding pre_def using two.combining_valid_proofs pAB(1) pBC(1) by blast
  have pre_asm: "assumptions pre = {}"
    unfolding pre_def using pAB(2) pBC(2) by simp
  have pre_steps: "steps pre = steps pAB @ steps pBC"
    unfolding pre_def by simp
  have AB_in: "two_bal.iff_form A B \<in> set (steps pre)"
  proof -
    have "thesis pAB \<in> set (steps pAB)" using pAB(1) unfolding valid_proof_def by simp
    thus ?thesis using pAB(3) pre_steps by simp
  qed
  have BC_in: "two_bal.iff_form B C \<in> set (steps pre)"
  proof -
    have "thesis pBC \<in> set (steps pBC)" using pBC(1) unfolding valid_proof_def by simp
    thus ?thesis using pBC(3) pre_steps by simp
  qed
  define pr where pr_def: "pr = combine_proofs pre ti"
  have valid_pr: "valid_proof Ftwo pr"
    unfolding pr_def using two.combining_valid_proofs valid_pre valid_ti by blast
  have pr_asm: "assumptions pr = {}"
  proof -
    have "assumptions pr = assumptions pre \<union> (assumptions ti - set (steps pre))"
      unfolding pr_def by simp
    also have "\<dots> = {} \<union> ({two_bal.iff_form A B, two_bal.iff_form B C} - set (steps pre))"
      using pre_asm ti_asm by simp
    also have "\<dots> = {}" using AB_in BC_in by blast
    finally show ?thesis .
  qed
  have pr_th: "thesis pr = two_bal.iff_form A C"
    unfolding pr_def using ti_thesis by simp
  have pr_wf: "\<forall> st \<in> set (steps pr). formula_well_formed (alphabet Ftwo) st"
    unfolding pr_def using pre_steps pAB(5) pBC(5) ti_wf by auto
  have pr_len: "len_proof pr = len_proof pAB + len_proof pBC + len_proof ti"
    unfolding pr_def pre_def by simp
  show ?thesis
    unfolding two_prov_iff_def
    using valid_pr pr_asm pr_th pr_wf pr_len pAB(4) pBC(4) ti_len by force
qed

subsection \<open>Per-slot congruence for Ftwo connectives\<close>

lemma sub_formula_atom_id: "sub_formula Atom (f :: 'c2 formula) = f"
  by (induction f) (simp_all add: map_idI)

lemma two_conn_iff_as_iff_form:
  "two_bal.conn_iff = two_bal.iff_form (Atom ''a'') (Atom ''b'')"
proof -
  have "two_bal.iff_sub (Atom ''a'') (Atom ''b'') = Atom"
    unfolding two_bal.iff_sub_def by auto
  thus ?thesis
    unfolding two_bal.iff_form_def using sub_formula_atom_id by simp
qed

definition two_max_arity :: nat where
  "two_max_arity = Max ((arity (alphabet Ftwo)) ` (UNIV :: 'c2 set))"

lemma two_max_arity_ge: "arity (alphabet Ftwo) c \<le> two_max_arity"
  unfolding two_max_arity_def using two.finite_alphabet by (intro Max_ge) auto

definition two_slot_base :: "'c2 \<Rightarrow> nat \<Rightarrow> 'c2 frege_proof" where
  "two_slot_base c i = (SOME pr. valid_proof Ftwo pr
     \<and> assumptions pr = {two_bal.conn_iff}
     \<and> thesis pr = two_bal.iff_form
          (Conn c ((map Atom (two_bal.canonical_atoms c))[i := Atom ''a'']))
          (Conn c ((map Atom (two_bal.canonical_atoms c))[i := Atom ''b'']))
     \<and> (\<forall> st \<in> set (steps pr). formula_well_formed (alphabet Ftwo) st))"

lemma two_slot_base_spec:
  assumes "i < arity (alphabet Ftwo) c"
  shows "valid_proof Ftwo (two_slot_base c i)
       \<and> assumptions (two_slot_base c i) = {two_bal.conn_iff}
       \<and> thesis (two_slot_base c i) = two_bal.iff_form
            (Conn c ((map Atom (two_bal.canonical_atoms c))[i := Atom ''a'']))
            (Conn c ((map Atom (two_bal.canonical_atoms c))[i := Atom ''b'']))
       \<and> (\<forall> st \<in> set (steps (two_slot_base c i)).
            formula_well_formed (alphabet Ftwo) st)"
proof -
  have ex: "\<exists> pr. valid_proof Ftwo pr \<and> assumptions pr = {two_bal.conn_iff}
     \<and> thesis pr = two_bal.iff_form
          (Conn c ((map Atom (two_bal.canonical_atoms c))[i := Atom ''a'']))
          (Conn c ((map Atom (two_bal.canonical_atoms c))[i := Atom ''b'']))
     \<and> (\<forall> st \<in> set (steps pr). formula_well_formed (alphabet Ftwo) st)"
    using two_bal.iff_congruent_base[OF assms]
    unfolding two_bal.iff_form_def two_bal.iff_sub_def by simp
  show ?thesis unfolding two_slot_base_def by (rule someI_ex[OF ex])
qed

definition two_slot_bound :: nat where
  "two_slot_bound = Max ((\<lambda>(c,i). len_proof (two_slot_base c i))
                          ` ((UNIV :: 'c2 set) \<times> {..< Suc two_max_arity}))"

lemma two_slot_bound_ge:
  assumes "i < arity (alphabet Ftwo) c"
  shows "len_proof (two_slot_base c i) \<le> two_slot_bound"
proof -
  have fin: "finite ((UNIV :: 'c2 set) \<times> {..< Suc two_max_arity})"
    using two.finite_alphabet by simp
  have "i \<le> two_max_arity" using assms two_max_arity_ge[of c] by simp
  hence mem: "(c,i) \<in> (UNIV :: 'c2 set) \<times> {..< Suc two_max_arity}" by simp
  show ?thesis
    unfolding two_slot_bound_def using fin mem by (intro Max_ge) auto
qed

lemma two_prov_iff_slot:
  fixes c :: 'c2 and i :: nat
  assumes i_lt: "i < arity (alphabet Ftwo) c"
      and len_xs: "length xs = arity (alphabet Ftwo) c"
      and wf_xs: "\<And>g. g \<in> set xs \<Longrightarrow> formula_well_formed (alphabet Ftwo) g"
      and wfB: "formula_well_formed (alphabet Ftwo) B"
      and ab: "two_prov_iff (xs ! i) B m"
  shows "two_prov_iff (Conn c xs) (Conn c (xs[i := B]))
           (m + two_slot_bound
                * max 1 (len_formula (xs ! i) + len_formula B
                          + sum_list (map len_formula xs)))"
proof -
  define atoms where "atoms = two_bal.canonical_atoms c"
  have at_len: "length atoms = arity (alphabet Ftwo) c"
   and at_dist: "distinct atoms"
   and at_a: "''a'' \<notin> set atoms" and at_b: "''b'' \<notin> set atoms"
   and at_ci: "set atoms \<inter> var_set_form two_bal.conn_iff = {}"
    unfolding atoms_def using two_bal.canonical_atoms_spec by blast+
  define sg where "sg = (\<lambda>w. if w = ''a'' then xs ! i else if w = ''b'' then B
                             else marker_substitution atoms xs w)"
  have i_xs: "i < length xs" using i_lt len_xs by simp
  have xs_at: "length xs = length atoms" using len_xs at_len by simp
  \<comment> \<open>the substitution is the identity on the unknown extra atoms of conn_iff\<close>
  have sub_conn_iff:
    "\<And>w. w \<in> var_set_form two_bal.conn_iff \<Longrightarrow> w \<noteq> ''a'' \<Longrightarrow> w \<noteq> ''b'' \<Longrightarrow> sg w = Atom w"
  proof -
    fix w assume w_ci: "w \<in> var_set_form two_bal.conn_iff" and "w \<noteq> ''a''" and "w \<noteq> ''b''"
    have "w \<notin> set atoms" using w_ci at_ci by blast
    thus "sg w = Atom w"
      unfolding sg_def using \<open>w \<noteq> ''a''\<close> \<open>w \<noteq> ''b''\<close> marker_substitution_outside by simp
  qed
  \<comment> \<open>it maps the canonical atoms onto the actual arguments\<close>
  have map_sg: "map sg atoms = xs"
  proof (rule nth_equalityI)
    show "length (map sg atoms) = length xs" using xs_at by simp
  next
    fix k assume "k < length (map sg atoms)"
    hence k_at: "k < length atoms" by simp
    hence k_xs: "k < length xs" using xs_at by simp
    have "atoms ! k \<in> set atoms" using k_at by simp
    hence nab: "atoms ! k \<noteq> ''a''" "atoms ! k \<noteq> ''b''" using at_a at_b by auto
    have "sg (atoms ! k) = marker_substitution atoms xs (atoms ! k)"
      unfolding sg_def using nab by simp
    also have "\<dots> = xs ! k"
      by (rule marker_substitution_nth[OF at_dist xs_at k_at])
    finally show "map sg atoms ! k = xs ! k" using k_at by simp
  qed
  have side_a: "sub_formula sg (Conn c ((map Atom atoms)[i := Atom ''a''])) = Conn c xs"
  proof -
    have "map (sub_formula sg) ((map Atom atoms)[i := Atom ''a''])
        = (map (sub_formula sg) (map Atom atoms))[i := sub_formula sg (Atom ''a'')]"
      by (simp add: map_update)
    also have "\<dots> = (map sg atoms)[i := xs ! i]"
      unfolding sg_def by (simp add: comp_def)
    also have "\<dots> = xs[i := xs ! i]" using map_sg by simp
    also have "\<dots> = xs" using i_xs by simp
    finally show ?thesis by simp
  qed
  have side_b: "sub_formula sg (Conn c ((map Atom atoms)[i := Atom ''b''])) = Conn c (xs[i := B])"
  proof -
    have "map (sub_formula sg) ((map Atom atoms)[i := Atom ''b''])
        = (map (sub_formula sg) (map Atom atoms))[i := sub_formula sg (Atom ''b'')]"
      by (simp add: map_update)
    also have "\<dots> = (map sg atoms)[i := B]"
      unfolding sg_def by (simp add: comp_def)
    also have "\<dots> = xs[i := B]" using map_sg by simp
    finally show ?thesis by simp
  qed
  \<comment> \<open>instantiate the constant-size per-slot base proof\<close>
  define ti where ti_def: "ti = sub_proof sg (two_slot_base c i)"
  have bspec: "valid_proof Ftwo (two_slot_base c i)
       \<and> assumptions (two_slot_base c i) = {two_bal.conn_iff}
       \<and> thesis (two_slot_base c i) = two_bal.iff_form
            (Conn c ((map Atom atoms)[i := Atom ''a'']))
            (Conn c ((map Atom atoms)[i := Atom ''b'']))
       \<and> (\<forall> st \<in> set (steps (two_slot_base c i)). formula_well_formed (alphabet Ftwo) st)"
    unfolding atoms_def using two_slot_base_spec[OF i_lt] by simp
  have valid_ti: "valid_proof Ftwo ti"
    unfolding ti_def using two.proof_substitution bspec by blast
  have ti_asm: "assumptions ti = {two_bal.iff_form (xs ! i) B}"
  proof -
    have "assumptions ti = (sub_formula sg) ` {two_bal.conn_iff}"
      unfolding ti_def using bspec by simp
    also have "\<dots> = {sub_formula sg (two_bal.iff_form (Atom ''a'') (Atom ''b''))}"
      using two_conn_iff_as_iff_form by simp
    also have "\<dots> = {two_bal.iff_form (sub_formula sg (Atom ''a'')) (sub_formula sg (Atom ''b''))}"
      using two_bal.sub_formula_iff_form[OF sub_conn_iff] by simp
    also have "\<dots> = {two_bal.iff_form (xs ! i) B}"
      unfolding sg_def by simp
    finally show ?thesis .
  qed
  have ti_th: "thesis ti = two_bal.iff_form (Conn c xs) (Conn c (xs[i := B]))"
  proof -
    have "thesis ti = sub_formula sg (two_bal.iff_form
            (Conn c ((map Atom atoms)[i := Atom ''a'']))
            (Conn c ((map Atom atoms)[i := Atom ''b''])))"
      unfolding ti_def using bspec by simp
    also have "\<dots> = two_bal.iff_form
            (sub_formula sg (Conn c ((map Atom atoms)[i := Atom ''a''])))
            (sub_formula sg (Conn c ((map Atom atoms)[i := Atom ''b''])))"
      by (rule two_bal.sub_formula_iff_form[OF sub_conn_iff])
    also have "\<dots> = two_bal.iff_form (Conn c xs) (Conn c (xs[i := B]))"
      using side_a side_b by simp
    finally show ?thesis .
  qed
  have sg_wf: "\<And>v. formula_well_formed (alphabet Ftwo) (sg v)"
  proof -
    fix v
    have "sg v \<in> set xs \<union> {B} \<union> {Atom v}"
    proof (cases "v = ''a''")
      case True
      thus ?thesis unfolding sg_def using i_xs by simp
    next
      case False
      show ?thesis
      proof (cases "v = ''b''")
        case True
        thus ?thesis unfolding sg_def using False by simp
      next
        case False2: False
        have "marker_substitution atoms xs v \<in> set xs \<union> {Atom v}"
          by (rule marker_substitution_range)
        thus ?thesis unfolding sg_def using False False2 by auto
      qed
    qed
    thus "formula_well_formed (alphabet Ftwo) (sg v)"
      using wf_xs wfB by auto
  qed
  have ti_wf: "\<forall> st \<in> set (steps ti). formula_well_formed (alphabet Ftwo) st"
  proof
    fix st assume "st \<in> set (steps ti)"
    then obtain s0 where s0: "s0 \<in> set (steps (two_slot_base c i))"
      and st_eq: "st = sub_formula sg s0"
      unfolding ti_def by auto
    have wf0: "formula_well_formed (alphabet Ftwo) s0" using bspec s0 by blast
    show "formula_well_formed (alphabet Ftwo) st"
      using st_eq sub_formula_well_formed[OF wf0 sg_wf] by simp
  qed
  \<comment> \<open>the substitution's total size\<close>
  have len_sg: "len_sub ({''a'', ''b''} \<union> set atoms) sg
              = max 1 (len_formula (xs ! i) + len_formula B + sum_list (map len_formula xs))"
  proof -
    have fin_at: "finite (set atoms)" by simp
    have ab_neq: "(''a'' :: string) \<noteq> ''b''" by simp
    have eq_set: "{''a'', ''b''} \<union> set atoms = insert ''a'' (insert ''b'' (set atoms))"
      by simp
    have "(\<Sum> v \<in> insert ''a'' (insert ''b'' (set atoms)). len_formula (sg v))
        = len_formula (sg ''a'') + (\<Sum> v \<in> insert ''b'' (set atoms). len_formula (sg v))"
      using fin_at at_a ab_neq by simp
    also have "\<dots> = len_formula (sg ''a'') + len_formula (sg ''b'')
                   + (\<Sum> v \<in> set atoms. len_formula (sg v))"
      using fin_at at_b by simp
    also have "\<dots> = len_formula (xs ! i) + len_formula B
                   + (\<Sum> v \<in> set atoms. len_formula (sg v))"
      unfolding sg_def by simp
    finally have split: "(\<Sum> v \<in> {''a'', ''b''} \<union> set atoms. len_formula (sg v))
        = len_formula (xs ! i) + len_formula B + (\<Sum> v \<in> set atoms. len_formula (sg v))"
      using eq_set by simp
    have "(\<Sum> v \<in> set atoms. len_formula (sg v))
        = sum_list (map (\<lambda>v. len_formula (sg v)) atoms)"
      using at_dist by (simp add: sum_list_distinct_conv_sum_set)
    also have "\<dots> = sum_list (map len_formula (map sg atoms))" by (simp add: o_def)
    also have "\<dots> = sum_list (map len_formula xs)" using map_sg by simp
    finally have inner: "(\<Sum> v \<in> set atoms. len_formula (sg v))
        = sum_list (map len_formula xs)" .
    show ?thesis unfolding len_sub_def using split inner by simp
  qed
  have ti_len: "len_proof ti \<le> two_slot_bound
                  * max 1 (len_formula (xs ! i) + len_formula B
                            + sum_list (map len_formula xs))"
  proof -
    have fin: "finite ({''a'', ''b''} \<union> set atoms)" by simp
    have outside: "\<forall>v. v \<notin> {''a'', ''b''} \<union> set atoms \<longrightarrow> sg v = Atom v"
      unfolding sg_def using marker_substitution_outside by auto
    have "len_proof ti \<le> len_proof (two_slot_base c i)
                          * len_sub ({''a'', ''b''} \<union> set atoms) sg"
      unfolding ti_def by (rule sub_proof_bound[OF fin outside])
    also have "\<dots> \<le> two_slot_bound
                    * max 1 (len_formula (xs ! i) + len_formula B
                              + sum_list (map len_formula xs))"
      using two_slot_bound_ge[OF i_lt] len_sg by (simp add: mult_le_mono1)
    finally show ?thesis .
  qed
  \<comment> \<open>discharge the assumption with the given equivalence proof\<close>
  obtain pAB where pAB: "valid_proof Ftwo pAB" "assumptions pAB = {}"
    "frege_proof.thesis pAB = two_bal.iff_form (xs ! i) B" "len_proof pAB \<le> m"
    "\<forall> st \<in> set (steps pAB). formula_well_formed (alphabet Ftwo) st"
    using ab unfolding two_prov_iff_def by blast
  define pr where pr_def: "pr = combine_proofs pAB ti"
  have valid_pr: "valid_proof Ftwo pr"
    unfolding pr_def using two.combining_valid_proofs pAB(1) valid_ti by blast
  have AB_in: "two_bal.iff_form (xs ! i) B \<in> set (steps pAB)"
  proof -
    have "frege_proof.thesis pAB \<in> set (steps pAB)"
      using pAB(1) unfolding valid_proof_def by simp
    thus ?thesis using pAB(3) by simp
  qed
  have pr_asm: "assumptions pr = {}"
  proof -
    have "assumptions pr = assumptions pAB \<union> (assumptions ti - set (steps pAB))"
      unfolding pr_def by simp
    also have "\<dots> = {} \<union> ({two_bal.iff_form (xs ! i) B} - set (steps pAB))"
      using pAB(2) ti_asm by simp
    also have "\<dots> = {}" using AB_in by blast
    finally show ?thesis .
  qed
  have pr_th: "thesis pr = two_bal.iff_form (Conn c xs) (Conn c (xs[i := B]))"
    unfolding pr_def using ti_th by simp
  have pr_wf: "\<forall> st \<in> set (steps pr). formula_well_formed (alphabet Ftwo) st"
    unfolding pr_def using pAB(5) ti_wf by auto
  have pr_len: "len_proof pr = len_proof pAB + len_proof ti"
    unfolding pr_def by simp
  show ?thesis
    unfolding two_prov_iff_def
    using valid_pr pr_asm pr_th pr_wf pr_len pAB(4) ti_len by force
qed

subsection \<open>Folding the per-slot congruence over all argument positions\<close>

text \<open>
  \<^text>\<open>two_prov_iff_slot\<close> rewrites ONE argument of a connective.  Rewriting all of
  them is an induction along the ``hybrid'' argument lists \<open>take k bs @ drop k as\<close>, whose
  first \<open>k\<close> entries already come from \<open>bs\<close> while the remaining ones still come from \<open>as\<close>.
  Advancing \<open>k\<close> by one is exactly one application of the per-slot lemma, glued on with
  \<^text>\<open>two_prov_iff_trans\<close>.  Every formula occurring anywhere along the chain is
  assembled from arguments of \<open>as\<close> and \<open>bs\<close>, so a single uniform per-step cost covers all
  the steps, and the number of steps is bounded by the constant \<^const>\<open>two_max_arity\<close>.
\<close>

lemma sum_list_take_le: "sum_list (take k (ys :: nat list)) \<le> sum_list ys"
proof -
  have "sum_list (take k ys) + sum_list (drop k ys) = sum_list ys"
    using sum_list_append[of "take k ys" "drop k ys"] by simp
  thus ?thesis by simp
qed

lemma sum_list_drop_le: "sum_list (drop k (ys :: nat list)) \<le> sum_list ys"
proof -
  have "sum_list (take k ys) + sum_list (drop k ys) = sum_list ys"
    using sum_list_append[of "take k ys" "drop k ys"] by simp
  thus ?thesis by simp
qed

lemma hybrid_nth:
  assumes lb: "length bs = length as" and k_le: "k \<le> length as" and j_lt: "j < length as"
  shows "(take k bs @ drop k as) ! j = (if j < k then bs ! j else as ! j)"
proof (cases "j < k")
  case True
  have lk: "length (take k bs) = k" using lb k_le by simp
  have "(take k bs @ drop k as) ! j = take k bs ! j"
    using True lk by (simp add: nth_append)
  also have "\<dots> = bs ! j" using True by simp
  finally show ?thesis using True by simp
next
  case False
  have lk: "length (take k bs) = k" using lb k_le by simp
  have "(take k bs @ drop k as) ! j = drop k as ! (j - k)"
    using False lk by (simp add: nth_append)
  also have "\<dots> = as ! (k + (j - k))" using k_le by simp
  also have "\<dots> = as ! j" using False by simp
  finally show ?thesis using False by simp
qed

lemma hybrid_step:
  assumes lb: "length bs = length as" and k_lt: "k < length as"
  shows "take (Suc k) bs @ drop (Suc k) as = (take k bs @ drop k as)[k := bs ! k]"
proof -
  have k_bs: "k < length bs" using lb k_lt by simp
  have lk: "length (take k bs) = k" using k_bs by simp
  have left: "take (Suc k) bs = take k bs @ [bs ! k]"
    using k_bs by (rule take_Suc_conv_app_nth)
  have mid: "drop k as = as ! k # drop (Suc k) as"
    using Cons_nth_drop_Suc[OF k_lt] by simp
  have "(take k bs @ drop k as)[k := bs ! k]
      = (take k bs @ (as ! k # drop (Suc k) as))[k := bs ! k]"
    using mid by simp
  also have "\<dots> = take k bs @ (as ! k # drop (Suc k) as)[k - k := bs ! k]"
    using lk by (simp add: list_update_append)
  also have "\<dots> = (take k bs @ [bs ! k]) @ drop (Suc k) as" by simp
  also have "\<dots> = take (Suc k) bs @ drop (Suc k) as" using left by simp
  finally show ?thesis by (rule sym)
qed

definition two_arg_size :: "'c2 formula list \<Rightarrow> 'c2 formula list \<Rightarrow> nat" where
  "two_arg_size as bs = sum_list (map len_formula as) + sum_list (map len_formula bs)"

definition two_slot_step_cost :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "two_slot_step_cost m S = (m + two_slot_bound * max 1 (3 * S))
     + len_proof two_bal.trans_base_proof * max 1 (3 * Suc S)"


lemma two_prov_iff_conn_prefix:
  fixes c :: 'c2
  assumes len_as: "length as = arity (alphabet Ftwo) c"
      and len_bs: "length bs = length as"
      and wf_as: "\<And>g. g \<in> set as \<Longrightarrow> formula_well_formed (alphabet Ftwo) g"
      and wf_bs: "\<And>g. g \<in> set bs \<Longrightarrow> formula_well_formed (alphabet Ftwo) g"
      and pw: "\<And>j. j < length as \<Longrightarrow> two_prov_iff (as ! j) (bs ! j) m"
      and k_le: "k \<le> length as"
    shows "two_prov_iff (Conn c as) (Conn c (take k bs @ drop k as))
             (len_proof two_refl_base * max 1 (Suc (two_arg_size as bs))
                + k * two_slot_step_cost m (two_arg_size as bs))"
proof -
  let ?S = "two_arg_size as bs"
  let ?R = "len_proof two_refl_base * max 1 (Suc (two_arg_size as bs))"
  let ?C = "two_slot_step_cost m (two_arg_size as bs)"
  \<comment> \<open>uniform facts about every hybrid argument list\<close>
  have hyb_len: "length (take j bs @ drop j as) = length as" if "j \<le> length as" for j
    using that len_bs by simp
  have hyb_elem_wf: "formula_well_formed (alphabet Ftwo) g"
    if "g \<in> set (take j bs @ drop j as)" for j g
  proof -
    have "g \<in> set bs \<union> set as"
      using that by (auto dest: in_set_takeD in_set_dropD)
    thus ?thesis using wf_as wf_bs by blast
  qed
  have hyb_wf: "formula_well_formed (alphabet Ftwo) (Conn c (take j bs @ drop j as))"
    if "j \<le> length as" for j
  proof -
    have "length (take j bs @ drop j as) = arity (alphabet Ftwo) c"
      using hyb_len[OF that] len_as by simp
    moreover have "\<forall> g \<in> set (take j bs @ drop j as). formula_well_formed (alphabet Ftwo) g"
      using hyb_elem_wf by blast
    ultimately show ?thesis by simp
  qed
  have hyb_sum: "sum_list (map len_formula (take j bs @ drop j as)) \<le> ?S" for j
  proof -
    have "sum_list (map len_formula (take j bs @ drop j as))
        = sum_list (map len_formula (take j bs)) + sum_list (map len_formula (drop j as))"
      by simp
    also have "\<dots> = sum_list (take j (map len_formula bs))
                   + sum_list (drop j (map len_formula as))"
      by (simp add: take_map drop_map)
    also have "\<dots> \<le> sum_list (map len_formula bs) + sum_list (map len_formula as)"
      using sum_list_take_le sum_list_drop_le by (rule add_le_mono)
    finally show ?thesis unfolding two_arg_size_def by simp
  qed
  have hyb_size: "len_formula (Conn c (take j bs @ drop j as)) \<le> Suc ?S" for j
    using hyb_sum[of j] by simp
  have as_wf: "formula_well_formed (alphabet Ftwo) (Conn c as)"
    using hyb_wf[of 0] by simp
  have as_size: "len_formula (Conn c as) \<le> Suc ?S"
    using hyb_size[of 0] by simp
  show ?thesis using k_le
  proof (induction k)
    case 0
    have r0: "two_prov_iff (Conn c as) (Conn c as)
                (len_proof two_refl_base * max 1 (len_formula (Conn c as)))"
      by (rule two_prov_iff_refl[OF as_wf])
    have r1: "len_proof two_refl_base * max 1 (len_formula (Conn c as)) \<le> ?R"
    proof -
      have "max 1 (len_formula (Conn c as)) \<le> max 1 (Suc ?S)"
        using as_size by (rule max.mono[OF order_refl])
      thus ?thesis by (rule mult_le_mono2)
    qed
    have "two_prov_iff (Conn c as) (Conn c as) ?R"
      by (rule two_prov_iff_mono[OF r0 r1])
    thus ?case by simp
  next
    case (Suc k)
    have k_lt: "k < length as" using Suc.prems by simp
    have k_le': "k \<le> length as" using k_lt by simp
    have k_bs: "k < length bs" using k_lt len_bs by simp
    have ih: "two_prov_iff (Conn c as) (Conn c (take k bs @ drop k as)) (?R + k * ?C)"
      by (rule Suc.IH[OF k_le'])
    \<comment> \<open>the single slot that changes in this step\<close>
    have k_ar: "k < arity (alphabet Ftwo) c" using k_lt len_as by simp
    have hk_len: "length (take k bs @ drop k as) = arity (alphabet Ftwo) c"
      using hyb_len[OF k_le'] len_as by simp
    have bk_wf: "formula_well_formed (alphabet Ftwo) (bs ! k)"
      by (rule wf_bs[OF nth_mem[OF k_bs]])
    have hk_nth: "(take k bs @ drop k as) ! k = as ! k"
      using hybrid_nth[OF len_bs k_le' k_lt] by simp
    have slot_pre: "two_prov_iff ((take k bs @ drop k as) ! k) (bs ! k) m"
      using pw[OF k_lt] hk_nth by simp
    have slot: "two_prov_iff (Conn c (take k bs @ drop k as))
                  (Conn c ((take k bs @ drop k as)[k := bs ! k]))
                  (m + two_slot_bound
                       * max 1 (len_formula ((take k bs @ drop k as) ! k)
                                 + len_formula (bs ! k)
                                 + sum_list (map len_formula (take k bs @ drop k as))))"
      by (rule two_prov_iff_slot[OF k_ar hk_len hyb_elem_wf bk_wf slot_pre])
    \<comment> \<open>every formula the slot step mentions is small\<close>
    have as_k_le: "len_formula (as ! k) \<le> ?S"
    proof -
      have "len_formula (as ! k) \<in> len_formula ` set as"
        using nth_mem[OF k_lt] by (rule imageI)
      hence "len_formula (as ! k) \<in> set (map len_formula as)" by simp
      hence "len_formula (as ! k) \<le> sum_list (map len_formula as)"
        by (rule member_le_sum_list) simp
      thus ?thesis unfolding two_arg_size_def by simp
    qed
    have bs_k_le: "len_formula (bs ! k) \<le> ?S"
    proof -
      have "len_formula (bs ! k) \<in> len_formula ` set bs"
        using nth_mem[OF k_bs] by (rule imageI)
      hence "len_formula (bs ! k) \<in> set (map len_formula bs)" by simp
      hence "len_formula (bs ! k) \<le> sum_list (map len_formula bs)"
        by (rule member_le_sum_list) simp
      thus ?thesis unfolding two_arg_size_def by simp
    qed
    have three: "len_formula ((take k bs @ drop k as) ! k) + len_formula (bs ! k)
                   + sum_list (map len_formula (take k bs @ drop k as)) \<le> 3 * ?S"
    proof -
      have a1: "len_formula ((take k bs @ drop k as) ! k) \<le> ?S"
        using as_k_le hk_nth by simp
      have "len_formula ((take k bs @ drop k as) ! k) + len_formula (bs ! k)
              + sum_list (map len_formula (take k bs @ drop k as)) \<le> ?S + ?S + ?S"
        by (intro add_mono a1 bs_k_le hyb_sum)
      thus ?thesis by simp
    qed
    have slot2: "two_prov_iff (Conn c (take k bs @ drop k as))
                   (Conn c ((take k bs @ drop k as)[k := bs ! k]))
                   (m + two_slot_bound * max 1 (3 * ?S))"
    proof (rule two_prov_iff_mono[OF slot])
      have "max 1 (len_formula ((take k bs @ drop k as) ! k) + len_formula (bs ! k)
                    + sum_list (map len_formula (take k bs @ drop k as)))
            \<le> max 1 (3 * ?S)"
        using three by (rule max.mono[OF order_refl])
      hence "two_slot_bound
               * max 1 (len_formula ((take k bs @ drop k as) ! k) + len_formula (bs ! k)
                         + sum_list (map len_formula (take k bs @ drop k as)))
             \<le> two_slot_bound * max 1 (3 * ?S)"
        by (rule mult_le_mono2)
      thus "m + two_slot_bound
                 * max 1 (len_formula ((take k bs @ drop k as) ! k) + len_formula (bs ! k)
                           + sum_list (map len_formula (take k bs @ drop k as)))
            \<le> m + two_slot_bound * max 1 (3 * ?S)"
        by simp
    qed
    have hstep: "(take k bs @ drop k as)[k := bs ! k] = take (Suc k) bs @ drop (Suc k) as"
      using hybrid_step[OF len_bs k_lt] by (rule sym)
    have slot3: "two_prov_iff (Conn c (take k bs @ drop k as))
                   (Conn c (take (Suc k) bs @ drop (Suc k) as))
                   (m + two_slot_bound * max 1 (3 * ?S))"
      using slot2 hstep by simp
    \<comment> \<open>glue the new step onto the chain built so far\<close>
    have wfB: "formula_well_formed (alphabet Ftwo) (Conn c (take k bs @ drop k as))"
      by (rule hyb_wf[OF k_le'])
    have wfC: "formula_well_formed (alphabet Ftwo)
                 (Conn c (take (Suc k) bs @ drop (Suc k) as))"
      by (rule hyb_wf[OF Suc.prems])
    have tr: "two_prov_iff (Conn c as) (Conn c (take (Suc k) bs @ drop (Suc k) as))
                ((?R + k * ?C) + (m + two_slot_bound * max 1 (3 * ?S))
                 + len_proof two_bal.trans_base_proof
                     * max 1 (len_formula (Conn c as)
                              + len_formula (Conn c (take k bs @ drop k as))
                              + len_formula (Conn c (take (Suc k) bs @ drop (Suc k) as))))"
      by (rule two_prov_iff_trans[OF ih slot3 as_wf wfB wfC])
    have sizes3: "len_formula (Conn c as)
                    + len_formula (Conn c (take k bs @ drop k as))
                    + len_formula (Conn c (take (Suc k) bs @ drop (Suc k) as))
                  \<le> 3 * Suc ?S"
    proof -
      have "len_formula (Conn c as)
              + len_formula (Conn c (take k bs @ drop k as))
              + len_formula (Conn c (take (Suc k) bs @ drop (Suc k) as))
            \<le> Suc ?S + Suc ?S + Suc ?S"
        by (intro add_mono as_size hyb_size)
      thus ?thesis by simp
    qed
    have trans_le: "len_proof two_bal.trans_base_proof
                      * max 1 (len_formula (Conn c as)
                               + len_formula (Conn c (take k bs @ drop k as))
                               + len_formula (Conn c (take (Suc k) bs @ drop (Suc k) as)))
                    \<le> len_proof two_bal.trans_base_proof * max 1 (3 * Suc ?S)"
    proof -
      have "max 1 (len_formula (Conn c as)
                   + len_formula (Conn c (take k bs @ drop k as))
                   + len_formula (Conn c (take (Suc k) bs @ drop (Suc k) as)))
            \<le> max 1 (3 * Suc ?S)"
        using sizes3 by (rule max.mono[OF order_refl])
      thus ?thesis by (rule mult_le_mono2)
    qed
    have cost: "(?R + k * ?C) + (m + two_slot_bound * max 1 (3 * ?S))
                 + len_proof two_bal.trans_base_proof
                     * max 1 (len_formula (Conn c as)
                              + len_formula (Conn c (take k bs @ drop k as))
                              + len_formula (Conn c (take (Suc k) bs @ drop (Suc k) as)))
               \<le> ?R + Suc k * ?C"
    proof -
      have "(?R + k * ?C) + (m + two_slot_bound * max 1 (3 * ?S))
              + len_proof two_bal.trans_base_proof
                  * max 1 (len_formula (Conn c as)
                           + len_formula (Conn c (take k bs @ drop k as))
                           + len_formula (Conn c (take (Suc k) bs @ drop (Suc k) as)))
            \<le> (?R + k * ?C) + (m + two_slot_bound * max 1 (3 * ?S))
              + len_proof two_bal.trans_base_proof * max 1 (3 * Suc ?S)"
        using trans_le by (rule add_left_mono)
      also have "\<dots> = ?R + k * ?C + ?C"
        unfolding two_slot_step_cost_def by (simp add: algebra_simps)
      also have "\<dots> = ?R + Suc k * ?C" by (simp add: algebra_simps)
      finally show ?thesis .
    qed
    show ?case by (rule two_prov_iff_mono[OF tr cost])
  qed
qed


text \<open>
  Instantiating the prefix induction at \<open>k = length as\<close> rewrites EVERY argument, which is
  the k-ary connective congruence the roundtrip induction needs.  The number of slots is
  replaced by the alphabet-wide constant \<^const>\<open>two_max_arity\<close> so that the bound no
  longer mentions the particular connective.
\<close>

lemma two_prov_iff_conn:
  fixes c :: 'c2
  assumes len_as: "length as = arity (alphabet Ftwo) c"
      and len_bs: "length bs = length as"
      and wf_as: "\<And>g. g \<in> set as \<Longrightarrow> formula_well_formed (alphabet Ftwo) g"
      and wf_bs: "\<And>g. g \<in> set bs \<Longrightarrow> formula_well_formed (alphabet Ftwo) g"
      and pw: "\<And>j. j < length as \<Longrightarrow> two_prov_iff (as ! j) (bs ! j) m"
    shows "two_prov_iff (Conn c as) (Conn c bs)
             (len_proof two_refl_base * max 1 (Suc (two_arg_size as bs))
                + two_max_arity * two_slot_step_cost m (two_arg_size as bs))"
proof -
  have full: "two_prov_iff (Conn c as) (Conn c (take (length as) bs @ drop (length as) as))
                (len_proof two_refl_base * max 1 (Suc (two_arg_size as bs))
                   + length as * two_slot_step_cost m (two_arg_size as bs))"
    by (rule two_prov_iff_conn_prefix[OF len_as len_bs wf_as wf_bs pw order_refl])
  have hyb_all: "take (length as) bs @ drop (length as) as = bs"
    using len_bs by simp
  have base: "two_prov_iff (Conn c as) (Conn c bs)
                (len_proof two_refl_base * max 1 (Suc (two_arg_size as bs))
                   + length as * two_slot_step_cost m (two_arg_size as bs))"
    using full hyb_all by simp
  have ar: "length as \<le> two_max_arity" using len_as two_max_arity_ge[of c] by simp
  have "length as * two_slot_step_cost m (two_arg_size as bs)
      \<le> two_max_arity * two_slot_step_cost m (two_arg_size as bs)"
    using ar by (rule mult_le_mono1)
  hence le: "len_proof two_refl_base * max 1 (Suc (two_arg_size as bs))
               + length as * two_slot_step_cost m (two_arg_size as bs)
             \<le> len_proof two_refl_base * max 1 (Suc (two_arg_size as bs))
               + two_max_arity * two_slot_step_cost m (two_arg_size as bs)"
    by (rule add_left_mono)
  show ?thesis by (rule two_prov_iff_mono[OF base le])
qed


subsection \<open>The roundtrip base equivalence over fresh atoms\<close>

text \<open>
  \<^const>\<open>roundtrip_base_proof\<close> is stated over the MARKER variables, and those are
  produced by \<^const>\<open>marker_variables\<close>, whose specification promises only length and
  distinctness -- in particular nothing keeps them away from the variables of
  \<^text>\<open>conn_iff\<close>.  Substituting into that proof would therefore not commute with
  \<^text>\<open>iff_form\<close>.  Renaming the markers onto \<^text>\<open>two_bal.canonical_atoms\<close>, which
  ARE fresh for \<open>conn_iff\<close> by construction, repairs this at no cost: the renamed template
  still meets the template specification, so its equivalence with the bare connective
  again has a proof of constant size.
\<close>

lemma roundtrip_template_var_set:
  "var_set_form (roundtrip_template c)
     \<subseteq> set (marker_variables (arity (alphabet Ftwo) c))"
proof -
  have tmpl_wf: "formula_well_formed (alphabet Fone) (rev.connective_template c)"
    using rev.connective_template_spec by blast
  have "var_set_form (roundtrip_template c)
      \<subseteq> var_set_form (rev.connective_template c)"
    unfolding roundtrip_template_def by (rule translate_formula_var_set[OF tmpl_wf])
  thus ?thesis using rev.connective_template_spec by blast
qed

definition roundtrip_canon :: "'c2 \<Rightarrow> 'c2 formula" where
  "roundtrip_canon c = sub_formula
     (marker_substitution (marker_variables (arity (alphabet Ftwo) c))
        (map Atom (two_bal.canonical_atoms c)))
     (roundtrip_template c)"

lemma roundtrip_canon_wf:
  "formula_well_formed (alphabet Ftwo) (roundtrip_canon c)"
proof -
  let ?mu = "marker_substitution (marker_variables (arity (alphabet Ftwo) c))
               (map Atom (two_bal.canonical_atoms c))"
  have mu_wf: "formula_well_formed (alphabet Ftwo) (?mu v)" for v
  proof -
    have atoms_wf: "formula_well_formed (alphabet Ftwo) g"
      if "g \<in> set (map Atom (two_bal.canonical_atoms c)) \<union> {Atom v}" for g
      using that by auto
    have "?mu v \<in> set (map Atom (two_bal.canonical_atoms c)) \<union> {Atom v}"
      by (rule marker_substitution_range)
    thus ?thesis by (rule atoms_wf)
  qed
  show ?thesis
    unfolding roundtrip_canon_def
    by (rule sub_formula_well_formed[OF roundtrip_template_wf mu_wf])
qed

lemma roundtrip_canon_eval:
  "eval (alphabet Ftwo) val (roundtrip_canon c)
   = conn_evals (alphabet Ftwo) c (map val (two_bal.canonical_atoms c))"
proof -
  let ?names = "marker_variables (arity (alphabet Ftwo) c)"
  let ?canon = "two_bal.canonical_atoms c"
  let ?mu = "marker_substitution ?names (map Atom ?canon)"
  have len_names: "length ?names = arity (alphabet Ftwo) c" and dist: "distinct ?names"
    using marker_variables_spec by blast+
  have len_canon: "length ?canon = arity (alphabet Ftwo) c"
    using two_bal.canonical_atoms_spec by blast
  have inner: "map (\<lambda>v. eval (alphabet Ftwo) val (?mu v)) ?names = map val ?canon"
  proof (rule nth_equalityI)
    show "length (map (\<lambda>v. eval (alphabet Ftwo) val (?mu v)) ?names) = length (map val ?canon)"
      using len_names len_canon by simp
  next
    fix i assume "i < length (map (\<lambda>v. eval (alphabet Ftwo) val (?mu v)) ?names)"
    hence i_lt: "i < length ?names" by simp
    hence i_canon: "i < length ?canon" using len_names len_canon by simp
    have args_len: "length (map Atom ?canon) = length ?names"
      using len_names len_canon by simp
    have mu_i: "?mu (?names ! i) = Atom (?canon ! i)"
      using marker_substitution_nth[OF dist args_len i_lt] i_canon by simp
    show "map (\<lambda>v. eval (alphabet Ftwo) val (?mu v)) ?names ! i = map val ?canon ! i"
    proof -
      have "map (\<lambda>v. eval (alphabet Ftwo) val (?mu v)) ?names ! i
          = eval (alphabet Ftwo) val (?mu (?names ! i))"
        using i_lt by simp
      also have "\<dots> = val (?canon ! i)" unfolding mu_i by simp
      also have "\<dots> = map val ?canon ! i" using i_canon by simp
      finally show ?thesis .
    qed
  qed
  have "eval (alphabet Ftwo) val (roundtrip_canon c)
      = eval (alphabet Ftwo) (\<lambda>v. eval (alphabet Ftwo) val (?mu v)) (roundtrip_template c)"
    unfolding roundtrip_canon_def by (rule sub_formula_eval)
  also have "\<dots> = conn_evals (alphabet Ftwo) c
                   (map (\<lambda>v. eval (alphabet Ftwo) val (?mu v)) ?names)"
    by (rule roundtrip_template_eval)
  also have "\<dots> = conn_evals (alphabet Ftwo) c (map val ?canon)"
    using inner by simp
  finally show ?thesis .
qed

definition roundtrip_canon_proof :: "'c2 \<Rightarrow> 'c2 frege_proof" where
  "roundtrip_canon_proof c =
     two_bal.entails_proof {}
       (two_bal.iff_form (roundtrip_canon c)
          (Conn c (map Atom (two_bal.canonical_atoms c))))"

lemma roundtrip_canon_proof_spec:
  "valid_proof Ftwo (roundtrip_canon_proof c)
   \<and> assumptions (roundtrip_canon_proof c) = {}
   \<and> thesis (roundtrip_canon_proof c)
       = two_bal.iff_form (roundtrip_canon c)
           (Conn c (map Atom (two_bal.canonical_atoms c)))
   \<and> (\<forall> st \<in> set (steps (roundtrip_canon_proof c)).
        formula_well_formed (alphabet Ftwo) st)"
proof -
  let ?canon = "two_bal.canonical_atoms c"
  have len_canon: "length ?canon = arity (alphabet Ftwo) c"
    using two_bal.canonical_atoms_spec by blast
  have wf_rhs: "formula_well_formed (alphabet Ftwo) (Conn c (map Atom ?canon))"
    using len_canon by simp
  have wf_lhs: "formula_well_formed (alphabet Ftwo) (roundtrip_canon c)"
    by (rule roundtrip_canon_wf)
  have wf_fs: "\<forall> f \<in> {}. formula_well_formed (alphabet Ftwo) f" by simp
  have wf_th: "formula_well_formed (alphabet Ftwo)
                 (two_bal.iff_form (roundtrip_canon c) (Conn c (map Atom ?canon)))"
    by (rule two_bal.iff_form_wf[OF wf_lhs wf_rhs])
  have sem: "\<forall> val. (\<forall> f \<in> {}. eval (alphabet Ftwo) val f)
             \<longrightarrow> eval (alphabet Ftwo) val
                  (two_bal.iff_form (roundtrip_canon c) (Conn c (map Atom ?canon)))"
  proof (intro allI impI)
    fix val
    have "eval (alphabet Ftwo) val (roundtrip_canon c)
        = conn_evals (alphabet Ftwo) c (map val ?canon)"
      by (rule roundtrip_canon_eval)
    also have "\<dots> = eval (alphabet Ftwo) val (Conn c (map Atom ?canon))"
      by (simp add: comp_def)
    finally show "eval (alphabet Ftwo) val
                    (two_bal.iff_form (roundtrip_canon c) (Conn c (map Atom ?canon)))"
      using two_bal.iff_form_eval by simp
  qed
  show ?thesis
    unfolding roundtrip_canon_proof_def
    using two_bal.entails_proof_spec[OF wf_fs wf_th sem] .
qed

definition roundtrip_canon_bound :: nat where
  "roundtrip_canon_bound = Max ((\<lambda> c :: 'c2. len_proof (roundtrip_canon_proof c)) ` UNIV)"

lemma roundtrip_canon_bound_ge:
  "len_proof (roundtrip_canon_proof c) \<le> roundtrip_canon_bound"
  unfolding roundtrip_canon_bound_def
  using two.finite_alphabet by (intro Max_ge) auto


lemma sub_formula_after:
  "sub_formula t (sub_formula s f) = sub_formula (\<lambda>v. sub_formula t (s v)) f"
  by (induction f) simp_all

lemma roundtrip_canon_subst:
  assumes wf: "formula_well_formed (alphabet Ftwo) (Conn c args)"
  shows "sub_formula
           (marker_substitution (two_bal.canonical_atoms c)
              (map (\<lambda>g. translate_formula (rev.translate_formula g)) args))
           (roundtrip_canon c)
       = translate_formula (rev.translate_formula (Conn c args))"
proof -
  let ?names = "marker_variables (arity (alphabet Ftwo) c)"
  let ?canon = "two_bal.canonical_atoms c"
  let ?args = "map (\<lambda>g. translate_formula (rev.translate_formula g)) args"
  let ?mu = "marker_substitution ?names (map Atom ?canon)"
  let ?rho = "marker_substitution ?canon ?args"
  have len_args: "length args = arity (alphabet Ftwo) c" using wf by simp
  have len_names: "length ?names = arity (alphabet Ftwo) c" and dist: "distinct ?names"
    using marker_variables_spec by blast+
  have len_canon: "length ?canon = arity (alphabet Ftwo) c" and dist_c: "distinct ?canon"
    using two_bal.canonical_atoms_spec by blast+
  have l1: "length (map Atom ?canon) = length ?names" using len_names len_canon by simp
  have l2: "length ?args = length ?canon" using len_args len_canon by simp
  have l3: "length ?args = length ?names" using len_args len_names by simp
  have agree: "sub_formula ?rho (?mu u) = marker_substitution ?names ?args u"
    if u_in: "u \<in> var_set_form (roundtrip_template c)" for u
  proof -
    have u_names: "u \<in> set ?names" using u_in roundtrip_template_var_set by blast
    have "\<exists> i < length ?names. ?names ! i = u"
      using u_names by (simp add: in_set_conv_nth)
    then obtain i where i_lt: "i < length ?names" and u_eq: "u = ?names ! i" by auto
    have i_canon: "i < length ?canon" using i_lt len_names len_canon by simp
    have "sub_formula ?rho (?mu u) = sub_formula ?rho (?mu (?names ! i))"
      using u_eq by simp
    also have "\<dots> = sub_formula ?rho (map Atom ?canon ! i)"
      by (rule arg_cong[OF marker_substitution_nth[OF dist l1 i_lt]])
    also have "\<dots> = sub_formula ?rho (Atom (?canon ! i))"
      using i_canon by simp
    also have "\<dots> = ?rho (?canon ! i)" by simp
    also have "\<dots> = ?args ! i" by (rule marker_substitution_nth[OF dist_c l2 i_canon])
    finally have lhs: "sub_formula ?rho (?mu u) = ?args ! i" .
    have "marker_substitution ?names ?args u = marker_substitution ?names ?args (?names ! i)"
      using u_eq by simp
    also have "\<dots> = ?args ! i" by (rule marker_substitution_nth[OF dist l3 i_lt])
    finally show ?thesis using lhs by simp
  qed
  have "sub_formula ?rho (roundtrip_canon c)
      = sub_formula (\<lambda>u. sub_formula ?rho (?mu u)) (roundtrip_template c)"
    unfolding roundtrip_canon_def by (rule sub_formula_after)
  also have "\<dots> = sub_formula (marker_substitution ?names ?args) (roundtrip_template c)"
    by (rule sub_formula_cong) (rule agree)
  also have "\<dots> = translate_formula (rev.translate_formula (Conn c args))"
    using roundtrip_unfold[OF wf] by simp
  finally show ?thesis .
qed

text \<open>
  One node of the roundtrip: the composed translation of \<open>Conn c args\<close> is provably
  equivalent to the connective applied to the composed translations of the arguments.
  The cost is the CONSTANT \<^const>\<open>roundtrip_canon_bound\<close> scaled by the size of the
  translated arguments -- the usual price of instantiating a fixed proof by a
  substitution.
\<close>

lemma roundtrip_conn_step:
  assumes wf: "formula_well_formed (alphabet Ftwo) (Conn c args)"
  shows "two_prov_iff (translate_formula (rev.translate_formula (Conn c args)))
           (Conn c (map (\<lambda>g. translate_formula (rev.translate_formula g)) args))
           (roundtrip_canon_bound
              * max 1 (sum_list (map len_formula
                   (map (\<lambda>g. translate_formula (rev.translate_formula g)) args))))"
proof -
  let ?canon = "two_bal.canonical_atoms c"
  let ?args = "map (\<lambda>g. translate_formula (rev.translate_formula g)) args"
  let ?rho = "marker_substitution ?canon ?args"
  have len_args: "length args = arity (alphabet Ftwo) c" using wf by simp
  have len_canon: "length ?canon = arity (alphabet Ftwo) c"
   and dist_c: "distinct ?canon"
   and canon_ci: "set ?canon \<inter> var_set_form two_bal.conn_iff = {}"
    using two_bal.canonical_atoms_spec by blast+
  have l2: "length ?args = length ?canon" using len_args len_canon by simp
  have map_rho: "map ?rho ?canon = ?args"
  proof (rule nth_equalityI)
    show "length (map ?rho ?canon) = length ?args" using l2 by simp
  next
    fix i assume "i < length (map ?rho ?canon)"
    hence i_lt: "i < length ?canon" by simp
    have "map ?rho ?canon ! i = ?rho (?canon ! i)" using i_lt by simp
    also have "\<dots> = ?args ! i" by (rule marker_substitution_nth[OF dist_c l2 i_lt])
    finally show "map ?rho ?canon ! i = ?args ! i" .
  qed
  have canon_sub: "sub_formula ?rho (Conn c (map Atom ?canon)) = Conn c ?args"
  proof -
    have "map (sub_formula ?rho) (map Atom ?canon) = map ?rho ?canon"
      by (simp add: comp_def)
    thus ?thesis using map_rho by simp
  qed
  have rho_id: "?rho w = Atom w"
    if "w \<in> var_set_form two_bal.conn_iff" "w \<noteq> ''a''" "w \<noteq> ''b''" for w
  proof -
    have "w \<notin> set ?canon" using that(1) canon_ci by blast
    thus ?thesis by (rule marker_substitution_outside)
  qed
  have rho_wf: "formula_well_formed (alphabet Ftwo) (?rho v)" for v
  proof -
    have args_wf: "formula_well_formed (alphabet Ftwo) g"
      if "g \<in> set ?args \<union> {Atom v}" for g
      using that translate_formula_well_formed by auto
    have "?rho v \<in> set ?args \<union> {Atom v}" by (rule marker_substitution_range)
    thus ?thesis by (rule args_wf)
  qed
  \<comment> \<open>instantiate the constant-size per-connective base proof\<close>
  define ti where ti_def: "ti = sub_proof ?rho (roundtrip_canon_proof c)"
  have valid_ti: "valid_proof Ftwo ti"
    unfolding ti_def using two.proof_substitution roundtrip_canon_proof_spec by blast
  have ti_asm: "assumptions ti = {}"
    unfolding ti_def using roundtrip_canon_proof_spec by simp
  have ti_th: "thesis ti = two_bal.iff_form
                 (translate_formula (rev.translate_formula (Conn c args))) (Conn c ?args)"
  proof -
    have "thesis ti = sub_formula ?rho
            (two_bal.iff_form (roundtrip_canon c) (Conn c (map Atom ?canon)))"
      unfolding ti_def using roundtrip_canon_proof_spec by simp
    also have "\<dots> = two_bal.iff_form (sub_formula ?rho (roundtrip_canon c))
                     (sub_formula ?rho (Conn c (map Atom ?canon)))"
      by (rule two_bal.sub_formula_iff_form[OF rho_id])
    also have "\<dots> = two_bal.iff_form
                     (translate_formula (rev.translate_formula (Conn c args)))
                     (Conn c ?args)"
      using roundtrip_canon_subst[OF wf] canon_sub by simp
    finally show ?thesis .
  qed
  have ti_wf: "\<forall> st \<in> set (steps ti). formula_well_formed (alphabet Ftwo) st"
  proof
    fix st assume "st \<in> set (steps ti)"
    then obtain s0 where s0: "s0 \<in> set (steps (roundtrip_canon_proof c))"
      and st_eq: "st = sub_formula ?rho s0"
      unfolding ti_def by auto
    have wf0: "formula_well_formed (alphabet Ftwo) s0"
      using roundtrip_canon_proof_spec s0 by blast
    show "formula_well_formed (alphabet Ftwo) st"
      using st_eq sub_formula_well_formed[OF wf0 rho_wf] by simp
  qed
  have len_rho: "len_sub (set ?canon) ?rho = max 1 (sum_list (map len_formula ?args))"
  proof -
    have "(\<Sum> v \<in> set ?canon. len_formula (?rho v))
        = sum_list (map (\<lambda>v. len_formula (?rho v)) ?canon)"
      using dist_c by (simp add: sum_list_distinct_conv_sum_set)
    also have "\<dots> = sum_list (map len_formula (map ?rho ?canon))" by (simp add: o_def)
    also have "\<dots> = sum_list (map len_formula ?args)" using map_rho by simp
    finally show ?thesis unfolding len_sub_def by simp
  qed
  have ti_len: "len_proof ti
                  \<le> roundtrip_canon_bound * max 1 (sum_list (map len_formula ?args))"
  proof -
    have fin: "finite (set ?canon)" by simp
    have outside: "\<forall>v. v \<notin> set ?canon \<longrightarrow> ?rho v = Atom v"
      using marker_substitution_outside by blast
    have "len_proof ti \<le> len_proof (roundtrip_canon_proof c) * len_sub (set ?canon) ?rho"
      unfolding ti_def by (rule sub_proof_bound[OF fin outside])
    also have "\<dots> \<le> roundtrip_canon_bound * max 1 (sum_list (map len_formula ?args))"
      using roundtrip_canon_bound_ge len_rho by (simp add: mult_le_mono1)
    finally show ?thesis .
  qed
  show ?thesis
    unfolding two_prov_iff_def
    using valid_ti ti_asm ti_th ti_wf ti_len by blast
qed


subsection \<open>The roundtrip induction\<close>

text \<open>
  The composed map \<open>\<Phi> = translate_formula \<circ> rev.translate_formula\<close> sends Ftwo-formulas to
  Ftwo-formulas, and the two previous lemmas give, one node at a time, an Ftwo-proof that
  \<open>\<Phi> \<sigma>\<close> is equivalent to \<open>\<sigma>\<close>.  Assembling them costs a bounded factor per LEVEL of \<open>\<sigma>\<close>:
  each of the up to \<^const>\<open>two_max_arity\<close> slot rewrites pays separately for the
  equivalence of the argument it rewrites, so the cost of a level is a constant multiple
  of the cost of the level below.  The total is therefore a constant to the power of the
  DEPTH, times the weight below.  That is exactly the shape the translation itself already
  has (\<^text>\<open>rev.translate_formula_length\<close>), and it is polynomial for the
  logarithmic-depth formulas Spira balancing produces.
\<close>

fun roundtrip_weight :: "'c2 formula \<Rightarrow> nat" where
  "roundtrip_weight (Atom v) = 2"
| "roundtrip_weight (Conn c args) =
     len_formula (translate_formula (rev.translate_formula (Conn c args)))
       + len_formula (Conn c args) + sum_list (map roundtrip_weight args)"

lemma roundtrip_weight_ge_1: "1 \<le> roundtrip_weight f"
proof (cases f)
  case (Atom v)
  thus ?thesis by simp
next
  case (Conn c args)
  have "1 \<le> len_formula (translate_formula (rev.translate_formula (Conn c args)))"
    by (rule len_formula_positive)
  thus ?thesis using Conn by simp
qed

lemma roundtrip_len_phi:
  "len_formula (translate_formula (rev.translate_formula f)) \<le> roundtrip_weight f"
proof (cases f)
  case (Atom v)
  have "translate_formula (rev.translate_formula (Atom v)) = Atom v" by simp
  thus ?thesis using Atom by simp
next
  case (Conn c args)
  thus ?thesis by simp
qed

lemma roundtrip_len: "len_formula f \<le> roundtrip_weight f"
  by (cases f) simp_all

lemma roundtrip_weight_arg:
  assumes "g \<in> set args"
  shows "roundtrip_weight g \<le> roundtrip_weight (Conn c args)"
proof -
  have "roundtrip_weight g \<in> roundtrip_weight ` set args"
    using assms by (rule imageI)
  hence "roundtrip_weight g \<in> set (map roundtrip_weight args)" by simp
  hence "roundtrip_weight g \<le> sum_list (map roundtrip_weight args)"
    by (rule member_le_sum_list) simp
  thus ?thesis by simp
qed

lemma roundtrip_arg_size:
  "two_arg_size (map (\<lambda>g. translate_formula (rev.translate_formula g)) args) args
     \<le> roundtrip_weight (Conn c args)"
proof -
  have p1: "sum_list (map len_formula
              (map (\<lambda>g. translate_formula (rev.translate_formula g)) args))
          \<le> sum_list (map roundtrip_weight args)"
  proof -
    have "sum_list (map len_formula
            (map (\<lambda>g. translate_formula (rev.translate_formula g)) args))
        = sum_list (map (\<lambda>g. len_formula (translate_formula (rev.translate_formula g))) args)"
      by (simp add: o_def)
    also have "\<dots> \<le> sum_list (map roundtrip_weight args)"
      by (rule sum_list_mono) (rule roundtrip_len_phi)
    finally show ?thesis .
  qed
  have p2: "sum_list (map len_formula args) \<le> len_formula (Conn c args)" by simp
  show ?thesis
    unfolding two_arg_size_def using add_mono[OF p1 p2] by simp
qed

lemma max_one_le: "1 \<le> (n :: nat) \<Longrightarrow> m \<le> n \<Longrightarrow> max 1 m \<le> n"
  by simp

definition roundtrip_const :: nat where
  "roundtrip_const = roundtrip_canon_bound + 2 * len_proof two_refl_base
     + two_max_arity * (1 + 3 * two_slot_bound
                          + 6 * len_proof two_bal.trans_base_proof)
     + 4 * len_proof two_bal.trans_base_proof + 1"

lemma roundtrip_const_ge_1: "1 \<le> roundtrip_const"
  unfolding roundtrip_const_def by simp


lemma roundtrip_provable:
  assumes "formula_well_formed (alphabet Ftwo) sigma"
  shows "two_prov_iff (translate_formula (rev.translate_formula sigma)) sigma
           (roundtrip_const ^ depth_formula sigma * roundtrip_weight sigma)"
  using assms
proof (induction sigma)
  case (Atom v)
  have tr: "translate_formula (rev.translate_formula (Atom v)) = Atom v" by simp
  have wfa: "formula_well_formed (alphabet Ftwo) (Atom v)" by simp
  have r1: "len_proof two_refl_base * max 1 (len_formula (Atom v))
            \<le> roundtrip_const ^ depth_formula (Atom v) * roundtrip_weight (Atom v)"
  proof -
    have "len_proof two_refl_base \<le> roundtrip_const"
      unfolding roundtrip_const_def by simp
    thus ?thesis by simp
  qed
  have "two_prov_iff (Atom v) (Atom v)
          (roundtrip_const ^ depth_formula (Atom v) * roundtrip_weight (Atom v))"
    by (rule two_prov_iff_mono[OF two_prov_iff_refl[OF wfa] r1])
  thus ?case using tr by simp
next
  case (Conn c args)
  let ?K = "roundtrip_const"
  let ?AS = "map (\<lambda>g. translate_formula (rev.translate_formula g)) args"
  let ?W = "roundtrip_weight (Conn c args)"
  let ?S = "two_arg_size ?AS args"
  let ?D = "depth_formula (Conn c args)"
  let ?P = "?K ^ (?D - 1)"
  let ?Q = "?P * ?W"
  let ?TB = "len_proof two_bal.trans_base_proof"
  have wf: "formula_well_formed (alphabet Ftwo) (Conn c args)" using Conn.prems .
  have len_args: "length args = arity (alphabet Ftwo) c" using wf by simp
  have wf_arg: "formula_well_formed (alphabet Ftwo) g" if "g \<in> set args" for g
    using wf that by simp
  have W1: "1 \<le> ?W" by (rule roundtrip_weight_ge_1)
  have K1: "1 \<le> ?K" by (rule roundtrip_const_ge_1)
  have P1: "1 \<le> ?P" using K1 by simp
  have Q1: "1 \<le> ?Q" using P1 W1 by simp
  have W_Q: "?W \<le> ?Q" using mult_le_mono1[OF P1, of ?W] by simp
  have S_le: "?S \<le> ?W" by (rule roundtrip_arg_size)
  have D1: "1 \<le> ?D" by (cases "args = []") simp_all
  have KD: "?K ^ ?D = ?K * ?P"
  proof -
    have "?K ^ ?D = ?K ^ Suc (?D - 1)" using D1 by simp
    thus ?thesis by simp
  qed
  have as_sum: "sum_list (map len_formula ?AS) \<le> ?W"
  proof -
    have "sum_list (map len_formula ?AS) \<le> ?S" unfolding two_arg_size_def by simp
    thus ?thesis using S_le by simp
  qed
  \<comment> \<open>the template node: one instance of the constant-size per-connective proof\<close>
  have step0: "two_prov_iff (translate_formula (rev.translate_formula (Conn c args)))
                 (Conn c ?AS)
                 (roundtrip_canon_bound * max 1 (sum_list (map len_formula ?AS)))"
    by (rule roundtrip_conn_step[OF wf])
  have step: "two_prov_iff (translate_formula (rev.translate_formula (Conn c args)))
                (Conn c ?AS) (roundtrip_canon_bound * ?Q)"
  proof (rule two_prov_iff_mono[OF step0])
    have "max 1 (sum_list (map len_formula ?AS)) \<le> ?W"
      by (rule max_one_le[OF W1 as_sum])
    also have "\<dots> \<le> ?Q" by (rule W_Q)
    finally show "roundtrip_canon_bound * max 1 (sum_list (map len_formula ?AS))
                  \<le> roundtrip_canon_bound * ?Q"
      by (rule mult_le_mono2)
  qed
  \<comment> \<open>the arguments, by the induction hypothesis\<close>
  have as_len: "length ?AS = arity (alphabet Ftwo) c" using len_args by simp
  have bs_len: "length args = length ?AS" by simp
  have as_wf: "formula_well_formed (alphabet Ftwo) g" if "g \<in> set ?AS" for g
    using that translate_formula_well_formed by auto
  have pw: "two_prov_iff (?AS ! j) (args ! j) ?Q" if j_lt: "j < length ?AS" for j
  proof -
    have j_args: "j < length args" using j_lt by simp
    have mem: "args ! j \<in> set args" using j_args by (rule nth_mem)
    have ih: "two_prov_iff (translate_formula (rev.translate_formula (args ! j))) (args ! j)
                (?K ^ depth_formula (args ! j) * roundtrip_weight (args ! j))"
      by (rule Conn.IH[OF mem wf_arg[OF mem]])
    have dep: "depth_formula (args ! j) \<le> ?D - 1"
    proof -
      have ne: "args \<noteq> []" using j_args by auto
      have "depth_formula (args ! j) \<in> depth_formula ` set args"
        using nth_mem[OF j_args] by (rule imageI)
      hence "depth_formula (args ! j) \<in> set (map depth_formula args)" by simp
      hence "depth_formula (args ! j) \<le> Max (set (map depth_formula args))" by simp
      thus ?thesis using ne by simp
    qed
    have pk: "?K ^ depth_formula (args ! j) \<le> ?P" by (rule power_increasing[OF dep K1])
    have "?K ^ depth_formula (args ! j) * roundtrip_weight (args ! j) \<le> ?Q"
      by (rule mult_le_mono[OF pk roundtrip_weight_arg[OF mem]])
    hence "two_prov_iff (translate_formula (rev.translate_formula (args ! j))) (args ! j) ?Q"
      by (rule two_prov_iff_mono[OF ih])
    thus ?thesis using j_args by simp
  qed
  have cong: "two_prov_iff (Conn c ?AS) (Conn c args)
                (len_proof two_refl_base * max 1 (Suc ?S)
                   + two_max_arity * two_slot_step_cost ?Q ?S)"
    by (rule two_prov_iff_conn[OF as_len bs_len as_wf wf_arg pw])
  \<comment> \<open>glue the node onto the arguments\<close>
  have wfA: "formula_well_formed (alphabet Ftwo)
               (translate_formula (rev.translate_formula (Conn c args)))"
    by (rule translate_formula_well_formed)
  have wfB: "formula_well_formed (alphabet Ftwo) (Conn c ?AS)"
    using as_len as_wf by simp
  have tr: "two_prov_iff (translate_formula (rev.translate_formula (Conn c args)))
              (Conn c args)
              (roundtrip_canon_bound * ?Q
                 + (len_proof two_refl_base * max 1 (Suc ?S)
                      + two_max_arity * two_slot_step_cost ?Q ?S)
                 + ?TB * max 1 (len_formula (translate_formula
                                  (rev.translate_formula (Conn c args)))
                                + len_formula (Conn c ?AS)
                                + len_formula (Conn c args)))"
    by (rule two_prov_iff_trans[OF step cong wfA wfB wf])
  \<comment> \<open>every piece of that cost is a constant multiple of \<open>?Q\<close>\<close>
  have b_le: "len_proof two_refl_base * max 1 (Suc ?S)
              \<le> len_proof two_refl_base * (2 * ?Q)"
  proof -
    have "Suc ?S = ?S + 1" by simp
    also have "\<dots> \<le> ?W + ?W" by (rule add_mono[OF S_le W1])
    also have "\<dots> = 2 * ?W" by simp
    also have "\<dots> \<le> 2 * ?Q" using W_Q by simp
    finally have hS: "Suc ?S \<le> 2 * ?Q" .
    have h1: "1 \<le> 2 * ?Q" using Q1 by simp
    have "max 1 (Suc ?S) \<le> 2 * ?Q" by (rule max_one_le[OF h1 hS])
    thus ?thesis by (rule mult_le_mono2)
  qed
  have c_le: "two_max_arity * two_slot_step_cost ?Q ?S
              \<le> two_max_arity * ((1 + 3 * two_slot_bound + 6 * ?TB) * ?Q)"
  proof -
    have e1: "3 * ?S \<le> 3 * ?Q"
    proof -
      have "3 * ?S \<le> 3 * ?W" using S_le by simp
      also have "\<dots> \<le> 3 * ?Q" using W_Q by simp
      finally show ?thesis .
    qed
    have m3: "max 1 (3 * ?S) \<le> 3 * ?Q"
    proof -
      have h1: "1 \<le> 3 * ?Q" using Q1 by simp
      show ?thesis by (rule max_one_le[OF h1 e1])
    qed
    have m6: "max 1 (3 * Suc ?S) \<le> 6 * ?Q"
    proof -
      have e2: "(3 :: nat) \<le> 3 * ?Q" using Q1 by simp
      have "3 * Suc ?S = 3 * ?S + 3" by simp
      also have "\<dots> \<le> 3 * ?Q + 3 * ?Q" by (rule add_mono[OF e1 e2])
      also have "\<dots> = 6 * ?Q" by simp
      finally have h: "3 * Suc ?S \<le> 6 * ?Q" .
      have h1: "1 \<le> 6 * ?Q" using Q1 by simp
      show ?thesis by (rule max_one_le[OF h1 h])
    qed
    have "two_slot_step_cost ?Q ?S
        = (?Q + two_slot_bound * max 1 (3 * ?S)) + ?TB * max 1 (3 * Suc ?S)"
      unfolding two_slot_step_cost_def ..
    also have "\<dots> \<le> (?Q + two_slot_bound * (3 * ?Q)) + ?TB * (6 * ?Q)"
    proof (rule add_mono)
      have "two_slot_bound * max 1 (3 * ?S) \<le> two_slot_bound * (3 * ?Q)"
        by (rule mult_le_mono2[OF m3])
      thus "?Q + two_slot_bound * max 1 (3 * ?S) \<le> ?Q + two_slot_bound * (3 * ?Q)"
        by (rule add_left_mono)
    next
      show "?TB * max 1 (3 * Suc ?S) \<le> ?TB * (6 * ?Q)"
        by (rule mult_le_mono2[OF m6])
    qed
    also have "\<dots> = (1 + 3 * two_slot_bound + 6 * ?TB) * ?Q"
      by (simp add: algebra_simps)
    finally have "two_slot_step_cost ?Q ?S \<le> (1 + 3 * two_slot_bound + 6 * ?TB) * ?Q" .
    thus ?thesis by (rule mult_le_mono2)
  qed
  have d_le: "?TB * max 1 (len_formula (translate_formula
                              (rev.translate_formula (Conn c args)))
                            + len_formula (Conn c ?AS) + len_formula (Conn c args))
              \<le> ?TB * (4 * ?Q)"
  proof -
    have t1: "len_formula (translate_formula (rev.translate_formula (Conn c args))) \<le> ?W"
      by (rule roundtrip_len_phi)
    have t2: "len_formula (Conn c ?AS) \<le> 2 * ?W"
    proof -
      have "len_formula (Conn c ?AS) = 1 + sum_list (map len_formula ?AS)" by simp
      also have "\<dots> \<le> ?W + ?W" by (rule add_mono[OF W1 as_sum])
      also have "\<dots> = 2 * ?W" by simp
      finally show ?thesis .
    qed
    have t3: "len_formula (Conn c args) \<le> ?W" by (rule roundtrip_len)
    have "len_formula (translate_formula (rev.translate_formula (Conn c args)))
            + len_formula (Conn c ?AS) + len_formula (Conn c args)
          \<le> ?W + 2 * ?W + ?W"
      by (intro add_mono t1 t2 t3)
    also have "\<dots> = 4 * ?W" by simp
    also have "\<dots> \<le> 4 * ?Q" using W_Q by simp
    finally have h: "len_formula (translate_formula
                        (rev.translate_formula (Conn c args)))
                      + len_formula (Conn c ?AS) + len_formula (Conn c args) \<le> 4 * ?Q" .
    have h1: "1 \<le> 4 * ?Q" using Q1 by simp
    have "max 1 (len_formula (translate_formula (rev.translate_formula (Conn c args)))
                  + len_formula (Conn c ?AS) + len_formula (Conn c args)) \<le> 4 * ?Q"
      by (rule max_one_le[OF h1 h])
    hence "?TB * max 1 (len_formula (translate_formula
                           (rev.translate_formula (Conn c args)))
                         + len_formula (Conn c ?AS) + len_formula (Conn c args))
           \<le> ?TB * (4 * ?Q)"
      by (rule mult_le_mono2)
    thus ?thesis .
  qed
  have total: "roundtrip_canon_bound * ?Q
                 + (len_proof two_refl_base * max 1 (Suc ?S)
                      + two_max_arity * two_slot_step_cost ?Q ?S)
                 + ?TB * max 1 (len_formula (translate_formula
                                  (rev.translate_formula (Conn c args)))
                                + len_formula (Conn c ?AS)
                                + len_formula (Conn c args))
               \<le> ?K ^ ?D * ?W"
  proof -
    have "roundtrip_canon_bound * ?Q
            + (len_proof two_refl_base * max 1 (Suc ?S)
                 + two_max_arity * two_slot_step_cost ?Q ?S)
            + ?TB * max 1 (len_formula (translate_formula
                             (rev.translate_formula (Conn c args)))
                           + len_formula (Conn c ?AS) + len_formula (Conn c args))
          \<le> roundtrip_canon_bound * ?Q
            + (len_proof two_refl_base * (2 * ?Q)
                 + two_max_arity * ((1 + 3 * two_slot_bound + 6 * ?TB) * ?Q))
            + ?TB * (4 * ?Q)"
      by (intro add_mono b_le c_le d_le order_refl)
    also have "\<dots> = (roundtrip_canon_bound + 2 * len_proof two_refl_base
                     + two_max_arity * (1 + 3 * two_slot_bound + 6 * ?TB)
                     + 4 * ?TB) * ?Q"
      by (simp add: algebra_simps)
    also have "\<dots> \<le> ?K * ?Q"
    proof (rule mult_le_mono1)
      show "roundtrip_canon_bound + 2 * len_proof two_refl_base
              + two_max_arity * (1 + 3 * two_slot_bound + 6 * ?TB) + 4 * ?TB \<le> ?K"
        unfolding roundtrip_const_def by simp
    qed
    also have "\<dots> = (?K * ?P) * ?W" by (rule mult.assoc[symmetric])
    also have "\<dots> = ?K ^ ?D * ?W" using KD by simp
    finally show ?thesis .
  qed
  show ?case by (rule two_prov_iff_mono[OF tr total])
qed


text \<open>
  \<^const>\<open>roundtrip_weight\<close> sums the size of the roundtrip image over the nodes of the
  formula, so it is bounded by the number of nodes times a uniform bound on those sizes.
  The uniform bound is what the depth-indexed translation bound supplies once the depth is
  fixed --- which is exactly the situation at \<open>spira_trans \<tau>\<close>.
\<close>

lemma roundtrip_weight_bound:
  fixes B :: nat
  assumes big: "\<And>g. formula_well_formed (alphabet Ftwo) g
                    \<Longrightarrow> depth_formula g \<le> depth_formula f \<Longrightarrow> len_formula g \<le> len_formula f
                    \<Longrightarrow> len_formula (translate_formula (rev.translate_formula g)) \<le> B"
      and lenB: "len_formula f \<le> B"
      and wf: "formula_well_formed (alphabet Ftwo) f"
  shows "roundtrip_weight f \<le> 2 * B * len_formula f"
  using assms
proof (induction f)
  case (Atom v)
  have "1 \<le> B" using Atom.prems(2) by simp
  thus ?case by simp
next
  case (Conn c args)
  let ?L = "len_formula (Conn c args)"
  have LB: "?L \<le> B" using Conn.prems(2) .
  have PB: "len_formula (translate_formula (rev.translate_formula (Conn c args))) \<le> B"
    by (rule Conn.prems(1)[OF Conn.prems(3)]) simp_all
  have argwf: "formula_well_formed (alphabet Ftwo) g" if g_in: "g \<in> set args" for g
    using Conn.prems(3) g_in by simp
  have argb: "roundtrip_weight g \<le> 2 * B * len_formula g" if g_in: "g \<in> set args" for g
  proof (rule Conn.IH[OF g_in])
    fix h :: "'c2 formula"
    assume wfh: "formula_well_formed (alphabet Ftwo) h"
       and dh: "depth_formula h \<le> depth_formula g"
       and lh: "len_formula h \<le> len_formula g"
    have "depth_formula h \<le> depth_formula (Conn c args)"
      using dh depth_formula_arg_le[OF g_in] by (rule order_trans)
    moreover have "len_formula h \<le> len_formula (Conn c args)"
      using lh len_formula_arg_le[OF g_in] by (rule order_trans)
    ultimately show "len_formula (translate_formula (rev.translate_formula h)) \<le> B"
      by (rule Conn.prems(1)[OF wfh])
  next
    have "len_formula g \<le> len_formula (Conn c args)"
      by (rule len_formula_arg_le[OF g_in])
    thus "len_formula g \<le> B" using LB by (rule order_trans)
  next
    show "formula_well_formed (alphabet Ftwo) g" by (rule argwf[OF g_in])
  qed
  have sums: "sum_list (map roundtrip_weight args)
              \<le> sum_list (map (\<lambda>g. 2 * B * len_formula g) args)"
    by (rule sum_list_mono) (rule argb)
  have sums2: "sum_list (map (\<lambda>g. 2 * B * len_formula g) args)
              = 2 * B * sum_list (map len_formula args)"
    by (induction args) (simp_all add: algebra_simps)
  have split: "?L = 1 + sum_list (map len_formula args)" by simp
  have "roundtrip_weight (Conn c args)
        = len_formula (translate_formula (rev.translate_formula (Conn c args)))
          + ?L + sum_list (map roundtrip_weight args)"
    by simp
  also have "\<dots> \<le> B + ?L + 2 * B * sum_list (map len_formula args)"
    using PB sums sums2 by simp
  also have "\<dots> \<le> 2 * B * ?L"
  proof -
    have "B + ?L \<le> 2 * B" using LB by simp
    hence "B + ?L + 2 * B * sum_list (map len_formula args)
           \<le> 2 * B + 2 * B * sum_list (map len_formula args)" by simp
    also have "\<dots> = 2 * B * (1 + sum_list (map len_formula args))"
      by (simp add: algebra_simps)
    finally show ?thesis using split by simp
  qed
  finally show ?case .
qed

text \<open>
  The packaging of \<^text>\<open>power_ceiling_log_poly_bound\<close> used throughout the assembly:
  a constant raised to a LOGARITHMIC exponent is polynomial.  Every \<open>const ^ depth\<close> factor
  in the chain is applied to a Spira-balanced formula, which is exactly why each of them
  is absorbed by a polynomial.
\<close>

lemma pow_log_poly:
  fixes T :: nat and c :: real
  assumes T1: "1 \<le> T" and c0: "0 \<le> c"
  shows "\<exists> p :: nat poly. \<forall> n :: nat. T ^ (nat \<lceil>c * log 2 (real n + 1)\<rceil>) \<le> poly p n"
proof -
  obtain q :: "nat poly" where q:
    "\<And>n :: nat. T ^ (nat \<lceil>0 + c * log 2 (real n + 1)\<rceil>)
                  \<le> T ^ (nat \<lceil>0::real\<rceil> + 1) * poly q n"
    using power_ceiling_log_poly_bound[OF T1 _ c0, of 0] by auto
  show ?thesis
  proof (rule exI[where x = "Polynomial.smult T q"], rule allI)
    fix n :: nat
    have "T ^ (nat \<lceil>c * log 2 (real n + 1)\<rceil>) \<le> T ^ (nat \<lceil>0::real\<rceil> + 1) * poly q n"
      using q[of n] by simp
    also have "\<dots> = poly (Polynomial.smult T q) n" by simp
    finally show "T ^ (nat \<lceil>c * log 2 (real n + 1)\<rceil>)
                    \<le> poly (Polynomial.smult T q) n" .
  qed
qed

text \<open>
  The size of the roundtrip image, in terms of a depth bound and a size bound for the
  argument.  Both template translations contribute a factor exponential in the depth, and
  the inner one also multiplies the depth by its own template depth.
\<close>

lemma roundtrip_len_bound:
  assumes wf: "formula_well_formed (alphabet Ftwo) g"
      and dep: "depth_formula g \<le> d"
      and len: "len_formula g \<le> l"
  shows "len_formula (translate_formula (rev.translate_formula g))
           \<le> (template_length_bound ^ rev.template_depth_bound) ^ d
             * (rev.template_length_bound ^ d * l)"
proof -
  have wf1: "formula_well_formed (alphabet Fone) (rev.translate_formula g)"
    by (rule rev.translate_formula_well_formed)
  have d1: "depth_formula (rev.translate_formula g) \<le> d * rev.template_depth_bound"
  proof -
    have "depth_formula (rev.translate_formula g)
            \<le> depth_formula g * rev.template_depth_bound"
      by (rule rev.translate_formula_depth[OF wf])
    also have "\<dots> \<le> d * rev.template_depth_bound"
      using dep by (rule mult_le_mono1)
    finally show ?thesis .
  qed
  have l1: "len_formula (rev.translate_formula g) \<le> rev.template_length_bound ^ d * l"
  proof -
    have "len_formula (rev.translate_formula g)
            \<le> rev.template_length_bound ^ d * len_formula g"
      by (rule rev.translate_formula_length[OF wf dep])
    also have "\<dots> \<le> rev.template_length_bound ^ d * l"
      using len by (rule mult_le_mono2)
    finally show ?thesis .
  qed
  have pw: "template_length_bound ^ (d * rev.template_depth_bound)
              = (template_length_bound ^ rev.template_depth_bound) ^ d"
  proof -
    have "template_length_bound ^ (d * rev.template_depth_bound)
            = template_length_bound ^ (rev.template_depth_bound * d)"
      by (simp add: mult.commute)
    also have "\<dots> = (template_length_bound ^ rev.template_depth_bound) ^ d"
      by (rule power_mult)
    finally show ?thesis .
  qed
  have "len_formula (translate_formula (rev.translate_formula g))
          \<le> template_length_bound ^ (d * rev.template_depth_bound)
            * len_formula (rev.translate_formula g)"
    by (rule translate_formula_length[OF wf1 d1])
  also have "\<dots> \<le> template_length_bound ^ (d * rev.template_depth_bound)
                 * (rev.template_length_bound ^ d * l)"
    using l1 by (rule mult_le_mono2)
  finally show ?thesis using pw by simp
qed

text \<open>
  Step 4 of the chain, made polynomial.  \<^text>\<open>roundtrip_provable\<close> costs
  \<open>roundtrip_const ^ depth \<sigma> * roundtrip_weight \<sigma>\<close>, which is polynomial precisely when \<sigma> is
  BALANCED --- and \<sigma> is always \<^text>\<open>spira_trans \<tau>\<close> here.  The same balancing bounds the
  size of the roundtrip image itself, which the modus-ponens conversion later has to pay
  for.  All three bounds are collected under a single polynomial.
\<close>

lemma roundtrip_spira_poly:
  "\<exists> p :: nat poly. \<forall> \<tau>. formula_well_formed (alphabet Ftwo) \<tau> \<longrightarrow>
       two_prov_iff (translate_formula (rev.translate_formula (two_bal.spira_trans \<tau>)))
         (two_bal.spira_trans \<tau>) (poly p (len_formula \<tau>))
     \<and> len_formula (translate_formula (rev.translate_formula (two_bal.spira_trans \<tau>)))
         \<le> poly p (len_formula \<tau>)
     \<and> len_formula (two_bal.spira_trans \<tau>) \<le> poly p (len_formula \<tau>)"
proof -
  obtain szp :: "nat poly" where szp:
    "\<And>f. formula_well_formed (alphabet Ftwo) f
         \<Longrightarrow> len_formula (two_bal.spira_trans f) \<le> poly szp (len_formula f)"
    using two_bal.trans_b by blast
  obtain cs0 :: real where cs0:
    "\<And>f. formula_well_formed (alphabet Ftwo) f
         \<Longrightarrow> real (depth_formula (two_bal.spira_trans f))
             \<le> cs0 * log 2 (real (len_formula f) + 1)"
    using two_bal.trans_c by blast
  define cs :: real where "cs = max cs0 0"
  have cs_nn: "0 \<le> cs" unfolding cs_def by simp
  have cs_bound: "real (depth_formula (two_bal.spira_trans f))
                    \<le> cs * log 2 (real (len_formula f) + 1)"
    if wff: "formula_well_formed (alphabet Ftwo) f" for f
  proof -
    have "0 \<le> log 2 (real (len_formula f) + 1)" by simp
    hence "cs0 * log 2 (real (len_formula f) + 1)
             \<le> cs * log 2 (real (len_formula f) + 1)"
      unfolding cs_def by (intro mult_right_mono) simp_all
    thus ?thesis using cs0[OF wff] by linarith
  qed
  define DD :: "nat \<Rightarrow> nat" where "DD n = nat \<lceil>cs * log 2 (real n + 1)\<rceil>" for n
  have dep_le: "depth_formula (two_bal.spira_trans f) \<le> DD (len_formula f)"
    if wff: "formula_well_formed (alphabet Ftwo) f" for f
    unfolding DD_def by (rule nat_le_nat_ceiling) (rule cs_bound[OF wff])
  \<comment> \<open>the three constants raised to the logarithmic depth\<close>
  define KK where "KK = roundtrip_const"
  define AA where "AA = template_length_bound ^ rev.template_depth_bound"
  define RR where "RR = rev.template_length_bound"
  have KK1: "1 \<le> KK" unfolding KK_def by (rule roundtrip_const_ge_1)
  have AA1: "1 \<le> AA" unfolding AA_def
    using template_length_bound_positive by (rule one_le_power)
  have RR1: "1 \<le> RR" unfolding RR_def by (rule rev.template_length_bound_positive)
  obtain pK :: "nat poly" where pK: "\<And>n. KK ^ DD n \<le> poly pK n"
    using pow_log_poly[OF KK1 cs_nn] unfolding DD_def by blast
  obtain pA :: "nat poly" where pA: "\<And>n. AA ^ DD n \<le> poly pA n"
    using pow_log_poly[OF AA1 cs_nn] unfolding DD_def by blast
  obtain pR :: "nat poly" where pR: "\<And>n. RR ^ DD n \<le> poly pR n"
    using pow_log_poly[OF RR1 cs_nn] unfolding DD_def by blast
  have pA1: "1 \<le> poly pA n" for n
    using AA1 pA[of n] by (meson one_le_power order_trans)
  have pR1: "1 \<le> poly pR n" for n
    using RR1 pR[of n] by (meson one_le_power order_trans)
  define PB :: "nat poly" where "PB = pA * pR * szp"
  have polyPB: "poly PB n = poly pA n * (poly pR n * poly szp n)" for n
    unfolding PB_def by (simp add: mult.assoc)
  define p :: "nat poly" where
    "p = pK * (Polynomial.smult 2 PB * szp) + PB + szp"
  have polyp: "poly p n = poly pK n * (2 * poly PB n * poly szp n)
                          + poly PB n + poly szp n" for n
    unfolding p_def by simp
  show ?thesis
  proof (rule exI[where x = p], intro allI impI)
    fix \<tau> :: "'c2 formula"
    assume wf: "formula_well_formed (alphabet Ftwo) \<tau>"
    define L where "L = len_formula \<tau>"
    define s where "s = two_bal.spira_trans \<tau>"
    have s_wf: "formula_well_formed (alphabet Ftwo) s"
      unfolding s_def by (rule two_bal.spira_trans_wf[OF wf])
    have s_len: "len_formula s \<le> poly szp L"
      unfolding s_def L_def by (rule szp[OF wf])
    have s_dep: "depth_formula s \<le> DD L"
      unfolding s_def L_def by (rule dep_le[OF wf])
    \<comment> \<open>the uniform bound on the roundtrip image of every subformula of s\<close>
    have uniform: "len_formula (translate_formula (rev.translate_formula g)) \<le> poly PB L"
      if g_wf: "formula_well_formed (alphabet Ftwo) g"
         and g_dep: "depth_formula g \<le> depth_formula s"
         and g_len: "len_formula g \<le> len_formula s" for g
    proof -
      have d': "depth_formula g \<le> DD L" using g_dep s_dep by (rule order_trans)
      have l': "len_formula g \<le> poly szp L" using g_len s_len by (rule order_trans)
      have "len_formula (translate_formula (rev.translate_formula g))
              \<le> AA ^ DD L * (RR ^ DD L * poly szp L)"
        unfolding AA_def RR_def by (rule roundtrip_len_bound[OF g_wf d' l'])
      also have "\<dots> \<le> poly pA L * (poly pR L * poly szp L)"
        using pA[of L] pR[of L] by (intro mult_le_mono) simp_all
      finally show ?thesis using polyPB by simp
    qed
    have szp_le_PB: "poly szp L \<le> poly PB L"
    proof -
      have "poly szp L = 1 * (1 * poly szp L)" by simp
      also have "\<dots> \<le> poly pA L * (poly pR L * poly szp L)"
        by (rule mult_le_mono[OF pA1 mult_le_mono[OF pR1 order_refl]])
      also have "\<dots> = poly PB L" using polyPB by simp
      finally show ?thesis .
    qed
    have s_lenPB: "len_formula s \<le> poly PB L"
      using s_len szp_le_PB by (rule order_trans)
    have weight: "roundtrip_weight s \<le> 2 * poly PB L * len_formula s"
      by (rule roundtrip_weight_bound[OF uniform s_lenPB s_wf])
    have prov: "two_prov_iff (translate_formula (rev.translate_formula s)) s
                  (roundtrip_const ^ depth_formula s * roundtrip_weight s)"
      by (rule roundtrip_provable[OF s_wf])
    have cost: "roundtrip_const ^ depth_formula s * roundtrip_weight s
                  \<le> poly pK L * (2 * poly PB L * poly szp L)"
    proof (rule mult_le_mono)
      have "roundtrip_const ^ depth_formula s \<le> KK ^ DD L"
        unfolding KK_def using s_dep KK1[unfolded KK_def] by (rule power_increasing)
      thus "roundtrip_const ^ depth_formula s \<le> poly pK L" using pK[of L] by simp
    next
      have "roundtrip_weight s \<le> 2 * poly PB L * len_formula s" by (rule weight)
      also have "\<dots> \<le> 2 * poly PB L * poly szp L"
        using s_len by (rule mult_le_mono2)
      finally show "roundtrip_weight s \<le> 2 * poly PB L * poly szp L" .
    qed
    have c1: "two_prov_iff (translate_formula (rev.translate_formula s)) s (poly p L)"
    proof (rule two_prov_iff_mono[OF prov])
      show "roundtrip_const ^ depth_formula s * roundtrip_weight s \<le> poly p L"
        using cost polyp by simp
    qed
    have c2: "len_formula (translate_formula (rev.translate_formula s)) \<le> poly p L"
    proof -
      have "len_formula (translate_formula (rev.translate_formula s)) \<le> poly PB L"
        by (rule uniform[OF s_wf order_refl order_refl])
      thus ?thesis using polyp by simp
    qed
    have c3: "len_formula s \<le> poly p L"
      using s_len polyp by simp
    show "two_prov_iff (translate_formula (rev.translate_formula (two_bal.spira_trans \<tau>)))
            (two_bal.spira_trans \<tau>) (poly p (len_formula \<tau>))
          \<and> len_formula (translate_formula
                (rev.translate_formula (two_bal.spira_trans \<tau>)))
              \<le> poly p (len_formula \<tau>)
          \<and> len_formula (two_bal.spira_trans \<tau>) \<le> poly p (len_formula \<tau>)"
      using c1 c2 c3 unfolding s_def L_def by blast
  qed
qed


subsection \<open>Undoing the balancing inside Ftwo\<close>

text \<open>
  The last leg of the chain: an Ftwo-proof of \<open>spira_trans \<tau> \<longleftrightarrow> \<tau>\<close>.  It is
  \<^text>\<open>two_bal.transform_commutes_form\<close> instantiated at the IDENTITY substitution
  \<^const>\<open>Atom\<close>: both sides of the commutation then collapse, the left one to
  \<^text>\<open>spira_trans \<tau>\<close> and the right one to \<open>\<tau>\<close> itself, because \<open>spira_trans\<close> fixes
  atoms.

  This is available for an ARBITRARY Ftwo only because \<^text>\<open>frege_closure\<close> carries no
  closure assumption.  It is what keeps the last leg INSIDE Ftwo: every route that leaves
  Ftwo pays a factor exponential in the depth of \<open>\<tau>\<close>, which is unbounded.
\<close>

lemma two_prov_iff_of_balanced:
  assumes "two_bal.provable_balanced_iff A B lines sz dep"
  shows "two_prov_iff A B (lines * sz)"
proof -
  obtain q where q_valid: "valid_proof Ftwo q"
      and q_asm: "assumptions q = {}"
      and q_th: "frege_proof.thesis q = two_bal.iff_form A B"
      and q_lines: "length (steps q) \<le> lines"
      and q_sz: "\<forall> s \<in> set (steps q). len_formula s \<le> sz"
      and q_wf: "\<forall> s \<in> set (steps q). formula_well_formed (alphabet Ftwo) s"
    using assms unfolding two_bal.provable_balanced_iff_def by blast
  have "len_proof q = sum_list (map len_formula (steps q))" by simp
  also have "\<dots> \<le> length (steps q) * sz"
    using q_sz by (rule two_bal.sum_list_map_le)
  also have "\<dots> \<le> lines * sz"
    using q_lines by (rule mult_le_mono1)
  finally have q_len: "len_proof q \<le> lines * sz" .
  show ?thesis
    unfolding two_prov_iff_def
    using q_valid q_asm q_th q_len q_wf by blast
qed

lemma spira_trans_two_atom: "two_bal.spira_trans (Atom v) = Atom v"
proof -
  have dom: "two_bal.spira_trans_dom (Atom v)"
    by (rule two_bal.spira_trans.domintros)
  thus ?thesis by (simp add: two_bal.spira_trans.psimps(1))
qed

lemma two_spira_iff:
  "\<exists> p :: nat poly. \<forall> \<tau>. formula_well_formed (alphabet Ftwo) \<tau>
        \<longrightarrow> two_prov_iff (two_bal.spira_trans \<tau>) \<tau> (poly p (len_formula \<tau>))"
proof -
  obtain bnd :: "nat poly" and cdep :: real where TC:
    "\<forall> f sub. formula_well_formed (alphabet Ftwo) f
              \<and> (\<forall> f' \<in> range sub. formula_well_formed (alphabet Ftwo) f') \<longrightarrow>
       (let M = len_formula f + (\<Sum> v \<in> var_set_form f. len_formula (sub v))
        in (\<exists> lines sz dep.
              two_bal.provable_balanced_iff (two_bal.spira_trans (sub_formula sub f))
                (sub_formula (\<lambda> v. two_bal.spira_trans (sub v)) f) lines sz dep
            \<and> lines \<le> poly bnd M
            \<and> sz \<le> poly bnd M
            \<and> real dep \<le> real (depth_formula f) + cdep * log 2 (real M + 1)))"
    using two_bal.transform_commutes_form by blast
  define p :: "nat poly" where "p = (pcompose bnd (monom 2 1))\<^sup>2"
  have poly_p: "poly p n = poly bnd (2 * n) * poly bnd (2 * n)" for n
    unfolding p_def by (simp add: poly_pcompose poly_monom power2_eq_square)
  show ?thesis
  proof (rule exI[where x = p], intro allI impI)
    fix \<tau> :: "'c2 formula"
    assume wf: "formula_well_formed (alphabet Ftwo) \<tau>"
    let ?M = "len_formula \<tau> + (\<Sum> v \<in> var_set_form \<tau>. len_formula (Atom v :: 'c2 formula))"
    have rng: "\<forall> f' \<in> range (Atom :: string \<Rightarrow> 'c2 formula).
                 formula_well_formed (alphabet Ftwo) f'" by auto
    note TCi = TC[THEN spec, THEN spec, of \<tau> "Atom :: string \<Rightarrow> 'c2 formula"]
    note inst = mp[OF TCi conjI[OF wf rng], unfolded Let_def]
    from inst obtain lines sz dep where
        PBI: "two_bal.provable_balanced_iff
                (two_bal.spira_trans (sub_formula Atom \<tau>))
                (sub_formula (\<lambda> v. two_bal.spira_trans (Atom v)) \<tau>) lines sz dep"
      and Lb: "lines \<le> poly bnd ?M"
      and Sb: "sz \<le> poly bnd ?M"
      by blast
    have lhs: "sub_formula Atom \<tau> = \<tau>" by (rule sub_formula_atom_id)
    have rhs_fun: "(\<lambda> v. two_bal.spira_trans (Atom v)) = (Atom :: string \<Rightarrow> 'c2 formula)"
      by (rule ext) (rule spira_trans_two_atom)
    have rhs: "sub_formula (\<lambda> v. two_bal.spira_trans (Atom v)) \<tau> = \<tau>"
      unfolding rhs_fun by (rule sub_formula_atom_id)
    have PBI': "two_bal.provable_balanced_iff (two_bal.spira_trans \<tau>) \<tau> lines sz dep"
      using PBI lhs rhs by simp
    \<comment> \<open>the identity substitution contributes one symbol per variable\<close>
    have M_le: "?M \<le> 2 * len_formula \<tau>"
    proof -
      have "(\<Sum> v \<in> var_set_form \<tau>. len_formula (Atom v :: 'c2 formula))
              = card (var_set_form \<tau>)" by simp
      thus ?thesis using card_var_set_form_le_len[of \<tau>] by simp
    qed
    have lines_le: "lines \<le> poly bnd (2 * len_formula \<tau>)"
      by (rule order_trans[OF Lb poly_nat_mono[OF M_le]])
    have sz_le: "sz \<le> poly bnd (2 * len_formula \<tau>)"
      by (rule order_trans[OF Sb poly_nat_mono[OF M_le]])
    have prod_le: "lines * sz \<le> poly p (len_formula \<tau>)"
      using mult_le_mono[OF lines_le sz_le] poly_p by simp
    have base: "two_prov_iff (two_bal.spira_trans \<tau>) \<tau> (lines * sz)"
      by (rule two_prov_iff_of_balanced[OF PBI'])
    show "two_prov_iff (two_bal.spira_trans \<tau>) \<tau> (poly p (len_formula \<tau>))"
      by (rule two_prov_iff_mono[OF base prod_le])
  qed
qed

subsection \<open>Chaining the two Ftwo-internal equivalences\<close>

text \<open>
  Steps 4 and 5 composed: the roundtrip image of the balanced formula is Ftwo-provably
  equivalent to \<open>\<tau>\<close> itself.  Transitivity costs one more constant-size base proof
  instantiated at the three formulas involved, all of which are polynomially bounded.
\<close>

lemma phi_spira_iff_tau:
  "\<exists> p :: nat poly. \<forall> \<tau>. formula_well_formed (alphabet Ftwo) \<tau> \<longrightarrow>
       two_prov_iff (translate_formula (rev.translate_formula (two_bal.spira_trans \<tau>)))
         \<tau> (poly p (len_formula \<tau>))
     \<and> len_formula (translate_formula (rev.translate_formula (two_bal.spira_trans \<tau>)))
         \<le> poly p (len_formula \<tau>)"
proof -
  obtain p4 :: "nat poly" where P4:
    "\<And>\<tau>. formula_well_formed (alphabet Ftwo) \<tau> \<Longrightarrow>
       two_prov_iff (translate_formula (rev.translate_formula (two_bal.spira_trans \<tau>)))
         (two_bal.spira_trans \<tau>) (poly p4 (len_formula \<tau>))
     \<and> len_formula (translate_formula (rev.translate_formula (two_bal.spira_trans \<tau>)))
         \<le> poly p4 (len_formula \<tau>)
     \<and> len_formula (two_bal.spira_trans \<tau>) \<le> poly p4 (len_formula \<tau>)"
    using roundtrip_spira_poly by blast
  obtain p5 :: "nat poly" where P5:
    "\<And>\<tau>. formula_well_formed (alphabet Ftwo) \<tau> \<Longrightarrow>
       two_prov_iff (two_bal.spira_trans \<tau>) \<tau> (poly p5 (len_formula \<tau>))"
    using two_spira_iff by blast
  define TB where "TB = len_proof two_bal.trans_base_proof"
  define p :: "nat poly" where
    "p = p4 + p5 + Polynomial.smult TB (1 + Polynomial.smult 2 p4 + monom 1 1)"
  have polyp: "poly p n = poly p4 n + poly p5 n + TB * (1 + 2 * poly p4 n + n)" for n
    unfolding p_def by (simp add: poly_monom)
  show ?thesis
  proof (rule exI[where x = p], intro allI impI)
    fix \<tau> :: "'c2 formula"
    assume wf: "formula_well_formed (alphabet Ftwo) \<tau>"
    define L where "L = len_formula \<tau>"
    define A where "A = translate_formula (rev.translate_formula (two_bal.spira_trans \<tau>))"
    define B where "B = two_bal.spira_trans \<tau>"
    have wfA: "formula_well_formed (alphabet Ftwo) A"
      unfolding A_def by (rule translate_formula_well_formed)
    have wfB: "formula_well_formed (alphabet Ftwo) B"
      unfolding B_def by (rule two_bal.spira_trans_wf[OF wf])
    have ab: "two_prov_iff A B (poly p4 L)"
      unfolding A_def B_def L_def using P4[OF wf] by blast
    have bc: "two_prov_iff B \<tau> (poly p5 L)"
      unfolding B_def L_def by (rule P5[OF wf])
    have lenA: "len_formula A \<le> poly p4 L"
      unfolding A_def L_def using P4[OF wf] by blast
    have lenB: "len_formula B \<le> poly p4 L"
      unfolding B_def L_def using P4[OF wf] by blast
    have chain: "two_prov_iff A \<tau>
                   (poly p4 L + poly p5 L
                      + TB * max 1 (len_formula A + len_formula B + len_formula \<tau>))"
      unfolding TB_def by (rule two_prov_iff_trans[OF ab bc wfA wfB wf])
    have costle: "poly p4 L + poly p5 L
                    + TB * max 1 (len_formula A + len_formula B + len_formula \<tau>)
                  \<le> poly p L"
    proof -
      have "len_formula A + len_formula B + len_formula \<tau> \<le> poly p4 L + poly p4 L + L"
        unfolding L_def using lenA lenB by (simp add: L_def add_mono)
      hence "max 1 (len_formula A + len_formula B + len_formula \<tau>)
               \<le> 1 + 2 * poly p4 L + L" by simp
      hence "TB * max 1 (len_formula A + len_formula B + len_formula \<tau>)
               \<le> TB * (1 + 2 * poly p4 L + L)" by (rule mult_le_mono2)
      thus ?thesis using polyp by simp
    qed
    have c1: "two_prov_iff A \<tau> (poly p L)"
      by (rule two_prov_iff_mono[OF chain costle])
    have c2: "len_formula A \<le> poly p L"
      using lenA polyp by simp
    show "two_prov_iff (translate_formula
              (rev.translate_formula (two_bal.spira_trans \<tau>))) \<tau> (poly p (len_formula \<tau>))
          \<and> len_formula (translate_formula
              (rev.translate_formula (two_bal.spira_trans \<tau>)))
              \<le> poly p (len_formula \<tau>)"
      using c1 c2 unfolding A_def L_def by blast
  qed
qed

subsection \<open>Balancing the Fone-proof and translating it into Ftwo\<close>

lemma log2_mono_nat:
  fixes m n :: nat
  assumes "m \<le> n"
  shows "log 2 (real m + 1) \<le> log 2 (real n + 1)"
proof -
  have "real m + 1 \<le> real n + 1" using assms by simp
  thus ?thesis using log_le_cancel_iff[of 2 "real m + 1" "real n + 1"] by simp
qed

text \<open>
  Steps 1--3.  Because \<^text>\<open>frege_closure\<close> is assumption-free, Fone can be balanced
  where it stands --- no closed extension of Fone and no renaming back.  The point of
  balancing is the DEPTH bound it produces: the template translation into Ftwo costs
  \<open>T ^ D\<close> with \<open>D\<close> the largest line depth, and \<^text>\<open>one_bal.proof_balancing\<close> makes \<open>D\<close>
  logarithmic in the proof size plus the depth of the thesis.  The thesis here is
  \<^const>\<open>reverse_translate\<close> of \<tau>, i.e. a template translation of the BALANCED
  \<^text>\<open>spira_trans \<tau>\<close>, so its own depth is logarithmic in \<open>len_formula \<tau>\<close> as well.
  Both logarithms are therefore in \<open>len_proof w + len_formula \<tau>\<close>, and \<open>T ^ D\<close> is polynomial
  in it --- which is exactly the bound clause (B) of \<^const>\<open>simulates\<close> allows.
\<close>

lemma translated_balanced_proof:
  "\<exists> q :: nat poly. \<forall> w \<tau>.
      (formula_well_formed (alphabet Ftwo) \<tau>
       \<and> frege_proof.thesis w = reverse_translate \<tau>
       \<and> valid_proof Fone w \<and> assumptions w = {}
       \<and> (\<forall> s \<in> set (steps w). formula_well_formed (alphabet Fone) s))
      \<longrightarrow> (\<exists> pr2. valid_proof Ftwo pr2 \<and> assumptions pr2 = {}
            \<and> frege_proof.thesis pr2
                = translate_formula (rev.translate_formula (two_bal.spira_trans \<tau>))
            \<and> len_proof pr2 \<le> poly q (len_proof w + len_formula \<tau>))"
proof -
  obtain cs0 :: real where cs0:
    "\<And>f. formula_well_formed (alphabet Ftwo) f
         \<Longrightarrow> real (depth_formula (two_bal.spira_trans f))
             \<le> cs0 * log 2 (real (len_formula f) + 1)"
    using two_bal.trans_c by blast
  define cs :: real where "cs = max cs0 0"
  have cs_nn: "0 \<le> cs" unfolding cs_def by simp
  have cs_bound: "real (depth_formula (two_bal.spira_trans f))
                    \<le> cs * log 2 (real (len_formula f) + 1)"
    if wff: "formula_well_formed (alphabet Ftwo) f" for f
  proof -
    have "0 \<le> log 2 (real (len_formula f) + 1)" by simp
    hence "cs0 * log 2 (real (len_formula f) + 1)
             \<le> cs * log 2 (real (len_formula f) + 1)"
      unfolding cs_def by (intro mult_right_mono) simp_all
    thus ?thesis using cs0[OF wff] by linarith
  qed
  obtain Bbal :: "nat poly" and cbal0 :: real where PBAL:
    "\<forall> pr. valid_proof Fone pr \<and> assumptions pr = {}
           \<and> (\<forall> s \<in> set (steps pr). formula_well_formed (alphabet Fone) s) \<longrightarrow>
        (\<exists> pr'. valid_proof Fone pr' \<and> assumptions pr' = {}
              \<and> frege_proof.thesis pr' = frege_proof.thesis pr
              \<and> len_proof pr' \<le> poly Bbal (len_proof pr)
              \<and> (\<forall> line \<in> set (steps pr').
                   real (depth_formula line)
                   \<le> real (depth_formula (frege_proof.thesis pr))
                     + cbal0 * log 2 (real (len_proof pr) + 1))
              \<and> (\<forall> line \<in> set (steps pr'). formula_well_formed (alphabet Fone) line))"
    using one_bal.proof_balancing by blast
  obtain szb :: "nat poly" and T :: nat where T1: "1 \<le> T" and TSIM:
    "\<forall> pr D. valid_proof Fone pr \<and> assumptions pr = {}
         \<and> (\<forall> st \<in> set (steps pr). formula_well_formed (alphabet Fone) st)
         \<and> (\<forall> st \<in> set (steps pr). depth_formula st \<le> D)
       \<longrightarrow> (\<exists> pr2. valid_proof Ftwo pr2
             \<and> assumptions pr2 = {}
             \<and> frege_proof.thesis pr2 = translate_formula (frege_proof.thesis pr)
             \<and> len_proof pr2 \<le> T ^ D * poly szb (len_proof pr))"
    using translated_proof_simulation by blast
  define RTD where "RTD = rev.template_depth_bound"
  define cb :: real where "cb = max cbal0 0"
  have cb_nn: "0 \<le> cb" unfolding cb_def by simp
  define cc :: real where "cc = real RTD * cs + cb"
  have cc_nn: "0 \<le> cc"
    unfolding cc_def using cs_nn cb_nn by simp
  obtain dpp :: "nat poly" where DPP:
    "\<And>n :: nat. T ^ (nat \<lceil>cc * log 2 (real n + 1)\<rceil>) \<le> poly dpp n"
    using pow_log_poly[OF T1 cc_nn] by blast
  define q :: "nat poly" where "q = dpp * pcompose szb Bbal"
  have polyq: "poly q n = poly dpp n * poly szb (poly Bbal n)" for n
    unfolding q_def by (simp add: poly_pcompose)
  show ?thesis
  proof (rule exI[where x = q], intro allI impI)
    fix w :: "'c1 frege_proof" and \<tau> :: "'c2 formula"
    assume H: "formula_well_formed (alphabet Ftwo) \<tau>
       \<and> frege_proof.thesis w = reverse_translate \<tau>
       \<and> valid_proof Fone w \<and> assumptions w = {}
       \<and> (\<forall> s \<in> set (steps w). formula_well_formed (alphabet Fone) s)"
    have wf: "formula_well_formed (alphabet Ftwo) \<tau>" using H by blast
    have thw: "frege_proof.thesis w = reverse_translate \<tau>" using H by blast
    have vw: "valid_proof Fone w" using H by blast
    have aw: "assumptions w = {}" using H by blast
    have wfw: "\<forall> s \<in> set (steps w). formula_well_formed (alphabet Fone) s" using H by blast
    define S where "S = len_proof w"
    define L where "L = len_formula \<tau>"
    define N where "N = S + L"
    define s where "s = two_bal.spira_trans \<tau>"
    have s_wf: "formula_well_formed (alphabet Ftwo) s"
      unfolding s_def by (rule two_bal.spira_trans_wf[OF wf])
    have thw': "frege_proof.thesis w = rev.translate_formula s"
      using thw unfolding reverse_translate_def s_def by simp
    have logN_nn: "0 \<le> log 2 (real N + 1)" by simp
    \<comment> \<open>the thesis of w is a template translation of a BALANCED formula\<close>
    have dep_thw: "real (depth_formula (frege_proof.thesis w))
                     \<le> (real RTD * cs) * log 2 (real N + 1)"
    proof -
      have h0: "depth_formula (frege_proof.thesis w) \<le> depth_formula s * RTD"
        unfolding thw' RTD_def by (rule rev.translate_formula_depth[OF s_wf])
      have h1: "real (depth_formula (frege_proof.thesis w))
                   \<le> real (depth_formula s) * real RTD"
        using of_nat_mono[OF h0] by simp
      have h2: "real (depth_formula s) \<le> cs * log 2 (real L + 1)"
        unfolding s_def L_def by (rule cs_bound[OF wf])
      have h3: "real (depth_formula s) * real RTD
                  \<le> (cs * log 2 (real L + 1)) * real RTD"
        using h2 by (intro mult_right_mono) simp_all
      have h4: "log 2 (real L + 1) \<le> log 2 (real N + 1)"
        unfolding N_def by (rule log2_mono_nat) simp
      have h5: "cs * log 2 (real L + 1) \<le> cs * log 2 (real N + 1)"
        using h4 cs_nn by (rule mult_left_mono)
      have h6: "(cs * log 2 (real L + 1)) * real RTD
                  \<le> (cs * log 2 (real N + 1)) * real RTD"
        using h5 by (intro mult_right_mono) simp_all
      have "real (depth_formula (frege_proof.thesis w))
              \<le> real (depth_formula s) * real RTD" by (rule h1)
      also have "\<dots> \<le> (cs * log 2 (real L + 1)) * real RTD" by (rule h3)
      also have "\<dots> \<le> (cs * log 2 (real N + 1)) * real RTD" by (rule h6)
      also have "\<dots> = (real RTD * cs) * log 2 (real N + 1)"
        by (simp add: algebra_simps)
      finally show ?thesis .
    qed
    \<comment> \<open>balance w inside Fone\<close>
    obtain w' where w'_valid: "valid_proof Fone w'"
        and w'_asm: "assumptions w' = {}"
        and w'_th: "frege_proof.thesis w' = frege_proof.thesis w"
        and w'_len: "len_proof w' \<le> poly Bbal S"
        and w'_dep: "\<forall> line \<in> set (steps w').
                       real (depth_formula line)
                       \<le> real (depth_formula (frege_proof.thesis w))
                         + cbal0 * log 2 (real S + 1)"
        and w'_wf: "\<forall> line \<in> set (steps w'). formula_well_formed (alphabet Fone) line"
      using PBAL vw aw wfw unfolding S_def by blast
    define D where "D = nat \<lceil>cc * log 2 (real N + 1)\<rceil>"
    have dep_D: "\<forall> line \<in> set (steps w'). depth_formula line \<le> D"
    proof
      fix line assume lin: "line \<in> set (steps w')"
      have g1: "real (depth_formula line)
                  \<le> real (depth_formula (frege_proof.thesis w))
                    + cbal0 * log 2 (real S + 1)"
        using w'_dep lin by blast
      have g2: "cbal0 * log 2 (real S + 1) \<le> cb * log 2 (real S + 1)"
        unfolding cb_def by (intro mult_right_mono) simp_all
      have g3: "cb * log 2 (real S + 1) \<le> cb * log 2 (real N + 1)"
      proof (rule mult_left_mono[OF _ cb_nn])
        show "log 2 (real S + 1) \<le> log 2 (real N + 1)"
          unfolding N_def by (rule log2_mono_nat) simp
      qed
      have "real (depth_formula line) \<le> cc * log 2 (real N + 1)"
        using g1 g2 g3 dep_thw unfolding cc_def by (simp add: algebra_simps)
      thus "depth_formula line \<le> D"
        unfolding D_def by (rule nat_le_nat_ceiling)
    qed
    \<comment> \<open>translate the balanced proof into Ftwo\<close>
    obtain pr2 where pr2_valid: "valid_proof Ftwo pr2"
        and pr2_asm: "assumptions pr2 = {}"
        and pr2_th: "frege_proof.thesis pr2 = translate_formula (frege_proof.thesis w')"
        and pr2_len: "len_proof pr2 \<le> T ^ D * poly szb (len_proof w')"
      using TSIM w'_valid w'_asm w'_wf dep_D by blast
    have pr2_th': "frege_proof.thesis pr2 = translate_formula (rev.translate_formula s)"
      using pr2_th w'_th thw' by simp
    have bound: "len_proof pr2 \<le> poly q N"
    proof -
      have b1: "T ^ D \<le> poly dpp N" unfolding D_def by (rule DPP)
      have b2: "poly szb (len_proof w') \<le> poly szb (poly Bbal N)"
      proof (rule poly_nat_mono)
        have bs: "poly Bbal S \<le> poly Bbal N"
          using poly_nat_mono[of S N Bbal] unfolding N_def by simp
        show "len_proof w' \<le> poly Bbal N" by (rule order_trans[OF w'_len bs])
      qed
      have "len_proof pr2 \<le> T ^ D * poly szb (len_proof w')" by (rule pr2_len)
      also have "\<dots> \<le> poly dpp N * poly szb (poly Bbal N)"
        using b1 b2 by (rule mult_le_mono)
      finally show ?thesis using polyq by simp
    qed
    show "\<exists> pr2. valid_proof Ftwo pr2 \<and> assumptions pr2 = {}
            \<and> frege_proof.thesis pr2
                = translate_formula (rev.translate_formula (two_bal.spira_trans \<tau>))
            \<and> len_proof pr2 \<le> poly q (len_proof w + len_formula \<tau>)"
      using pr2_valid pr2_asm pr2_th' bound unfolding s_def N_def S_def L_def by blast
  qed
qed

subsection \<open>Clause (B) of the simulation predicate\<close>

text \<open>
  The whole chain.  From an Fone-proof of \<open>g \<tau>\<close> we obtain an Ftwo-proof of the roundtrip
  image of the balanced formula (steps 1--3), an Ftwo-proof that this image is equivalent
  to \<open>\<tau>\<close> (steps 4--5), and one constant-size modus ponens conversion joins them into an
  Ftwo-proof of \<open>\<tau>\<close> itself.
\<close>

lemma simulation_exists:
  "\<exists> q :: nat poly. \<forall> w \<tau>.
      (formula_well_formed (alphabet Ftwo) \<tau>
       \<and> frege_proof.thesis w = reverse_translate \<tau>
       \<and> valid_proof Fone w \<and> assumptions w = {}
       \<and> (\<forall> s \<in> set (steps w). formula_well_formed (alphabet Fone) s))
      \<longrightarrow> (\<exists> pr. valid_proof Ftwo pr \<and> frege_proof.thesis pr = \<tau>
            \<and> assumptions pr = {}
            \<and> len_proof pr \<le> poly q (len_proof w + len_formula \<tau>))"
proof -
  obtain q1 :: "nat poly" where Q1:
    "\<forall> w \<tau>.
      (formula_well_formed (alphabet Ftwo) \<tau>
       \<and> frege_proof.thesis w = reverse_translate \<tau>
       \<and> valid_proof Fone w \<and> assumptions w = {}
       \<and> (\<forall> s \<in> set (steps w). formula_well_formed (alphabet Fone) s))
      \<longrightarrow> (\<exists> pr2. valid_proof Ftwo pr2 \<and> assumptions pr2 = {}
            \<and> frege_proof.thesis pr2
                = translate_formula (rev.translate_formula (two_bal.spira_trans \<tau>))
            \<and> len_proof pr2 \<le> poly q1 (len_proof w + len_formula \<tau>))"
    using translated_balanced_proof by blast
  obtain q2 :: "nat poly" where Q2:
    "\<And>\<tau>. formula_well_formed (alphabet Ftwo) \<tau> \<Longrightarrow>
       two_prov_iff (translate_formula (rev.translate_formula (two_bal.spira_trans \<tau>)))
         \<tau> (poly q2 (len_formula \<tau>))
     \<and> len_formula (translate_formula (rev.translate_formula (two_bal.spira_trans \<tau>)))
         \<le> poly q2 (len_formula \<tau>)"
    using phi_spira_iff_tau by blast
  define MP where "MP = len_proof two_mp_base"
  define q :: "nat poly" where
    "q = q1 + q2 + Polynomial.smult MP (1 + q2 + monom 1 1)"
  have polyq: "poly q n = poly q1 n + poly q2 n + MP * (1 + poly q2 n + n)" for n
    unfolding q_def by (simp add: poly_monom)
  show ?thesis
  proof (rule exI[where x = q], intro allI impI)
    fix w :: "'c1 frege_proof" and \<tau> :: "'c2 formula"
    assume H: "formula_well_formed (alphabet Ftwo) \<tau>
       \<and> frege_proof.thesis w = reverse_translate \<tau>
       \<and> valid_proof Fone w \<and> assumptions w = {}
       \<and> (\<forall> s \<in> set (steps w). formula_well_formed (alphabet Fone) s)"
    have wf: "formula_well_formed (alphabet Ftwo) \<tau>" using H by blast
    define N where "N = len_proof w + len_formula \<tau>"
    define L where "L = len_formula \<tau>"
    define A where "A = translate_formula (rev.translate_formula (two_bal.spira_trans \<tau>))"
    have LN: "L \<le> N" unfolding L_def N_def by simp
    note Q1i = Q1[THEN spec, THEN spec, of \<tau> w]
    obtain pr2 where pr2_valid: "valid_proof Ftwo pr2"
        and pr2_asm: "assumptions pr2 = {}"
        and pr2_th: "frege_proof.thesis pr2 = A"
        and pr2_len: "len_proof pr2 \<le> poly q1 N"
      using mp[OF Q1i H] unfolding A_def N_def by blast
    have iff_prov: "two_prov_iff A \<tau> (poly q2 L)"
      unfolding A_def L_def using Q2[OF wf] by blast
    have lenA: "len_formula A \<le> poly q2 L"
      unfolding A_def L_def using Q2[OF wf] by blast
    obtain pii where pii_valid: "valid_proof Ftwo pii"
        and pii_asm: "assumptions pii = {}"
        and pii_th: "frege_proof.thesis pii = two_bal.iff_form A \<tau>"
        and pii_len: "len_proof pii \<le> poly q2 L"
      using iff_prov unfolding two_prov_iff_def by blast
    obtain pr where pr_valid: "valid_proof Ftwo pr"
        and pr_asm: "assumptions pr = {}"
        and pr_th: "frege_proof.thesis pr = \<tau>"
        and pr_len: "len_proof pr \<le> len_proof pr2 + len_proof pii
                       + MP * max 1 (len_formula A + len_formula \<tau>)"
      using two_iff_elimination[OF pr2_valid pr2_asm pr2_th pii_valid pii_asm pii_th]
      unfolding MP_def by blast
    have bound: "len_proof pr \<le> poly q N"
    proof -
      have t1: "len_proof pr2 \<le> poly q1 N" by (rule pr2_len)
      have t2: "len_proof pii \<le> poly q2 N"
        by (rule order_trans[OF pii_len poly_nat_mono[OF LN]])
      have t3: "max 1 (len_formula A + len_formula \<tau>) \<le> 1 + poly q2 N + N"
      proof -
        have "len_formula A \<le> poly q2 N"
          by (rule order_trans[OF lenA poly_nat_mono[OF LN]])
        moreover have "len_formula \<tau> \<le> N" unfolding N_def by simp
        ultimately show ?thesis by simp
      qed
      have "len_proof pr \<le> len_proof pr2 + len_proof pii
                            + MP * max 1 (len_formula A + len_formula \<tau>)"
        by (rule pr_len)
      also have "\<dots> \<le> poly q1 N + poly q2 N + MP * (1 + poly q2 N + N)"
        by (intro add_mono mult_le_mono2 t1 t2 t3)
      finally show ?thesis using polyq by simp
    qed
    show "\<exists> pr. valid_proof Ftwo pr \<and> frege_proof.thesis pr = \<tau>
            \<and> assumptions pr = {}
            \<and> len_proof pr \<le> poly q (len_proof w + len_formula \<tau>)"
      using pr_valid pr_th pr_asm bound unfolding N_def by blast
  qed
qed


subsection \<open>Ftwo simulates Fone\<close>

text \<open>
  Both clauses of \<^const>\<open>simulates\<close>, with \<open>g = \<close>\<^const>\<open>reverse_translate\<close> and \<open>f\<close>
  picked out of the existence statement by choice.  Nothing about Fone or Ftwo is used
  beyond \<^const>\<open>frege_system\<close>, so this is Reckhow's theorem for the pair.
\<close>

theorem reckhow_simulates: "simulates Fone Ftwo"
proof -
  obtain p :: "nat poly" where P:
    "\<And>\<tau>. formula_well_formed (alphabet Ftwo) \<tau>
         \<Longrightarrow> len_formula (reverse_translate \<tau>) \<le> poly p (len_formula \<tau>)"
    using reverse_translate_length by blast
  obtain q :: "nat poly" where Q:
    "\<forall> w \<tau>.
      (formula_well_formed (alphabet Ftwo) \<tau>
       \<and> frege_proof.thesis w = reverse_translate \<tau>
       \<and> valid_proof Fone w \<and> assumptions w = {}
       \<and> (\<forall> s \<in> set (steps w). formula_well_formed (alphabet Fone) s))
      \<longrightarrow> (\<exists> pr. valid_proof Ftwo pr \<and> frege_proof.thesis pr = \<tau>
            \<and> assumptions pr = {}
            \<and> len_proof pr \<le> poly q (len_proof w + len_formula \<tau>))"
    using simulation_exists by blast
  define f :: "'c1 frege_proof \<Rightarrow> 'c2 formula \<Rightarrow> 'c2 frege_proof" where
    "f w \<tau> = (SOME pr. valid_proof Ftwo pr \<and> frege_proof.thesis pr = \<tau>
                       \<and> assumptions pr = {}
                       \<and> len_proof pr \<le> poly q (len_proof w + len_formula \<tau>))"
    for w :: "'c1 frege_proof" and \<tau> :: "'c2 formula"
  show ?thesis
    unfolding simulates_def
  proof (rule exI[where x = f], rule exI[where x = reverse_translate],
         rule exI[where x = p], rule exI[where x = q], rule conjI)
    show "\<forall> \<tau>. formula_well_formed (alphabet Ftwo) \<tau> \<longrightarrow>
             formula_well_formed (alphabet Fone) (reverse_translate \<tau>)
           \<and> formulas_equiv (reverse_translate \<tau>) (alphabet Fone) \<tau> (alphabet Ftwo)
           \<and> len_formula (reverse_translate \<tau>) \<le> poly p (len_formula \<tau>)"
    proof (intro allI impI)
      fix \<tau> :: "'c2 formula"
      assume wf: "formula_well_formed (alphabet Ftwo) \<tau>"
      show "formula_well_formed (alphabet Fone) (reverse_translate \<tau>)
            \<and> formulas_equiv (reverse_translate \<tau>) (alphabet Fone) \<tau> (alphabet Ftwo)
            \<and> len_formula (reverse_translate \<tau>) \<le> poly p (len_formula \<tau>)"
        using reverse_translate_well_formed reverse_translate_equiv[OF wf] P[OF wf]
        by blast
    qed
  next
    show "\<forall> w \<tau>.
       (formula_well_formed (alphabet Ftwo) \<tau>
        \<and> frege_proof.thesis w = reverse_translate \<tau>
        \<and> valid_proof Fone w \<and> assumptions w = {}
        \<and> (\<forall> s \<in> set (steps w). formula_well_formed (alphabet Fone) s))
       \<longrightarrow> valid_proof Ftwo (f w \<tau>)
           \<and> frege_proof.thesis (f w \<tau>) = \<tau>
           \<and> assumptions (f w \<tau>) = {}
           \<and> len_proof (f w \<tau>) \<le> poly q (len_proof w + len_formula \<tau>)"
    proof (intro allI impI)
      fix w :: "'c1 frege_proof" and \<tau> :: "'c2 formula"
      assume H: "formula_well_formed (alphabet Ftwo) \<tau>
        \<and> frege_proof.thesis w = reverse_translate \<tau>
        \<and> valid_proof Fone w \<and> assumptions w = {}
        \<and> (\<forall> s \<in> set (steps w). formula_well_formed (alphabet Fone) s)"
      have ex: "\<exists> pr. valid_proof Ftwo pr \<and> frege_proof.thesis pr = \<tau>
                    \<and> assumptions pr = {}
                    \<and> len_proof pr \<le> poly q (len_proof w + len_formula \<tau>)"
        using mp[OF Q[THEN spec, THEN spec, of \<tau> w] H] .
      show "valid_proof Ftwo (f w \<tau>)
            \<and> frege_proof.thesis (f w \<tau>) = \<tau>
            \<and> assumptions (f w \<tau>) = {}
            \<and> len_proof (f w \<tau>) \<le> poly q (len_proof w + len_formula \<tau>)"
        unfolding f_def by (rule someI_ex[OF ex])
    qed
  qed
qed

end

text \<open>
  Reckhow's theorem.  Any two Frege systems simulate each other: the statement is symmetric
  in the two systems, so one direction suffices.  Nothing beyond \<^const>\<open>frege_system\<close> ---
  finiteness, soundness and implicational completeness of the rules --- is assumed of
  either alphabet.
\<close>

theorem Reckhow:
  assumes "frege_system F1 \<and> frege_system F2"
  shows "simulates F1 F2"
proof -
  have f1: "frege_system F1" using assms by blast
  have f2: "frege_system F2" using assms by blast
  interpret frege_pair F1 F2 by (rule frege_pair.intro[OF f1 f2])
  show ?thesis by (rule reckhow_simulates)
qed

end

end
