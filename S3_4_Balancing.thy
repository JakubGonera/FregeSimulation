theory S3_4_Balancing
  imports S2_Frege Arithmetic "HOL.Transcendental"
begin

section \<open>Balancing formulas\<close>

text \<open>The lemma numbers in this theory follow Filmus' exposition.\<close>

subsection \<open>Congruence under substitution (Lemma 3.2)\<close>

text \<open>
  Replacing a formula by an equivalent one should preserve equivalence inside any
  surrounding formula. We establish this substitution principle together with
  bounds on the proof needed to justify the replacement. These bounds will let
  later constructions combine small equivalence proofs without losing control of
  size or depth.
\<close>

lemmas eval_sub_formula = sub_formula_eval

lemma sub_formula_agree:
  assumes "\<forall>v \<in> var_set_form f. s1 v = s2 v"
  shows "sub_formula s1 f = sub_formula s2 f"
  by (rule sub_formula_cong) (use assms in blast)

lemma sub_formula_comp:
  fixes s1 s2 :: "string \<Rightarrow> 'c formula" and f :: "'c formula"
  shows "sub_formula s1 (sub_formula s2 f) = sub_formula (\<lambda>v. sub_formula s1 (s2 v)) f"
  by (induction f) simp_all

lemma fresh_distinct_atoms_exist_general:
  fixes avoid :: "string set"
  assumes fin: "finite avoid"
  shows "\<exists>vs :: string list. length vs = n \<and> distinct vs \<and> set vs \<inter> avoid = {}"
proof (induction n)
  case 0
  show ?case by (rule exI[where x="[]"]) simp
next
  case (Suc n)
  obtain vs :: "string list" where
    vs_props: "length vs = n" "distinct vs" "set vs \<inter> avoid = {}"
    using Suc.IH by blast
  have inf_strings: "infinite (UNIV :: string set)"
    by (simp add: infinite_UNIV_listI)
  have finite_full: "finite (set vs \<union> avoid)"
    using vs_props fin by simp
  obtain x :: string where x_fresh: "x \<notin> set vs \<union> avoid"
    using inf_strings finite_full
    by (meson ex_new_if_finite finite_UnI finite_set)
  let ?vs' = "x # vs"
  have "length ?vs' = Suc n" using vs_props by simp
  moreover have "distinct ?vs'" using vs_props x_fresh by auto
  moreover have "set ?vs' \<inter> avoid = {}" using vs_props x_fresh by auto
  ultimately show ?case by blast
qed

locale frege_balancing =
  fixes F :: "'c frege"
  assumes "frege_system F"
begin

text \<open>
  A fixed De Morgan formula represents equivalence.  The variables in this
  witness are fixed here; later substitution lemmas supply arbitrary formulas.
\<close>

definition iff_dm :: "dm_conn formula" where
  "iff_dm = Conn Or [Conn And [Atom ''a'', Atom ''b''], 
                     Conn And [Conn Not [Atom ''a''], Conn Not [Atom ''b'']]]"

definition conn_iff :: "'c formula" where
  "conn_iff = (SOME f. formula_well_formed (alphabet F) f
       \<and> formulas_equiv f (alphabet F) iff_dm dm_alphabet
       \<and> var_set_form f \<subseteq> {''a'', ''b''})"

lemma conn_iff_spec:
  "\<exists>f. formula_well_formed (alphabet F) f
       \<and> formulas_equiv f (alphabet F) iff_dm dm_alphabet
       \<and> var_set_form f \<subseteq> {''a'', ''b''}"
proof -
  have fs: "frege_system F" using frege_balancing_axioms
    unfolding frege_balancing_def by blast
  have vars: "var_set_form iff_dm \<subseteq> {''a'', ''b''}"
    unfolding iff_dm_def by simp
  show ?thesis using frege_system.func_complete_supported[OF fs vars]
    unfolding formulas_equiv_def by blast
qed

lemma conn_iff_wf: "formula_well_formed (alphabet F) conn_iff"
  unfolding conn_iff_def using someI_ex[OF conn_iff_spec] by blast

lemma conn_iff_equiv: "formulas_equiv conn_iff (alphabet F) iff_dm dm_alphabet"
  unfolding conn_iff_def using someI_ex[OF conn_iff_spec] by blast

lemma conn_iff_vars: "var_set_form conn_iff \<subseteq> {''a'', ''b''}"
  unfolding conn_iff_def using someI_ex[OF conn_iff_spec] by blast

text \<open>The corresponding result for Lemma 3.1 was established in the
  theory of Frege systems.\<close>

fun is_subformula :: "'c formula \<Rightarrow> 'c formula \<Rightarrow> bool" where
  "is_subformula small (Atom a) = (small = Atom a)" |
  "is_subformula small (Conn c fs) = (small = Conn c fs \<or> (\<exists> g \<in> set fs. is_subformula small g))"

lemma subformula_smaller:
  assumes "is_subformula q p"
      and "p \<noteq> q"
    shows "len_formula q < len_formula p"
  using assms
proof (induction p)
  case (Atom a)
  from Atom.prems have "q = Atom a" by simp
  with Atom.prems(2) show ?case by simp
next
  case (Conn c fs)
  from Conn.prems have "q = Conn c fs \<or> (\<exists> g \<in> set fs. is_subformula q g)" by simp
  with Conn.prems(2) obtain g where g_in: "g \<in> set fs"
                                 and g_sub: "is_subformula q g" by auto
  have g_le: "len_formula g \<le> sum_list (map len_formula fs)"
    using g_in by (induction fs) auto
  show ?case
  proof (cases "q = g")
    case True
    have "len_formula q = len_formula g" using True by simp
    also have "\<dots> \<le> sum_list (map len_formula fs)" using g_le .
    also have "\<dots> < 1 + sum_list (map len_formula fs)" by simp
    also have "\<dots> = len_formula (Conn c fs)" by simp
    finally show ?thesis .
  next
    case False
    have "len_formula q < len_formula g"
      using Conn.IH g_in g_sub False by blast
    also have "\<dots> \<le> sum_list (map len_formula fs)" using g_le .
    also have "\<dots> < 1 + sum_list (map len_formula fs)" by simp
    also have "\<dots> = len_formula (Conn c fs)" by simp
    finally show ?thesis .
  qed
qed


text \<open>
  Each connective has a fixed congruence proof.  A canonical instantiation
  of its argument variables lets us bound the cost of these proofs uniformly.
\<close>

definition canonical_atoms :: "'c \<Rightarrow> string list" where
  "canonical_atoms c = (SOME vs.
       length vs = arity (alphabet F) c
     \<and> distinct vs
     \<and> set vs \<inter> ({''a'', ''b''} \<union> var_set_form conn_iff) = {})"

lemma var_set_form_finite: "finite (var_set_form f)"
  by (induction f) auto

lemma canonical_atoms_spec:
  shows "length (canonical_atoms c) = arity (alphabet F) c \<and>
         distinct (canonical_atoms c) \<and>
         ''a'' \<notin> set (canonical_atoms c) \<and>
         ''b'' \<notin> set (canonical_atoms c) \<and>
         set (canonical_atoms c) \<inter> var_set_form conn_iff = {}"
proof -
  have fin: "finite ({''a'', ''b''} \<union> var_set_form conn_iff)"
    using var_set_form_finite by simp
  have ex: "\<exists>vs :: string list.
              length vs = arity (alphabet F) c \<and> distinct vs
            \<and> set vs \<inter> ({''a'', ''b''} \<union> var_set_form conn_iff) = {}"
    using fresh_distinct_atoms_exist_general[OF fin] by blast
  have spec: "length (canonical_atoms c) = arity (alphabet F) c \<and>
              distinct (canonical_atoms c) \<and>
              set (canonical_atoms c) \<inter> ({''a'', ''b''} \<union> var_set_form conn_iff) = {}"
    unfolding canonical_atoms_def using someI_ex[OF ex] .
  thus ?thesis by auto
qed

lemma iff_congruent_base:
  fixes c :: 'c and i :: nat
  assumes i_bound: "i < arity (alphabet F) c"
  shows "\<exists>pr. valid_proof F pr \<and>
              assumptions pr = {conn_iff} \<and>
              thesis pr = sub_formula
                (\<lambda>v. if v = ''a''
                       then Conn c ((map Atom (canonical_atoms c))[i := Atom ''a''])
                     else if v = ''b''
                       then Conn c ((map Atom (canonical_atoms c))[i := Atom ''b''])
                     else Atom v)
                conn_iff \<and>
              (\<forall>st \<in> set (steps pr). formula_well_formed (alphabet F) st)"
proof -
  let ?atoms = "canonical_atoms c"
  let ?children_a = "(map Atom ?atoms)[i := Atom ''a'']"
  let ?children_b = "(map Atom ?atoms)[i := Atom ''b'']"
  let ?sub' = "\<lambda>v. if v = ''a'' then Conn c ?children_a
                  else if v = ''b'' then Conn c ?children_b
                  else Atom v"
  let ?al = "alphabet F"

  have atoms_len: "length ?atoms = arity (alphabet F) c"
    using canonical_atoms_spec by simp
  hence i_lt_atoms: "i < length ?atoms" using i_bound by simp
  have i_lt_map: "i < length (map Atom ?atoms)" using i_lt_atoms by simp

  have fs_F: "frege_system F"
    by (meson frege_balancing_axioms frege_balancing_def)


  have iff_dm_eval: "\<And>v. eval dm_alphabet v iff_dm = (v ''a'' = v ''b'')"
    unfolding iff_dm_def dm_alphabet_def by auto

  have sem_valid: "\<forall>val. eval ?al val conn_iff \<longrightarrow>
                         eval ?al val (sub_formula ?sub' conn_iff)"
  proof (intro allI impI)
    fix val :: "string \<Rightarrow> bool"
    assume assm: "eval ?al val conn_iff"
    let ?v2 = "\<lambda>v. eval ?al val (?sub' v)"

    have eval1: "eval ?al val conn_iff = (val ''a'' = val ''b'')"
    proof -
      have "eval ?al val conn_iff = eval dm_alphabet val iff_dm"
        using conn_iff_equiv unfolding formulas_equiv_def by simp
      also have "\<dots> = (val ''a'' = val ''b'')" using iff_dm_eval .
      finally show ?thesis .
    qed

    have ab_eq: "val ''a'' = val ''b''" using assm eval1 by simp

    have sub_eval2: "eval ?al val (sub_formula ?sub' conn_iff) = (?v2 ''a'' = ?v2 ''b'')"
    proof -
      have "eval ?al val (sub_formula ?sub' conn_iff) = eval ?al ?v2 conn_iff"
        by (rule eval_sub_formula)
      also have "\<dots> = eval dm_alphabet ?v2 iff_dm"
        using conn_iff_equiv unfolding formulas_equiv_def by simp
      also have "\<dots> = (?v2 ''a'' = ?v2 ''b'')"
        using iff_dm_eval .
      finally show ?thesis .
    qed

    have v2a: "?v2 ''a'' = eval ?al val (Conn c ?children_a)" by simp
    have v2b: "?v2 ''b'' = eval ?al val (Conn c ?children_b)" by simp

    have map_eq: "map (eval ?al val) ?children_a = map (eval ?al val) ?children_b"
    proof (rule nth_equalityI)
      show "length (map (eval ?al val) ?children_a) =
            length (map (eval ?al val) ?children_b)"
        by simp
    next
      fix j
      assume j_bound: "j < length (map (eval ?al val) ?children_a)"
      hence j_lt_map: "j < length (map Atom ?atoms)" by simp
      have nth_a: "map (eval ?al val) ?children_a ! j = eval ?al val (?children_a ! j)"
        using j_lt_map by simp
      have nth_b: "map (eval ?al val) ?children_b ! j = eval ?al val (?children_b ! j)"
        using j_lt_map by simp
      show "map (eval ?al val) ?children_a ! j = map (eval ?al val) ?children_b ! j"
      proof (cases "j = i")
        case True
        have a_at_j: "?children_a ! j = Atom ''a''"
          using True i_lt_map by simp
        have b_at_j: "?children_b ! j = Atom ''b''"
          using True i_lt_map by simp
        have lhs: "map (eval ?al val) ?children_a ! j = val ''a''"
        proof -
          have "map (eval ?al val) ?children_a ! j = eval ?al val (?children_a ! j)"
            using nth_a .
          also have "\<dots> = eval ?al val (Atom ''a'')"
            using a_at_j by (rule arg_cong)
          also have "\<dots> = val ''a''" by simp
          finally show ?thesis .
        qed
        have rhs: "map (eval ?al val) ?children_b ! j = val ''b''"
        proof -
          have "map (eval ?al val) ?children_b ! j = eval ?al val (?children_b ! j)"
            using nth_b .
          also have "\<dots> = eval ?al val (Atom ''b'')"
            using b_at_j by (rule arg_cong)
          also have "\<dots> = val ''b''" by simp
          finally show ?thesis .
        qed
        show ?thesis using lhs rhs ab_eq by simp
      next
        case False
        have a_at_j: "?children_a ! j = (map Atom ?atoms) ! j"
          using False j_lt_map by (simp add: nth_list_update)
        have b_at_j: "?children_b ! j = (map Atom ?atoms) ! j"
          using False j_lt_map by (simp add: nth_list_update)
        have lhs: "map (eval ?al val) ?children_a ! j = eval ?al val ((map Atom ?atoms) ! j)"
        proof -
          have "map (eval ?al val) ?children_a ! j = eval ?al val (?children_a ! j)"
            using nth_a .
          also have "\<dots> = eval ?al val ((map Atom ?atoms) ! j)"
            using a_at_j by (rule arg_cong)
          finally show ?thesis .
        qed
        have rhs: "map (eval ?al val) ?children_b ! j = eval ?al val ((map Atom ?atoms) ! j)"
        proof -
          have "map (eval ?al val) ?children_b ! j = eval ?al val (?children_b ! j)"
            using nth_b .
          also have "\<dots> = eval ?al val ((map Atom ?atoms) ! j)"
            using b_at_j by (rule arg_cong)
          finally show ?thesis .
        qed
        show ?thesis using lhs rhs by simp
      qed
    qed

    have conn_eq:
      "eval ?al val (Conn c ?children_a) = eval ?al val (Conn c ?children_b)"
      using map_eq by simp

    from conn_eq v2a v2b have v2_eq: "?v2 ''a'' = ?v2 ''b''" by simp
    thus "eval ?al val (sub_formula ?sub' conn_iff)"
      using sub_eval2 by simp
  qed

  have one_premise:
    "\<forall>val. (\<forall>f \<in> {conn_iff}. eval ?al val f) \<longrightarrow>
           eval ?al val (sub_formula ?sub' conn_iff)"
    using sem_valid by simp

  have fs_wf: "\<forall>f\<in>{conn_iff}. formula_well_formed (alphabet F) f"
    using conn_iff_wf by simp
  have conn_sub_wf:
    "formula_well_formed (alphabet F) (Conn c ((map Atom ?atoms)[i := Atom z]))" for z :: string
  proof -
    have allg: "formula_well_formed (alphabet F) (g :: 'c formula)"
      if "g \<in> set ((map Atom ?atoms)[i := Atom z])" for g
    proof -
      from that have "g \<in> insert (Atom z) (set (map Atom ?atoms))"
        using set_update_subset_insert by fastforce
      thus "formula_well_formed (alphabet F) g" by auto
    qed
    have "length ((map Atom ?atoms)[i := Atom z]) = arity (alphabet F) c"
      using atoms_len by simp
    thus ?thesis using allg by auto
  qed
  have sub'_wf: "formula_well_formed (alphabet F) (?sub' v)" for v :: string
    using conn_sub_wf by auto
  have th_wf: "formula_well_formed (alphabet F) (sub_formula ?sub' conn_iff)"
    using sub_formula_well_formed[OF conn_iff_wf sub'_wf] .
  have inst: "(\<forall>f\<in>{conn_iff}. formula_well_formed (alphabet F) f) \<longrightarrow>
              formula_well_formed (alphabet F) (sub_formula ?sub' conn_iff) \<longrightarrow>
              (\<forall>val. (\<forall>f\<in>{conn_iff}. eval (alphabet F) val f) \<longrightarrow>
                     eval (alphabet F) val (sub_formula ?sub' conn_iff)) \<longrightarrow>
              (\<exists>pr. valid_proof F pr \<and> assumptions pr = {conn_iff} \<and>
                    thesis pr = sub_formula ?sub' conn_iff \<and>
                    (\<forall>st \<in> set (steps pr). formula_well_formed (alphabet F) st))"
    using frege_system.impl_complete[OF fs_F] by blast
  show "\<exists>pr. valid_proof F pr \<and>
             assumptions pr = {conn_iff} \<and>
             thesis pr = sub_formula ?sub' conn_iff \<and>
             (\<forall>st \<in> set (steps pr). formula_well_formed (alphabet F) st)"
    using inst fs_wf th_wf one_premise by blast
qed

text \<open>
  Choose a base proof for each connective and argument position.  Finiteness
  of the alphabet and bounded arities give uniform maxima for the number of
  steps, their size, and their depth.  Substitution scales these constants.
\<close>

definition base_proof :: "'c \<Rightarrow> nat \<Rightarrow> 'c frege_proof" where
  "base_proof c i = (SOME pr. valid_proof F pr \<and>
       assumptions pr = {conn_iff} \<and>
       thesis pr = sub_formula
         (\<lambda>v. if v = ''a''
                then Conn c ((map Atom (canonical_atoms c))[i := Atom ''a''])
              else if v = ''b''
                then Conn c ((map Atom (canonical_atoms c))[i := Atom ''b''])
              else Atom v)
         conn_iff \<and>
       (\<forall>st \<in> set (steps pr). formula_well_formed (alphabet F) st))"

lemma base_proof_spec:
  assumes "i < arity (alphabet F) c"
  shows "valid_proof F (base_proof c i) \<and>
         assumptions (base_proof c i) = {conn_iff} \<and>
         thesis (base_proof c i) = sub_formula
           (\<lambda>v. if v = ''a''
                  then Conn c ((map Atom (canonical_atoms c))[i := Atom ''a''])
                else if v = ''b''
                  then Conn c ((map Atom (canonical_atoms c))[i := Atom ''b''])
                else Atom v)
           conn_iff \<and>
         (\<forall>st \<in> set (steps (base_proof c i)). formula_well_formed (alphabet F) st)"
  unfolding base_proof_def using someI_ex[OF iff_congruent_base[OF assms]] .

definition base_index_set :: "('c \<times> nat) set" where
  "base_index_set = {(c, i). i < arity (alphabet F) c}"

lemma base_index_set_finite: "finite base_index_set"
proof -
  have alphabet_finite: "finite (UNIV :: 'c set)"
    by (meson frege_balancing_axioms frege_balancing_def frege_system.finite_alphabet)
  have "base_index_set \<subseteq>
        (\<Union>c \<in> UNIV. (\<lambda>i. (c, i)) ` {i. i < arity (alphabet F) c})"
    unfolding base_index_set_def by auto
  moreover have "finite (\<Union>c \<in> (UNIV :: 'c set). (\<lambda>i. (c, i)) ` {i. i < arity (alphabet F) c})"
    using alphabet_finite by auto
  ultimately show ?thesis by (rule finite_subset)
qed

definition base_steps_count :: "'c \<times> nat \<Rightarrow> nat" where
  "base_steps_count p = length (steps (base_proof (fst p) (snd p)))"

definition base_step_lens :: "'c \<times> nat \<Rightarrow> nat set" where
  "base_step_lens p = len_formula ` set (steps (base_proof (fst p) (snd p)))"

definition base_step_depths :: "'c \<times> nat \<Rightarrow> nat set" where
  "base_step_depths p = depth_formula ` set (steps (base_proof (fst p) (snd p)))"

definition base_max_steps :: nat where
  "base_max_steps = Max (insert 1 (base_steps_count ` base_index_set))"

definition base_max_step_len :: nat where
  "base_max_step_len = Max (insert 1 (insert (len_formula conn_iff)
                              (\<Union>p \<in> base_index_set. base_step_lens p)))"

definition base_max_step_depth :: nat where
  "base_max_step_depth = Max (insert 1 (insert (depth_formula conn_iff)
                                (\<Union>p \<in> base_index_set. base_step_depths p)))"

lemma base_step_lens_finite: "finite (base_step_lens p)"
  unfolding base_step_lens_def by simp

lemma base_step_depths_finite: "finite (base_step_depths p)"
  unfolding base_step_depths_def by simp

lemma base_max_steps_bound:
  assumes "(c, i) \<in> base_index_set"
  shows "length (steps (base_proof c i)) \<le> base_max_steps"
proof -
  have fin: "finite (insert 1 (base_steps_count ` base_index_set))"
    using base_index_set_finite by simp
  have "length (steps (base_proof c i)) = base_steps_count (c, i)"
    unfolding base_steps_count_def by simp
  moreover have "base_steps_count (c, i) \<in> base_steps_count ` base_index_set"
    using assms by (rule imageI)
  ultimately show ?thesis
    unfolding base_max_steps_def using fin by (auto intro: Max_ge)
qed

lemma base_max_step_len_conn_iff: "len_formula conn_iff \<le> base_max_step_len"
proof -
  let ?S = "insert 1 (insert (len_formula conn_iff) (\<Union>p \<in> base_index_set. base_step_lens p))"
  have fin: "finite ?S"
    using base_index_set_finite base_step_lens_finite by auto
  have mem: "len_formula conn_iff \<in> ?S" by auto
  show ?thesis
    unfolding base_max_step_len_def
    using Max_ge[OF fin mem] .
qed

lemma base_max_step_depth_conn_iff: "depth_formula conn_iff \<le> base_max_step_depth"
proof -
  let ?S = "insert 1 (insert (depth_formula conn_iff) (\<Union>p \<in> base_index_set. base_step_depths p))"
  have fin: "finite ?S"
    using base_index_set_finite base_step_depths_finite by auto
  have mem: "depth_formula conn_iff \<in> ?S" by auto
  show ?thesis
    unfolding base_max_step_depth_def
    using Max_ge[OF fin mem] .
qed

lemma base_max_step_len_bound:
  assumes "(c, i) \<in> base_index_set"
  assumes "step \<in> set (steps (base_proof c i))"
  shows "len_formula step \<le> base_max_step_len"
proof -
  let ?S = "insert 1 (insert (len_formula conn_iff) (\<Union>p \<in> base_index_set. base_step_lens p))"
  have fin: "finite ?S"
    using base_index_set_finite base_step_lens_finite by auto
  have "len_formula step \<in> base_step_lens (c, i)"
    using assms unfolding base_step_lens_def by simp
  hence in_S: "len_formula step \<in> ?S" using assms by auto
  have "len_formula step \<le> Max ?S" using Max_ge[OF fin in_S] .
  thus ?thesis unfolding base_max_step_len_def .
qed

lemma base_max_step_depth_bound:
  assumes "(c, i) \<in> base_index_set"
  assumes "step \<in> set (steps (base_proof c i))"
  shows "depth_formula step \<le> base_max_step_depth"
proof -
  let ?S = "insert 1 (insert (depth_formula conn_iff) (\<Union>p \<in> base_index_set. base_step_depths p))"
  have fin: "finite ?S"
    using base_index_set_finite base_step_depths_finite by auto
  have "depth_formula step \<in> base_step_depths (c, i)"
    using assms unfolding base_step_depths_def by simp
  hence in_S: "depth_formula step \<in> ?S" using assms by auto
  have "depth_formula step \<le> Max ?S" using Max_ge[OF fin in_S] .
  thus ?thesis unfolding base_max_step_depth_def .
qed

subsection \<open>A balancing connective (Lemma 4.1)\<close>

text \<open>
  We choose a fixed formula that acts as a conditional: it returns one branch when
  its selector is true and the other when it is false. Functional completeness
  supplies this formula in the given alphabet. It will combine the three recursive
  pieces of the balancing construction.
\<close>

definition dm_balancing where
  "dm_balancing = Conn Or [Conn And [Atom ''x'', Atom ''z''], 
                           Conn And [Atom ''y'', Conn Not [Atom ''z'']]]"

lemma balancing_formula_exists:
  "\<exists>f. formula_well_formed (alphabet F) f
       \<and> formulas_equiv dm_balancing dm_alphabet f (alphabet F)
       \<and> var_set_form f \<subseteq> {''x'', ''y'', ''z''}"
proof -
  have fs: "frege_system F" using frege_balancing_axioms
    unfolding frege_balancing_def by blast
  have vars: "var_set_form dm_balancing \<subseteq> {''x'', ''y'', ''z''}"
    unfolding dm_balancing_def by simp
  show ?thesis using frege_system.func_complete_supported[OF fs vars] by blast
qed

definition custom_balancing where
  "custom_balancing = (SOME f. formula_well_formed (alphabet F) f
       \<and> formulas_equiv dm_balancing dm_alphabet f (alphabet F)
       \<and> var_set_form f \<subseteq> {''x'', ''y'', ''z''})"

fun balance :: "'c formula \<Rightarrow> 'c formula \<Rightarrow> 'c formula \<Rightarrow> 'c formula" where
  "balance x y z = (let sub = \<lambda>v.
                  if v = ''x'' then x
                  else if v = ''y'' then y
                  else if v = ''z'' then z
                  else Atom v in sub_formula sub custom_balancing)"

lemma custom_balancing_spec:
  shows "formula_well_formed (alphabet F) custom_balancing
       \<and> formulas_equiv dm_balancing dm_alphabet custom_balancing (alphabet F)"
  unfolding custom_balancing_def
  using someI_ex[OF balancing_formula_exists] by blast

lemma custom_balancing_vars:
  "var_set_form custom_balancing \<subseteq> {''x'', ''y'', ''z''}"
  unfolding custom_balancing_def using someI_ex[OF balancing_formula_exists] by blast

lemma dm_balancing_eval:
  shows "eval dm_alphabet val dm_balancing
         = (if val ''z'' then val ''x'' else val ''y'')"
  unfolding dm_balancing_def by (auto simp: dm_alphabet_def)

lemma balance_eval:
  shows "eval (alphabet F) val (balance x y z)
         = (if eval (alphabet F) val z
            then eval (alphabet F) val x
            else eval (alphabet F) val y)"
proof -
  let ?sub = "\<lambda>v. if v = ''x'' then x
                  else if v = ''y'' then y
                  else if v = ''z'' then z
                  else Atom v"
  let ?val' = "\<lambda>v. eval (alphabet F) val (?sub v)"
  have unfold: "balance x y z = sub_formula ?sub custom_balancing"
    by (simp add: Let_def)
  have step_sub: "eval (alphabet F) val (sub_formula ?sub custom_balancing)
               = eval (alphabet F) ?val' custom_balancing"
    by (rule eval_sub_formula)
  have step_equiv: "eval (alphabet F) ?val' custom_balancing
               = eval dm_alphabet ?val' dm_balancing"
    using custom_balancing_spec unfolding formulas_equiv_def by auto
  have step_dm: "eval dm_alphabet ?val' dm_balancing
               = (if ?val' ''z'' then ?val' ''x'' else ?val' ''y'')"
    by (rule dm_balancing_eval)
  have "?val' ''x'' = eval (alphabet F) val x"
   and "?val' ''y'' = eval (alphabet F) val y"
   and "?val' ''z'' = eval (alphabet F) val z"
    by simp_all
  thus ?thesis using unfold step_sub step_equiv step_dm by simp
qed

subsection \<open>Finding a balanced subformula (Lemma 4.2)\<close>

text \<open>
  Balancing needs a subformula that is neither too small nor too large. Descending
  through sufficiently large children finds such an occurrence, with size bounds
  determined by the maximum connective arity. These bounds ensure that replacing
  the occurrence by a constant leaves a smaller problem.
\<close>


fun children :: "'c formula \<Rightarrow> 'c formula set" where
  "children (Atom v) = {}" |
  "children (Conn c fs) = set fs"

lemma child_neq_parent:
  assumes "q \<in> children p"
  shows "p \<noteq> q"
  by (metis add.right_neutral add_Suc_right assms children.cases 
      children.simps(1,2) dual_order.refl empty_iff formula.size(4)
      le_imp_less_Suc less_not_refl size_list_estimation')


lemma spira_descent:
  fixes T :: nat
  assumes "len_formula p \<ge> T"
  shows "\<exists> q. is_subformula q p \<and> len_formula q \<ge> T \<and>
              (\<forall> c \<in> children q. len_formula c < T)"
  using assms
proof (induction "len_formula p" arbitrary: p rule: less_induct)
  case less
  show ?case
  proof (cases "\<forall> c \<in> children p. len_formula c < T")
    case True
    thus ?thesis
      by (metis is_subformula.elims(3) less.prems)
  next
    case False
    hence "\<exists> c \<in> children p. len_formula c \<ge> T"
      by fastforce
    from this obtain q :: "'c formula" where
     q_def: "len_formula q \<ge> T \<and> q \<in> children p" by force
    hence subf: "is_subformula q p"
      by (metis children.simps(1,2) emptyE is_subformula.elims(3))
    have "p \<noteq> q" using q_def child_neq_parent by simp
    hence "len_formula q < len_formula p" 
      using subformula_smaller[of q p] subf by simp
    thus ?thesis
      by (metis children.elims empty_iff is_subformula.simps(2) less.hyps q_def)
  qed
qed

lemma subformula_wf:
  assumes "formula_well_formed a f"
      and "is_subformula q f"
    shows "formula_well_formed a q"
  using assms
proof (induction f)
  case (Atom v)
  from Atom.prems(2) have "q = Atom v" by simp
  thus ?case by simp
next
  case (Conn c fs)
  from Conn.prems(2) have disjunction:
    "q = Conn c fs \<or> (\<exists> g \<in> set fs. is_subformula q g)"
    by simp
  show ?case
  proof (cases "q = Conn c fs")
    case True
    thus ?thesis using Conn.prems(1) by simp
  next
    case False
    with disjunction obtain g where g_in: "g \<in> set fs"
                                and g_sub: "is_subformula q g"
      by auto
    have wf_child: "formula_well_formed a g"
      using Conn.prems(1) g_in by simp
    show ?thesis using Conn.IH g_in wf_child g_sub by blast
  qed
qed

lemma spiras_selection_gen:
  assumes "formula_well_formed (alphabet F) p"
      and "len_formula p \<ge> 2" (* It's not a single atom *)
      and "k = Max ((arity (alphabet F)) ` (UNIV :: 'c set))"
      and "k > 1" (* k == 1 is a special case *)
  obtains q where
      "is_subformula q p"
      "(k + 1) * len_formula q + k \<ge> len_formula p"
      "(k + 1) * len_formula q \<le> k * len_formula p"
proof -
  let ?n = "len_formula p"
  let ?T = "?n div (k+1)" (* floor(n/(k+1)) *)
  have p_ge_T: "len_formula p \<ge> ?T"
    by (rule div_le_dividend)
  from spira_descent obtain q where w:
    "is_subformula q p" "len_formula q \<ge> ?T"
    "\<forall> c \<in> children q. len_formula c < ?T"
    using p_ge_T by blast
  from w(2) have lower: "(k + 1) * len_formula q + k \<ge> ?n"
    by (rule nat_div_to_mult)
  have upper: "(k + 1) * len_formula q \<le> k * len_formula p"
  proof (cases q)
    case (Atom v)
    hence "len_formula q = 1" by simp
    thus ?thesis using assms
      by (simp add: Suc_leI)
  next
    case (Conn c fs)
    have "formula_well_formed (alphabet F) (Conn c fs)"
      using assms w subformula_wf Conn by blast
    hence "length fs = arity (alphabet F) c"
      by force
    hence len_fs_le_k: "length fs \<le> k"
    proof -
      have alphabet_finite: "finite (UNIV :: 'c set)"
        by (meson frege_balancing_axioms frege_balancing_def
                  frege_system.finite_alphabet)
      hence finite_image: "finite ((arity (alphabet F)) ` (UNIV :: 'c set))"
        by simp
      have "arity (alphabet F) c \<in> (arity (alphabet F)) ` (UNIV :: 'c set)"
        by simp
      with finite_image have
        "arity (alphabet F) c \<le> Max ((arity (alphabet F)) ` (UNIV :: 'c set))"
        by (rule Max_ge)
      thus ?thesis
        using \<open>length fs = arity (alphabet F) c\<close> assms(3) by simp
    qed
    have len_le: "len_formula (Conn c fs) \<le> 1 + k * Max (set (map len_formula fs))"
    proof -
      let ?M = "Max (set (map len_formula fs))"
      show ?thesis
      proof (cases "fs = []")
        case True
        thus ?thesis by simp
      next
        case False
        have fin: "finite (set (map len_formula fs))" by simp
        have each_le: "\<And>x. x \<in> set fs \<Longrightarrow> len_formula x \<le> ?M"
        proof -
          fix x assume "x \<in> set fs"
          hence "len_formula x \<in> set (map len_formula fs)" by simp
          with fin show "len_formula x \<le> ?M" by simp
        qed
        have "sum_list (map len_formula fs) \<le> sum_list (map (\<lambda>_. ?M) fs)"
          using each_le by (rule sum_list_mono)
        also have "sum_list (map (\<lambda>_. ?M) fs) = length fs * ?M"
          by (simp add: sum_list_triv)
        also have "length fs * ?M \<le> k * ?M"
          using len_fs_le_k by (rule mult_le_mono1)
        finally have sum_le:
          "sum_list (map len_formula fs) \<le> k * ?M" .
        have "len_formula (Conn c fs) = 1 + sum_list (map len_formula fs)"
          by simp
        also have "\<dots> \<le> 1 + k * ?M" using sum_le by simp
        finally show ?thesis .
      qed
    qed
    show ?thesis
    proof (cases "fs = []")
      case True
      hence len_q_eq: "len_formula q = 1" using Conn by simp
      have "(k + 1) * len_formula q = k + 1" using len_q_eq by simp
      also have "k + 1 \<le> 2 * k" using assms(4) by linarith
      also have "2 * k = k * 2" by simp
      also have "k * 2 \<le> k * ?n"
        using assms(2) by (rule mult_le_mono2)
      finally show ?thesis .
    next
      case False
      let ?M = "Max (set (map len_formula fs))"
      have M_lt_T: "?M < ?T"
      proof -
        have Mset: "?M \<in> set (map len_formula fs)"
          using False by simp
        then obtain c' where c'_in: "c' \<in> set fs"
                         and c'_eq: "len_formula c' = ?M"
          by auto
        from c'_in have "c' \<in> children q" using Conn by simp
        hence "len_formula c' < ?T" using w(3) by blast
        thus ?thesis using c'_eq by simp
      qed
      have M_plus_1_bound: "(k + 1) * (?M + 1) \<le> ?n"
      proof -
        have "(k + 1) * (?M + 1) \<le> (k + 1) * ?T"
          using M_lt_T by (intro mult_le_mono2) simp
        also have "(k + 1) * ?T \<le> ?n"
          using div_mult_mod_eq[of ?n "k + 1"]
          by (simp add: algebra_simps)
        finally show ?thesis .
      qed
      have aux: "(k + 1) * (1 + k * ?M) \<le> k * ?n"
      proof -
        have eq: "(k + 1) * (1 + k * ?M) = (k + 1) + k * ((k + 1) * ?M)"
          by (simp add: algebra_simps)
        have packed_eq:
          "k * ((k + 1) * ?M) + k * (k + 1) = k * ((k + 1) * (?M + 1))"
          by (simp add: algebra_simps)
        have "k * ((k + 1) * (?M + 1)) \<le> k * ?n"
          using M_plus_1_bound by (rule mult_le_mono2)
        with packed_eq have packed:
          "k * ((k + 1) * ?M) + k * (k + 1) \<le> k * ?n"
          by simp
        have offset: "(k + 1) \<le> k * (k + 1)"
          using assms(4) by simp
        from packed offset show ?thesis using eq by linarith
      qed
      have "(k + 1) * len_formula (Conn c fs) \<le> (k + 1) * (1 + k * ?M)"
        using len_le by (rule mult_le_mono2)
      also have "\<dots> \<le> k * ?n" using aux .
      finally show ?thesis using Conn by simp
    qed
  qed
  show ?thesis using w(1) lower upper that by blast
qed

lemma spiras_selection_one:
  assumes "formula_well_formed (alphabet F) p"
      and "len_formula p \<ge> 2" (* It's not a single atom *)
      and "Max ((arity (alphabet F)) ` (UNIV :: 'c set)) = 1"
  obtains q where
      "is_subformula q p"
      "3 * len_formula q \<ge> len_formula p"
      "3 * len_formula q \<le> 2 * len_formula p"
proof -
  let ?n = "len_formula p"
  let ?T = "(2 * ?n) div 3"
  have T_ge_1: "?T \<ge> 1"
  proof -
    have "(3::nat) \<le> 2 * ?n" using assms(2) by simp
    hence "(3::nat) div 3 \<le> (2 * ?n) div 3" by (rule div_le_mono)
    thus ?thesis by simp
  qed
  have T_le_n: "?T \<le> ?n"
  proof -
    have "2 * ?n \<le> 3 * ?n" by simp
    hence "(2 * ?n) div 3 \<le> (3 * ?n) div 3" by (rule div_le_mono)
    also have "(3 * ?n) div 3 = ?n" by simp
    finally show ?thesis .
  qed
  from spira_descent T_le_n obtain q where w:
    "is_subformula q p" "len_formula q \<ge> ?T"
    "\<forall> c \<in> children q. len_formula c < ?T"
    by blast
  have wf_q: "formula_well_formed (alphabet F) q"
    using assms(1) w(1) subformula_wf by blast
  have alphabet_finite: "finite (UNIV :: 'c set)"
    by (meson frege_balancing_axioms frege_balancing_def
              frege_system.finite_alphabet)
  hence finite_image: "finite ((arity (alphabet F)) ` (UNIV :: 'c set))"
    by simp
  have len_q_le_T: "len_formula q \<le> ?T"
  proof (cases q)
    case (Atom v)
    hence "len_formula q = 1" by simp
    thus ?thesis using T_ge_1 by simp
  next
    case (Conn c fs)
    have "arity (alphabet F) c \<in> (arity (alphabet F)) ` (UNIV :: 'c set)"
      by simp
    with finite_image have
      "arity (alphabet F) c \<le> Max ((arity (alphabet F)) ` (UNIV :: 'c set))"
      by (rule Max_ge)
    hence arity_le_1: "arity (alphabet F) c \<le> 1" using assms(3) by simp
    have "length fs = arity (alphabet F) c" using wf_q Conn by simp
    hence len_fs: "length fs \<le> 1" using arity_le_1 by simp
    show ?thesis
    proof (cases fs)
      case Nil
      hence "len_formula q = 1" using Conn by simp
      thus ?thesis using T_ge_1 by simp
    next
      case (Cons f fs')
      have "length fs' = 0" using len_fs Cons by simp
      hence "fs' = []" by simp
      with Cons have fs_singleton: "fs = [f]" by simp
      hence q_unfold: "len_formula q = 1 + len_formula f" using Conn by simp
      have "f \<in> children q" using fs_singleton Conn by simp
      hence "len_formula f < ?T" using w(3) by blast
      hence "len_formula f \<le> ?T - 1" by simp
      thus ?thesis using q_unfold T_ge_1 by simp
    qed
  qed
  from w(2) len_q_le_T have len_q_eq: "len_formula q = ?T" by simp
  have bound1: "3 * len_formula q \<ge> ?n"
  proof -
    have decomp: "?T * 3 + (2 * ?n) mod 3 = 2 * ?n"
      by (rule div_mult_mod_eq)
    have mod_le: "(2 * ?n) mod 3 \<le> 2"
      using mod_less_divisor[of 3 "2 * ?n"] by simp
    from decomp mod_le assms(2) have "?T * 3 \<ge> ?n" by linarith
    hence "3 * ?T \<ge> ?n" by (simp add: algebra_simps)
    thus ?thesis using len_q_eq by simp
  qed
  have bound2: "3 * len_formula q \<le> 2 * ?n"
  proof -
    have "?T * 3 \<le> 2 * ?n"
      using div_mult_mod_eq[of "2 * ?n" 3] by linarith
    hence "3 * ?T \<le> 2 * ?n" by (simp add: algebra_simps)
    thus ?thesis using len_q_eq by simp
  qed
  show ?thesis using w(1) bound1 bound2 that by blast
qed

definition spira_threshold :: nat where
  "spira_threshold = 4 * max (Max ((arity (alphabet F)) ` (UNIV :: 'c set))) 2 + 4"

definition spiras_sel :: "'c formula \<Rightarrow> 'c formula" where
  "spiras_sel p = (
     let k = Max ((arity (alphabet F)) ` (UNIV :: 'c set)) in
     if k > 1 then
       (SOME q. is_subformula q p
                \<and> (k + 1) * len_formula q + k \<ge> len_formula p
                \<and> (k + 1) * len_formula q \<le> k * len_formula p)
     else
       (SOME q. is_subformula q p
                \<and> 3 * len_formula q \<ge> len_formula p
                \<and> 3 * len_formula q \<le> 2 * len_formula p))"


subsection \<open>Lemma 4.3\<close>

text \<open>
  We now construct the balanced form of a formula and prove its three main
  properties: the same truth value, logarithmic depth, and polynomial size. The
  construction repeatedly splits at the occurrence selected above. Small formulas
  form the base cases of the recursion.
\<close>

subsubsection \<open>The balancing construction and equivalence\<close>

text \<open>
  A position records one particular occurrence of a subformula, so replacing it
  does not affect other occurrences of the same formula. We define replacement by
  a Boolean constant and recursively balance the two replacements and the selected
  subformula. Shannon expansion then proves that combining these pieces preserves
  the original truth value.
\<close>

definition top_conn :: "'c" where
  "top_conn = (SOME t. arity (alphabet F) t = 0
                     \<and> (\<forall> val. eval (alphabet F) val (Conn t []) = True))"

definition bot_conn :: "'c" where
  "bot_conn = (SOME b. arity (alphabet F) b = 0
                     \<and> (\<forall> val. eval (alphabet F) val (Conn b []) = False))"

lemma top_conn_spec:
  shows "arity (alphabet F) top_conn = 0
       \<and> (\<forall> val. eval (alphabet F) val (Conn top_conn []) = True)"
proof -
  have "\<exists> t. arity (alphabet F) t = 0
           \<and> (\<forall> val. eval (alphabet F) val (Conn t []) = True)"
    by (meson frege_balancing_axioms frege_balancing_def frege_system.has_top)
  thus ?thesis unfolding top_conn_def by (rule someI_ex)
qed

lemma bot_conn_spec:
  shows "arity (alphabet F) bot_conn = 0
       \<and> (\<forall> val. eval (alphabet F) val (Conn bot_conn []) = False)"
proof -
  have "\<exists> b. arity (alphabet F) b = 0
           \<and> (\<forall> val. eval (alphabet F) val (Conn b []) = False)"
    by (meson frege_balancing_axioms frege_balancing_def frege_system.has_bot)
  thus ?thesis unfolding bot_conn_def by (rule someI_ex)
qed

definition true_const :: "'c formula" where
  "true_const = Conn top_conn []"

definition false_const :: "'c formula" where
  "false_const = Conn bot_conn []"

lemma true_const_eval:
  shows "eval (alphabet F) val true_const = True"
  unfolding true_const_def using top_conn_spec by simp

lemma false_const_eval:
  shows "eval (alphabet F) val false_const = False"
  unfolding false_const_def using bot_conn_spec by simp

lemma true_const_wf:
  shows "formula_well_formed (alphabet F) true_const"
  unfolding true_const_def using top_conn_spec by simp

lemma false_const_wf:
  shows "formula_well_formed (alphabet F) false_const"
  unfolding false_const_def using bot_conn_spec by simp

lemma true_const_len:
  shows "len_formula true_const = 1"
  unfolding true_const_def by simp

lemma false_const_len:
  shows "len_formula false_const = 1"
  unfolding false_const_def by simp

text \<open>
  A position is a path of child indices from the root.  The empty path
  denotes the whole formula.  Positions identify a particular node, even
  when several subformulas have the same shape; this distinction is needed
  when fixing a selected subformula during balancing.
\<close>

fun subterm_at :: "'c formula \<Rightarrow> nat list \<Rightarrow> 'c formula" where
  "subterm_at p [] = p" |
  "subterm_at (Atom v) (i # js) = Atom v" |
  "subterm_at (Conn c fs) (i # js) = subterm_at (fs ! i) js"

fun valid_position :: "'c formula \<Rightarrow> nat list \<Rightarrow> bool" where
  "valid_position p [] = True" |
  "valid_position (Atom v) (i # js) = False" |
  "valid_position (Conn c fs) (i # js) = (i < length fs \<and> valid_position (fs ! i) js)"

text \<open>Fixing a position replaces only that subtree by a constant.\<close>
fun fix_at :: "nat list \<Rightarrow> bool \<Rightarrow> 'c formula \<Rightarrow> 'c formula" where
  "fix_at [] b p = (if b then true_const else false_const)" |
  "fix_at (i # js) b (Atom v) = Atom v" |
  "fix_at (i # js) b (Conn c fs) = Conn c (fs[i := fix_at js b (fs ! i)])"

lemma is_subformula_imp_position:
  "is_subformula q p \<Longrightarrow> \<exists> pos. valid_position p pos \<and> subterm_at p pos = q"
proof (induction p)
  case (Atom a)
  hence "q = Atom a" by simp
  thus ?case by (intro exI[where x = "[]"]) simp
next
  case (Conn c fs)
  from Conn.prems have "q = Conn c fs \<or> (\<exists> g \<in> set fs. is_subformula q g)"
    by simp
  thus ?case
  proof
    assume "q = Conn c fs"
    thus ?case by (intro exI[where x = "[]"]) simp
  next
    assume "\<exists> g \<in> set fs. is_subformula q g"
    then obtain g where g_in: "g \<in> set fs" and g_sub: "is_subformula q g"
      by blast
    have "\<exists> i. i < length fs \<and> fs ! i = g"
      using g_in by (simp add: in_set_conv_nth)
    then obtain i where i_lt: "i < length fs" and fs_i: "fs ! i = g" by blast
    from Conn.IH[OF g_in g_sub] obtain pos'
      where v': "valid_position g pos'" and s': "subterm_at g pos' = q" by blast
    have "valid_position (Conn c fs) (i # pos')"
      using i_lt fs_i v' by simp
    moreover have "subterm_at (Conn c fs) (i # pos') = q"
      using fs_i s' by simp
    ultimately show ?case by blast
  qed
qed

lemma sum_list_len_update_eq:
  "i < length fs
   \<Longrightarrow> sum_list (map len_formula (fs[i := z])) + len_formula (fs ! i)
       = sum_list (map len_formula fs) + len_formula z"
proof (induction fs arbitrary: i)
  case Nil
  thus ?case by simp
next
  case (Cons a fs')
  show ?case
  proof (cases i)
    case 0
    thus ?thesis by (simp add: algebra_simps)
  next
    case (Suc i')
    have i'_lt: "i' < length fs'" using Cons.prems Suc by simp
    have IH': "sum_list (map len_formula (fs'[i' := z])) + len_formula (fs' ! i')
             = sum_list (map len_formula fs') + len_formula z"
      using Cons.IH[OF i'_lt] .
    have "sum_list (map len_formula ((a # fs')[i := z])) + len_formula ((a # fs') ! i)
        = len_formula a
          + (sum_list (map len_formula (fs'[i' := z])) + len_formula (fs' ! i'))"
      using Suc by (simp add: algebra_simps)
    also have "\<dots> = len_formula a
                    + (sum_list (map len_formula fs') + len_formula z)"
      using IH' by simp
    also have "\<dots> = sum_list (map len_formula (a # fs')) + len_formula z"
      by (simp add: algebra_simps)
    finally show ?thesis .
  qed
qed

lemma fix_at_eval:
  assumes "valid_position p pos"
  shows "eval (alphabet F) val p
         = (if eval (alphabet F) val (subterm_at p pos)
            then eval (alphabet F) val (fix_at pos True p)
            else eval (alphabet F) val (fix_at pos False p))"
  using assms
proof (induction pos arbitrary: p)
  case Nil
  show ?case
    using true_const_eval false_const_eval by simp
next
  case (Cons i js)
  from Cons.prems obtain c fs where p_eq: "p = Conn c fs"
    by (cases p) auto
  have i_lt: "i < length fs"
   and vjs: "valid_position (fs ! i) js"
    using Cons.prems p_eq by auto
  let ?ev = "eval (alphabet F) val"
  let ?child = "fs ! i"
  have IH: "?ev ?child = (if ?ev (subterm_at ?child js)
                          then ?ev (fix_at js True ?child)
                          else ?ev (fix_at js False ?child))"
    using Cons.IH[OF vjs] .
  have sub_eq: "subterm_at p (i # js) = subterm_at ?child js"
    using p_eq by simp
  have conn_eq: "\<And> z. ?ev z = ?ev ?child
                 \<Longrightarrow> ?ev (Conn c (fs[i := z])) = ?ev p"
  proof -
    fix z assume z_ev: "?ev z = ?ev ?child"
    have "map ?ev (fs[i := z]) = map ?ev fs"
    proof (rule nth_equalityI)
      show "length (map ?ev (fs[i := z])) = length (map ?ev fs)" by simp
    next
      fix j assume "j < length (map ?ev (fs[i := z]))"
      hence j_lt: "j < length fs" by simp
      show "map ?ev (fs[i := z]) ! j = map ?ev fs ! j"
      proof (cases "j = i")
        case True
        thus ?thesis using z_ev i_lt j_lt by simp
      next
        case False
        thus ?thesis using j_lt by (simp add: nth_list_update)
      qed
    qed
    thus "?ev (Conn c (fs[i := z])) = ?ev p"
      using p_eq by simp
  qed
  show ?case
  proof (cases "?ev (subterm_at ?child js)")
    case True
    have "?ev (fix_at js True ?child) = ?ev ?child"
      using IH True by simp
    from conn_eq[OF this]
    have "?ev (Conn c (fs[i := fix_at js True ?child])) = ?ev p" .
    hence "?ev (fix_at (i # js) True p) = ?ev p"
      using p_eq by simp
    thus ?thesis using True sub_eq by simp
  next
    case False
    have "?ev (fix_at js False ?child) = ?ev ?child"
      using IH False by simp
    from conn_eq[OF this]
    have "?ev (Conn c (fs[i := fix_at js False ?child])) = ?ev p" .
    hence "?ev (fix_at (i # js) False p) = ?ev p"
      using p_eq by simp
    thus ?thesis using False sub_eq by simp
  qed
qed

lemma fix_at_len_le:
  shows "len_formula (fix_at pos b p) \<le> len_formula p"
proof (induction pos arbitrary: p)
  case Nil
  have "len_formula (fix_at [] b p) = 1"
    using true_const_len false_const_len by simp
  moreover have "len_formula p \<ge> 1" by (rule len_formula_positive)
  ultimately show ?case by simp
next
  case (Cons i js)
  show ?case
  proof (cases p)
    case (Atom v)
    thus ?thesis by simp
  next
    case (Conn c fs)
    show ?thesis
    proof (cases "i < length fs")
      case True
      have IH: "len_formula (fix_at js b (fs ! i)) \<le> len_formula (fs ! i)"
        using Cons.IH .
      have "sum_list (map len_formula (fs[i := fix_at js b (fs ! i)]))
            + len_formula (fs ! i)
          = sum_list (map len_formula fs) + len_formula (fix_at js b (fs ! i))"
        using sum_list_len_update_eq[OF True] .
      hence "sum_list (map len_formula (fs[i := fix_at js b (fs ! i)]))
           \<le> sum_list (map len_formula fs)"
        using IH by linarith
      thus ?thesis using Conn by simp
    next
      case False
      hence "fs[i := fix_at js b (fs ! i)] = fs"
        by (simp add: list_update_beyond)
      thus ?thesis using Conn by simp
    qed
  qed
qed

lemma fix_at_len_strict:
  assumes "valid_position p pos"
      and "len_formula (subterm_at p pos) \<ge> 2"
    shows "len_formula (fix_at pos b p) < len_formula p"
  using assms
proof (induction pos arbitrary: p)
  case Nil
  have lhs_eq: "len_formula (fix_at [] b p) = 1"
    using true_const_len false_const_len by simp
  have "len_formula p \<ge> 2" using Nil.prems(2) by simp
  thus ?case using lhs_eq by simp
next
  case (Cons i js)
  from Cons.prems(1) obtain c fs where p_eq: "p = Conn c fs"
    by (cases p) auto
  have i_lt: "i < length fs"
   and vjs: "valid_position (fs ! i) js"
    using Cons.prems(1) p_eq by auto
  have sub2: "len_formula (subterm_at (fs ! i) js) \<ge> 2"
    using Cons.prems(2) p_eq by simp
  have IH: "len_formula (fix_at js b (fs ! i)) < len_formula (fs ! i)"
    using Cons.IH[OF vjs sub2] .
  have "sum_list (map len_formula (fs[i := fix_at js b (fs ! i)]))
        + len_formula (fs ! i)
      = sum_list (map len_formula fs) + len_formula (fix_at js b (fs ! i))"
    using sum_list_len_update_eq[OF i_lt] .
  hence "sum_list (map len_formula (fs[i := fix_at js b (fs ! i)]))
       < sum_list (map len_formula fs)"
    using IH by linarith
  thus ?case using p_eq by simp
qed

text \<open>
  Fixing a position replaces its subtree by a single constant node.  The
  following additive identity records the exact size change without natural
  number subtraction.
\<close>

lemma fix_at_len_eq:
  assumes "valid_position p pos"
  shows "len_formula (fix_at pos b p) + len_formula (subterm_at p pos)
       = len_formula p + 1"
  using assms
proof (induction pos arbitrary: p)
  case Nil
  have "len_formula (fix_at [] b p) = 1"
    using true_const_len false_const_len by simp
  thus ?case by simp
next
  case (Cons i js)
  from Cons.prems obtain c fs where p_eq: "p = Conn c fs"
    by (cases p) auto
  have i_lt: "i < length fs" and vjs: "valid_position (fs ! i) js"
    using Cons.prems p_eq by auto
  have IH: "len_formula (fix_at js b (fs ! i))
            + len_formula (subterm_at (fs ! i) js)
          = len_formula (fs ! i) + 1"
    using Cons.IH[OF vjs] .
  have upd: "sum_list (map len_formula (fs[i := fix_at js b (fs ! i)]))
             + len_formula (fs ! i)
           = sum_list (map len_formula fs) + len_formula (fix_at js b (fs ! i))"
    using sum_list_len_update_eq[OF i_lt] .
  have lenp: "len_formula p = 1 + sum_list (map len_formula fs)"
    using p_eq by simp
  have "len_formula (fix_at (i # js) b p)
        + len_formula (subterm_at p (i # js))
      = 1 + sum_list (map len_formula (fs[i := fix_at js b (fs ! i)]))
        + len_formula (subterm_at (fs ! i) js)"
    using p_eq by simp
  also have "\<dots> = len_formula p + 1"
    using upd IH lenp by linarith
  finally show ?case .
qed

lemma fix_at_wf:
  assumes "formula_well_formed (alphabet F) p"
  shows "formula_well_formed (alphabet F) (fix_at pos b p)"
  using assms
proof (induction pos arbitrary: p)
  case Nil
  show ?case
    using true_const_wf false_const_wf by simp
next
  case (Cons i js)
  show ?case
  proof (cases p)
    case (Atom v)
    thus ?thesis by simp
  next
    case (Conn c fs)
    have len_fs: "length fs = arity (alphabet F) c"
     and child_wf: "\<forall> g \<in> set fs. formula_well_formed (alphabet F) g"
      using Cons.prems Conn by auto
    show ?thesis
    proof (cases "i < length fs")
      case False
      hence "fs[i := fix_at js b (fs ! i)] = fs"
        by (simp add: list_update_beyond)
      thus ?thesis using Conn Cons.prems by simp
    next
      case True
      have wf_child: "formula_well_formed (alphabet F) (fs ! i)"
        using child_wf True nth_mem by blast
      have wf_fixed: "formula_well_formed (alphabet F) (fix_at js b (fs ! i))"
        using Cons.IH[OF wf_child] .
      have upd_len: "length (fs[i := fix_at js b (fs ! i)]) = arity (alphabet F) c"
        using len_fs by simp
      have upd_wf: "\<forall> g \<in> set (fs[i := fix_at js b (fs ! i)]).
                      formula_well_formed (alphabet F) g"
      proof
        fix g assume g_in: "g \<in> set (fs[i := fix_at js b (fs ! i)])"
        have "g \<in> insert (fix_at js b (fs ! i)) (set fs)"
          using g_in set_update_subset_insert[of fs i "fix_at js b (fs ! i)"]
          by blast
        thus "formula_well_formed (alphabet F) g"
          using child_wf wf_fixed by blast
      qed
      show ?thesis using Conn upd_len upd_wf by simp
    qed
  qed
qed

lemma fix_at_sum_bound:
  assumes "valid_position p pos"
  shows "len_formula (subterm_at p pos) + len_formula (fix_at pos b p)
         \<le> len_formula p + 1"
  using assms
proof (induction pos arbitrary: p)
  case Nil
  have "len_formula (fix_at [] b p) = 1"
    using true_const_len false_const_len by simp
  thus ?case by simp
next
  case (Cons i js)
  from Cons.prems obtain c fs where p_eq: "p = Conn c fs"
    by (cases p) auto
  have i_lt: "i < length fs"
   and vjs: "valid_position (fs ! i) js"
    using Cons.prems p_eq by auto
  have IH: "len_formula (subterm_at (fs ! i) js)
            + len_formula (fix_at js b (fs ! i))
          \<le> len_formula (fs ! i) + 1"
    using Cons.IH[OF vjs] .
  have eq: "sum_list (map len_formula (fs[i := fix_at js b (fs ! i)]))
            + len_formula (fs ! i)
          = sum_list (map len_formula fs) + len_formula (fix_at js b (fs ! i))"
    using sum_list_len_update_eq[OF i_lt] .
  have p_len: "len_formula p = 1 + sum_list (map len_formula fs)"
    using p_eq by simp
  have "len_formula (subterm_at p (i # js)) + len_formula (fix_at (i # js) b p)
      = len_formula (subterm_at (fs ! i) js)
        + (1 + sum_list (map len_formula (fs[i := fix_at js b (fs ! i)])))"
    using p_eq by simp
  also have "\<dots> \<le> len_formula p + 1"
    using IH eq p_len by linarith
  finally show ?case .
qed

text \<open>
  The selected subformula is assigned a witnessing position, so later
  constructions operate on a specific occurrence of that subformula.
\<close>

definition spiras_sel_position :: "'c formula \<Rightarrow> nat list" where
  "spiras_sel_position p =
     (SOME pos. valid_position p pos \<and> subterm_at p pos = spiras_sel p)"

function (domintros) spira_trans :: "'c formula \<Rightarrow> 'c formula" where
  "spira_trans (Atom v) = (Atom v)" |
  "spira_trans (Conn c []) = (Conn c [])" |
  "spira_trans (Conn c (f # fs)) =
     (let p = Conn c (f # fs); pos = spiras_sel_position p in
        if len_formula p < spira_threshold then p
        else balance (spira_trans (fix_at pos True p))
                     (spira_trans (fix_at pos False p))
                     (spira_trans (subterm_at p pos)))"
  by pat_completeness auto

lemma is_subformula_len_le:
  shows "is_subformula q p \<Longrightarrow> len_formula q \<le> len_formula p"
proof (induction p)
  case (Atom v)
  thus ?case by simp
next
  case (Conn c fs)
  from Conn.prems have "q = Conn c fs \<or> (\<exists> g \<in> set fs. is_subformula q g)"
    by simp
  thus ?case
  proof
    assume "q = Conn c fs"
    thus ?case by simp
  next
    assume "\<exists> g \<in> set fs. is_subformula q g"
    then obtain g where g_in: "g \<in> set fs" and g_sub: "is_subformula q g"
      by blast
    hence "len_formula q \<le> len_formula g" using Conn.IH by simp
    moreover have "len_formula g \<le> sum_list (map len_formula fs)"
      using g_in by (induction fs) auto
    ultimately show ?case by simp
  qed
qed

lemma is_subformula_in_child_len_lt:
  assumes "g \<in> set fs"
      and "is_subformula q g"
    shows "len_formula q < len_formula (Conn c fs)"
proof -
  have "len_formula q \<le> len_formula g" using assms(2) is_subformula_len_le by simp
  also have "len_formula g \<le> sum_list (map len_formula fs)"
    using assms(1) by (induction fs) auto
  also have "sum_list (map len_formula fs) < len_formula (Conn c fs)" by simp
  finally show ?thesis .
qed

text \<open>
  The following position lemmas describe path decomposition, fixing a node
  below an ancestor, and commuting fixes at disjoint positions.  They supply
  the structural facts used in the rebalancing proof of Lemma 5.1.
\<close>

lemma subterm_at_atom:
  "subterm_at (Atom v) rp = Atom v"
  by (cases rp) simp_all

lemma subterm_at_append:
  "subterm_at p (qp @ rp) = subterm_at (subterm_at p qp) rp"
proof (induction qp arbitrary: p)
  case Nil
  show ?case by simp
next
  case (Cons i qp')
  show ?case
  proof (cases p)
    case (Atom v)
    thus ?thesis by (simp add: subterm_at_atom)
  next
    case (Conn c0 fs)
    thus ?thesis using Cons.IH by simp
  qed
qed

lemma valid_position_append:
  "valid_position p (qp @ rp)
   \<longleftrightarrow> valid_position p qp \<and> valid_position (subterm_at p qp) rp"
proof (induction qp arbitrary: p)
  case Nil
  show ?case by simp
next
  case (Cons i qp')
  show ?case
  proof (cases p)
    case (Atom v)
    thus ?thesis by simp
  next
    case (Conn c0 fs)
    thus ?thesis using Cons.IH by auto
  qed
qed

lemma valid_position_imp_is_subformula:
  "valid_position p pos \<Longrightarrow> is_subformula (subterm_at p pos) p"
proof (induction pos arbitrary: p)
  case Nil
  show ?case by (cases p) simp_all
next
  case (Cons i pos')
  from Cons.prems obtain c0 fs where p_eq: "p = Conn c0 fs"
    by (cases p) auto
  have i_lt: "i < length fs" and vp: "valid_position (fs ! i) pos'"
    using Cons.prems p_eq by auto
  have child_sub: "is_subformula (subterm_at (fs ! i) pos') (fs ! i)"
    using Cons.IH[OF vp] .
  have "\<exists> g \<in> set fs. is_subformula (subterm_at (fs ! i) pos') g"
    using child_sub i_lt nth_mem by blast
  thus ?case using p_eq by simp
qed

lemma subterm_at_wf:
  assumes "formula_well_formed a p"
      and "valid_position p pos"
    shows "formula_well_formed a (subterm_at p pos)"
  using subformula_wf[OF assms(1) valid_position_imp_is_subformula[OF assms(2)]] .

lemma subterm_at_len_le:
  assumes "valid_position p pos"
  shows "len_formula (subterm_at p pos) \<le> len_formula p"
  using is_subformula_len_le[OF valid_position_imp_is_subformula[OF assms]] .

lemma subterm_at_len_lt:
  assumes "valid_position p pos"
      and "pos \<noteq> []"
    shows "len_formula (subterm_at p pos) < len_formula p"
proof -
  obtain i pos' where pos_eq: "pos = i # pos'"
    using assms(2) by (cases pos) auto
  obtain c0 fs where p_eq: "p = Conn c0 fs"
    using assms(1) pos_eq by (cases p) auto
  have i_lt: "i < length fs" and vp: "valid_position (fs ! i) pos'"
    using assms(1) pos_eq p_eq by auto
  have child_sub: "is_subformula (subterm_at (fs ! i) pos') (fs ! i)"
    using valid_position_imp_is_subformula[OF vp] .
  have "subterm_at p pos = subterm_at (fs ! i) pos'"
    using pos_eq p_eq by simp
  moreover have "len_formula (subterm_at (fs ! i) pos') < len_formula (Conn c0 fs)"
    using is_subformula_in_child_len_lt[OF nth_mem[OF i_lt] child_sub] .
  ultimately show ?thesis using p_eq by simp
qed

text \<open>
  Fixing an ancestor overrides any previous fix at one of its descendants.
  Positions make this statement precise even when identical subformulas occur
  more than once.
\<close>

lemma fix_at_ancestor_overrides:
  "fix_at qp c (fix_at (qp @ rp) b p) = fix_at qp c p"
proof (induction qp arbitrary: p)
  case Nil
  show ?case by simp
next
  case (Cons i qp')
  show ?case
  proof (cases p)
    case (Atom v)
    thus ?thesis by simp
  next
    case (Conn c0 fs)
    show ?thesis
    proof (cases "i < length fs")
      case True
      have "fix_at (i # qp') c (fix_at ((i # qp') @ rp) b (Conn c0 fs))
          = Conn c0 (fs[i := fix_at qp' c (fix_at (qp' @ rp) b (fs ! i))])"
        using True by simp
      also have "\<dots> = Conn c0 (fs[i := fix_at qp' c (fs ! i)])"
        using Cons.IH by simp
      finally show ?thesis using Conn by simp
    next
      case False
      thus ?thesis using Conn by (simp add: list_update_beyond)
    qed
  qed
qed

text \<open>
  Viewed from an ancestor, fixing a descendant is the same as fixing the
  corresponding position inside the ancestor's subtree.
\<close>

lemma subterm_at_fix_at_prefix:
  "valid_position p qp
   \<Longrightarrow> subterm_at (fix_at (qp @ rp) b p) qp = fix_at rp b (subterm_at p qp)"
proof (induction qp arbitrary: p)
  case Nil
  show ?case by simp
next
  case (Cons i qp')
  from Cons.prems obtain c0 fs where p_eq: "p = Conn c0 fs"
    by (cases p) auto
  have i_lt: "i < length fs" and vq: "valid_position (fs ! i) qp'"
    using Cons.prems p_eq by auto
  have "subterm_at (fix_at ((i # qp') @ rp) b (Conn c0 fs)) (i # qp')
      = subterm_at (fix_at (qp' @ rp) b (fs ! i)) qp'"
    using i_lt by simp
  also have "\<dots> = fix_at rp b (subterm_at (fs ! i) qp')"
    using Cons.IH[OF vq] .
  finally show ?case using p_eq by simp
qed

text \<open>
  Two positions are disjoint when neither is a prefix of the other.  Their
  selected subtrees then do not overlap.
\<close>

fun positions_disjoint :: "nat list \<Rightarrow> nat list \<Rightarrow> bool" where
  "positions_disjoint [] rp = False" |
  "positions_disjoint qp [] = False" |
  "positions_disjoint (i # qp') (j # rp') =
     (if i = j then positions_disjoint qp' rp' else True)"

lemma positions_disjoint_sym:
  "positions_disjoint qp rp = positions_disjoint rp qp"
proof (induction qp arbitrary: rp)
  case Nil
  show ?case by (cases rp) simp_all
next
  case (Cons i qp')
  show ?case by (cases rp) (simp_all add: Cons.IH)
qed

lemma position_trichotomy:
  "qp = rp
   \<or> (\<exists> s. s \<noteq> [] \<and> rp = qp @ s)
   \<or> (\<exists> s. s \<noteq> [] \<and> qp = rp @ s)
   \<or> positions_disjoint qp rp"
proof (induction qp arbitrary: rp)
  case Nil
  show ?case
  proof (cases rp)
    case Nil
    thus ?thesis by simp
  next
    case (Cons j rp')
    have "rp \<noteq> [] \<and> rp = [] @ rp" using Cons by simp
    thus ?thesis by blast
  qed
next
  case (Cons i qp')
  show ?case
  proof (cases rp)
    case Nil
    have "i # qp' \<noteq> [] \<and> i # qp' = [] @ (i # qp')" by simp
    thus ?thesis using Nil by blast
  next
    case (Cons j rp')
    show ?thesis
    proof (cases "i = j")
      case False
      have "positions_disjoint (i # qp') rp" using Cons False by simp
      thus ?thesis by blast
    next
      case True
      from Cons.IH[of rp'] consider
          (a) "qp' = rp'"
        | (b) "\<exists> s. s \<noteq> [] \<and> rp' = qp' @ s"
        | (c) "\<exists> s. s \<noteq> [] \<and> qp' = rp' @ s"
        | (d) "positions_disjoint qp' rp'"
        by blast
      thus ?thesis
      proof cases
        case a
        thus ?thesis using Cons True by simp
      next
        case b
        then obtain s where "s \<noteq> [] \<and> rp' = qp' @ s" by blast
        hence "rp = (i # qp') @ s \<and> s \<noteq> []" using Cons True by simp
        thus ?thesis by blast
      next
        case c
        then obtain s where "s \<noteq> [] \<and> qp' = rp' @ s" by blast
        hence "i # qp' = rp @ s \<and> s \<noteq> []" using Cons True by simp
        thus ?thesis by blast
      next
        case d
        have "positions_disjoint (i # qp') rp" using Cons True d by simp
        thus ?thesis by blast
      qed
    qed
  qed
qed

lemma fix_at_commute_disjoint:
  "positions_disjoint qp rp
   \<Longrightarrow> fix_at qp c (fix_at rp b p) = fix_at rp b (fix_at qp c p)"
proof (induction qp arbitrary: rp p)
  case Nil
  thus ?case by simp
next
  case (Cons i qp')
  obtain j rp' where rp_eq: "rp = j # rp'"
    using Cons.prems by (cases rp) auto
  show ?case
  proof (cases p)
    case (Atom v)
    thus ?thesis using rp_eq by simp
  next
    case (Conn c0 fs)
    show ?thesis
    proof (cases "i = j")
      case neq: False
      have "fix_at (i # qp') c (fix_at rp b (Conn c0 fs))
          = Conn c0 ((fs[j := fix_at rp' b (fs ! j)])[i := fix_at qp' c (fs ! i)])"
        using rp_eq neq by simp
      also have "\<dots> = Conn c0 ((fs[i := fix_at qp' c (fs ! i)])[j := fix_at rp' b (fs ! j)])"
        using list_update_swap[of j i fs "fix_at rp' b (fs ! j)" "fix_at qp' c (fs ! i)"]
              neq by simp
      also have "\<dots> = fix_at rp b (fix_at (i # qp') c (Conn c0 fs))"
        using rp_eq neq by simp
      finally show ?thesis using Conn by simp
    next
      case eq: True
      from Cons.prems rp_eq eq have disj': "positions_disjoint qp' rp'" by simp
      show ?thesis
      proof (cases "i < length fs")
        case True
        have "fix_at (i # qp') c (fix_at rp b (Conn c0 fs))
            = Conn c0 (fs[i := fix_at qp' c (fix_at rp' b (fs ! i))])"
          using rp_eq eq True by simp
        also have "\<dots> = Conn c0 (fs[i := fix_at rp' b (fix_at qp' c (fs ! i))])"
          using Cons.IH[OF disj'] by simp
        also have "\<dots> = fix_at rp b (fix_at (i # qp') c (Conn c0 fs))"
          using rp_eq eq True by simp
        finally show ?thesis using Conn by simp
      next
        case False
        thus ?thesis using rp_eq eq Conn by (simp add: list_update_beyond)
      qed
    qed
  qed
qed

lemma subterm_at_fix_at_disjoint:
  "positions_disjoint qp rp
   \<Longrightarrow> subterm_at (fix_at rp b p) qp = subterm_at p qp"
proof (induction qp arbitrary: rp p)
  case Nil
  thus ?case by simp
next
  case (Cons i qp')
  obtain j rp' where rp_eq: "rp = j # rp'"
    using Cons.prems by (cases rp) auto
  show ?case
  proof (cases p)
    case (Atom v)
    thus ?thesis using rp_eq by simp
  next
    case (Conn c0 fs)
    show ?thesis
    proof (cases "i = j")
      case neq: False
      have "subterm_at (fix_at rp b (Conn c0 fs)) (i # qp') = subterm_at (fs ! i) qp'"
        using rp_eq neq by simp
      thus ?thesis using Conn by simp
    next
      case eq: True
      from Cons.prems rp_eq eq have disj': "positions_disjoint qp' rp'" by simp
      show ?thesis
      proof (cases "i < length fs")
        case True
        have "subterm_at (fix_at rp b (Conn c0 fs)) (i # qp')
            = subterm_at (fix_at rp' b (fs ! i)) qp'"
          using rp_eq eq True by simp
        also have "\<dots> = subterm_at (fs ! i) qp'"
          using Cons.IH[OF disj'] .
        finally show ?thesis using Conn by simp
      next
        case False
        thus ?thesis using rp_eq eq Conn by (simp add: list_update_beyond)
      qed
    qed
  qed
qed

text \<open>Fixing a descendant preserves the position of its ancestor.\<close>
lemma valid_position_fix_at_prefix:
  "valid_position p (qp @ rp) \<Longrightarrow> valid_position (fix_at (qp @ rp) b p) qp"
proof (induction qp arbitrary: p)
  case Nil
  show ?case by simp
next
  case (Cons i qp')
  from Cons.prems obtain c0 fs where p_eq: "p = Conn c0 fs"
    by (cases p) auto
  have i_lt: "i < length fs" and vrest: "valid_position (fs ! i) (qp' @ rp)"
    using Cons.prems p_eq by auto
  have "valid_position (fix_at (qp' @ rp) b (fs ! i)) qp'"
    using Cons.IH[OF vrest] .
  thus ?case using p_eq i_lt by simp
qed

text \<open>Fixing a disjoint position preserves the other position.\<close>
lemma valid_position_fix_at_disjoint:
  "positions_disjoint qp rp \<Longrightarrow> valid_position p qp
   \<Longrightarrow> valid_position (fix_at rp b p) qp"
proof (induction qp arbitrary: rp p)
  case Nil
  thus ?case by simp
next
  case (Cons i qp')
  obtain j rp' where rp_eq: "rp = j # rp'"
    using Cons.prems(1) by (cases rp) auto
  from Cons.prems(2) obtain c0 fs where p_eq: "p = Conn c0 fs"
    by (cases p) auto
  have i_lt: "i < length fs" and vi: "valid_position (fs ! i) qp'"
    using Cons.prems(2) p_eq by auto
  show ?case
  proof (cases "i = j")
    case neq: False
    have "valid_position (fix_at rp b (Conn c0 fs)) (i # qp')
        = (i < length fs \<and> valid_position (fs ! i) qp')"
      using rp_eq neq by simp
    thus ?thesis using p_eq i_lt vi by simp
  next
    case eq: True
    from Cons.prems(1) rp_eq eq have disj': "positions_disjoint qp' rp'" by simp
    have ih: "valid_position (fix_at rp' b (fs ! i)) qp'"
      using Cons.IH[OF disj' vi] .
    have "valid_position (fix_at rp b (Conn c0 fs)) (i # qp')
        = (i < length fs \<and> valid_position (fix_at rp' b (fs ! i)) qp')"
      using rp_eq eq i_lt by simp
    thus ?thesis using p_eq i_lt ih by simp
  qed
qed

text \<open>Fixing a non-root position retains the outer connective and its
  children.\<close>
lemma fix_at_len_ge_2:
  assumes "valid_position p pos" and "pos \<noteq> []"
  shows "len_formula (fix_at pos b p) \<ge> 2"
proof -
  obtain i pos' where pos_eq: "pos = i # pos'"
    using assms(2) by (cases pos) auto
  obtain c0 fs where p_eq: "p = Conn c0 fs"
    using assms(1) pos_eq by (cases p) auto
  have i_lt: "i < length fs" using assms(1) pos_eq p_eq by auto
  have fix_eq: "fix_at pos b p = Conn c0 (fs[i := fix_at pos' b (fs ! i)])"
    using pos_eq p_eq by simp
  have "fs[i := fix_at pos' b (fs ! i)] \<noteq> []" using i_lt by auto
  then obtain g gs where g_eq: "fs[i := fix_at pos' b (fs ! i)] = g # gs"
    by (cases "fs[i := fix_at pos' b (fs ! i)]") auto
  have "len_formula (fix_at pos b p)
      = 1 + (len_formula g + sum_list (map len_formula gs))"
    using fix_eq g_eq by simp
  moreover have "len_formula g \<ge> 1" by (rule len_formula_positive)
  ultimately show ?thesis by simp
qed

lemma spiras_sel_pred_when_wf:
  assumes "formula_well_formed (alphabet F) p"
      and "len_formula p \<ge> 2"
    shows "is_subformula (spiras_sel p) p
         \<and> len_formula (spiras_sel p) < len_formula p"
proof -
  let ?k = "Max ((arity (alphabet F)) ` (UNIV :: 'c set))"
  show ?thesis
  proof (cases "?k > 1")
    case True
    let ?P = "\<lambda>q. is_subformula q p
              \<and> (?k + 1) * len_formula q + ?k \<ge> len_formula p
              \<and> (?k + 1) * len_formula q \<le> ?k * len_formula p"
    have ex: "\<exists> q. ?P q"
      using spiras_selection_gen[OF assms(1,2) refl True] by blast
    have sel_eq: "spiras_sel p = (SOME q. ?P q)"
      unfolding spiras_sel_def using True by (simp add: Let_def)
    hence "?P (spiras_sel p)" using someI_ex[OF ex] by simp
    hence sub: "is_subformula (spiras_sel p) p"
      and upper: "(?k + 1) * len_formula (spiras_sel p) \<le> ?k * len_formula p"
      by auto
    have "len_formula (spiras_sel p) < len_formula p"
    proof (rule ccontr)
      assume "\<not> len_formula (spiras_sel p) < len_formula p"
      hence le: "len_formula p \<le> len_formula (spiras_sel p)" by simp
      have "(?k + 1) * len_formula p \<le> (?k + 1) * len_formula (spiras_sel p)"
        using le by (rule mult_le_mono2)
      with upper have "(?k + 1) * len_formula p \<le> ?k * len_formula p" by linarith
      with assms(2) show False by (simp add: algebra_simps)
    qed
    thus ?thesis using sub by simp
  next
    case k_le: False
    show ?thesis
    proof (cases "?k = 1")
      case True
      let ?P = "\<lambda>q. is_subformula q p
                \<and> 3 * len_formula q \<ge> len_formula p
                \<and> 3 * len_formula q \<le> 2 * len_formula p"
      have ex: "\<exists> q. ?P q"
        using spiras_selection_one[OF assms(1,2) True] by blast
      have sel_eq: "spiras_sel p = (SOME q. ?P q)"
        unfolding spiras_sel_def using k_le by (simp add: Let_def)
      hence "?P (spiras_sel p)" using someI_ex[OF ex] by simp
      hence sub: "is_subformula (spiras_sel p) p"
       and upper: "3 * len_formula (spiras_sel p) \<le> 2 * len_formula p"
        by auto
      have "len_formula (spiras_sel p) < len_formula p"
        using upper assms(2) by linarith
      thus ?thesis using sub by simp
    next
      case False
      with k_le have k0: "?k = 0" by simp
      \<comment> \<open>If max arity is 0, all connectives are nullary, so well-formed
          formulas have length at most 1, contradicting assms(2).\<close>
      have alphabet_finite: "finite (UNIV :: 'c set)"
        by (meson frege_balancing_axioms frege_balancing_def
                  frege_system.finite_alphabet)
      have all_arity_zero: "\<forall> c. arity (alphabet F) c = 0"
      proof
        fix c
        have x_in: "arity (alphabet F) c
                  \<in> (arity (alphabet F)) ` (UNIV :: 'c set)" by simp
        have fin_im: "finite ((arity (alphabet F)) ` (UNIV :: 'c set))"
          using alphabet_finite by simp
        from fin_im x_in
        have "arity (alphabet F) c \<le> ?k" by (rule Max_ge)
        thus "arity (alphabet F) c = 0" using k0 by simp
      qed
      have "len_formula p \<le> 1"
        using assms(1) all_arity_zero
      proof (induction p)
        case (Atom v)
        show ?case by simp
      next
        case (Conn c fs)
        from Conn.prems(1) have "length fs = arity (alphabet F) c"
                            and "\<forall> g \<in> set fs. formula_well_formed (alphabet F) g"
          by auto
        with all_arity_zero have "fs = []" by simp
        thus ?case by simp
      qed
      with assms(2) show ?thesis by simp
    qed
  qed
qed

lemma spiras_sel_len_ge_2_when_wf:
  assumes "formula_well_formed (alphabet F) p"
      and "len_formula p \<ge> spira_threshold"
    shows "len_formula (spiras_sel p) \<ge> 2"
proof -
  let ?k = "Max ((arity (alphabet F)) ` (UNIV :: 'c set))"
  have p_ge_2: "len_formula p \<ge> 2"
    using assms(2) unfolding spira_threshold_def by simp
  show ?thesis
  proof (cases "?k > 1")
    case True
    let ?P = "\<lambda>q. is_subformula q p
              \<and> (?k + 1) * len_formula q + ?k \<ge> len_formula p
              \<and> (?k + 1) * len_formula q \<le> ?k * len_formula p"
    have ex: "\<exists> q. ?P q"
      using spiras_selection_gen[OF assms(1) p_ge_2 refl True] by blast
    have "spiras_sel p = (SOME q. ?P q)"
      unfolding spiras_sel_def using True by (simp add: Let_def)
    hence pred: "?P (spiras_sel p)" using someI_ex[OF ex] by simp
    hence lower: "(?k + 1) * len_formula (spiras_sel p) + ?k \<ge> len_formula p"
      by auto
    have "len_formula p \<ge> 2 * ?k + 2"
      using assms(2) unfolding spira_threshold_def by simp
    with lower have key: "(?k + 1) * len_formula (spiras_sel p) \<ge> ?k + 2"
      by linarith
    show ?thesis
    proof (rule ccontr)
      assume "\<not> len_formula (spiras_sel p) \<ge> 2"
      hence le1: "len_formula (spiras_sel p) \<le> 1" by simp
      have "(?k + 1) * len_formula (spiras_sel p) \<le> (?k + 1) * 1"
        using le1 by (rule mult_le_mono2)
      hence "(?k + 1) * len_formula (spiras_sel p) \<le> ?k + 1" by simp
      with key show False by linarith
    qed
  next
    case k_le: False
    show ?thesis
    proof (cases "?k = 1")
      case True
      let ?P = "\<lambda>q. is_subformula q p
                \<and> 3 * len_formula q \<ge> len_formula p
                \<and> 3 * len_formula q \<le> 2 * len_formula p"
      have ex: "\<exists> q. ?P q"
        using spiras_selection_one[OF assms(1) p_ge_2 True] by blast
      have "spiras_sel p = (SOME q. ?P q)"
        unfolding spiras_sel_def using k_le by (simp add: Let_def)
      hence pred: "?P (spiras_sel p)" using someI_ex[OF ex] by simp
      hence lower: "3 * len_formula (spiras_sel p) \<ge> len_formula p"
        by auto
      have "len_formula p \<ge> 4"
        using assms(2) True unfolding spira_threshold_def by simp
      with lower have key: "3 * len_formula (spiras_sel p) \<ge> 4" by linarith
      show ?thesis
      proof (rule ccontr)
        assume "\<not> len_formula (spiras_sel p) \<ge> 2"
        hence "len_formula (spiras_sel p) \<le> 1" by simp
        hence "3 * len_formula (spiras_sel p) \<le> 3" by simp
        with key show False by linarith
      qed
    next
      case False
      with k_le have k0: "?k = 0" by simp
      have alphabet_finite: "finite (UNIV :: 'c set)"
        by (meson frege_balancing_axioms frege_balancing_def
                  frege_system.finite_alphabet)
      have all_arity_zero: "\<forall> c. arity (alphabet F) c = 0"
      proof
        fix c
        have x_in: "arity (alphabet F) c
                  \<in> (arity (alphabet F)) ` (UNIV :: 'c set)" by simp
        have fin_im: "finite ((arity (alphabet F)) ` (UNIV :: 'c set))"
          using alphabet_finite by simp
        from fin_im x_in
        have "arity (alphabet F) c \<le> ?k" by (rule Max_ge)
        thus "arity (alphabet F) c = 0" using k0 by simp
      qed
      have "len_formula p \<le> 1"
        using assms(1) all_arity_zero
      proof (induction p)
        case (Atom v)
        show ?case by simp
      next
        case (Conn c fs)
        from Conn.prems(1) have "length fs = arity (alphabet F) c" by simp
        with all_arity_zero have "fs = []" by simp
        thus ?case by simp
      qed
      with p_ge_2 show ?thesis by simp
    qed
  qed
qed

lemma spiras_sel_position_spec:
  assumes "formula_well_formed (alphabet F) p"
      and "len_formula p \<ge> 2"
    shows "valid_position p (spiras_sel_position p)
         \<and> subterm_at p (spiras_sel_position p) = spiras_sel p"
proof -
  have "is_subformula (spiras_sel p) p"
    using spiras_sel_pred_when_wf[OF assms] by simp
  hence "\<exists> pos. valid_position p pos \<and> subterm_at p pos = spiras_sel p"
    by (rule is_subformula_imp_position)
  thus ?thesis
    unfolding spiras_sel_position_def by (rule someI_ex)
qed

lemma spira_trans_dom_and_eval:
  assumes "formula_well_formed (alphabet F) f"
  shows "spira_trans_dom f
       \<and> (\<forall> val. eval (alphabet F) val f = eval (alphabet F) val (spira_trans f))"
  using assms
proof (induction "len_formula f" arbitrary: f rule: less_induct)
  case less
  show ?case
  proof (cases f)
    case (Atom v)
    have dom_unfolded: "spira_trans_dom (Atom v)"
      by (rule spira_trans.domintros)
    hence dom: "spira_trans_dom f" using Atom by simp
    moreover have "spira_trans f = f"
      using dom Atom by (simp add: spira_trans.psimps(1))
    ultimately show ?thesis by simp
  next
    case (Conn c fs)
    show ?thesis
    proof (cases fs)
      case Nil
      have dom_unfolded: "spira_trans_dom (Conn c [])"
        by (rule spira_trans.domintros)
      hence dom: "spira_trans_dom f" using Conn Nil by simp
      moreover have "spira_trans f = f"
        using dom Conn Nil by (simp add: spira_trans.psimps(2))
      ultimately show ?thesis by simp
    next
      case (Cons f1 fs1)
      let ?p = f
      let ?pos = "spiras_sel_position ?p"
      let ?q = "subterm_at ?p ?pos"
      let ?ev = "\<lambda>val. eval (alphabet F) val"
      show ?thesis
      proof (cases "len_formula ?p < spira_threshold")
        case small: True
        \<comment> \<open>Below threshold: function returns \<open>p\<close> (identity).\<close>
        have dom_unfolded: "spira_trans_dom (Conn c (f1 # fs1))"
          apply (rule spira_trans.domintros)
          using small Conn Cons apply simp_all
          done
        hence dom: "spira_trans_dom ?p" using Conn Cons by simp
        have eq: "spira_trans ?p = ?p"
        proof -
          have "spira_trans (Conn c (f1 # fs1)) =
                (let p = Conn c (f1 # fs1); pos = spiras_sel_position p in
                  if len_formula p < spira_threshold then p
                  else balance (spira_trans (fix_at pos True p))
                               (spira_trans (fix_at pos False p))
                               (spira_trans (subterm_at p pos)))"
            using dom Conn Cons by (simp add: spira_trans.psimps(3))
          thus ?thesis using small Conn Cons by (simp add: Let_def)
        qed
        thus ?thesis using dom by simp
      next
        case big: False
        \<comment> \<open>At/above threshold: recursion fires; spiras_sel gives a strict
            subformula of length \<open>\<ge> 2\<close>, and spiras_sel_position a valid
            path to that one node.\<close>
        have wf_p: "formula_well_formed (alphabet F) ?p" using less.prems .
        have p_ge_threshold: "len_formula ?p \<ge> spira_threshold" using big by simp
        have p_ge_2: "len_formula ?p \<ge> 2"
          using p_ge_threshold spira_threshold_def by simp
        have pos_spec: "valid_position ?p ?pos \<and> subterm_at ?p ?pos = spiras_sel ?p"
          using spiras_sel_position_spec[OF wf_p p_ge_2] .
        have pos_valid: "valid_position ?p ?pos" using pos_spec by simp
        have q_eq: "?q = spiras_sel ?p" using pos_spec by simp
        from spiras_sel_pred_when_wf[OF wf_p p_ge_2]
        have q_sub: "is_subformula ?q ?p"
         and q_lt: "len_formula ?q < len_formula ?p" using q_eq by auto
        have q_ge_2: "len_formula ?q \<ge> 2"
          using spiras_sel_len_ge_2_when_wf[OF wf_p p_ge_threshold] q_eq by simp
        have wf_q: "formula_well_formed (alphabet F) ?q"
          using wf_p q_sub subformula_wf by blast
        have wf_T: "formula_well_formed (alphabet F) (fix_at ?pos True ?p)"
          using wf_p by (rule fix_at_wf)
        have wf_F: "formula_well_formed (alphabet F) (fix_at ?pos False ?p)"
          using wf_p by (rule fix_at_wf)
        have len_T: "len_formula (fix_at ?pos True ?p) < len_formula ?p"
          using fix_at_len_strict[OF pos_valid q_ge_2] .
        have len_F: "len_formula (fix_at ?pos False ?p) < len_formula ?p"
          using fix_at_len_strict[OF pos_valid q_ge_2] .
        from less.hyps[OF q_lt wf_q]
        have dom_q: "spira_trans_dom ?q"
         and ih_q: "\<forall> val. ?ev val ?q = ?ev val (spira_trans ?q)" by auto
        from less.hyps[OF len_T wf_T]
        have dom_T: "spira_trans_dom (fix_at ?pos True ?p)"
         and ih_T: "\<forall> val. ?ev val (fix_at ?pos True ?p)
                          = ?ev val (spira_trans (fix_at ?pos True ?p))" by auto
        from less.hyps[OF len_F wf_F]
        have dom_F: "spira_trans_dom (fix_at ?pos False ?p)"
         and ih_F: "\<forall> val. ?ev val (fix_at ?pos False ?p)
                          = ?ev val (spira_trans (fix_at ?pos False ?p))" by auto
        have dom_unfolded: "spira_trans_dom (Conn c (f1 # fs1))"
          apply (rule spira_trans.domintros)
          using Conn Cons dom_q dom_T dom_F big apply simp_all
          done
        hence dom: "spira_trans_dom ?p" using Conn Cons by simp
        have st_eq: "spira_trans ?p = balance (spira_trans (fix_at ?pos True ?p))
                                              (spira_trans (fix_at ?pos False ?p))
                                              (spira_trans ?q)"
        proof -
          have psimp: "spira_trans (Conn c (f1 # fs1)) =
                       (let p = Conn c (f1 # fs1); pos = spiras_sel_position p in
                         if len_formula p < spira_threshold then p
                         else balance (spira_trans (fix_at pos True p))
                                      (spira_trans (fix_at pos False p))
                                      (spira_trans (subterm_at p pos)))"
            using dom Conn Cons by (simp add: spira_trans.psimps(3))
          thus ?thesis using big Conn Cons by (simp add: Let_def)
        qed
        have eval_eq: "\<forall> val. ?ev val ?p = ?ev val (spira_trans ?p)"
        proof
          fix val
          have "?ev val (spira_trans ?p)
              = ?ev val (balance (spira_trans (fix_at ?pos True ?p))
                                 (spira_trans (fix_at ?pos False ?p))
                                 (spira_trans ?q))"
            using st_eq by simp
          also have "\<dots> = (if ?ev val (spira_trans ?q)
                           then ?ev val (spira_trans (fix_at ?pos True ?p))
                           else ?ev val (spira_trans (fix_at ?pos False ?p)))"
            by (rule balance_eval)
          also have "\<dots> = (if ?ev val ?q
                           then ?ev val (fix_at ?pos True ?p)
                           else ?ev val (fix_at ?pos False ?p))"
            using ih_T ih_F ih_q by simp
          also have "\<dots> = ?ev val ?p"
            using fix_at_eval[OF pos_valid, symmetric] by simp
          finally show "?ev val ?p = ?ev val (spira_trans ?p)" by simp
        qed
        from dom eval_eq show ?thesis by simp
      qed
    qed
  qed
qed

subsubsection \<open>Logarithmic depth\<close>

text \<open>
  Above the fixed size threshold, every recursive input is smaller by a fixed
  factor. Consequently, each branch of the construction has only logarithmically
  many recursive levels. Since the conditional template adds a fixed amount of
  depth at each level, the resulting formula has logarithmic depth.
\<close>


lemma balance_depth_bound:
  shows "depth_formula (balance x y z)
       \<le> depth_formula custom_balancing
         + Max (insert 1 {depth_formula x, depth_formula y, depth_formula z})"
proof -
  let ?sub = "\<lambda>v. if v = ''x'' then x
                  else if v = ''y'' then y
                  else if v = ''z'' then z
                  else Atom v"
  let ?vs = "{''x'', ''y'', ''z''}"
  have wf_sub: "\<forall> v. v \<notin> ?vs \<longrightarrow> ?sub v = Atom v" by auto
  have fin_vs: "finite ?vs" by simp
  have unfold: "balance x y z = sub_formula ?sub custom_balancing"
    by (simp add: Let_def)
  have A: "depth_formula (sub_formula ?sub custom_balancing)
      \<le> depth_formula custom_balancing + depth_sub ?vs ?sub"
    by (rule sub_formula_depth_bound[OF fin_vs wf_sub])
  have B: "depth_sub ?vs ?sub
         = Max (insert 1 {depth_formula x, depth_formula y, depth_formula z})"
    by (simp add: depth_sub_def)
  show ?thesis unfolding unfold B[symmetric] by (rule A)
qed

lemma depth_le_len:
  shows "depth_formula f \<le> len_formula f"
proof (induction f)
  case (Atom v) show ?case by simp
next
  case (Conn c fs)
  show ?case
  proof (cases fs)
    case Nil show ?thesis using Nil by simp
  next
    case (Cons g gs)
    have fin: "finite (set (map depth_formula fs))" by simp
    have ne: "set (map depth_formula fs) \<noteq> {}" using Cons by simp
    have "Max (set (map depth_formula fs)) \<in> set (map depth_formula fs)"
      using fin ne Max_in by blast
    then obtain h where h_in: "h \<in> set fs"
                    and h_eq: "depth_formula h = Max (set (map depth_formula fs))"
      by auto
    have "depth_formula h \<le> len_formula h" using Conn.IH h_in by simp
    moreover have "len_formula h \<le> sum_list (map len_formula fs)"
      using h_in by (induction fs) auto
    ultimately have "Max (set (map depth_formula fs))
                   \<le> sum_list (map len_formula fs)"
      using h_eq by simp
    thus ?thesis using Cons by simp
  qed
qed

lemma recursive_arg_len_bound_gen:
  fixes p :: "'c formula" and b :: bool
  assumes "formula_well_formed (alphabet F) p"
      and "len_formula p \<ge> spira_threshold"
      and "k = Max ((arity (alphabet F)) ` (UNIV :: 'c set))"
      and "k > 1"
    shows "(k + 1) * len_formula (spiras_sel p) \<le> k * len_formula p
         \<and> (k + 1) * len_formula (fix_at (spiras_sel_position p) b p)
            \<le> k * len_formula p + 2 * k + 1"
proof -
  let ?q = "spiras_sel p"
  let ?pos = "spiras_sel_position p"
  have p_ge_2: "len_formula p \<ge> 2"
    using assms(2) unfolding spira_threshold_def by simp
  have p_ge_k: "len_formula p \<ge> k"
    using assms(2,3) unfolding spira_threshold_def by simp
  have pos_valid: "valid_position p ?pos"
    using spiras_sel_position_spec[OF assms(1) p_ge_2] by simp
  have q_eq: "subterm_at p ?pos = ?q"
    using spiras_sel_position_spec[OF assms(1) p_ge_2] by simp
  let ?P = "\<lambda>q. is_subformula q p
            \<and> (k + 1) * len_formula q + k \<ge> len_formula p
            \<and> (k + 1) * len_formula q \<le> k * len_formula p"
  have ex: "\<exists> q. ?P q"
    using spiras_selection_gen[OF assms(1) p_ge_2 assms(3,4)] by blast
  have "spiras_sel p = (SOME q. ?P q)"
    unfolding spiras_sel_def using assms(3,4) by (simp add: Let_def)
  hence pred: "?P ?q" using someI_ex[OF ex] by simp
  hence sub: "is_subformula ?q p"
    and lower: "(k + 1) * len_formula ?q + k \<ge> len_formula p"
    and upper: "(k + 1) * len_formula ?q \<le> k * len_formula p"
    by auto
  have q_le_p: "len_formula ?q \<le> len_formula p"
    using sub is_subformula_len_le by simp
  have fix_sum: "len_formula ?q + len_formula (fix_at ?pos b p)
              \<le> len_formula p + 1"
  proof -
    have "len_formula (subterm_at p ?pos) + len_formula (fix_at ?pos b p)
        \<le> len_formula p + 1"
      using fix_at_sum_bound[OF pos_valid] .
    thus ?thesis using q_eq by simp
  qed
  have lower_in_nat: "(k + 1) * len_formula ?q \<ge> len_formula p - k"
    using lower by simp
  have "(k + 1) * len_formula (fix_at ?pos b p)
      \<le> (k + 1) * (len_formula p + 1 - len_formula ?q)"
    using fix_sum by (intro mult_le_mono2) simp
  also have "(k + 1) * (len_formula p + 1 - len_formula ?q)
           = (k + 1) * (len_formula p + 1) - (k + 1) * len_formula ?q"
    using q_le_p by (simp add: diff_mult_distrib2)
  also have "\<dots> \<le> (k + 1) * (len_formula p + 1) - (len_formula p - k)"
    using lower_in_nat by simp
  also have "(k + 1) * (len_formula p + 1) - (len_formula p - k)
           = k * len_formula p + 2 * k + 1"
    using p_ge_k by (simp add: algebra_simps)
  finally have fix_bound: "(k + 1) * len_formula (fix_at ?pos b p)
                         \<le> k * len_formula p + 2 * k + 1" .
  show ?thesis using upper fix_bound by simp
qed

lemma recursive_arg_len_bound_one:
  fixes p :: "'c formula" and b :: bool
  assumes "formula_well_formed (alphabet F) p"
      and "len_formula p \<ge> spira_threshold"
      and "Max ((arity (alphabet F)) ` (UNIV :: 'c set)) = 1"
    shows "3 * len_formula (spiras_sel p) \<le> 2 * len_formula p
         \<and> 3 * len_formula (fix_at (spiras_sel_position p) b p)
            \<le> 2 * len_formula p + 3"
proof -
  let ?q = "spiras_sel p"
  let ?pos = "spiras_sel_position p"
  have p_ge_2: "len_formula p \<ge> 2"
    using assms(2) unfolding spira_threshold_def by simp
  have pos_valid: "valid_position p ?pos"
    using spiras_sel_position_spec[OF assms(1) p_ge_2] by simp
  have q_eq: "subterm_at p ?pos = ?q"
    using spiras_sel_position_spec[OF assms(1) p_ge_2] by simp
  let ?P = "\<lambda>q. is_subformula q p
            \<and> 3 * len_formula q \<ge> len_formula p
            \<and> 3 * len_formula q \<le> 2 * len_formula p"
  have ex: "\<exists> q. ?P q"
    using spiras_selection_one[OF assms(1) p_ge_2 assms(3)] by blast
  have "spiras_sel p = (SOME q. ?P q)"
    unfolding spiras_sel_def using assms(3) by (simp add: Let_def)
  hence pred: "?P ?q" using someI_ex[OF ex] by simp
  hence sub: "is_subformula ?q p"
    and lower: "3 * len_formula ?q \<ge> len_formula p"
    and upper: "3 * len_formula ?q \<le> 2 * len_formula p"
    by auto
  have q_le_p: "len_formula ?q \<le> len_formula p"
    using sub is_subformula_len_le by simp
  have fix_sum: "len_formula ?q + len_formula (fix_at ?pos b p)
              \<le> len_formula p + 1"
  proof -
    have "len_formula (subterm_at p ?pos) + len_formula (fix_at ?pos b p)
        \<le> len_formula p + 1"
      using fix_at_sum_bound[OF pos_valid] .
    thus ?thesis using q_eq by simp
  qed
  have "3 * len_formula (fix_at ?pos b p)
      \<le> 3 * (len_formula p + 1 - len_formula ?q)"
    using fix_sum by (intro mult_le_mono2) simp
  also have "3 * (len_formula p + 1 - len_formula ?q)
           = 3 * (len_formula p + 1) - 3 * len_formula ?q"
    using q_le_p by (simp add: diff_mult_distrib2)
  also have "\<dots> \<le> 3 * (len_formula p + 1) - len_formula p"
    using lower by simp
  also have "3 * (len_formula p + 1) - len_formula p = 2 * len_formula p + 3"
    by (simp add: algebra_simps)
  finally have fix_bound: "3 * len_formula (fix_at ?pos b p)
                         \<le> 2 * len_formula p + 3" .
  show ?thesis using upper fix_bound by simp
qed

lemma wf_arity_zero_imp_len_1:
  assumes "formula_well_formed (alphabet F) p"
      and "Max ((arity (alphabet F)) ` (UNIV :: 'c set)) = 0"
    shows "len_formula p = 1"
proof -
  have alphabet_finite: "finite (UNIV :: 'c set)"
    by (meson frege_balancing_axioms frege_balancing_def
              frege_system.finite_alphabet)
  have all_zero: "\<forall> c. arity (alphabet F) c = 0"
  proof
    fix c
    have x_in: "arity (alphabet F) c
              \<in> (arity (alphabet F)) ` (UNIV :: 'c set)" by simp
    have fin_im: "finite ((arity (alphabet F)) ` (UNIV :: 'c set))"
      using alphabet_finite by simp
    from fin_im x_in
    have "arity (alphabet F) c
        \<le> Max ((arity (alphabet F)) ` (UNIV :: 'c set))" by (rule Max_ge)
    thus "arity (alphabet F) c = 0" using assms(2) by simp
  qed
  show ?thesis using assms(1) all_zero
  proof (induction p)
    case (Atom v) show ?case by simp
  next
    case (Conn c fs)
    from Conn.prems(1) have "length fs = arity (alphabet F) c" by simp
    with all_zero have "fs = []" by simp
    thus ?case by simp
  qed
qed

lemma spira_trans_id_when_small:
  assumes "formula_well_formed (alphabet F) f"
      and "len_formula f < spira_threshold"
    shows "spira_trans f = f"
proof -
  from spira_trans_dom_and_eval[OF assms(1)] have dom: "spira_trans_dom f" by simp
  show ?thesis
  proof (cases f)
    case (Atom v)
    thus ?thesis using dom by (simp add: spira_trans.psimps)
  next
    case (Conn c fs)
    show ?thesis
    proof (cases fs)
      case Nil
      thus ?thesis using Conn dom by (simp add: spira_trans.psimps)
    next
      case (Cons f1 fs1)
      hence "spira_trans (Conn c (f1 # fs1))
           = (let p = Conn c (f1 # fs1); pos = spiras_sel_position p in
              if len_formula p < spira_threshold then p
              else balance (spira_trans (fix_at pos True p))
                           (spira_trans (fix_at pos False p))
                           (spira_trans (subterm_at p pos)))"
        using dom Conn by (simp add: spira_trans.psimps)
      thus ?thesis using assms(2) Conn Cons by (simp add: Let_def)
    qed
  qed
qed

text \<open>The depth bound: \<open>O(log n)\<close> with the constant determined by the alphabet's
      max-arity \<open>k\<close> and the depth of \<open>custom_balancing\<close>.\<close>

lemma trans_c_k0:
  assumes "Max ((arity (alphabet F)) ` (UNIV :: 'c set)) = 0"
  shows "\<forall> f :: 'c formula. formula_well_formed (alphabet F) f \<longrightarrow>
           real (depth_formula (spira_trans f))
           \<le> 1 * log 2 (real (len_formula f) + 1)"
proof (intro allI impI)
  fix f :: "'c formula" assume wf: "formula_well_formed (alphabet F) f"
  have len_eq: "len_formula f = 1"
    using wf assms by (rule wf_arity_zero_imp_len_1)
  have len_lt: "len_formula f < spira_threshold"
    using len_eq unfolding spira_threshold_def by simp
  have st_eq: "spira_trans f = f"
    using wf len_lt by (rule spira_trans_id_when_small)
  have "depth_formula f \<le> len_formula f" by (rule depth_le_len)
  hence "real (depth_formula f) \<le> 1" using len_eq by simp
  moreover have "log 2 (real (len_formula f) + 1) = 1"
    using len_eq by simp
  ultimately show "real (depth_formula (spira_trans f))
                 \<le> 1 * log 2 (real (len_formula f) + 1)"
    using st_eq by simp
qed

lemma depth_formula_ge_1: "depth_formula f \<ge> 1"
proof (induction f)
  case (Atom v) show ?case by simp
next
  case (Conn c fs) show ?case by (cases fs) auto
qed

lemma trans_c:
  shows "\<exists> c :: real. \<forall> f :: 'c formula.
           formula_well_formed (alphabet F) f \<longrightarrow>
           real (depth_formula (spira_trans f))
           \<le> c * log 2 (real (len_formula f) + 1)"
proof -
  let ?k = "Max ((arity (alphabet F)) ` (UNIV :: 'c set))"
  consider (k0) "?k = 0" | (kpos) "?k \<ge> 1" by linarith
  thus ?thesis
  proof cases
    case k0
    show ?thesis using trans_c_k0[OF k0] by blast
  next
    case kpos
    let ?D = "real (depth_formula custom_balancing)"
    define A where "A = (if ?k > 1 then ?k + 1 else 3)"
    define B where "B = (if ?k > 1 then ?k else 2)"
    define C where "C = (if ?k > 1 then 2 * ?k + 1 else 3)"
    define T where "T = spira_threshold"

    have A_gt_B: "A > B" unfolding A_def B_def using kpos by auto
    have AC_ge_B: "A + C \<ge> B" unfolding A_def C_def B_def by auto
    have T_ge_2: "T \<ge> 2" unfolding T_def spira_threshold_def by simp

    have ratio_pos: "B * T + C + A < A * (T + 1)"
    proof (cases "?k > 1")
      case True
      have A_eq: "A = ?k + 1" using A_def True by simp
      have B_eq: "B = ?k" using B_def True by simp
      have C_eq: "C = 2 * ?k + 1" using C_def True by simp
      have T_eq: "T = 4 * ?k + 4" using T_def spira_threshold_def True by simp
      show ?thesis unfolding A_eq B_eq C_eq T_eq by (simp add: algebra_simps)
    next
      case False
      with kpos have keq: "?k = 1" by simp
      have A_eq: "A = 3" using A_def False by simp
      have B_eq: "B = 2" using B_def False by simp
      have C_eq: "C = 3" using C_def False by simp
      have T_eq: "T = 12" using T_def spira_threshold_def keq by simp
      show ?thesis unfolding A_eq B_eq C_eq T_eq by simp
    qed

    let ?ratio = "real (A * (T + 1)) / real (B * T + C + A)"
    have A_ge_1: "A \<ge> 1" unfolding A_def using kpos by auto
    have ratio_gt_1: "?ratio > 1"
    proof -
      have denom_pos: "(0::real) < real (B * T + C + A)"
      proof -
        have "(0::real) < real A" using A_ge_1 by simp
        also have "real A \<le> real (B * T + C + A)" by simp
        finally show ?thesis .
      qed
      have num_gt: "real (B * T + C + A) < real (A * (T + 1))"
        using ratio_pos by (simp only: of_nat_less_iff)
      from denom_pos num_gt show ?thesis by (simp add: divide_simps)
    qed
    have log_ratio_pos: "log 2 ?ratio > 0" using ratio_gt_1 by simp

    define c where "c = max (real T) (?D / log 2 ?ratio)"
    have c_pos: "c \<ge> 0" unfolding c_def using T_ge_2 by simp
    have c_ge_T: "c \<ge> real T" unfolding c_def by simp
    have c_log_ge_D: "c * log 2 ?ratio \<ge> ?D"
    proof -
      have "?D / log 2 ?ratio \<le> c" unfolding c_def by simp
      thus ?thesis using log_ratio_pos by (simp add: divide_le_eq)
    qed

    have arg_bound: "\<And> p b. formula_well_formed (alphabet F) p
                       \<Longrightarrow> len_formula p \<ge> T
                       \<Longrightarrow> A * (len_formula (spiras_sel p) + 1) \<le> B * len_formula p + C + A
                         \<and> A * (len_formula (fix_at (spiras_sel_position p) b p) + 1)
                            \<le> B * len_formula p + C + A"
    proof -
      fix p :: "'c formula" and b :: bool
      assume wf: "formula_well_formed (alphabet F) p"
         and lenge: "len_formula p \<ge> T"
      have lenge_st: "len_formula p \<ge> spira_threshold"
        using lenge T_def by simp
      show "A * (len_formula (spiras_sel p) + 1) \<le> B * len_formula p + C + A
          \<and> A * (len_formula (fix_at (spiras_sel_position p) b p) + 1)
             \<le> B * len_formula p + C + A"
      proof (cases "?k > 1")
        case True
        from recursive_arg_len_bound_gen[OF wf lenge_st refl True, of b]
        show ?thesis
          unfolding A_def B_def C_def using True by (auto simp: algebra_simps)
      next
        case False
        with kpos have keq: "?k = 1" by simp
        from recursive_arg_len_bound_one[OF wf lenge_st keq, of b]
        show ?thesis
          unfolding A_def B_def C_def using False by auto
      qed
    qed

    have main: "\<forall> f :: 'c formula. formula_well_formed (alphabet F) f \<longrightarrow>
                                   real (depth_formula (spira_trans f))
                                   \<le> c * log 2 (real (len_formula f) + 1)"
    proof (intro allI impI)
      fix f :: "'c formula"
      assume wf_f: "formula_well_formed (alphabet F) f"
      from wf_f
      show "real (depth_formula (spira_trans f))
          \<le> c * log 2 (real (len_formula f) + 1)"
      proof (induction "len_formula f" arbitrary: f rule: less_induct)
        case less
        show ?case
        proof (cases "len_formula f < T")
          case small: True
          have f_lt: "len_formula f < spira_threshold"
            using small T_def by simp
          have st_eq: "spira_trans f = f"
            using less.prems f_lt by (rule spira_trans_id_when_small)
          have "depth_formula f \<le> len_formula f" by (rule depth_le_len)
          hence "real (depth_formula f) \<le> real (len_formula f)" by simp
          also have "\<dots> < real T" using small by simp
          also have "\<dots> \<le> c" using c_ge_T by simp
          also have "c \<le> c * log 2 (real (len_formula f) + 1)"
          proof -
            have len_ge_1: "len_formula f \<ge> 1" by (rule len_formula_positive)
            hence "real (len_formula f) + 1 \<ge> 2" by simp
            hence "log 2 (real (len_formula f) + 1) \<ge> log 2 (2::real)"
              by (intro log_mono) auto
            hence log_ge_1: "log 2 (real (len_formula f) + 1) \<ge> 1" by simp
            from log_ge_1 c_pos
            have "c * 1 \<le> c * log 2 (real (len_formula f) + 1)"
              by (intro mult_left_mono) auto
            thus ?thesis by simp
          qed
          finally show ?thesis using st_eq by simp
        next
          case big: False
          have f_ge_T: "len_formula f \<ge> T" using big by simp
          have f_ge_st: "len_formula f \<ge> spira_threshold"
            using f_ge_T T_def by simp
          have f_ge_2: "len_formula f \<ge> 2"
            using f_ge_st spira_threshold_def by simp

          obtain cn gs where f_eq: "f = Conn cn gs" and gs_ne: "gs \<noteq> []"
          proof (cases f)
            case (Atom v)
            with f_ge_2 show ?thesis by simp
          next
            case (Conn cn gs)
            with f_ge_2 have "gs \<noteq> []" by (cases gs) auto
            with Conn show ?thesis using that by simp
          qed
          obtain g gs' where gs_eq: "gs = g # gs'" using gs_ne
            by (cases gs) auto
          let ?p = f
          let ?pos = "spiras_sel_position ?p"
          let ?q = "subterm_at ?p ?pos"
          let ?ft = "fix_at ?pos True ?p"
          let ?ff = "fix_at ?pos False ?p"

          have wf_p: "formula_well_formed (alphabet F) ?p" using less.prems .
          have pos_spec: "valid_position ?p ?pos \<and> subterm_at ?p ?pos = spiras_sel ?p"
            using spiras_sel_position_spec[OF wf_p f_ge_2] .
          have pos_valid: "valid_position ?p ?pos" using pos_spec by simp
          have q_eq: "?q = spiras_sel ?p" using pos_spec by simp
          from spira_trans_dom_and_eval[OF wf_p]
          have dom_p: "spira_trans_dom ?p" by simp
          have st_unfold: "spira_trans ?p
                         = balance (spira_trans ?ft)
                                   (spira_trans ?ff)
                                   (spira_trans ?q)"
          proof -
            have psimp: "spira_trans (Conn cn (g # gs')) =
                  (let p = Conn cn (g # gs'); pos = spiras_sel_position p in
                   if len_formula p < spira_threshold then p
                   else balance (spira_trans (fix_at pos True p))
                                (spira_trans (fix_at pos False p))
                                (spira_trans (subterm_at p pos)))"
              using dom_p f_eq gs_eq
              by (simp add: spira_trans.psimps)
            thus ?thesis using f_ge_st f_eq gs_eq by (simp add: Let_def)
          qed

          have q_sub: "is_subformula ?q ?p"
            and q_lt: "len_formula ?q < len_formula ?p"
            using spiras_sel_pred_when_wf[OF wf_p f_ge_2] q_eq by auto
          have wf_q: "formula_well_formed (alphabet F) ?q"
            using wf_p q_sub subformula_wf by blast
          have wf_T: "formula_well_formed (alphabet F) ?ft"
            using wf_p by (rule fix_at_wf)
          have wf_F: "formula_well_formed (alphabet F) ?ff"
            using wf_p by (rule fix_at_wf)

          have q_ge_2: "len_formula ?q \<ge> 2"
            using spiras_sel_len_ge_2_when_wf[OF wf_p f_ge_st] q_eq by simp
          have ft_lt: "len_formula ?ft < len_formula ?p"
            using fix_at_len_strict[OF pos_valid q_ge_2] .
          have ff_lt: "len_formula ?ff < len_formula ?p"
            using fix_at_len_strict[OF pos_valid q_ge_2] .

          from less.hyps[OF q_lt wf_q]
          have ih_q: "real (depth_formula (spira_trans ?q))
                    \<le> c * log 2 (real (len_formula ?q) + 1)" .
          from less.hyps[OF ft_lt wf_T]
          have ih_T: "real (depth_formula (spira_trans ?ft))
                    \<le> c * log 2 (real (len_formula ?ft) + 1)" .
          from less.hyps[OF ff_lt wf_F]
          have ih_F: "real (depth_formula (spira_trans ?ff))
                    \<le> c * log 2 (real (len_formula ?ff) + 1)" .

          from arg_bound[of ?p True, OF wf_p f_ge_T]
          have q_arg: "A * (len_formula ?q + 1) \<le> B * len_formula ?p + C + A"
            and ft_arg: "A * (len_formula ?ft + 1) \<le> B * len_formula ?p + C + A"
            using q_eq by auto
          from arg_bound[of ?p False, OF wf_p f_ge_T]
          have ff_arg: "A * (len_formula ?ff + 1) \<le> B * len_formula ?p + C + A" by auto

          have log_q: "?D + c * log 2 (real (len_formula ?q) + 1)
                     \<le> c * log 2 (real (len_formula ?p) + 1)"
            using trans_c_log_step[OF A_gt_B AC_ge_B q_arg f_ge_T ratio_pos
                                       c_log_ge_D c_pos] .
          have log_T: "?D + c * log 2 (real (len_formula ?ft) + 1)
                     \<le> c * log 2 (real (len_formula ?p) + 1)"
            using trans_c_log_step[OF A_gt_B AC_ge_B ft_arg f_ge_T ratio_pos
                                       c_log_ge_D c_pos] .
          have log_F: "?D + c * log 2 (real (len_formula ?ff) + 1)
                     \<le> c * log 2 (real (len_formula ?p) + 1)"
            using trans_c_log_step[OF A_gt_B AC_ge_B ff_arg f_ge_T ratio_pos
                                       c_log_ge_D c_pos] .

          have stq_ge_1: "depth_formula (spira_trans ?q) \<ge> 1"
            by (rule depth_formula_ge_1)
          have stT_ge_1: "depth_formula (spira_trans ?ft) \<ge> 1"
            by (rule depth_formula_ge_1)
          have stF_ge_1: "depth_formula (spira_trans ?ff) \<ge> 1"
            by (rule depth_formula_ge_1)

          have max_collapse: "Max (insert 1 {depth_formula (spira_trans ?ft),
                                              depth_formula (spira_trans ?ff),
                                              depth_formula (spira_trans ?q)})
                            = Max {depth_formula (spira_trans ?ft),
                                   depth_formula (spira_trans ?ff),
                                   depth_formula (spira_trans ?q)}"
            using stq_ge_1 stT_ge_1 stF_ge_1 by auto

          have "depth_formula (spira_trans ?p)
              \<le> depth_formula custom_balancing
              + Max (insert 1 {depth_formula (spira_trans ?ft),
                               depth_formula (spira_trans ?ff),
                               depth_formula (spira_trans ?q)})"
            using st_unfold balance_depth_bound by simp
          hence depth_real_bound:
              "real (depth_formula (spira_trans ?p))
             \<le> ?D
             + real (Max {depth_formula (spira_trans ?ft),
                          depth_formula (spira_trans ?ff),
                          depth_formula (spira_trans ?q)})"
            using max_collapse by simp

          let ?MS = "{depth_formula (spira_trans ?ft),
                      depth_formula (spira_trans ?ff),
                      depth_formula (spira_trans ?q)}"
          have max_le: "real (Max ?MS) \<le> c * log 2 (real (len_formula ?p) + 1) - ?D"
          proof -
            have ms_fin: "finite ?MS" by simp
            have ms_ne: "?MS \<noteq> {}" by simp
            from Max_in[OF ms_fin ms_ne]
            have m_in: "Max ?MS \<in> ?MS" .
            from m_in have "Max ?MS = depth_formula (spira_trans ?ft)
                          \<or> Max ?MS = depth_formula (spira_trans ?ff)
                          \<or> Max ?MS = depth_formula (spira_trans ?q)" by auto
            thus ?thesis
            proof (elim disjE)
              assume eq: "Max ?MS = depth_formula (spira_trans ?ft)"
              have "real (Max ?MS) \<le> c * log 2 (real (len_formula ?ft) + 1)"
                using eq ih_T by simp
              also have "\<dots> \<le> c * log 2 (real (len_formula ?p) + 1) - ?D"
                using log_T by simp
              finally show ?thesis .
            next
              assume eq: "Max ?MS = depth_formula (spira_trans ?ff)"
              have "real (Max ?MS) \<le> c * log 2 (real (len_formula ?ff) + 1)"
                using eq ih_F by simp
              also have "\<dots> \<le> c * log 2 (real (len_formula ?p) + 1) - ?D"
                using log_F by simp
              finally show ?thesis .
            next
              assume eq: "Max ?MS = depth_formula (spira_trans ?q)"
              have "real (Max ?MS) \<le> c * log 2 (real (len_formula ?q) + 1)"
                using eq ih_q by simp
              also have "\<dots> \<le> c * log 2 (real (len_formula ?p) + 1) - ?D"
                using log_q by simp
              finally show ?thesis .
            qed
          qed
          from depth_real_bound max_le show ?thesis by simp
        qed
      qed
    qed
    show ?thesis using main by blast
  qed
qed

subsubsection \<open>Well-formedness and polynomial size\<close>

text \<open>
  The construction uses only connectives from the original alphabet and respects
  their arities. A formula with bounded arity has size at most exponential in its
  depth. Applying this estimate to the logarithmic depth bound gives a polynomial
  bound on the size of the balanced formula.
\<close>

lemma sub_formula_wf:
  fixes sub :: "string \<Rightarrow> 'c formula" and g :: "'c formula"
  assumes wf_g: "formula_well_formed (alphabet F) g"
      and wf_sub: "\<And> v. formula_well_formed (alphabet F) (sub v)"
  shows "formula_well_formed (alphabet F) (sub_formula sub g)"
  using wf_g
proof (induction g)
  case (Atom v)
  show ?case using wf_sub by simp
next
  case (Conn cn fs)
  have len_eq: "length fs = arity (alphabet F) cn"
   and wf_each: "\<forall> g \<in> set fs. formula_well_formed (alphabet F) g"
    using Conn.prems by auto
  have new_len: "length (map (sub_formula sub) fs) = arity (alphabet F) cn"
    using len_eq by simp
  have new_each: "\<forall> g' \<in> set (map (sub_formula sub) fs).
                  formula_well_formed (alphabet F) g'"
  proof
    fix g' assume "g' \<in> set (map (sub_formula sub) fs)"
    then obtain g where g_in: "g \<in> set fs" and g'_eq: "g' = sub_formula sub g"
      by auto
    have wf_inner: "formula_well_formed (alphabet F) g"
      using wf_each g_in by simp
    show "formula_well_formed (alphabet F) g'"
      using Conn.IH g_in wf_inner g'_eq by simp
  qed
  show ?case using new_len new_each by simp
qed

lemma balance_wf:
  assumes wf_x: "formula_well_formed (alphabet F) x"
      and wf_y: "formula_well_formed (alphabet F) y"
      and wf_z: "formula_well_formed (alphabet F) z"
  shows "formula_well_formed (alphabet F) (balance x y z)"
proof -
  let ?sub = "\<lambda>v. if v = ''x'' then x
                  else if v = ''y'' then y
                  else if v = ''z'' then z
                  else Atom v"
  have wf_sub: "\<And> v. formula_well_formed (alphabet F) (?sub v)"
    using wf_x wf_y wf_z by simp
  have wf_cb: "formula_well_formed (alphabet F) custom_balancing"
    using custom_balancing_spec by simp
  have unfold: "balance x y z = sub_formula ?sub custom_balancing"
    by (simp add: Let_def)
  show ?thesis using unfold sub_formula_wf[OF wf_cb wf_sub] by simp
qed

lemma spira_trans_wf:
  fixes f :: "'c formula"
  assumes "formula_well_formed (alphabet F) f"
  shows "formula_well_formed (alphabet F) (spira_trans f)"
  using assms
proof (induction "len_formula f" arbitrary: f rule: less_induct)
  case less
  show ?case
  proof (cases f)
    case (Atom v)
    have dom: "spira_trans_dom f"
      using spira_trans_dom_and_eval[OF less.prems] by simp
    have "spira_trans f = f"
      using dom Atom by (simp add: spira_trans.psimps(1))
    thus ?thesis using less.prems by simp
  next
    case (Conn cn fs)
    show ?thesis
    proof (cases fs)
      case Nil
      have dom: "spira_trans_dom f"
        using spira_trans_dom_and_eval[OF less.prems] by simp
      have "spira_trans f = f"
        using dom Conn Nil by (simp add: spira_trans.psimps(2))
      thus ?thesis using less.prems by simp
    next
      case (Cons f1 fs1)
      let ?p = f
      let ?pos = "spiras_sel_position ?p"
      let ?q = "subterm_at ?p ?pos"
      let ?ft = "fix_at ?pos True ?p"
      let ?ff = "fix_at ?pos False ?p"
      have wf_p: "formula_well_formed (alphabet F) ?p" using less.prems .
      have dom_p: "spira_trans_dom ?p"
        using spira_trans_dom_and_eval[OF wf_p] by simp
      show ?thesis
      proof (cases "len_formula ?p < spira_threshold")
        case True
        have psimp: "spira_trans (Conn cn (f1 # fs1)) =
                     (let p = Conn cn (f1 # fs1); pos = spiras_sel_position p in
                       if len_formula p < spira_threshold then p
                       else balance (spira_trans (fix_at pos True p))
                                    (spira_trans (fix_at pos False p))
                                    (spira_trans (subterm_at p pos)))"
          using dom_p Conn Cons by (simp add: spira_trans.psimps(3))
        have "spira_trans ?p = ?p"
          using psimp True Conn Cons by (simp add: Let_def)
        thus ?thesis using less.prems by simp
      next
        case big: False
        have ge: "len_formula ?p \<ge> spira_threshold" using big by simp
        have ge2: "len_formula ?p \<ge> 2"
          using ge spira_threshold_def by simp
        have pos_spec: "valid_position ?p ?pos \<and> subterm_at ?p ?pos = spiras_sel ?p"
          using spiras_sel_position_spec[OF wf_p ge2] .
        have pos_valid: "valid_position ?p ?pos" using pos_spec by simp
        have q_eq: "?q = spiras_sel ?p" using pos_spec by simp
        from spiras_sel_pred_when_wf[OF wf_p ge2]
        have q_sub: "is_subformula ?q ?p"
         and q_lt: "len_formula ?q < len_formula ?p" using q_eq by auto
        have q_ge_2: "len_formula ?q \<ge> 2"
          using spiras_sel_len_ge_2_when_wf[OF wf_p ge] q_eq by simp
        have wf_q: "formula_well_formed (alphabet F) ?q"
          using wf_p q_sub subformula_wf by blast
        have wf_ft: "formula_well_formed (alphabet F) ?ft"
          using wf_p by (rule fix_at_wf)
        have wf_ff: "formula_well_formed (alphabet F) ?ff"
          using wf_p by (rule fix_at_wf)
        have ft_lt: "len_formula ?ft < len_formula ?p"
          using fix_at_len_strict[OF pos_valid q_ge_2] .
        have ff_lt: "len_formula ?ff < len_formula ?p"
          using fix_at_len_strict[OF pos_valid q_ge_2] .
        from less.hyps[OF q_lt wf_q]
        have wf_t_q: "formula_well_formed (alphabet F) (spira_trans ?q)" .
        from less.hyps[OF ft_lt wf_ft]
        have wf_t_ft: "formula_well_formed (alphabet F) (spira_trans ?ft)" .
        from less.hyps[OF ff_lt wf_ff]
        have wf_t_ff: "formula_well_formed (alphabet F) (spira_trans ?ff)" .
        have st_eq: "spira_trans ?p
                   = balance (spira_trans ?ft) (spira_trans ?ff) (spira_trans ?q)"
        proof -
          have psimp: "spira_trans (Conn cn (f1 # fs1)) =
                       (let p = Conn cn (f1 # fs1); pos = spiras_sel_position p in
                         if len_formula p < spira_threshold then p
                         else balance (spira_trans (fix_at pos True p))
                                      (spira_trans (fix_at pos False p))
                                      (spira_trans (subterm_at p pos)))"
            using dom_p Conn Cons by (simp add: spira_trans.psimps(3))
          thus ?thesis using big Conn Cons by (simp add: Let_def)
        qed
        show ?thesis
          using st_eq balance_wf[OF wf_t_ft wf_t_ff wf_t_q] by simp
      qed
    qed
  qed
qed

lemma len_le_arity_pow_depth:
  fixes f :: "'c formula"
  assumes "formula_well_formed (alphabet F) f"
  shows "len_formula f \<le>
         (Max ((arity (alphabet F)) ` (UNIV :: 'c set)) + 1) ^ depth_formula f"
  using assms
proof (induction f)
  case (Atom v) show ?case by simp
next
  case (Conn cn fs)
  let ?M = "Max ((arity (alphabet F)) ` (UNIV :: 'c set)) + 1"
  let ?k = "Max ((arity (alphabet F)) ` (UNIV :: 'c set))"
  have alphabet_finite: "finite (UNIV :: 'c set)"
    by (meson frege_balancing_axioms frege_balancing_def
              frege_system.finite_alphabet)
  hence finite_image: "finite ((arity (alphabet F)) ` (UNIV :: 'c set))" by simp
  have len_eq: "length fs = arity (alphabet F) cn"
   and wf_each: "\<forall> g \<in> set fs. formula_well_formed (alphabet F) g"
    using Conn.prems by auto
  have arity_le_k: "arity (alphabet F) cn \<le> ?k"
    using Max_ge[OF finite_image] by auto
  show ?case
  proof (cases fs)
    case Nil
    show ?thesis using Nil by simp
  next
    case (Cons g0 gs0)
    have fs_ne: "fs \<noteq> []" using Cons by simp
    let ?max_depth = "Max (set (map depth_formula fs))"
    have depths_finite: "finite (set (map depth_formula fs))" by simp
    have depth_eq: "depth_formula (Conn cn fs) = 1 + ?max_depth"
      using fs_ne by simp
    have len_unfold: "len_formula (Conn cn fs) = 1 + sum_list (map len_formula fs)"
      by simp
    have each_le: "\<forall> g \<in> set fs. len_formula g \<le> ?M ^ ?max_depth"
    proof
      fix g assume g_in: "g \<in> set fs"
      have wf_g: "formula_well_formed (alphabet F) g" using wf_each g_in by simp
      have ih_g: "len_formula g \<le> ?M ^ depth_formula g"
        using Conn.IH g_in wf_g by simp
      have depth_g_le: "depth_formula g \<le> ?max_depth"
        using Max_ge[OF depths_finite] g_in by simp
      have M_pow_mono: "?M ^ depth_formula g \<le> ?M ^ ?max_depth"
        using depth_g_le by (rule power_increasing) simp
      from ih_g M_pow_mono show "len_formula g \<le> ?M ^ ?max_depth" by linarith
    qed
    have sum_le: "sum_list (map len_formula fs) \<le> length fs * (?M ^ ?max_depth)"
    proof -
      have step: "sum_list (map len_formula fs)
                \<le> sum_list (map (\<lambda>_. ?M ^ ?max_depth) fs)"
        using each_le by (intro sum_list_pointwise_le) auto
      have const_sum: "sum_list (map (\<lambda>_. ?M ^ ?max_depth) fs)
                     = length fs * (?M ^ ?max_depth)"
        by (rule sum_list_const_nat)
      from step const_sum show ?thesis by linarith
    qed
    have step1: "len_formula (Conn cn fs) \<le> 1 + length fs * (?M ^ ?max_depth)"
      using len_unfold sum_le by linarith
    have step2: "1 + length fs * (?M ^ ?max_depth) \<le> 1 + ?k * (?M ^ ?max_depth)"
      using arity_le_k len_eq by simp
    have step3: "1 + ?k * (?M ^ ?max_depth) \<le> ?M * (?M ^ ?max_depth)"
    proof -
      have eq: "?M * ?M ^ ?max_depth = ?k * ?M ^ ?max_depth + ?M ^ ?max_depth"
        by (simp add: distrib_right)
      have one_le: "(1::nat) \<le> ?M ^ ?max_depth" by simp
      from eq one_le show ?thesis by linarith
    qed
    have step4: "?M * ?M ^ ?max_depth = ?M ^ depth_formula (Conn cn fs)"
      using depth_eq by simp
    from step1 step2 step3 step4 show ?thesis by linarith
  qed
qed

lemma trans_b:
  shows "\<exists> p :: nat poly. \<forall> f :: 'c formula.
           formula_well_formed (alphabet F) f \<longrightarrow>
           len_formula (spira_trans f) \<le> poly p (len_formula f)"
proof -
  define M :: nat where "M = Max ((arity (alphabet F)) ` (UNIV :: 'c set)) + 1"
  have M_ge_1: "M \<ge> 1" unfolding M_def by simp
  have M_real_ge_1: "real M \<ge> 1" using M_ge_1 by simp
  have M_real_pos: "real M > 0" using M_ge_1 by simp
  obtain c :: real where c_bound:
    "\<forall> g :: 'c formula. formula_well_formed (alphabet F) g \<longrightarrow>
                       real (depth_formula (spira_trans g))
                       \<le> c * log 2 (real (len_formula g) + 1)"
    using trans_c by blast
  define c' :: real where "c' = max c 0"
  have c'_nn: "c' \<ge> 0" unfolding c'_def by simp
  have c'_ge_c: "c' \<ge> c" unfolding c'_def by simp
  define a :: real where "a = c' * log 2 (real M)"
  have logM_nn: "log 2 (real M) \<ge> 0" using M_real_ge_1 by simp
  have a_nn: "a \<ge> 0"
    unfolding a_def using c'_nn logM_nn by simp
  define e :: nat where "e = nat \<lceil>a\<rceil>"
  have a_le_e: "a \<le> real e"
    unfolding e_def using a_nn by linarith
  define p :: "nat poly" where "p = monom (2 ^ e) e"
  have poly_eval: "\<And> L :: nat. poly p L = 2 ^ e * L ^ e"
    unfolding p_def by (simp add: poly_monom)

  show ?thesis
  proof (intro exI[of _ p] allI impI)
    fix f :: "'c formula"
    assume wf: "formula_well_formed (alphabet F) f"
    define L :: nat where "L = len_formula f"
    have L_ge_1: "L \<ge> 1" unfolding L_def using len_formula_positive by simp
    have L_real_ge_1: "real L \<ge> 1" using L_ge_1 by simp
    have Lp1_real_ge_1: "real L + 1 \<ge> 1" using L_real_ge_1 by simp
    have wf_t: "formula_well_formed (alphabet F) (spira_trans f)"
      by (rule spira_trans_wf[OF wf])
    have len_pow: "len_formula (spira_trans f) \<le> M ^ depth_formula (spira_trans f)"
      using wf_t unfolding M_def by (rule len_le_arity_pow_depth)
    have depth_log: "real (depth_formula (spira_trans f))
                   \<le> c' * log 2 (real L + 1)"
    proof -
      have logL_nn: "log 2 (real L + 1) \<ge> 0" using L_real_ge_1 by simp
      have base: "real (depth_formula (spira_trans f))
                \<le> c * log 2 (real (len_formula f) + 1)"
        using c_bound wf by simp
      hence "real (depth_formula (spira_trans f)) \<le> c * log 2 (real L + 1)"
        using L_def by simp
      also have "\<dots> \<le> c' * log 2 (real L + 1)"
        using c'_ge_c logL_nn by (intro mult_right_mono) auto
      finally show ?thesis .
    qed
    have swap_id: "real M powr (c' * log 2 (real L + 1))
                 = (real L + 1) powr (c' * log 2 (real M))"
    proof -
      have M_ne: "real M \<noteq> 0" using M_real_pos by simp
      have Lp1_ne: "real L + 1 \<noteq> 0" using L_real_ge_1 by simp
      have "real M powr (c' * log 2 (real L + 1))
          = exp (c' * log 2 (real L + 1) * ln (real M))"
        using M_ne by (simp add: powr_def)
      also have "\<dots> = exp (c' * (ln (real L + 1) / ln 2) * ln (real M))"
        by (simp add: log_def)
      also have "\<dots> = exp (c' * (ln (real M) / ln 2) * ln (real L + 1))"
        by (simp add: ac_simps)
      also have "\<dots> = exp (c' * log 2 (real M) * ln (real L + 1))"
        by (simp add: log_def)
      also have "\<dots> = (real L + 1) powr (c' * log 2 (real M))"
        using Lp1_ne by (simp add: powr_def)
      finally show ?thesis .
    qed
    have step_real: "real (M ^ depth_formula (spira_trans f))
                   \<le> (real L + 1) powr a"
    proof -
      have "real (M ^ depth_formula (spira_trans f))
          = real M ^ depth_formula (spira_trans f)" by simp
      also have "\<dots> = real M powr real (depth_formula (spira_trans f))"
        using M_real_pos by (simp add: powr_realpow)
      also have "\<dots> \<le> real M powr (c' * log 2 (real L + 1))"
        using depth_log M_real_ge_1 by (rule powr_mono)
      also have "\<dots> = (real L + 1) powr (c' * log 2 (real M))"
        using swap_id .
      finally show ?thesis unfolding a_def .
    qed
    have step_pow: "(real L + 1) powr a \<le> (real L + 1) powr real e"
      using a_le_e Lp1_real_ge_1 by (rule powr_mono)
    have step_to_nat_pow: "(real L + 1) powr real e = real ((L + 1) ^ e)"
    proof -
      have pos: "(0::real) < real L + 1" using L_real_ge_1 by simp
      have "(real L + 1) powr real e = (real L + 1) ^ e"
        using pos by (simp add: powr_realpow)
      also have "\<dots> = real ((L + 1) ^ e)" by (simp add: add.commute)
      finally show ?thesis .
    qed
    have step_2L: "(L + 1) ^ e \<le> (2 * L) ^ e"
      using L_ge_1 by (intro power_mono) auto
    have step_split: "(2 * L :: nat) ^ e = 2 ^ e * L ^ e"
      by (simp add: power_mult_distrib)
    have real_to_pow: "real (len_formula (spira_trans f)) \<le> real ((L + 1) ^ e)"
    proof -
      have "real (len_formula (spira_trans f))
          \<le> real (M ^ depth_formula (spira_trans f))"
        using len_pow by simp
      also have "\<dots> \<le> (real L + 1) powr a" using step_real .
      also have "\<dots> \<le> (real L + 1) powr real e" using step_pow .
      also have "\<dots> = real ((L + 1) ^ e)" using step_to_nat_pow .
      finally show ?thesis .
    qed
    have nat_chain: "len_formula (spira_trans f) \<le> 2 ^ e * L ^ e"
    proof -
      have step_a: "len_formula (spira_trans f) \<le> (L + 1) ^ e"
        using real_to_pow by linarith
      have step_b: "(L + 1) ^ e \<le> (2 * L) ^ e" using step_2L .
      have step_c: "(2 * L :: nat) ^ e = 2 ^ e * L ^ e" using step_split .
      from step_a step_b step_c show ?thesis by linarith
    qed
    show "len_formula (spira_trans f) \<le> poly p (len_formula f)"
      using nat_chain poly_eval[of L] L_def by simp
  qed
qed

end

end
