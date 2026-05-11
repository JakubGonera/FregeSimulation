theory Translation
  imports Frege Arithmetic "HOL.Transcendental"
begin

(* The numbering of lemmas follows Yuval Filmus' manuscript *)

subsection \<open>Lemma 3.2\<close>

definition plug :: "string \<Rightarrow> 'c formula \<Rightarrow> 'c formula \<Rightarrow> 'c formula" where
  "plug h \<tau> \<chi> = sub_formula (\<lambda>v. if v = h then \<tau> else Atom v) \<chi>"

definition deducible :: "'c frege \<Rightarrow> ('c formula) set \<Rightarrow> 'c formula \<Rightarrow> nat \<Rightarrow> bool" where
  "deducible F asms c n \<longleftrightarrow>
     (\<exists> p. valid_proof F p \<and> assumptions p \<subseteq> asms \<and> thesis p = c \<and> len_proof p \<le> n)"

lemma eval_sub_formula:
  "eval al val (sub_formula sub f) = eval al (\<lambda>v. eval al val (sub v)) f"
proof (induction f)
  case (Atom a)
  show ?case by simp
next
  case (Conn c zs)
  have step: "\<And>x. x \<in> set zs \<Longrightarrow>
       eval al val (sub_formula sub x) = eval al (\<lambda>v. eval al val (sub v)) x"
    using Conn.IH by blast
  have map_eq: "map (eval al val \<circ> sub_formula sub) zs =
                map (eval al (\<lambda>v. eval al val (sub v))) zs"
  proof (rule map_cong)
    show "zs = zs" by (rule refl)
  next
    fix x assume x_in: "x \<in> set zs"
    show "(eval al val \<circ> sub_formula sub) x = eval al (\<lambda>v. eval al val (sub v)) x"
      using step[OF x_in] by (simp add: comp_def)
  qed
  have "eval al val (sub_formula sub (Conn c zs)) =
        conn_evals al c (map (eval al val \<circ> sub_formula sub) zs)"
    by (simp add: comp_def)
  also have "\<dots> = conn_evals al c (map (eval al (\<lambda>v. eval al val (sub v))) zs)"
    by (simp only: map_eq)
  also have "\<dots> = eval al (\<lambda>v. eval al val (sub v)) (Conn c zs)"
    by simp
  finally show ?case .
qed

lemma sub_formula_agree:
  fixes s1 s2 :: "string \<Rightarrow> 'c formula" and f :: "'c formula"
  assumes "\<forall>v \<in> var_set_form f. s1 v = s2 v"
  shows "sub_formula s1 f = sub_formula s2 f"
  using assms
proof (induction f)
  case (Atom a)
  thus ?case by simp
next
  case (Conn c fs)
  have "\<forall>g \<in> set fs. \<forall>v \<in> var_set_form g. s1 v = s2 v"
    using Conn.prems by simp
  hence pointwise: "\<forall>g \<in> set fs. sub_formula s1 g = sub_formula s2 g"
    using Conn.IH by blast
  have "map (sub_formula s1) fs = map (sub_formula s2) fs"
    using pointwise by (induction fs) auto
  thus ?case by simp
qed

lemma sub_formula_comp:
  fixes s1 s2 :: "string \<Rightarrow> 'c formula" and f :: "'c formula"
  shows "sub_formula s1 (sub_formula s2 f) = sub_formula (\<lambda>v. sub_formula s1 (s2 v)) f"
  by (induction f) simp_all

lemma map_of_zip_nth_lookup:
  fixes xs :: "'a list" and ys :: "'b list" and k :: nat
  assumes "distinct xs" "length xs = length ys" "k < length xs"
  shows "map_of (zip xs ys) (xs ! k) = Some (ys ! k)"
  using assms
proof (induction k arbitrary: xs ys)
  case 0
  show ?case
  proof (cases xs)
    case Nil
    thus ?thesis using 0(3) by simp
  next
    case (Cons x xs')
    then obtain y ys' where ys_eq: "ys = y # ys'"
      using 0(2) by (cases ys) auto
    show ?thesis using Cons ys_eq by simp
  qed
next
  case (Suc k)
  obtain x xs' where xs_eq: "xs = x # xs'"
    using Suc.prems(3) by (cases xs) auto
  obtain y ys' where ys_eq: "ys = y # ys'"
    using Suc.prems(2,3) xs_eq by (cases ys) auto
  from Suc.prems xs_eq ys_eq have
    dist': "distinct xs'" and len': "length xs' = length ys'" and k_lt': "k < length xs'"
    by simp_all
  have IH': "map_of (zip xs' ys') (xs' ! k) = Some (ys' ! k)"
    using Suc.IH[OF dist' len' k_lt'] .
  have x_not_in: "x \<notin> set xs'" using Suc.prems(1) xs_eq by simp
  have nth_in: "xs' ! k \<in> set xs'" using k_lt' nth_mem by blast
  hence neq: "xs' ! k \<noteq> x" using x_not_in by blast
  show ?case using xs_eq ys_eq IH' neq by simp
qed

lemma map_of_zip_None_lookup:
  fixes xs :: "'a list" and ys :: "'b list" and k :: 'a
  assumes "k \<notin> set xs"
  shows "map_of (zip xs ys) k = None"
  using assms
proof (induction xs arbitrary: ys)
  case Nil show ?case by simp
next
  case (Cons x xs')
  show ?case
  proof (cases ys)
    case Nil thus ?thesis by simp
  next
    case (Cons y ys')
    have "k \<noteq> x" using Cons.prems by simp
    moreover have "k \<notin> set xs'" using Cons.prems by simp
    ultimately show ?thesis using Cons.IH[where ys = ys'] Cons by simp
  qed
qed

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

lemma fresh_distinct_atoms_exist:
  "\<exists>vs :: string list.
       length vs = n \<and> distinct vs \<and> ''a'' \<notin> set vs \<and> ''b'' \<notin> set vs"
proof -
  have "\<exists>vs. length vs = n \<and> distinct vs \<and> set vs \<inter> {''a'', ''b''} = {}"
    using fresh_distinct_atoms_exist_general[where avoid = "{''a'', ''b''}"] by simp
  thus ?thesis by auto
qed

locale frege_balancing =
  fixes F :: "'c frege"
  assumes "frege_system F"
begin

(* 
   iff_dm \<equiv> (a \<and> b) \<or> (\<not>a \<and> \<not>b) 
   for now we will hardcode variable names to get the artificial connective
   without proving the general equivalence over all formulas substituted.
*)
definition iff_dm :: "dm_conn formula" where
  "iff_dm = Conn Or [Conn And [Atom ''a'', Atom ''b''], 
                     Conn And [Conn Not [Atom ''a''], Conn Not [Atom ''b'']]]"

definition conn_iff :: "'c formula" where
  "conn_iff = (SOME f. formulas_equiv f (alphabet F) iff_dm dm_alphabet)"

lemma conn_iff_spec:
  shows "\<exists> f. formulas_equiv f (alphabet F) iff_dm dm_alphabet"
  by (meson formulas_equiv_def frege_balancing_axioms frege_balancing_def frege_system_def)

(* lemma 3.1 already proven in Frege.thy *)

fun contains_atom :: "'c formula \<Rightarrow> string \<Rightarrow> bool" where
  "contains_atom (Atom s) h = (h = s)" |
  "contains_atom (Conn c fs) h = (\<exists> f \<in> set fs. contains_atom f h)"

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


fun distinguished :: "'c formula \<Rightarrow> string \<Rightarrow> bool" where
  "distinguished (Atom _) _ = True" |
  "distinguished (Conn _ fs) h =
     ((\<exists> f \<in> set fs. contains_atom f h) \<longrightarrow>
        (\<exists>! i. i < length fs \<and> contains_atom (fs ! i) h)
      \<and> (\<forall> f \<in> set fs. distinguished f h))"

(*
  hole_depth \<chi> h: depth at which the variable h sits inside \<chi>. Used as the
  induction measure for iff_congruent --- when distinguished \<chi> h holds, the
  path from the root of \<chi> down to h is unique, so this measure is well-behaved
  and strictly decreases when descending along that unique path.
*)
fun hole_depth :: "'c formula \<Rightarrow> string \<Rightarrow> nat" where
  "hole_depth (Atom a) h = 0" |
  "hole_depth (Conn _ fs) h =
     (if \<exists>f \<in> set fs. contains_atom f h
      then 1 + Max ((\<lambda>f. hole_depth f h) ` set fs)
      else 0)"

lemma hole_depth_decreases:
  assumes contains: "contains_atom (Conn c fs) h"
  assumes i_lt: "i < length fs"
  assumes i_contains: "contains_atom (fs ! i) h"
  shows "hole_depth (fs ! i) h < hole_depth (Conn c fs) h"
proof -
  have witness: "\<exists>f \<in> set fs. contains_atom f h"
    using i_lt i_contains nth_mem by force
  have fin: "finite ((\<lambda>f. hole_depth f h) ` set fs)" by simp
  have ne: "(\<lambda>f. hole_depth f h) ` set fs \<noteq> {}"
    using i_lt by auto
  have "hole_depth (fs ! i) h \<in> (\<lambda>f. hole_depth f h) ` set fs"
    using i_lt nth_mem by force
  hence "hole_depth (fs ! i) h \<le> Max ((\<lambda>f. hole_depth f h) ` set fs)"
    using fin by (simp add: Max_ge)
  also have "\<dots> < 1 + Max ((\<lambda>f. hole_depth f h) ` set fs)" by simp
  also have "\<dots> = hole_depth (Conn c fs) h"
    using witness by simp
  finally show ?thesis .
qed

lemma hole_depth_le_len: "hole_depth \<chi> h \<le> len_formula \<chi>"
proof (induction \<chi>)
  case (Atom a)
  show ?case by simp
next
  case (Conn c fs)
  show ?case
  proof (cases "\<exists>f \<in> set fs. contains_atom f h")
    case False
    thus ?thesis by simp
  next
    case True
    have fin: "finite ((\<lambda>f. hole_depth f h) ` set fs)" by simp
    have ne: "(\<lambda>f. hole_depth f h) ` set fs \<noteq> {}" using True by auto
    have all_le: "\<forall>x \<in> (\<lambda>f. hole_depth f h) ` set fs. x \<le> sum_list (map len_formula fs)"
    proof
      fix x assume "x \<in> (\<lambda>f. hole_depth f h) ` set fs"
      then obtain f where f_in: "f \<in> set fs" and x_eq: "x = hole_depth f h" by auto
      have ih: "hole_depth f h \<le> len_formula f"
        using Conn.IH f_in by blast
      have "len_formula f \<le> sum_list (map len_formula fs)"
        using f_in by (induction fs) auto
      thus "x \<le> sum_list (map len_formula fs)" using ih x_eq by simp
    qed
    have max_le: "Max ((\<lambda>f. hole_depth f h) ` set fs) \<le> sum_list (map len_formula fs)"
      using fin ne all_le by (auto intro: Max.boundedI)
    have "hole_depth (Conn c fs) h = 1 + Max ((\<lambda>f. hole_depth f h) ` set fs)"
      using True by simp
    also have "\<dots> \<le> 1 + sum_list (map len_formula fs)" using max_le by simp
    also have "\<dots> = len_formula (Conn c fs)" by simp
    finally show ?thesis .
  qed
qed

lemma not_contains_imp_plug_id:
  shows "\<not> contains_atom \<chi> h \<Longrightarrow> plug h \<tau> \<chi> = \<chi>"
proof (induction \<chi>)
  case (Atom a)
  thus ?case unfolding plug_def by simp
next
  case (Conn c fs)
  hence none_contains: "\<forall>f \<in> set fs. \<not> contains_atom f h" by auto
  have IH: "\<forall>f \<in> set fs. plug h \<tau> f = f"
    using Conn.IH none_contains by blast
  have "plug h \<tau> (Conn c fs) = Conn c (map (plug h \<tau>) fs)"
    unfolding plug_def by simp
  also have "\<dots> = Conn c (map id fs)"
    using IH by (intro arg_cong[where f="Conn c"]) (simp add: map_idI)
  also have "\<dots> = Conn c fs" by simp
  finally show ?case .
qed

(*
  We prove the existence of a fixed proof for congruence of each connective,
  but to be able to say that this contributes only a constant factor we
  designate a "canonical" instantiation of a connective and variables as children
*)
definition canonical_atoms :: "'c \<Rightarrow> string list" where
  "canonical_atoms c = (SOME vs.
       length vs = arity (alphabet F) c
     \<and> distinct vs
     \<and> set vs \<inter> ({''a'', ''b''} \<union> var_set_form conn_iff) = {})"

definition canonical_conn :: "'c \<Rightarrow> 'c formula" where
  "canonical_conn c = Conn c (map Atom (canonical_atoms c))"

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
                conn_iff"
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

  have conn_iff_equiv: "formulas_equiv conn_iff ?al iff_dm dm_alphabet"
    unfolding conn_iff_def using someI_ex[OF conn_iff_spec] .

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

  show "\<exists>pr. valid_proof F pr \<and>
             assumptions pr = {conn_iff} \<and>
             thesis pr = sub_formula ?sub' conn_iff"
    using one_premise frege_system.impl_complete[OF fs_F] by blast
qed

(*
  Pick, once and for all, a representative base proof for every (connective,
  position) pair. Because the alphabet is finite and arities are bounded, we
  can take the maximum step count, step length and step depth across all such
  proofs --- these are the universal constants we will scale by under
  substitution.
*)
definition base_proof :: "'c \<Rightarrow> nat \<Rightarrow> 'c frege_proof" where
  "base_proof c i = (SOME pr. valid_proof F pr \<and>
       assumptions pr = {conn_iff} \<and>
       thesis pr = sub_formula
         (\<lambda>v. if v = ''a''
                then Conn c ((map Atom (canonical_atoms c))[i := Atom ''a''])
              else if v = ''b''
                then Conn c ((map Atom (canonical_atoms c))[i := Atom ''b''])
              else Atom v)
         conn_iff)"

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
           conn_iff"
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

(*
  Under distinguished + contains_atom, the unique-path property lets us
  rewrite plug: only the i_0-th child of \<chi> contributes to plug h \<tau> \<chi>; all
  siblings stay as they are. The proof of iff_congruent uses this to match
  the substituted base proof's thesis with the lemma's sub'.
*)
lemma plug_under_distinguished:
  assumes "distinguished \<chi> h" "contains_atom \<chi> h"
  shows "\<chi> = Atom h \<or>
         (\<exists>c' fs i_0. \<chi> = Conn c' fs \<and> i_0 < length fs \<and>
                       contains_atom (fs ! i_0) h \<and>
                       distinguished (fs ! i_0) h \<and>
                       (\<forall>j < length fs. j \<noteq> i_0 \<longrightarrow> \<not> contains_atom (fs ! j) h))"
proof (cases \<chi>)
  case (Atom a)
  hence "a = h" using assms(2) by simp
  thus ?thesis using Atom by simp
next
  case (Conn c' fs)
  have witness: "\<exists>f \<in> set fs. contains_atom f h"
    using assms(2) Conn by simp
  hence uniq: "\<exists>!i. i < length fs \<and> contains_atom (fs ! i) h"
    using assms(1) Conn by simp
  have dist_children: "\<forall>f \<in> set fs. distinguished f h"
    using assms(1) Conn witness by simp
  obtain i_0 where i_0_props: "i_0 < length fs" "contains_atom (fs ! i_0) h"
    using uniq by auto
  have others: "\<forall>j < length fs. j \<noteq> i_0 \<longrightarrow> \<not> contains_atom (fs ! j) h"
    using uniq i_0_props by blast
  have dist_i_0: "distinguished (fs ! i_0) h"
    using dist_children i_0_props nth_mem by blast
  show ?thesis
    using Conn i_0_props others dist_i_0 by blast
qed

lemma plug_distinguished_unfold:
  assumes "distinguished (Conn c' fs) h"
  assumes "contains_atom (Conn c' fs) h"
  assumes "i_0 < length fs"
  assumes "contains_atom (fs ! i_0) h"
  shows "plug h \<tau> (Conn c' fs) = Conn c' (fs[i_0 := plug h \<tau> (fs ! i_0)])"
proof -
  have witness: "\<exists>f \<in> set fs. contains_atom f h"
    using assms(2) by simp
  have uniq: "\<exists>!i. i < length fs \<and> contains_atom (fs ! i) h"
    using assms(1) witness by simp
  have others: "\<And>j. j < length fs \<Longrightarrow> j \<noteq> i_0 \<Longrightarrow> \<not> contains_atom (fs ! j) h"
    using uniq assms(3,4) by blast
  let ?sub = "\<lambda>v. if v = h then \<tau> else Atom v"
  have map_eq:
    "map (sub_formula ?sub) fs = (fs[i_0 := sub_formula ?sub (fs ! i_0)])"
  proof (rule nth_equalityI)
    show "length (map (sub_formula ?sub) fs) = length (fs[i_0 := sub_formula ?sub (fs ! i_0)])"
      by simp
  next
    fix j
    assume "j < length (map (sub_formula ?sub) fs)"
    hence j_lt: "j < length fs" by simp
    show "map (sub_formula ?sub) fs ! j = (fs[i_0 := sub_formula ?sub (fs ! i_0)]) ! j"
    proof (cases "j = i_0")
      case True
      hence "(fs[i_0 := sub_formula ?sub (fs ! i_0)]) ! j = sub_formula ?sub (fs ! i_0)"
        using assms(3) by simp
      moreover have "map (sub_formula ?sub) fs ! j = sub_formula ?sub (fs ! j)"
        using j_lt by simp
      ultimately show ?thesis using True by simp
    next
      case False
      hence not_contains_j: "\<not> contains_atom (fs ! j) h"
        using others j_lt by blast
      have "sub_formula ?sub (fs ! j) = fs ! j"
        using not_contains_imp_plug_id[OF not_contains_j, of \<tau>]
        unfolding plug_def by simp
      hence "map (sub_formula ?sub) fs ! j = fs ! j"
        using j_lt by simp
      moreover have "(fs[i_0 := sub_formula ?sub (fs ! i_0)]) ! j = fs ! j"
        using False j_lt by (simp add: nth_list_update)
      ultimately show ?thesis by simp
    qed
  qed
  have "plug h \<tau> (Conn c' fs) = Conn c' (map (sub_formula ?sub) fs)"
    unfolding plug_def by simp
  also have "\<dots> = Conn c' (fs[i_0 := sub_formula ?sub (fs ! i_0)])"
    using map_eq by simp
  also have "\<dots> = Conn c' (fs[i_0 := plug h \<tau> (fs ! i_0)])"
    unfolding plug_def by simp
  finally show ?thesis .
qed

(*
  Inductive core of lemma 3.2: structural induction along the unique path
  from the root of \<chi> down to h. The bounds are explicit in the universal
  constants base_max_steps, base_max_step_len, base_max_step_depth so that
  the polynomial in the public statement of iff_congruent can be read off
  directly.
*)
lemma iff_congruent_inductive:
  fixes \<phi> \<psi> \<chi> :: "'c formula" and h :: string
  assumes "distinguished \<chi> h" "contains_atom \<chi> h"
  assumes "formula_well_formed (alphabet F) \<chi>"
  shows "\<exists>pr. valid_proof F pr \<and>
              assumptions pr = {sub_formula
                                  (\<lambda>v. if v = ''a'' then \<phi>
                                       else if v = ''b'' then \<psi>
                                       else Atom v)
                                  conn_iff} \<and>
              thesis pr = sub_formula
                            (\<lambda>v. if v = ''a'' then plug h \<phi> \<chi>
                                 else if v = ''b'' then plug h \<psi> \<chi>
                                 else Atom v)
                            conn_iff \<and>
              length (steps pr) \<le> base_max_steps * hole_depth \<chi> h + 1 \<and>
              (\<forall>step \<in> set (steps pr).
                 len_formula step \<le>
                   base_max_step_len * (1 + 2 * len_formula \<chi> * max (len_formula \<phi>) (len_formula \<psi>) + len_formula \<chi>) \<and>
                 depth_formula step \<le>
                   max (depth_formula \<phi>) (depth_formula \<psi>) + depth_formula \<chi> + base_max_step_depth)"
  using assms
proof (induction \<chi>)
  case (Atom a)
  let ?sub  = "\<lambda>v. if v = ''a'' then \<phi> else if v = ''b'' then \<psi> else Atom v"
  let ?sub' = "\<lambda>v. if v = ''a'' then plug h \<phi> (Atom a)
                  else if v = ''b'' then plug h \<psi> (Atom a) else Atom v"
  let ?s1 = "max (len_formula \<phi>) (len_formula \<psi>)"
  let ?d1 = "max (depth_formula \<phi>) (depth_formula \<psi>)"

  have a_eq_h: "a = h" using Atom.prems(2) by simp
  have plug_phi: "plug h \<phi> (Atom a) = \<phi>" using a_eq_h unfolding plug_def by simp
  have plug_psi: "plug h \<psi> (Atom a) = \<psi>" using a_eq_h unfolding plug_def by simp
  have subs_eq: "?sub' = ?sub" using plug_phi plug_psi by auto

  let ?stmt = "sub_formula ?sub conn_iff"
  define pr where
    pr_def: "pr = \<lparr>assumptions = {?stmt}, thesis = ?stmt, steps = [?stmt]\<rparr>"

  have valid: "valid_proof F pr"
    unfolding pr_def valid_proof_def by simp
  have asm: "assumptions pr = {?stmt}" unfolding pr_def by simp
  have thes: "thesis pr = sub_formula ?sub' conn_iff"
    unfolding pr_def using subs_eq by simp
  have len_pr: "length (steps pr) \<le> base_max_steps * hole_depth (Atom a) h + 1"
    unfolding pr_def by simp

  have phi_len_ge_1: "len_formula \<phi> \<ge> 1" by (rule len_formula_positive)
  have psi_len_ge_1: "len_formula \<psi> \<ge> 1" by (rule len_formula_positive)
  have s1_ge_1: "?s1 \<ge> 1" using phi_len_ge_1 by simp

  (* Length bound for ?stmt *)
  have len_sub_bound:
    "len_sub {''a'', ''b''} ?sub \<le> 2 * ?s1"
  proof -
    have "len_sub {''a'', ''b''} ?sub
            = max 1 (len_formula \<phi> + len_formula \<psi>)"
      unfolding len_sub_def by simp
    also have "\<dots> \<le> 2 * ?s1"
      using s1_ge_1 by simp
    finally show ?thesis .
  qed
  have stmt_len: "len_formula ?stmt \<le> len_formula conn_iff * (2 * ?s1)"
  proof -
    have "len_formula ?stmt \<le> len_formula conn_iff * len_sub {''a'', ''b''} ?sub"
      by (rule sub_formula_bound) auto
    also have "\<dots> \<le> len_formula conn_iff * (2 * ?s1)"
      using len_sub_bound by (rule mult_left_mono) simp
    finally show ?thesis .
  qed

  have ci_le_M: "len_formula conn_iff \<le> base_max_step_len"
    by (rule base_max_step_len_conn_iff)

  have stmt_len_final:
    "len_formula ?stmt \<le> base_max_step_len * (1 + 2 * len_formula (Atom a) * ?s1 + len_formula (Atom a))"
  proof -
    have "len_formula ?stmt \<le> len_formula conn_iff * (2 * ?s1)" using stmt_len .
    also have "\<dots> \<le> base_max_step_len * (2 * ?s1)"
      using ci_le_M by (rule mult_right_mono) simp
    also have "\<dots> \<le> base_max_step_len * (2 + 2 * ?s1)"
      by (rule mult_left_mono) simp_all
    also have "\<dots> = base_max_step_len * (1 + 2 * len_formula (Atom a) * ?s1 + len_formula (Atom a))"
      by simp
    finally show ?thesis .
  qed

  (* Depth bound for ?stmt *)
  have phi_d_ge_1: "depth_formula \<phi> \<ge> 1"
    by (cases \<phi>) auto
  have d1_ge_1: "?d1 \<ge> 1" using phi_d_ge_1 by simp
  have depth_sub_bound: "depth_sub {''a'', ''b''} ?sub \<le> ?d1"
  proof -
    have "(\<lambda>v. depth_formula (?sub v)) ` {''a'', ''b''} = {depth_formula \<phi>, depth_formula \<psi>}"
      by auto
    hence eq: "depth_sub {''a'', ''b''} ?sub
             = Max (insert 1 {depth_formula \<phi>, depth_formula \<psi>})"
      unfolding depth_sub_def by simp
    have "Max (insert 1 {depth_formula \<phi>, depth_formula \<psi>}) \<le> ?d1"
    proof (rule Max.boundedI)
      show "finite (insert 1 {depth_formula \<phi>, depth_formula \<psi>})" by simp
      show "insert 1 {depth_formula \<phi>, depth_formula \<psi>} \<noteq> {}" by simp
      fix x assume "x \<in> insert 1 {depth_formula \<phi>, depth_formula \<psi>}"
      thus "x \<le> ?d1" using d1_ge_1 by auto
    qed
    thus ?thesis using eq by simp
  qed
  have stmt_depth: "depth_formula ?stmt \<le> depth_formula conn_iff + ?d1"
  proof -
    have "depth_formula ?stmt \<le> depth_formula conn_iff + depth_sub {''a'', ''b''} ?sub"
      by (rule sub_formula_depth_bound) auto
    also have "\<dots> \<le> depth_formula conn_iff + ?d1"
      using depth_sub_bound by simp
    finally show ?thesis .
  qed
  have ci_d_le_D: "depth_formula conn_iff \<le> base_max_step_depth"
    by (rule base_max_step_depth_conn_iff)
  have stmt_depth_final:
    "depth_formula ?stmt \<le> ?d1 + depth_formula (Atom a) + base_max_step_depth"
  proof -
    have "depth_formula ?stmt \<le> depth_formula conn_iff + ?d1" using stmt_depth .
    also have "\<dots> \<le> base_max_step_depth + ?d1" using ci_d_le_D by simp
    also have "\<dots> \<le> ?d1 + depth_formula (Atom a) + base_max_step_depth" by linarith
    finally show ?thesis .
  qed

  have step_bnd:
    "\<forall>step \<in> set (steps pr).
       len_formula step \<le> base_max_step_len * (1 + 2 * len_formula (Atom a) * ?s1 + len_formula (Atom a)) \<and>
       depth_formula step \<le> ?d1 + depth_formula (Atom a) + base_max_step_depth"
    unfolding pr_def
    using stmt_len_final stmt_depth_final by simp

  show ?case
    using valid asm thes len_pr step_bnd by blast
next
  case (Conn c' fs)
  let ?sub  = "\<lambda>v. if v = ''a'' then \<phi> else if v = ''b'' then \<psi> else Atom v"
  let ?sub' = "\<lambda>v. if v = ''a'' then plug h \<phi> (Conn c' fs)
                  else if v = ''b'' then plug h \<psi> (Conn c' fs) else Atom v"
  let ?s1 = "max (len_formula \<phi>) (len_formula \<psi>)"
  let ?d1 = "max (depth_formula \<phi>) (depth_formula \<psi>)"
  let ?al = "alphabet F"

  have dist: "distinguished (Conn c' fs) h" using Conn.prems(1) .
  have contains: "contains_atom (Conn c' fs) h" using Conn.prems(2) .
  have lm: "formula_well_formed (alphabet F) (Conn c' fs)" using Conn.prems(3) .

  have witness: "\<exists>f \<in> set fs. contains_atom f h" using contains by simp
  have uniq: "\<exists>!i. i < length fs \<and> contains_atom (fs ! i) h"
    using dist witness by simp
  obtain i_0 where i_0_props: "i_0 < length fs" "contains_atom (fs ! i_0) h"
    using uniq by auto
  have others_no_h: "\<And>j. j < length fs \<Longrightarrow> j \<noteq> i_0 \<Longrightarrow> \<not> contains_atom (fs ! j) h"
    using uniq i_0_props by blast
  have all_dist: "\<forall>f \<in> set fs. distinguished f h"
    using dist witness by simp
  have dist_i0: "distinguished (fs ! i_0) h"
    using all_dist i_0_props nth_mem by blast
  have lm_i0: "formula_well_formed (alphabet F) (fs ! i_0)"
    using lm i_0_props nth_mem by simp
  have len_fs_eq_arity: "length fs = arity (alphabet F) c'"
    using lm by simp
  have i_0_lt_arity: "i_0 < arity (alphabet F) c'"
    using i_0_props len_fs_eq_arity by simp
  have idx_in_set: "(c', i_0) \<in> base_index_set"
    unfolding base_index_set_def using i_0_lt_arity by simp

  let ?\<sigma> = "fs ! i_0"

  (* Apply IH to \<sigma> *)
  have IH_applied:
    "\<exists>pr. valid_proof F pr \<and>
          assumptions pr = {sub_formula ?sub conn_iff} \<and>
          thesis pr = sub_formula
                        (\<lambda>v. if v = ''a'' then plug h \<phi> ?\<sigma>
                             else if v = ''b'' then plug h \<psi> ?\<sigma>
                             else Atom v)
                        conn_iff \<and>
          length (steps pr) \<le> base_max_steps * hole_depth ?\<sigma> h + 1 \<and>
          (\<forall>step \<in> set (steps pr).
             len_formula step \<le>
               base_max_step_len * (1 + 2 * len_formula ?\<sigma> * ?s1 + len_formula ?\<sigma>) \<and>
             depth_formula step \<le> ?d1 + depth_formula ?\<sigma> + base_max_step_depth)"
    using Conn.IH[OF nth_mem[OF i_0_props(1)] dist_i0 i_0_props(2) lm_i0] .

  let ?sub_inner = "\<lambda>v. if v = ''a'' then plug h \<phi> ?\<sigma>
                       else if v = ''b'' then plug h \<psi> ?\<sigma> else Atom v"
  from IH_applied obtain pr_sigma where pr_sigma_props:
    "valid_proof F pr_sigma \<and>
     assumptions pr_sigma = {sub_formula ?sub conn_iff} \<and>
     frege_proof.thesis pr_sigma = sub_formula ?sub_inner conn_iff \<and>
     length (steps pr_sigma) \<le> base_max_steps * hole_depth ?\<sigma> h + 1 \<and>
     (\<forall>step \<in> set (steps pr_sigma).
        len_formula step \<le>
          base_max_step_len * (1 + 2 * len_formula ?\<sigma> * ?s1 + len_formula ?\<sigma>) \<and>
        depth_formula step \<le> ?d1 + depth_formula ?\<sigma> + base_max_step_depth)"
    by blast

  (* Base proof for (c', i_0) *)
  let ?canon = "canonical_atoms c'"
  let ?canon_a = "(map Atom ?canon)[i_0 := Atom ''a'']"
  let ?canon_b = "(map Atom ?canon)[i_0 := Atom ''b'']"
  let ?base_sub = "\<lambda>v. if v = ''a'' then Conn c' ?canon_a
                      else if v = ''b'' then Conn c' ?canon_b
                      else Atom v"
  let ?pr_b = "base_proof c' i_0"

  have b_props:
    "valid_proof F ?pr_b \<and>
     assumptions ?pr_b = {conn_iff} \<and>
     frege_proof.thesis ?pr_b = sub_formula ?base_sub conn_iff"
    using base_proof_spec[OF i_0_lt_arity] by simp

  have canon_len: "length ?canon = length fs"
    using canonical_atoms_spec len_fs_eq_arity by simp
  have canon_distinct: "distinct ?canon" using canonical_atoms_spec by simp
  have canon_no_a: "''a'' \<notin> set ?canon" using canonical_atoms_spec by simp
  have canon_no_b: "''b'' \<notin> set ?canon" using canonical_atoms_spec by simp

  (*
    Substitution that lifts the canonical base proof onto our actual context:
    the iff atoms ''a'', ''b'' get pointed at the inductive sides plug h \<phi> \<sigma>
    and plug h \<psi> \<sigma>, while each canonical atom canon!j is replaced by the
    actual j-th sibling fs!j. By canonical_atoms_spec these regions are
    disjoint, so the function is well-defined.
  *)
  let ?sub_lift = "\<lambda>v.
     if v = ''a'' then plug h \<phi> ?\<sigma>
     else if v = ''b'' then plug h \<psi> ?\<sigma>
     else case map_of (zip ?canon fs) v of
            None \<Rightarrow> Atom v
          | Some f' \<Rightarrow> f'"

  have canon_disj_ci: "set ?canon \<inter> var_set_form conn_iff = {}"
    using canonical_atoms_spec by simp

  have sl_a: "?sub_lift ''a'' = plug h \<phi> ?\<sigma>" by simp
  have sl_b: "?sub_lift ''b'' = plug h \<psi> ?\<sigma>" by simp

  have sl_canon: "\<And>j. j < length ?canon \<Longrightarrow> ?sub_lift (?canon ! j) = fs ! j"
  proof -
    fix j assume j_lt: "j < length ?canon"
    have canon_j_in: "?canon ! j \<in> set ?canon" using j_lt by simp
    have neq_a: "?canon ! j \<noteq> ''a''" using canon_no_a canon_j_in by auto
    have neq_b: "?canon ! j \<noteq> ''b''" using canon_no_b canon_j_in by auto
    have lookup: "map_of (zip ?canon fs) (?canon ! j) = Some (fs ! j)"
      using map_of_zip_nth_lookup[OF canon_distinct canon_len j_lt] .
    show "?sub_lift (?canon ! j) = fs ! j" using neq_a neq_b lookup by simp
  qed

  have sl_other: "\<And>v. v \<noteq> ''a'' \<Longrightarrow> v \<noteq> ''b'' \<Longrightarrow> v \<notin> set ?canon \<Longrightarrow> ?sub_lift v = Atom v"
  proof -
    fix v assume na: "v \<noteq> ''a''" and nb: "v \<noteq> ''b''" and nc: "v \<notin> set ?canon"
    have lookup_none: "map_of (zip ?canon fs) v = None"
      using map_of_zip_None_lookup[OF nc] .
    show "?sub_lift v = Atom v" using na nb lookup_none by simp
  qed

  (* On var_set_form conn_iff, ?sub_lift agrees with ?sub_inner *)
  have sl_eq_inner_on_ci:
    "\<forall>v \<in> var_set_form conn_iff. ?sub_lift v = ?sub_inner v"
  proof
    fix v assume v_in: "v \<in> var_set_form conn_iff"
    show "?sub_lift v = ?sub_inner v"
    proof (cases "v = ''a''")
      case True thus ?thesis by simp
    next
      case neq_a: False
      show ?thesis
      proof (cases "v = ''b''")
        case True thus ?thesis using neq_a by simp
      next
        case neq_b: False
        have not_canon: "v \<notin> set ?canon" using canon_disj_ci v_in by blast
        show ?thesis
          using sl_other[OF neq_a neq_b not_canon] neq_a neq_b by simp
      qed
    qed
  qed

  have ci_sub_lift_eq: "sub_formula ?sub_lift conn_iff = sub_formula ?sub_inner conn_iff"
    using sub_formula_agree[OF sl_eq_inner_on_ci] .

  (* Show the lifted ?canon_a list equals the plugged children list *)
  have lift_canon_a_eq:
    "map (sub_formula ?sub_lift) ?canon_a = fs[i_0 := plug h \<phi> ?\<sigma>]"
  proof (rule nth_equalityI)
    show "length (map (sub_formula ?sub_lift) ?canon_a) = length (fs[i_0 := plug h \<phi> ?\<sigma>])"
      using canon_len by simp
  next
    fix j assume j_lt_lhs: "j < length (map (sub_formula ?sub_lift) ?canon_a)"
    hence j_lt_canon: "j < length ?canon" by simp
    hence j_lt_fs: "j < length fs" using canon_len by simp
    have nth_map_eq:
      "map (sub_formula ?sub_lift) ?canon_a ! j = sub_formula ?sub_lift (?canon_a ! j)"
      using j_lt_lhs by simp
    show "map (sub_formula ?sub_lift) ?canon_a ! j = fs[i_0 := plug h \<phi> ?\<sigma>] ! j"
    proof (cases "j = i_0")
      case True
      have a_at_i: "?canon_a ! j = Atom ''a''"
        using True i_0_props(1) canon_len by simp
      have step1: "sub_formula ?sub_lift (?canon_a ! j) = sub_formula ?sub_lift (Atom ''a'')"
        using a_at_i by (rule arg_cong)
      have step2: "sub_formula ?sub_lift (Atom ''a'') = plug h \<phi> ?\<sigma>"
        using sl_a by simp
      have lhs_eq: "map (sub_formula ?sub_lift) ?canon_a ! j = plug h \<phi> ?\<sigma>"
        using nth_map_eq step1 step2 by simp
      have rhs_eq: "fs[i_0 := plug h \<phi> ?\<sigma>] ! j = plug h \<phi> ?\<sigma>"
        using True i_0_props(1) by simp
      show ?thesis using lhs_eq rhs_eq by simp
    next
      case False
      have c_at_j: "?canon_a ! j = Atom (?canon ! j)"
        using False j_lt_canon by (simp add: nth_list_update)
      have step1: "sub_formula ?sub_lift (?canon_a ! j) = sub_formula ?sub_lift (Atom (?canon ! j))"
        using c_at_j by (rule arg_cong)
      have step2: "sub_formula ?sub_lift (Atom (?canon ! j)) = ?sub_lift (?canon ! j)" by simp
      have step3: "?sub_lift (?canon ! j) = fs ! j" using sl_canon[OF j_lt_canon] .
      have lhs_eq: "map (sub_formula ?sub_lift) ?canon_a ! j = fs ! j"
        using nth_map_eq step1 step2 step3 by simp
      have rhs_eq: "fs[i_0 := plug h \<phi> ?\<sigma>] ! j = fs ! j"
        using False j_lt_fs by (simp add: nth_list_update)
      show ?thesis using lhs_eq rhs_eq by simp
    qed
  qed

  have lift_canon_b_eq:
    "map (sub_formula ?sub_lift) ?canon_b = fs[i_0 := plug h \<psi> ?\<sigma>]"
  proof (rule nth_equalityI)
    show "length (map (sub_formula ?sub_lift) ?canon_b) = length (fs[i_0 := plug h \<psi> ?\<sigma>])"
      using canon_len by simp
  next
    fix j assume j_lt_lhs: "j < length (map (sub_formula ?sub_lift) ?canon_b)"
    hence j_lt_canon: "j < length ?canon" by simp
    hence j_lt_fs: "j < length fs" using canon_len by simp
    have nth_map_eq:
      "map (sub_formula ?sub_lift) ?canon_b ! j = sub_formula ?sub_lift (?canon_b ! j)"
      using j_lt_lhs by simp
    show "map (sub_formula ?sub_lift) ?canon_b ! j = fs[i_0 := plug h \<psi> ?\<sigma>] ! j"
    proof (cases "j = i_0")
      case True
      have b_at_i: "?canon_b ! j = Atom ''b''"
        using True i_0_props(1) canon_len by simp
      have step1: "sub_formula ?sub_lift (?canon_b ! j) = sub_formula ?sub_lift (Atom ''b'')"
        using b_at_i by (rule arg_cong)
      have step2: "sub_formula ?sub_lift (Atom ''b'') = plug h \<psi> ?\<sigma>"
        using sl_b by simp
      have lhs_eq: "map (sub_formula ?sub_lift) ?canon_b ! j = plug h \<psi> ?\<sigma>"
        using nth_map_eq step1 step2 by simp
      have rhs_eq: "fs[i_0 := plug h \<psi> ?\<sigma>] ! j = plug h \<psi> ?\<sigma>"
        using True i_0_props(1) by simp
      show ?thesis using lhs_eq rhs_eq by simp
    next
      case False
      have c_at_j: "?canon_b ! j = Atom (?canon ! j)"
        using False j_lt_canon by (simp add: nth_list_update)
      have step1: "sub_formula ?sub_lift (?canon_b ! j) = sub_formula ?sub_lift (Atom (?canon ! j))"
        using c_at_j by (rule arg_cong)
      have step2: "sub_formula ?sub_lift (Atom (?canon ! j)) = ?sub_lift (?canon ! j)" by simp
      have step3: "?sub_lift (?canon ! j) = fs ! j" using sl_canon[OF j_lt_canon] .
      have lhs_eq: "map (sub_formula ?sub_lift) ?canon_b ! j = fs ! j"
        using nth_map_eq step1 step2 step3 by simp
      have rhs_eq: "fs[i_0 := plug h \<psi> ?\<sigma>] ! j = fs ! j"
        using False j_lt_fs by (simp add: nth_list_update)
      show ?thesis using lhs_eq rhs_eq by simp
    qed
  qed

  (* Apply plug_distinguished_unfold to relate the plugged Conn to plug-of-Conn *)
  have plug_eq_phi: "plug h \<phi> (Conn c' fs) = Conn c' (fs[i_0 := plug h \<phi> ?\<sigma>])"
    using plug_distinguished_unfold[OF dist contains i_0_props(1) i_0_props(2)] .
  have plug_eq_psi: "plug h \<psi> (Conn c' fs) = Conn c' (fs[i_0 := plug h \<psi> ?\<sigma>])"
    using plug_distinguished_unfold[OF dist contains i_0_props(1) i_0_props(2)] .

  let ?composed = "\<lambda>v. sub_formula ?sub_lift (?base_sub v)"
  have composed_a: "?composed ''a'' = plug h \<phi> (Conn c' fs)"
    using lift_canon_a_eq plug_eq_phi by simp
  have composed_b: "?composed ''b'' = plug h \<psi> (Conn c' fs)"
    using lift_canon_b_eq plug_eq_psi by simp

  have composed_eq_sub'_on_ci:
    "\<forall>v \<in> var_set_form conn_iff. ?composed v = ?sub' v"
  proof
    fix v assume v_in: "v \<in> var_set_form conn_iff"
    show "?composed v = ?sub' v"
    proof (cases "v = ''a''")
      case True thus ?thesis using composed_a by simp
    next
      case neq_a: False
      show ?thesis
      proof (cases "v = ''b''")
        case True thus ?thesis using composed_b neq_a by simp
      next
        case neq_b: False
        have not_canon: "v \<notin> set ?canon" using canon_disj_ci v_in by blast
        have "?composed v = sub_formula ?sub_lift (Atom v)" using neq_a neq_b by simp
        also have "\<dots> = ?sub_lift v" by simp
        also have "\<dots> = Atom v" using sl_other[OF neq_a neq_b not_canon] .
        finally show ?thesis using neq_a neq_b by simp
      qed
    qed
  qed

  have base_thesis_eq:
    "sub_formula ?sub_lift (sub_formula ?base_sub conn_iff) = sub_formula ?sub' conn_iff"
  proof -
    have "sub_formula ?sub_lift (sub_formula ?base_sub conn_iff)
            = sub_formula ?composed conn_iff"
      using sub_formula_comp[of ?sub_lift ?base_sub conn_iff] .
    also have "\<dots> = sub_formula ?sub' conn_iff"
      using sub_formula_agree[OF composed_eq_sub'_on_ci] .
    finally show ?thesis .
  qed

  (* Substitute pr_b *)
  have fs_F: "frege_system F"
    by (meson frege_balancing_axioms frege_balancing_def)

  let ?sub_pr_b = "sub_proof ?sub_lift ?pr_b"
  have spr_valid: "valid_proof F ?sub_pr_b"
    using frege_system.proof_substitution[OF fs_F, where pr = ?pr_b and sub = ?sub_lift] b_props
    by simp
  have spr_assms: "assumptions ?sub_pr_b = {sub_formula ?sub_lift conn_iff}"
    using b_props by simp
  have spr_thesis: "frege_proof.thesis ?sub_pr_b = sub_formula ?sub' conn_iff"
    using b_props base_thesis_eq by simp
  have spr_steps: "steps ?sub_pr_b = map (sub_formula ?sub_lift) (steps ?pr_b)"
    by simp

  (* Combine pr_sigma with substituted base *)
  have pr_sigma_valid: "valid_proof F pr_sigma" using pr_sigma_props by simp
  have steps_pr_sigma_ne: "steps pr_sigma \<noteq> []"
    using pr_sigma_valid unfolding valid_proof_def by simp
  have thesis_pr_sigma_eq: "frege_proof.thesis pr_sigma = sub_formula ?sub_inner conn_iff"
    using pr_sigma_props by simp
  have thesis_pr_sigma_last: "frege_proof.thesis pr_sigma = last (steps pr_sigma)"
    using pr_sigma_valid unfolding valid_proof_def by simp
  have thesis_in_steps: "frege_proof.thesis pr_sigma \<in> set (steps pr_sigma)"
    using thesis_pr_sigma_last steps_pr_sigma_ne by simp
  hence inner_in_steps: "sub_formula ?sub_inner conn_iff \<in> set (steps pr_sigma)"
    using thesis_pr_sigma_eq by simp

  let ?pr_combined = "combine_proofs pr_sigma ?sub_pr_b"
  have c_valid: "valid_proof F ?pr_combined"
    using frege_system.combining_valid_proofs[OF fs_F, of pr_sigma ?sub_pr_b]
          pr_sigma_valid spr_valid by blast

  have c_assms: "assumptions ?pr_combined = {sub_formula ?sub conn_iff}"
  proof -
    have "assumptions ?pr_combined =
            assumptions pr_sigma \<union> (assumptions ?sub_pr_b - set (steps pr_sigma))"
      by simp
    also have "\<dots> = {sub_formula ?sub conn_iff} \<union>
                     ({sub_formula ?sub_lift conn_iff} - set (steps pr_sigma))"
      using pr_sigma_props spr_assms by simp
    also have "\<dots> = {sub_formula ?sub conn_iff} \<union>
                     ({sub_formula ?sub_inner conn_iff} - set (steps pr_sigma))"
      using ci_sub_lift_eq by simp
    also have "\<dots> = {sub_formula ?sub conn_iff} \<union> {}"
      using inner_in_steps by simp
    also have "\<dots> = {sub_formula ?sub conn_iff}" by simp
    finally show ?thesis .
  qed

  have c_thesis: "frege_proof.thesis ?pr_combined = sub_formula ?sub' conn_iff"
    using spr_thesis by simp

  have c_steps: "steps ?pr_combined = steps pr_sigma @ steps ?sub_pr_b" by simp

  (* Length bound *)
  have base_len_bound: "length (steps ?pr_b) \<le> base_max_steps"
    using base_max_steps_bound[OF idx_in_set] .
  have spr_len_eq: "length (steps ?sub_pr_b) = length (steps ?pr_b)"
    by simp
  have spr_len_bound: "length (steps ?sub_pr_b) \<le> base_max_steps"
    using base_len_bound spr_len_eq by simp

  have hd_decr: "Suc (hole_depth ?\<sigma> h) \<le> hole_depth (Conn c' fs) h"
    using hole_depth_decreases[OF contains i_0_props(1) i_0_props(2)] by simp

  have c_len_bound: "length (steps ?pr_combined) \<le> base_max_steps * hole_depth (Conn c' fs) h + 1"
  proof -
    have "length (steps ?pr_combined) = length (steps pr_sigma) + length (steps ?sub_pr_b)"
      using c_steps by simp
    also have "\<dots> \<le> (base_max_steps * hole_depth ?\<sigma> h + 1) + base_max_steps"
      using pr_sigma_props spr_len_bound by simp
    also have "\<dots> = base_max_steps * Suc (hole_depth ?\<sigma> h) + 1"
      by (simp add: algebra_simps)
    also have "\<dots> \<le> base_max_steps * hole_depth (Conn c' fs) h + 1"
    proof -
      have "base_max_steps * Suc (hole_depth ?\<sigma> h) \<le> base_max_steps * hole_depth (Conn c' fs) h"
        using hd_decr by (rule mult_left_mono) simp
      thus ?thesis by simp
    qed
    finally show ?thesis .
  qed

  (* len_formula \<sigma> bounded by len_formula (Conn c' fs) *)
  have sigma_len_le_chi: "len_formula ?\<sigma> \<le> len_formula (Conn c' fs)"
  proof -
    have i_lt: "i_0 < length fs" using i_0_props(1) .
    have "len_formula (fs ! i_0) \<le> sum_list (map len_formula fs)"
      using i_lt
    proof (induction fs arbitrary: i_0)
      case Nil thus ?case by simp
    next
      case (Cons f fs')
      show ?case
      proof (cases i_0)
        case 0 thus ?thesis using Cons by simp
      next
        case (Suc i')
        have "i' < length fs'" using Cons.prems Suc by simp
        hence "len_formula (fs' ! i') \<le> sum_list (map len_formula fs')"
          using Cons.IH by simp
        thus ?thesis using Suc by simp
      qed
    qed
    thus ?thesis by simp
  qed

  have sigma_d_le_chi: "depth_formula ?\<sigma> \<le> depth_formula (Conn c' fs)"
  proof -
    have i_lt: "i_0 < length fs" using i_0_props(1) .
    hence "depth_formula (fs ! i_0) \<in> set (map depth_formula fs)" by auto
    moreover have ne_set: "set (map depth_formula fs) \<noteq> {}"
      using i_lt by auto
    moreover have fin: "finite (set (map depth_formula fs))" by simp
    ultimately have "depth_formula ?\<sigma> \<le> Max (set (map depth_formula fs))"
      by (auto intro: Max_ge)
    also have "\<dots> \<le> depth_formula (Conn c' fs)"
    proof -
      have fs_ne: "fs \<noteq> []" using i_lt by auto
      hence "length fs > 0" by simp
      hence "depth_formula (Conn c' fs) = 1 + Max (set (map depth_formula fs))" by simp
      thus ?thesis by simp
    qed
    finally show ?thesis .
  qed

  let ?chi = "Conn c' fs"
  let ?S2 = "len_formula ?chi"
  let ?D2 = "depth_formula ?chi"

  (* Bound len_sub for ?sub_lift *)
  let ?VS = "{''a'', ''b''} \<union> set ?canon"
  have fin_VS: "finite ?VS" by simp
  have ext_id_VS: "\<forall>v. v \<notin> ?VS \<longrightarrow> ?sub_lift v = Atom v"
    using sl_other by simp

  have plug_phi_len: "len_formula (plug h \<phi> ?\<sigma>) \<le> len_formula ?\<sigma> * ?s1"
  proof -
    let ?subh = "\<lambda>v. if v = h then \<phi> else Atom v"
    have fin_h: "finite {h}" by simp
    have ext_id_h: "\<forall>v. v \<notin> {h} \<longrightarrow> ?subh v = Atom v" by simp
    have "len_formula (sub_formula ?subh ?\<sigma>) \<le> len_formula ?\<sigma> * len_sub {h} ?subh"
      using sub_formula_bound[OF fin_h ext_id_h] .
    moreover have "len_sub {h} ?subh \<le> ?s1"
    proof -
      have "len_sub {h} ?subh = max 1 (len_formula \<phi>)"
        unfolding len_sub_def by simp
      also have "\<dots> = len_formula \<phi>"
        using len_formula_positive[of \<phi>] by simp
      also have "\<dots> \<le> ?s1" by simp
      finally show ?thesis .
    qed
    ultimately have "len_formula (sub_formula ?subh ?\<sigma>) \<le> len_formula ?\<sigma> * ?s1"
      using dual_order.trans mult_left_mono zero_le
      by (smt (verit, ccfv_SIG)) 
    thus ?thesis unfolding plug_def .
  qed

  have plug_psi_len: "len_formula (plug h \<psi> ?\<sigma>) \<le> len_formula ?\<sigma> * ?s1"
  proof -
    let ?subh = "\<lambda>v. if v = h then \<psi> else Atom v"
    have fin_h: "finite {h}" by simp
    have ext_id_h: "\<forall>v. v \<notin> {h} \<longrightarrow> ?subh v = Atom v" by simp
    have "len_formula (sub_formula ?subh ?\<sigma>) \<le> len_formula ?\<sigma> * len_sub {h} ?subh"
      using sub_formula_bound[OF fin_h ext_id_h] .
    moreover have "len_sub {h} ?subh \<le> ?s1"
    proof -
      have "len_sub {h} ?subh = max 1 (len_formula \<psi>)"
        unfolding len_sub_def by simp
      also have "\<dots> = len_formula \<psi>"
        using len_formula_positive[of \<psi>] by simp
      also have "\<dots> \<le> ?s1" by simp
      finally show ?thesis .
    qed
    ultimately have "len_formula (sub_formula ?subh ?\<sigma>) \<le> len_formula ?\<sigma> * ?s1"
      using dual_order.trans mult_left_mono zero_le
      by (smt (verit, best)) 
    thus ?thesis unfolding plug_def .
  qed

  have canon_sum_eq:
    "(\<Sum>v \<in> set ?canon. len_formula (?sub_lift v)) = sum_list (map len_formula fs)"
  proof -
    have step:
      "(\<Sum>v \<in> set ?canon. len_formula (?sub_lift v))
       = sum_list (map (\<lambda>v. len_formula (?sub_lift v)) ?canon)"
      using canon_distinct by (simp add: sum.distinct_set_conv_list)
    have map_eq: "map (\<lambda>v. len_formula (?sub_lift v)) ?canon = map len_formula fs"
    proof (rule nth_equalityI)
      show "length (map (\<lambda>v. len_formula (?sub_lift v)) ?canon) = length (map len_formula fs)"
        using canon_len by simp
    next
      fix j assume "j < length (map (\<lambda>v. len_formula (?sub_lift v)) ?canon)"
      hence j_lt: "j < length ?canon" by simp
      hence j_lt_fs: "j < length fs" using canon_len by simp
      have "map (\<lambda>v. len_formula (?sub_lift v)) ?canon ! j = len_formula (?sub_lift (?canon ! j))"
        using j_lt by simp
      also have "\<dots> = len_formula (fs ! j)" using sl_canon[OF j_lt] by simp
      also have "\<dots> = map len_formula fs ! j" using j_lt_fs by simp
      finally show "map (\<lambda>v. len_formula (?sub_lift v)) ?canon ! j = map len_formula fs ! j" .
    qed
    show ?thesis using step map_eq by simp
  qed

  have len_sub_lift_bound: "len_sub ?VS ?sub_lift \<le> 1 + 2 * ?S2 * ?s1 + ?S2"
  proof -
    have a_neq_b: "(''a'' :: string) \<noteq> ''b''" by simp
    have a_not_canon: "''a'' \<notin> set ?canon" using canon_no_a .
    have b_not_canon: "''b'' \<notin> set ?canon" using canon_no_b .
    have fin_canon: "finite (set ?canon)" by simp
    have sum_split:
      "(\<Sum>v \<in> ?VS. len_formula (?sub_lift v))
       = len_formula (?sub_lift ''a'') + len_formula (?sub_lift ''b'')
         + (\<Sum>v \<in> set ?canon. len_formula (?sub_lift v))"
    proof -
      have "(\<Sum>v \<in> insert ''a'' (insert ''b'' (set ?canon)). len_formula (?sub_lift v))
              = len_formula (?sub_lift ''a'')
                + (\<Sum>v \<in> insert ''b'' (set ?canon). len_formula (?sub_lift v))"
        using a_neq_b a_not_canon fin_canon by (simp add: sum.insert)
      also have "(\<Sum>v \<in> insert ''b'' (set ?canon). len_formula (?sub_lift v))
                  = len_formula (?sub_lift ''b'') + (\<Sum>v \<in> set ?canon. len_formula (?sub_lift v))"
        using b_not_canon fin_canon by (simp add: sum.insert)
      finally show ?thesis by simp
    qed

    have a_le: "len_formula (?sub_lift ''a'') \<le> ?S2 * ?s1"
    proof -
      have "len_formula (?sub_lift ''a'') = len_formula (plug h \<phi> ?\<sigma>)" using sl_a by simp
      also have "\<dots> \<le> len_formula ?\<sigma> * ?s1" using plug_phi_len .
      also have "\<dots> \<le> ?S2 * ?s1"
        using sigma_len_le_chi by (rule mult_right_mono) simp
      finally show ?thesis .
    qed
    have b_le: "len_formula (?sub_lift ''b'') \<le> ?S2 * ?s1"
    proof -
      have "len_formula (?sub_lift ''b'') = len_formula (plug h \<psi> ?\<sigma>)" using sl_b by simp
      also have "\<dots> \<le> len_formula ?\<sigma> * ?s1" using plug_psi_len .
      also have "\<dots> \<le> ?S2 * ?s1"
        using sigma_len_le_chi by (rule mult_right_mono) simp
      finally show ?thesis .
    qed
    have canon_sum_le: "(\<Sum>v \<in> set ?canon. len_formula (?sub_lift v)) \<le> ?S2"
    proof -
      have "(\<Sum>v \<in> set ?canon. len_formula (?sub_lift v)) = sum_list (map len_formula fs)"
        using canon_sum_eq .
      also have "\<dots> \<le> 1 + sum_list (map len_formula fs)" by simp
      also have "\<dots> = ?S2" by simp
      finally show ?thesis .
    qed
    have sum_bound:
      "(\<Sum>v \<in> ?VS. len_formula (?sub_lift v)) \<le> 2 * ?S2 * ?s1 + ?S2"
      using a_le b_le canon_sum_le sum_split by simp
    have "len_sub ?VS ?sub_lift = max 1 (\<Sum>v \<in> ?VS. len_formula (?sub_lift v))"
      unfolding len_sub_def by simp
    also have "\<dots> \<le> 1 + (\<Sum>v \<in> ?VS. len_formula (?sub_lift v))"
      by simp
    also have "\<dots> \<le> 1 + 2 * ?S2 * ?s1 + ?S2" using sum_bound by simp
    finally show ?thesis .
  qed

  (* Bound depth_sub for ?sub_lift *)
  have phi_d_ge_1: "depth_formula \<phi> \<ge> 1" by (cases \<phi>) auto
  have psi_d_ge_1: "depth_formula \<psi> \<ge> 1" by (cases \<psi>) auto

  have plug_phi_d: "depth_formula (plug h \<phi> ?\<sigma>) \<le> depth_formula ?\<sigma> + ?d1"
  proof -
    let ?subh = "\<lambda>v. if v = h then \<phi> else Atom v"
    have fin_h: "finite {h}" by simp
    have ext_id_h: "\<forall>v. v \<notin> {h} \<longrightarrow> ?subh v = Atom v" by simp
    have "depth_formula (sub_formula ?subh ?\<sigma>) \<le> depth_formula ?\<sigma> + depth_sub {h} ?subh"
      using sub_formula_depth_bound[OF fin_h ext_id_h] .
    moreover have "depth_sub {h} ?subh \<le> ?d1"
    proof -
      have "depth_sub {h} ?subh = Max (insert 1 {depth_formula \<phi>})"
        unfolding depth_sub_def by simp
      also have "\<dots> = max 1 (depth_formula \<phi>)" by simp
      also have "\<dots> = depth_formula \<phi>" using phi_d_ge_1 by simp
      also have "\<dots> \<le> ?d1" by simp
      finally show ?thesis .
    qed
    ultimately have "depth_formula (sub_formula ?subh ?\<sigma>) \<le> depth_formula ?\<sigma> + ?d1"
      by simp
    thus ?thesis unfolding plug_def .
  qed

  have plug_psi_d: "depth_formula (plug h \<psi> ?\<sigma>) \<le> depth_formula ?\<sigma> + ?d1"
  proof -
    let ?subh = "\<lambda>v. if v = h then \<psi> else Atom v"
    have fin_h: "finite {h}" by simp
    have ext_id_h: "\<forall>v. v \<notin> {h} \<longrightarrow> ?subh v = Atom v" by simp
    have "depth_formula (sub_formula ?subh ?\<sigma>) \<le> depth_formula ?\<sigma> + depth_sub {h} ?subh"
      using sub_formula_depth_bound[OF fin_h ext_id_h] .
    moreover have "depth_sub {h} ?subh \<le> ?d1"
    proof -
      have "depth_sub {h} ?subh = Max (insert 1 {depth_formula \<psi>})"
        unfolding depth_sub_def by simp
      also have "\<dots> = max 1 (depth_formula \<psi>)" by simp
      also have "\<dots> = depth_formula \<psi>" using psi_d_ge_1 by simp
      also have "\<dots> \<le> ?d1" by simp
      finally show ?thesis .
    qed
    ultimately have "depth_formula (sub_formula ?subh ?\<sigma>) \<le> depth_formula ?\<sigma> + ?d1"
      by simp
    thus ?thesis unfolding plug_def .
  qed

  have d1_pos: "?d1 \<ge> 1"
  proof -
    have "depth_formula \<phi> \<ge> 1" by (cases \<phi>) auto
    thus ?thesis by simp
  qed

  have depth_sub_lift_bound: "depth_sub ?VS ?sub_lift \<le> ?d1 + ?D2"
  proof -
    have D2_ge_1: "?D2 \<ge> 1" by (cases ?chi) auto
    have one_le: "(1 :: nat) \<le> ?d1 + ?D2" using d1_pos by simp
    have v_in_VS_bound:
      "\<And>v. v \<in> ?VS \<Longrightarrow> depth_formula (?sub_lift v) \<le> ?d1 + ?D2"
    proof -
      fix v assume v_in: "v \<in> ?VS"
      show "depth_formula (?sub_lift v) \<le> ?d1 + ?D2"
      proof (cases "v = ''a''")
        case True
        have "depth_formula (?sub_lift v) = depth_formula (plug h \<phi> ?\<sigma>)"
          using True sl_a by simp
        also have "\<dots> \<le> depth_formula ?\<sigma> + ?d1" using plug_phi_d .
        also have "\<dots> \<le> ?D2 + ?d1" using sigma_d_le_chi by simp
        finally show ?thesis by simp
      next
        case neq_a: False
        show ?thesis
        proof (cases "v = ''b''")
          case True
          have "depth_formula (?sub_lift v) = depth_formula (plug h \<psi> ?\<sigma>)"
            using True sl_b by simp
          also have "\<dots> \<le> depth_formula ?\<sigma> + ?d1" using plug_psi_d .
          also have "\<dots> \<le> ?D2 + ?d1" using sigma_d_le_chi by simp
          finally show ?thesis by simp
        next
          case neq_b: False
          have v_in_canon: "v \<in> set ?canon" using v_in neq_a neq_b by auto
          then obtain j where j_lt: "j < length ?canon" and v_eq: "v = ?canon ! j"
            by (auto simp: in_set_conv_nth)
          have sl_v_eq: "?sub_lift v = fs ! j"
          proof -
            have "?sub_lift v = ?sub_lift (?canon ! j)" using v_eq by (rule arg_cong)
            also have "\<dots> = fs ! j" using sl_canon[OF j_lt] .
            finally show ?thesis .
          qed
          have j_lt_fs: "j < length fs" using j_lt canon_len by simp
          have "depth_formula (fs ! j) \<le> ?D2"
          proof -
            have d_in: "depth_formula (fs ! j) \<in> set (map depth_formula fs)"
              using j_lt_fs by auto
            have ne_set_fs: "set (map depth_formula fs) \<noteq> {}"
              using j_lt_fs by auto
            have fin_set_fs: "finite (set (map depth_formula fs))" by simp
            have d_le_max: "depth_formula (fs ! j) \<le> Max (set (map depth_formula fs))"
              using fin_set_fs d_in by (rule Max_ge)
            have fs_ne: "fs \<noteq> []" using j_lt_fs by auto
            have "?D2 = 1 + Max (set (map depth_formula fs))"
              using fs_ne by simp
            thus ?thesis using d_le_max by simp
          qed
          hence "depth_formula (?sub_lift v) \<le> ?D2" using sl_v_eq by simp
          thus ?thesis by simp
        qed
      qed
    qed
    have all_le:
      "\<forall>x \<in> insert 1 ((\<lambda>v. depth_formula (?sub_lift v)) ` ?VS). x \<le> ?d1 + ?D2"
    proof
      fix x assume x_in: "x \<in> insert 1 ((\<lambda>v. depth_formula (?sub_lift v)) ` ?VS)"
      show "x \<le> ?d1 + ?D2"
      proof (cases "x = 1")
        case True
        thus ?thesis using one_le by simp
      next
        case False
        hence "x \<in> (\<lambda>v. depth_formula (?sub_lift v)) ` ?VS" using x_in by simp
        from imageE[OF this] obtain v where
          x_eq: "x = depth_formula (?sub_lift v)" and v_in: "v \<in> ?VS" by blast
        show ?thesis using v_in_VS_bound[OF v_in] x_eq by simp
      qed
    qed
    have fin_set: "finite (insert 1 ((\<lambda>v. depth_formula (?sub_lift v)) ` ?VS))" by simp
    have ne_set: "insert 1 ((\<lambda>v. depth_formula (?sub_lift v)) ` ?VS) \<noteq> {}" by simp
    have "Max (insert 1 ((\<lambda>v. depth_formula (?sub_lift v)) ` ?VS)) \<le> ?d1 + ?D2"
    proof (rule Max.boundedI)
      show "finite (insert 1 ((\<lambda>v. depth_formula (?sub_lift v)) ` ?VS))" using fin_set .
      show "insert 1 ((\<lambda>v. depth_formula (?sub_lift v)) ` ?VS) \<noteq> {}" using ne_set .
      fix a assume "a \<in> insert 1 ((\<lambda>v. depth_formula (?sub_lift v)) ` ?VS)"
      thus "a \<le> ?d1 + ?D2" using all_le by blast
    qed
    thus ?thesis unfolding depth_sub_def .
  qed

  (* Step length and depth bounds *)
  have step_bnd:
    "\<forall>step \<in> set (steps ?pr_combined).
       len_formula step \<le>
         base_max_step_len * (1 + 2 * ?S2 * ?s1 + ?S2) \<and>
       depth_formula step \<le> ?d1 + ?D2 + base_max_step_depth"
  proof
    fix step assume step_in: "step \<in> set (steps ?pr_combined)"
    have steps_split: "set (steps ?pr_combined) = set (steps pr_sigma) \<union> set (steps ?sub_pr_b)"
      using c_steps by simp
    from step_in steps_split consider
        (sigma) "step \<in> set (steps pr_sigma)"
      | (base) "step \<in> set (steps ?sub_pr_b)" by auto
    thus "len_formula step \<le> base_max_step_len * (1 + 2 * ?S2 * ?s1 + ?S2) \<and>
          depth_formula step \<le> ?d1 + ?D2 + base_max_step_depth"
    proof cases
      case sigma
      have len_step:
        "len_formula step \<le> base_max_step_len * (1 + 2 * len_formula ?\<sigma> * ?s1 + len_formula ?\<sigma>)"
        using pr_sigma_props sigma by blast
      have d_step:
        "depth_formula step \<le> ?d1 + depth_formula ?\<sigma> + base_max_step_depth"
        using pr_sigma_props sigma by blast
      have len_mono:
        "base_max_step_len * (1 + 2 * len_formula ?\<sigma> * ?s1 + len_formula ?\<sigma>)
         \<le> base_max_step_len * (1 + 2 * ?S2 * ?s1 + ?S2)"
      proof (rule mult_left_mono)
        have a: "len_formula ?\<sigma> \<le> ?S2" using sigma_len_le_chi .
        have "len_formula ?\<sigma> * ?s1 \<le> ?S2 * ?s1"
          using a by (rule mult_right_mono) simp
        hence b: "2 * len_formula ?\<sigma> * ?s1 \<le> 2 * ?S2 * ?s1" by simp
        show "1 + 2 * len_formula ?\<sigma> * ?s1 + len_formula ?\<sigma>
              \<le> 1 + 2 * ?S2 * ?s1 + ?S2"
          using a b by simp
      qed simp
      have d_mono: "?d1 + depth_formula ?\<sigma> + base_max_step_depth
                    \<le> ?d1 + ?D2 + base_max_step_depth"
        using sigma_d_le_chi by simp
      from len_step len_mono d_step d_mono show ?thesis by simp
    next
      case base
      then obtain orig where orig_in: "orig \<in> set (steps ?pr_b)" and step_eq: "step = sub_formula ?sub_lift orig"
        using spr_steps by auto
      have orig_len_bound: "len_formula orig \<le> base_max_step_len"
        using base_max_step_len_bound[OF idx_in_set orig_in] .
      have orig_d_bound: "depth_formula orig \<le> base_max_step_depth"
        using base_max_step_depth_bound[OF idx_in_set orig_in] .
      have step_len:
        "len_formula step \<le> len_formula orig * len_sub ?VS ?sub_lift"
        using sub_formula_bound[OF fin_VS ext_id_VS, of orig] step_eq by simp
      have step_d:
        "depth_formula step \<le> depth_formula orig + depth_sub ?VS ?sub_lift"
        using sub_formula_depth_bound[OF fin_VS ext_id_VS, of orig] step_eq by simp
      have len_step_bound:
        "len_formula step \<le> base_max_step_len * (1 + 2 * ?S2 * ?s1 + ?S2)"
      proof -
        have "len_formula step \<le> len_formula orig * len_sub ?VS ?sub_lift"
          using step_len .
        also have "\<dots> \<le> base_max_step_len * len_sub ?VS ?sub_lift"
          using orig_len_bound by (rule mult_right_mono) simp
        also have "\<dots> \<le> base_max_step_len * (1 + 2 * ?S2 * ?s1 + ?S2)"
          using len_sub_lift_bound by (rule mult_left_mono) simp
        finally show ?thesis .
      qed
      have d_step_bound:
        "depth_formula step \<le> ?d1 + ?D2 + base_max_step_depth"
      proof -
        have "depth_formula step \<le> depth_formula orig + depth_sub ?VS ?sub_lift"
          using step_d .
        also have "\<dots> \<le> base_max_step_depth + depth_sub ?VS ?sub_lift"
          using orig_d_bound by simp
        also have "\<dots> \<le> base_max_step_depth + (?d1 + ?D2)"
          using depth_sub_lift_bound by simp
        also have "\<dots> = ?d1 + ?D2 + base_max_step_depth" by simp
        finally show ?thesis .
      qed
      from len_step_bound d_step_bound show ?thesis by simp
    qed
  qed

  show ?case
    using c_valid c_assms c_thesis c_len_bound step_bnd by blast
qed

(* lemma 3.2: *)
lemma iff_congruent:
  shows "\<exists> c bound :: nat poly. \<forall> \<phi> \<psi> \<chi> h.
           let sub  = \<lambda>v. if v = ''a'' then \<phi> else if v = ''b'' then \<psi> else Atom v;
               sub' = \<lambda>v. if v = ''a'' then plug h \<phi> \<chi>
                         else if v = ''b'' then plug h \<psi> \<chi> else Atom v;
               s1 = max (len_formula \<phi>) (len_formula \<psi>);
               s2 = len_formula \<chi>;
               d1 = max (depth_formula \<phi>) (depth_formula \<psi>);
               d2 = depth_formula \<chi>
           in distinguished \<chi> h \<and> contains_atom \<chi> h \<and> formula_well_formed (alphabet F) \<chi> \<longrightarrow>
           (\<exists> pr. valid_proof F pr \<and>
              assumptions pr = {sub_formula sub conn_iff} \<and>
              thesis pr = (sub_formula sub' conn_iff) \<and>
              length (steps pr) \<le> poly bound s2 \<and>
              (\<forall> step \<in> set (steps pr). len_formula step \<le> poly bound (s1 + s2) \<and>
                                        depth_formula step \<le> d1 + d2 + c))"
proof -
  let ?N = "base_max_steps"
  let ?M = "base_max_step_len"
  let ?D = "base_max_step_depth"
  define K :: nat where K_def: "K = ?N + ?M + 1"
  define bnd :: "nat poly" where bnd_def: "bnd = [: K, K, K :]"

  have K_ge_N: "K \<ge> ?N" unfolding K_def by simp
  have K_ge_M: "K \<ge> ?M" unfolding K_def by simp
  have K_ge_1: "K \<ge> 1" unfolding K_def by simp

  have poly_eval: "\<And>x. poly bnd x = K + K * x + K * x * x"
    unfolding bnd_def by (simp add: algebra_simps)

  show ?thesis
  proof (intro exI[where x="?D"] exI[where x="bnd"] allI impI)
    fix \<phi> \<psi> \<chi> :: "'c formula" and h :: string
    let ?sub  = "\<lambda>v. if v = ''a'' then \<phi> else if v = ''b'' then \<psi> else Atom v"
    let ?sub' = "\<lambda>v. if v = ''a'' then plug h \<phi> \<chi>
                    else if v = ''b'' then plug h \<psi> \<chi> else Atom v"
    let ?s1 = "max (len_formula \<phi>) (len_formula \<psi>)"
    let ?s2 = "len_formula \<chi>"
    let ?d1 = "max (depth_formula \<phi>) (depth_formula \<psi>)"
    let ?d2 = "depth_formula \<chi>"

    show "let sub  = \<lambda>v. if v = ''a'' then \<phi> else if v = ''b'' then \<psi> else Atom v;
              sub' = \<lambda>v. if v = ''a'' then plug h \<phi> \<chi>
                         else if v = ''b'' then plug h \<psi> \<chi> else Atom v;
              s1 = max (len_formula \<phi>) (len_formula \<psi>);
              s2 = len_formula \<chi>;
              d1 = max (depth_formula \<phi>) (depth_formula \<psi>);
              d2 = depth_formula \<chi>
          in distinguished \<chi> h \<and> contains_atom \<chi> h \<and> formula_well_formed (alphabet F) \<chi> \<longrightarrow>
          (\<exists> pr. valid_proof F pr \<and>
              assumptions pr = {sub_formula sub conn_iff} \<and>
              thesis pr = (sub_formula sub' conn_iff) \<and>
              length (steps pr) \<le> poly bnd s2 \<and>
              (\<forall> step \<in> set (steps pr). len_formula step \<le> poly bnd (s1 + s2) \<and>
                                        depth_formula step \<le> d1 + d2 + ?D))"
      unfolding Let_def
    proof (intro impI)
      assume preconds: "distinguished \<chi> h \<and> contains_atom \<chi> h \<and> formula_well_formed (alphabet F) \<chi>"
      hence dist: "distinguished \<chi> h" and contains: "contains_atom \<chi> h"
        and lm: "formula_well_formed (alphabet F) \<chi>" by simp_all

      have ind: "\<exists>pr. valid_proof F pr \<and>
         assumptions pr = {sub_formula ?sub conn_iff} \<and>
         frege_proof.thesis pr = sub_formula ?sub' conn_iff \<and>
         length (steps pr) \<le> ?N * hole_depth \<chi> h + 1 \<and>
         (\<forall>step \<in> set (steps pr).
            len_formula step \<le> ?M * (1 + 2 * ?s2 * ?s1 + ?s2) \<and>
            depth_formula step \<le> ?d1 + ?d2 + ?D)"
        using iff_congruent_inductive[OF dist contains lm, of \<phi> \<psi>] by simp
      from ind obtain pr where pr_props:
        "valid_proof F pr \<and>
         assumptions pr = {sub_formula ?sub conn_iff} \<and>
         frege_proof.thesis pr = sub_formula ?sub' conn_iff \<and>
         length (steps pr) \<le> ?N * hole_depth \<chi> h + 1 \<and>
         (\<forall>step \<in> set (steps pr).
            len_formula step \<le> ?M * (1 + 2 * ?s2 * ?s1 + ?s2) \<and>
            depth_formula step \<le> ?d1 + ?d2 + ?D)"
        by blast
      have pr_valid: "valid_proof F pr" using pr_props by simp
      have pr_assms: "assumptions pr = {sub_formula ?sub conn_iff}" using pr_props by simp
      have pr_thesis: "thesis pr = sub_formula ?sub' conn_iff" using pr_props by simp
      have pr_len: "length (steps pr) \<le> ?N * hole_depth \<chi> h + 1" using pr_props by simp
      have pr_step:
        "\<forall>step \<in> set (steps pr).
           len_formula step \<le> ?M * (1 + 2 * ?s2 * ?s1 + ?s2) \<and>
           depth_formula step \<le> ?d1 + ?d2 + ?D"
        using pr_props by simp

      have hole_le_len: "hole_depth \<chi> h \<le> len_formula \<chi>"
        by (rule hole_depth_le_len)

      (* Length bound: ?N * hole_depth + 1 \<le> poly bnd s2 *)
      have len_pr_bound: "length (steps pr) \<le> poly bnd ?s2"
      proof -
        have "length (steps pr) \<le> ?N * hole_depth \<chi> h + 1" by (rule pr_len)
        also have "\<dots> \<le> ?N * ?s2 + 1" using hole_le_len by simp
        also have "\<dots> \<le> K * ?s2 + 1" using K_ge_N by (simp add: mult_right_mono)
        also have "\<dots> \<le> K + K * ?s2 + K * ?s2 * ?s2" using K_ge_1 by simp
        also have "\<dots> = poly bnd ?s2" using poly_eval by simp
        finally show ?thesis .
      qed

      (* Step bounds *)
      have step_bound:
        "\<forall>step \<in> set (steps pr).
           len_formula step \<le> poly bnd (?s1 + ?s2) \<and>
           depth_formula step \<le> ?d1 + ?d2 + ?D"
      proof
        fix step assume step_in: "step \<in> set (steps pr)"
        from step_in pr_step have
          len_step: "len_formula step \<le> ?M * (1 + 2 * ?s2 * ?s1 + ?s2)" and
          depth_step: "depth_formula step \<le> ?d1 + ?d2 + ?D"
          by blast+
        have len_le_poly: "len_formula step \<le> poly bnd (?s1 + ?s2)"
        proof -
          let ?S = "?s1 + ?s2"
          have "len_formula step \<le> ?M * (1 + 2 * ?s2 * ?s1 + ?s2)"
            using len_step .
          also have "\<dots> = ?M + 2 * ?M * ?s2 * ?s1 + ?M * ?s2"
            by (simp add: algebra_simps)
          also have "\<dots> \<le> K + 2 * K * ?s2 * ?s1 + K * ?s2"
            using K_ge_M K_ge_1 by (simp add: add_mono mult_right_mono)
          also have "\<dots> \<le> K + K * ?S + K * ?S * ?S"
          proof -
            have s2_le_S: "?s2 \<le> ?S" by simp
            have s1s2_le_SS: "2 * ?s2 * ?s1 \<le> ?S * ?S"
            proof -
              have expand: "?S * ?S = ?s1 * ?s1 + 2 * ?s1 * ?s2 + ?s2 * ?s2"
                by (simp add: algebra_simps add_mult_distrib add_mult_distrib2)
              hence "?S * ?S \<ge> 2 * ?s1 * ?s2" by simp
              thus ?thesis by (simp add: algebra_simps)
            qed
            have K_s2: "K * ?s2 \<le> K * ?S"
              using s2_le_S by (rule mult_left_mono) simp
            have K_s1s2: "2 * K * ?s2 * ?s1 \<le> K * (?S * ?S)"
            proof -
              have "2 * K * ?s2 * ?s1 = K * (2 * ?s2 * ?s1)"
                by (simp add: algebra_simps)
              also have "\<dots> \<le> K * (?S * ?S)"
                using s1s2_le_SS by (rule mult_left_mono) simp
              finally show ?thesis .
            qed
            have lhs_eq: "K + 2 * K * ?s2 * ?s1 + K * ?s2 = K + 2 * K * ?s2 * ?s1 + K * ?s2"
              by simp
            show ?thesis using K_s2 K_s1s2 by (simp add: algebra_simps)
          qed
          also have "\<dots> = poly bnd ?S" using poly_eval by simp
          finally show ?thesis .
        qed
        from len_le_poly depth_step show
          "len_formula step \<le> poly bnd (?s1 + ?s2) \<and>
           depth_formula step \<le> ?d1 + ?d2 + ?D" by simp
      qed

      show "\<exists> pr. valid_proof F pr \<and>
              assumptions pr = {sub_formula ?sub conn_iff} \<and>
              thesis pr = sub_formula ?sub' conn_iff \<and>
              length (steps pr) \<le> poly bnd ?s2 \<and>
              (\<forall> step \<in> set (steps pr). len_formula step \<le> poly bnd (?s1 + ?s2) \<and>
                                        depth_formula step \<le> ?d1 + ?d2 + ?D)"
        using pr_valid pr_assms pr_thesis len_pr_bound step_bound by blast
    qed
  qed
qed

subsection  \<open>Lemma 4.1\<close>

definition dm_balancing where
  "dm_balancing = Conn Or [Conn And [Atom ''x'', Atom ''z''], 
                           Conn And [Atom ''y'', Conn Not [Atom ''z'']]]"

lemma balancing_formula_exists:
  shows "\<exists> f. formula_well_formed (alphabet F) f \<and> formulas_equiv dm_balancing dm_alphabet f (alphabet F)"
  by (meson frege_balancing_axioms frege_balancing_def frege_system.func_complete)
  
  
definition custom_balancing where
  "custom_balancing = (SOME f. formula_well_formed (alphabet F) f \<and> formulas_equiv dm_balancing dm_alphabet f (alphabet F))"

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
  using someI_ex[OF balancing_formula_exists] .

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

(* I do not formalise the lemma 4.1 to see what exact form would be the most useful *)

subsection \<open>Lemma 4.2\<close>


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
  "spira_threshold = 2 * Max ((arity (alphabet F)) ` (UNIV :: 'c set)) + 2"

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

paragraph \<open>(a)\<close>

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

(* Equivalent to the notation P_Q=1 etc.*)

fun fix_sub_formula :: "'c formula \<Rightarrow> bool \<Rightarrow> 'c formula \<Rightarrow> 'c formula" where
  "fix_sub_formula q b (Atom v) = (if (Atom v) = q then (if b then true_const else false_const)
                            else (Atom v))" |
  "fix_sub_formula q b (Conn c fs) = (if (Conn c fs) = q then (if b then true_const else false_const)
                                      else (Conn c (map (fix_sub_formula q b) fs)))"

lemma fix_sub_formula_eval:
  shows "eval (alphabet F) val p
         = (if eval (alphabet F) val q
            then eval (alphabet F) val (fix_sub_formula q True p)
            else eval (alphabet F) val (fix_sub_formula q False p))"
proof (induction p)
  case (Atom v)
  show ?case
  proof (cases "Atom v = q")
    case True
    hence q_eq: "q = Atom v" by simp
    have ftrue: "fix_sub_formula q True (Atom v) = true_const"
      by (subst q_eq) simp
    have ffalse: "fix_sub_formula q False (Atom v) = false_const"
      by (subst q_eq) simp
    show ?thesis
      using True ftrue ffalse true_const_eval false_const_eval by simp
  next
    case False
    thus ?thesis by simp
  qed
next
  case (Conn c fs)
  let ?ev = "eval (alphabet F) val"
  show ?case
  proof (cases "Conn c fs = q")
    case True
    thus ?thesis
      using true_const_eval false_const_eval by auto
  next
    case neq: False
    show ?thesis
    proof (cases "?ev q")
      case True
      have each: "\<And>a. a \<in> set fs \<Longrightarrow> ?ev a = ?ev (fix_sub_formula q True a)"
        using Conn.IH True by simp
      have map_eq: "map ?ev fs = map ?ev (map (fix_sub_formula q True) fs)"
      proof -
        have "map ?ev fs = map (\<lambda>a. ?ev (fix_sub_formula q True a)) fs"
          by (intro list.map_cong0) (simp add: each)
        thus ?thesis by simp
      qed
      have "?ev (Conn c fs) = conn_evals (alphabet F) c (map ?ev fs)" by simp
      also have "conn_evals (alphabet F) c (map ?ev fs)
                 = conn_evals (alphabet F) c (map ?ev (map (fix_sub_formula q True) fs))"
        by (subst map_eq) (rule refl)
      also have "\<dots> = ?ev (Conn c (map (fix_sub_formula q True) fs))" by simp
      finally show ?thesis using True neq by simp
    next
      case False
      have each: "\<And>a. a \<in> set fs \<Longrightarrow> ?ev a = ?ev (fix_sub_formula q False a)"
        using Conn.IH False by simp
      have map_eq: "map ?ev fs = map ?ev (map (fix_sub_formula q False) fs)"
      proof -
        have "map ?ev fs = map (\<lambda>a. ?ev (fix_sub_formula q False a)) fs"
          by (intro list.map_cong0) (simp add: each)
        thus ?thesis by simp
      qed
      have "?ev (Conn c fs) = conn_evals (alphabet F) c (map ?ev fs)" by simp
      also have "conn_evals (alphabet F) c (map ?ev fs)
                 = conn_evals (alphabet F) c (map ?ev (map (fix_sub_formula q False) fs))"
        by (subst map_eq) (rule refl)
      also have "\<dots> = ?ev (Conn c (map (fix_sub_formula q False) fs))" by simp
      finally show ?thesis using False neq by simp
    qed
  qed
qed

lemma fix_sub_formula_len_le:
  shows "len_formula (fix_sub_formula q b p) \<le> len_formula p"
proof (induction p)
  case (Atom v)
  show ?case
  proof (cases "Atom v = q")
    case True
    hence q_eq: "q = Atom v" by simp
    have "fix_sub_formula q b (Atom v)
        = (if b then true_const else false_const)"
      unfolding q_eq by simp
    thus ?thesis
      using true_const_len false_const_len by simp
  next
    case False
    thus ?thesis by simp
  qed
next
  case (Conn c fs)
  show ?case
  proof (cases "Conn c fs = q")
    case True
    hence q_eq: "q = Conn c fs" by simp
    have "fix_sub_formula q b (Conn c fs)
        = (if b then true_const else false_const)"
      unfolding q_eq by simp
    moreover have "len_formula (Conn c fs) \<ge> 1"
      by (rule len_formula_positive)
    ultimately show ?thesis
      using true_const_len false_const_len by simp
  next
    case False
    hence unfold: "fix_sub_formula q b (Conn c fs)
                 = Conn c (map (fix_sub_formula q b) fs)"
      by simp
    have "sum_list (map (len_formula \<circ> fix_sub_formula q b) fs)
        \<le> sum_list (map len_formula fs)"
    proof (rule sum_list_pointwise_le, intro ballI)
      fix x assume "x \<in> set fs"
      thus "(len_formula \<circ> fix_sub_formula q b) x \<le> len_formula x"
        using Conn.IH by simp
    qed
    thus ?thesis using unfold by simp
  qed
qed

lemma sum_list_len_lt_aux:
  assumes "g \<in> set fs"
      and "len_formula (fix_sub_formula q b g) < len_formula g"
  shows "sum_list (map (len_formula \<circ> fix_sub_formula q b) fs)
       < sum_list (map len_formula fs)"
  using assms
proof (induction fs)
  case Nil
  show ?case using Nil.prems by simp
next
  case (Cons a fs)
  show ?case
  proof (cases "g = a")
    case True
    have head: "len_formula (fix_sub_formula q b a) < len_formula a"
      using Cons.prems(2) True by simp
    have tail: "sum_list (map (len_formula \<circ> fix_sub_formula q b) fs)
              \<le> sum_list (map len_formula fs)"
    proof (induction fs)
      case Nil
      show ?case by simp
    next
      case (Cons a fs)
      have head_le: "len_formula (fix_sub_formula q b a) \<le> len_formula a"
        by (rule fix_sub_formula_len_le)
      from head_le Cons.IH
      have "len_formula (fix_sub_formula q b a)
            + sum_list (map (len_formula \<circ> fix_sub_formula q b) fs)
          \<le> len_formula a + sum_list (map len_formula fs)"
        by (rule add_mono)
      thus ?case by (simp add: o_def)
    qed
    from head tail show ?thesis by (simp add: o_def)
  next
    case False
    with Cons.prems(1) have g_in_fs: "g \<in> set fs" by simp
    hence "sum_list (map (len_formula \<circ> fix_sub_formula q b) fs)
         < sum_list (map len_formula fs)"
      using Cons.prems(2) Cons.IH by blast
    moreover have "len_formula (fix_sub_formula q b a) \<le> len_formula a"
      using fix_sub_formula_len_le by simp
    ultimately show ?thesis by (simp add: o_def)
  qed
qed

lemma fix_sub_formula_len_strict:
  assumes "is_subformula q p"
      and "len_formula q \<ge> 2"
    shows "len_formula (fix_sub_formula q b p) < len_formula p"
  using assms
proof (induction p)
  case (Atom v)
  from Atom.prems(1) have "q = Atom v" by simp
  hence "len_formula q = 1" by simp
  with Atom.prems(2) show ?case by simp
next
  case (Conn c fs)
  show ?case
  proof (cases "Conn c fs = q")
    case True
    hence q_eq: "q = Conn c fs" by simp
    have "fix_sub_formula q b (Conn c fs) = (if b then true_const else false_const)"
      unfolding q_eq by simp
    moreover have "len_formula (if b then true_const else false_const) = 1"
      using true_const_len false_const_len by simp
    ultimately have lhs_eq: "len_formula (fix_sub_formula q b (Conn c fs)) = 1"
      by simp
    have "len_formula (Conn c fs) \<ge> 2"
      using True Conn.prems(2) by simp
    thus ?thesis using lhs_eq by simp
  next
    case False
    from Conn.prems(1) False
    obtain g where g_in: "g \<in> set fs" and g_sub: "is_subformula q g"
      by auto
    have ih_g: "len_formula (fix_sub_formula q b g) < len_formula g"
      using Conn.IH g_in g_sub Conn.prems(2) by blast
    have unfold: "fix_sub_formula q b (Conn c fs)
                = Conn c (map (fix_sub_formula q b) fs)"
      using False by simp
    have sum_lt: "sum_list (map (len_formula \<circ> fix_sub_formula q b) fs)
                < sum_list (map len_formula fs)"
      using g_in ih_g by (rule sum_list_len_lt_aux)
    show ?thesis using unfold sum_lt by simp
  qed
qed


function (domintros) spira_trans :: "'c formula \<Rightarrow> 'c formula" where
  "spira_trans (Atom v) = (Atom v)" |
  "spira_trans (Conn c []) = (Conn c [])" |
  "spira_trans (Conn c (f # fs)) =
     (let p = Conn c (f # fs); q = spiras_sel p in
        if len_formula p < spira_threshold then p
        else balance (spira_trans (fix_sub_formula q True p))
                     (spira_trans (fix_sub_formula q False p))
                     (spira_trans q))"
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

lemma sub_in_cons_list_len_lt:
  assumes "is_subformula q g"
      and "g = f \<or> g \<in> set fs"
    shows "len_formula q < Suc (len_formula f + sum_list (map len_formula fs))"
proof -
  have "len_formula q \<le> len_formula g"
    using assms(1) is_subformula_len_le by simp
  also have "len_formula g \<le> sum_list (map len_formula (f # fs))"
    using assms(2) member_le_sum_list[where xs="map len_formula (f # fs)"] by auto
  also have "sum_list (map len_formula (f # fs))
           = Suc (len_formula f + sum_list (map len_formula fs)) - 1"
    by simp
  finally show ?thesis by simp
qed

lemma sum_fix_lt_when_q_in_tail:
  assumes "xb \<in> set fs"
      and "is_subformula q xb"
      and "len_formula q \<ge> 2"
    shows "len_formula (fix_sub_formula q b f)
         + sum_list (map (len_formula \<circ> fix_sub_formula q b) fs)
         < len_formula f + sum_list (map len_formula fs)"
proof -
  have head_le: "len_formula (fix_sub_formula q b f) \<le> len_formula f"
    by (rule fix_sub_formula_len_le)
  have child_lt: "len_formula (fix_sub_formula q b xb) < len_formula xb"
    using assms(2,3) by (rule fix_sub_formula_len_strict)
  have tail_lt: "sum_list (map (len_formula \<circ> fix_sub_formula q b) fs)
              < sum_list (map len_formula fs)"
    using assms(1) child_lt by (rule sum_list_len_lt_aux)
  from head_le tail_lt show ?thesis by simp
qed

lemma sum_fix_lt_when_q_is_head:
  assumes "is_subformula q f"
      and "len_formula q \<ge> 2"
    shows "len_formula (fix_sub_formula q b f)
         + sum_list (map (len_formula \<circ> fix_sub_formula q b) fs)
         < len_formula f + sum_list (map len_formula fs)"
proof -
  have head_lt: "len_formula (fix_sub_formula q b f) < len_formula f"
    using assms by (rule fix_sub_formula_len_strict)
  have tail_le: "sum_list (map (len_formula \<circ> fix_sub_formula q b) fs)
              \<le> sum_list (map len_formula fs)"
  proof (rule sum_list_pointwise_le, intro ballI)
    fix x assume "x \<in> set fs"
    show "(len_formula \<circ> fix_sub_formula q b) x \<le> len_formula x"
      using fix_sub_formula_len_le by simp
  qed
  from head_lt tail_le show ?thesis by simp
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

lemma spiras_sel_neq:
  assumes "formula_well_formed (alphabet F) p"
      and "len_formula p \<ge> 2"
    shows "spiras_sel p \<noteq> p"
proof
  assume "spiras_sel p = p"
  hence "len_formula (spiras_sel p) = len_formula p" by simp
  moreover have "len_formula (spiras_sel p) < len_formula p"
    using spiras_sel_pred_when_wf[OF assms] by simp
  ultimately show False by simp
qed

lemma fix_sub_formula_wf:
  assumes "formula_well_formed (alphabet F) p"
  shows "formula_well_formed (alphabet F) (fix_sub_formula q b p)"
  using assms
proof (induction p)
  case (Atom v)
  show ?case
    using true_const_wf false_const_wf by simp
next
  case (Conn c fs)
  show ?case
  proof (cases "Conn c fs = q")
    case True
    hence q_eq: "q = Conn c fs" by simp
    have "fix_sub_formula q b (Conn c fs) = (if b then true_const else false_const)"
      unfolding q_eq by simp
    thus ?thesis
      using true_const_wf false_const_wf by simp
  next
    case False
    hence unfold: "fix_sub_formula q b (Conn c fs)
                 = Conn c (map (fix_sub_formula q b) fs)"
      by simp
    from Conn.prems have "length fs = arity (alphabet F) c"
                     and child_wf: "\<forall> g \<in> set fs. formula_well_formed (alphabet F) g"
      by auto
    hence len_eq: "length (map (fix_sub_formula q b) fs) = arity (alphabet F) c"
      by simp
    have all_wf:
      "\<forall> g \<in> set (map (fix_sub_formula q b) fs).
         formula_well_formed (alphabet F) g"
      using child_wf Conn.IH by auto
    show ?thesis
      using unfold len_eq all_wf by simp
  qed
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
      let ?q = "spiras_sel ?p"
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
                (let p = Conn c (f1 # fs1); q = spiras_sel p in
                  if len_formula p < spira_threshold then p
                  else balance (spira_trans (fix_sub_formula q True p))
                               (spira_trans (fix_sub_formula q False p))
                               (spira_trans q))"
            using dom Conn Cons by (simp add: spira_trans.psimps(3))
          thus ?thesis using small Conn Cons by (simp add: Let_def)
        qed
        thus ?thesis using dom by simp
      next
        case big: False
        \<comment> \<open>At/above threshold: recursion fires; spiras_sel gives a strict
            subformula of length \<open>\<ge> 2\<close>.\<close>
        have wf_p: "formula_well_formed (alphabet F) ?p" using less.prems .
        have p_ge_threshold: "len_formula ?p \<ge> spira_threshold" using big by simp
        have p_ge_2: "len_formula ?p \<ge> 2"
          using p_ge_threshold spira_threshold_def by simp
        from spiras_sel_pred_when_wf[OF wf_p p_ge_2]
        have q_sub: "is_subformula ?q ?p"
         and q_lt: "len_formula ?q < len_formula ?p" by auto
        have q_neq: "?q \<noteq> ?p"
          using spiras_sel_neq[OF wf_p p_ge_2] .
        have q_ge_2: "len_formula ?q \<ge> 2"
          using spiras_sel_len_ge_2_when_wf[OF wf_p p_ge_threshold] .
        have wf_q: "formula_well_formed (alphabet F) ?q"
          using wf_p q_sub subformula_wf by blast
        have wf_T: "formula_well_formed (alphabet F) (fix_sub_formula ?q True ?p)"
          using wf_p by (rule fix_sub_formula_wf)
        have wf_F: "formula_well_formed (alphabet F) (fix_sub_formula ?q False ?p)"
          using wf_p by (rule fix_sub_formula_wf)
        have len_T: "len_formula (fix_sub_formula ?q True ?p) < len_formula ?p"
          using fix_sub_formula_len_strict[OF q_sub q_ge_2] .
        have len_F: "len_formula (fix_sub_formula ?q False ?p) < len_formula ?p"
          using fix_sub_formula_len_strict[OF q_sub q_ge_2] .
        from less.hyps[OF q_lt wf_q]
        have dom_q: "spira_trans_dom ?q"
         and ih_q: "\<forall> val. ?ev val ?q = ?ev val (spira_trans ?q)" by auto
        from less.hyps[OF len_T wf_T]
        have dom_T: "spira_trans_dom (fix_sub_formula ?q True ?p)"
         and ih_T: "\<forall> val. ?ev val (fix_sub_formula ?q True ?p)
                          = ?ev val (spira_trans (fix_sub_formula ?q True ?p))" by auto
        from less.hyps[OF len_F wf_F]
        have dom_F: "spira_trans_dom (fix_sub_formula ?q False ?p)"
         and ih_F: "\<forall> val. ?ev val (fix_sub_formula ?q False ?p)
                          = ?ev val (spira_trans (fix_sub_formula ?q False ?p))" by auto
        have dom_unfolded: "spira_trans_dom (Conn c (f1 # fs1))"
          apply (rule spira_trans.domintros)
          using Conn Cons dom_q dom_T dom_F big apply simp_all
          done
        hence dom: "spira_trans_dom ?p" using Conn Cons by simp
        have st_eq: "spira_trans ?p = balance (spira_trans (fix_sub_formula ?q True ?p))
                                              (spira_trans (fix_sub_formula ?q False ?p))
                                              (spira_trans ?q)"
        proof -
          have psimp: "spira_trans (Conn c (f1 # fs1)) =
                       (let p = Conn c (f1 # fs1); q = spiras_sel p in
                         if len_formula p < spira_threshold then p
                         else balance (spira_trans (fix_sub_formula q True p))
                                      (spira_trans (fix_sub_formula q False p))
                                      (spira_trans q))"
            using dom Conn Cons by (simp add: spira_trans.psimps(3))
          thus ?thesis using big Conn Cons by (simp add: Let_def)
        qed
        have eval_eq: "\<forall> val. ?ev val ?p = ?ev val (spira_trans ?p)"
        proof
          fix val
          have "?ev val (spira_trans ?p)
              = ?ev val (balance (spira_trans (fix_sub_formula ?q True ?p))
                                 (spira_trans (fix_sub_formula ?q False ?p))
                                 (spira_trans ?q))"
            using st_eq by simp
          also have "\<dots> = (if ?ev val (spira_trans ?q)
                           then ?ev val (spira_trans (fix_sub_formula ?q True ?p))
                           else ?ev val (spira_trans (fix_sub_formula ?q False ?p)))"
            by (rule balance_eval)
          also have "\<dots> = (if ?ev val ?q
                           then ?ev val (fix_sub_formula ?q True ?p)
                           else ?ev val (fix_sub_formula ?q False ?p))"
            using ih_T ih_F ih_q by simp
          also have "\<dots> = ?ev val ?p"
            using fix_sub_formula_eval[symmetric] by simp
          finally show "?ev val ?p = ?ev val (spira_trans ?p)" by simp
        qed
        from dom eval_eq show ?thesis by simp
      qed
    qed
  qed
qed

lemma trans_a:
  assumes "formula_well_formed (alphabet F) f"
  shows "formulas_equiv f (alphabet F) (spira_trans f) (alphabet F)"
  using spira_trans_dom_and_eval[OF assms]
  unfolding formulas_equiv_def by blast


paragraph \<open>(c)\<close>


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
  have "depth_formula (sub_formula ?sub custom_balancing)
      \<le> depth_formula custom_balancing + depth_sub ?vs ?sub"
    by (rule sub_formula_depth_bound[OF fin_vs wf_sub])
  moreover have "depth_sub ?vs ?sub
               = Max (insert 1 ((\<lambda>v. depth_formula (?sub v)) ` ?vs))"
    by (simp add: depth_sub_def)
  moreover have "(\<lambda>v. depth_formula (?sub v)) ` ?vs
               = {depth_formula x, depth_formula y, depth_formula z}"
    by auto
  ultimately show ?thesis using unfold by simp
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

lemma fix_sub_q_sum_bound:
  shows "is_subformula q p
       \<Longrightarrow> len_formula q + len_formula (fix_sub_formula q b p) \<le> len_formula p + 1"
proof (induction p)
  case (Atom v)
  hence "q = Atom v" by simp
  hence "len_formula q = 1" "len_formula (fix_sub_formula q b (Atom v)) = 1"
    using true_const_len false_const_len by auto
  thus ?case by simp
next
  case (Conn c fs)
  show ?case
  proof (cases "Conn c fs = q")
    case True
    hence q_eq: "q = Conn c fs" by simp
    have "fix_sub_formula q b (Conn c fs) = (if b then true_const else false_const)"
      unfolding q_eq by simp
    hence "len_formula (fix_sub_formula q b (Conn c fs)) = 1"
      using true_const_len false_const_len by simp
    moreover have "len_formula q = len_formula (Conn c fs)" using True by simp
    moreover have "len_formula (Conn c fs) \<ge> 1" by (rule len_formula_positive)
    ultimately show ?thesis by simp
  next
    case neq: False
    from Conn.prems neq
    obtain g where g_in: "g \<in> set fs" and g_sub: "is_subformula q g" by auto
    have ih_g: "len_formula q + len_formula (fix_sub_formula q b g)
              \<le> len_formula g + 1"
      using Conn.IH g_in g_sub by blast
    hence g_bound: "len_formula (fix_sub_formula q b g) + len_formula q
                  \<le> len_formula g + 1" by simp
    have unfold: "fix_sub_formula q b (Conn c fs)
                = Conn c (map (fix_sub_formula q b) fs)"
      using neq by simp
    have q_le_g: "len_formula q \<le> len_formula g"
      using g_sub is_subformula_len_le by simp
    have q_le_sum: "len_formula q \<le> sum_list (map len_formula fs)"
      using q_le_g g_in member_le_sum_list[where xs="map len_formula fs"]
      by (cases "g = g") fastforce+
    have sum_bound:
      "sum_list (map (len_formula \<circ> fix_sub_formula q b) fs) + len_formula q
       \<le> sum_list (map len_formula fs) + 1"
      using g_in g_bound q_le_g
    proof (induction fs)
      case Nil
      thus ?case by simp
    next
      case (Cons h hs)
      show ?case
      proof (cases "h = g")
        case True
        have other_le:
          "sum_list (map (len_formula \<circ> fix_sub_formula q b) hs)
           \<le> sum_list (map len_formula hs)"
        proof (rule sum_list_pointwise_le, intro ballI)
          fix x assume "x \<in> set hs"
          show "(len_formula \<circ> fix_sub_formula q b) x \<le> len_formula x"
            using fix_sub_formula_len_le by simp
        qed
        thus ?thesis using True g_bound by (simp add: o_def)
      next
        case False
        with Cons.prems(1) have g_in_hs: "g \<in> set hs" by simp
        from Cons.IH[OF g_in_hs Cons.prems(2,3)]
        have ih: "sum_list (map (len_formula \<circ> fix_sub_formula q b) hs)
                  + len_formula q
                \<le> sum_list (map len_formula hs) + 1" .
        have head_le: "len_formula (fix_sub_formula q b h) \<le> len_formula h"
          using fix_sub_formula_len_le by simp
        from ih head_le show ?thesis by (simp add: o_def)
      qed
    qed
    have "len_formula (fix_sub_formula q b (Conn c fs))
        = 1 + sum_list (map (len_formula \<circ> fix_sub_formula q b) fs)"
      using unfold by (simp add: o_def)
    moreover have "len_formula (Conn c fs) = 1 + sum_list (map len_formula fs)"
      by simp
    ultimately show ?thesis using sum_bound by simp
  qed
qed

lemma recursive_arg_len_bound_gen:
  fixes p :: "'c formula" and b :: bool
  assumes "formula_well_formed (alphabet F) p"
      and "len_formula p \<ge> spira_threshold"
      and "k = Max ((arity (alphabet F)) ` (UNIV :: 'c set))"
      and "k > 1"
    shows "(k + 1) * len_formula (spiras_sel p) \<le> k * len_formula p
         \<and> (k + 1) * len_formula (fix_sub_formula (spiras_sel p) b p)
            \<le> k * len_formula p + 2 * k + 1"
proof -
  let ?q = "spiras_sel p"
  have p_ge_2: "len_formula p \<ge> 2"
    using assms(2) unfolding spira_threshold_def by simp
  have p_ge_k: "len_formula p \<ge> k"
    using assms(2,3) unfolding spira_threshold_def by simp
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
  have fix_sum: "len_formula ?q + len_formula (fix_sub_formula ?q b p)
              \<le> len_formula p + 1"
    using sub by (rule fix_sub_q_sum_bound)
  have lower_in_nat: "(k + 1) * len_formula ?q \<ge> len_formula p - k"
    using lower by simp
  have "(k + 1) * len_formula (fix_sub_formula ?q b p)
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
  finally have fix_bound: "(k + 1) * len_formula (fix_sub_formula ?q b p)
                         \<le> k * len_formula p + 2 * k + 1" .
  show ?thesis using upper fix_bound by simp
qed

lemma recursive_arg_len_bound_one:
  fixes p :: "'c formula" and b :: bool
  assumes "formula_well_formed (alphabet F) p"
      and "len_formula p \<ge> spira_threshold"
      and "Max ((arity (alphabet F)) ` (UNIV :: 'c set)) = 1"
    shows "3 * len_formula (spiras_sel p) \<le> 2 * len_formula p
         \<and> 3 * len_formula (fix_sub_formula (spiras_sel p) b p)
            \<le> 2 * len_formula p + 3"
proof -
  let ?q = "spiras_sel p"
  have p_ge_2: "len_formula p \<ge> 2"
    using assms(2) unfolding spira_threshold_def by simp
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
  have fix_sum: "len_formula ?q + len_formula (fix_sub_formula ?q b p)
              \<le> len_formula p + 1"
    using sub by (rule fix_sub_q_sum_bound)
  have "3 * len_formula (fix_sub_formula ?q b p)
      \<le> 3 * (len_formula p + 1 - len_formula ?q)"
    using fix_sum by (intro mult_le_mono2) simp
  also have "3 * (len_formula p + 1 - len_formula ?q)
           = 3 * (len_formula p + 1) - 3 * len_formula ?q"
    using q_le_p by (simp add: diff_mult_distrib2)
  also have "\<dots> \<le> 3 * (len_formula p + 1) - len_formula p"
    using lower by simp
  also have "3 * (len_formula p + 1) - len_formula p = 2 * len_formula p + 3"
    by (simp add: algebra_simps)
  finally have fix_bound: "3 * len_formula (fix_sub_formula ?q b p)
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
           = (let p = Conn c (f1 # fs1); q = spiras_sel p in
              if len_formula p < spira_threshold then p
              else balance (spira_trans (fix_sub_formula q True p))
                           (spira_trans (fix_sub_formula q False p))
                           (spira_trans q))"
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
      have T_eq: "T = 2 * ?k + 2" using T_def spira_threshold_def by simp
      show ?thesis unfolding A_eq B_eq C_eq T_eq by (simp add: algebra_simps)
    next
      case False
      with kpos have keq: "?k = 1" by simp
      have A_eq: "A = 3" using A_def False by simp
      have B_eq: "B = 2" using B_def False by simp
      have C_eq: "C = 3" using C_def False by simp
      have T_eq: "T = 4" using T_def spira_threshold_def keq by simp
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
                         \<and> A * (len_formula (fix_sub_formula (spiras_sel p) b p) + 1)
                            \<le> B * len_formula p + C + A"
    proof -
      fix p :: "'c formula" and b :: bool
      assume wf: "formula_well_formed (alphabet F) p"
         and lenge: "len_formula p \<ge> T"
      have lenge_st: "len_formula p \<ge> spira_threshold"
        using lenge T_def by simp
      show "A * (len_formula (spiras_sel p) + 1) \<le> B * len_formula p + C + A
          \<and> A * (len_formula (fix_sub_formula (spiras_sel p) b p) + 1)
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
          let ?q = "spiras_sel ?p"
          let ?ft = "fix_sub_formula ?q True ?p"
          let ?ff = "fix_sub_formula ?q False ?p"

          have wf_p: "formula_well_formed (alphabet F) ?p" using less.prems .
          from spira_trans_dom_and_eval[OF wf_p]
          have dom_p: "spira_trans_dom ?p" by simp
          have st_unfold: "spira_trans ?p
                         = balance (spira_trans ?ft)
                                   (spira_trans ?ff)
                                   (spira_trans ?q)"
          proof -
            have psimp: "spira_trans (Conn cn (g # gs')) =
                  (let p = Conn cn (g # gs'); q = spiras_sel p in
                   if len_formula p < spira_threshold then p
                   else balance (spira_trans (fix_sub_formula q True p))
                                (spira_trans (fix_sub_formula q False p))
                                (spira_trans q))"
              using dom_p f_eq gs_eq
              by (simp add: spira_trans.psimps)
            thus ?thesis using f_ge_st f_eq gs_eq by (simp add: Let_def)
          qed

          have q_sub: "is_subformula ?q ?p"
            and q_lt: "len_formula ?q < len_formula ?p"
            using spiras_sel_pred_when_wf[OF wf_p f_ge_2] by auto
          have wf_q: "formula_well_formed (alphabet F) ?q"
            using wf_p q_sub subformula_wf by blast
          have wf_T: "formula_well_formed (alphabet F) ?ft"
            using wf_p by (rule fix_sub_formula_wf)
          have wf_F: "formula_well_formed (alphabet F) ?ff"
            using wf_p by (rule fix_sub_formula_wf)

          have q_ge_2: "len_formula ?q \<ge> 2"
            using spiras_sel_len_ge_2_when_wf[OF wf_p f_ge_st] .
          have ft_lt: "len_formula ?ft < len_formula ?p"
            using fix_sub_formula_len_strict[OF q_sub q_ge_2] .
          have ff_lt: "len_formula ?ff < len_formula ?p"
            using fix_sub_formula_len_strict[OF q_sub q_ge_2] .

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
            and ft_arg: "A * (len_formula ?ft + 1) \<le> B * len_formula ?p + C + A" by auto
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

paragraph \<open>(b)\<close>

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
      let ?q = "spiras_sel ?p"
      let ?ft = "fix_sub_formula ?q True ?p"
      let ?ff = "fix_sub_formula ?q False ?p"
      have wf_p: "formula_well_formed (alphabet F) ?p" using less.prems .
      have dom_p: "spira_trans_dom ?p"
        using spira_trans_dom_and_eval[OF wf_p] by simp
      show ?thesis
      proof (cases "len_formula ?p < spira_threshold")
        case True
        have psimp: "spira_trans (Conn cn (f1 # fs1)) =
                     (let p = Conn cn (f1 # fs1); q = spiras_sel p in
                       if len_formula p < spira_threshold then p
                       else balance (spira_trans (fix_sub_formula q True p))
                                    (spira_trans (fix_sub_formula q False p))
                                    (spira_trans q))"
          using dom_p Conn Cons by (simp add: spira_trans.psimps(3))
        have "spira_trans ?p = ?p"
          using psimp True Conn Cons by (simp add: Let_def)
        thus ?thesis using less.prems by simp
      next
        case big: False
        have ge: "len_formula ?p \<ge> spira_threshold" using big by simp
        have ge2: "len_formula ?p \<ge> 2"
          using ge spira_threshold_def by simp
        from spiras_sel_pred_when_wf[OF wf_p ge2]
        have q_sub: "is_subformula ?q ?p"
         and q_lt: "len_formula ?q < len_formula ?p" by auto
        have q_ge_2: "len_formula ?q \<ge> 2"
          using spiras_sel_len_ge_2_when_wf[OF wf_p ge] .
        have wf_q: "formula_well_formed (alphabet F) ?q"
          using wf_p q_sub subformula_wf by blast
        have wf_ft: "formula_well_formed (alphabet F) ?ft"
          using wf_p by (rule fix_sub_formula_wf)
        have wf_ff: "formula_well_formed (alphabet F) ?ff"
          using wf_p by (rule fix_sub_formula_wf)
        have ft_lt: "len_formula ?ft < len_formula ?p"
          using fix_sub_formula_len_strict[OF q_sub q_ge_2] .
        have ff_lt: "len_formula ?ff < len_formula ?p"
          using fix_sub_formula_len_strict[OF q_sub q_ge_2] .
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
                       (let p = Conn cn (f1 # fs1); q = spiras_sel p in
                         if len_formula p < spira_threshold then p
                         else balance (spira_trans (fix_sub_formula q True p))
                                      (spira_trans (fix_sub_formula q False p))
                                      (spira_trans q))"
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

subsection \<open>Lemma 5.1\<close>


(* theorem 1.1 *)
theorem proof_balancing:
  shows "\<exists> bound :: nat poly. \<exists> c :: real.
           \<forall> pr. valid_proof F pr \<and> assumptions pr = {} \<longrightarrow>
             (\<exists> pr'. valid_proof F pr'
                   \<and> assumptions pr' = {}
                   \<and> thesis pr' = thesis pr
                   \<and> len_proof pr' \<le> poly bound (len_proof pr)
                   \<and> (\<forall> line \<in> set (steps pr').
                        real (depth_formula line)
                        \<le> real (depth_formula (thesis pr))
                          + c * log 2 (real (len_formula line))))"
  sorry
end
end
