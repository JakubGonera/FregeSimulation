theory Translation
  imports Frege "HOL.Transcendental"
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

paragraph  \<open>Lemma 4.1\<close>

definition dm_balancing where
  "dm_balancing = Conn Or [Conn And [Atom ''x'', Atom ''z''], 
                           Conn And [Atom ''y'', Conn Not [Atom ''z'']]]"

lemma balancing_formula_exists:
  shows "\<exists> f. formula_well_formed (alphabet F) f \<and> formulas_equiv dm_balancing dm_alphabet f (alphabet F)"
  using frege_balancing_axioms frege_balancing_def frege_system_def by auto
  
  
definition custom_balancing where
  "custom_balancing = (SOME f. formula_well_formed (alphabet F) f \<and> formulas_equiv dm_balancing dm_alphabet f (alphabet F))"

(* I do not formalise the lemma 4.1 to see what exact form would be the most useful *)

paragraph \<open>Lemma 4.2\<close>


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

lemma nat_ceil_le:
  fixes k :: "nat"
    and n :: "nat"
  shows "(n + k) div (k + 1) \<le> n"
proof -
  have "(n + 1) * (k + 1) = n + k + (n * k + 1)"
    by (simp add: algebra_simps)
  hence "n + k < (n + 1) * (k + 1)"
    by simp
  hence "(n + k) div (k + 1) < n + 1"
    by (rule less_mult_imp_div_less)
  thus ?thesis by simp
qed

lemma spiras_selection:
  assumes "well_formed_formula (alphabet F) p"
      and "\<exists> c. p = Conn c fs" (* It's not a single atom *)
      and "k = Max ((arity (alphabet F)) ` (UNIV :: 'c set))"
      and "k > 1" (* k == 1 is a special case *)
  obtains q where
      "is_subformula q p"
      "(k + 1) * len_formula q \<ge> len_formula p"
      "(k + 1) * len_formula q \<le> k * len_formula p"
proof -
  let ?n = "len_formula p"
  let ?T = "(?n + k) div (k+1)" (* ceil(n/(k+1)) *)
  have p_ge_T: "len_formula p \<ge> ?T"
    using nat_ceil_le by simp
  from spira_descent obtain q where w:
    "is_subformula q p" "len_formula q \<ge> ?T"
    "\<forall> c \<in> children q. len_formula c < ?T"
    using p_ge_T by blast
  hence "(k + 1) * len_formula q \<ge> len_formula p"
  


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
