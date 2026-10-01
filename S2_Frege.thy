theory S2_Frege
  imports Main "HOL-Computational_Algebra.Polynomial"
begin

section \<open>Frege systems and simulation\<close>

text \<open>Formulas may use arbitrary connectives.  Their arities and evaluation
  are supplied by the alphabet of a Frege system.\<close>

datatype 'c formula =
  Atom string |
  Conn 'c "('c formula list)"

record 'c rule =
  prems :: "('c formula) list"
  concl :: "'c formula"

record 'c alphabet =
  arity :: "'c \<Rightarrow> nat"
  conn_evals :: "'c \<Rightarrow> (bool list \<Rightarrow> bool)"

datatype dm_conn = Top | Bot | Not | Or | And

definition dm_alphabet :: "dm_conn alphabet" where
  "dm_alphabet = \<lparr>
    arity = (\<lambda>c. case c of Top \<Rightarrow> 0 | Bot \<Rightarrow> 0 | Not \<Rightarrow> 1 | Or \<Rightarrow> 2 | And \<Rightarrow> 2),
    conn_evals = (\<lambda> c. case c of
      Top \<Rightarrow> (\<lambda>_. True)                \<comment> \<open>nullary: ignores input list\<close>
    | Bot \<Rightarrow> (\<lambda>_. False)               \<comment> \<open>nullary\<close>
    | Not \<Rightarrow> (\<lambda>args. case args of [x] \<Rightarrow> \<not> x | _ \<Rightarrow> undefined)
    | Or  \<Rightarrow> (\<lambda>args. case args of [x, y] \<Rightarrow> x \<or> y | _ \<Rightarrow> undefined)
    | And \<Rightarrow> (\<lambda>args. case args of [x, y] \<Rightarrow> x \<and> y | _ \<Rightarrow> undefined))
  \<rparr>"

record 'c frege =
  rules :: "('c rule) set"
  alphabet :: "'c alphabet"

fun eval :: "'c alphabet \<Rightarrow> (string \<Rightarrow> bool) \<Rightarrow> 'c formula \<Rightarrow> bool" where
  "eval al v (Atom a) = v a" |
  "eval al v (Conn c fs) = (conn_evals al c) (map (eval al v) fs)"

record 'c frege_proof =
  assumptions :: "('c formula) set"
  thesis :: "'c formula"
  steps :: "('c formula) list"

fun sub_formula :: "(string \<Rightarrow> 'c formula) \<Rightarrow> 'c formula \<Rightarrow> 'c formula" where
  "sub_formula sub (Atom a) = sub a" |
  "sub_formula sub (Conn c fs) = Conn c (map (sub_formula sub) fs)"

fun sub_rule :: "(string \<Rightarrow> 'c formula) \<Rightarrow> 'c rule \<Rightarrow> 'c rule" where
  "sub_rule sub r = \<lparr>
    prems = map (sub_formula sub) (prems r),
    concl = sub_formula sub (concl r)
  \<rparr>"

fun sub_proof :: "(string \<Rightarrow> 'c formula) \<Rightarrow> 'c frege_proof \<Rightarrow> 'c frege_proof" where
  "sub_proof sub pr = \<lparr>
    assumptions = (sub_formula sub)` (assumptions pr),
    thesis = sub_formula sub (thesis pr),
    steps = map (sub_formula sub) (steps pr)
  \<rparr>"

fun var_set_form :: "'c formula \<Rightarrow> string set" where
  "var_set_form (Atom a) = {a}" |
  "var_set_form (Conn c fs) = \<Union> (var_set_form ` (set fs))"

fun var_set_rule :: "'c rule \<Rightarrow> string set" where
  "var_set_rule rule = \<Union> (var_set_form ` (set (prems rule))) \<union> var_set_form (concl rule)"

fun var_set_proof :: "'c frege_proof \<Rightarrow> string set" where
  "var_set_proof pr = \<Union> (var_set_form ` (assumptions pr)) \<union>
                      \<Union> (var_set_form ` (set (steps pr))) \<union>
                         var_set_form (thesis pr)"

text \<open>
  Substitution changes the valuation of the original formula according to the
  formulas substituted for its variables. We also record how substitution affects
  occurring variables, and that irrelevant variables do not affect evaluation.
\<close>

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

definition rule_restricted_sub :: "'c rule \<Rightarrow> (string \<Rightarrow> 'c formula) \<Rightarrow> bool" where
  "rule_restricted_sub rule sub \<longleftrightarrow> (\<forall> v. v \<notin> var_set_rule rule \<longrightarrow> sub v = Atom v)"

definition derived :: "('c rule) set \<Rightarrow> ('c formula) list \<Rightarrow> 'c formula \<Rightarrow> bool" where
  "derived rs fs f \<longleftrightarrow> (\<exists> r \<in> rs. \<exists> sub. let sub_r = sub_rule sub r in
                       (concl sub_r) = f \<and>
                       (\<forall> f1 \<in> set (prems sub_r). \<exists> f2 \<in> set fs. f1 = f2))"

lemma derived_mono:
  assumes "set fs \<subseteq> set gs"
  assumes "derived rs fs f"
  shows   "derived rs gs f"
proof -
  obtain r sub
    where r_in: "r \<in> rs"
      and concl_eq: "concl (sub_rule sub r) = f"
      and prems_fs:
        "\<forall>f1 \<in> set (prems (sub_rule sub r)).
           \<exists>f2 \<in> set fs. f1 = f2"
    using assms(2)
    unfolding derived_def
    by auto

  have prems_gs:
    "\<forall>f1 \<in> set (prems (sub_rule sub r)).
       \<exists>f2 \<in> set gs. f1 = f2"
  proof
    fix f1
    assume "f1 \<in> set (prems (sub_rule sub r))"
    then obtain f2 where
      "f2 \<in> set fs" and "f1 = f2"
      using prems_fs by blast
    hence "f2 \<in> set gs"
      using assms(1) by blast
    thus "\<exists>f2 \<in> set gs. f1 = f2"
      using \<open>f1 = f2\<close> by blast
  qed
  show ?thesis
    unfolding derived_def
    using r_in concl_eq prems_gs
    by auto
qed

definition valid_proof :: "'c frege \<Rightarrow> 'c frege_proof \<Rightarrow> bool" where
  "valid_proof F pr \<longleftrightarrow>
    thesis pr = last (steps pr) \<and> steps pr \<noteq> []
    \<and> (\<forall>i < length (steps pr).
         steps pr ! i \<in> assumptions pr
         \<or> derived (rules F) (take i (steps pr)) (steps pr ! i))"

lemma valid_proof_thesis_mem:
  assumes "valid_proof F pr"
  shows "thesis pr \<in> set (steps pr)"
  using assms unfolding valid_proof_def by auto

fun combine_proofs :: "'c frege_proof \<Rightarrow> 'c frege_proof \<Rightarrow> 'c frege_proof" where
  "combine_proofs pr1 pr2 = \<lparr>assumptions = assumptions pr1 \<union> (assumptions pr2 - set (steps pr1)),
                             thesis = thesis pr2,
                             steps = steps pr1 @ steps pr2\<rparr>"

definition sound_rule :: "'c frege \<Rightarrow> 'c rule \<Rightarrow> bool" where
  "sound_rule F r \<longleftrightarrow>
    (\<forall> val. (\<forall> form \<in> set (prems r). eval (alphabet F) val form) \<longrightarrow> eval (alphabet F) val (concl r))"

fun depth_formula :: "'c formula \<Rightarrow> nat" where
  "depth_formula (Atom v) = 1" |
  "depth_formula (Conn c fs) = (if length fs > 0 then 1 + Max (set (map depth_formula fs)) else 1)"

fun depth_proof :: "'c frege_proof \<Rightarrow> nat" where
  "depth_proof pr = Max (set (map depth_formula (steps pr)))"

fun len_formula :: "'c formula \<Rightarrow> nat" where
  "len_formula (Atom v) = 1" |
  "len_formula (Conn c fs) = 1 + sum_list (map len_formula fs)"

fun len_proof :: "'c frege_proof \<Rightarrow> nat" where
  "len_proof pr = sum_list (map len_formula (steps pr))"

definition len_sub :: "string set \<Rightarrow> (string \<Rightarrow> 'c formula) \<Rightarrow> nat" where
  "len_sub var_set sub =
     max 1 (\<Sum> v \<in> var_set. len_formula (sub v))"

definition depth_sub :: "string set \<Rightarrow> (string \<Rightarrow> 'c formula) \<Rightarrow> nat" where
  "depth_sub var_set sub =
     Max (insert 1 ((\<lambda>v. depth_formula (sub v)) ` var_set))"

lemma depth_sub_bound:
  assumes "finite var_set" and "v \<in> var_set"
  shows "depth_formula (sub v) \<le> depth_sub var_set sub"
  unfolding depth_sub_def using assms by (auto intro: Max_ge)

lemma len_formula_positive:
  shows "len_formula f \<ge> 1"
  by (metis le_add_same_cancel1 le_numeral_extra(4) len_formula.elims zero_le)

lemma len_proof_positive:
  assumes "valid_proof F pr"
  shows "len_proof pr \<ge> 1"
proof -
  have a: "steps pr \<noteq> []"
    using assms valid_proof_def[of F pr] by simp
  have "\<forall> f \<in> set (steps pr). len_formula f \<ge> 1"
    using len_formula_positive by auto
  then obtain f fs where steps_def: "steps pr = f # fs"
    using a by (cases "steps pr") auto
  have "len_proof pr = len_formula f + sum_list (map len_formula fs)"
    using steps_def by simp
  also have "\<dots> \<ge> 1 + 0"
    using len_formula_positive[of f] by simp
  finally show ?thesis by simp
qed

lemma sub_formula_bound:
  fixes f :: "'c formula"
  and sub :: "(string \<Rightarrow> 'c formula)"
  and var_set :: "string set"
  assumes "finite var_set" and "\<forall> v. v \<notin> var_set \<longrightarrow> sub v = Atom v"
  shows "len_formula (sub_formula sub f) \<le> (len_formula f) * (len_sub var_set sub)"
  using assms
proof (induction f arbitrary: sub var_set)
  case (Atom a)
  have "len_formula (Atom a) = 1" by simp
  thus ?case
  proof (cases "a \<in> var_set")
    case False
    hence "sub_formula sub (Atom a) = Atom a"
      using assms by (simp add: Atom.prems(2))
    thus ?thesis
      by (simp add: len_sub_def)
  next
    case True
    have len_eq: "len_formula (sub_formula sub (Atom a)) = len_formula (sub a)" by simp
    have "len_formula (sub a) \<le> len_sub var_set sub" using True len_sub_def[of var_set sub]
      by (metis Atom.prems(1) le_max_iff_disj sum_nonneg_leq_bound zero_le)
    thus ?thesis using len_eq by simp
  qed
next
  case (Conn c fs)
  have sub_len_ge1: "1 \<le> len_sub var_set sub"
    unfolding len_sub_def by simp
  have ih_sum:
    "sum_list (map (len_formula \<circ> sub_formula sub) fs)
     \<le> sum_list (map (\<lambda>x. len_formula x * len_sub var_set sub) fs)"
  proof -
    have all_bound:
      "\<forall>x \<in> set fs. len_formula (sub_formula sub x) \<le> len_formula x * len_sub var_set sub"
      using Conn.IH Conn.prems by blast
    from all_bound show ?thesis
    proof (induction fs)
      case Nil
      then show ?case by simp
    next
      case (Cons f fs')
      have f_bound: "len_formula (sub_formula sub f) \<le> len_formula f * len_sub var_set sub"
        using Cons.prems by simp
      have tail_all:
        "\<forall>x \<in> set fs'. len_formula (sub_formula sub x) \<le> len_formula x * len_sub var_set sub"
        using Cons.prems by simp
      have tail_bound:
        "sum_list (map (len_formula \<circ> sub_formula sub) fs')
         \<le> sum_list (map (\<lambda>x. len_formula x * len_sub var_set sub) fs')"
        using Cons.IH[OF tail_all] .
      have tail_bound':
        "(\<Sum>a\<leftarrow>fs'. len_formula (sub_formula sub a))
         \<le> (\<Sum>x\<leftarrow>fs'. len_formula x * len_sub var_set sub)"
      proof -
        have lhs_eq:
          "(\<Sum>a\<leftarrow>fs'. len_formula (sub_formula sub a)) =
           sum_list (map (len_formula \<circ> sub_formula sub) fs')"
          by (induction fs') simp_all
        have rhs_eq:
          "(\<Sum>x\<leftarrow>fs'. len_formula x * len_sub var_set sub) =
           sum_list (map (\<lambda>x. len_formula x * len_sub var_set sub) fs')"
          by (induction fs') simp_all
        show ?thesis
          using tail_bound lhs_eq rhs_eq by simp
      qed
      have comb_bound:
        "len_formula (sub_formula sub f) + (\<Sum>a\<leftarrow>fs'. len_formula (sub_formula sub a))
         \<le> len_formula f * len_sub var_set sub +
            (\<Sum>x\<leftarrow>fs'. len_formula x * len_sub var_set sub)"
        using add_mono[OF f_bound tail_bound'] by simp
      show ?case
        using comb_bound by simp
    qed
  qed
  have left:
    "len_formula (sub_formula sub (Conn c fs))
     = 1 + sum_list (map (len_formula \<circ> sub_formula sub) fs)"
    by simp
  have right:
    "(len_formula (Conn c fs)) * len_sub var_set sub
     = (1 + sum_list (map len_formula fs)) * len_sub var_set sub"
    by simp
  have one_le:
    "1 + sum_list (map (len_formula \<circ> sub_formula sub) fs)
     \<le> len_sub var_set sub + sum_list (map (\<lambda>x. len_formula x * len_sub var_set sub) fs)"
  proof -
    have "1 + sum_list (map (len_formula \<circ> sub_formula sub) fs)
          \<le> 1 + sum_list (map (\<lambda>x. len_formula x * len_sub var_set sub) fs)"
      using ih_sum by simp
    also have "\<dots> \<le> len_sub var_set sub
                  + sum_list (map (\<lambda>x. len_formula x * len_sub var_set sub) fs)"
      using sub_len_ge1 by simp
    finally show ?thesis .
  qed
  have "\<dots> = (1 + sum_list (map len_formula fs)) * len_sub var_set sub"
  proof -
    have mul_sum:
      "sum_list (map (\<lambda>x. len_formula x * len_sub var_set sub) fs) =
       len_sub var_set sub * sum_list (map len_formula fs)"
    proof (induction fs)
      case Nil
      then show ?case by simp
    next
      case (Cons a as)
      then show ?case
        by (simp add: algebra_simps)
    qed
    show ?thesis
      using mul_sum by (simp add: algebra_simps)
  qed
  with left right one_le show ?case
    using sub_len_ge1 by simp
qed

lemma sub_proof_bound:
  fixes pr :: "'c frege_proof"
  and sub :: "(string \<Rightarrow> 'c formula)"
  and var_set :: "string set"
  assumes "finite var_set" and "\<forall> v. v \<notin> var_set \<longrightarrow> sub v = Atom v"
  shows "len_proof (sub_proof sub pr) \<le> (len_proof pr) * (len_sub var_set sub)"
proof -
  have "sum_list (map (\<lambda>f. len_formula (sub_formula sub f)) (steps pr))
      \<le> sum_list (map (\<lambda>f. len_formula f * len_sub var_set sub) (steps pr))"
    by (rule sum_list_mono) (use sub_formula_bound[OF assms] in simp)
  thus ?thesis by (simp add: comp_def sum_list_mult_const)
qed

lemma sub_formula_depth_bound:
  fixes f :: "'c formula"
  and sub :: "(string \<Rightarrow> 'c formula)"
  and var_set :: "string set"
  assumes "finite var_set" and "\<forall> v. v \<notin> var_set \<longrightarrow> sub v = Atom v"
  shows "depth_formula (sub_formula sub f) \<le> depth_formula f + depth_sub var_set sub"
  using assms
proof (induction f arbitrary: sub var_set)
  case (Atom a)
  show ?case
  proof (cases "a \<in> var_set")
    case True
    have "depth_formula (sub_formula sub (Atom a)) = depth_formula (sub a)" by simp
    also have "\<dots> \<le> depth_sub var_set sub"
      using depth_sub_bound[OF Atom.prems(1) True] .
    also have "\<dots> \<le> depth_formula (Atom a) + depth_sub var_set sub" by simp
    finally show ?thesis .
  next
    case False
    hence "sub a = Atom a" using Atom.prems(2) by simp
    hence "depth_formula (sub_formula sub (Atom a)) = 1" by simp
    moreover have "1 \<le> depth_formula (Atom a) + depth_sub var_set sub" by simp
    ultimately show ?thesis by simp
  qed
next
  case (Conn c fs)
  let ?D = "depth_sub var_set sub"
  show ?case
  proof (cases "fs = []")
    case True
    hence "depth_formula (sub_formula sub (Conn c fs)) = 1" by simp
    moreover have "depth_formula (Conn c fs) = 1" using True by simp
    ultimately show ?thesis by simp
  next
    case False
    let ?fs' = "map (sub_formula sub) fs"
    have lhs: "depth_formula (sub_formula sub (Conn c fs)) =
               1 + Max (set (map depth_formula ?fs'))"
      using False by simp
    have rhs: "depth_formula (Conn c fs) = 1 + Max (set (map depth_formula fs))"
      using False by simp
    have fin_fs': "finite (set (map depth_formula ?fs'))" by simp
    have ne_set': "set (map depth_formula ?fs') \<noteq> {}" using False by simp
    have fin_fs: "finite (set (map depth_formula fs))" by simp

    have ih_pointwise:
      "\<forall>f' \<in> set fs. depth_formula (sub_formula sub f') \<le> depth_formula f' + ?D"
      using Conn.IH Conn.prems by blast

    have all_le:
      "\<forall>x \<in> set (map depth_formula ?fs').
         x \<le> Max (set (map depth_formula fs)) + ?D"
    proof
      fix x assume "x \<in> set (map depth_formula ?fs')"
      then obtain f' where f'_in: "f' \<in> set fs"
                       and x_eq: "x = depth_formula (sub_formula sub f')"
        by auto
      from ih_pointwise f'_in
      have ih: "depth_formula (sub_formula sub f') \<le> depth_formula f' + ?D"
        by blast
      have df'_le: "depth_formula f' \<le> Max (set (map depth_formula fs))"
        using f'_in fin_fs by simp
      from ih df'_le show "x \<le> Max (set (map depth_formula fs)) + ?D"
        using x_eq by simp
    qed

    have max_le:
      "Max (set (map depth_formula ?fs')) \<le> Max (set (map depth_formula fs)) + ?D"
    proof (rule Max.boundedI)
      show "finite (set (map depth_formula ?fs'))" using fin_fs' .
      show "set (map depth_formula ?fs') \<noteq> {}" using ne_set' .
      fix a assume "a \<in> set (map depth_formula ?fs')"
      thus "a \<le> Max (set (map depth_formula fs)) + ?D" using all_le by blast
    qed

    have "depth_formula (sub_formula sub (Conn c fs))
            = 1 + Max (set (map depth_formula ?fs'))"
      using lhs .
    also have "\<dots> \<le> 1 + Max (set (map depth_formula fs)) + ?D"
      using max_le by simp
    also have "\<dots> = depth_formula (Conn c fs) + ?D"
      using rhs by simp
    finally show ?thesis .
  qed
qed

definition formulas_equiv :: "'c1 formula \<Rightarrow> 'c1 alphabet \<Rightarrow> 'c2 formula \<Rightarrow> 'c2 alphabet \<Rightarrow> bool" where
  "formulas_equiv f1 a1 f2 a2 \<longleftrightarrow> (\<forall> val. eval a1 val f1 = eval a2 val f2)"

definition conns_equiv :: "'c1 \<Rightarrow> 'c1 alphabet \<Rightarrow> 'c2 \<Rightarrow> 'c2 alphabet \<Rightarrow> bool" where
  "conns_equiv conn1 a1 conn2 a2 \<longleftrightarrow> (arity a1 conn1 = arity a2 conn2 \<and>
                                    (\<forall> val fs1 fs2. length fs1 = length fs2 \<longrightarrow>
                                           (\<forall> i. i < length fs1 \<longrightarrow> formulas_equiv (fs1 ! i) a1 (fs2 ! i) a2) \<longrightarrow>
                                           eval a1 val (Conn conn1 fs1) = eval a2 val (Conn conn2 fs2)))"

definition equiv_formula_sets :: "'c1 formula set \<Rightarrow> 'c1 alphabet \<Rightarrow> 'c2 formula set \<Rightarrow> 'c2 alphabet \<Rightarrow> bool" where
  "equiv_formula_sets fs1 a1 fs2 a2 \<longleftrightarrow> (\<forall> f1 \<in> fs1. \<exists> f2 \<in> fs2. formulas_equiv f1 a1 f2 a2) \<and>
                                        (\<forall> f2 \<in> fs2. \<exists> f1 \<in> fs1. formulas_equiv f2 a2 f1 a1)"

fun formula_well_formed :: "'c alphabet \<Rightarrow> 'c formula \<Rightarrow> bool" where
  "formula_well_formed alph (Atom _) = True" |
  "formula_well_formed alph (Conn c fs) =
     (length fs = arity alph c \<and> (\<forall>g \<in> set fs. formula_well_formed alph g))"

lemma sub_formula_well_formed:
  assumes "formula_well_formed alph g"
    and "\<And>v. formula_well_formed alph (sub v)"
  shows "formula_well_formed alph (sub_formula sub g)"
  using assms by (induction g) auto

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

lemma marker_substitution_map:
  assumes "distinct names" "length arguments = length names"
  shows "map (marker_substitution names arguments) names = arguments"
  by (rule nth_equalityI)
     (use assms marker_substitution_nth[OF assms] in auto)

lemma marker_substitution_length:
  assumes "distinct names" "length arguments = length names"
  shows "len_sub (set names) (marker_substitution names arguments)
       = max 1 (sum_list (map len_formula arguments))"
proof -
  let ?sub = "marker_substitution names arguments"
  have "(\<Sum>v\<in>set names. len_formula (?sub v))
       = sum_list (map (\<lambda>v. len_formula (?sub v)) names)"
    using assms(1) by (simp add: sum_list_distinct_conv_sum_set)
  also have "\<dots> = sum_list (map len_formula (map ?sub names))"
    by (simp add: comp_def)
  also have "\<dots> = sum_list (map len_formula arguments)"
    by (simp only: marker_substitution_map[OF assms])
  finally show ?thesis unfolding len_sub_def by simp
qed

lemma marker_substitution_depth:
  assumes "1 \<le> D" "\<And>g. g \<in> set arguments \<Longrightarrow> depth_formula g \<le> D"
  shows "depth_sub (set names) (marker_substitution names arguments) \<le> D"
proof -
  have "depth_formula (marker_substitution names arguments v) \<le> D" for v
    using marker_substitution_range[of names arguments v] assms by auto
  with assms(1) show ?thesis unfolding depth_sub_def by (intro Max.boundedI) auto
qed

lemma depth_formula_child_le:
  assumes "g \<in> set fs"
  shows "depth_formula g \<le> depth_formula (Conn c fs)"
proof -
  have "depth_formula g \<le> Max (set (map depth_formula fs))"
    using assms by (intro Max_ge) auto
  thus ?thesis using assms by (cases fs) auto
qed

lemma sub_proof_line_bounds:
  assumes fin: "finite V"
      and outside: "\<forall>v. v \<notin> V \<longrightarrow> sub v = Atom v"
      and sz: "\<forall>s\<in>set (steps pr). len_formula s \<le> S"
      and dep: "\<forall>s\<in>set (steps pr). depth_formula s \<le> D"
      and wf: "\<forall>s\<in>set (steps pr). formula_well_formed alph s"
      and sub_wf: "\<And>v. formula_well_formed alph (sub v)"
  shows "\<forall>s\<in>set (steps (sub_proof sub pr)).
       len_formula s \<le> S * len_sub V sub
       \<and> depth_formula s \<le> D + depth_sub V sub
       \<and> formula_well_formed alph s"
proof (intro ballI)
  fix s assume "s \<in> set (steps (sub_proof sub pr))"
  then obtain t where t: "t \<in> set (steps pr)" "s = sub_formula sub t" by auto
  have l: "len_formula s \<le> S * len_sub V sub"
    using sub_formula_bound[OF fin outside, of t] sz t
    by (meson mult_le_mono1 order_trans)
  have d: "depth_formula s \<le> D + depth_sub V sub"
    using sub_formula_depth_bound[OF fin outside, of t] dep t
    by (meson add_right_mono order_trans)
  have wft: "formula_well_formed alph t" using wf t(1) by blast
  have wfs: "formula_well_formed alph (sub_formula sub t)"
    by (rule sub_formula_well_formed[OF wft sub_wf])
  show "len_formula s \<le> S * len_sub V sub
       \<and> depth_formula s \<le> D + depth_sub V sub
       \<and> formula_well_formed alph s"
    using l d wfs t(2) by simp
qed

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

locale frege_system =
  fixes F :: "'c frege"
  assumes sound: "\<forall> r \<in> rules F. sound_rule F r"
  and impl_complete:
    "\<forall> fs th.
       (\<forall> f \<in> fs. formula_well_formed (alphabet F) f) \<longrightarrow>
       formula_well_formed (alphabet F) th \<longrightarrow>
       (\<forall> val. (\<forall> f \<in> fs. eval (alphabet F) val f) \<longrightarrow> eval (alphabet F) val th)
       \<longrightarrow> (\<exists> pr. valid_proof F pr
                 \<and> assumptions pr = fs
                 \<and> thesis pr = th
                 \<and> (\<forall> st \<in> set (steps pr). formula_well_formed (alphabet F) st))"
  and finite: "finite (rules F)"
  and finite_alphabet: "finite (UNIV :: 'c set)"
  and func_complete:
    "\<forall>f :: dm_conn formula.
       \<exists> f' :: 'c formula. formula_well_formed (alphabet F) f' \<and>
                           formulas_equiv f dm_alphabet f' (alphabet F)"
  and has_top:
    "\<exists> t. arity (alphabet F) t = 0 \<and> (\<forall> val. eval (alphabet F) val (Conn t []) = True)"
  and has_bot:
    "\<exists> b. arity (alphabet F) b = 0 \<and> (\<forall> val. eval (alphabet F) val (Conn b []) = False)"
begin

lemma func_complete_supported:
  assumes "var_set_form dmf \<subseteq> V"
  shows "\<exists>f. formula_well_formed (alphabet F) f
       \<and> var_set_form f \<subseteq> V
       \<and> formulas_equiv dmf dm_alphabet f (alphabet F)"
proof -
  obtain f where wf: "formula_well_formed (alphabet F) f"
    and eq: "formulas_equiv dmf dm_alphabet f (alphabet F)"
    using func_complete by blast
  obtain t where ar: "arity (alphabet F) t = 0"
    and top: "\<And>val. eval (alphabet F) val (Conn t []) = True"
    using has_top by blast
  show ?thesis
    using connective_template_pruned[OF eq wf ar top assms]
    unfolding formulas_equiv_def by blast
qed

lemma combining_valid_proofs_pr1:
  fixes pr1 :: "'c frege_proof" and pr2 :: "'c frege_proof"
  assumes "valid_proof F pr1 \<and> valid_proof F pr2"
  and "comb = combine_proofs pr1 pr2"
  and "i < length (steps pr1)"
  shows "steps comb ! i \<in> assumptions comb \<or>
           derived (rules F) (take i (steps comb)) (steps comb ! i)"
proof -
  have "i < length (steps comb)" using assms by simp
  hence 1: "steps pr1 ! i = steps comb ! i" using assms by (simp add: nth_append_left)
  have "assumptions pr1 \<subseteq> assumptions comb" using assms(2) by simp
  hence 2: "steps pr1 ! i \<in> assumptions pr1 \<longrightarrow> steps comb ! i \<in> assumptions comb" using 1 by auto
  have "take i (steps pr1) = take i (steps comb)" using assms by simp
  hence 3: "derived (rules F) (take i (steps pr1)) (steps pr1 ! i) \<longrightarrow>
         derived (rules F) (take i (steps comb)) (steps comb ! i)" using 1 by simp
  have vp1: "valid_proof F pr1"
    using assms(1) by simp
  have "steps pr1 ! i \<in> assumptions pr1 \<or>
        derived (rules F) (take i (steps pr1)) (steps pr1 ! i)"
    using vp1 assms(3) unfolding valid_proof_def by simp
  thus ?thesis using 2 3 by blast
qed

lemma combining_valid_proofs:
  fixes pr1 :: "'c frege_proof" and pr2 :: "'c frege_proof"
  assumes "valid_proof F pr1 \<and> valid_proof F pr2"
  and "comb = combine_proofs pr1 pr2"
  shows "valid_proof F comb"
proof -
  have app: "steps comb = (steps pr1) @ (steps pr2)" using assms(2) by simp
  have vp2: "valid_proof F pr2" using assms(1) by simp
  hence "last (steps comb) = last (steps pr2)"
    using app unfolding valid_proof_def by simp
  have th2: "thesis pr2 = last (steps pr2)"
    using vp2 unfolding valid_proof_def by simp
  have nz2: "steps pr2 \<noteq> []"
    using vp2 unfolding valid_proof_def by simp
  have a: "thesis comb = last (steps comb) \<and> steps comb \<noteq> []"
    using assms(2) th2 nz2 app by simp

  have b: "\<forall> i < length (steps comb). (steps comb ! i \<in> assumptions comb \<or>
                                    derived (rules F) (take i (steps comb)) (steps comb ! i))"
  proof (rule allI)
    fix i
    show "i < length (steps comb) \<longrightarrow> steps comb ! i \<in> assumptions comb \<or>
         derived (rules F) (take i (steps comb)) (steps comb ! i)"
    proof (cases "i < length (steps pr1)")
      case True
      thus ?thesis using combining_valid_proofs_pr1 assms by simp
    next
      case False
      let ?j = "length (steps pr1)"
      show ?thesis
      proof
        assume i_in_range: "i < length (steps comb)"
        hence 02: "drop ?j (steps comb) = steps pr2" using assms(2) False by simp
        hence 12: "steps pr2 ! (i - ?j) = steps comb ! i"
          using False app by (simp add: nth_append_right)
        hence 22: "steps pr2 ! (i - ?j) \<in> assumptions pr2 \<longrightarrow>
               steps comb ! i \<in> assumptions comb \<or> (\<exists> k < ?j. steps comb ! k = steps comb ! i)"
        proof (cases "steps pr2 ! (i - ?j) \<in> set (steps pr1)")
          case True
          thus ?thesis by (metis app in_set_conv_nth nth_append)
        next
          case False
          show ?thesis
          proof
            assume "steps pr2 ! (i - ?j) \<in> assumptions pr2"
            hence 131: "steps comb ! i \<in> assumptions pr2" using 12 by simp
            have 132: "assumptions comb = assumptions pr1 \<union> (assumptions pr2 - set (steps pr1))"
               using assms(2) by simp
            have "steps comb ! i \<notin> set (steps pr1)" using 12 False by simp
            hence "steps comb ! i \<in> assumptions comb" using 131 132 by simp
            thus "steps comb ! i \<in> assumptions comb \<or> (\<exists>k<?j. steps comb ! k = steps comb ! i)"
              by simp
          qed
        qed
        have repeat_proof:
          "((\<exists> k < ?j. steps comb ! k = steps comb ! i)
             \<and> \<not> (steps comb ! i \<in> assumptions comb))
           \<longrightarrow> derived (rules F) (take i (steps comb)) (steps comb ! i)"
        proof
          assume assm:
            "(\<exists> k < ?j. steps comb ! k = steps comb ! i)
             \<and> \<not> (steps comb ! i \<in> assumptions comb)"
          then obtain k where
            k_lt: "k < ?j"
            and eq: "steps comb ! k = steps comb ! i"
            and not_assm: "\<not> (steps comb ! i \<in> assumptions comb)"
            by auto
          have "steps comb ! k \<in> assumptions comb \<or>
             derived (rules F) (take k (steps comb)) (steps comb ! k)"
            using assms combining_valid_proofs_pr1 k_lt by simp
          hence "derived (rules F) (take k (steps comb)) (steps comb ! k)" using not_assm eq by simp
          thus "derived (rules F) (take i (steps comb)) (steps comb ! i)"
            by (metis False derived_mono eq k_lt linorder_not_le order_less_trans
                      set_take_subset_set_take)
        qed
        have 32: "derived (rules F) (take (i - ?j) (steps pr2)) (steps pr2 ! (i - ?j)) \<longrightarrow>
              derived (rules F) (take i (steps comb)) (steps comb ! i)" using 12 02 derived_mono
          by (metis drop_take set_drop_subset)
        have vp2: "valid_proof F pr2"
          using assms(1) by simp
        have i_bound: "i < ?j + length (steps pr2)"
          using i_in_range app by simp
        have j_le_i: "?j \<le> i"
          using False by simp
        have idx2: "i - ?j < length (steps pr2)"
          using i_bound j_le_i by arith
        have "steps pr2 ! (i - ?j) \<in> assumptions pr2 \<or>
              derived (rules F) (take (i - ?j) (steps pr2)) (steps pr2 ! (i - ?j))"
          using vp2 idx2 unfolding valid_proof_def by simp
        thus "steps comb ! i \<in> assumptions comb \<or>
              derived (rules F) (take i (steps comb)) (steps comb ! i)"
          using 22 32 repeat_proof by auto
      qed
    qed
  qed

  show ?thesis
    unfolding valid_proof_def
    using a b by simp
qed

lemma proof_substitution:
  fixes pr :: "'c frege_proof"
    and sub :: "string \<Rightarrow> 'c formula"
  assumes "valid_proof F pr"
  shows "valid_proof F (sub_proof sub pr)"
proof -
  have sub_formula_comp:
    "sub_formula s1 (sub_formula s2 f) =
      sub_formula (\<lambda>a. sub_formula s1 (s2 a)) f"
    for s1 s2 :: "string \<Rightarrow> 'c formula" and f :: "'c formula"
    by (induction f) simp_all

  have derived_substitution:
    "derived (rules F) fs f \<Longrightarrow>
      derived (rules F) (map (sub_formula sub) fs) (sub_formula sub f)"
    for fs f
  proof -
    assume der: "derived (rules F) fs f"
    then obtain r s where
      r_in: "r \<in> rules F"
      and concl_eq: "concl (sub_rule s r) = f"
      and prems_fs:
        "\<forall>p \<in> set (prems (sub_rule s r)). \<exists>q \<in> set fs. p = q"
      unfolding derived_def by auto
    let ?s' = "\<lambda>a. sub_formula sub (s a)"
    have concl_sub: "concl (sub_rule ?s' r) = sub_formula sub f"
    proof -
      have c1: "concl (sub_rule ?s' r) = sub_formula ?s' (concl r)"
        by simp
      have c2: "sub_formula ?s' (concl r) = sub_formula sub (sub_formula s (concl r))"
        using sub_formula_comp[of sub s "concl r"] by simp
      have c3: "concl (sub_rule s r) = sub_formula s (concl r)"
        by simp
      have "concl (sub_rule ?s' r) = sub_formula sub (concl (sub_rule s r))"
        using c1 c2 c3 by simp
      also have "... = sub_formula sub f"
        using concl_eq by simp
      finally show ?thesis .
    qed
    have prems_sub:
      "\<forall>p \<in> set (prems (sub_rule ?s' r)). \<exists>q \<in> set (map (sub_formula sub) fs). p = q"
    proof
      fix p
      assume p_sub: "p \<in> set (prems (sub_rule ?s' r))"
      have prems_comp:
        "prems (sub_rule ?s' r) = map (sub_formula sub) (prems (sub_rule s r))"
      proof (cases r)
        case (fields prems concl)
        have comp_eq: "sub_formula ?s' = (sub_formula sub) \<circ> (sub_formula s)"
          by (rule ext) (simp add: sub_formula_comp[symmetric])
        have "map (sub_formula ?s') prems = map (sub_formula sub) (map (sub_formula s) prems)"
          using comp_eq by simp
        with fields show ?thesis
          by simp
      qed
      from p_sub prems_comp obtain x where
        x_in: "x \<in> set (prems r)"
        and p_eq1: "p = sub_formula ?s' x"
        by auto
      have p0_in: "sub_formula s x \<in> set (prems (sub_rule s r))"
        using x_in by simp
      have p_eq: "p = sub_formula sub (sub_formula s x)"
        using p_eq1 sub_formula_comp[of sub s x] by simp
      from prems_fs p0_in obtain q where "q \<in> set fs" and "sub_formula s x = q" by auto
      thus "\<exists>q \<in> set (map (sub_formula sub) fs). p = q"
        using p_eq by auto
    qed
    show ?thesis
      unfolding derived_def
      using r_in concl_sub prems_sub by auto
  qed

  have steps_ok:
    "\<forall>i < length (steps (sub_proof sub pr)).
      steps (sub_proof sub pr) ! i \<in> assumptions (sub_proof sub pr) \<or>
      derived (rules F) (take i (steps (sub_proof sub pr))) (steps (sub_proof sub pr) ! i)"
  proof (intro allI impI)
    fix i
    assume i_lt: "i < length (steps (sub_proof sub pr))"
    then have i_lt_pr: "i < length (steps pr)" by simp
    have step:
      "steps pr ! i \<in> assumptions pr \<or>
       derived (rules F) (take i (steps pr)) (steps pr ! i)"
      using assms i_lt_pr unfolding valid_proof_def by simp
    from step show "steps (sub_proof sub pr) ! i \<in> assumptions (sub_proof sub pr) \<or>
      derived (rules F) (take i (steps (sub_proof sub pr))) (steps (sub_proof sub pr) ! i)"
    proof
      assume "steps pr ! i \<in> assumptions pr"
      thus ?thesis using i_lt by simp
    next
      assume "derived (rules F) (take i (steps pr)) (steps pr ! i)"
      then have
        "derived (rules F)
          (map (sub_formula sub) (take i (steps pr)))
          (sub_formula sub (steps pr ! i))"
        using derived_substitution by blast
      thus ?thesis
        using i_lt by (simp add: take_map)
    qed
  qed

  show ?thesis
    using assms steps_ok
    unfolding valid_proof_def by (simp add: last_map)
qed
end

section \<open>Bounded derivations and fixed proof instances\<close>

text \<open>These bounds apply to proofs with assumptions as well as closed proofs.
  Substitution and cutting a closed premise into a fixed derivation are proved
  once, so the later equivalence macros only need their logical instances.\<close>

definition bounded_derivation ::
  "'c frege \<Rightarrow> 'c formula set \<Rightarrow> 'c formula \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "bounded_derivation F H A lines sz dep \<longleftrightarrow>
    (\<exists>pr. valid_proof F pr \<and> assumptions pr \<subseteq> H \<and> frege_proof.thesis pr = A
      \<and> length (steps pr) \<le> lines
      \<and> (\<forall>t\<in>set (steps pr). len_formula t \<le> sz \<and> depth_formula t \<le> dep
                              \<and> formula_well_formed (alphabet F) t))"

lemma bounded_derivation_weaken:
  assumes "bounded_derivation F H A l s d" "H \<subseteq> H'"
    "l \<le> l'" "s \<le> s'" "d \<le> d'"
  shows "bounded_derivation F H' A l' s' d'"
  using assms unfolding bounded_derivation_def
  by (elim exE, intro exI conjI) (auto intro: order.trans)

lemma bounded_derivation_from_proof:
  assumes "valid_proof F pr" "assumptions pr \<subseteq> H" "frege_proof.thesis pr = A"
    "\<forall>t\<in>set (steps pr). formula_well_formed (alphabet F) t"
  shows "bounded_derivation F H A (length (steps pr))
    (Max (insert 1 (len_formula ` set (steps pr))))
    (Max (insert 1 (depth_formula ` set (steps pr))))"
  unfolding bounded_derivation_def
  by (rule exI[of _ pr]) (use assms in \<open>auto intro: Max_ge\<close>)

lemma bounded_derivation_subst:
  assumes "frege_system F" "bounded_derivation F H A l s d" "finite V"
    "\<forall>v. v \<notin> V \<longrightarrow> sub v = Atom v"
    "\<And>v. formula_well_formed (alphabet F) (sub v)"
  shows "bounded_derivation F (sub_formula sub ` H) (sub_formula sub A)
    l (s * len_sub V sub) (d + depth_sub V sub)"
proof -
  obtain pr where pr: "valid_proof F pr" "assumptions pr \<subseteq> H"
    "frege_proof.thesis pr = A" "length (steps pr) \<le> l"
    "\<forall>t\<in>set (steps pr). len_formula t \<le> s"
    "\<forall>t\<in>set (steps pr). depth_formula t \<le> d"
    "\<forall>t\<in>set (steps pr). formula_well_formed (alphabet F) t"
    using assms(2) unfolding bounded_derivation_def by blast
  have valid: "valid_proof F (sub_proof sub pr)"
    by (rule frege_system.proof_substitution[OF assms(1) pr(1)])
  note bounds = sub_proof_line_bounds[OF assms(3,4) pr(5,6,7) assms(5)]
  show ?thesis unfolding bounded_derivation_def
    by (rule exI[of _ "sub_proof sub pr"]) (use valid bounds pr(2,3,4) in auto)
qed

lemma bounded_derivation_marker_instance:
  assumes fs: "frege_system F"
    and base: "bounded_derivation F H A l s d"
    and names: "distinct names" "length arguments = length names"
    and wf: "\<And>g. g \<in> set arguments \<Longrightarrow> formula_well_formed (alphabet F) g"
    and dep: "1 \<le> D" "\<And>g. g \<in> set arguments \<Longrightarrow> depth_formula g \<le> D"
  shows "bounded_derivation F
    (sub_formula (marker_substitution names arguments) ` H)
    (sub_formula (marker_substitution names arguments) A)
    l (s * max 1 (sum_list (map len_formula arguments))) (d + D)"
proof -
  let ?sub = "marker_substitution names arguments"
  have outside: "\<forall>v. v \<notin> set names \<longrightarrow> ?sub v = Atom v"
    using marker_substitution_outside by blast
  have sub_wf: "formula_well_formed (alphabet F) (?sub v)" for v
    using marker_substitution_range[of names arguments v] wf by auto
  have instantiated: "bounded_derivation F (sub_formula ?sub ` H) (sub_formula ?sub A)
    l (s * max 1 (sum_list (map len_formula arguments))) (d + depth_sub (set names) ?sub)"
    using bounded_derivation_subst[OF fs base finite_set outside sub_wf]
    by (simp only: marker_substitution_length[OF names])
  show ?thesis
    by (rule bounded_derivation_weaken[OF instantiated subset_refl le_refl le_refl])
       (use marker_substitution_depth[OF dep, where names=names] in simp)
qed

lemma bounded_derivation_cut_max:
  assumes fs: "frege_system F"
    and prem: "bounded_derivation F {} A l s d"
    and rule: "bounded_derivation F (insert A H) B l' s' d'"
  shows "bounded_derivation F H B (l + l') (max s s') (max d d')"
proof -
  obtain p where p: "valid_proof F p" "assumptions p = {}"
    "frege_proof.thesis p = A" "length (steps p) \<le> l"
    "\<forall>t\<in>set (steps p). len_formula t \<le> s \<and> depth_formula t \<le> d
                              \<and> formula_well_formed (alphabet F) t"
    using prem unfolding bounded_derivation_def by auto
  obtain q where q: "valid_proof F q" "assumptions q \<subseteq> insert A H"
    "frege_proof.thesis q = B" "length (steps q) \<le> l'"
    "\<forall>t\<in>set (steps q). len_formula t \<le> s' \<and> depth_formula t \<le> d'
                              \<and> formula_well_formed (alphabet F) t"
    using rule unfolding bounded_derivation_def by auto
  have valid: "valid_proof F (combine_proofs p q)"
    using frege_system.combining_valid_proofs[OF fs] p(1) q(1) by blast
  have asm: "assumptions (combine_proofs p q) \<subseteq> H"
    using valid_proof_thesis_mem[OF p(1)] p(2,3) q(2) by auto
  show ?thesis unfolding bounded_derivation_def
    by (rule exI[of _ "combine_proofs p q"])
       (use valid asm p(4,5) q(3,4,5) in auto)
qed

lemma bounded_derivation_cut:
  assumes "frege_system F"
    "bounded_derivation F {} A l s d"
    "bounded_derivation F (insert A H) B l' s' d'"
  shows "bounded_derivation F H B (l + l') (s + s') (max d d')"
  by (rule bounded_derivation_weaken[OF bounded_derivation_cut_max[OF assms]
              subset_refl le_refl _ le_refl]) simp

lemma bounded_derivation_cuts:
  assumes fs: "frege_system F"
    and closed: "\<And>i. i \<in> set inds \<Longrightarrow> bounded_derivation F {} (prem i) (lf i) Sc Dc"
    and base: "bounded_derivation F (prem ` set inds \<union> H) A L S D"
  shows "bounded_derivation F H A
    (sum_list (map lf inds) + L) (max Sc S) (max Dc D)"
  using base closed
proof (induction inds arbitrary: H)
  case Nil
  show ?case
    by (rule bounded_derivation_weaken[OF Nil.prems(1)])
       simp_all
next
  case (Cons i inds)
  have rest: "bounded_derivation F (insert (prem i) H) A
    (sum_list (map lf inds) + L) (max Sc S) (max Dc D)"
    by (rule Cons.IH)
       (use Cons.prems in \<open>auto simp: insert_commute\<close>)
  have head: "bounded_derivation F {} (prem i) (lf i) Sc Dc"
    using Cons.prems(2) by simp
  show ?case using bounded_derivation_cut_max[OF fs head rest]
    by (simp add: add.assoc max.assoc)
qed

definition equiv_proofs :: "'c1 frege_proof \<Rightarrow> 'c1 frege \<Rightarrow> 'c2 frege_proof \<Rightarrow> 'c2 frege \<Rightarrow> bool" where
  "equiv_proofs pr1 F1 pr2 F2 \<longleftrightarrow> (frege_system F1 \<and> valid_proof F1 pr1 \<and>
                                   frege_system F2 \<and> valid_proof F2 pr2 \<and>
                                   equiv_formula_sets (assumptions pr1) (alphabet F1) (assumptions pr2) (alphabet F2) \<and>
                                   formulas_equiv (thesis pr1) (alphabet F1) (thesis pr2) (alphabet F2))"


text \<open>
  A simulation uses a faithful translation of formulas: every well-formed
  target formula must map to an equivalent, well-formed source formula of
  polynomially bounded size.  This condition is unconditional.  Without it,
  an ill-formed translation could make the proof condition vacuous, because
  every step of a valid source proof must be well-formed.

  The translated proof has size polynomial in the source proof size plus the
  target formula size, as in the two-language setting discussed by Kraj\'i\v{c}ek.
  The predicate below specifies size bounds; it does not require the
  translation functions to run in polynomial time.
\<close>

definition simulates :: "'c1 frege \<Rightarrow> 'c2 frege \<Rightarrow> bool" where
  "simulates F1 F2 \<longleftrightarrow>
     (\<exists> f g p q.
        (\<forall> \<tau>. formula_well_formed (alphabet F2) \<tau> \<longrightarrow>
                formula_well_formed (alphabet F1) (g \<tau>)
              \<and> formulas_equiv (g \<tau>) (alphabet F1) \<tau> (alphabet F2)
              \<and> len_formula (g \<tau>) \<le> poly p (len_formula \<tau>))
      \<and> (\<forall> w \<tau>.
           (formula_well_formed (alphabet F2) \<tau>
            \<and> thesis w = g \<tau> \<and> valid_proof F1 w \<and> assumptions w = {}
            \<and> (\<forall> s \<in> set (steps w). formula_well_formed (alphabet F1) s))
           \<longrightarrow> valid_proof F2 (f w \<tau>)
               \<and> thesis (f w \<tau>) = \<tau>
               \<and> assumptions (f w \<tau>) = {}
               \<and> len_proof (f w \<tau>) \<le> poly q (len_proof w + len_formula \<tau>)))"

end
