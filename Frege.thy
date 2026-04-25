theory Frege
  imports Main "HOL-Computational_Algebra.Polynomial"
begin

(* A formula can be built over arbitrary connectives,
  evaluation of which we supply later in a Frege *)

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

lemma depth_sub_ge_1:
  assumes "finite var_set"
  shows "1 \<le> depth_sub var_set sub"
  unfolding depth_sub_def using assms by simp

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
  let ?L = "len_sub var_set sub"
  let ?steps = "steps pr"

  have step_bound:
    "\<forall>f \<in> set ?steps. len_formula (sub_formula sub f) \<le> len_formula f * ?L"
    using assms sub_formula_bound by blast

  have sum_bound_gen:
    "sum_list (map (\<lambda>f. len_formula (sub_formula sub f)) xs)
     \<le> sum_list (map (\<lambda>f. len_formula f * ?L) xs)"
    for xs
  proof (induction xs)
    case Nil
    then show ?case by simp
  next
    case (Cons f fs)
    have f_bound: "len_formula (sub_formula sub f) \<le> len_formula f * ?L"
      using assms sub_formula_bound[where f = f and sub = sub and var_set = var_set] by simp
    have fs_bound:
      "sum_list (map (\<lambda>f. len_formula (sub_formula sub f)) fs)
       \<le> sum_list (map (\<lambda>f. len_formula f * ?L) fs)"
      using Cons.IH by simp
    have comb:
      "len_formula (sub_formula sub f) + sum_list (map (\<lambda>f. len_formula (sub_formula sub f)) fs)
       \<le> len_formula f * ?L + sum_list (map (\<lambda>f. len_formula f * ?L) fs)"
      using add_mono[OF f_bound fs_bound] by simp
    show ?case
      using comb by simp
  qed
  have sum_bound:
    "sum_list (map (\<lambda>f. len_formula (sub_formula sub f)) (steps pr))
     \<le> sum_list (map (\<lambda>f. len_formula f * ?L) (steps pr))"
    using sum_bound_gen[of "steps pr"] .

  have scaled_sum_gen:
    "sum_list (map (\<lambda>f. len_formula f * ?L) xs) = sum_list (map len_formula xs) * ?L"
    for xs
  proof (induction xs)
    case Nil
    then show ?case by simp
  next
    case (Cons f fs)
    then show ?case
      by (simp add: algebra_simps)
  qed
  have scaled_sum:
    "sum_list (map (\<lambda>f. len_formula f * ?L) ?steps) = sum_list (map len_formula ?steps) * ?L"
    using scaled_sum_gen[of ?steps] .

  have lhs:
    "len_proof (sub_proof sub pr) = sum_list (map (\<lambda>f. len_formula (sub_formula sub f)) ?steps)"
    by (simp add: comp_def)
  have rhs:
    "len_proof pr * ?L = sum_list (map len_formula ?steps) * ?L"
    by simp

  show ?thesis
    using lhs rhs sum_bound scaled_sum by simp
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
        using f'_in fin_fs by (simp add: Max_ge)
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

lemma sub_proof_depth_bound:
  fixes pr :: "'c frege_proof"
  and sub :: "(string \<Rightarrow> 'c formula)"
  and var_set :: "string set"
  assumes finite_vs: "finite var_set"
  and identity_outside: "\<forall> v. v \<notin> var_set \<longrightarrow> sub v = Atom v"
  and steps_ne: "steps pr \<noteq> []"
  shows "depth_proof (sub_proof sub pr) \<le> depth_proof pr + depth_sub var_set sub"
proof -
  let ?D = "depth_sub var_set sub"
  let ?steps = "steps pr"
  let ?steps' = "map (sub_formula sub) ?steps"

  have steps'_eq: "steps (sub_proof sub pr) = ?steps'" by simp
  have ne': "?steps' \<noteq> []" using steps_ne by simp

  have fin: "finite (set (map depth_formula ?steps))" by simp
  have fin': "finite (set (map depth_formula ?steps'))" by simp
  have ne_set': "set (map depth_formula ?steps') \<noteq> {}" using ne' by simp

  have step_bound:
    "\<forall>f \<in> set ?steps. depth_formula (sub_formula sub f) \<le> depth_formula f + ?D"
    using sub_formula_depth_bound[OF finite_vs identity_outside] by blast

  have all_le: "\<forall>x \<in> set (map depth_formula ?steps'). x \<le> depth_proof pr + ?D"
  proof
    fix x assume "x \<in> set (map depth_formula ?steps')"
    then obtain f where f_in: "f \<in> set ?steps"
                    and x_eq: "x = depth_formula (sub_formula sub f)"
      by auto
    from step_bound f_in
    have ih: "depth_formula (sub_formula sub f) \<le> depth_formula f + ?D"
      by blast
    have df_le: "depth_formula f \<le> depth_proof pr"
      using f_in fin by (simp add: Max_ge)
    from ih df_le show "x \<le> depth_proof pr + ?D"
      using x_eq by simp
  qed

  have "depth_proof (sub_proof sub pr) = Max (set (map depth_formula ?steps'))"
    using steps'_eq by simp
  also have "\<dots> \<le> depth_proof pr + ?D"
  proof (rule Max.boundedI)
    show "finite (set (map depth_formula ?steps'))" using fin' .
    show "set (map depth_formula ?steps') \<noteq> {}" using ne_set' .
    fix a assume "a \<in> set (map depth_formula ?steps')"
    thus "a \<le> depth_proof pr + ?D" using all_le by blast
  qed
  finally show ?thesis .
qed

definition formulas_equiv :: "'c1 formula \<Rightarrow> 'c1 alphabet \<Rightarrow> 'c2 formula \<Rightarrow> 'c2 alphabet \<Rightarrow> bool" where
  "formulas_equiv f1 a1 f2 a2 \<longleftrightarrow> (\<forall> val. eval a1 val f1 = eval a2 val f2)"

locale frege_system =
  fixes F :: "'c frege"
  assumes sound: "\<forall> r \<in> rules F. sound_rule F r"
  and impl_complete:
    "\<forall> fs th.
       (\<forall> val. (\<forall> f \<in> fs. eval (alphabet F) val f) \<longrightarrow> eval (alphabet F) val th)
       \<longrightarrow> (\<exists> pr. valid_proof F pr
                 \<and> assumptions pr = fs
                 \<and> thesis pr = th)"
  and finite: "finite (rules F)"
  and finite_alphabet: "finite (UNIV :: 'c set)"
  and func_complete:
    "\<forall>f :: dm_conn formula.
       \<exists> f' :: 'c formula. formulas_equiv f dm_alphabet f' (alphabet F)"
begin

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

definition simulates :: "'c frege \<Rightarrow> 'c frege \<Rightarrow> bool" where
  "simulates F1 F2 \<longleftrightarrow>
     (\<exists> f g p q. \<forall> w \<tau>.
        (thesis w = g \<tau> \<and> valid_proof F1 w \<and> assumptions w = {})
        \<longrightarrow> valid_proof F2 (f w \<tau>)
            \<and> thesis (f w \<tau>) = \<tau>
            \<and> assumptions (f w \<tau>) = {}
            \<and> len_formula (g \<tau>) \<le> poly p (len_formula \<tau>)
            \<and> len_proof (f w \<tau>) \<le> poly q (len_proof w))"

(* A theorem on (only) simulation of Frege systems. For p-simulation we need f and
  g to be polynomial time*)
theorem Reckhow:
  assumes "frege_system F1 \<and> frege_system F2"
  shows "simulates F1 F2"
  sorry

end
