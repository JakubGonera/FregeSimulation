theory Frege
  imports Main "HOL-Computational_Algebra.Polynomial"
begin

(* A formula can be built over arbitrary connectives, 
  evaluation of which we supply later in a Frege *)

datatype formula = 
  Atom string |
  Conn string "formula list"

record rule =
  prems :: "formula list"
  concl :: "formula"

record alphabet = 
  conns :: "string set"
  conn_evals :: "string \<Rightarrow> (bool list \<Rightarrow> bool)"

record frege =
  rules :: "rule set"
  alphabet :: "alphabet"

fun eval :: "alphabet \<Rightarrow> (string \<Rightarrow> bool) \<Rightarrow> formula \<Rightarrow> bool" where
  "eval al v (Atom a) = v a" |
  "eval al v (Conn c fs) = (conn_evals al c) (map (eval al v) fs)"

record frege_proof =
  assumptions :: "formula set"
  thesis :: "formula"
  steps :: "formula list"

fun sub_formula :: "(string \<Rightarrow> formula) \<Rightarrow> formula \<Rightarrow> formula" where
  "sub_formula sub (Atom a) = sub a" |
  "sub_formula sub (Conn c fs) = Conn c (map (sub_formula sub) fs)"

fun sub_rule :: "(string \<Rightarrow> formula) \<Rightarrow> rule \<Rightarrow> rule" where
  "sub_rule sub r = \<lparr>
    prems = map (sub_formula sub) (prems r),
    concl = sub_formula sub (concl r)
  \<rparr>"

fun sub_proof :: "(string \<Rightarrow> formula) \<Rightarrow> frege_proof \<Rightarrow> frege_proof" where
  "sub_proof sub pr = \<lparr>
    assumptions = (sub_formula sub)` (assumptions pr),
    thesis = sub_formula sub (thesis pr),
    steps = map (sub_formula sub) (steps pr)
\<rparr>"

definition derived :: "rule set \<Rightarrow> formula list \<Rightarrow> formula \<Rightarrow> bool" where
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


definition valid_proof :: "frege \<Rightarrow> frege_proof \<Rightarrow> bool" where
  "valid_proof F pr \<longleftrightarrow> 
    thesis pr = last (steps pr) \<and> steps pr \<noteq> []
    \<and> (\<forall>i < length (steps pr). 
 steps pr ! i \<in> assumptions pr \<or> derived (rules F) (take i (steps pr)) (steps pr ! i))"

fun combine_proofs :: "frege_proof \<Rightarrow> frege_proof \<Rightarrow> frege_proof" where
  "combine_proofs pr1 pr2 = \<lparr>assumptions = assumptions pr1 \<union> (assumptions pr2 - set (steps pr1)),
                             thesis = thesis pr2,
                             steps = steps pr1 @ steps pr2\<rparr>"

definition sound_rule :: "frege \<Rightarrow> rule \<Rightarrow> bool" where
  "sound_rule F r \<longleftrightarrow> 
    (\<forall> val. (\<forall> form \<in> set (prems r). eval (alphabet F) val form) \<longrightarrow> eval (alphabet F) val (concl r))"

fun len_formula :: "formula \<Rightarrow> nat" where
  "len_formula (Atom s) = 1" |
  "len_formula (Conn s fs) = 1 + sum_list (map (\<lambda> f. len_formula f) fs)"

fun len_proof :: "frege_proof \<Rightarrow> nat" where
  "len_proof pr = sum_list (map len_formula (steps pr))"

definition len_sub :: "(string \<Rightarrow> formula) \<Rightarrow> nat" where
  "len_sub sub =
     (\<Sum> s \<in> {s. len_formula (sub s) \<noteq> 0}. len_formula (sub s))"

locale frege_system = 
  fixes F :: frege
  assumes sound: "\<forall> r \<in> rules F. sound_rule F r"
  and impl_complete: "\<forall> fs th val. ((\<forall> f \<in> fs. eval (alphabet F) val f) \<longrightarrow> eval (alphabet F) val th) 
                          \<longrightarrow> (\<exists> pr. valid_proof F pr
                                   \<and> assumptions pr = fs 
                                   \<and> thesis pr = th)"
  and finite: "finite (rules F)"
begin

lemma combining_valid_proofs_pr1:
  fixes pr1 :: frege_proof and pr2 :: frege_proof
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
  have "steps pr1 ! i \<in> assumptions pr1 \<or> 
        derived (rules F) (take i (steps pr1)) (steps pr1 ! i)" 
    using assms valid_proof_def by simp
  thus ?thesis using 2 3 by blast
qed

lemma combining_valid_proofs:
  fixes pr1 :: frege_proof and pr2 :: frege_proof
  assumes "valid_proof F pr1 \<and> valid_proof F pr2"
  and "comb = combine_proofs pr1 pr2"
  shows "valid_proof F comb"
proof -
 have app: "steps comb = (steps pr1) @ (steps pr2)" using assms(2) by simp
  hence "last (steps comb) = last (steps pr2)" using assms(1) valid_proof_def by simp
  hence a: "thesis comb = last (steps comb) \<and> steps comb \<noteq> []" 
    using assms valid_proof_def by simp

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
        hence 12: "steps pr2 ! (i - ?j) = steps comb ! i" using False app by (simp add: nth_append_right)
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
        have repeat_proof: "((\<exists> k < ?j. steps comb ! k = steps comb ! i) \<and> \<not> (steps comb ! i \<in> assumptions comb)) \<longrightarrow> 
              derived (rules F) (take i (steps comb)) (steps comb ! i)"
        proof
          assume assm: "(\<exists> k < ?j. steps comb ! k = steps comb ! i) \<and> \<not> (steps comb ! i \<in> assumptions comb)"
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
            by (metis False derived_mono eq k_lt linorder_not_le order_less_trans set_take_subset_set_take)
        qed
        have 32: "derived (rules F) (take (i - ?j) (steps pr2)) (steps pr2 ! (i - ?j)) \<longrightarrow> 
              derived (rules F) (take i (steps comb)) (steps comb ! i)" using 12 02 derived_mono
          by (metis drop_take set_drop_subset)
        have "steps pr2 ! (i - ?j) \<in> assumptions pr2 \<or> 
              derived (rules F) (take (i - ?j) (steps pr2)) (steps pr2 ! (i - ?j))" 
          using assms(1) False valid_proof_def i_in_range app by simp
        thus "steps comb ! i \<in> assumptions comb \<or> 
              derived (rules F) (take i (steps comb)) (steps comb ! i)" using 22 32 repeat_proof by auto
      qed
    qed
  qed

  show ?thesis using a b valid_proof_def by simp
qed

lemma proof_substitution:
  fixes pr :: frege_proof 
    and sub :: "string \<Rightarrow> formula"
  assumes "valid_proof F pr"
  shows "valid_proof F (sub_proof sub pr)"
proof -
  have sub_formula_comp:
    "sub_formula s1 (sub_formula s2 f) =
      sub_formula (\<lambda>a. sub_formula s1 (s2 a)) f"
    for s1 s2 f
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
      have "concl (sub_rule ?s' r) = sub_formula sub (concl (sub_rule s r))"
        using sub_formula_comp by (cases r) simp
      also have "... = sub_formula sub f"
        using concl_eq by simp
      finally show ?thesis .
    qed
    have prems_sub:
      "\<forall>p \<in> set (prems (sub_rule ?s' r)). \<exists>q \<in> set (map (sub_formula sub) fs). p = q"
    proof
      fix p
      assume "p \<in> set (prems (sub_rule ?s' r))"
      then have p_in:
        "p \<in> set (map (sub_formula sub) (prems (sub_rule s r)))"
        using sub_formula_comp by (cases r) simp
      then obtain p0 where
        p0_in: "p0 \<in> set (prems (sub_rule s r))"
        and p_eq: "p = sub_formula sub p0"
        by auto
      from prems_fs p0_in obtain q where "q \<in> set fs" and "p0 = q" by auto
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

definition simulates :: "frege \<Rightarrow> frege \<Rightarrow> bool" where
 "simulates F1 F2 \<longleftrightarrow> (\<exists> f g p q. \<forall> w \<tau>. (thesis w = g \<tau> \<and> valid_proof F1 w) \<longrightarrow> 
    valid_proof F2 (f w \<tau>) \<and> thesis (f w \<tau>) = \<tau> \<and> 
    len_formula (g \<tau>) \<le> poly p (len_formula \<tau>) \<and>
    len_proof w \<le> poly q (len_proof (f w \<tau>)))"


(* A theorem on (only) simulation of Frege systems. For p-simulation we need f and
  g to be polynomial time*)
theorem Reckhow:
  assumes "frege_system F1 \<and> frege_system F2"
  shows "simulates F1 F2"
  sorry

  
end
