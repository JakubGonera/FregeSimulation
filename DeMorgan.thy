theory DeMorgan
  imports Frege
begin

type_synonym dformula = "dm_conn formula"
type_synonym drule = "dm_conn rule"
type_synonym dfrege = "dm_conn frege"
type_synonym dproof = "dm_conn frege_proof"

(* -- General lemmas that might be useful for the main proof as well -- *)
definition derived_with :: "nat \<Rightarrow> dproof \<Rightarrow> drule \<Rightarrow> (string \<Rightarrow> dformula) \<Rightarrow> bool" where
  "derived_with i pr r s \<longleftrightarrow> (let sub_r = sub_rule s r in
                       i < length (steps pr) \<and> (concl sub_r) = steps pr ! i \<and>
                       (\<forall>f1 \<in> set (prems sub_r). \<exists>f2 \<in> set (take i (steps pr)). f1 = f2))"

lemma step_le_proof:
  shows "\<forall>pr. \<forall>f \<in> set (steps pr). len_formula f \<le> len_proof pr"
proof -
  have member_le_sum:
    "len_formula f \<le> sum_list (map len_formula fs)"
    if "f \<in> set fs"
    for f :: "'c formula" and fs :: "'c formula list"
    using that
  proof (induction fs)
    case Nil
    then show ?case by simp
  next
    case (Cons g gs)
    show ?case
    proof (cases "f = g")
      case True
      then show ?thesis by simp
    next
      case False
      then have "f \<in> set gs"
        using Cons.prems by simp
      then have "len_formula f \<le> sum_list (map len_formula gs)"
        using Cons.IH by simp
      then show ?thesis by simp
    qed
  qed
  have step_bound:
    "len_formula f \<le> len_proof pr"
    if "f \<in> set (steps pr)"
    for pr :: "'c frege_proof" and f :: "'c formula"
    using member_le_sum[of f "steps pr"] that by simp
  show ?thesis
  proof (rule allI)
    fix pr :: "'c frege_proof"
    show "\<forall>f \<in> set (steps pr). len_formula f \<le> len_proof pr"
    proof (rule ballI)
      fix f :: "'c formula"
      assume "f \<in> set (steps pr)"
      then show "len_formula f \<le> len_proof pr"
        using step_bound by blast
    qed
  qed
qed

lemma var_set_rule_finite:
  shows "finite (var_set_rule r)"
proof (cases r)
  case (fields prems concl)
  have fin_prems: "finite (\<Union> (var_set_form ` set prems))"
  proof (induction prems)
    case Nil
    then show ?case by simp
  next
    case (Cons p ps)
    have fin_p: "finite (var_set_form p)"
      by (induction p) auto
    then show ?case
      using Cons by auto
  qed
  have fin_concl: "finite (var_set_form concl)"
    by (induction concl) auto
  show ?thesis
    using fields fin_prems fin_concl by simp
qed

(* -- End of general proofs -- *)

locale de_morgan_frege =
  fixes F :: dfrege
  assumes alph: "alphabet F = dm_alphabet"
  and "frege_system F"
  and rules_wf: "\<forall>r \<in> rules F. (\<forall>f \<in> set (prems r). formula_well_formed (alphabet F) f)
                                \<and> formula_well_formed (alphabet F) (concl r)"
begin
abbreviation a where "a \<equiv> alphabet F"

lemma len_sub_bound_by_proof:
  assumes "r \<in> rules F"
      and "derived_with i pr r s"
      and "rule_restricted_sub r s"
      and "c = Max ((\<lambda>r. card (var_set_rule r)) ` rules F) + 1"
      and "valid_proof F pr"
    shows "len_sub (var_set_rule r) s \<le> c * len_proof pr"
proof -
  let ?var_set = "var_set_rule r"
  have sub_bound: "\<forall>f. \<forall>v \<in> var_set_form f. len_formula (s v) \<le> len_formula (sub_formula s f)"
  proof
    fix f
    show "\<forall>v \<in> var_set_form f. len_formula (s v) \<le> len_formula (sub_formula s f)"
    proof (induction f)
      case (Atom x)
      show ?case by simp
    next
      case (Conn c gs)
      have "sub_formula s (Conn c gs) = Conn c (map (sub_formula s) gs)" by simp
      hence "len_formula (sub_formula s (Conn c gs)) =
                1 + sum_list (map (\<lambda>g. len_formula g) (map (sub_formula s) gs))"
        by simp
      hence unroll: "len_formula (sub_formula s (Conn c gs)) =
                1 + sum_list (map (\<lambda>g. len_formula (sub_formula s g)) gs)"
      proof (induction gs)
        case Nil
        then show ?case by simp
      next
        case (Cons g gs)
        then show ?case by simp
      qed
      have var_in_gs: "v \<in> var_set_form (Conn c gs) \<longrightarrow> (\<exists>f \<in> set gs. v \<in> var_set_form f)"
        by simp
      have g_le:
        "\<forall>g \<in> set gs. len_formula (sub_formula s g) \<le> len_formula (sub_formula s (Conn c gs))"
      proof
        fix g
        assume g_in: "g \<in> set gs"
        have g_sum_bound:
          "len_formula (sub_formula s g)
             \<le> sum_list (map (\<lambda>g. len_formula (sub_formula s g)) gs)"
          using g_in
        proof (induction gs)
          case Nil
          then show ?case by simp
        next
          case (Cons h hs)
          then show ?case by (cases "g = h") simp_all
        qed
        show "len_formula (sub_formula s g) \<le> len_formula (sub_formula s (Conn c gs))"
        proof -
          have sum_bound:
            "sum_list (map (\<lambda>g. len_formula (sub_formula s g)) gs)
              \<le> len_formula (sub_formula s (Conn c gs))"
          proof (induction gs)
            case Nil
            then show ?case by simp
          next
            case (Cons h hs)
            then show ?case by simp
          qed
          show ?thesis
            using g_sum_bound sum_bound by arith
        qed
      qed
      show ?case
      proof (intro ballI)
        fix v
        assume v_in: "v \<in> var_set_form (Conn c gs)"
        have ex_g: "\<exists>g \<in> set gs. v \<in> var_set_form g"
          using var_in_gs v_in by simp
        then obtain g where g_in: "g \<in> set gs" and vg_in: "v \<in> var_set_form g"
          by blast
        have IHg: "\<forall>v \<in> var_set_form g. len_formula (s v) \<le> len_formula (sub_formula s g)"
          using Conn.IH g_in by blast
        have v_to_g: "len_formula (s v) \<le> len_formula (sub_formula s g)"
          using IHg vg_in by blast
        have g_to_conn: "len_formula (sub_formula s g) \<le> len_formula (sub_formula s (Conn c gs))"
          using g_le g_in by blast
        show "len_formula (s v) \<le> len_formula (sub_formula s (Conn c gs))"
          using v_to_g g_to_conn by arith
      qed
    qed
  qed
  have form_bound: "\<forall>v \<in> ?var_set. len_formula (s v) \<le> len_proof pr"
  proof (intro ballI)
    fix v
    assume v_in_vs: "v \<in> ?var_set"
    show "len_formula (s v) \<le> len_proof pr"
    proof (cases "v \<in> var_set_form (concl r)")
      case True
      have "concl (sub_rule s r) \<in> set (steps pr)"
        using assms(2) derived_with_def by simp
      hence a: "len_formula (concl (sub_rule s r)) \<le> len_proof pr"
        using step_le_proof by blast
      have b: "concl (sub_rule s r) = sub_formula s (concl r)" by simp
      have c: "len_formula (s v) \<le> len_formula (sub_formula s (concl r))"
        using sub_bound True by simp
      thus ?thesis using a b by simp
    next
      case False
      hence v_in_prem: "v \<in> \<Union> (var_set_form ` set (prems r))"
        using v_in_vs by simp
      obtain f :: dformula
        where v_def: "v \<in> var_set_form f \<and> f \<in> set (prems r)"
        using v_in_prem by auto
      then obtain g :: dformula
        where g_eq: "g \<in> set (prems (sub_rule s r)) \<and> g = sub_formula s f"
        by auto
      hence "g \<in> set (steps pr)" using assms(2) derived_with_def
        by (meson in_set_takeD)
      hence g_le: "len_formula g \<le> len_proof pr"
        using step_le_proof by blast
      have "len_formula (s v) \<le> len_formula g"
        using g_eq v_def sub_bound by simp
      thus ?thesis using g_le by simp
    qed
  qed
  have c_bound: "card ?var_set \<le> c"
  proof -
    let ?set = "(\<lambda>r. card (var_set_rule r)) ` rules F"
    have "finite (rules F)"
      using de_morgan_frege_axioms de_morgan_frege_def by (simp add: frege_system.finite)
    hence "finite ?set" by simp
    thus ?thesis using Max_ge[of ?set] assms(1,4)
      by (meson image_iff trans_le_add1)
  qed
  have "len_sub ?var_set s = max 1 (\<Sum>v \<in> ?var_set. len_formula (s v))"
    using len_sub_def by simp
  hence "len_sub ?var_set s \<le> max 1 (\<Sum>v \<in> ?var_set. len_proof pr)"
    using form_bound
    by (smt (verit) max.absorb_iff2 max.boundedE max.orderE nat_le_linear sum_mono)
  hence "len_sub ?var_set s \<le> max 1 (card ?var_set * len_proof pr)"
    by simp
  hence "len_sub ?var_set s \<le> max 1 (c * len_proof pr)" using c_bound
    by (meson dual_order.trans le_numeral_extra(4) max.mono mult_le_cancel2)
  thus ?thesis using len_proof_positive assms(4)
    by (metis assms(5) le_add2 less_one linorder_not_le max_absorb2 mult_is_0)
qed
end

locale de_morgan_sim =
  fixes F :: dfrege and F' :: dfrege
  assumes dm1: "de_morgan_frege F" and dm2: "de_morgan_frege F'"
begin

lemma proof_exists_for_rule:
  assumes "rule \<in> rules F"
    shows "\<exists> pr. valid_proof F' pr \<and> assumptions pr = set (prems rule) \<and> thesis pr = concl rule"
proof -
  have alph_eq: "alphabet F = alphabet F'"
    using dm1 dm2 de_morgan_frege_def by fastforce
  hence val_sat: "\<forall> val. (\<forall> f \<in> set (prems rule). eval (alphabet F') val f)
                \<longrightarrow> eval (alphabet F') val (concl rule)"
    using dm1 assms frege_system.sound sound_rule_def
    by (metis de_morgan_frege_def)
  have rwf0: "(\<forall>f\<in>set (prems rule). formula_well_formed (alphabet F) f)
              \<and> formula_well_formed (alphabet F) (concl rule)"
    using de_morgan_frege.rules_wf[OF dm1] assms by blast
  have rwf: "(\<forall>f\<in>set (prems rule). formula_well_formed (alphabet F') f)
             \<and> formula_well_formed (alphabet F') (concl rule)"
    using rwf0 alph_eq by simp
  have "(\<forall>f\<in>set (prems rule). formula_well_formed (alphabet F') f) \<longrightarrow>
        formula_well_formed (alphabet F') (concl rule) \<longrightarrow>
        (\<forall> val. (\<forall> f \<in> set (prems rule). eval (alphabet F') val f) \<longrightarrow>
                 eval (alphabet F') val (concl rule))
                          \<longrightarrow> (\<exists> pr. valid_proof F' pr
                                   \<and> assumptions pr = set (prems rule)
                                   \<and> thesis pr = concl rule)"
    using dm2 frege_system.impl_complete[of F'] de_morgan_frege_def by blast
  thus ?thesis using val_sat rwf by blast
qed

lemma rule_proof_fun_exists: "\<exists> f :: drule \<Rightarrow> dproof. \<forall> rule \<in> rules F.
          valid_proof F' (f rule) \<and>
          assumptions (f rule) = set (prems rule) \<and>
          thesis (f rule) = concl rule"
  by (meson proof_exists_for_rule)

definition rule_proof_fun where
  "rule_proof_fun = (SOME f. \<forall> rule \<in> rules F.
          valid_proof F' (f rule) \<and>
          assumptions (f rule) = set (prems rule) \<and>
          thesis (f rule) = concl rule)"

fun step_proof :: "drule \<Rightarrow> (string \<Rightarrow> dformula) \<Rightarrow> dproof" where
  "step_proof rule sub = sub_proof sub (rule_proof_fun rule)"

lemma step_proof_proves:
  assumes "r \<in> rules F"
  shows "valid_proof F' (step_proof r s) \<and>
         assumptions (step_proof r s) = set (prems (sub_rule s r)) \<and>
         thesis (step_proof r s) = concl (sub_rule s r)"
proof -
  have ex_fun:
    "\<exists>f :: drule \<Rightarrow> dproof. \<forall>rule \<in> rules F.
      valid_proof F' (f rule)
      \<and> assumptions (f rule) = set (prems rule)
      \<and> thesis (f rule) = concl rule"
    using rule_proof_fun_exists .
  have fun_prop:
    "\<forall>rule \<in> rules F.
      valid_proof F' (rule_proof_fun rule) \<and>
      assumptions (rule_proof_fun rule) = set (prems rule) \<and>
      thesis (rule_proof_fun rule) = concl rule"
    unfolding rule_proof_fun_def by (rule someI_ex[OF ex_fun])
  then have base:
    "valid_proof F' (rule_proof_fun r) \<and>
     assumptions (rule_proof_fun r) = set (prems r) \<and>
     thesis (rule_proof_fun r) = concl r"
    using assms by blast
  then have base_valid: "valid_proof F' (rule_proof_fun r)"
    and base_assm: "assumptions (rule_proof_fun r) = set (prems r)"
    and base_th: "thesis (rule_proof_fun r) = concl r"
    by auto
  have fsys: "frege_system F'"
    using dm2 unfolding de_morgan_frege_def by simp
  interpret fs: frege_system F'
    by (rule fsys)
  have sub_valid: "valid_proof F' (step_proof r s)"
    unfolding step_proof.simps using fs.proof_substitution[OF base_valid] .
  have sub_assm: "assumptions (step_proof r s) = set (prems (sub_rule s r))"
    using base_assm by simp
  have sub_th: "thesis (step_proof r s) = concl (sub_rule s r)"
    using base_th by simp
  show ?thesis
    using sub_valid sub_assm sub_th by simp
qed

definition choose_rule_sub where
  "choose_rule_sub frege i pr =
     (SOME (r,s). r \<in> rules frege \<and> derived_with i pr r s \<and> rule_restricted_sub r s)"

definition sim_step :: "dproof \<Rightarrow> nat \<Rightarrow> dproof \<Rightarrow> dproof" where
  "sim_step pr i acc =
    (let step = (steps pr) ! i in
      if step \<in> assumptions pr then
        combine_proofs acc \<lparr>assumptions = {}, thesis = step, steps = [step]\<rparr>
      else
        let (r, s) = choose_rule_sub F i pr in
        let pr = step_proof r s
        in combine_proofs acc pr)"

definition sim :: "dproof \<Rightarrow> dformula \<Rightarrow> dproof" where
  "sim pr th =
     fold (sim_step pr)
       [0..<length (steps pr)]
       \<lparr>assumptions = assumptions pr,
        thesis = th,
        steps = []\<rparr>"

lemma sub_formula_agree:
  "sub_formula s1 f = sub_formula s2 f"
  if "\<forall>v \<in> var_set_form f. s1 v = s2 v"
  for s1 s2 :: "string \<Rightarrow> dformula" and f
  using that
proof (induction f)
  case (Atom x)
  then show ?case by simp
next
  case (Conn c fs)
  then show ?case by simp
qed

lemma sub_rule_agree:
  "sub_rule s1 r = sub_rule s2 r"
  if "\<forall>v \<in> var_set_rule r. s1 v = s2 v"
  for s1 s2 :: "string \<Rightarrow> dformula" and r
using that
by (cases r) (auto intro: sub_formula_agree)

lemma choose_rule_sub_props:
  assumes "\<exists>r s. r \<in> rules G \<and> derived_with i p r s"
  shows "fst (choose_rule_sub G i p) \<in> rules G \<and>
         derived_with i p (fst (choose_rule_sub G i p)) (snd (choose_rule_sub G i p)) \<and>
         rule_restricted_sub (fst (choose_rule_sub G i p)) (snd (choose_rule_sub G i p))"
proof -
  from assms obtain r s where r_in: "r \<in> rules G" and dwith: "derived_with i p r s"
    by blast
  define s' where "s' = (\<lambda>v. if v \<in> var_set_rule r then s v else Atom v)"
  have rs_eq: "sub_rule s' r = sub_rule s r"
    unfolding s'_def by (rule sub_rule_agree) auto
  have dwith': "derived_with i p r s'"
    using dwith unfolding derived_with_def rs_eq by simp
  have rsub': "rule_restricted_sub r s'"
    unfolding rule_restricted_sub_def s'_def by simp
  let ?P = "\<lambda>rs :: drule \<times> (string \<Rightarrow> dformula).
    case rs of (r, s) \<Rightarrow> r \<in> rules G \<and> derived_with i p r s \<and> rule_restricted_sub r s"
  have ex_pair: "\<exists>rs. ?P rs"
    using r_in dwith' rsub' by force
  have "?P (SOME rs. ?P rs)"
    by (rule someI_ex[OF ex_pair])
  then show ?thesis
    unfolding choose_rule_sub_def by (cases "SOME rs. ?P rs") auto
qed

lemma sim_step_progress:
  fixes pr acc :: dproof
  assumes valid_pr: "valid_proof F pr"
      and assm_pr: "assumptions pr = {}"
      and k_lt: "k < length (steps pr)"
      and acc_assm: "assumptions acc = {}"
      and acc_steps: "set (take k (steps pr)) \<subseteq> set (steps acc)"
      and acc_valid: "k = 0 \<or> valid_proof F' acc"
      and acc0: "k = 0 \<longrightarrow> steps acc = []"
  shows "assumptions (sim_step pr k acc) = {} \<and>
         valid_proof F' (sim_step pr k acc) \<and>
         thesis (sim_step pr k acc) = steps pr ! k \<and>
         set (take (Suc k) (steps pr)) \<subseteq> set (steps (sim_step pr k acc))"
proof -
  let ?step = "steps pr ! k"
  have step_not_assm: "?step \<notin> assumptions pr"
    using assm_pr by simp
  have step_der: "derived (rules F) (take k (steps pr)) ?step"
    using valid_pr k_lt step_not_assm unfolding valid_proof_def by auto
  then obtain r s where r_in: "r \<in> rules F" and dwith: "derived_with k pr r s"
    using k_lt unfolding derived_def derived_with_def by auto
  have choose_props:
    "fst (choose_rule_sub F k pr) \<in> rules F \<and>
     derived_with k pr (fst (choose_rule_sub F k pr)) (snd (choose_rule_sub F k pr)) \<and>
     rule_restricted_sub (fst (choose_rule_sub F k pr)) (snd (choose_rule_sub F k pr))"
    using choose_rule_sub_props[of F k pr] r_in dwith by blast
  let ?r = "fst (choose_rule_sub F k pr)"
  let ?s = "snd (choose_rule_sub F k pr)"
  have step_props:
    "valid_proof F' (step_proof ?r ?s) \<and>
     assumptions (step_proof ?r ?s) = set (prems (sub_rule ?s ?r)) \<and>
     thesis (step_proof ?r ?s) = concl (sub_rule ?s ?r)"
    using step_proof_proves choose_props by blast
  have dchoose: "derived_with k pr ?r ?s"
    using choose_props by simp
  have prems_seen: "set (prems (sub_rule ?s ?r)) \<subseteq> set (steps acc)"
  proof
    fix f
    assume "f \<in> set (prems (sub_rule ?s ?r))"
    then obtain g where "g \<in> set (take k (steps pr))" and "f = g"
      using dchoose unfolding derived_with_def by auto
    thus "f \<in> set (steps acc)"
      using acc_steps by blast
  qed
  have eq: "sim_step pr k acc = combine_proofs acc (step_proof ?r ?s)"
  proof (cases "choose_rule_sub F k pr")
    case (Pair r s)
    then show ?thesis
      using step_not_assm k_lt by (simp add: sim_step_def Let_def)
  qed
  have valid_next: "valid_proof F' (sim_step pr k acc)"
  proof (cases "k = 0")
    case True
    have step_valid: "valid_proof F' (step_proof ?r ?s)"
      using step_props by blast
    have acc_steps0: "steps acc = []"
      using True acc0 by simp
    have comb_eq: "combine_proofs acc (step_proof ?r ?s) = step_proof ?r ?s"
      using acc_assm acc_steps0 step_props by (cases acc) simp
    have "sim_step pr k acc = combine_proofs acc (step_proof ?r ?s)"
      using eq .
    also have "\<dots> = step_proof ?r ?s"
      using comb_eq .
    finally have "sim_step pr k acc = step_proof ?r ?s" .
    then show ?thesis
      using step_valid by simp
  next
    case False
    then have acc_valid': "valid_proof F' acc"
      using acc_valid by blast
    have fsys: "frege_system F'"
      using dm2 unfolding de_morgan_frege_def by simp
    show ?thesis
      using eq acc_valid' step_props prems_seen fsys frege_system.combining_valid_proofs
      by blast
  qed
  have assm_next: "assumptions (sim_step pr k acc) = {}"
    using eq acc_assm step_props prems_seen by simp
  have steps_next: "set (take (Suc k) (steps pr)) \<subseteq> set (steps (sim_step pr k acc))"
  proof
    fix f
    assume "f \<in> set (take (Suc k) (steps pr))"
    then obtain i where i_lt_take: "i < length (take (Suc k) (steps pr))"
      and fi_take: "take (Suc k) (steps pr) ! i = f"
      by (auto simp: in_set_conv_nth)
    hence i_lt: "i < Suc k"
      by simp
    have fi: "f = steps pr ! i"
      using fi_take i_lt k_lt by simp
    consider "i < k" | "i = k"
      using i_lt by linarith
    then show "f \<in> set (steps (sim_step pr k acc))"
    proof cases
      case 1
      have i_take: "i < length (take k (steps pr))"
        using 1 k_lt by simp
      have nth_in: "(take k (steps pr)) ! i \<in> set (take k (steps pr))"
        using i_take by (rule nth_mem)
      have "(take k (steps pr)) ! i = steps pr ! i"
        using 1 k_lt by simp
      then have "steps pr ! i \<in> set (take k (steps pr))"
        using nth_in by simp
      hence "f \<in> set (take k (steps pr))"
        using fi by simp
      then show ?thesis
        using eq acc_steps by auto
    next
      case 2
      have "concl (sub_rule ?s ?r) = steps pr ! k"
        using dchoose unfolding derived_with_def by simp
      moreover have "thesis (step_proof ?r ?s) = concl (sub_rule ?s ?r)"
        using step_props by blast
      moreover have "valid_proof F' (step_proof ?r ?s)"
        using step_props by blast
      then have "thesis (step_proof ?r ?s) \<in> set (steps (step_proof ?r ?s))"
        unfolding valid_proof_def by (metis last_in_set)
      ultimately show ?thesis
        using 2 fi eq by auto
    qed
  qed
  have thesis_next: "thesis (sim_step pr k acc) = steps pr ! k"
  proof -
    have "concl (sub_rule ?s ?r) = steps pr ! k"
      using dchoose unfolding derived_with_def by simp
    with eq step_props show ?thesis by simp
  qed
  show ?thesis
    using assm_next valid_next thesis_next steps_next by simp
qed

lemma sim_proves:
  fixes pr :: dproof
  assumes "valid_proof F pr"
  and "assumptions pr = {}"
  and "pr' = sim pr (thesis pr)"
shows "valid_proof F' pr' \<and> thesis pr' = thesis pr \<and> assumptions pr' = {}"
proof -
  let ?init = "\<lparr>assumptions = assumptions pr, thesis = thesis pr, steps = []\<rparr>"
  let ?acc = "\<lambda>k. fold (sim_step pr) [0..<k] ?init"
  let ?n = "length (steps pr)"

  have prefix_inv:
    "\<forall>k\<le>?n.
      assumptions (?acc k) = {} \<and>
      set (take k (steps pr)) \<subseteq> set (steps (?acc k)) \<and>
      (k = 0 \<or> (valid_proof F' (?acc k) \<and> thesis (?acc k) = steps pr ! (k - 1)))"
  proof (intro allI impI)
    fix k
    assume k_le: "k \<le> ?n"
    show "assumptions (?acc k) = {} \<and>
      set (take k (steps pr)) \<subseteq> set (steps (?acc k)) \<and>
      (k = 0 \<or> (valid_proof F' (?acc k) \<and> thesis (?acc k) = steps pr ! (k - 1)))"
      using k_le
    proof (induction k)
      case 0
      then show ?case using assms(2) by simp
    next
      case (Suc k)
      have IH: "assumptions (?acc k) = {} \<and>
        set (take k (steps pr)) \<subseteq> set (steps (?acc k)) \<and>
        (k = 0 \<or> (valid_proof F' (?acc k) \<and> thesis (?acc k) = steps pr ! (k - 1)))"
        using Suc.IH Suc.prems by simp
      have k_lt: "k < ?n" using Suc.prems by simp
      have acc0: "k = 0 \<longrightarrow> steps (?acc k) = []"
        by (cases k) simp_all
      have step_prog:
        "assumptions (sim_step pr k (?acc k)) = {} \<and>
         valid_proof F' (sim_step pr k (?acc k)) \<and>
         thesis (sim_step pr k (?acc k)) = steps pr ! k \<and>
         set (take (Suc k) (steps pr)) \<subseteq> set (steps (sim_step pr k (?acc k)))"
        using sim_step_progress[of pr k "?acc k"] assms k_lt acc0 IH by blast
      show ?case
        using step_prog by simp
    qed
  qed

  have final_assm: "assumptions (?acc ?n) = {}"
    using prefix_inv by simp
  have final_valid: "valid_proof F' (?acc ?n)"
    using prefix_inv assms(1) unfolding valid_proof_def by auto
  have final_thesis: "thesis (?acc ?n) = thesis pr"
  proof -
    have n_pos: "?n \<noteq> 0"
      using assms(1) unfolding valid_proof_def by auto
    have "thesis (?acc ?n) = steps pr ! (?n - 1)"
      using prefix_inv n_pos by auto
    also have "\<dots> = last (steps pr)"
      using assms(1) unfolding valid_proof_def
      by (simp add: last_conv_nth)
    also have "\<dots> = thesis pr"
      using assms(1) unfolding valid_proof_def by simp
    finally show ?thesis .
  qed
  show ?thesis
    using assms(3) final_assm final_valid final_thesis unfolding sim_def by auto
qed

lemma step_proof_bound:
  shows "\<exists> g :: nat poly. \<forall> rule \<in> rules F. \<forall> pr i sub.
            derived_with i pr rule sub \<and> rule_restricted_sub rule sub \<and> valid_proof F pr \<longrightarrow>
            len_proof (step_proof rule sub) \<le> poly g (len_proof pr)"
proof -
  let ?c = "Max ((\<lambda>r. card (var_set_rule r)) ` rules F) + 1"
  let ?S = "(\<lambda>r. ?c * len_proof (rule_proof_fun r)) ` rules F"
  let ?g = "[:0, Max ?S:]"
  have fin_rules: "finite (rules F)"
    using dm1 unfolding de_morgan_frege_def by (simp add: frege_system.finite)
  hence fin_S: "finite ?S"
    by simp
  show ?thesis
  proof (rule exI[of _ ?g], intro ballI allI impI)
    fix rule pr i sub
    assume r_in: "rule \<in> rules F"
    assume assm: "derived_with i pr rule sub \<and> rule_restricted_sub rule sub \<and> valid_proof F pr"
    have rsub: "rule_restricted_sub rule sub"
      using assm by simp
    have valid_pr: "valid_proof F pr"
      using assm by simp
    have len_sub_bound: "len_sub (var_set_rule rule) sub \<le> ?c * len_proof pr"
      using de_morgan_frege.len_sub_bound_by_proof[OF dm1 r_in, of i pr sub ?c] assm by simp
    have restricted_sub: "\<forall>v. v \<notin> var_set_rule rule \<longrightarrow> sub v = Atom v"
      using rsub unfolding rule_restricted_sub_def by simp
    have step_bound:
      "len_proof (step_proof rule sub)
       \<le> len_proof (rule_proof_fun rule) * len_sub (var_set_rule rule) sub"
      unfolding step_proof.simps
      using sub_proof_bound[of "var_set_rule rule" sub "rule_proof_fun rule"]
            var_set_rule_finite[of rule] restricted_sub
      by simp
    have step_bound':
      "len_proof (step_proof rule sub)
       \<le> (?c * len_proof (rule_proof_fun rule)) * len_proof pr"
    proof -
      have coeff_nonneg: "0 \<le> len_proof (rule_proof_fun rule)"
        by simp
      have mult_bound:
        "len_proof (rule_proof_fun rule) * len_sub (var_set_rule rule) sub
         \<le> len_proof (rule_proof_fun rule) * (?c * len_proof pr)"
        using len_sub_bound coeff_nonneg by (rule mult_left_mono)
      have "len_proof (step_proof rule sub) \<le> len_proof (rule_proof_fun rule) * (?c * len_proof pr)"
        using step_bound mult_bound by linarith
      then show ?thesis
        by (simp add: algebra_simps)
    qed
    have coeff_in: "?c * len_proof (rule_proof_fun rule) \<in> ?S"
      using r_in by simp
    have coeff_le: "?c * len_proof (rule_proof_fun rule) \<le> Max ?S"
      using Max_ge[OF fin_S coeff_in] by simp
    have mono: "(?c * len_proof (rule_proof_fun rule)) * len_proof pr \<le> Max ?S * len_proof pr"
      using coeff_le by (simp add: mult_right_mono)
    have "len_proof (step_proof rule sub) \<le> Max ?S * len_proof pr"
      using step_bound' mono by linarith
    then show "len_proof (step_proof rule sub) \<le> poly ?g (len_proof pr)"
      by (simp add: algebra_simps)
  qed
qed

lemma sim_step_bound:
  shows "\<exists> bound. \<forall>pr i acc.
           i \<ge> 0 \<and> i < length (steps pr) \<and> valid_proof F pr \<and> assumptions pr = {}
           \<longrightarrow> len_proof (sim_step pr i acc) \<le> poly bound (len_proof pr) + len_proof acc"
proof -
  obtain g :: "nat poly" where g_prop:
    "\<forall>rule\<in>rules F. \<forall>pr i sub.
      derived_with i pr rule sub \<and> rule_restricted_sub rule sub \<and> valid_proof F pr \<longrightarrow>
      len_proof (step_proof rule sub) \<le> poly g (len_proof pr)"
    using step_proof_bound by blast
  let ?bound = "[:0, 1:] + g"
  show ?thesis
  proof (rule exI[of _ ?bound], intro allI impI)
    fix pr i acc
    assume assm: "i \<ge> 0 \<and> i < length (steps pr) \<and> valid_proof F pr \<and> assumptions pr = {}"
    have i_lt: "i < length (steps pr)"
      using assm by simp
    have pr_valid: "valid_proof F pr"
      using assm by simp
    have pr_assm: "assumptions pr = {}"
      using assm by simp
    let ?step = "steps pr ! i"
    have step_notin: "?step \<notin> assumptions pr"
      using pr_assm by simp
    have step_der: "derived (rules F) (take i (steps pr)) ?step"
      using pr_valid i_lt step_notin unfolding valid_proof_def by auto
    then obtain r s where r_in0: "r \<in> rules F"
      and concl0: "concl (sub_rule s r) = ?step"
      and prems0: "\<forall>f1\<in>set (prems (sub_rule s r)). \<exists>f2\<in>set (take i (steps pr)). f1 = f2"
      unfolding derived_def by auto
    have dwith0: "derived_with i pr r s"
      using i_lt concl0 prems0 unfolding derived_with_def by simp
    have ex_rs: "\<exists>r s. r \<in> rules F \<and> derived_with i pr r s"
      using r_in0 dwith0 by blast
    have choose_props:
      "fst (choose_rule_sub F i pr) \<in> rules F \<and>
       derived_with i pr (fst (choose_rule_sub F i pr)) (snd (choose_rule_sub F i pr)) \<and>
       rule_restricted_sub (fst (choose_rule_sub F i pr)) (snd (choose_rule_sub F i pr))"
      using choose_rule_sub_props[OF ex_rs] .
    let ?rule = "fst (choose_rule_sub F i pr)"
    let ?sub = "snd (choose_rule_sub F i pr)"
    have r_in: "?rule \<in> rules F"
      using choose_props by simp
    have dwith: "derived_with i pr ?rule ?sub"
      using choose_props by simp
    have rsub: "rule_restricted_sub ?rule ?sub"
      using choose_props by simp
    have step_b: "len_proof (step_proof ?rule ?sub) \<le> poly g (len_proof pr)"
      using g_prop r_in dwith rsub pr_valid by blast
    have step_eq: "sim_step pr i acc = combine_proofs acc (step_proof ?rule ?sub)"
    proof (cases "choose_rule_sub F i pr")
      case (Pair r s)
      then show ?thesis
        using step_notin i_lt by (simp add: sim_step_def Let_def)
    qed
    have "len_proof (sim_step pr i acc) = len_proof acc + len_proof (step_proof ?rule ?sub)"
      using step_eq by simp
    also have "\<dots> \<le> len_proof acc + poly g (len_proof pr)"
      using step_b by simp
    also have "\<dots> \<le> len_proof acc + poly ?bound (len_proof pr)"
      by simp
    finally show "len_proof (sim_step pr i acc) \<le> poly ?bound (len_proof pr) + len_proof acc"
      by (simp add: add.assoc add.commute add.left_commute)
  qed
qed

lemma sim_bound:
  assumes "valid_proof F pr \<and> assumptions pr = {}"
  shows "\<exists> bound. len_proof (sim pr (thesis pr)) \<le> poly bound (len_proof pr)"
proof -
  obtain g :: "nat poly" where g_prop:
    "\<forall>pr i acc. i \<ge> 0 \<and> i < length (steps pr) \<and> valid_proof F pr \<and> assumptions pr = {} \<longrightarrow>
      len_proof (sim_step pr i acc) \<le> poly g (len_proof pr) + len_proof acc"
    using sim_step_bound by blast
  let ?acc = "\<lambda>k. fold (sim_step pr) [0..<k]
                    \<lparr>assumptions = assumptions pr, thesis = thesis pr, steps = []\<rparr>"
  have pr_valid: "valid_proof F pr"
    using assms by simp
  have pr_assm: "assumptions pr = {}"
    using assms by simp
  have steps_bound: "length (steps pr) \<le> len_proof pr"
  proof -
    have ones_le_list:
      "sum_list (replicate (length fs) 1) \<le> sum_list (map len_formula fs)"
      for fs :: "dformula list"
    proof (induction fs)
      case Nil
      then show ?case by simp
    next
      case (Cons f fs)
      have "1 + sum_list (replicate (length fs) 1)
              \<le> len_formula f + sum_list (map len_formula fs)"
        using Cons.IH len_formula_positive[of f] by simp
      then show ?case by simp
    qed
    have ones_le:
      "sum_list (replicate (length (steps pr)) 1) \<le> sum_list (map len_formula (steps pr))"
      using ones_le_list[of "steps pr"] .
    have ones_eq_list: "sum_list (replicate (length fs) 1) = length fs" for fs :: "dformula list"
    proof (induction fs)
      case Nil
      then show ?case by simp
    next
      case (Cons f fs)
      then show ?case by simp
    qed
    have ones_eq: "sum_list (replicate (length (steps pr)) 1) = length (steps pr)"
      using ones_eq_list[of "steps pr"] .
    then have "length (steps pr) \<le> sum_list (map len_formula (steps pr))"
      using ones_le by simp
    then show ?thesis by simp
  qed
  have fold_bound:
    "\<forall>k\<le>length (steps pr). len_proof (?acc k) \<le> k * poly g (len_proof pr)"
  proof (intro allI impI)
    fix k
    assume k_le: "k \<le> length (steps pr)"
    show "len_proof (?acc k) \<le> k * poly g (len_proof pr)"
      using k_le
    proof (induction k)
      case 0
      then show ?case by simp
    next
      case (Suc k)
      have k_lt: "k < length (steps pr)"
        using Suc.prems by simp
      have ih: "len_proof (?acc k) \<le> k * poly g (len_proof pr)"
        using Suc.IH Suc.prems by simp
      have step_b:
        "len_proof (sim_step pr k (?acc k)) \<le> poly g (len_proof pr) + len_proof (?acc k)"
        using g_prop k_lt pr_valid pr_assm by simp
      have "?acc (Suc k) = sim_step pr k (?acc k)"
        by simp
      then have "len_proof (?acc (Suc k)) \<le> poly g (len_proof pr) + len_proof (?acc k)"
        using step_b by simp
      also have "\<dots> \<le> poly g (len_proof pr) + k * poly g (len_proof pr)"
        using ih by simp
      also have "\<dots> = Suc k * poly g (len_proof pr)"
        by simp
      finally show ?case .
    qed
  qed
  let ?bound = "[:0, 1:] * g"
  have final_fold:
    "len_proof (sim pr (thesis pr)) \<le> length (steps pr) * poly g (len_proof pr)"
    unfolding sim_def using fold_bound by simp
  also have "\<dots> \<le> len_proof pr * poly g (len_proof pr)"
    using steps_bound by simp
  also have "\<dots> = poly ?bound (len_proof pr)"
    by simp
  finally show ?thesis
    by (rule exI[of _ ?bound])
qed

lemma simulation_de_morgan:
  shows "simulates F F'"
proof -
  obtain g :: "nat poly" where g_prop:
    "\<forall>pr i acc. i \<ge> 0 \<and> i < length (steps pr) \<and> valid_proof F pr \<and> assumptions pr = {} \<longrightarrow>
      len_proof (sim_step pr i acc) \<le> poly g (len_proof pr) + len_proof acc"
    using sim_step_bound by blast
  let ?f = "\<lambda>w \<tau>. sim w (thesis w)"
  let ?g = "\<lambda>\<tau>. \<tau>"
  let ?p = "[:0, 1:]"
  let ?q = "[:0, 1:] * g"
  have sim_case:
    "(thesis w = ?g \<tau> \<and> valid_proof F w \<and> assumptions w = {}) \<longrightarrow>
      valid_proof F' (?f w \<tau>) \<and> thesis (?f w \<tau>) = \<tau> \<and> assumptions (?f w \<tau>) = {} \<and>
      len_formula (?g \<tau>) \<le> poly ?p (len_formula \<tau>) \<and>
      len_proof (?f w \<tau>) \<le> poly ?q (len_proof w)" for w \<tau>
  proof
    assume assm: "thesis w = ?g \<tau> \<and> valid_proof F w \<and> assumptions w = {}"
    have th_eq: "thesis w = \<tau>"
      using assm by simp
    have w_valid: "valid_proof F w"
      using assm by simp
    have w_assm: "assumptions w = {}"
      using assm by simp
    have pr_props:
      "valid_proof F' (?f w \<tau>) \<and> thesis (?f w \<tau>) = thesis w \<and> assumptions (?f w \<tau>) = {}"
      using sim_proves[of w "sim w (thesis w)"] w_valid w_assm by simp
    let ?acc = "\<lambda>k. fold (sim_step w) [0..<k]
      \<lparr>assumptions = assumptions w, thesis = thesis w, steps = []\<rparr>"
    have steps_bound: "length (steps w) \<le> len_proof w"
    proof -
      have ones_le_list:
        "sum_list (replicate (length fs) 1) \<le> sum_list (map len_formula fs)"
        for fs :: "dformula list"
      proof (induction fs)
        case Nil
        then show ?case by simp
      next
        case (Cons f fs)
        have "1 + sum_list (replicate (length fs) 1)
                \<le> len_formula f + sum_list (map len_formula fs)"
          using Cons.IH len_formula_positive[of f] by simp
        then show ?case by simp
      qed
      have ones_le:
        "sum_list (replicate (length (steps w)) 1) \<le> sum_list (map len_formula (steps w))"
        using ones_le_list[of "steps w"] .
      have ones_eq_list: "sum_list (replicate (length fs) 1) = length fs" for fs :: "dformula list"
      proof (induction fs)
        case Nil
        then show ?case by simp
      next
        case (Cons f fs)
        then show ?case by simp
      qed
      have ones_eq: "sum_list (replicate (length (steps w)) 1) = length (steps w)"
        using ones_eq_list[of "steps w"] .
      then have "length (steps w) \<le> sum_list (map len_formula (steps w))"
        using ones_le by simp
      then show ?thesis by simp
    qed
    have fold_bound:
      "\<forall>k\<le>length (steps w). len_proof (?acc k) \<le> k * poly g (len_proof w)"
    proof (intro allI impI)
      fix k
      assume k_le: "k \<le> length (steps w)"
      show "len_proof (?acc k) \<le> k * poly g (len_proof w)"
        using k_le
      proof (induction k)
        case 0
        then show ?case by simp
      next
        case (Suc k)
        have k_lt: "k < length (steps w)"
          using Suc.prems by simp
        have ih: "len_proof (?acc k) \<le> k * poly g (len_proof w)"
          using Suc.IH Suc.prems by simp
        have step_b:
          "len_proof (sim_step w k (?acc k)) \<le> poly g (len_proof w) + len_proof (?acc k)"
          using g_prop k_lt w_valid w_assm by simp
        have "?acc (Suc k) = sim_step w k (?acc k)"
          by simp
        then have "len_proof (?acc (Suc k)) \<le> poly g (len_proof w) + len_proof (?acc k)"
          using step_b by simp
        also have "\<dots> \<le> poly g (len_proof w) + k * poly g (len_proof w)"
          using ih by simp
        also have "\<dots> = Suc k * poly g (len_proof w)"
          by simp
        finally show ?case .
      qed
    qed
    have global_bound:
      "len_proof (?f w \<tau>) \<le> poly ?q (len_proof w)"
    proof -
      have "len_proof (sim w (thesis w)) \<le> length (steps w) * poly g (len_proof w)"
        unfolding sim_def using fold_bound by simp
      also have "\<dots> \<le> len_proof w * poly g (len_proof w)"
        using steps_bound by simp
      also have "\<dots> = poly ?q (len_proof w)"
        by simp
      finally show ?thesis by simp
    qed
    show "valid_proof F' (?f w \<tau>) \<and> thesis (?f w \<tau>) = \<tau> \<and> assumptions (?f w \<tau>) = {} \<and>
      len_formula (?g \<tau>) \<le> poly ?p (len_formula \<tau>) \<and>
      len_proof (?f w \<tau>) \<le> poly ?q (len_proof w)"
    proof -
      have valid_f: "valid_proof F' (?f w \<tau>)"
        using pr_props by simp
      have thesis_f: "thesis (?f w \<tau>) = \<tau>"
        using pr_props th_eq by simp
      have assm_f: "assumptions (?f w \<tau>) = {}"
        using pr_props by simp
      have len_g: "len_formula (?g \<tau>) \<le> poly ?p (len_formula \<tau>)"
        by simp
      show ?thesis
      proof (intro conjI)
        show "valid_proof F' (?f w \<tau>)"
          using valid_f .
        show "thesis (?f w \<tau>) = \<tau>"
          using thesis_f .
        show "assumptions (?f w \<tau>) = {}"
          using assm_f .
        show "len_formula (?g \<tau>) \<le> poly ?p (len_formula \<tau>)"
          using len_g .
        show "len_proof (?f w \<tau>) \<le> poly ?q (len_proof w)"
          using global_bound .
      qed
    qed
  qed
  show ?thesis
    unfolding simulates_def
  proof (rule exI[of _ ?f], rule exI[of _ ?g], rule exI[of _ ?p], rule exI[of _ ?q], intro allI)
    fix w \<tau>
    show "thesis w = ?g \<tau> \<and> valid_proof F w \<and> assumptions w = {} \<longrightarrow>
      valid_proof F' (?f w \<tau>) \<and> thesis (?f w \<tau>) = \<tau> \<and> assumptions (?f w \<tau>) = {} \<and>
      len_formula (?g \<tau>) \<le> poly ?p (len_formula \<tau>) \<and>
      len_proof (?f w \<tau>) \<le> poly ?q (len_proof w)"
      using sim_case[of w \<tau>] .
  qed
qed
end
end
