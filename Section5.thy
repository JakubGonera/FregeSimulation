theory Section5
  imports Translation
begin

text \<open>
  Lemma 5.1 of the Reckhow development, factored out of theory Translation.

  This theory contains the rebalancing construction and its polynomial
  simulation proof: the iff abstraction layer (iff_form, provable_balanced_iff),
  the proof combinators (iff_trans, iff_sym, iff_refl, balance_cong,
  provable_balanced_iff_subst/_weaken), the rebalancing function, the three
  case constructions, the L(n,m) recurrence machinery (rebal_L and friends),
  and the main results rebalancing_provable (Lemma 5.1) and proof_balancing.

  It depends only on the public interface of theory Translation: the
  frege_balancing locale together with everything established there up to and
  including Lemma 4.3 (in particular custom_balancing, conn_iff, the semantic
  translation spira_trans, and func_complete of the frege_system).
\<close>

context frege_balancing
begin

section \<open>Lemma 5.1: the rebalancing construction and polynomial simulation\<close>

subsection \<open>The iff abstraction and the PBI predicate\<close>

(*
  The iff layer. iff_form A B is the ambient-alphabet formula that asserts
  "A and B are equivalent": conn_iff (the witness for the De Morgan iff)
  with its two variables ''a'', ''b'' substituted by A and B. Since conn_iff
  is only a semantic witness (B1), every fact about iff_form is established
  through its eval lemma, never through its unknown syntactic shape.
*)

definition iff_sub :: "'c formula \<Rightarrow> 'c formula \<Rightarrow> string \<Rightarrow> 'c formula" where
  "iff_sub A B = (\<lambda>v. if v = ''a'' then A else if v = ''b'' then B else Atom v)"

definition iff_form :: "'c formula \<Rightarrow> 'c formula \<Rightarrow> 'c formula" where
  "iff_form A B = sub_formula (iff_sub A B) conn_iff"

lemma iff_form_eval:
  "eval (alphabet F) val (iff_form A B)
   = (eval (alphabet F) val A = eval (alphabet F) val B)"
proof -
  let ?al = "alphabet F"
  have conn_iff_equiv: "formulas_equiv conn_iff ?al iff_dm dm_alphabet"
    unfolding conn_iff_def using someI_ex[OF conn_iff_spec] .
  have iff_dm_eval: "\<And>w. eval dm_alphabet w iff_dm = (w ''a'' = w ''b'')"
    unfolding iff_dm_def dm_alphabet_def by auto
  have "eval ?al val (iff_form A B)
      = eval ?al (\<lambda>w. eval ?al val (iff_sub A B w)) conn_iff"
    unfolding iff_form_def by (rule eval_sub_formula)
  also have "\<dots> = eval dm_alphabet (\<lambda>w. eval ?al val (iff_sub A B w)) iff_dm"
    using conn_iff_equiv unfolding formulas_equiv_def by simp
  also have "\<dots> = (eval ?al val (iff_sub A B ''a'') = eval ?al val (iff_sub A B ''b''))"
    using iff_dm_eval by simp
  also have "\<dots> = (eval ?al val A = eval ?al val B)"
    unfolding iff_sub_def by simp
  finally show ?thesis .
qed

(*
  Lifting: substituting into iff_form A B is the same as building iff_form on
  the substituted sides --- provided sub leaves conn_iff's own variables other
  than ''a'', ''b'' untouched. This is how a fixed proof over fresh atoms is
  instantiated to the actual formulas (Filmus' lemma 3.1).
*)
lemma sub_formula_iff_form:
  assumes "\<And>w. w \<in> var_set_form conn_iff \<Longrightarrow> w \<noteq> ''a'' \<Longrightarrow> w \<noteq> ''b''
                 \<Longrightarrow> sub w = Atom w"
  shows "sub_formula sub (iff_form A B)
       = iff_form (sub_formula sub A) (sub_formula sub B)"
proof -
  have "sub_formula sub (iff_form A B)
      = sub_formula (\<lambda>w. sub_formula sub (iff_sub A B w)) conn_iff"
    unfolding iff_form_def by (rule sub_formula_comp)
  also have "\<dots> = sub_formula (iff_sub (sub_formula sub A) (sub_formula sub B)) conn_iff"
  proof (rule sub_formula_agree, intro ballI)
    fix w assume w_in: "w \<in> var_set_form conn_iff"
    show "sub_formula sub (iff_sub A B w)
        = iff_sub (sub_formula sub A) (sub_formula sub B) w"
    proof (cases "w = ''a''")
      case True
      thus ?thesis unfolding iff_sub_def by simp
    next
      case neq_a: False
      show ?thesis
      proof (cases "w = ''b''")
        case True
        thus ?thesis using neq_a unfolding iff_sub_def by simp
      next
        case neq_b: False
        have "sub w = Atom w" using assms[OF w_in neq_a neq_b] .
        thus ?thesis using neq_a neq_b unfolding iff_sub_def by simp
      qed
    qed
  qed
  also have "\<dots> = iff_form (sub_formula sub A) (sub_formula sub B)"
    unfolding iff_form_def by (rule refl)
  finally show ?thesis .
qed

(*
  taut_proof taut: a fixed, no-assumption Frege proof of any tautology,
  obtained from impl_complete. For the finitely many fixed identities used
  below (reflexivity, transitivity, balance congruence, the case identities)
  this gives proofs of constant size, scaled later by proof_substitution.
*)
definition taut_proof :: "'c formula \<Rightarrow> 'c frege_proof" where
  "taut_proof taut =
     (SOME pr. valid_proof F pr \<and> assumptions pr = {} \<and> thesis pr = taut)"

lemma taut_proof_spec:
  assumes "\<forall>val. eval (alphabet F) val taut"
  shows "valid_proof F (taut_proof taut)
       \<and> assumptions (taut_proof taut) = {}
       \<and> thesis (taut_proof taut) = taut"
proof -
  have fs_F: "frege_system F"
    by (meson frege_balancing_axioms frege_balancing_def)
  have "\<forall>val. (\<forall>f \<in> {}. eval (alphabet F) val f) \<longrightarrow> eval (alphabet F) val taut"
    using assms by simp
  hence "\<exists>pr. valid_proof F pr \<and> assumptions pr = {} \<and> thesis pr = taut"
    using frege_system.impl_complete[OF fs_F] by blast
  thus ?thesis unfolding taut_proof_def by (rule someI_ex)
qed

(*
  provable_balanced_iff A B lines sz dep: there is a no-assumption Frege proof
  of A \<leftrightarrow> B with at most "lines" steps, every step of length at most "sz" and
  depth at most "dep". Bundling the three bounds together is what lets the
  per-line depth/size invariant compose across proof combinations (E2).
*)
definition provable_balanced_iff ::
  "'c formula \<Rightarrow> 'c formula \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "provable_balanced_iff A B lines sz dep \<longleftrightarrow>
     (\<exists>pr. valid_proof F pr \<and> assumptions pr = {}
           \<and> thesis pr = iff_form A B
           \<and> length (steps pr) \<le> lines
           \<and> (\<forall>s \<in> set (steps pr). len_formula s \<le> sz)
           \<and> (\<forall>s \<in> set (steps pr). depth_formula s \<le> dep))"

lemma provable_balanced_iff_weaken:
  assumes "provable_balanced_iff A B lines sz dep"
      and "lines \<le> lines'" and "sz \<le> sz'" and "dep \<le> dep'"
    shows "provable_balanced_iff A B lines' sz' dep'"
  using assms unfolding provable_balanced_iff_def
  by (meson order.trans)

(*
  Fresh atoms. avoid_atoms collects every variable the fixed gluing formulas
  (conn_iff, custom_balancing) and the literal atoms ''a''..''z'' use; the
  fresh_atoms pool steers clear of all of them, so a fixed identity over fresh
  variables can be substituted into actual formulas without capture (B6).
*)
definition avoid_atoms :: "string set" where
  "avoid_atoms = {''a'', ''b'', ''x'', ''y'', ''z''}
                 \<union> var_set_form conn_iff \<union> var_set_form custom_balancing"

lemma avoid_atoms_finite: "finite avoid_atoms"
  unfolding avoid_atoms_def by (simp add: var_set_form_finite)

\<comment> \<open>A substitution that is the identity outside an avoid-disjoint atom set fixes
    every variable of conn_iff (resp. custom_balancing) other than a,b (resp.
    x,y,z) --- the recurring substitution-hygiene obligation discharged at every
    fixed-proof lift site.\<close>
lemma fresh_sub_conn:
  assumes disj: "set atoms \<inter> avoid_atoms = {}"
      and sid: "\<forall>v. v \<notin> set atoms \<longrightarrow> sub v = Atom v"
      and "w \<in> var_set_form conn_iff" and "w \<noteq> ''a''" and "w \<noteq> ''b''"
    shows "sub w = Atom w"
proof -
  have "w \<in> avoid_atoms" using assms(3) unfolding avoid_atoms_def by blast
  hence "w \<notin> set atoms" using disj by blast
  thus ?thesis using sid by blast
qed

lemma fresh_sub_cb:
  assumes disj: "set atoms \<inter> avoid_atoms = {}"
      and sid: "\<forall>v. v \<notin> set atoms \<longrightarrow> sub v = Atom v"
      and "v \<in> var_set_form custom_balancing"
          "v \<noteq> ''x''" "v \<noteq> ''y''" "v \<noteq> ''z''"
    shows "sub v = Atom v"
proof -
  have "v \<in> avoid_atoms" using assms(3) unfolding avoid_atoms_def by blast
  hence "v \<notin> set atoms" using disj by blast
  thus ?thesis using sid by blast
qed

definition fresh_atoms :: "nat \<Rightarrow> string list" where
  "fresh_atoms n =
     (SOME vs. length vs = n \<and> distinct vs \<and> set vs \<inter> avoid_atoms = {})"

lemma fresh_atoms_spec:
  "length (fresh_atoms n) = n \<and> distinct (fresh_atoms n)
   \<and> set (fresh_atoms n) \<inter> avoid_atoms = {}"
proof -
  have "\<exists>vs. length vs = n \<and> distinct vs \<and> set vs \<inter> avoid_atoms = {}"
    using fresh_distinct_atoms_exist_general[OF avoid_atoms_finite] .
  thus ?thesis unfolding fresh_atoms_def by (rule someI_ex)
qed

(* iff_refl: a balanced proof of A \<leftrightarrow> A, from the fixed identity z \<leftrightarrow> z. *)
subsection \<open>Reflexivity and lifting tautologies to Frege proofs (Filmus 3.1)\<close>

definition refl_atom :: string where
  "refl_atom = fresh_atoms 1 ! 0"

lemma refl_atom_fresh: "refl_atom \<notin> avoid_atoms"
proof -
  have len1: "length (fresh_atoms 1) = 1" using fresh_atoms_spec[of 1] by simp
  have "fresh_atoms 1 ! 0 \<in> set (fresh_atoms 1)"
    using nth_mem[of 0 "fresh_atoms 1"] len1 by simp
  moreover have "set (fresh_atoms 1) \<inter> avoid_atoms = {}"
    using fresh_atoms_spec[of 1] by simp
  ultimately show ?thesis unfolding refl_atom_def by blast
qed

lemma refl_atom_not_conn_iff: "refl_atom \<notin> var_set_form conn_iff"
  using refl_atom_fresh unfolding avoid_atoms_def by blast

definition refl_base_proof :: "'c frege_proof" where
  "refl_base_proof = taut_proof (iff_form (Atom refl_atom) (Atom refl_atom))"

definition refl_lines :: nat where
  "refl_lines = length (steps refl_base_proof)"

definition refl_step_len :: nat where
  "refl_step_len = Max (insert 1 (len_formula ` set (steps refl_base_proof)))"

definition refl_step_depth :: nat where
  "refl_step_depth = Max (insert 1 (depth_formula ` set (steps refl_base_proof)))"

(*
  Substitution lifting for provable_balanced_iff (Filmus' lemma 3.1): a
  balanced proof of A \<leftrightarrow> B becomes one of (sub A) \<leftrightarrow> (sub B), the line count
  preserved, per-line size scaled by len_sub, per-line depth raised by
  depth_sub. sub must be the identity off var_set and on conn_iff's own
  variables (other than ''a'', ''b'').
*)
lemma provable_balanced_iff_subst:
  assumes "provable_balanced_iff A B lines sz dep"
      and "finite var_set"
      and "\<forall>v. v \<notin> var_set \<longrightarrow> sub v = Atom v"
      and "\<And>w. w \<in> var_set_form conn_iff \<Longrightarrow> w \<noteq> ''a'' \<Longrightarrow> w \<noteq> ''b''
                 \<Longrightarrow> sub w = Atom w"
    shows "provable_balanced_iff (sub_formula sub A) (sub_formula sub B)
             lines (sz * len_sub var_set sub) (dep + depth_sub var_set sub)"
proof -
  have fs_F: "frege_system F"
    by (meson frege_balancing_axioms frege_balancing_def)
  from assms(1) obtain pr where pr:
    "valid_proof F pr" "assumptions pr = {}" "frege_proof.thesis pr = iff_form A B"
    "length (steps pr) \<le> lines"
    "\<forall>s \<in> set (steps pr). len_formula s \<le> sz"
    "\<forall>s \<in> set (steps pr). depth_formula s \<le> dep"
    unfolding provable_balanced_iff_def by blast
  let ?pr' = "sub_proof sub pr"
  have valid': "valid_proof F ?pr'"
    using frege_system.proof_substitution[OF fs_F] pr(1) by blast
  have asm': "assumptions ?pr' = {}" using pr(2) by simp
  have thesis': "frege_proof.thesis ?pr'
               = iff_form (sub_formula sub A) (sub_formula sub B)"
  proof -
    have "frege_proof.thesis ?pr' = sub_formula sub (iff_form A B)"
      using pr(3) by simp
    also have "\<dots> = iff_form (sub_formula sub A) (sub_formula sub B)"
      by (rule sub_formula_iff_form[OF assms(4)])
    finally show ?thesis .
  qed
  have len': "length (steps ?pr') \<le> lines" using pr(4) by simp
  have step_len': "\<forall>s' \<in> set (steps ?pr').
                     len_formula s' \<le> sz * len_sub var_set sub"
  proof
    fix s' assume "s' \<in> set (steps ?pr')"
    then obtain s where s_in: "s \<in> set (steps pr)"
                    and s'_eq: "s' = sub_formula sub s" by auto
    have "len_formula s' \<le> len_formula s * len_sub var_set sub"
      using s'_eq sub_formula_bound[OF assms(2,3)] by simp
    moreover have "len_formula s \<le> sz" using pr(5) s_in by blast
    ultimately show "len_formula s' \<le> sz * len_sub var_set sub"
      using mult_le_mono1 le_trans by blast
  qed
  have step_dep': "\<forall>s' \<in> set (steps ?pr').
                     depth_formula s' \<le> dep + depth_sub var_set sub"
  proof
    fix s' assume "s' \<in> set (steps ?pr')"
    then obtain s where s_in: "s \<in> set (steps pr)"
                    and s'_eq: "s' = sub_formula sub s" by auto
    have "depth_formula s' \<le> depth_formula s + depth_sub var_set sub"
      using s'_eq sub_formula_depth_bound[OF assms(2,3)] by simp
    moreover have "depth_formula s \<le> dep" using pr(6) s_in by blast
    ultimately show "depth_formula s' \<le> dep + depth_sub var_set sub"
      using add_le_mono1 le_trans by blast
  qed
  show ?thesis
    unfolding provable_balanced_iff_def
    using valid' asm' thesis' len' step_len' step_dep' by blast
qed

(*
  iff_from_taut: when iff_form A B is a tautology, its taut_proof is a balanced
  proof of A \<leftrightarrow> B. The bounds are read off that fixed proof, so for fixed A, B
  (the case identities) they are constants.
*)
lemma iff_from_taut:
  assumes "\<forall>val. eval (alphabet F) val (iff_form A B)"
  shows "provable_balanced_iff A B
           (length (steps (taut_proof (iff_form A B))))
           (Max (insert 1 (len_formula ` set (steps (taut_proof (iff_form A B))))))
           (Max (insert 1 (depth_formula ` set (steps (taut_proof (iff_form A B))))))"
proof -
  let ?pr = "taut_proof (iff_form A B)"
  have spec: "valid_proof F ?pr \<and> assumptions ?pr = {}
            \<and> thesis ?pr = iff_form A B"
    using taut_proof_spec[OF assms] .
  have fin_l: "finite (insert 1 (len_formula ` set (steps ?pr)))" by simp
  have fin_d: "finite (insert 1 (depth_formula ` set (steps ?pr)))" by simp
  have step_len: "\<forall>s \<in> set (steps ?pr).
                    len_formula s \<le> Max (insert 1 (len_formula ` set (steps ?pr)))"
  proof
    fix s assume "s \<in> set (steps ?pr)"
    hence "len_formula s \<in> insert 1 (len_formula ` set (steps ?pr))" by simp
    thus "len_formula s \<le> Max (insert 1 (len_formula ` set (steps ?pr)))"
      using Max_ge[OF fin_l] by blast
  qed
  have step_dep: "\<forall>s \<in> set (steps ?pr).
                    depth_formula s \<le> Max (insert 1 (depth_formula ` set (steps ?pr)))"
  proof
    fix s assume "s \<in> set (steps ?pr)"
    hence "depth_formula s \<in> insert 1 (depth_formula ` set (steps ?pr))" by simp
    thus "depth_formula s \<le> Max (insert 1 (depth_formula ` set (steps ?pr)))"
      using Max_ge[OF fin_d] by blast
  qed
  show ?thesis
    unfolding provable_balanced_iff_def
    using spec step_len step_dep by blast
qed

lemma iff_refl:
  "provable_balanced_iff A A
      refl_lines (refl_step_len * len_formula A) (refl_step_depth + depth_formula A)"
proof -
  let ?z = "refl_atom"
  let ?sub = "\<lambda>w. if w = ?z then A else Atom w"
  have taut: "\<forall>val. eval (alphabet F) val (iff_form (Atom ?z) (Atom ?z))"
    by (simp add: iff_form_eval)
  have base: "provable_balanced_iff (Atom ?z) (Atom ?z)
                refl_lines refl_step_len refl_step_depth"
    using iff_from_taut[OF taut]
    unfolding refl_lines_def refl_step_len_def refl_step_depth_def refl_base_proof_def
    by simp
  have fin: "finite {?z}" by simp
  have sub_id: "\<forall>v. v \<notin> {?z} \<longrightarrow> ?sub v = Atom v" by simp
  have sub_ci: "\<And>w. w \<in> var_set_form conn_iff \<Longrightarrow> w \<noteq> ''a'' \<Longrightarrow> w \<noteq> ''b''
                 \<Longrightarrow> ?sub w = Atom w"
    using refl_atom_not_conn_iff by auto
  have len_sub_eq: "len_sub {?z} ?sub = len_formula A"
    using len_formula_positive[of A] by (simp add: len_sub_def)
  have depth_sub_eq: "depth_sub {?z} ?sub = depth_formula A"
    using depth_formula_ge_1[of A] by (simp add: depth_sub_def)
  show ?thesis
    using provable_balanced_iff_subst[OF base fin sub_id sub_ci]
    by (simp add: len_sub_eq depth_sub_eq)
qed

(*
  entails_proof fs th: a fixed Frege proof of th from assumptions fs, whenever
  fs semantically entails th. The assumption-bearing generalisation of
  taut_proof, used to build the fixed transitivity / congruence proofs.
*)
subsection \<open>Transitivity of balanced equivalence\<close>

definition entails_proof :: "'c formula set \<Rightarrow> 'c formula \<Rightarrow> 'c frege_proof" where
  "entails_proof fs th =
     (SOME pr. valid_proof F pr \<and> assumptions pr = fs \<and> thesis pr = th)"

lemma entails_proof_spec:
  assumes "\<forall>val. (\<forall>f \<in> fs. eval (alphabet F) val f) \<longrightarrow> eval (alphabet F) val th"
  shows "valid_proof F (entails_proof fs th)
       \<and> assumptions (entails_proof fs th) = fs
       \<and> thesis (entails_proof fs th) = th"
proof -
  have fs_F: "frege_system F"
    by (meson frege_balancing_axioms frege_balancing_def)
  have "\<exists>pr. valid_proof F pr \<and> assumptions pr = fs \<and> thesis pr = th"
    using frege_system.impl_complete[OF fs_F] assms by blast
  thus ?thesis unfolding entails_proof_def by (rule someI_ex)
qed

(* iff_trans: transitivity, from the fixed identity (x \<leftrightarrow> y), (y \<leftrightarrow> z) \<turnstile> (x \<leftrightarrow> z). *)
definition trans_atom_x :: string where "trans_atom_x = fresh_atoms 3 ! 0"
definition trans_atom_y :: string where "trans_atom_y = fresh_atoms 3 ! 1"
definition trans_atom_z :: string where "trans_atom_z = fresh_atoms 3 ! 2"

lemma trans_atoms_spec:
  "trans_atom_x \<notin> avoid_atoms \<and> trans_atom_y \<notin> avoid_atoms
   \<and> trans_atom_z \<notin> avoid_atoms
   \<and> trans_atom_x \<noteq> trans_atom_y \<and> trans_atom_x \<noteq> trans_atom_z
   \<and> trans_atom_y \<noteq> trans_atom_z"
proof -
  have len3: "length (fresh_atoms 3) = 3" using fresh_atoms_spec[of 3] by simp
  have dist: "distinct (fresh_atoms 3)" using fresh_atoms_spec[of 3] by simp
  have disj: "set (fresh_atoms 3) \<inter> avoid_atoms = {}"
    using fresh_atoms_spec[of 3] by simp
  have m0: "fresh_atoms 3 ! 0 \<in> set (fresh_atoms 3)"
    using nth_mem[of 0 "fresh_atoms 3"] len3 by simp
  have m1: "fresh_atoms 3 ! 1 \<in> set (fresh_atoms 3)"
    using nth_mem[of 1 "fresh_atoms 3"] len3 by simp
  have m2: "fresh_atoms 3 ! 2 \<in> set (fresh_atoms 3)"
    using nth_mem[of 2 "fresh_atoms 3"] len3 by simp
  have "trans_atom_x \<notin> avoid_atoms" unfolding trans_atom_x_def using m0 disj by blast
  moreover have "trans_atom_y \<notin> avoid_atoms"
    unfolding trans_atom_y_def using m1 disj by blast
  moreover have "trans_atom_z \<notin> avoid_atoms"
    unfolding trans_atom_z_def using m2 disj by blast
  moreover have "trans_atom_x \<noteq> trans_atom_y"
    unfolding trans_atom_x_def trans_atom_y_def
    using nth_eq_iff_index_eq[OF dist, of 0 1] len3 by simp
  moreover have "trans_atom_x \<noteq> trans_atom_z"
    unfolding trans_atom_x_def trans_atom_z_def
    using nth_eq_iff_index_eq[OF dist, of 0 2] len3 by simp
  moreover have "trans_atom_y \<noteq> trans_atom_z"
    unfolding trans_atom_y_def trans_atom_z_def
    using nth_eq_iff_index_eq[OF dist, of 1 2] len3 by simp
  ultimately show ?thesis by blast
qed

definition trans_base_proof :: "'c frege_proof" where
  "trans_base_proof =
     entails_proof
       {iff_form (Atom trans_atom_x) (Atom trans_atom_y),
        iff_form (Atom trans_atom_y) (Atom trans_atom_z)}
       (iff_form (Atom trans_atom_x) (Atom trans_atom_z))"

lemma trans_base_proof_spec:
  "valid_proof F trans_base_proof
   \<and> assumptions trans_base_proof =
       {iff_form (Atom trans_atom_x) (Atom trans_atom_y),
        iff_form (Atom trans_atom_y) (Atom trans_atom_z)}
   \<and> thesis trans_base_proof = iff_form (Atom trans_atom_x) (Atom trans_atom_z)"
proof -
  have "\<forall>val. (\<forall>f \<in> {iff_form (Atom trans_atom_x) (Atom trans_atom_y),
                     iff_form (Atom trans_atom_y) (Atom trans_atom_z)}.
                eval (alphabet F) val f)
              \<longrightarrow> eval (alphabet F) val
                    (iff_form (Atom trans_atom_x) (Atom trans_atom_z))"
    using iff_form_eval by auto
  thus ?thesis
    unfolding trans_base_proof_def using entails_proof_spec by blast
qed

definition trans_lines :: nat where
  "trans_lines = length (steps trans_base_proof)"

definition trans_step_len :: nat where
  "trans_step_len = Max (insert 1 (len_formula ` set (steps trans_base_proof)))"

definition trans_step_depth :: nat where
  "trans_step_depth = Max (insert 1 (depth_formula ` set (steps trans_base_proof)))"

lemma iff_trans:
  assumes "provable_balanced_iff A B l1 s1 d1"
      and "provable_balanced_iff B C l2 s2 d2"
    shows "provable_balanced_iff A C
             (l1 + l2 + trans_lines)
             (s1 + s2 + trans_step_len
                * (len_formula A + len_formula B + len_formula C))
             (max d1 (max d2 (trans_step_depth
                + max (depth_formula A)
                      (max (depth_formula B) (depth_formula C)))))"
proof -
  have fs_F: "frege_system F"
    by (meson frege_balancing_axioms frege_balancing_def)
  let ?x = "trans_atom_x" and ?y = "trans_atom_y" and ?z = "trans_atom_z"
  let ?sub = "\<lambda>w. if w = ?x then A else if w = ?y then B
                  else if w = ?z then C else Atom w"
  let ?lines_t = "l1 + l2 + trans_lines"
  let ?sz_t = "s1 + s2 + trans_step_len
                 * (len_formula A + len_formula B + len_formula C)"
  let ?dep_t = "max d1 (max d2 (trans_step_depth
                  + max (depth_formula A)
                        (max (depth_formula B) (depth_formula C))))"

  have neq: "?x \<noteq> ?y" "?x \<noteq> ?z" "?y \<noteq> ?z" using trans_atoms_spec by blast+

  from assms(1) obtain pAB where pAB:
    "valid_proof F pAB" "assumptions pAB = {}"
    "frege_proof.thesis pAB = iff_form A B"
    "length (steps pAB) \<le> l1"
    "\<forall>s \<in> set (steps pAB). len_formula s \<le> s1"
    "\<forall>s \<in> set (steps pAB). depth_formula s \<le> d1"
    unfolding provable_balanced_iff_def by blast
  from assms(2) obtain pBC where pBC:
    "valid_proof F pBC" "assumptions pBC = {}"
    "frege_proof.thesis pBC = iff_form B C"
    "length (steps pBC) \<le> l2"
    "\<forall>s \<in> set (steps pBC). len_formula s \<le> s2"
    "\<forall>s \<in> set (steps pBC). depth_formula s \<le> d2"
    unfolding provable_balanced_iff_def by blast

  \<comment> \<open>sub leaves conn_iff's own variables alone.\<close>
  have sub_conn_iff:
    "\<And>w. w \<in> var_set_form conn_iff \<Longrightarrow> w \<noteq> ''a'' \<Longrightarrow> w \<noteq> ''b''
           \<Longrightarrow> ?sub w = Atom w"
  proof -
    fix w assume w_ci: "w \<in> var_set_form conn_iff"
      and "w \<noteq> ''a''" and "w \<noteq> ''b''"
    have "w \<in> avoid_atoms" using w_ci unfolding avoid_atoms_def by blast
    hence "w \<noteq> ?x \<and> w \<noteq> ?y \<and> w \<noteq> ?z" using trans_atoms_spec by blast
    thus "?sub w = Atom w" by simp
  qed
  have sub_id: "\<forall>v. v \<notin> {?x, ?y, ?z} \<longrightarrow> ?sub v = Atom v" by auto
  have fin_xyz: "finite {?x, ?y, ?z}" by simp

  \<comment> \<open>The substituted transitivity proof, kept opaque so its named facts
      stay usable through the combine steps below.\<close>
  define ti where ti_def: "ti = sub_proof ?sub trans_base_proof"
  have valid_ti: "valid_proof F ti"
    unfolding ti_def
    using frege_system.proof_substitution[OF fs_F] trans_base_proof_spec by blast
  have ti_steps: "steps ti = map (sub_formula ?sub) (steps trans_base_proof)"
    unfolding ti_def by simp
  have ti_thesis: "frege_proof.thesis ti = iff_form A C"
  proof -
    have "frege_proof.thesis ti
        = sub_formula ?sub (iff_form (Atom ?x) (Atom ?z))"
      unfolding ti_def using trans_base_proof_spec by simp
    also have "\<dots> = iff_form (sub_formula ?sub (Atom ?x)) (sub_formula ?sub (Atom ?z))"
      by (rule sub_formula_iff_form[OF sub_conn_iff])
    also have "\<dots> = iff_form A C" using neq by simp
    finally show ?thesis .
  qed
  have ti_asm: "assumptions ti = {iff_form A B, iff_form B C}"
  proof -
    have sub_xy: "sub_formula ?sub (iff_form (Atom ?x) (Atom ?y)) = iff_form A B"
    proof -
      have "sub_formula ?sub (iff_form (Atom ?x) (Atom ?y))
          = iff_form (sub_formula ?sub (Atom ?x)) (sub_formula ?sub (Atom ?y))"
        by (rule sub_formula_iff_form[OF sub_conn_iff])
      also have "\<dots> = iff_form A B" using neq by simp
      finally show ?thesis .
    qed
    have sub_yz: "sub_formula ?sub (iff_form (Atom ?y) (Atom ?z)) = iff_form B C"
    proof -
      have "sub_formula ?sub (iff_form (Atom ?y) (Atom ?z))
          = iff_form (sub_formula ?sub (Atom ?y)) (sub_formula ?sub (Atom ?z))"
        by (rule sub_formula_iff_form[OF sub_conn_iff])
      also have "\<dots> = iff_form B C" using neq by simp
      finally show ?thesis .
    qed
    have "assumptions ti = (sub_formula ?sub) ` (assumptions trans_base_proof)"
      unfolding ti_def by simp
    also have "\<dots> = (sub_formula ?sub) `
         {iff_form (Atom ?x) (Atom ?y), iff_form (Atom ?y) (Atom ?z)}"
      using trans_base_proof_spec by simp
    also have "\<dots> = {iff_form A B, iff_form B C}"
      using sub_xy sub_yz by simp
    finally show ?thesis .
  qed
  have ti_lines: "length (steps ti) = trans_lines"
    using ti_steps by (simp add: trans_lines_def)

  \<comment> \<open>Substitution-size facts for the transitivity proof's lines.\<close>
  have len_sub_eq: "len_sub {?x, ?y, ?z} ?sub
                  = len_formula A + len_formula B + len_formula C"
  proof -
    have "(\<Sum>v \<in> {?x, ?y, ?z}. len_formula (?sub v))
        = len_formula A + len_formula B + len_formula C"
      using neq by simp
    moreover have "len_formula A \<ge> 1" by (rule len_formula_positive)
    ultimately show ?thesis unfolding len_sub_def by simp
  qed
  have depth_sub_le: "depth_sub {?x, ?y, ?z} ?sub
                    \<le> max (depth_formula A)
                          (max (depth_formula B) (depth_formula C))"
  proof -
    have img: "(\<lambda>v. depth_formula (?sub v)) ` {?x, ?y, ?z}
             = {depth_formula A, depth_formula B, depth_formula C}"
      using neq by auto
    have "depth_sub {?x, ?y, ?z} ?sub
        = Max (insert 1 {depth_formula A, depth_formula B, depth_formula C})"
      unfolding depth_sub_def using img by simp
    also have "\<dots> \<le> max (depth_formula A)
                        (max (depth_formula B) (depth_formula C))"
    proof (rule Max.boundedI)
      show "finite (insert 1 {depth_formula A, depth_formula B, depth_formula C})"
        by simp
      show "insert 1 {depth_formula A, depth_formula B, depth_formula C} \<noteq> {}"
        by simp
      fix e assume "e \<in> insert 1 {depth_formula A, depth_formula B, depth_formula C}"
      thus "e \<le> max (depth_formula A) (max (depth_formula B) (depth_formula C))"
        using depth_formula_ge_1[of A] depth_formula_ge_1[of B]
              depth_formula_ge_1[of C] by auto
    qed
    finally show ?thesis .
  qed

  have fin_tl: "finite (insert 1 (len_formula ` set (steps trans_base_proof)))"
    by simp
  have fin_td: "finite (insert 1 (depth_formula ` set (steps trans_base_proof)))"
    by simp

  \<comment> \<open>Combine: proof of A \<leftrightarrow> B, proof of B \<leftrightarrow> C, then the transitivity step.\<close>
  define c1 where c1_def: "c1 = combine_proofs pAB pBC"
  have valid_c1: "valid_proof F c1"
    unfolding c1_def
    using frege_system.combining_valid_proofs[OF fs_F] pAB(1) pBC(1) by blast
  have c1_asm: "assumptions c1 = {}"
    unfolding c1_def using pAB(2) pBC(2) by simp
  have c1_steps: "steps c1 = steps pAB @ steps pBC"
    unfolding c1_def by simp

  define cb where cb_def: "cb = combine_proofs c1 ti"
  have valid_cb: "valid_proof F cb"
    unfolding cb_def
    using frege_system.combining_valid_proofs[OF fs_F] valid_c1 valid_ti by blast

  have AB_in: "iff_form A B \<in> set (steps pAB)"
  proof -
    have ne: "steps pAB \<noteq> []" using pAB(1) unfolding valid_proof_def by simp
    have "frege_proof.thesis pAB = last (steps pAB)"
      using pAB(1) unfolding valid_proof_def by simp
    hence "iff_form A B = last (steps pAB)" using pAB(3) by simp
    moreover have "last (steps pAB) \<in> set (steps pAB)" using ne by (rule last_in_set)
    ultimately show ?thesis by simp
  qed
  have BC_in: "iff_form B C \<in> set (steps pBC)"
  proof -
    have ne: "steps pBC \<noteq> []" using pBC(1) unfolding valid_proof_def by simp
    have "frege_proof.thesis pBC = last (steps pBC)"
      using pBC(1) unfolding valid_proof_def by simp
    hence "iff_form B C = last (steps pBC)" using pBC(3) by simp
    moreover have "last (steps pBC) \<in> set (steps pBC)" using ne by (rule last_in_set)
    ultimately show ?thesis by simp
  qed

  have cb_asm: "assumptions cb = {}"
  proof -
    have sub: "{iff_form A B, iff_form B C} \<subseteq> set (steps c1)"
      using AB_in BC_in c1_steps by auto
    have "assumptions cb = assumptions c1 \<union> (assumptions ti - set (steps c1))"
      unfolding cb_def by simp
    also have "\<dots> = {} \<union> ({iff_form A B, iff_form B C} - set (steps c1))"
      using c1_asm ti_asm by simp
    also have "\<dots> = {}" using sub by blast
    finally show ?thesis .
  qed
  have cb_thesis: "frege_proof.thesis cb = iff_form A C"
    unfolding cb_def using ti_thesis by simp
  have cb_steps: "steps cb = steps pAB @ steps pBC @ steps ti"
  proof -
    have "steps cb = steps c1 @ steps ti" unfolding cb_def by simp
    thus ?thesis using c1_steps by simp
  qed

  have cb_lines: "length (steps cb) \<le> ?lines_t"
  proof -
    have "length (steps cb)
        = length (steps pAB) + length (steps pBC) + length (steps ti)"
      using cb_steps by simp
    thus ?thesis using pAB(4) pBC(4) ti_lines by linarith
  qed

  have step_len: "\<forall>s \<in> set (steps cb). len_formula s \<le> ?sz_t"
  proof
    fix s assume "s \<in> set (steps cb)"
    hence "s \<in> set (steps pAB) \<or> s \<in> set (steps pBC) \<or> s \<in> set (steps ti)"
      using cb_steps by auto
    thus "len_formula s \<le> ?sz_t"
    proof (elim disjE)
      assume "s \<in> set (steps pAB)"
      hence "len_formula s \<le> s1" using pAB(5) by blast
      thus ?thesis by linarith
    next
      assume "s \<in> set (steps pBC)"
      hence "len_formula s \<le> s2" using pBC(5) by blast
      thus ?thesis by linarith
    next
      assume "s \<in> set (steps ti)"
      then obtain s0 where s0_in: "s0 \<in> set (steps trans_base_proof)"
                       and s_eq: "s = sub_formula ?sub s0"
        using ti_steps by auto
      have "len_formula s \<le> len_formula s0 * len_sub {?x, ?y, ?z} ?sub"
        using s_eq sub_formula_bound[OF fin_xyz sub_id] by simp
      also have "\<dots> = len_formula s0
                      * (len_formula A + len_formula B + len_formula C)"
        using len_sub_eq by simp
      also have "\<dots> \<le> trans_step_len
                      * (len_formula A + len_formula B + len_formula C)"
      proof -
        have "len_formula s0 \<in> insert 1 (len_formula ` set (steps trans_base_proof))"
          using s0_in by simp
        hence "len_formula s0 \<le> trans_step_len"
          unfolding trans_step_len_def using Max_ge[OF fin_tl] by blast
        thus ?thesis by (rule mult_le_mono1)
      qed
      finally show ?thesis by linarith
    qed
  qed

  have step_depth: "\<forall>s \<in> set (steps cb). depth_formula s \<le> ?dep_t"
  proof
    fix s assume "s \<in> set (steps cb)"
    hence "s \<in> set (steps pAB) \<or> s \<in> set (steps pBC) \<or> s \<in> set (steps ti)"
      using cb_steps by auto
    thus "depth_formula s \<le> ?dep_t"
    proof (elim disjE)
      assume "s \<in> set (steps pAB)"
      hence "depth_formula s \<le> d1" using pAB(6) by blast
      moreover have "d1 \<le> ?dep_t" by simp
      ultimately show ?thesis by linarith
    next
      assume "s \<in> set (steps pBC)"
      hence "depth_formula s \<le> d2" using pBC(6) by blast
      moreover have "d2 \<le> ?dep_t" by simp
      ultimately show ?thesis by linarith
    next
      assume "s \<in> set (steps ti)"
      then obtain s0 where s0_in: "s0 \<in> set (steps trans_base_proof)"
                       and s_eq: "s = sub_formula ?sub s0"
        using ti_steps by auto
      have "depth_formula s \<le> depth_formula s0 + depth_sub {?x, ?y, ?z} ?sub"
        using s_eq sub_formula_depth_bound[OF fin_xyz sub_id] by simp
      also have "\<dots> \<le> depth_formula s0
                      + max (depth_formula A)
                            (max (depth_formula B) (depth_formula C))"
        using depth_sub_le by simp
      also have "\<dots> \<le> trans_step_depth
                      + max (depth_formula A)
                            (max (depth_formula B) (depth_formula C))"
      proof -
        have "depth_formula s0
            \<in> insert 1 (depth_formula ` set (steps trans_base_proof))"
          using s0_in by simp
        hence "depth_formula s0 \<le> trans_step_depth"
          unfolding trans_step_depth_def using Max_ge[OF fin_td] by blast
        thus ?thesis by simp
      qed
      also have "\<dots> \<le> ?dep_t" by simp
      finally show ?thesis .
    qed
  qed

  show ?thesis
    unfolding provable_balanced_iff_def
  proof (intro exI[where x = cb] conjI)
    show "valid_proof F cb" using valid_cb .
    show "assumptions cb = {}" using cb_asm .
    show "frege_proof.thesis cb = iff_form A C" using cb_thesis .
    show "length (steps cb) \<le> ?lines_t" using cb_lines .
    show "\<forall>s \<in> set (steps cb). len_formula s \<le> ?sz_t" using step_len .
    show "\<forall>s \<in> set (steps cb). depth_formula s \<le> ?dep_t" using step_depth .
  qed
qed

(*
  Congruence lifting through balance. Since balance is custom_balancing under
  substitution and custom_balancing is only a func_complete witness (B2), the
  single-hole iff_congruent does not apply; balance congruence is handled
  directly from the semantics. sub_formula_balance is the syntactic half.
*)
subsection \<open>Balance congruence (Filmus 3.2)\<close>

lemma sub_formula_balance:
  assumes "\<And>v. v \<in> var_set_form custom_balancing \<Longrightarrow> v \<noteq> ''x'' \<Longrightarrow> v \<noteq> ''y''
                 \<Longrightarrow> v \<noteq> ''z'' \<Longrightarrow> sub v = Atom v"
  shows "sub_formula sub (balance x y z)
       = balance (sub_formula sub x) (sub_formula sub y) (sub_formula sub z)"
proof -
  let ?bs = "\<lambda>v. if v = ''x'' then x else if v = ''y'' then y
                 else if v = ''z'' then z else Atom v"
  let ?bs' = "\<lambda>v. if v = ''x'' then sub_formula sub x
                  else if v = ''y'' then sub_formula sub y
                  else if v = ''z'' then sub_formula sub z else Atom v"
  have unfold1: "balance x y z = sub_formula ?bs custom_balancing"
    by (simp add: Let_def)
  have unfold2: "balance (sub_formula sub x) (sub_formula sub y) (sub_formula sub z)
               = sub_formula ?bs' custom_balancing"
    by (simp add: Let_def)
  have "sub_formula sub (balance x y z)
      = sub_formula (\<lambda>v. sub_formula sub (?bs v)) custom_balancing"
    using unfold1 by (simp add: sub_formula_comp)
  also have "\<dots> = sub_formula ?bs' custom_balancing"
  proof (rule sub_formula_agree, intro ballI)
    fix v assume v_in: "v \<in> var_set_form custom_balancing"
    show "sub_formula sub (?bs v) = ?bs' v"
    proof (cases "v = ''x''")
      case True thus ?thesis by simp
    next
      case nx: False
      show ?thesis
      proof (cases "v = ''y''")
        case True thus ?thesis using nx by simp
      next
        case ny: False
        show ?thesis
        proof (cases "v = ''z''")
          case True thus ?thesis using nx ny by simp
        next
          case nz: False
          have "sub v = Atom v" using assms[OF v_in nx ny nz] .
          thus ?thesis using nx ny nz by simp
        qed
      qed
    qed
  qed
  also have "\<dots> = balance (sub_formula sub x) (sub_formula sub y) (sub_formula sub z)"
    using unfold2 by simp
  finally show ?thesis .
qed

(* balance_cong: the fixed congruence (x\<leftrightarrow>x'),(y\<leftrightarrow>y'),(z\<leftrightarrow>z')
   \<turnstile> balance x y z \<leftrightarrow> balance x' y' z', over six fresh atoms. *)
definition cong_atoms :: "string list" where
  "cong_atoms = fresh_atoms 6"

lemma cong_atoms_spec:
  "length cong_atoms = 6 \<and> distinct cong_atoms
   \<and> set cong_atoms \<inter> avoid_atoms = {}"
  unfolding cong_atoms_def using fresh_atoms_spec[of 6] by simp

definition balance_cong_base_proof :: "'c frege_proof" where
  "balance_cong_base_proof =
     entails_proof
       {iff_form (Atom (cong_atoms ! 0)) (Atom (cong_atoms ! 1)),
        iff_form (Atom (cong_atoms ! 2)) (Atom (cong_atoms ! 3)),
        iff_form (Atom (cong_atoms ! 4)) (Atom (cong_atoms ! 5))}
       (iff_form
          (balance (Atom (cong_atoms ! 0)) (Atom (cong_atoms ! 2))
                   (Atom (cong_atoms ! 4)))
          (balance (Atom (cong_atoms ! 1)) (Atom (cong_atoms ! 3))
                   (Atom (cong_atoms ! 5))))"

lemma balance_cong_base_proof_spec:
  "valid_proof F balance_cong_base_proof
   \<and> assumptions balance_cong_base_proof =
       {iff_form (Atom (cong_atoms ! 0)) (Atom (cong_atoms ! 1)),
        iff_form (Atom (cong_atoms ! 2)) (Atom (cong_atoms ! 3)),
        iff_form (Atom (cong_atoms ! 4)) (Atom (cong_atoms ! 5))}
   \<and> thesis balance_cong_base_proof =
       iff_form
         (balance (Atom (cong_atoms ! 0)) (Atom (cong_atoms ! 2))
                  (Atom (cong_atoms ! 4)))
         (balance (Atom (cong_atoms ! 1)) (Atom (cong_atoms ! 3))
                  (Atom (cong_atoms ! 5)))"
proof -
  let ?a0 = "cong_atoms ! 0" and ?a1 = "cong_atoms ! 1"
  and ?a2 = "cong_atoms ! 2" and ?a3 = "cong_atoms ! 3"
  and ?a4 = "cong_atoms ! 4" and ?a5 = "cong_atoms ! 5"
  have "\<forall>val. (\<forall>f \<in> {iff_form (Atom ?a0) (Atom ?a1),
                     iff_form (Atom ?a2) (Atom ?a3),
                     iff_form (Atom ?a4) (Atom ?a5)}.
                eval (alphabet F) val f)
              \<longrightarrow> eval (alphabet F) val
                    (iff_form (balance (Atom ?a0) (Atom ?a2) (Atom ?a4))
                              (balance (Atom ?a1) (Atom ?a3) (Atom ?a5)))"
  proof (intro allI impI)
    fix val
    assume "\<forall>f \<in> {iff_form (Atom ?a0) (Atom ?a1),
                  iff_form (Atom ?a2) (Atom ?a3),
                  iff_form (Atom ?a4) (Atom ?a5)}.
              eval (alphabet F) val f"
    hence e0: "eval (alphabet F) val (iff_form (Atom ?a0) (Atom ?a1))"
      and e2: "eval (alphabet F) val (iff_form (Atom ?a2) (Atom ?a3))"
      and e4: "eval (alphabet F) val (iff_form (Atom ?a4) (Atom ?a5))"
      by auto
    have ee0: "eval (alphabet F) val (Atom ?a0) = eval (alphabet F) val (Atom ?a1)"
      using e0 by (simp add: iff_form_eval)
    have ee2: "eval (alphabet F) val (Atom ?a2) = eval (alphabet F) val (Atom ?a3)"
      using e2 by (simp add: iff_form_eval)
    have ee4: "eval (alphabet F) val (Atom ?a4) = eval (alphabet F) val (Atom ?a5)"
      using e4 by (simp add: iff_form_eval)
    have "eval (alphabet F) val (balance (Atom ?a0) (Atom ?a2) (Atom ?a4))
        = (if eval (alphabet F) val (Atom ?a4)
           then eval (alphabet F) val (Atom ?a0)
           else eval (alphabet F) val (Atom ?a2))"
      by (rule balance_eval)
    also have "\<dots> = (if eval (alphabet F) val (Atom ?a5)
                     then eval (alphabet F) val (Atom ?a1)
                     else eval (alphabet F) val (Atom ?a3))"
      using ee0 ee2 ee4 by simp
    also have "\<dots> = eval (alphabet F) val (balance (Atom ?a1) (Atom ?a3) (Atom ?a5))"
      by (rule balance_eval[symmetric])
    finally have baleq: "eval (alphabet F) val (balance (Atom ?a0) (Atom ?a2) (Atom ?a4))
        = eval (alphabet F) val (balance (Atom ?a1) (Atom ?a3) (Atom ?a5))" .
    thus "eval (alphabet F) val
            (iff_form (balance (Atom ?a0) (Atom ?a2) (Atom ?a4))
                      (balance (Atom ?a1) (Atom ?a3) (Atom ?a5)))"
      by (simp add: iff_form_eval)
  qed
  thus ?thesis
    unfolding balance_cong_base_proof_def using entails_proof_spec by blast
qed

definition balance_cong_lines :: nat where
  "balance_cong_lines = length (steps balance_cong_base_proof)"

definition balance_cong_step_len :: nat where
  "balance_cong_step_len =
     Max (insert 1 (len_formula ` set (steps balance_cong_base_proof)))"

definition balance_cong_step_depth :: nat where
  "balance_cong_step_depth =
     Max (insert 1 (depth_formula ` set (steps balance_cong_base_proof)))"

lemma balance_cong:
  assumes "provable_balanced_iff X X' lx sx dx"
      and "provable_balanced_iff Y Y' ly sy dy"
      and "provable_balanced_iff Z Z' lz sz dz"
    shows "provable_balanced_iff (balance X Y Z) (balance X' Y' Z')
             (lx + ly + lz + balance_cong_lines)
             (sx + sy + sz + balance_cong_step_len
                * (6 * (len_formula X + len_formula X' + len_formula Y
                        + len_formula Y' + len_formula Z + len_formula Z')))
             (max dx (max dy (max dz (balance_cong_step_depth
                + max (depth_formula X) (max (depth_formula X')
                    (max (depth_formula Y) (max (depth_formula Y')
                      (max (depth_formula Z) (depth_formula Z')))))))))"
proof -
  have fs_F: "frege_system F"
    by (meson frege_balancing_axioms frege_balancing_def)
  let ?a0 = "cong_atoms ! 0" and ?a1 = "cong_atoms ! 1"
  and ?a2 = "cong_atoms ! 2" and ?a3 = "cong_atoms ! 3"
  and ?a4 = "cong_atoms ! 4" and ?a5 = "cong_atoms ! 5"
  let ?vals = "[X, X', Y, Y', Z, Z']"
  let ?csub = "\<lambda>v. case map_of (zip cong_atoms ?vals) v of
                    None \<Rightarrow> Atom v | Some f \<Rightarrow> f"
  let ?sumlens = "len_formula X + len_formula X' + len_formula Y
                  + len_formula Y' + len_formula Z + len_formula Z'"
  let ?maxdep6 = "max (depth_formula X) (max (depth_formula X')
                    (max (depth_formula Y) (max (depth_formula Y')
                      (max (depth_formula Z) (depth_formula Z')))))"
  let ?lines_t = "lx + ly + lz + balance_cong_lines"
  let ?sz_t = "sx + sy + sz + balance_cong_step_len * (6 * ?sumlens)"
  let ?dep_t = "max dx (max dy (max dz (balance_cong_step_depth + ?maxdep6)))"

  have cong_len: "length cong_atoms = 6" using cong_atoms_spec by simp
  have cong_dist: "distinct cong_atoms" using cong_atoms_spec by simp
  have cong_disj: "set cong_atoms \<inter> avoid_atoms = {}" using cong_atoms_spec by simp
  have lveq: "length cong_atoms = length ?vals" using cong_len by simp
  have fin_ca: "finite (set cong_atoms)" by simp

  \<comment> \<open>The substitution lifting the six fresh atoms to the actual formulas.\<close>
  have csub_nth: "\<And>k::nat. k < 6 \<Longrightarrow> ?csub (cong_atoms ! k) = ?vals ! k"
  proof -
    fix k :: nat assume "k < 6"
    hence "map_of (zip cong_atoms ?vals) (cong_atoms ! k) = Some (?vals ! k)"
      using map_of_zip_nth_lookup[OF cong_dist lveq] cong_len by simp
    thus "?csub (cong_atoms ! k) = ?vals ! k" by simp
  qed
  have csub_off: "\<And>v. v \<notin> set cong_atoms \<Longrightarrow> ?csub v = Atom v"
  proof -
    fix v assume "v \<notin> set cong_atoms"
    hence "map_of (zip cong_atoms ?vals) v = None" by (rule map_of_zip_None_lookup)
    thus "?csub v = Atom v" by simp
  qed
  have sub_id: "\<forall>v. v \<notin> set cong_atoms \<longrightarrow> ?csub v = Atom v"
    using csub_off by blast
  note csub_conn = fresh_sub_conn[OF cong_disj sub_id]
  note csub_cb = fresh_sub_cb[OF cong_disj sub_id]
  have csub_in_vals: "\<And>v. v \<in> set cong_atoms \<Longrightarrow> ?csub v \<in> set ?vals"
  proof -
    fix v assume "v \<in> set cong_atoms"
    hence "\<exists>w. map_of (zip cong_atoms ?vals) v = Some w"
      using map_of_zip_is_Some[OF lveq] by blast
    then obtain w where w: "map_of (zip cong_atoms ?vals) v = Some w" by blast
    hence "(v, w) \<in> set (zip cong_atoms ?vals)" by (rule map_of_SomeD)
    hence "w \<in> set ?vals" by (rule set_zip_rightD)
    thus "?csub v \<in> set ?vals" using w by simp
  qed

  \<comment> \<open>Substitution-size facts.\<close>
  have csub_len_le: "\<And>v. v \<in> set cong_atoms \<Longrightarrow> len_formula (?csub v) \<le> ?sumlens"
  proof -
    fix v assume "v \<in> set cong_atoms"
    hence "?csub v \<in> set ?vals" using csub_in_vals by blast
    hence "?csub v = X \<or> ?csub v = X' \<or> ?csub v = Y \<or> ?csub v = Y'
           \<or> ?csub v = Z \<or> ?csub v = Z'" by auto
    thus "len_formula (?csub v) \<le> ?sumlens" by (elim disjE) simp_all
  qed
  have csub_depth_le: "\<And>v. v \<in> set cong_atoms \<Longrightarrow> depth_formula (?csub v) \<le> ?maxdep6"
  proof -
    fix v assume "v \<in> set cong_atoms"
    hence "?csub v \<in> set ?vals" using csub_in_vals by blast
    hence "?csub v = X \<or> ?csub v = X' \<or> ?csub v = Y \<or> ?csub v = Y'
           \<or> ?csub v = Z \<or> ?csub v = Z'" by auto
    thus "depth_formula (?csub v) \<le> ?maxdep6" by (elim disjE) simp_all
  qed
  have len_sub_le: "len_sub (set cong_atoms) ?csub \<le> 6 * ?sumlens"
  proof -
    have "(\<Sum>v \<in> set cong_atoms. len_formula (?csub v))
        = sum_list (map (\<lambda>v. len_formula (?csub v)) cong_atoms)"
      by (simp add: sum_list_distinct_conv_sum_set[OF cong_dist])
    also have "\<dots> \<le> sum_list (map (\<lambda>v. ?sumlens) cong_atoms)"
      by (rule sum_list_mono[OF csub_len_le])
    also have "\<dots> = length cong_atoms * ?sumlens"
      by (simp add: sum_list_triv)
    also have "\<dots> = 6 * ?sumlens" using cong_len by simp
    finally have sum_le: "(\<Sum>v \<in> set cong_atoms. len_formula (?csub v))
                          \<le> 6 * ?sumlens" .
    have "(1::nat) \<le> 6 * ?sumlens"
      using len_formula_positive[of X] by simp
    thus ?thesis unfolding len_sub_def using sum_le by simp
  qed
  have depth_sub_le: "depth_sub (set cong_atoms) ?csub \<le> ?maxdep6"
    unfolding depth_sub_def
  proof (rule Max.boundedI)
    show "finite (insert 1 ((\<lambda>v. depth_formula (?csub v)) ` set cong_atoms))"
      by simp
    show "insert 1 ((\<lambda>v. depth_formula (?csub v)) ` set cong_atoms) \<noteq> {}"
      by simp
    fix e assume e_in: "e \<in> insert 1 ((\<lambda>v. depth_formula (?csub v)) ` set cong_atoms)"
    show "e \<le> ?maxdep6"
    proof (cases "e = 1")
      case True
      thus ?thesis using depth_formula_ge_1[of X] by auto
    next
      case False
      hence "e \<in> (\<lambda>v. depth_formula (?csub v)) ` set cong_atoms" using e_in by simp
      then obtain v where v_in: "v \<in> set cong_atoms"
                      and e_eq: "e = depth_formula (?csub v)" by auto
      show ?thesis unfolding e_eq by (rule csub_depth_le[OF v_in])
    qed
  qed

  from assms(1) obtain pX where pX:
    "valid_proof F pX" "assumptions pX = {}"
    "frege_proof.thesis pX = iff_form X X'"
    "length (steps pX) \<le> lx"
    "\<forall>s \<in> set (steps pX). len_formula s \<le> sx"
    "\<forall>s \<in> set (steps pX). depth_formula s \<le> dx"
    unfolding provable_balanced_iff_def by blast
  from assms(2) obtain pY where pY:
    "valid_proof F pY" "assumptions pY = {}"
    "frege_proof.thesis pY = iff_form Y Y'"
    "length (steps pY) \<le> ly"
    "\<forall>s \<in> set (steps pY). len_formula s \<le> sy"
    "\<forall>s \<in> set (steps pY). depth_formula s \<le> dy"
    unfolding provable_balanced_iff_def by blast
  from assms(3) obtain pZ where pZ:
    "valid_proof F pZ" "assumptions pZ = {}"
    "frege_proof.thesis pZ = iff_form Z Z'"
    "length (steps pZ) \<le> lz"
    "\<forall>s \<in> set (steps pZ). len_formula s \<le> sz"
    "\<forall>s \<in> set (steps pZ). depth_formula s \<le> dz"
    unfolding provable_balanced_iff_def by blast

  \<comment> \<open>The substituted congruence proof.\<close>
  define ci where ci_def: "ci = sub_proof ?csub balance_cong_base_proof"
  have valid_ci: "valid_proof F ci"
    unfolding ci_def
    using frege_system.proof_substitution[OF fs_F] balance_cong_base_proof_spec
    by blast
  have ci_steps: "steps ci = map (sub_formula ?csub) (steps balance_cong_base_proof)"
    unfolding ci_def by simp
  have ci_lines: "length (steps ci) = balance_cong_lines"
    using ci_steps by (simp add: balance_cong_lines_def)
  have ci_thesis: "frege_proof.thesis ci = iff_form (balance X Y Z) (balance X' Y' Z')"
  proof -
    have bXYZ: "sub_formula ?csub (balance (Atom ?a0) (Atom ?a2) (Atom ?a4))
              = balance X Y Z"
    proof -
      have "sub_formula ?csub (balance (Atom ?a0) (Atom ?a2) (Atom ?a4))
          = balance (sub_formula ?csub (Atom ?a0)) (sub_formula ?csub (Atom ?a2))
                    (sub_formula ?csub (Atom ?a4))"
        by (rule sub_formula_balance[OF csub_cb])
      thus ?thesis by (simp add: csub_nth)
    qed
    have bXYZ': "sub_formula ?csub (balance (Atom ?a1) (Atom ?a3) (Atom ?a5))
               = balance X' Y' Z'"
    proof -
      have "sub_formula ?csub (balance (Atom ?a1) (Atom ?a3) (Atom ?a5))
          = balance (sub_formula ?csub (Atom ?a1)) (sub_formula ?csub (Atom ?a3))
                    (sub_formula ?csub (Atom ?a5))"
        by (rule sub_formula_balance[OF csub_cb])
      thus ?thesis by (simp add: csub_nth)
    qed
    have "frege_proof.thesis ci
        = sub_formula ?csub
            (iff_form (balance (Atom ?a0) (Atom ?a2) (Atom ?a4))
                      (balance (Atom ?a1) (Atom ?a3) (Atom ?a5)))"
      unfolding ci_def using balance_cong_base_proof_spec by simp
    also have "\<dots> = iff_form
            (sub_formula ?csub (balance (Atom ?a0) (Atom ?a2) (Atom ?a4)))
            (sub_formula ?csub (balance (Atom ?a1) (Atom ?a3) (Atom ?a5)))"
      by (rule sub_formula_iff_form[OF csub_conn])
    also have "\<dots> = iff_form (balance X Y Z) (balance X' Y' Z')"
      using bXYZ bXYZ' by simp
    finally show ?thesis .
  qed
  have ci_asm: "assumptions ci = {iff_form X X', iff_form Y Y', iff_form Z Z'}"
  proof -
    have aXX: "sub_formula ?csub (iff_form (Atom ?a0) (Atom ?a1)) = iff_form X X'"
    proof -
      have "sub_formula ?csub (iff_form (Atom ?a0) (Atom ?a1))
          = iff_form (sub_formula ?csub (Atom ?a0)) (sub_formula ?csub (Atom ?a1))"
        by (rule sub_formula_iff_form[OF csub_conn])
      thus ?thesis by (simp add: csub_nth)
    qed
    have aYY: "sub_formula ?csub (iff_form (Atom ?a2) (Atom ?a3)) = iff_form Y Y'"
    proof -
      have "sub_formula ?csub (iff_form (Atom ?a2) (Atom ?a3))
          = iff_form (sub_formula ?csub (Atom ?a2)) (sub_formula ?csub (Atom ?a3))"
        by (rule sub_formula_iff_form[OF csub_conn])
      thus ?thesis by (simp add: csub_nth)
    qed
    have aZZ: "sub_formula ?csub (iff_form (Atom ?a4) (Atom ?a5)) = iff_form Z Z'"
    proof -
      have "sub_formula ?csub (iff_form (Atom ?a4) (Atom ?a5))
          = iff_form (sub_formula ?csub (Atom ?a4)) (sub_formula ?csub (Atom ?a5))"
        by (rule sub_formula_iff_form[OF csub_conn])
      thus ?thesis by (simp add: csub_nth)
    qed
    have "assumptions ci = (sub_formula ?csub) ` (assumptions balance_cong_base_proof)"
      unfolding ci_def by simp
    also have "\<dots> = (sub_formula ?csub) `
         {iff_form (Atom ?a0) (Atom ?a1), iff_form (Atom ?a2) (Atom ?a3),
          iff_form (Atom ?a4) (Atom ?a5)}"
      using balance_cong_base_proof_spec by simp
    also have "\<dots> = {iff_form X X', iff_form Y Y', iff_form Z Z'}"
      using aXX aYY aZZ by simp
    finally show ?thesis .
  qed

  \<comment> \<open>Combine the three input proofs, then the congruence step.\<close>
  define c1 where c1_def: "c1 = combine_proofs pX pY"
  have valid_c1: "valid_proof F c1"
    unfolding c1_def
    using frege_system.combining_valid_proofs[OF fs_F] pX(1) pY(1) by blast
  have c1_asm: "assumptions c1 = {}"
    unfolding c1_def using pX(2) pY(2) by simp
  have c1_steps: "steps c1 = steps pX @ steps pY"
    unfolding c1_def by simp

  define c2 where c2_def: "c2 = combine_proofs c1 pZ"
  have valid_c2: "valid_proof F c2"
    unfolding c2_def
    using frege_system.combining_valid_proofs[OF fs_F] valid_c1 pZ(1) by blast
  have c2_asm: "assumptions c2 = {}"
    unfolding c2_def using c1_asm pZ(2) by simp
  have c2_steps: "steps c2 = steps pX @ steps pY @ steps pZ"
  proof -
    have "steps c2 = steps c1 @ steps pZ" unfolding c2_def by simp
    thus ?thesis using c1_steps by simp
  qed

  define cb where cb_def: "cb = combine_proofs c2 ci"
  have valid_cb: "valid_proof F cb"
    unfolding cb_def
    using frege_system.combining_valid_proofs[OF fs_F] valid_c2 valid_ci by blast

  have XX_in: "iff_form X X' \<in> set (steps pX)"
  proof -
    have ne: "steps pX \<noteq> []" using pX(1) unfolding valid_proof_def by simp
    have "frege_proof.thesis pX = last (steps pX)"
      using pX(1) unfolding valid_proof_def by simp
    hence "iff_form X X' = last (steps pX)" using pX(3) by simp
    moreover have "last (steps pX) \<in> set (steps pX)" using ne by (rule last_in_set)
    ultimately show ?thesis by simp
  qed
  have YY_in: "iff_form Y Y' \<in> set (steps pY)"
  proof -
    have ne: "steps pY \<noteq> []" using pY(1) unfolding valid_proof_def by simp
    have "frege_proof.thesis pY = last (steps pY)"
      using pY(1) unfolding valid_proof_def by simp
    hence "iff_form Y Y' = last (steps pY)" using pY(3) by simp
    moreover have "last (steps pY) \<in> set (steps pY)" using ne by (rule last_in_set)
    ultimately show ?thesis by simp
  qed
  have ZZ_in: "iff_form Z Z' \<in> set (steps pZ)"
  proof -
    have ne: "steps pZ \<noteq> []" using pZ(1) unfolding valid_proof_def by simp
    have "frege_proof.thesis pZ = last (steps pZ)"
      using pZ(1) unfolding valid_proof_def by simp
    hence "iff_form Z Z' = last (steps pZ)" using pZ(3) by simp
    moreover have "last (steps pZ) \<in> set (steps pZ)" using ne by (rule last_in_set)
    ultimately show ?thesis by simp
  qed

  have cb_asm: "assumptions cb = {}"
  proof -
    have sub: "{iff_form X X', iff_form Y Y', iff_form Z Z'} \<subseteq> set (steps c2)"
      using XX_in YY_in ZZ_in c2_steps by auto
    have "assumptions cb = assumptions c2 \<union> (assumptions ci - set (steps c2))"
      unfolding cb_def by simp
    also have "\<dots> = {} \<union> ({iff_form X X', iff_form Y Y', iff_form Z Z'}
                          - set (steps c2))"
      using c2_asm ci_asm by simp
    also have "\<dots> = {}" using sub by blast
    finally show ?thesis .
  qed
  have cb_thesis: "frege_proof.thesis cb = iff_form (balance X Y Z) (balance X' Y' Z')"
    unfolding cb_def using ci_thesis by simp
  have cb_steps: "steps cb = steps pX @ steps pY @ steps pZ @ steps ci"
  proof -
    have "steps cb = steps c2 @ steps ci" unfolding cb_def by simp
    thus ?thesis using c2_steps by simp
  qed

  have cb_lines: "length (steps cb) \<le> ?lines_t"
  proof -
    have "length (steps cb)
        = length (steps pX) + length (steps pY) + length (steps pZ)
          + length (steps ci)"
      using cb_steps by simp
    thus ?thesis using pX(4) pY(4) pZ(4) ci_lines by linarith
  qed

  have fin_bl: "finite (insert 1 (len_formula ` set (steps balance_cong_base_proof)))"
    by simp
  have fin_bd: "finite (insert 1 (depth_formula ` set (steps balance_cong_base_proof)))"
    by simp

  have step_len: "\<forall>s \<in> set (steps cb). len_formula s \<le> ?sz_t"
  proof
    fix s assume "s \<in> set (steps cb)"
    hence "s \<in> set (steps pX) \<or> s \<in> set (steps pY) \<or> s \<in> set (steps pZ)
           \<or> s \<in> set (steps ci)"
      using cb_steps by auto
    thus "len_formula s \<le> ?sz_t"
    proof (elim disjE)
      assume "s \<in> set (steps pX)"
      hence "len_formula s \<le> sx" using pX(5) by blast
      thus ?thesis by linarith
    next
      assume "s \<in> set (steps pY)"
      hence "len_formula s \<le> sy" using pY(5) by blast
      thus ?thesis by linarith
    next
      assume "s \<in> set (steps pZ)"
      hence "len_formula s \<le> sz" using pZ(5) by blast
      thus ?thesis by linarith
    next
      assume "s \<in> set (steps ci)"
      then obtain s0 where s0_in: "s0 \<in> set (steps balance_cong_base_proof)"
                       and s_eq: "s = sub_formula ?csub s0"
        using ci_steps by auto
      have "len_formula s \<le> len_formula s0 * len_sub (set cong_atoms) ?csub"
        using s_eq sub_formula_bound[OF fin_ca sub_id] by simp
      also have "\<dots> \<le> len_formula s0 * (6 * ?sumlens)"
        using len_sub_le by (rule mult_le_mono2)
      also have "\<dots> \<le> balance_cong_step_len * (6 * ?sumlens)"
      proof -
        have "len_formula s0
            \<in> insert 1 (len_formula ` set (steps balance_cong_base_proof))"
          using s0_in by simp
        hence "len_formula s0 \<le> balance_cong_step_len"
          unfolding balance_cong_step_len_def using Max_ge[OF fin_bl] by blast
        thus ?thesis by (rule mult_le_mono1)
      qed
      finally show ?thesis by linarith
    qed
  qed

  have dx_le: "dx \<le> ?dep_t" by (rule max.cobounded1)
  have dy_le: "dy \<le> ?dep_t"
  proof -
    have "dy \<le> max dy (max dz (balance_cong_step_depth + ?maxdep6))"
      by (rule max.cobounded1)
    also have "\<dots> \<le> ?dep_t" by (rule max.cobounded2)
    finally show ?thesis .
  qed
  have dz_le: "dz \<le> ?dep_t"
  proof -
    have "dz \<le> max dz (balance_cong_step_depth + ?maxdep6)"
      by (rule max.cobounded1)
    also have "\<dots> \<le> max dy (max dz (balance_cong_step_depth + ?maxdep6))"
      by (rule max.cobounded2)
    also have "\<dots> \<le> ?dep_t" by (rule max.cobounded2)
    finally show ?thesis .
  qed
  have ci_dep_le: "balance_cong_step_depth + ?maxdep6 \<le> ?dep_t"
  proof -
    have "balance_cong_step_depth + ?maxdep6
        \<le> max dz (balance_cong_step_depth + ?maxdep6)"
      by (rule max.cobounded2)
    also have "\<dots> \<le> max dy (max dz (balance_cong_step_depth + ?maxdep6))"
      by (rule max.cobounded2)
    also have "\<dots> \<le> ?dep_t" by (rule max.cobounded2)
    finally show ?thesis .
  qed

  have step_depth: "\<forall>s \<in> set (steps cb). depth_formula s \<le> ?dep_t"
  proof
    fix s assume "s \<in> set (steps cb)"
    hence "s \<in> set (steps pX) \<or> s \<in> set (steps pY) \<or> s \<in> set (steps pZ)
           \<or> s \<in> set (steps ci)"
      using cb_steps by auto
    thus "depth_formula s \<le> ?dep_t"
    proof (elim disjE)
      assume "s \<in> set (steps pX)"
      hence "depth_formula s \<le> dx" using pX(6) by blast
      thus ?thesis using dx_le by linarith
    next
      assume "s \<in> set (steps pY)"
      hence "depth_formula s \<le> dy" using pY(6) by blast
      thus ?thesis using dy_le by linarith
    next
      assume "s \<in> set (steps pZ)"
      hence "depth_formula s \<le> dz" using pZ(6) by blast
      thus ?thesis using dz_le by linarith
    next
      assume "s \<in> set (steps ci)"
      then obtain s0 where s0_in: "s0 \<in> set (steps balance_cong_base_proof)"
                       and s_eq: "s = sub_formula ?csub s0"
        using ci_steps by auto
      have "depth_formula s \<le> depth_formula s0 + depth_sub (set cong_atoms) ?csub"
        using s_eq sub_formula_depth_bound[OF fin_ca sub_id] by simp
      also have "\<dots> \<le> depth_formula s0 + ?maxdep6"
        using depth_sub_le by linarith
      also have "\<dots> \<le> balance_cong_step_depth + ?maxdep6"
      proof -
        have "depth_formula s0
            \<in> insert 1 (depth_formula ` set (steps balance_cong_base_proof))"
          using s0_in by simp
        hence "depth_formula s0 \<le> balance_cong_step_depth"
          unfolding balance_cong_step_depth_def using Max_ge[OF fin_bd] by blast
        thus ?thesis by (rule add_right_mono)
      qed
      also have "\<dots> \<le> ?dep_t" using ci_dep_le by linarith
      finally show ?thesis .
    qed
  qed

  show ?thesis
    unfolding provable_balanced_iff_def
  proof (intro exI[where x = cb] conjI)
    show "valid_proof F cb" using valid_cb .
    show "assumptions cb = {}" using cb_asm .
    show "frege_proof.thesis cb = iff_form (balance X Y Z) (balance X' Y' Z')"
      using cb_thesis .
    show "length (steps cb) \<le> ?lines_t" using cb_lines .
    show "\<forall>s \<in> set (steps cb). len_formula s \<le> ?sz_t" using step_len .
    show "\<forall>s \<in> set (steps cb). depth_formula s \<le> ?dep_t" using step_depth .
  qed
qed

(*
  rebalancing p pos: Reckhow's t(P/R) --- the top-level subtree at pos is
  pulled out and the formula rebalanced around it. The threshold guard makes
  rebalancing collapse to spira_trans p below threshold and at the
  spira-selected position, so the easy cases of Lemma 5.1 are reflexivity (E3).
*)
(*
  rebalancing p pos: Reckhow's t(P/R) --- balance(t(P_{R=1}), t(P_{R=0}),
  t(R)). Faithful to Definition 5.1, with no threshold guard, so the three
  hard cases of Lemma 5.1 open up uniformly; the below-threshold degeneracy
  is concentrated in one easy case instead.
*)
subsection \<open>Rebalancing: definition and basic facts\<close>

definition rebalancing :: "'c formula \<Rightarrow> nat list \<Rightarrow> 'c formula" where
  "rebalancing p pos =
     balance (spira_trans (fix_at pos True p))
             (spira_trans (fix_at pos False p))
             (spira_trans (subterm_at p pos))"

lemma rebalancing_eq_spira_trans:
  assumes "formula_well_formed (alphabet F) p"
      and "len_formula p \<ge> spira_threshold"
    shows "rebalancing p (spiras_sel_position p) = spira_trans p"
proof -
  from spira_trans_dom_and_eval[OF assms(1)] have dom: "spira_trans_dom p" by simp
  have ge2: "len_formula p \<ge> 2" using assms(2) unfolding spira_threshold_def by simp
  show ?thesis
  proof (cases p)
    case (Atom v)
    thus ?thesis using ge2 by simp
  next
    case (Conn c fs)
    show ?thesis
    proof (cases fs)
      case Nil
      thus ?thesis using ge2 Conn by simp
    next
      case (Cons f1 fs1)
      have psimp: "spira_trans (Conn c (f1 # fs1)) =
            (let p' = Conn c (f1 # fs1); pos = spiras_sel_position p' in
              if len_formula p' < spira_threshold then p'
              else balance (spira_trans (fix_at pos True p'))
                           (spira_trans (fix_at pos False p'))
                           (spira_trans (subterm_at p' pos)))"
        using dom Conn Cons by (simp add: spira_trans.psimps(3))
      have "spira_trans p
          = balance (spira_trans (fix_at (spiras_sel_position p) True p))
                    (spira_trans (fix_at (spiras_sel_position p) False p))
                    (spira_trans (subterm_at p (spiras_sel_position p)))"
        using psimp Conn Cons assms(2) by (simp add: Let_def)
      thus ?thesis unfolding rebalancing_def by simp
    qed
  qed
qed

lemma rebalancing_wf:
  assumes "formula_well_formed (alphabet F) p"
      and "valid_position p pos"
    shows "formula_well_formed (alphabet F) (rebalancing p pos)"
proof -
  have w1: "formula_well_formed (alphabet F) (spira_trans (fix_at pos True p))"
    using fix_at_wf[OF assms(1)] by (rule spira_trans_wf)
  have w2: "formula_well_formed (alphabet F) (spira_trans (fix_at pos False p))"
    using fix_at_wf[OF assms(1)] by (rule spira_trans_wf)
  have w3: "formula_well_formed (alphabet F) (spira_trans (subterm_at p pos))"
    using subterm_at_wf[OF assms] by (rule spira_trans_wf)
  show ?thesis unfolding rebalancing_def using balance_wf[OF w1 w2 w3] by simp
qed

lemma rebalancing_eval:
  assumes "formula_well_formed (alphabet F) p"
      and "valid_position p pos"
    shows "eval (alphabet F) val (rebalancing p pos) = eval (alphabet F) val p"
proof -
  have wf_T: "formula_well_formed (alphabet F) (fix_at pos True p)"
    using assms(1) by (rule fix_at_wf)
  have wf_F: "formula_well_formed (alphabet F) (fix_at pos False p)"
    using assms(1) by (rule fix_at_wf)
  have wf_sub: "formula_well_formed (alphabet F) (subterm_at p pos)"
    using subterm_at_wf[OF assms] .
  have "eval (alphabet F) val (rebalancing p pos)
      = (if eval (alphabet F) val (spira_trans (subterm_at p pos))
         then eval (alphabet F) val (spira_trans (fix_at pos True p))
         else eval (alphabet F) val (spira_trans (fix_at pos False p)))"
    unfolding rebalancing_def by (rule balance_eval)
  also have "\<dots> = (if eval (alphabet F) val (subterm_at p pos)
                   then eval (alphabet F) val (fix_at pos True p)
                   else eval (alphabet F) val (fix_at pos False p))"
    using spira_trans_dom_and_eval[OF wf_T] spira_trans_dom_and_eval[OF wf_F]
          spira_trans_dom_and_eval[OF wf_sub] by simp
  also have "\<dots> = eval (alphabet F) val p"
    using fix_at_eval[OF assms(2), symmetric] by simp
  finally show ?thesis .
qed

(*
  Case 1's key identity (Reckhow's P_{R=b,Q=c} = P_{Q=c}): rebalancing the
  R-fixed formula P_{R=b} at the ancestor position qp gives a balance whose
  outer leaves are t(P_{Q=True}), t(P_{Q=False}) --- the R-fix is overridden
  by the ancestor fix --- and whose inner node is t(Q_{R=b}).
*)
lemma case1_right_leaf:
  assumes "valid_position p qp"
    shows "rebalancing (fix_at (qp @ rp) b p) qp
         = balance (spira_trans (fix_at qp True p))
                   (spira_trans (fix_at qp False p))
                   (spira_trans (fix_at rp b (subterm_at p qp)))"
proof -
  have t: "fix_at qp True (fix_at (qp @ rp) b p) = fix_at qp True p"
    by (rule fix_at_ancestor_overrides)
  have f: "fix_at qp False (fix_at (qp @ rp) b p) = fix_at qp False p"
    by (rule fix_at_ancestor_overrides)
  have s: "subterm_at (fix_at (qp @ rp) b p) qp = fix_at rp b (subterm_at p qp)"
    by (rule subterm_at_fix_at_prefix[OF assms])
  show ?thesis unfolding rebalancing_def using t f s by simp
qed

(* iff_sym: symmetry, from the fixed identity (x \<leftrightarrow> y) \<turnstile> (y \<leftrightarrow> x). *)
subsection \<open>Symmetry of balanced equivalence\<close>

definition sym_atom_x :: string where "sym_atom_x = fresh_atoms 2 ! 0"
definition sym_atom_y :: string where "sym_atom_y = fresh_atoms 2 ! 1"

lemma sym_atoms_spec:
  "sym_atom_x \<notin> avoid_atoms \<and> sym_atom_y \<notin> avoid_atoms
   \<and> sym_atom_x \<noteq> sym_atom_y"
proof -
  have len2: "length (fresh_atoms 2) = 2" using fresh_atoms_spec[of 2] by simp
  have dist: "distinct (fresh_atoms 2)" using fresh_atoms_spec[of 2] by simp
  have disj: "set (fresh_atoms 2) \<inter> avoid_atoms = {}"
    using fresh_atoms_spec[of 2] by simp
  have m0: "fresh_atoms 2 ! 0 \<in> set (fresh_atoms 2)"
    using nth_mem[of 0 "fresh_atoms 2"] len2 by simp
  have m1: "fresh_atoms 2 ! 1 \<in> set (fresh_atoms 2)"
    using nth_mem[of 1 "fresh_atoms 2"] len2 by simp
  have "sym_atom_x \<notin> avoid_atoms" unfolding sym_atom_x_def using m0 disj by blast
  moreover have "sym_atom_y \<notin> avoid_atoms"
    unfolding sym_atom_y_def using m1 disj by blast
  moreover have "sym_atom_x \<noteq> sym_atom_y"
    unfolding sym_atom_x_def sym_atom_y_def
    using nth_eq_iff_index_eq[OF dist, of 0 1] len2 by simp
  ultimately show ?thesis by blast
qed

definition sym_base_proof :: "'c frege_proof" where
  "sym_base_proof =
     entails_proof {iff_form (Atom sym_atom_x) (Atom sym_atom_y)}
                   (iff_form (Atom sym_atom_y) (Atom sym_atom_x))"

lemma sym_base_proof_spec:
  "valid_proof F sym_base_proof
   \<and> assumptions sym_base_proof = {iff_form (Atom sym_atom_x) (Atom sym_atom_y)}
   \<and> thesis sym_base_proof = iff_form (Atom sym_atom_y) (Atom sym_atom_x)"
proof -
  have "\<forall>val. (\<forall>f \<in> {iff_form (Atom sym_atom_x) (Atom sym_atom_y)}.
                eval (alphabet F) val f)
              \<longrightarrow> eval (alphabet F) val
                    (iff_form (Atom sym_atom_y) (Atom sym_atom_x))"
    using iff_form_eval by auto
  thus ?thesis
    unfolding sym_base_proof_def using entails_proof_spec by blast
qed

definition sym_lines :: nat where
  "sym_lines = length (steps sym_base_proof)"

definition sym_step_len :: nat where
  "sym_step_len = Max (insert 1 (len_formula ` set (steps sym_base_proof)))"

definition sym_step_depth :: nat where
  "sym_step_depth = Max (insert 1 (depth_formula ` set (steps sym_base_proof)))"

lemma iff_sym:
  assumes "provable_balanced_iff A B l s d"
    shows "provable_balanced_iff B A
             (l + sym_lines)
             (s + sym_step_len * (len_formula A + len_formula B))
             (max d (sym_step_depth
                + max (depth_formula A) (depth_formula B)))"
proof -
  have fs_F: "frege_system F"
    by (meson frege_balancing_axioms frege_balancing_def)
  let ?x = "sym_atom_x" and ?y = "sym_atom_y"
  let ?sub = "\<lambda>w. if w = ?x then A else if w = ?y then B else Atom w"
  let ?lines_t = "l + sym_lines"
  let ?sz_t = "s + sym_step_len * (len_formula A + len_formula B)"
  let ?dep_t = "max d (sym_step_depth
                  + max (depth_formula A) (depth_formula B))"

  have neq: "?x \<noteq> ?y" using sym_atoms_spec by blast

  from assms obtain pAB where pAB:
    "valid_proof F pAB" "assumptions pAB = {}"
    "frege_proof.thesis pAB = iff_form A B"
    "length (steps pAB) \<le> l"
    "\<forall>t \<in> set (steps pAB). len_formula t \<le> s"
    "\<forall>t \<in> set (steps pAB). depth_formula t \<le> d"
    unfolding provable_balanced_iff_def by blast

  have sub_conn_iff:
    "\<And>w. w \<in> var_set_form conn_iff \<Longrightarrow> w \<noteq> ''a'' \<Longrightarrow> w \<noteq> ''b''
           \<Longrightarrow> ?sub w = Atom w"
  proof -
    fix w assume w_ci: "w \<in> var_set_form conn_iff"
      and "w \<noteq> ''a''" and "w \<noteq> ''b''"
    have "w \<in> avoid_atoms" using w_ci unfolding avoid_atoms_def by blast
    hence "w \<noteq> ?x \<and> w \<noteq> ?y" using sym_atoms_spec by blast
    thus "?sub w = Atom w" by simp
  qed
  have sub_id: "\<forall>v. v \<notin> {?x, ?y} \<longrightarrow> ?sub v = Atom v" by auto
  have fin_xy: "finite {?x, ?y}" by simp

  define si where si_def: "si = sub_proof ?sub sym_base_proof"
  have valid_si: "valid_proof F si"
    unfolding si_def
    using frege_system.proof_substitution[OF fs_F] sym_base_proof_spec by blast
  have si_steps: "steps si = map (sub_formula ?sub) (steps sym_base_proof)"
    unfolding si_def by simp
  have si_thesis: "frege_proof.thesis si = iff_form B A"
  proof -
    have "frege_proof.thesis si
        = sub_formula ?sub (iff_form (Atom ?y) (Atom ?x))"
      unfolding si_def using sym_base_proof_spec by simp
    also have "\<dots> = iff_form (sub_formula ?sub (Atom ?y)) (sub_formula ?sub (Atom ?x))"
      by (rule sub_formula_iff_form[OF sub_conn_iff])
    also have "\<dots> = iff_form B A" using neq by simp
    finally show ?thesis .
  qed
  have si_asm: "assumptions si = {iff_form A B}"
  proof -
    have "sub_formula ?sub (iff_form (Atom ?x) (Atom ?y)) = iff_form A B"
    proof -
      have "sub_formula ?sub (iff_form (Atom ?x) (Atom ?y))
          = iff_form (sub_formula ?sub (Atom ?x)) (sub_formula ?sub (Atom ?y))"
        by (rule sub_formula_iff_form[OF sub_conn_iff])
      thus ?thesis using neq by simp
    qed
    moreover have "assumptions si
                 = (sub_formula ?sub) ` (assumptions sym_base_proof)"
      unfolding si_def by simp
    ultimately show ?thesis using sym_base_proof_spec by simp
  qed
  have si_lines: "length (steps si) = sym_lines"
    using si_steps by (simp add: sym_lines_def)

  have len_sub_eq: "len_sub {?x, ?y} ?sub = len_formula A + len_formula B"
  proof -
    have "(\<Sum>v \<in> {?x, ?y}. len_formula (?sub v))
        = len_formula A + len_formula B"
      using neq by simp
    moreover have "len_formula A \<ge> 1" by (rule len_formula_positive)
    ultimately show ?thesis unfolding len_sub_def by simp
  qed
  have depth_sub_le: "depth_sub {?x, ?y} ?sub
                    \<le> max (depth_formula A) (depth_formula B)"
  proof -
    have img: "(\<lambda>v. depth_formula (?sub v)) ` {?x, ?y}
             = {depth_formula A, depth_formula B}"
      using neq by auto
    have "depth_sub {?x, ?y} ?sub
        = Max (insert 1 {depth_formula A, depth_formula B})"
      unfolding depth_sub_def using img by simp
    also have "\<dots> \<le> max (depth_formula A) (depth_formula B)"
    proof (rule Max.boundedI)
      show "finite (insert 1 {depth_formula A, depth_formula B})" by simp
      show "insert 1 {depth_formula A, depth_formula B} \<noteq> {}" by simp
      fix e assume "e \<in> insert 1 {depth_formula A, depth_formula B}"
      thus "e \<le> max (depth_formula A) (depth_formula B)"
        using depth_formula_ge_1[of A] depth_formula_ge_1[of B] by auto
    qed
    finally show ?thesis .
  qed

  have fin_sl: "finite (insert 1 (len_formula ` set (steps sym_base_proof)))"
    by simp
  have fin_sd: "finite (insert 1 (depth_formula ` set (steps sym_base_proof)))"
    by simp

  define cb where cb_def: "cb = combine_proofs pAB si"
  have valid_cb: "valid_proof F cb"
    unfolding cb_def
    using frege_system.combining_valid_proofs[OF fs_F] pAB(1) valid_si by blast

  have AB_in: "iff_form A B \<in> set (steps pAB)"
  proof -
    have ne: "steps pAB \<noteq> []" using pAB(1) unfolding valid_proof_def by simp
    have "frege_proof.thesis pAB = last (steps pAB)"
      using pAB(1) unfolding valid_proof_def by simp
    hence "iff_form A B = last (steps pAB)" using pAB(3) by simp
    moreover have "last (steps pAB) \<in> set (steps pAB)" using ne by (rule last_in_set)
    ultimately show ?thesis by simp
  qed

  have cb_asm: "assumptions cb = {}"
  proof -
    have "assumptions cb = assumptions pAB \<union> (assumptions si - set (steps pAB))"
      unfolding cb_def by simp
    also have "\<dots> = {} \<union> ({iff_form A B} - set (steps pAB))"
      using pAB(2) si_asm by simp
    also have "\<dots> = {}" using AB_in by blast
    finally show ?thesis .
  qed
  have cb_thesis: "frege_proof.thesis cb = iff_form B A"
    unfolding cb_def using si_thesis by simp
  have cb_steps: "steps cb = steps pAB @ steps si"
    unfolding cb_def by simp

  have cb_lines: "length (steps cb) \<le> ?lines_t"
  proof -
    have "length (steps cb) = length (steps pAB) + length (steps si)"
      using cb_steps by simp
    thus ?thesis using pAB(4) si_lines by linarith
  qed

  have d_le: "d \<le> ?dep_t" by (rule max.cobounded1)
  have si_dep_le: "sym_step_depth + max (depth_formula A) (depth_formula B) \<le> ?dep_t"
    by (rule max.cobounded2)

  have step_len: "\<forall>t \<in> set (steps cb). len_formula t \<le> ?sz_t"
  proof
    fix t assume "t \<in> set (steps cb)"
    hence "t \<in> set (steps pAB) \<or> t \<in> set (steps si)"
      using cb_steps by auto
    thus "len_formula t \<le> ?sz_t"
    proof (elim disjE)
      assume "t \<in> set (steps pAB)"
      hence "len_formula t \<le> s" using pAB(5) by blast
      thus ?thesis by linarith
    next
      assume "t \<in> set (steps si)"
      then obtain t0 where t0_in: "t0 \<in> set (steps sym_base_proof)"
                       and t_eq: "t = sub_formula ?sub t0"
        using si_steps by auto
      have "len_formula t \<le> len_formula t0 * len_sub {?x, ?y} ?sub"
        using t_eq sub_formula_bound[OF fin_xy sub_id] by simp
      also have "\<dots> = len_formula t0 * (len_formula A + len_formula B)"
        using len_sub_eq by simp
      also have "\<dots> \<le> sym_step_len * (len_formula A + len_formula B)"
      proof -
        have "len_formula t0 \<in> insert 1 (len_formula ` set (steps sym_base_proof))"
          using t0_in by simp
        hence "len_formula t0 \<le> sym_step_len"
          unfolding sym_step_len_def using Max_ge[OF fin_sl] by blast
        thus ?thesis by (rule mult_le_mono1)
      qed
      finally show ?thesis by linarith
    qed
  qed

  have step_depth: "\<forall>t \<in> set (steps cb). depth_formula t \<le> ?dep_t"
  proof
    fix t assume "t \<in> set (steps cb)"
    hence "t \<in> set (steps pAB) \<or> t \<in> set (steps si)"
      using cb_steps by auto
    thus "depth_formula t \<le> ?dep_t"
    proof (elim disjE)
      assume "t \<in> set (steps pAB)"
      hence "depth_formula t \<le> d" using pAB(6) by blast
      thus ?thesis using d_le by linarith
    next
      assume "t \<in> set (steps si)"
      then obtain t0 where t0_in: "t0 \<in> set (steps sym_base_proof)"
                       and t_eq: "t = sub_formula ?sub t0"
        using si_steps by auto
      have "depth_formula t \<le> depth_formula t0 + depth_sub {?x, ?y} ?sub"
        using t_eq sub_formula_depth_bound[OF fin_xy sub_id] by simp
      also have "\<dots> \<le> depth_formula t0
                      + max (depth_formula A) (depth_formula B)"
        using depth_sub_le by simp
      also have "\<dots> \<le> sym_step_depth + max (depth_formula A) (depth_formula B)"
      proof -
        have "depth_formula t0
            \<in> insert 1 (depth_formula ` set (steps sym_base_proof))"
          using t0_in by simp
        hence "depth_formula t0 \<le> sym_step_depth"
          unfolding sym_step_depth_def using Max_ge[OF fin_sd] by blast
        thus ?thesis by simp
      qed
      also have "\<dots> \<le> ?dep_t" using si_dep_le by linarith
      finally show ?thesis .
    qed
  qed

  show ?thesis
    unfolding provable_balanced_iff_def
  proof (intro exI[where x = cb] conjI)
    show "valid_proof F cb" using valid_cb .
    show "assumptions cb = {}" using cb_asm .
    show "frege_proof.thesis cb = iff_form B A" using cb_thesis .
    show "length (steps cb) \<le> ?lines_t" using cb_lines .
    show "\<forall>t \<in> set (steps cb). len_formula t \<le> ?sz_t" using step_len .
    show "\<forall>t \<in> set (steps cb). depth_formula t \<le> ?dep_t" using step_depth .
  qed
qed

(*
  The case identities. Opening up the rebalanced diagrams of Lemma 5.1's
  Cases 1/2/3 leaves balance-trees over a fixed set of generic leaves; the two
  diagrams are then equivalent by a fixed propositional tautology. Cases 1 and
  2 share the reassociation identity (Case 2 is its mirror, via iff_sym);
  Case 3 is a six-leaf identity.
*)
subsection \<open>The case-one selector-reassociation identity\<close>

definition reassoc_atoms :: "string list" where
  "reassoc_atoms = fresh_atoms 5"

lemma reassoc_atoms_spec:
  "length reassoc_atoms = 5 \<and> distinct reassoc_atoms
   \<and> set reassoc_atoms \<inter> avoid_atoms = {}"
  unfolding reassoc_atoms_def using fresh_atoms_spec[of 5] by simp

definition reassoc_lhs :: "'c formula" where
  "reassoc_lhs =
     balance (Atom (reassoc_atoms ! 1)) (Atom (reassoc_atoms ! 0))
             (balance (Atom (reassoc_atoms ! 3)) (Atom (reassoc_atoms ! 2))
                      (Atom (reassoc_atoms ! 4)))"

definition reassoc_rhs :: "'c formula" where
  "reassoc_rhs =
     balance (balance (Atom (reassoc_atoms ! 1)) (Atom (reassoc_atoms ! 0))
                      (Atom (reassoc_atoms ! 3)))
             (balance (Atom (reassoc_atoms ! 1)) (Atom (reassoc_atoms ! 0))
                      (Atom (reassoc_atoms ! 2)))
             (Atom (reassoc_atoms ! 4))"

lemma reassoc_taut:
  "\<forall>val. eval (alphabet F) val (iff_form reassoc_lhs reassoc_rhs)"
proof (intro allI)
  fix val
  let ?ev = "eval (alphabet F) val"
  have lhs: "?ev reassoc_lhs
           = (if (if ?ev (Atom (reassoc_atoms ! 4))
                  then ?ev (Atom (reassoc_atoms ! 3))
                  else ?ev (Atom (reassoc_atoms ! 2)))
              then ?ev (Atom (reassoc_atoms ! 1))
              else ?ev (Atom (reassoc_atoms ! 0)))"
    unfolding reassoc_lhs_def by (simp only: balance_eval)
  have rhs: "?ev reassoc_rhs
           = (if ?ev (Atom (reassoc_atoms ! 4))
              then (if ?ev (Atom (reassoc_atoms ! 3))
                    then ?ev (Atom (reassoc_atoms ! 1))
                    else ?ev (Atom (reassoc_atoms ! 0)))
              else (if ?ev (Atom (reassoc_atoms ! 2))
                    then ?ev (Atom (reassoc_atoms ! 1))
                    else ?ev (Atom (reassoc_atoms ! 0))))"
    unfolding reassoc_rhs_def by (simp only: balance_eval)
  have "?ev reassoc_lhs = ?ev reassoc_rhs"
    unfolding lhs rhs by simp
  thus "eval (alphabet F) val (iff_form reassoc_lhs reassoc_rhs)"
    by (simp add: iff_form_eval)
qed

definition case_one_lines :: nat where
  "case_one_lines = length (steps (taut_proof (iff_form reassoc_lhs reassoc_rhs)))"

definition case_one_step_len :: nat where
  "case_one_step_len =
     Max (insert 1 (len_formula ` set (steps (taut_proof
            (iff_form reassoc_lhs reassoc_rhs)))))"

definition case_one_step_depth :: nat where
  "case_one_step_depth =
     Max (insert 1 (depth_formula ` set (steps (taut_proof
            (iff_form reassoc_lhs reassoc_rhs)))))"

lemma case_one:
  "provable_balanced_iff reassoc_lhs reassoc_rhs
     case_one_lines case_one_step_len case_one_step_depth"
  using iff_from_taut[OF reassoc_taut]
  unfolding case_one_lines_def case_one_step_len_def case_one_step_depth_def .

(*
  Case 1 of Lemma 5.1 (R a descendant of Q). Given the three recursive
  equivalences --- t(Q) \<leftrightarrow> rebalancing Q at s, and t(P_{R=b}) \<leftrightarrow>
  rebalancing P_{R=b} at the spira node, for b \<in> {True, False} --- the
  rebalancing equivalence t(P) \<leftrightarrow> rebalancing P pos is provable by a
  balanced no-assumption proof. The chain is

    t(P) = balance XT XF (t Q)
         \<leftrightarrow> balance XT XF (balance RT RF TR)          (balance_cong on the spira node)
         \<leftrightarrow> balance (balance XT XF RT) (balance XT XF RF) TR   (case_one reassociation)
         \<leftrightarrow> rebalancing P pos                          (balance_cong of the flipped IHs)

  chained by iff_trans. This lemma supplies the construction; the
  polynomial bound on its size is the separate L(n,m) recurrence.
*)
(*
  Line-count glue for Case 1: the constant overhead of the three-step chain
  (two iff_trans, two balance_cong, two iff_sym, three iff_refl, the case_one
  reassociation). Exposing it gives the recurrence lines = lQ + lT + lF + const,
  the additive shape poly_master_closure consumes.
*)
subsection \<open>Size and depth budgets for the combinators\<close>

definition case_one_glue_lines :: nat where
  "case_one_glue_lines = 3 * refl_lines + 2 * sym_lines + 2 * balance_cong_lines
     + case_one_lines + 2 * trans_lines"

lemma len_balance_le:
  "len_formula (balance X Y Z)
   \<le> len_formula custom_balancing
       * (len_formula X + len_formula Y + len_formula Z + 1)"
proof -
  let ?bsub = "\<lambda>v. if v = ''x'' then X else if v = ''y'' then Y
                   else if v = ''z'' then Z else Atom v"
  have unfold: "balance X Y Z = sub_formula ?bsub custom_balancing"
    by (simp add: Let_def)
  have idoff: "\<forall>v. v \<notin> {''x'', ''y'', ''z''} \<longrightarrow> ?bsub v = Atom v" by simp
  have lensub: "len_sub {''x'', ''y'', ''z''} ?bsub
              \<le> len_formula X + len_formula Y + len_formula Z + 1"
  proof -
    have "len_sub {''x'', ''y'', ''z''} ?bsub
        = max 1 (\<Sum>v\<in>{''x'', ''y'', ''z''}. len_formula (?bsub v))"
      unfolding len_sub_def by simp
    also have "(\<Sum>v\<in>{''x'', ''y'', ''z''}. len_formula (?bsub v))
             = len_formula X + len_formula Y + len_formula Z" by simp
    finally show ?thesis by simp
  qed
  have "len_formula (balance X Y Z)
      \<le> len_formula custom_balancing * len_sub {''x'', ''y'', ''z''} ?bsub"
    unfolding unfold by (rule sub_formula_bound[OF _ idoff]) simp
  also have "\<dots> \<le> len_formula custom_balancing
                  * (len_formula X + len_formula Y + len_formula Z + 1)"
    using lensub by (rule mult_le_mono2)
  finally show ?thesis .
qed

lemma depth_balance_le:
  "depth_formula (balance X Y Z)
   \<le> depth_formula custom_balancing
       + (depth_formula X + depth_formula Y + depth_formula Z + 1)"
proof -
  let ?bsub = "\<lambda>v. if v = ''x'' then X else if v = ''y'' then Y
                   else if v = ''z'' then Z else Atom v"
  have unfold: "balance X Y Z = sub_formula ?bsub custom_balancing"
    by (simp add: Let_def)
  have idoff: "\<forall>v. v \<notin> {''x'', ''y'', ''z''} \<longrightarrow> ?bsub v = Atom v" by simp
  have depthsub: "depth_sub {''x'', ''y'', ''z''} ?bsub
              \<le> depth_formula X + depth_formula Y + depth_formula Z + 1"
    unfolding depth_sub_def
  proof (rule Max.boundedI)
    show "finite (insert 1 ((\<lambda>v. depth_formula (?bsub v))
                             ` {''x'', ''y'', ''z''}))" by simp
    show "insert 1 ((\<lambda>v. depth_formula (?bsub v)) ` {''x'', ''y'', ''z''})
          \<noteq> {}" by simp
    fix e assume "e \<in> insert 1 ((\<lambda>v. depth_formula (?bsub v))
                                  ` {''x'', ''y'', ''z''})"
    thus "e \<le> depth_formula X + depth_formula Y + depth_formula Z + 1"
      by auto
  qed
  have "depth_formula (balance X Y Z)
      \<le> depth_formula custom_balancing + depth_sub {''x'', ''y'', ''z''} ?bsub"
    unfolding unfold by (rule sub_formula_depth_bound[OF _ idoff]) simp
  also have "\<dots> \<le> depth_formula custom_balancing
                  + (depth_formula X + depth_formula Y + depth_formula Z + 1)"
    using depthsub by simp
  finally show ?thesis .
qed

(*
  Budget lemmas shared by the three case constructions. Each construction
  defines opaque budgets cb/dcb, LS/DS and the two-step ladders NN1/NN,
  SDB1/SDB; these lemmas carry the definitional equations as hypotheses so a
  construction re-binds them via [OF cbdef NN1def] etc. A balance of three
  LS-bounded (resp. NN1-/DS-/SDB1-bounded) formulas fits the next budget.
*)
lemma balance_len_below:
  assumes cbdef: "cb = len_formula custom_balancing"
      and NN1def: "NN1 = cb * (3 * LS + 1)"
      and "len_formula A \<le> LS" and "len_formula B \<le> LS" and "len_formula C \<le> LS"
    shows "len_formula (balance A B C) \<le> NN1"
proof -
  have "len_formula (balance A B C)
        \<le> cb * (len_formula A + len_formula B + len_formula C + 1)"
    unfolding cbdef by (rule len_balance_le)
  also have "\<dots> \<le> cb * (3 * LS + 1)"
    using assms(3,4,5) by (intro mult_le_mono2) simp
  finally show ?thesis unfolding NN1def .
qed

lemma balance_len_below_step:
  assumes cbdef: "cb = len_formula custom_balancing"
      and NNdef: "NN = cb * (3 * NN1 + 1)"
      and "len_formula A \<le> NN1" and "len_formula B \<le> NN1" and "len_formula C \<le> NN1"
    shows "len_formula (balance A B C) \<le> NN"
proof -
  have "len_formula (balance A B C)
        \<le> cb * (len_formula A + len_formula B + len_formula C + 1)"
    unfolding cbdef by (rule len_balance_le)
  also have "\<dots> \<le> cb * (3 * NN1 + 1)"
    using assms(3,4,5) by (intro mult_le_mono2) simp
  finally show ?thesis unfolding NNdef .
qed

lemma balance_depth_below:
  assumes dcbdef: "dcb = depth_formula custom_balancing"
      and SDB1def: "SDB1 = dcb + 3 * DS + 1"
      and "depth_formula A \<le> DS" and "depth_formula B \<le> DS" and "depth_formula C \<le> DS"
    shows "depth_formula (balance A B C) \<le> SDB1"
proof -
  have "depth_formula (balance A B C)
        \<le> dcb + (depth_formula A + depth_formula B + depth_formula C + 1)"
    unfolding dcbdef by (rule depth_balance_le)
  also have "\<dots> \<le> dcb + (3 * DS + 1)" using assms(3,4,5) by simp
  finally show ?thesis unfolding SDB1def by simp
qed

lemma balance_depth_below_step:
  assumes dcbdef: "dcb = depth_formula custom_balancing"
      and SDBdef: "SDB = dcb + 3 * SDB1 + 1"
      and "depth_formula A \<le> SDB1" and "depth_formula B \<le> SDB1"
          "depth_formula C \<le> SDB1"
    shows "depth_formula (balance A B C) \<le> SDB"
proof -
  have "depth_formula (balance A B C)
        \<le> dcb + (depth_formula A + depth_formula B + depth_formula C + 1)"
    unfolding dcbdef by (rule depth_balance_le)
  also have "\<dots> \<le> dcb + (3 * SDB1 + 1)" using assms(3,4,5) by simp
  finally show ?thesis unfolding SDBdef by simp
qed

lemma NN1_linear:
  fixes cb LS :: nat
  assumes NN1def: "NN1 = cb * (3 * LS + 1)"
  shows "NN1 \<le> 3 * cb * (LS + 1)"
proof -
  have "NN1 = cb * (3 * LS + 1)" unfolding NN1def by simp
  also have "\<dots> \<le> cb * (3 * (LS + 1))" by (intro mult_le_mono2) simp
  also have "\<dots> = 3 * cb * (LS + 1)" by (simp add: algebra_simps)
  finally show ?thesis .
qed

lemma NN_linear:
  fixes cb LS :: nat
  assumes cb1: "(1::nat) \<le> cb"
      and NN1def: "NN1 = cb * (3 * LS + 1)"
      and NNdef: "NN = cb * (3 * NN1 + 1)"
  shows "NN \<le> 12 * (cb * cb) * (LS + 1)"
proof -
  have NN1_1: "1 \<le> NN1" unfolding NN1def using cb1 by simp
  have "NN = cb * (3 * NN1 + 1)" unfolding NNdef by simp
  also have "\<dots> \<le> cb * (4 * NN1)" using NN1_1 by (intro mult_le_mono2) simp
  also have "\<dots> = 4 * cb * NN1" by (simp add: algebra_simps)
  also have "\<dots> \<le> 4 * cb * (3 * cb * (LS + 1))"
    using NN1_linear[OF NN1def] by (rule mult_le_mono2)
  also have "\<dots> = 12 * (cb * cb) * (LS + 1)" by (simp add: algebra_simps)
  finally show ?thesis .
qed

(*
  Bounded combinators. iff_sym / balance_cong / iff_trans state their per-line
  size as a sum of step costs and their depth as a max; for the L(n,m) recurrence
  the constructions need a composable bound in which every glued formula's
  len / depth is replaced by single budgets N / DN. These wrappers do that
  weakening once, so a construction chains pre-bounded steps and never has to
  manipulate the raw cost expressions.
*)
lemma iff_sym_bnd:
  assumes a: "provable_balanced_iff A B l s d"
      and sS: "s \<le> S" and dD: "d \<le> D"
      and lp: "len_formula A + len_formula B \<le> SL"
      and pp: "max (depth_formula A) (depth_formula B) \<le> SD"
    shows "provable_balanced_iff B A (l + sym_lines)
             (S + sym_step_len * SL) (max D (sym_step_depth + SD))"
proof (rule provable_balanced_iff_weaken[OF iff_sym[OF a] order_refl _ _])
  have "sym_step_len * (len_formula A + len_formula B) \<le> sym_step_len * SL"
    by (rule mult_le_mono[OF order_refl lp])
  thus "s + sym_step_len * (len_formula A + len_formula B)
        \<le> S + sym_step_len * SL"
    using sS by linarith
  show "max d (sym_step_depth + max (depth_formula A) (depth_formula B))
        \<le> max D (sym_step_depth + SD)"
    by (rule max.boundedI[OF max.coboundedI1[OF dD]
              max.coboundedI2[OF add_left_mono[OF pp]]])
qed

lemma balance_cong_bnd:
  assumes a1: "provable_balanced_iff X X' lx sx dx"
      and a2: "provable_balanced_iff Y Y' ly sy dy"
      and a3: "provable_balanced_iff Z Z' lz sz dz"
      and sp: "sx + sy + sz \<le> S"
      and dp: "max dx (max dy dz) \<le> D"
      and lp: "len_formula X + len_formula X' + len_formula Y + len_formula Y'
               + len_formula Z + len_formula Z' \<le> SL"
      and pp: "max (depth_formula X) (max (depth_formula X')
                 (max (depth_formula Y) (max (depth_formula Y')
                   (max (depth_formula Z) (depth_formula Z'))))) \<le> SD"
    shows "provable_balanced_iff (balance X Y Z) (balance X' Y' Z')
             (lx + ly + lz + balance_cong_lines)
             (S + balance_cong_step_len * (6 * SL))
             (max D (balance_cong_step_depth + SD))"
proof (rule provable_balanced_iff_weaken
         [OF balance_cong[OF a1 a2 a3] order_refl _ _])
  have "balance_cong_step_len * (6 * (len_formula X + len_formula X'
          + len_formula Y + len_formula Y' + len_formula Z + len_formula Z'))
        \<le> balance_cong_step_len * (6 * SL)"
    by (rule mult_le_mono2[OF mult_le_mono2[OF lp]])
  thus "sx + sy + sz + balance_cong_step_len * (6 * (len_formula X + len_formula X'
          + len_formula Y + len_formula Y' + len_formula Z + len_formula Z'))
        \<le> S + balance_cong_step_len * (6 * SL)"
    using sp by linarith
  have dx: "dx \<le> D" and dy: "dy \<le> D" and dz: "dz \<le> D"
    using dp by linarith+
  show "max dx (max dy (max dz (balance_cong_step_depth
          + max (depth_formula X) (max (depth_formula X')
              (max (depth_formula Y) (max (depth_formula Y')
                (max (depth_formula Z) (depth_formula Z'))))))))
        \<le> max D (balance_cong_step_depth + SD)"
    by (intro max.boundedI max.coboundedI1[OF dx] max.coboundedI1[OF dy]
              max.coboundedI1[OF dz]
              max.coboundedI2[OF add_left_mono[OF pp]])
qed

lemma iff_trans_bnd:
  assumes a1: "provable_balanced_iff A B l1 s1 d1"
      and a2: "provable_balanced_iff B C l2 s2 d2"
      and dp: "max d1 d2 \<le> D"
      and lp: "len_formula A + len_formula B + len_formula C \<le> SL"
      and pp: "max (depth_formula A)
                 (max (depth_formula B) (depth_formula C)) \<le> SD"
    shows "provable_balanced_iff A C (l1 + l2 + trans_lines)
             (s1 + s2 + trans_step_len * SL)
             (max D (trans_step_depth + SD))"
proof (rule provable_balanced_iff_weaken
         [OF iff_trans[OF a1 a2] order_refl _ _])
  have "trans_step_len * (len_formula A + len_formula B + len_formula C)
        \<le> trans_step_len * SL"
    by (rule mult_le_mono[OF order_refl lp])
  thus "s1 + s2 + trans_step_len
          * (len_formula A + len_formula B + len_formula C)
        \<le> s1 + s2 + trans_step_len * SL"
    by linarith
  have d1: "d1 \<le> D" and d2: "d2 \<le> D" using dp by linarith+
  show "max d1 (max d2 (trans_step_depth
          + max (depth_formula A) (max (depth_formula B) (depth_formula C))))
        \<le> max D (trans_step_depth + SD)"
    by (intro max.boundedI max.coboundedI1[OF d1] max.coboundedI1[OF d2]
              max.coboundedI2[OF add_left_mono[OF pp]])
qed

(*
  Glue coefficients for the construction size / depth bounds. Every formula
  glued into a construction chain is a balance of spira_trans leaves; its size
  is linear, and its depth additive, in those leaves. These (generous) constants
  absorb the per-step costs so a construction can expose
  sz \<le> \<Sum>(IH sizes) + rebal_glue_coeff * (\<Sum> leaf sizes + 1) and the
  analogous max-composed depth bound.
*)
definition rebal_glue_coeff :: nat where
  "rebal_glue_coeff = 4096 * (len_formula custom_balancing + 1)
     * (len_formula custom_balancing + 1)
     * (refl_step_len + sym_step_len + trans_step_len + balance_cong_step_len
        + case_one_step_len + 1)"

definition rebal_dep_coeff :: nat where
  "rebal_dep_coeff = 4096 * (depth_formula custom_balancing + refl_step_depth
     + sym_step_depth + trans_step_depth + balance_cong_step_depth
     + case_one_step_depth + 1)"

\<comment> \<open>The two glue-cost envelopes shared by the three case constructions.
    glue_coeff_envelope is the size-coefficient core (a coefficient sum bounded
    by 72*S fits the 4096-form glue constant); dep_coeff_envelope is the depth
    core (a base depth K below DC, with the +9*DS slack, fits DC*(DS+1)). Each
    construction keeps its case-specific bound on the coefficient sum / base
    depth and the unfolding to rebal_glue_coeff(3) / rebal_dep_coeff(3), then
    applies the envelope.\<close>
lemma glue_coeff_envelope:
  fixes C S cb :: nat
  assumes "C \<le> 72 * S"
  shows "C * (12 * (cb * cb)) \<le> 4096 * ((cb + 1) * (cb + 1)) * S"
proof -
  have c2: "cb * cb \<le> (cb + 1) * (cb + 1)" by (intro mult_le_mono) simp_all
  have "C * (12 * (cb * cb)) \<le> (72 * S) * (12 * ((cb + 1) * (cb + 1)))"
    by (intro mult_le_mono assms mult_le_mono2 c2)
  also have "\<dots> = 864 * ((cb + 1) * (cb + 1)) * S" by (simp add: algebra_simps)
  also have "\<dots> \<le> 4096 * ((cb + 1) * (cb + 1)) * S" by (intro mult_le_mono1) simp
  finally show ?thesis .
qed

lemma dep_coeff_envelope:
  fixes DBX K DS DC :: nat
  assumes dbx: "DBX = K + 9 * DS" and aK: "K \<le> DC" and rdc9: "9 \<le> DC"
  shows "DBX \<le> DC * (DS + 1)"
proof -
  have "9 * DS \<le> DC * DS" using rdc9 by (rule mult_le_mono1)
  hence "DBX \<le> DC + DC * DS" using dbx aK by linarith
  thus ?thesis by (simp add: algebra_simps)
qed

\<comment> \<open>The selector-reassociation step shared by Cases 1 and 2.  Both instantiate
    the fixed identity reassoc_lhs \<leftrightarrow> reassoc_rhs at the same five generic atoms
    with their own five leaf formulas; the substitution and its size/depth budgets
    are identical, so they are factored here once over A0..A4.\<close>
subsection \<open>The shared selector-reassociation substitution\<close>

definition reassoc_sigma ::
  "'c formula \<Rightarrow> 'c formula \<Rightarrow> 'c formula \<Rightarrow> 'c formula \<Rightarrow> 'c formula
   \<Rightarrow> string \<Rightarrow> 'c formula" where
  "reassoc_sigma A0 A1 A2 A3 A4 =
     (\<lambda>v. case map_of (zip reassoc_atoms [A0, A1, A2, A3, A4]) v of
            None \<Rightarrow> Atom v | Some f \<Rightarrow> f)"

lemma reassoc_sigma_val:
  assumes "k < 5"
  shows "reassoc_sigma A0 A1 A2 A3 A4 (reassoc_atoms ! k) = [A0, A1, A2, A3, A4] ! k"
proof -
  have dist: "distinct reassoc_atoms" using reassoc_atoms_spec by simp
  have lveq: "length reassoc_atoms = length [A0, A1, A2, A3, A4]"
    using reassoc_atoms_spec by simp
  have "map_of (zip reassoc_atoms [A0, A1, A2, A3, A4]) (reassoc_atoms ! k)
        = Some ([A0, A1, A2, A3, A4] ! k)"
    using map_of_zip_nth_lookup[OF dist lveq] assms reassoc_atoms_spec by simp
  thus ?thesis unfolding reassoc_sigma_def by simp
qed

lemma reassoc_sigma_off:
  assumes "v \<notin> set reassoc_atoms"
  shows "reassoc_sigma A0 A1 A2 A3 A4 v = Atom v"
proof -
  have "map_of (zip reassoc_atoms [A0, A1, A2, A3, A4]) v = None"
    using assms by (rule map_of_zip_None_lookup)
  thus ?thesis unfolding reassoc_sigma_def by simp
qed

lemma reassoc_sigma_len_sub_le:
  assumes "len_formula A0 \<le> B" and "len_formula A1 \<le> B" and "len_formula A2 \<le> B"
      and "len_formula A3 \<le> B" and "len_formula A4 \<le> B" and "1 \<le> B"
    shows "len_sub (set reassoc_atoms) (reassoc_sigma A0 A1 A2 A3 A4) \<le> 5 * B"
proof -
  let ?sub = "reassoc_sigma A0 A1 A2 A3 A4"
  have dist: "distinct reassoc_atoms" using reassoc_atoms_spec by simp
  have len5: "length reassoc_atoms = 5" using reassoc_atoms_spec by simp
  have card5: "card (set reassoc_atoms) = 5" using distinct_card[OF dist] len5 by simp
  have bnd: "len_formula (?sub v) \<le> B" if "v \<in> set reassoc_atoms" for v
  proof -
    from that obtain k where k5: "k < 5" and vk: "reassoc_atoms ! k = v"
      using len5 by (auto simp: in_set_conv_nth)
    have e: "?sub v = [A0, A1, A2, A3, A4] ! k"
      unfolding vk[symmetric] by (rule reassoc_sigma_val[OF k5])
    consider "k = 0" | "k = 1" | "k = 2" | "k = 3" | "k = 4" using k5 by linarith
    thus ?thesis using e assms by cases simp_all
  qed
  have "(\<Sum>v\<in>set reassoc_atoms. len_formula (?sub v)) \<le> (\<Sum>v\<in>set reassoc_atoms. B)"
    by (rule sum_mono) (rule bnd)
  also have "\<dots> = 5 * B" using card5 by simp
  finally show ?thesis unfolding len_sub_def using assms(6) by simp
qed

lemma reassoc_sigma_depth_sub_le:
  assumes "depth_formula A0 \<le> B" and "depth_formula A1 \<le> B" and "depth_formula A2 \<le> B"
      and "depth_formula A3 \<le> B" and "depth_formula A4 \<le> B" and "1 \<le> B"
    shows "depth_sub (set reassoc_atoms) (reassoc_sigma A0 A1 A2 A3 A4) \<le> B"
proof -
  let ?sub = "reassoc_sigma A0 A1 A2 A3 A4"
  have len5: "length reassoc_atoms = 5" using reassoc_atoms_spec by simp
  have bnd: "depth_formula (?sub v) \<le> B" if "v \<in> set reassoc_atoms" for v
  proof -
    from that obtain k where k5: "k < 5" and vk: "reassoc_atoms ! k = v"
      using len5 by (auto simp: in_set_conv_nth)
    have e: "?sub v = [A0, A1, A2, A3, A4] ! k"
      unfolding vk[symmetric] by (rule reassoc_sigma_val[OF k5])
    consider "k = 0" | "k = 1" | "k = 2" | "k = 3" | "k = 4" using k5 by linarith
    thus ?thesis using e assms by cases simp_all
  qed
  show ?thesis unfolding depth_sub_def
  proof (rule Max.boundedI)
    show "finite (insert 1 ((\<lambda>v. depth_formula (?sub v)) ` set reassoc_atoms))" by simp
    show "insert 1 ((\<lambda>v. depth_formula (?sub v)) ` set reassoc_atoms) \<noteq> {}" by simp
    fix e assume "e \<in> insert 1 ((\<lambda>v. depth_formula (?sub v)) ` set reassoc_atoms)"
    thus "e \<le> B" using bnd assms(6) by auto
  qed
qed

lemma reassoc_subst_step:
  "provable_balanced_iff
     (balance A1 A0 (balance A3 A2 A4))
     (balance (balance A1 A0 A3) (balance A1 A0 A2) A4)
     case_one_lines
     (case_one_step_len * len_sub (set reassoc_atoms) (reassoc_sigma A0 A1 A2 A3 A4))
     (case_one_step_depth
        + depth_sub (set reassoc_atoms) (reassoc_sigma A0 A1 A2 A3 A4))"
proof -
  let ?sub = "reassoc_sigma A0 A1 A2 A3 A4"
  have finite_set: "finite (set reassoc_atoms)" by simp
  have ra_disj: "set reassoc_atoms \<inter> avoid_atoms = {}" using reassoc_atoms_spec by simp
  have sig_id: "\<forall>v. v \<notin> set reassoc_atoms \<longrightarrow> ?sub v = Atom v"
    using reassoc_sigma_off by blast
  note sig_conn = fresh_sub_conn[OF ra_disj sig_id]
  note sig_cb = fresh_sub_cb[OF ra_disj sig_id]
  have sv0: "?sub (reassoc_atoms ! 0) = A0" using reassoc_sigma_val[of 0] by simp
  have sv1: "?sub (reassoc_atoms ! 1) = A1" using reassoc_sigma_val[of 1] by simp
  have sv2: "?sub (reassoc_atoms ! 2) = A2" using reassoc_sigma_val[of 2] by simp
  have sv3: "?sub (reassoc_atoms ! 3) = A3" using reassoc_sigma_val[of 3] by simp
  have sv4: "?sub (reassoc_atoms ! 4) = A4" using reassoc_sigma_val[of 4] by simp
  have subL: "sub_formula ?sub reassoc_lhs = balance A1 A0 (balance A3 A2 A4)"
  proof -
    have inner: "sub_formula ?sub
                   (balance (Atom (reassoc_atoms ! 3)) (Atom (reassoc_atoms ! 2))
                            (Atom (reassoc_atoms ! 4)))
               = balance A3 A2 A4"
    proof -
      have "sub_formula ?sub
              (balance (Atom (reassoc_atoms ! 3)) (Atom (reassoc_atoms ! 2))
                       (Atom (reassoc_atoms ! 4)))
          = balance (sub_formula ?sub (Atom (reassoc_atoms ! 3)))
                    (sub_formula ?sub (Atom (reassoc_atoms ! 2)))
                    (sub_formula ?sub (Atom (reassoc_atoms ! 4)))"
        by (rule sub_formula_balance[OF sig_cb])
      thus ?thesis by (simp only: sub_formula.simps sv3 sv2 sv4)
    qed
    have "sub_formula ?sub reassoc_lhs
        = balance (sub_formula ?sub (Atom (reassoc_atoms ! 1)))
                  (sub_formula ?sub (Atom (reassoc_atoms ! 0)))
                  (sub_formula ?sub
                     (balance (Atom (reassoc_atoms ! 3)) (Atom (reassoc_atoms ! 2))
                              (Atom (reassoc_atoms ! 4))))"
      unfolding reassoc_lhs_def by (rule sub_formula_balance[OF sig_cb])
    thus ?thesis by (simp only: sub_formula.simps sv1 sv0 inner)
  qed
  have subR: "sub_formula ?sub reassoc_rhs
            = balance (balance A1 A0 A3) (balance A1 A0 A2) A4"
  proof -
    have inL: "sub_formula ?sub
                 (balance (Atom (reassoc_atoms ! 1)) (Atom (reassoc_atoms ! 0))
                          (Atom (reassoc_atoms ! 3)))
             = balance A1 A0 A3"
    proof -
      have "sub_formula ?sub
              (balance (Atom (reassoc_atoms ! 1)) (Atom (reassoc_atoms ! 0))
                       (Atom (reassoc_atoms ! 3)))
          = balance (sub_formula ?sub (Atom (reassoc_atoms ! 1)))
                    (sub_formula ?sub (Atom (reassoc_atoms ! 0)))
                    (sub_formula ?sub (Atom (reassoc_atoms ! 3)))"
        by (rule sub_formula_balance[OF sig_cb])
      thus ?thesis by (simp only: sub_formula.simps sv1 sv0 sv3)
    qed
    have inR: "sub_formula ?sub
                 (balance (Atom (reassoc_atoms ! 1)) (Atom (reassoc_atoms ! 0))
                          (Atom (reassoc_atoms ! 2)))
             = balance A1 A0 A2"
    proof -
      have "sub_formula ?sub
              (balance (Atom (reassoc_atoms ! 1)) (Atom (reassoc_atoms ! 0))
                       (Atom (reassoc_atoms ! 2)))
          = balance (sub_formula ?sub (Atom (reassoc_atoms ! 1)))
                    (sub_formula ?sub (Atom (reassoc_atoms ! 0)))
                    (sub_formula ?sub (Atom (reassoc_atoms ! 2)))"
        by (rule sub_formula_balance[OF sig_cb])
      thus ?thesis by (simp only: sub_formula.simps sv1 sv0 sv2)
    qed
    have "sub_formula ?sub reassoc_rhs
        = balance (sub_formula ?sub
                     (balance (Atom (reassoc_atoms ! 1)) (Atom (reassoc_atoms ! 0))
                              (Atom (reassoc_atoms ! 3))))
                  (sub_formula ?sub
                     (balance (Atom (reassoc_atoms ! 1)) (Atom (reassoc_atoms ! 0))
                              (Atom (reassoc_atoms ! 2))))
                  (sub_formula ?sub (Atom (reassoc_atoms ! 4)))"
      unfolding reassoc_rhs_def by (rule sub_formula_balance[OF sig_cb])
    thus ?thesis by (simp only: sub_formula.simps inL inR sv4)
  qed
  show ?thesis
    using provable_balanced_iff_subst[OF case_one finite_set sig_id sig_conn,
                                      unfolded subL subR] .
qed

subsection \<open>The case-one construction\<close>

lemma case_one_construction:
  assumes wfP: "formula_well_formed (alphabet F) P"
      and geP: "len_formula P \<ge> spira_threshold"
      and pos_eq: "pos = spiras_sel_position P @ s"
      and vp: "valid_position P pos"
      and IH_Q: "provable_balanced_iff
                   (spira_trans (subterm_at P (spiras_sel_position P)))
                   (rebalancing (subterm_at P (spiras_sel_position P)) s)
                   lQ szQ depQ"
      and IH_T: "provable_balanced_iff
                   (spira_trans (fix_at pos True P))
                   (rebalancing (fix_at pos True P) (spiras_sel_position P))
                   lT szT depT"
      and IH_F: "provable_balanced_iff
                   (spira_trans (fix_at pos False P))
                   (rebalancing (fix_at pos False P) (spiras_sel_position P))
                   lF szF depF"
    shows "\<exists> sz dep.
       provable_balanced_iff (spira_trans P) (rebalancing P pos)
         (lQ + lT + lF + case_one_glue_lines) sz dep
     \<and> sz \<le> szQ + szT + szF + rebal_glue_coeff
         * (len_formula (spira_trans (fix_at (spiras_sel_position P) True P))
            + len_formula (spira_trans (fix_at (spiras_sel_position P) False P))
            + len_formula (spira_trans (fix_at s True
                (subterm_at P (spiras_sel_position P))))
            + len_formula (spira_trans (fix_at s False
                (subterm_at P (spiras_sel_position P))))
            + len_formula (spira_trans (subterm_at P pos))
            + len_formula (spira_trans (subterm_at P (spiras_sel_position P)))
            + len_formula (spira_trans (fix_at pos True P))
            + len_formula (spira_trans (fix_at pos False P)) + 1)
     \<and> dep \<le> max depQ (max depT (max depF (rebal_dep_coeff
         * (depth_formula (spira_trans (fix_at (spiras_sel_position P) True P))
            + depth_formula (spira_trans (fix_at (spiras_sel_position P) False P))
            + depth_formula (spira_trans (fix_at s True
                (subterm_at P (spiras_sel_position P))))
            + depth_formula (spira_trans (fix_at s False
                (subterm_at P (spiras_sel_position P))))
            + depth_formula (spira_trans (subterm_at P pos))
            + depth_formula (spira_trans (subterm_at P (spiras_sel_position P)))
            + depth_formula (spira_trans (fix_at pos True P))
            + depth_formula (spira_trans (fix_at pos False P)) + 1))))"
proof -
  let ?q  = "spiras_sel_position P"
  let ?Q  = "subterm_at P ?q"
  let ?XT = "spira_trans (fix_at ?q True P)"
  let ?XF = "spira_trans (fix_at ?q False P)"
  let ?RT = "spira_trans (fix_at s True ?Q)"
  let ?RF = "spira_trans (fix_at s False ?Q)"
  let ?TR = "spira_trans (subterm_at P pos)"
  let ?sigma = "reassoc_sigma ?XF ?XT ?RF ?RT ?TR"

  \<comment> \<open>The position splits as q (the spira node) followed by s.\<close>
  have split: "valid_position P ?q \<and> valid_position ?Q s"
    using vp by (simp only: pos_eq valid_position_append)
  have vpq: "valid_position P ?q" using split by simp

  \<comment> \<open>spira_trans P opens at the spira node into a balance.\<close>
  have F2: "spira_trans P = balance ?XT ?XF (spira_trans ?Q)"
  proof -
    have "spira_trans P = rebalancing P ?q"
      using rebalancing_eq_spira_trans[OF wfP geP] by simp
    also have "\<dots> = balance ?XT ?XF (spira_trans ?Q)"
      unfolding rebalancing_def by simp
    finally show ?thesis .
  qed

  \<comment> \<open>rebalancing of Q at s; its inner leaf is t(R) = t(subterm_at P pos).\<close>
  have sub_eq: "subterm_at ?Q s = subterm_at P pos"
    using subterm_at_append[of P ?q s] pos_eq by simp
  have F3: "rebalancing ?Q s = balance ?RT ?RF ?TR"
    unfolding rebalancing_def using sub_eq by simp

  \<comment> \<open>case1_right_leaf: rebalancing the R-fixed P at the ancestor q.\<close>
  have F4T: "rebalancing (fix_at pos True P) ?q = balance ?XT ?XF ?RT"
    using case1_right_leaf[OF vpq, of s True] pos_eq by simp
  have F4F: "rebalancing (fix_at pos False P) ?q = balance ?XT ?XF ?RF"
    using case1_right_leaf[OF vpq, of s False] pos_eq by simp

  \<comment> \<open>rebalancing P pos opens at pos.\<close>
  have F5: "rebalancing P pos
          = balance (spira_trans (fix_at pos True P))
                    (spira_trans (fix_at pos False P)) ?TR"
    unfolding rebalancing_def by simp

  \<comment> \<open>The three recursive equivalences, rewritten through F3/F4.\<close>
  from IH_Q have IHQ:
    "provable_balanced_iff (spira_trans ?Q) (balance ?RT ?RF ?TR) lQ szQ depQ"
    by (simp only: F3[symmetric])
  from IH_T have IHT:
    "provable_balanced_iff (spira_trans (fix_at pos True P))
        (balance ?XT ?XF ?RT) lT szT depT"
    by (simp only: F4T[symmetric])
  from IH_F have IHF:
    "provable_balanced_iff (spira_trans (fix_at pos False P))
        (balance ?XT ?XF ?RF) lF szF depF"
    by (simp only: F4F[symmetric])

  \<comment> \<open>Uniform size / depth budgets for the glued formulas. Every glued
      formula is a balance of spira_trans leaves, so its len / depth is a fixed
      multiple of, resp. an affine function of, the leaf-size / depth sums.\<close>
  define cb where cbdef: "cb = len_formula custom_balancing"
  define dcb where dcbdef: "dcb = depth_formula custom_balancing"
  have cb1: "(1::nat) \<le> cb" unfolding cbdef by (rule len_formula_positive)
  define LS where LSdef: "LS = len_formula ?XT + len_formula ?XF
     + len_formula ?RT + len_formula ?RF + len_formula ?TR
     + len_formula (spira_trans ?Q)
     + len_formula (spira_trans (fix_at pos True P))
     + len_formula (spira_trans (fix_at pos False P))"
  define DS where DSdef: "DS = depth_formula ?XT + depth_formula ?XF
     + depth_formula ?RT + depth_formula ?RF + depth_formula ?TR
     + depth_formula (spira_trans ?Q)
     + depth_formula (spira_trans (fix_at pos True P))
     + depth_formula (spira_trans (fix_at pos False P))"
  define NN1 where NN1def: "NN1 = cb * (3 * LS + 1)"
  define NN where NNdef: "NN = cb * (3 * NN1 + 1)"
  define SDB1 where SDB1def: "SDB1 = dcb + 3 * DS + 1"
  define SDB where SDBdef: "SDB = dcb + 3 * SDB1 + 1"
  define DBX where DBXdef: "DBX = refl_step_depth + sym_step_depth
       + trans_step_depth + balance_cong_step_depth + case_one_step_depth + SDB"
  define DB where DBdef: "DB = max depQ (max depT (max depF DBX))"
  have DBX_DB: "DBX \<le> DB" unfolding DBdef by (simp add: le_max_iff_disj)
  have depQ_DB: "depQ \<le> DB" and depT_DB: "depT \<le> DB"
   and depF_DB: "depF \<le> DB"
    unfolding DBdef by (simp_all add: le_max_iff_disj)

  \<comment> \<open>The eight spira_trans leaves are summands of LS / DS.\<close>
  have lXT: "len_formula ?XT \<le> LS" and lXF: "len_formula ?XF \<le> LS"
   and lRT: "len_formula ?RT \<le> LS" and lRF: "len_formula ?RF \<le> LS"
   and lTR: "len_formula ?TR \<le> LS"
   and lQ': "len_formula (spira_trans ?Q) \<le> LS"
   and lPT: "len_formula (spira_trans (fix_at pos True P)) \<le> LS"
   and lPF: "len_formula (spira_trans (fix_at pos False P)) \<le> LS"
    unfolding LSdef by simp_all
  have pXT: "depth_formula ?XT \<le> DS" and pXF: "depth_formula ?XF \<le> DS"
   and pRT: "depth_formula ?RT \<le> DS" and pRF: "depth_formula ?RF \<le> DS"
   and pTR: "depth_formula ?TR \<le> DS"
   and pQ': "depth_formula (spira_trans ?Q) \<le> DS"
   and pPT: "depth_formula (spira_trans (fix_at pos True P)) \<le> DS"
   and pPF: "depth_formula (spira_trans (fix_at pos False P)) \<le> DS"
    unfolding DSdef by simp_all
  have LS_NN1: "LS \<le> NN1" unfolding NN1def using cb1
    by (simp add: add.commute trans_le_add2 mult.commute)
  have NN1_NN: "NN1 \<le> NN" unfolding NNdef using cb1
    by (simp add: add.commute trans_le_add2 mult.commute)

  \<comment> \<open>A balance of three LS-bounded formulas is NN1-bounded; of three
      NN1-bounded formulas, NN-bounded.  Depth: SDB1 / SDB.\<close>
  note balNN1 = balance_len_below[OF cbdef NN1def]
  note balNN = balance_len_below_step[OF cbdef NNdef]
  note dbalSDB1 = balance_depth_below[OF dcbdef SDB1def]
  note dbalSDB = balance_depth_below_step[OF dcbdef SDBdef]

  have LS1: "1 \<le> LS" unfolding LSdef using len_formula_positive[of ?XT] by simp

  \<comment> \<open>Size / depth of every glued formula, against the budgets NN / SDB.\<close>
  have lP: "len_formula (spira_trans P) \<le> NN1"
    using balNN1[OF lXT lXF lQ'] F2 by simp
  have lreb: "len_formula (rebalancing P pos) \<le> NN1"
    using balNN1[OF lPT lPF lTR] F5 by simp
  have lRTRF: "len_formula (balance ?RT ?RF ?TR) \<le> NN1"
    by (rule balNN1[OF lRT lRF lTR])
  have lXTRT: "len_formula (balance ?XT ?XF ?RT) \<le> NN1"
    by (rule balNN1[OF lXT lXF lRT])
  have lXTRF: "len_formula (balance ?XT ?XF ?RF) \<le> NN1"
    by (rule balNN1[OF lXT lXF lRF])
  have lM1: "len_formula (balance ?XT ?XF (balance ?RT ?RF ?TR)) \<le> NN"
    by (rule balNN[OF le_trans[OF lXT LS_NN1] le_trans[OF lXF LS_NN1] lRTRF])
  have lM2: "len_formula (balance (balance ?XT ?XF ?RT)
                                  (balance ?XT ?XF ?RF) ?TR) \<le> NN"
    by (rule balNN[OF lXTRT lXTRF le_trans[OF lTR LS_NN1]])
  have pP: "depth_formula (spira_trans P) \<le> SDB1"
    using dbalSDB1[OF pXT pXF pQ'] F2 by simp
  have preb: "depth_formula (rebalancing P pos) \<le> SDB1"
    using dbalSDB1[OF pPT pPF pTR] F5 by simp
  have pRTRF: "depth_formula (balance ?RT ?RF ?TR) \<le> SDB1"
    by (rule dbalSDB1[OF pRT pRF pTR])
  have pXTRT: "depth_formula (balance ?XT ?XF ?RT) \<le> SDB1"
    by (rule dbalSDB1[OF pXT pXF pRT])
  have pXTRF: "depth_formula (balance ?XT ?XF ?RF) \<le> SDB1"
    by (rule dbalSDB1[OF pXT pXF pRF])
  have SDB1_SDB: "SDB1 \<le> SDB" unfolding SDBdef by simp
  have DS_SDB1: "DS \<le> SDB1" unfolding SDB1def by simp
  have pM1: "depth_formula (balance ?XT ?XF (balance ?RT ?RF ?TR)) \<le> SDB"
    by (rule dbalSDB[OF le_trans[OF pXT DS_SDB1] le_trans[OF pXF DS_SDB1] pRTRF])
  have pM2: "depth_formula (balance (balance ?XT ?XF ?RT)
                                    (balance ?XT ?XF ?RF) ?TR) \<le> SDB"
    by (rule dbalSDB[OF pXTRT pXTRF le_trans[OF pTR DS_SDB1]])

  \<comment> \<open>Substitution-step budgets via the shared reassoc_sigma helpers.\<close>
  have DS1: "1 \<le> DS"
    unfolding DSdef using depth_formula_ge_1[of ?XT] by linarith
  have lsub: "len_sub (set reassoc_atoms) ?sigma \<le> 5 * LS"
    by (rule reassoc_sigma_len_sub_le[OF lXF lXT lRF lRT lTR LS1])
  have dsub: "depth_sub (set reassoc_atoms) ?sigma \<le> DS"
    by (rule reassoc_sigma_depth_sub_le[OF pXF pXT pRF pRT pTR DS1])

  \<comment> \<open>NN / SDB bounds for every glued formula.\<close>
  have LS_NN: "LS \<le> NN" using LS_NN1 NN1_NN by simp
  note leafN = le_trans[OF lXT LS_NN] le_trans[OF lXF LS_NN]
               le_trans[OF lRT LS_NN] le_trans[OF lRF LS_NN]
               le_trans[OF lTR LS_NN] le_trans[OF lQ' LS_NN]
               le_trans[OF lPT LS_NN] le_trans[OF lPF LS_NN]
  note balN = le_trans[OF lRTRF NN1_NN] le_trans[OF lXTRT NN1_NN]
              le_trans[OF lXTRF NN1_NN] le_trans[OF lP NN1_NN]
              le_trans[OF lreb NN1_NN] lM1 lM2
  note leafD = le_trans[OF pXT DS_SDB1] le_trans[OF pXF DS_SDB1]
               le_trans[OF pRT DS_SDB1] le_trans[OF pRF DS_SDB1]
               le_trans[OF pTR DS_SDB1] le_trans[OF pQ' DS_SDB1]
               le_trans[OF pPT DS_SDB1] le_trans[OF pPF DS_SDB1]
  have DS_SDB: "DS \<le> SDB" using DS_SDB1 SDB1_SDB by simp
  note SDleafSDB = le_trans[OF pXT DS_SDB] le_trans[OF pXF DS_SDB]
                   le_trans[OF pRT DS_SDB] le_trans[OF pRF DS_SDB]
                   le_trans[OF pTR DS_SDB] le_trans[OF pQ' DS_SDB]
                   le_trans[OF pPT DS_SDB] le_trans[OF pPF DS_SDB]

  \<comment> \<open>Glue depths sit below DBX, hence below DB.\<close>
  have AX1: "refl_step_depth + depth_formula ?XT \<le> DBX"
    unfolding DBXdef using leafD(1) SDB1_SDB by linarith
  have AX2: "refl_step_depth + depth_formula ?XF \<le> DBX"
    unfolding DBXdef using leafD(2) SDB1_SDB by linarith
  have AX5: "refl_step_depth + depth_formula ?TR \<le> DBX"
    unfolding DBXdef using leafD(5) SDB1_SDB by linarith
  have symX: "sym_step_depth + SDB \<le> DBX" unfolding DBXdef by linarith
  have bcsdX: "balance_cong_step_depth + SDB \<le> DBX" unfolding DBXdef by linarith
  have transX: "trans_step_depth + SDB \<le> DBX" unfolding DBXdef by linarith

  \<comment> \<open>Step 1: the t(P) opening, via balance_cong on the spira node.\<close>
  have sp1: "refl_step_len * len_formula ?XT
           + refl_step_len * len_formula ?XF + szQ
           \<le> refl_step_len * NN + refl_step_len * NN + szQ"
    using mult_le_mono2[OF leafN(1), of refl_step_len]
          mult_le_mono2[OF leafN(2), of refl_step_len] by linarith
  have dp1: "max (refl_step_depth + depth_formula ?XT)
               (max (refl_step_depth + depth_formula ?XF) depQ) \<le> DB"
    by (intro max.boundedI le_trans[OF AX1 DBX_DB]
              le_trans[OF AX2 DBX_DB] depQ_DB)
  have lp1: "len_formula ?XT + len_formula ?XT + len_formula ?XF
           + len_formula ?XF + len_formula (spira_trans ?Q)
           + len_formula (balance ?RT ?RF ?TR) \<le> 6 * NN"
    using leafN(1) leafN(2) leafN(6) balN(1) by linarith
  have pp1: "max (depth_formula ?XT) (max (depth_formula ?XT)
               (max (depth_formula ?XF) (max (depth_formula ?XF)
                 (max (depth_formula (spira_trans ?Q))
                   (depth_formula (balance ?RT ?RF ?TR)))))) \<le> SDB"
    using SDleafSDB le_trans[OF pRTRF SDB1_SDB]
    by (intro max.boundedI) simp_all
  note step1 = balance_cong_bnd[OF iff_refl[where A = "?XT"]
      iff_refl[where A = "?XF"] IHQ sp1 dp1 lp1 pp1, folded F2]

  \<comment> \<open>Step 3: the rebalancing P pos folding, via balance_cong on the IHs.\<close>
  have lpT: "len_formula (spira_trans (fix_at pos True P))
           + len_formula (balance ?XT ?XF ?RT) \<le> 2 * NN"
    using leafN(7) balN(2) by linarith
  have ppT: "max (depth_formula (spira_trans (fix_at pos True P)))
               (depth_formula (balance ?XT ?XF ?RT)) \<le> SDB"
    using SDleafSDB(7) le_trans[OF pXTRT SDB1_SDB]
    by (intro max.boundedI) simp_all
  have lpF: "len_formula (spira_trans (fix_at pos False P))
           + len_formula (balance ?XT ?XF ?RF) \<le> 2 * NN"
    using leafN(8) balN(3) by linarith
  have ppF: "max (depth_formula (spira_trans (fix_at pos False P)))
               (depth_formula (balance ?XT ?XF ?RF)) \<le> SDB"
    using SDleafSDB(8) le_trans[OF pXTRF SDB1_SDB]
    by (intro max.boundedI) simp_all
  note isT = iff_sym_bnd[OF IHT order_refl order_refl lpT ppT]
  note isF = iff_sym_bnd[OF IHF order_refl order_refl lpF ppF]
  have sp3: "(szT + sym_step_len * (2 * NN)) + (szF + sym_step_len * (2 * NN))
           + refl_step_len * len_formula ?TR
           \<le> (szT + sym_step_len * (2 * NN))
              + (szF + sym_step_len * (2 * NN)) + refl_step_len * NN"
    using mult_le_mono2[OF leafN(5), of refl_step_len] by linarith
  have dp3: "max (max depT (sym_step_depth + SDB))
               (max (max depF (sym_step_depth + SDB))
                 (refl_step_depth + depth_formula ?TR)) \<le> DB"
    by (intro max.boundedI depT_DB le_trans[OF symX DBX_DB] depF_DB
              le_trans[OF symX DBX_DB] le_trans[OF AX5 DBX_DB])
  have lp3: "len_formula (balance ?XT ?XF ?RT)
           + len_formula (spira_trans (fix_at pos True P))
           + len_formula (balance ?XT ?XF ?RF)
           + len_formula (spira_trans (fix_at pos False P))
           + len_formula ?TR + len_formula ?TR \<le> 6 * NN"
    using leafN(5) leafN(7) leafN(8) balN(2) balN(3) by linarith
  have pp3: "max (depth_formula (balance ?XT ?XF ?RT))
               (max (depth_formula (spira_trans (fix_at pos True P)))
                 (max (depth_formula (balance ?XT ?XF ?RF))
                   (max (depth_formula (spira_trans (fix_at pos False P)))
                     (max (depth_formula ?TR)
                       (depth_formula ?TR))))) \<le> SDB"
    using SDleafSDB le_trans[OF pXTRT SDB1_SDB] le_trans[OF pXTRF SDB1_SDB]
    by (intro max.boundedI) simp_all
  note step3 = balance_cong_bnd[OF isT isF iff_refl[where A = "?TR"]
      sp3 dp3 lp3 pp3, folded F5]

  \<comment> \<open>Step 2: the reassociation, with len_sub bounded by 5 * LS.\<close>
  have sz2: "case_one_step_len * len_sub (set reassoc_atoms) ?sigma
           \<le> case_one_step_len * (5 * NN)"
  proof -
    have "len_sub (set reassoc_atoms) ?sigma \<le> 5 * NN"
      using lsub LS_NN by simp
    thus ?thesis by (rule mult_le_mono2)
  qed
  have dep2X: "case_one_step_depth + depth_sub (set reassoc_atoms) ?sigma \<le> DBX"
    unfolding DBXdef using dsub DS_SDB by linarith
  have dep2: "case_one_step_depth + depth_sub (set reassoc_atoms) ?sigma \<le> DB"
    by (rule le_trans[OF dep2X DBX_DB])
  note step2 = reassoc_subst_step[of ?XT ?XF ?RT ?RF ?TR]
  note step2' = provable_balanced_iff_weaken[OF step2 order_refl sz2 dep2]

  \<comment> \<open>Composition by iff_trans_bnd.\<close>
  have dpA: "max (max DB (balance_cong_step_depth + SDB)) DB \<le> DB"
    by (intro max.boundedI order_refl le_trans[OF bcsdX DBX_DB])
  have lpA: "len_formula (spira_trans P)
           + len_formula (balance ?XT ?XF (balance ?RT ?RF ?TR))
           + len_formula (balance (balance ?XT ?XF ?RT)
                                  (balance ?XT ?XF ?RF) ?TR) \<le> 3 * NN"
    using balN(4) lM1 lM2 by linarith
  have ppA: "max (depth_formula (spira_trans P))
               (max (depth_formula (balance ?XT ?XF (balance ?RT ?RF ?TR)))
                 (depth_formula (balance (balance ?XT ?XF ?RT)
                                         (balance ?XT ?XF ?RF) ?TR))) \<le> SDB"
    using le_trans[OF pP SDB1_SDB] pM1 pM2
    by (intro max.boundedI) simp_all
  note inner = iff_trans_bnd[OF step1 step2' dpA lpA ppA]
  have dpB: "max (max DB (trans_step_depth + SDB))
               (max DB (balance_cong_step_depth + SDB)) \<le> DB"
    by (intro max.boundedI order_refl le_trans[OF transX DBX_DB]
              le_trans[OF bcsdX DBX_DB])
  have lpB: "len_formula (spira_trans P)
           + len_formula (balance (balance ?XT ?XF ?RT)
                                  (balance ?XT ?XF ?RF) ?TR)
           + len_formula (rebalancing P pos) \<le> 3 * NN"
    using balN(4) lM2 balN(5) by linarith
  have ppB: "max (depth_formula (spira_trans P))
               (max (depth_formula (balance (balance ?XT ?XF ?RT)
                                            (balance ?XT ?XF ?RF) ?TR))
                 (depth_formula (rebalancing P pos))) \<le> SDB"
    using le_trans[OF pP SDB1_SDB] pM2 le_trans[OF preb SDB1_SDB]
    by (intro max.boundedI) simp_all
  note chain = iff_trans_bnd[OF inner step3 dpB lpB ppB]

  \<comment> \<open>The glue size sums to at most rebal_glue_coeff * (LS + 1).\<close>
  note NN1_lin = NN1_linear[OF NN1def]
  note NN_lin = NN_linear[OF cb1 NN1def NNdef]
  have cgc: "(3 * refl_step_len + 72 * balance_cong_step_len
              + 5 * case_one_step_len + 4 * sym_step_len + 6 * trans_step_len)
             * (12 * (cb * cb)) \<le> rebal_glue_coeff"
  proof -
    let ?S = "refl_step_len + sym_step_len + trans_step_len
              + balance_cong_step_len + case_one_step_len + 1"
    have c1: "3 * refl_step_len + 72 * balance_cong_step_len
              + 5 * case_one_step_len + 4 * sym_step_len + 6 * trans_step_len
              \<le> 72 * ?S" by simp
    have "(3 * refl_step_len + 72 * balance_cong_step_len
            + 5 * case_one_step_len + 4 * sym_step_len + 6 * trans_step_len)
          * (12 * (cb * cb))
          \<le> 4096 * ((cb + 1) * (cb + 1)) * ?S"
      by (rule glue_coeff_envelope[OF c1])
    also have "\<dots> = rebal_glue_coeff"
      unfolding rebal_glue_coeff_def cbdef by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  have glue_le: "refl_step_len * NN + refl_step_len * NN
       + balance_cong_step_len * (6 * (6 * NN)) + case_one_step_len * (5 * NN)
       + sym_step_len * (2 * NN) + sym_step_len * (2 * NN) + refl_step_len * NN
       + balance_cong_step_len * (6 * (6 * NN)) + trans_step_len * (3 * NN)
       + trans_step_len * (3 * NN)
       \<le> rebal_glue_coeff * (LS + 1)"
  proof -
    let ?C = "3 * refl_step_len + 72 * balance_cong_step_len
              + 5 * case_one_step_len + 4 * sym_step_len + 6 * trans_step_len"
    have eq: "refl_step_len * NN + refl_step_len * NN
       + balance_cong_step_len * (6 * (6 * NN)) + case_one_step_len * (5 * NN)
       + sym_step_len * (2 * NN) + sym_step_len * (2 * NN) + refl_step_len * NN
       + balance_cong_step_len * (6 * (6 * NN)) + trans_step_len * (3 * NN)
       + trans_step_len * (3 * NN) = ?C * NN"
      by (simp add: algebra_simps)
    have "?C * NN \<le> ?C * (12 * (cb * cb) * (LS + 1))"
      using NN_lin by (rule mult_le_mono2)
    also have "\<dots> = (?C * (12 * (cb * cb))) * (LS + 1)"
      by (simp add: algebra_simps)
    also have "\<dots> \<le> rebal_glue_coeff * (LS + 1)"
      using cgc by (rule mult_le_mono1)
    finally show ?thesis unfolding eq .
  qed

  \<comment> \<open>The depth glue: DBX is below the rebal_dep_coeff envelope.\<close>
  have DBX_env: "DBX \<le> rebal_dep_coeff * (DS + 1)"
  proof -
    have rdc9: "9 \<le> rebal_dep_coeff"
    proof -
      have "(9::nat) \<le> 4096 * depth_formula custom_balancing
            + 4096 * refl_step_depth + 4096 * sym_step_depth
            + 4096 * trans_step_depth + 4096 * balance_cong_step_depth
            + 4096 * case_one_step_depth + 4096" by linarith
      also have "\<dots> = rebal_dep_coeff"
        unfolding rebal_dep_coeff_def by (simp add: algebra_simps)
      finally show ?thesis .
    qed
    have a: "refl_step_depth + sym_step_depth + trans_step_depth
             + balance_cong_step_depth + case_one_step_depth + 4 * dcb + 4
             \<le> rebal_dep_coeff"
    proof -
      have "refl_step_depth + sym_step_depth + trans_step_depth
            + balance_cong_step_depth + case_one_step_depth + 4 * dcb + 4
            \<le> 4096 * dcb + 4096 * refl_step_depth + 4096 * sym_step_depth
              + 4096 * trans_step_depth + 4096 * balance_cong_step_depth
              + 4096 * case_one_step_depth + 4096" by linarith
      also have "\<dots> = rebal_dep_coeff"
        unfolding rebal_dep_coeff_def dcbdef by (simp add: algebra_simps)
      finally show ?thesis .
    qed
    have dbx: "DBX = (refl_step_depth + sym_step_depth + trans_step_depth
             + balance_cong_step_depth + case_one_step_depth + 4 * dcb + 4)
             + 9 * DS"
      unfolding DBXdef SDBdef SDB1def by simp
    show ?thesis by (rule dep_coeff_envelope[OF dbx a rdc9])
  qed
  have DB_le: "DB \<le> max depQ (max depT (max depF (rebal_dep_coeff * (DS + 1))))"
    unfolding DBdef by (intro max.mono order_refl DBX_env)
  have chain_dep_le: "max DB (trans_step_depth + SDB)
        \<le> max depQ (max depT (max depF (rebal_dep_coeff * (DS + 1))))"
  proof (rule max.boundedI[OF DB_le])
    have "trans_step_depth + SDB \<le> rebal_dep_coeff * (DS + 1)"
      using transX DBX_env by (rule le_trans)
    thus "trans_step_depth + SDB
          \<le> max depQ (max depT (max depF (rebal_dep_coeff * (DS + 1))))"
      by (simp add: le_max_iff_disj)
  qed

  \<comment> \<open>The sz glue: chain's per-line size budget, regrouped as
      szQ + szT + szF plus the glue sum bounded by glue_le.\<close>
  have sz_le: "refl_step_len * NN + refl_step_len * NN + szQ
       + balance_cong_step_len * (6 * (6 * NN)) + case_one_step_len * (5 * NN)
       + trans_step_len * (3 * NN)
       + (szT + sym_step_len * (2 * NN) + (szF + sym_step_len * (2 * NN))
          + refl_step_len * NN + balance_cong_step_len * (6 * (6 * NN)))
       + trans_step_len * (3 * NN)
       \<le> szQ + szT + szF + rebal_glue_coeff * (LS + 1)"
  proof -
    have "refl_step_len * NN + refl_step_len * NN + szQ
       + balance_cong_step_len * (6 * (6 * NN)) + case_one_step_len * (5 * NN)
       + trans_step_len * (3 * NN)
       + (szT + sym_step_len * (2 * NN) + (szF + sym_step_len * (2 * NN))
          + refl_step_len * NN + balance_cong_step_len * (6 * (6 * NN)))
       + trans_step_len * (3 * NN)
       = szQ + szT + szF
         + (refl_step_len * NN + refl_step_len * NN
            + balance_cong_step_len * (6 * (6 * NN))
            + case_one_step_len * (5 * NN) + sym_step_len * (2 * NN)
            + sym_step_len * (2 * NN) + refl_step_len * NN
            + balance_cong_step_len * (6 * (6 * NN)) + trans_step_len * (3 * NN)
            + trans_step_len * (3 * NN))"
      by (simp add: algebra_simps)
    also have "\<dots> \<le> szQ + szT + szF + rebal_glue_coeff * (LS + 1)"
      by (rule add_left_mono[OF glue_le])
    finally show ?thesis .
  qed

  show ?thesis
  proof (rule exI[where x = "szQ + szT + szF + rebal_glue_coeff * (LS + 1)"],
         rule exI[where x = "max depQ (max depT (max depF
                   (rebal_dep_coeff * (DS + 1))))"],
         intro conjI)
    show "provable_balanced_iff (spira_trans P) (rebalancing P pos)
            (lQ + lT + lF + case_one_glue_lines)
            (szQ + szT + szF + rebal_glue_coeff * (LS + 1))
            (max depQ (max depT (max depF (rebal_dep_coeff * (DS + 1)))))"
      \<comment> \<open>The line bound is an arithmetic identity; sz and dep are the
          structured facts sz_le and chain_dep_le.\<close>
      apply (rule provable_balanced_iff_weaken[OF chain])
        apply (simp add: case_one_glue_lines_def)
       apply (rule sz_le)
      apply (rule chain_dep_le)
      done
  next
    show "szQ + szT + szF + rebal_glue_coeff * (LS + 1)
          \<le> szQ + szT + szF + rebal_glue_coeff
              * (len_formula ?XT + len_formula ?XF + len_formula ?RT
                 + len_formula ?RF + len_formula ?TR
                 + len_formula (spira_trans ?Q)
                 + len_formula (spira_trans (fix_at pos True P))
                 + len_formula (spira_trans (fix_at pos False P)) + 1)"
      unfolding LSdef by simp
  next
    show "max depQ (max depT (max depF (rebal_dep_coeff * (DS + 1))))
          \<le> max depQ (max depT (max depF (rebal_dep_coeff
              * (depth_formula ?XT + depth_formula ?XF + depth_formula ?RT
                 + depth_formula ?RF + depth_formula ?TR
                 + depth_formula (spira_trans ?Q)
                 + depth_formula (spira_trans (fix_at pos True P))
                 + depth_formula (spira_trans (fix_at pos False P)) + 1))))"
      unfolding DSdef by simp
  qed
qed

(*
  Case 2 of Lemma 5.1 (Q a descendant of R). The spira node Q sits inside the
  rebalancing target R. Given the recursive equivalences --- t(P_{Q=b}) \<leftrightarrow>
  rebalancing P_{Q=b} at pos, for b \<in> {True, False}, and t(R) \<leftrightarrow>
  rebalancing R at s --- the rebalancing equivalence is provable. The chain
  mirrors Case 1 but runs the reassociation backwards (iff_sym of case_one):

    t(P) = balance QT QF (t Q)
         \<leftrightarrow> balance (balance PRT PRF RsT) (balance PRT PRF RsF) (t Q)  (balance_cong, IHs at Q)
         \<leftrightarrow> balance PRT PRF (balance RsT RsF (t Q))                  (case_one reversed)
         \<leftrightarrow> rebalancing P pos                                       (balance_cong, IH at R)
*)
subsection \<open>The case-two construction\<close>

definition case_two_glue_lines :: nat where
  "case_two_glue_lines = 3 * refl_lines + 2 * sym_lines + 2 * balance_cong_lines
     + case_one_lines + 2 * trans_lines"

lemma case_two_construction:
  assumes wfP: "formula_well_formed (alphabet F) P"
      and geP: "len_formula P \<ge> spira_threshold"
      and pos_eq2: "spiras_sel_position P = pos @ s"
      and vp: "valid_position P pos"
      and IH_T: "provable_balanced_iff
                   (spira_trans (fix_at (spiras_sel_position P) True P))
                   (rebalancing (fix_at (spiras_sel_position P) True P) pos)
                   lT szT depT"
      and IH_F: "provable_balanced_iff
                   (spira_trans (fix_at (spiras_sel_position P) False P))
                   (rebalancing (fix_at (spiras_sel_position P) False P) pos)
                   lF szF depF"
      and IH_R: "provable_balanced_iff
                   (spira_trans (subterm_at P pos))
                   (rebalancing (subterm_at P pos) s)
                   lR szR depR"
    shows "\<exists> sz dep.
       provable_balanced_iff (spira_trans P) (rebalancing P pos)
         (lT + lF + lR + case_two_glue_lines) sz dep
     \<and> sz \<le> szT + szF + szR + rebal_glue_coeff
         * (len_formula (spira_trans (fix_at (spiras_sel_position P) True P))
            + len_formula (spira_trans (fix_at (spiras_sel_position P) False P))
            + len_formula (spira_trans (fix_at pos True P))
            + len_formula (spira_trans (fix_at pos False P))
            + len_formula (spira_trans (fix_at s True (subterm_at P pos)))
            + len_formula (spira_trans (fix_at s False (subterm_at P pos)))
            + len_formula (spira_trans (subterm_at P (spiras_sel_position P)))
            + len_formula (spira_trans (subterm_at P pos)) + 1)
     \<and> dep \<le> max depT (max depF (max depR (rebal_dep_coeff
         * (depth_formula (spira_trans (fix_at (spiras_sel_position P) True P))
            + depth_formula (spira_trans (fix_at (spiras_sel_position P) False P))
            + depth_formula (spira_trans (fix_at pos True P))
            + depth_formula (spira_trans (fix_at pos False P))
            + depth_formula (spira_trans (fix_at s True (subterm_at P pos)))
            + depth_formula (spira_trans (fix_at s False (subterm_at P pos)))
            + depth_formula (spira_trans (subterm_at P (spiras_sel_position P)))
            + depth_formula (spira_trans (subterm_at P pos)) + 1))))"
proof -
  let ?q   = "spiras_sel_position P"
  let ?Q   = "subterm_at P ?q"
  let ?R   = "subterm_at P pos"
  let ?QT  = "spira_trans (fix_at ?q True P)"
  let ?QF  = "spira_trans (fix_at ?q False P)"
  let ?PRT = "spira_trans (fix_at pos True P)"
  let ?PRF = "spira_trans (fix_at pos False P)"
  let ?RsT = "spira_trans (fix_at s True ?R)"
  let ?RsF = "spira_trans (fix_at s False ?R)"
  let ?sigma = "reassoc_sigma ?PRF ?PRT ?RsF ?RsT (spira_trans ?Q)"

  \<comment> \<open>spira_trans P opens at the spira node Q.\<close>
  have F2: "spira_trans P = balance ?QT ?QF (spira_trans ?Q)"
  proof -
    have "spira_trans P = rebalancing P ?q"
      using rebalancing_eq_spira_trans[OF wfP geP] by simp
    also have "\<dots> = balance ?QT ?QF (spira_trans ?Q)"
      unfolding rebalancing_def by simp
    finally show ?thesis .
  qed

  \<comment> \<open>rebalancing of R at s; its inner leaf is t(Q).\<close>
  have sub_eq2: "subterm_at ?R s = ?Q"
    using subterm_at_append[of P pos s] pos_eq2 by simp
  have F_R: "rebalancing ?R s = balance ?RsT ?RsF (spira_trans ?Q)"
    unfolding rebalancing_def using sub_eq2 by simp

  \<comment> \<open>case1_right_leaf: rebalancing the Q-fixed P at the ancestor R.\<close>
  have F_QT: "rebalancing (fix_at ?q True P) pos = balance ?PRT ?PRF ?RsT"
    using case1_right_leaf[OF vp, of s True] pos_eq2 by simp
  have F_QF: "rebalancing (fix_at ?q False P) pos = balance ?PRT ?PRF ?RsF"
    using case1_right_leaf[OF vp, of s False] pos_eq2 by simp

  \<comment> \<open>rebalancing P pos opens at pos.\<close>
  have F5: "rebalancing P pos = balance ?PRT ?PRF (spira_trans ?R)"
    unfolding rebalancing_def by simp

  \<comment> \<open>The three recursive equivalences, rewritten through F_R/F_Q.\<close>
  from IH_T have IHQT:
    "provable_balanced_iff ?QT (balance ?PRT ?PRF ?RsT) lT szT depT"
    by (simp only: F_QT[symmetric])
  from IH_F have IHQF:
    "provable_balanced_iff ?QF (balance ?PRT ?PRF ?RsF) lF szF depF"
    by (simp only: F_QF[symmetric])
  from IH_R have IHR:
    "provable_balanced_iff (spira_trans ?R)
        (balance ?RsT ?RsF (spira_trans ?Q)) lR szR depR"
    by (simp only: F_R[symmetric])

  \<comment> \<open>Uniform size / depth budgets for the glued formulas.\<close>
  define cb where cbdef: "cb = len_formula custom_balancing"
  define dcb where dcbdef: "dcb = depth_formula custom_balancing"
  have cb1: "(1::nat) \<le> cb" unfolding cbdef by (rule len_formula_positive)
  define LS where LSdef: "LS = len_formula ?QT + len_formula ?QF
     + len_formula ?PRT + len_formula ?PRF + len_formula ?RsT + len_formula ?RsF
     + len_formula (spira_trans ?Q) + len_formula (spira_trans ?R)"
  define DS where DSdef: "DS = depth_formula ?QT + depth_formula ?QF
     + depth_formula ?PRT + depth_formula ?PRF + depth_formula ?RsT
     + depth_formula ?RsF + depth_formula (spira_trans ?Q)
     + depth_formula (spira_trans ?R)"
  define NN1 where NN1def: "NN1 = cb * (3 * LS + 1)"
  define NN where NNdef: "NN = cb * (3 * NN1 + 1)"
  define SDB1 where SDB1def: "SDB1 = dcb + 3 * DS + 1"
  define SDB where SDBdef: "SDB = dcb + 3 * SDB1 + 1"
  define DBX where DBXdef: "DBX = refl_step_depth + sym_step_depth
       + trans_step_depth + balance_cong_step_depth + case_one_step_depth + SDB"
  define DB where DBdef: "DB = max depT (max depF (max depR DBX))"
  have DBX_DB: "DBX \<le> DB" unfolding DBdef by (simp add: le_max_iff_disj)
  have depT_DB: "depT \<le> DB" and depF_DB: "depF \<le> DB" and depR_DB: "depR \<le> DB"
    unfolding DBdef by (simp_all add: le_max_iff_disj)

  have lQT: "len_formula ?QT \<le> LS" and lQF: "len_formula ?QF \<le> LS"
   and lPRT: "len_formula ?PRT \<le> LS" and lPRF: "len_formula ?PRF \<le> LS"
   and lRsT: "len_formula ?RsT \<le> LS" and lRsF: "len_formula ?RsF \<le> LS"
   and lQ': "len_formula (spira_trans ?Q) \<le> LS"
   and lR': "len_formula (spira_trans ?R) \<le> LS"
    unfolding LSdef by simp_all
  have pQT: "depth_formula ?QT \<le> DS" and pQF: "depth_formula ?QF \<le> DS"
   and pPRT: "depth_formula ?PRT \<le> DS" and pPRF: "depth_formula ?PRF \<le> DS"
   and pRsT: "depth_formula ?RsT \<le> DS" and pRsF: "depth_formula ?RsF \<le> DS"
   and pQ': "depth_formula (spira_trans ?Q) \<le> DS"
   and pR': "depth_formula (spira_trans ?R) \<le> DS"
    unfolding DSdef by simp_all
  have LS_NN1: "LS \<le> NN1" unfolding NN1def using cb1
    by (simp add: add.commute trans_le_add2 mult.commute)
  have NN1_NN: "NN1 \<le> NN" unfolding NNdef using cb1
    by (simp add: add.commute trans_le_add2 mult.commute)
  have LS_NN: "LS \<le> NN" using LS_NN1 NN1_NN by simp

  note balNN1 = balance_len_below[OF cbdef NN1def]
  note balNN = balance_len_below_step[OF cbdef NNdef]
  note dbalSDB1 = balance_depth_below[OF dcbdef SDB1def]
  note dbalSDB = balance_depth_below_step[OF dcbdef SDBdef]
  have LS1: "1 \<le> LS" unfolding LSdef using len_formula_positive[of ?QT] by simp
  have SDB1_SDB: "SDB1 \<le> SDB" unfolding SDBdef by simp
  have DS_SDB1: "DS \<le> SDB1" unfolding SDB1def by simp
  have DS_SDB: "DS \<le> SDB" using DS_SDB1 SDB1_SDB by simp

  \<comment> \<open>Size / depth of every glued formula, against NN / SDB.\<close>
  have lP: "len_formula (spira_trans P) \<le> NN1"
    using balNN1[OF lQT lQF lQ'] F2 by simp
  have lreb: "len_formula (rebalancing P pos) \<le> NN1"
    using balNN1[OF lPRT lPRF lR'] F5 by simp
  have lPPRsT: "len_formula (balance ?PRT ?PRF ?RsT) \<le> NN1"
    by (rule balNN1[OF lPRT lPRF lRsT])
  have lPPRsF: "len_formula (balance ?PRT ?PRF ?RsF) \<le> NN1"
    by (rule balNN1[OF lPRT lPRF lRsF])
  have lRsRsQ: "len_formula (balance ?RsT ?RsF (spira_trans ?Q)) \<le> NN1"
    by (rule balNN1[OF lRsT lRsF lQ'])
  have lB1: "len_formula (balance (balance ?PRT ?PRF ?RsT)
                            (balance ?PRT ?PRF ?RsF) (spira_trans ?Q)) \<le> NN"
    by (rule balNN[OF lPPRsT lPPRsF le_trans[OF lQ' LS_NN1]])
  have lB2: "len_formula (balance ?PRT ?PRF
                            (balance ?RsT ?RsF (spira_trans ?Q))) \<le> NN"
    by (rule balNN[OF le_trans[OF lPRT LS_NN1] le_trans[OF lPRF LS_NN1] lRsRsQ])
  have pP: "depth_formula (spira_trans P) \<le> SDB1"
    using dbalSDB1[OF pQT pQF pQ'] F2 by simp
  have preb: "depth_formula (rebalancing P pos) \<le> SDB1"
    using dbalSDB1[OF pPRT pPRF pR'] F5 by simp
  have pPPRsT: "depth_formula (balance ?PRT ?PRF ?RsT) \<le> SDB1"
    by (rule dbalSDB1[OF pPRT pPRF pRsT])
  have pPPRsF: "depth_formula (balance ?PRT ?PRF ?RsF) \<le> SDB1"
    by (rule dbalSDB1[OF pPRT pPRF pRsF])
  have pRsRsQ: "depth_formula (balance ?RsT ?RsF (spira_trans ?Q)) \<le> SDB1"
    by (rule dbalSDB1[OF pRsT pRsF pQ'])
  have pB1: "depth_formula (balance (balance ?PRT ?PRF ?RsT)
                              (balance ?PRT ?PRF ?RsF) (spira_trans ?Q)) \<le> SDB"
    by (rule dbalSDB[OF pPPRsT pPPRsF le_trans[OF pQ' DS_SDB1]])
  have pB2: "depth_formula (balance ?PRT ?PRF
                              (balance ?RsT ?RsF (spira_trans ?Q))) \<le> SDB"
    by (rule dbalSDB[OF le_trans[OF pPRT DS_SDB1] le_trans[OF pPRF DS_SDB1]
                        pRsRsQ])

  note leafN = le_trans[OF lQT LS_NN] le_trans[OF lQF LS_NN]
               le_trans[OF lPRT LS_NN] le_trans[OF lPRF LS_NN]
               le_trans[OF lRsT LS_NN] le_trans[OF lRsF LS_NN]
               le_trans[OF lQ' LS_NN] le_trans[OF lR' LS_NN]
  note leafD = le_trans[OF pQT DS_SDB1] le_trans[OF pQF DS_SDB1]
               le_trans[OF pPRT DS_SDB1] le_trans[OF pPRF DS_SDB1]
               le_trans[OF pRsT DS_SDB1] le_trans[OF pRsF DS_SDB1]
               le_trans[OF pQ' DS_SDB1] le_trans[OF pR' DS_SDB1]
  note SDleafSDB = le_trans[OF pQT DS_SDB] le_trans[OF pQF DS_SDB]
                   le_trans[OF pPRT DS_SDB] le_trans[OF pPRF DS_SDB]
                   le_trans[OF pRsT DS_SDB] le_trans[OF pRsF DS_SDB]
                   le_trans[OF pQ' DS_SDB] le_trans[OF pR' DS_SDB]

  \<comment> \<open>Substitution-step budgets via the shared reassoc_sigma helpers.\<close>
  have DS1: "1 \<le> DS"
    unfolding DSdef using depth_formula_ge_1[of ?QT] by linarith
  have lsub: "len_sub (set reassoc_atoms) ?sigma \<le> 5 * LS"
    by (rule reassoc_sigma_len_sub_le[OF lPRF lPRT lRsF lRsT lQ' LS1])
  have dsub: "depth_sub (set reassoc_atoms) ?sigma \<le> DS"
    by (rule reassoc_sigma_depth_sub_le[OF pPRF pPRT pRsF pRsT pQ' DS1])

  \<comment> \<open>Glue depths sit below DBX, hence below DB.\<close>
  have AXQ: "refl_step_depth + depth_formula (spira_trans ?Q) \<le> DBX"
    unfolding DBXdef using leafD(7) SDB1_SDB by linarith
  have AXPRT: "refl_step_depth + depth_formula ?PRT \<le> DBX"
    unfolding DBXdef using leafD(3) SDB1_SDB by linarith
  have AXPRF: "refl_step_depth + depth_formula ?PRF \<le> DBX"
    unfolding DBXdef using leafD(4) SDB1_SDB by linarith
  have symX: "sym_step_depth + SDB \<le> DBX" unfolding DBXdef by linarith
  have bcsdX: "balance_cong_step_depth + SDB \<le> DBX" unfolding DBXdef by linarith
  have transX: "trans_step_depth + SDB \<le> DBX" unfolding DBXdef by linarith

  \<comment> \<open>Step 1: the t(P) opening, via balance_cong on the spira node.\<close>
  have sp1: "szT + szF + refl_step_len * len_formula (spira_trans ?Q)
           \<le> szT + szF + refl_step_len * NN"
    using mult_le_mono2[OF le_trans[OF lQ' LS_NN], of refl_step_len] by linarith
  have dp1: "max depT (max depF
               (refl_step_depth + depth_formula (spira_trans ?Q))) \<le> DB"
    by (intro max.boundedI depT_DB depF_DB le_trans[OF AXQ DBX_DB])
  have lp1: "len_formula ?QT + len_formula (balance ?PRT ?PRF ?RsT)
           + len_formula ?QF + len_formula (balance ?PRT ?PRF ?RsF)
           + len_formula (spira_trans ?Q) + len_formula (spira_trans ?Q)
           \<le> 6 * NN"
    using leafN(1) leafN(2) leafN(7) lPPRsT lPPRsF NN1_NN by linarith
  have pp1: "max (depth_formula ?QT)
               (max (depth_formula (balance ?PRT ?PRF ?RsT))
                 (max (depth_formula ?QF)
                   (max (depth_formula (balance ?PRT ?PRF ?RsF))
                     (max (depth_formula (spira_trans ?Q))
                       (depth_formula (spira_trans ?Q)))))) \<le> SDB"
    using SDleafSDB le_trans[OF pPPRsT SDB1_SDB] le_trans[OF pPPRsF SDB1_SDB]
    by (intro max.boundedI) simp_all
  note step1 = balance_cong_bnd[OF IHQT IHQF iff_refl[where A = "spira_trans ?Q"]
      sp1 dp1 lp1 pp1, folded F2]

  \<comment> \<open>Step 3: the rebalancing P pos folding, via balance_cong on the R IH.\<close>
  have lpR: "len_formula (spira_trans ?R)
           + len_formula (balance ?RsT ?RsF (spira_trans ?Q)) \<le> 2 * NN"
    using leafN(8) lRsRsQ NN1_NN by linarith
  have ppR: "max (depth_formula (spira_trans ?R))
               (depth_formula (balance ?RsT ?RsF (spira_trans ?Q))) \<le> SDB"
    using SDleafSDB(8) le_trans[OF pRsRsQ SDB1_SDB]
    by (intro max.boundedI) simp_all
  note isR = iff_sym_bnd[OF IHR order_refl order_refl lpR ppR]
  have sp3: "refl_step_len * len_formula ?PRT + refl_step_len * len_formula ?PRF
           + (szR + sym_step_len * (2 * NN))
           \<le> refl_step_len * NN + refl_step_len * NN
              + (szR + sym_step_len * (2 * NN))"
    using mult_le_mono2[OF leafN(3), of refl_step_len]
          mult_le_mono2[OF leafN(4), of refl_step_len] by linarith
  have dp3: "max (refl_step_depth + depth_formula ?PRT)
               (max (refl_step_depth + depth_formula ?PRF)
                 (max depR (sym_step_depth + SDB))) \<le> DB"
    by (intro max.boundedI le_trans[OF AXPRT DBX_DB] le_trans[OF AXPRF DBX_DB]
              depR_DB le_trans[OF symX DBX_DB])
  have lp3: "len_formula ?PRT + len_formula ?PRT + len_formula ?PRF
           + len_formula ?PRF + len_formula (balance ?RsT ?RsF (spira_trans ?Q))
           + len_formula (spira_trans ?R) \<le> 6 * NN"
    using leafN(3) leafN(4) leafN(8) lRsRsQ NN1_NN by linarith
  have pp3: "max (depth_formula ?PRT) (max (depth_formula ?PRT)
               (max (depth_formula ?PRF) (max (depth_formula ?PRF)
                 (max (depth_formula (balance ?RsT ?RsF (spira_trans ?Q)))
                   (depth_formula (spira_trans ?R)))))) \<le> SDB"
    using SDleafSDB le_trans[OF pRsRsQ SDB1_SDB]
    by (intro max.boundedI) simp_all
  note step3 = balance_cong_bnd[OF iff_refl[where A = "?PRT"]
      iff_refl[where A = "?PRF"] isR sp3 dp3 lp3 pp3, folded F5]

  \<comment> \<open>Step 2: the reassociation, run backwards (iff_sym of case_one).\<close>
  have sz2: "case_one_step_len * len_sub (set reassoc_atoms) ?sigma
           \<le> case_one_step_len * (5 * NN)"
  proof -
    have "len_sub (set reassoc_atoms) ?sigma \<le> 5 * NN"
      using lsub LS_NN by simp
    thus ?thesis by (rule mult_le_mono2)
  qed
  have dep2X: "case_one_step_depth + depth_sub (set reassoc_atoms) ?sigma \<le> DBX"
    unfolding DBXdef using dsub DS_SDB by linarith
  have dep2: "case_one_step_depth + depth_sub (set reassoc_atoms) ?sigma \<le> DB"
    by (rule le_trans[OF dep2X DBX_DB])
  note step2sub = reassoc_subst_step[of ?PRT ?PRF ?RsT ?RsF "spira_trans ?Q"]
  note step2sub' = provable_balanced_iff_weaken[OF step2sub order_refl sz2 dep2]
  have lp2: "len_formula (balance ?PRT ?PRF (balance ?RsT ?RsF (spira_trans ?Q)))
           + len_formula (balance (balance ?PRT ?PRF ?RsT)
               (balance ?PRT ?PRF ?RsF) (spira_trans ?Q)) \<le> 2 * NN"
    using lB1 lB2 by linarith
  have pp2: "max (depth_formula (balance ?PRT ?PRF
                 (balance ?RsT ?RsF (spira_trans ?Q))))
               (depth_formula (balance (balance ?PRT ?PRF ?RsT)
                 (balance ?PRT ?PRF ?RsF) (spira_trans ?Q))) \<le> SDB"
    using pB1 pB2 by (intro max.boundedI) simp_all
  note step2 = iff_sym_bnd[OF step2sub' order_refl order_refl lp2 pp2]

  \<comment> \<open>Composition by iff_trans_bnd.\<close>
  have dpAB: "max (max DB (balance_cong_step_depth + SDB))
               (max DB (sym_step_depth + SDB)) \<le> DB"
    by (intro max.boundedI order_refl le_trans[OF bcsdX DBX_DB]
              order_refl le_trans[OF symX DBX_DB])
  have lpAB: "len_formula (spira_trans P)
           + len_formula (balance (balance ?PRT ?PRF ?RsT)
               (balance ?PRT ?PRF ?RsF) (spira_trans ?Q))
           + len_formula (balance ?PRT ?PRF
               (balance ?RsT ?RsF (spira_trans ?Q))) \<le> 3 * NN"
    using le_trans[OF lP NN1_NN] lB1 lB2 by linarith
  have ppAB: "max (depth_formula (spira_trans P))
               (max (depth_formula (balance (balance ?PRT ?PRF ?RsT)
                       (balance ?PRT ?PRF ?RsF) (spira_trans ?Q)))
                 (depth_formula (balance ?PRT ?PRF
                       (balance ?RsT ?RsF (spira_trans ?Q))))) \<le> SDB"
    using le_trans[OF pP SDB1_SDB] pB1 pB2 by (intro max.boundedI) simp_all
  note inner = iff_trans_bnd[OF step1 step2 dpAB lpAB ppAB]
  have dpBC: "max (max DB (trans_step_depth + SDB))
               (max DB (balance_cong_step_depth + SDB)) \<le> DB"
    by (intro max.boundedI order_refl le_trans[OF transX DBX_DB]
              order_refl le_trans[OF bcsdX DBX_DB])
  have lpBC: "len_formula (spira_trans P)
           + len_formula (balance ?PRT ?PRF
               (balance ?RsT ?RsF (spira_trans ?Q)))
           + len_formula (rebalancing P pos) \<le> 3 * NN"
    using le_trans[OF lP NN1_NN] lB2 le_trans[OF lreb NN1_NN] by linarith
  have ppBC: "max (depth_formula (spira_trans P))
               (max (depth_formula (balance ?PRT ?PRF
                       (balance ?RsT ?RsF (spira_trans ?Q))))
                 (depth_formula (rebalancing P pos))) \<le> SDB"
    using le_trans[OF pP SDB1_SDB] pB2 le_trans[OF preb SDB1_SDB]
    by (intro max.boundedI) simp_all
  note chain = iff_trans_bnd[OF inner step3 dpBC lpBC ppBC]

  \<comment> \<open>The glue size sums to at most rebal_glue_coeff * (LS + 1).\<close>
  note NN1_lin = NN1_linear[OF NN1def]
  note NN_lin = NN_linear[OF cb1 NN1def NNdef]
  have cgc: "(3 * refl_step_len + 72 * balance_cong_step_len
              + 5 * case_one_step_len + 4 * sym_step_len + 6 * trans_step_len)
             * (12 * (cb * cb)) \<le> rebal_glue_coeff"
  proof -
    let ?S = "refl_step_len + sym_step_len + trans_step_len
              + balance_cong_step_len + case_one_step_len + 1"
    have c1: "3 * refl_step_len + 72 * balance_cong_step_len
              + 5 * case_one_step_len + 4 * sym_step_len + 6 * trans_step_len
              \<le> 72 * ?S" by simp
    have "(3 * refl_step_len + 72 * balance_cong_step_len
            + 5 * case_one_step_len + 4 * sym_step_len + 6 * trans_step_len)
          * (12 * (cb * cb))
          \<le> 4096 * ((cb + 1) * (cb + 1)) * ?S"
      by (rule glue_coeff_envelope[OF c1])
    also have "\<dots> = rebal_glue_coeff"
      unfolding rebal_glue_coeff_def cbdef by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  have glue_le: "refl_step_len * NN + refl_step_len * NN
       + balance_cong_step_len * (6 * (6 * NN)) + case_one_step_len * (5 * NN)
       + sym_step_len * (2 * NN) + sym_step_len * (2 * NN) + refl_step_len * NN
       + balance_cong_step_len * (6 * (6 * NN)) + trans_step_len * (3 * NN)
       + trans_step_len * (3 * NN)
       \<le> rebal_glue_coeff * (LS + 1)"
  proof -
    let ?C = "3 * refl_step_len + 72 * balance_cong_step_len
              + 5 * case_one_step_len + 4 * sym_step_len + 6 * trans_step_len"
    have eq: "refl_step_len * NN + refl_step_len * NN
       + balance_cong_step_len * (6 * (6 * NN)) + case_one_step_len * (5 * NN)
       + sym_step_len * (2 * NN) + sym_step_len * (2 * NN) + refl_step_len * NN
       + balance_cong_step_len * (6 * (6 * NN)) + trans_step_len * (3 * NN)
       + trans_step_len * (3 * NN) = ?C * NN"
      by (simp add: algebra_simps)
    have "?C * NN \<le> ?C * (12 * (cb * cb) * (LS + 1))"
      using NN_lin by (rule mult_le_mono2)
    also have "\<dots> = (?C * (12 * (cb * cb))) * (LS + 1)"
      by (simp add: algebra_simps)
    also have "\<dots> \<le> rebal_glue_coeff * (LS + 1)"
      using cgc by (rule mult_le_mono1)
    finally show ?thesis unfolding eq .
  qed

  \<comment> \<open>The sz glue: chain's per-line size budget, regrouped as
      szT + szF + szR plus the glue sum bounded by glue_le.\<close>
  have sz_le: "szT + szF + refl_step_len * NN
       + balance_cong_step_len * (6 * (6 * NN))
       + (case_one_step_len * (5 * NN) + sym_step_len * (2 * NN))
       + trans_step_len * (3 * NN)
       + (refl_step_len * NN + refl_step_len * NN
          + (szR + sym_step_len * (2 * NN))
          + balance_cong_step_len * (6 * (6 * NN)))
       + trans_step_len * (3 * NN)
       \<le> szT + szF + szR + rebal_glue_coeff * (LS + 1)"
  proof -
    have "szT + szF + refl_step_len * NN
       + balance_cong_step_len * (6 * (6 * NN))
       + (case_one_step_len * (5 * NN) + sym_step_len * (2 * NN))
       + trans_step_len * (3 * NN)
       + (refl_step_len * NN + refl_step_len * NN
          + (szR + sym_step_len * (2 * NN))
          + balance_cong_step_len * (6 * (6 * NN)))
       + trans_step_len * (3 * NN)
       = szT + szF + szR
         + (refl_step_len * NN + refl_step_len * NN
            + balance_cong_step_len * (6 * (6 * NN))
            + case_one_step_len * (5 * NN) + sym_step_len * (2 * NN)
            + sym_step_len * (2 * NN) + refl_step_len * NN
            + balance_cong_step_len * (6 * (6 * NN)) + trans_step_len * (3 * NN)
            + trans_step_len * (3 * NN))"
      by (simp add: algebra_simps)
    also have "\<dots> \<le> szT + szF + szR + rebal_glue_coeff * (LS + 1)"
      by (rule add_left_mono[OF glue_le])
    finally show ?thesis .
  qed

  \<comment> \<open>The depth glue: DBX is below the rebal_dep_coeff envelope.\<close>
  have DBX_env: "DBX \<le> rebal_dep_coeff * (DS + 1)"
  proof -
    have rdc9: "9 \<le> rebal_dep_coeff"
    proof -
      have "(9::nat) \<le> 4096 * depth_formula custom_balancing
            + 4096 * refl_step_depth + 4096 * sym_step_depth
            + 4096 * trans_step_depth + 4096 * balance_cong_step_depth
            + 4096 * case_one_step_depth + 4096" by linarith
      also have "\<dots> = rebal_dep_coeff"
        unfolding rebal_dep_coeff_def by (simp add: algebra_simps)
      finally show ?thesis .
    qed
    have a: "refl_step_depth + sym_step_depth + trans_step_depth
             + balance_cong_step_depth + case_one_step_depth + 4 * dcb + 4
             \<le> rebal_dep_coeff"
    proof -
      have "refl_step_depth + sym_step_depth + trans_step_depth
            + balance_cong_step_depth + case_one_step_depth + 4 * dcb + 4
            \<le> 4096 * dcb + 4096 * refl_step_depth + 4096 * sym_step_depth
              + 4096 * trans_step_depth + 4096 * balance_cong_step_depth
              + 4096 * case_one_step_depth + 4096" by linarith
      also have "\<dots> = rebal_dep_coeff"
        unfolding rebal_dep_coeff_def dcbdef by (simp add: algebra_simps)
      finally show ?thesis .
    qed
    have dbx: "DBX = (refl_step_depth + sym_step_depth + trans_step_depth
             + balance_cong_step_depth + case_one_step_depth + 4 * dcb + 4)
             + 9 * DS"
      unfolding DBXdef SDBdef SDB1def by simp
    show ?thesis by (rule dep_coeff_envelope[OF dbx a rdc9])
  qed
  have DB_le: "DB \<le> max depT (max depF (max depR (rebal_dep_coeff * (DS + 1))))"
    unfolding DBdef by (intro max.mono order_refl DBX_env)
  have chain_dep_le: "max DB (trans_step_depth + SDB)
        \<le> max depT (max depF (max depR (rebal_dep_coeff * (DS + 1))))"
  proof (rule max.boundedI[OF DB_le])
    have "trans_step_depth + SDB \<le> rebal_dep_coeff * (DS + 1)"
      using transX DBX_env by (rule le_trans)
    thus "trans_step_depth + SDB
          \<le> max depT (max depF (max depR (rebal_dep_coeff * (DS + 1))))"
      by (simp add: le_max_iff_disj)
  qed

  show ?thesis
  proof (rule exI[where x = "szT + szF + szR + rebal_glue_coeff * (LS + 1)"],
         rule exI[where x = "max depT (max depF (max depR
                   (rebal_dep_coeff * (DS + 1))))"],
         intro conjI)
    show "provable_balanced_iff (spira_trans P) (rebalancing P pos)
            (lT + lF + lR + case_two_glue_lines)
            (szT + szF + szR + rebal_glue_coeff * (LS + 1))
            (max depT (max depF (max depR (rebal_dep_coeff * (DS + 1)))))"
      \<comment> \<open>The line bound is an arithmetic identity; sz and dep are the
          structured facts sz_le and chain_dep_le.\<close>
      apply (rule provable_balanced_iff_weaken[OF chain])
        apply (simp add: case_two_glue_lines_def)
       apply (rule sz_le)
      apply (rule chain_dep_le)
      done
  next
    show "szT + szF + szR + rebal_glue_coeff * (LS + 1)
          \<le> szT + szF + szR + rebal_glue_coeff
              * (len_formula ?QT + len_formula ?QF + len_formula ?PRT
                 + len_formula ?PRF + len_formula ?RsT + len_formula ?RsF
                 + len_formula (spira_trans ?Q)
                 + len_formula (spira_trans ?R) + 1)"
      unfolding LSdef by simp
  next
    show "max depT (max depF (max depR (rebal_dep_coeff * (DS + 1))))
          \<le> max depT (max depF (max depR (rebal_dep_coeff
              * (depth_formula ?QT + depth_formula ?QF + depth_formula ?PRT
                 + depth_formula ?PRF + depth_formula ?RsT + depth_formula ?RsF
                 + depth_formula (spira_trans ?Q)
                 + depth_formula (spira_trans ?R) + 1))))"
      unfolding DSdef by simp
  qed
qed

subsection \<open>The case-three identity and construction\<close>

definition case_three_lhs :: "'c formula" where
  "case_three_lhs =
     balance (balance (Atom (cong_atoms ! 3)) (Atom (cong_atoms ! 2))
                      (Atom (cong_atoms ! 5)))
             (balance (Atom (cong_atoms ! 1)) (Atom (cong_atoms ! 0))
                      (Atom (cong_atoms ! 5)))
             (Atom (cong_atoms ! 4))"

definition case_three_rhs :: "'c formula" where
  "case_three_rhs =
     balance (balance (Atom (cong_atoms ! 3)) (Atom (cong_atoms ! 1))
                      (Atom (cong_atoms ! 4)))
             (balance (Atom (cong_atoms ! 2)) (Atom (cong_atoms ! 0))
                      (Atom (cong_atoms ! 4)))
             (Atom (cong_atoms ! 5))"

lemma case_three_taut:
  "\<forall>val. eval (alphabet F) val (iff_form case_three_lhs case_three_rhs)"
proof (intro allI)
  fix val
  let ?ev = "eval (alphabet F) val"
  have lhs: "?ev case_three_lhs
           = (if ?ev (Atom (cong_atoms ! 4))
              then (if ?ev (Atom (cong_atoms ! 5))
                    then ?ev (Atom (cong_atoms ! 3))
                    else ?ev (Atom (cong_atoms ! 2)))
              else (if ?ev (Atom (cong_atoms ! 5))
                    then ?ev (Atom (cong_atoms ! 1))
                    else ?ev (Atom (cong_atoms ! 0))))"
    unfolding case_three_lhs_def by (simp only: balance_eval)
  have rhs: "?ev case_three_rhs
           = (if ?ev (Atom (cong_atoms ! 5))
              then (if ?ev (Atom (cong_atoms ! 4))
                    then ?ev (Atom (cong_atoms ! 3))
                    else ?ev (Atom (cong_atoms ! 1)))
              else (if ?ev (Atom (cong_atoms ! 4))
                    then ?ev (Atom (cong_atoms ! 2))
                    else ?ev (Atom (cong_atoms ! 0))))"
    unfolding case_three_rhs_def by (simp only: balance_eval)
  have "?ev case_three_lhs = ?ev case_three_rhs"
    unfolding lhs rhs by simp
  thus "eval (alphabet F) val (iff_form case_three_lhs case_three_rhs)"
    by (simp add: iff_form_eval)
qed

definition case_three_lines :: nat where
  "case_three_lines = length (steps (taut_proof (iff_form case_three_lhs case_three_rhs)))"

definition case_three_step_len :: nat where
  "case_three_step_len =
     Max (insert 1 (len_formula ` set (steps (taut_proof
            (iff_form case_three_lhs case_three_rhs)))))"

definition case_three_step_depth :: nat where
  "case_three_step_depth =
     Max (insert 1 (depth_formula ` set (steps (taut_proof
            (iff_form case_three_lhs case_three_rhs)))))"

lemma case_three:
  "provable_balanced_iff case_three_lhs case_three_rhs
     case_three_lines case_three_step_len case_three_step_depth"
  using iff_from_taut[OF case_three_taut]
  unfolding case_three_lines_def case_three_step_len_def case_three_step_depth_def .

(*
  Case 3 of Lemma 5.1 (Q and R disjoint subtrees). Fixing Q and fixing R
  commute, so the doubly-fixed formulas P_{Q=b,R=c} are well-defined and the
  recursion forks four ways. Given the four recursive equivalences ---
  t(P_{Q=b}) \<leftrightarrow> rebalancing P_{Q=b} at pos and t(P_{R=c}) \<leftrightarrow>
  rebalancing P_{R=c} at the spira node --- the rebalancing equivalence is
  provable. The chain commutes the Q-selector and R-selector via case_three:

    t(P) = balance QT QF (t Q)
         \<leftrightarrow> balance (balance GTT GTF R) (balance GFT GFF R) (t Q)   (balance_cong, IHs at Q)
         \<leftrightarrow> balance (balance GTT GFT Q) (balance GTF GFF Q) (t R)   (case_three)
         \<leftrightarrow> rebalancing P pos                                      (balance_cong, IHs at R)
*)
definition case_three_glue_lines :: nat where
  "case_three_glue_lines = 2 * refl_lines + 2 * sym_lines + 2 * balance_cong_lines
     + case_three_lines + 2 * trans_lines"

\<comment> \<open>Glue coefficients for Case 3. Identical in spirit to rebal_glue_coeff /
    rebal_dep_coeff, but the reassociation step here is the case_three tautology,
    so case_three_step_len / case_three_step_depth replace the case_one ones.\<close>
definition rebal_glue_coeff3 :: nat where
  "rebal_glue_coeff3 = 4096 * (len_formula custom_balancing + 1)
     * (len_formula custom_balancing + 1)
     * (refl_step_len + sym_step_len + trans_step_len + balance_cong_step_len
        + case_three_step_len + 1)"

definition rebal_dep_coeff3 :: nat where
  "rebal_dep_coeff3 = 4096 * (depth_formula custom_balancing + refl_step_depth
     + sym_step_depth + trans_step_depth + balance_cong_step_depth
     + case_three_step_depth + 1)"

lemma case_three_construction:
  assumes wfP: "formula_well_formed (alphabet F) P"
      and geP: "len_formula P \<ge> spira_threshold"
      and disj_pos: "positions_disjoint (spiras_sel_position P) pos"
      and IH_QT: "provable_balanced_iff
                    (spira_trans (fix_at (spiras_sel_position P) True P))
                    (rebalancing (fix_at (spiras_sel_position P) True P) pos)
                    lQT szQT depQT"
      and IH_QF: "provable_balanced_iff
                    (spira_trans (fix_at (spiras_sel_position P) False P))
                    (rebalancing (fix_at (spiras_sel_position P) False P) pos)
                    lQF szQF depQF"
      and IH_RT: "provable_balanced_iff
                    (spira_trans (fix_at pos True P))
                    (rebalancing (fix_at pos True P) (spiras_sel_position P))
                    lRT szRT depRT"
      and IH_RF: "provable_balanced_iff
                    (spira_trans (fix_at pos False P))
                    (rebalancing (fix_at pos False P) (spiras_sel_position P))
                    lRF szRF depRF"
    shows "\<exists> sz dep.
       provable_balanced_iff (spira_trans P) (rebalancing P pos)
         (lQT + lQF + lRT + lRF + case_three_glue_lines) sz dep
     \<and> sz \<le> szQT + szQF + szRT + szRF + rebal_glue_coeff3
         * (len_formula (spira_trans (fix_at (spiras_sel_position P) True P))
            + len_formula (spira_trans (fix_at (spiras_sel_position P) False P))
            + len_formula (spira_trans (fix_at pos True P))
            + len_formula (spira_trans (fix_at pos False P))
            + len_formula (spira_trans
                (fix_at (spiras_sel_position P) True (fix_at pos True P)))
            + len_formula (spira_trans
                (fix_at (spiras_sel_position P) True (fix_at pos False P)))
            + len_formula (spira_trans
                (fix_at (spiras_sel_position P) False (fix_at pos True P)))
            + len_formula (spira_trans
                (fix_at (spiras_sel_position P) False (fix_at pos False P)))
            + len_formula (spira_trans (subterm_at P (spiras_sel_position P)))
            + len_formula (spira_trans (subterm_at P pos)) + 1)
     \<and> dep \<le> max depQT (max depQF (max depRT (max depRF (rebal_dep_coeff3
         * (depth_formula (spira_trans (fix_at (spiras_sel_position P) True P))
            + depth_formula (spira_trans (fix_at (spiras_sel_position P) False P))
            + depth_formula (spira_trans (fix_at pos True P))
            + depth_formula (spira_trans (fix_at pos False P))
            + depth_formula (spira_trans
                (fix_at (spiras_sel_position P) True (fix_at pos True P)))
            + depth_formula (spira_trans
                (fix_at (spiras_sel_position P) True (fix_at pos False P)))
            + depth_formula (spira_trans
                (fix_at (spiras_sel_position P) False (fix_at pos True P)))
            + depth_formula (spira_trans
                (fix_at (spiras_sel_position P) False (fix_at pos False P)))
            + depth_formula (spira_trans (subterm_at P (spiras_sel_position P)))
            + depth_formula (spira_trans (subterm_at P pos))
            + 1)))))"
proof -
  let ?q   = "spiras_sel_position P"
  let ?Q   = "subterm_at P ?q"
  let ?R   = "subterm_at P pos"
  let ?QT  = "spira_trans (fix_at ?q True P)"
  let ?QF  = "spira_trans (fix_at ?q False P)"
  let ?PRT = "spira_trans (fix_at pos True P)"
  let ?PRF = "spira_trans (fix_at pos False P)"
  let ?gtt = "fix_at ?q True (fix_at pos True P)"
  let ?gtf = "fix_at ?q True (fix_at pos False P)"
  let ?gft = "fix_at ?q False (fix_at pos True P)"
  let ?gff = "fix_at ?q False (fix_at pos False P)"
  let ?vals = "[spira_trans ?gff, spira_trans ?gft, spira_trans ?gtf,
                spira_trans ?gtt, spira_trans ?Q, spira_trans ?R]"
  let ?sigma = "\<lambda>v. case map_of (zip cong_atoms ?vals) v of
                     None \<Rightarrow> Atom v | Some f \<Rightarrow> f"

  have dpq: "positions_disjoint pos ?q"
    by (subst positions_disjoint_sym, rule disj_pos)

  \<comment> \<open>spira_trans P opens at the spira node Q.\<close>
  have F2: "spira_trans P = balance ?QT ?QF (spira_trans ?Q)"
  proof -
    have "spira_trans P = rebalancing P ?q"
      using rebalancing_eq_spira_trans[OF wfP geP] by simp
    also have "\<dots> = balance ?QT ?QF (spira_trans ?Q)"
      unfolding rebalancing_def by simp
    finally show ?thesis .
  qed

  \<comment> \<open>rebalancing P pos opens at pos.\<close>
  have F5: "rebalancing P pos = balance ?PRT ?PRF (spira_trans ?R)"
    unfolding rebalancing_def by simp

  \<comment> \<open>rebalancing the Q-fixed P at the (disjoint) position pos.\<close>
  have F_QT: "rebalancing (fix_at ?q True P) pos
            = balance (spira_trans ?gtt) (spira_trans ?gtf) (spira_trans ?R)"
  proof -
    have c1: "fix_at pos True (fix_at ?q True P) = ?gtt"
      using fix_at_commute_disjoint[OF dpq] by simp
    have c2: "fix_at pos False (fix_at ?q True P) = ?gtf"
      using fix_at_commute_disjoint[OF dpq] by simp
    have s: "subterm_at (fix_at ?q True P) pos = ?R"
      using subterm_at_fix_at_disjoint[OF dpq] by simp
    show ?thesis unfolding rebalancing_def using c1 c2 s by simp
  qed
  have F_QF: "rebalancing (fix_at ?q False P) pos
            = balance (spira_trans ?gft) (spira_trans ?gff) (spira_trans ?R)"
  proof -
    have c1: "fix_at pos True (fix_at ?q False P) = ?gft"
      using fix_at_commute_disjoint[OF dpq] by simp
    have c2: "fix_at pos False (fix_at ?q False P) = ?gff"
      using fix_at_commute_disjoint[OF dpq] by simp
    have s: "subterm_at (fix_at ?q False P) pos = ?R"
      using subterm_at_fix_at_disjoint[OF dpq] by simp
    show ?thesis unfolding rebalancing_def using c1 c2 s by simp
  qed

  \<comment> \<open>rebalancing the R-fixed P at the (disjoint) spira node.\<close>
  have F_RT: "rebalancing (fix_at pos True P) ?q
            = balance (spira_trans ?gtt) (spira_trans ?gft) (spira_trans ?Q)"
  proof -
    have s: "subterm_at (fix_at pos True P) ?q = ?Q"
      using subterm_at_fix_at_disjoint[OF disj_pos] by simp
    show ?thesis unfolding rebalancing_def using s by simp
  qed
  have F_RF: "rebalancing (fix_at pos False P) ?q
            = balance (spira_trans ?gtf) (spira_trans ?gff) (spira_trans ?Q)"
  proof -
    have s: "subterm_at (fix_at pos False P) ?q = ?Q"
      using subterm_at_fix_at_disjoint[OF disj_pos] by simp
    show ?thesis unfolding rebalancing_def using s by simp
  qed

  \<comment> \<open>The four recursive equivalences, rewritten through F_Q/F_R.\<close>
  from IH_QT have IHQT:
    "provable_balanced_iff (spira_trans (fix_at ?q True P))
        (balance (spira_trans ?gtt) (spira_trans ?gtf) (spira_trans ?R))
        lQT szQT depQT"
    by (simp only: F_QT[symmetric])
  from IH_QF have IHQF:
    "provable_balanced_iff (spira_trans (fix_at ?q False P))
        (balance (spira_trans ?gft) (spira_trans ?gff) (spira_trans ?R))
        lQF szQF depQF"
    by (simp only: F_QF[symmetric])
  from IH_RT have IHRT:
    "provable_balanced_iff (spira_trans (fix_at pos True P))
        (balance (spira_trans ?gtt) (spira_trans ?gft) (spira_trans ?Q))
        lRT szRT depRT"
    by (simp only: F_RT[symmetric])
  from IH_RF have IHRF:
    "provable_balanced_iff (spira_trans (fix_at pos False P))
        (balance (spira_trans ?gtf) (spira_trans ?gff) (spira_trans ?Q))
        lRF szRF depRF"
    by (simp only: F_RF[symmetric])

  \<comment> \<open>Fresh-atom facts for the six congruence atoms.\<close>
  have ca_len: "length cong_atoms = 6" using cong_atoms_spec by simp
  have ca_dist: "distinct cong_atoms" using cong_atoms_spec by simp
  have ca_disj: "set cong_atoms \<inter> avoid_atoms = {}"
    using cong_atoms_spec by simp
  have lveq: "length cong_atoms = length ?vals" using ca_len by simp

  have sig_val: "\<And>k::nat. k < 6 \<Longrightarrow> ?sigma (cong_atoms ! k) = ?vals ! k"
  proof -
    fix k :: nat assume "k < 6"
    hence "map_of (zip cong_atoms ?vals) (cong_atoms ! k) = Some (?vals ! k)"
      using map_of_zip_nth_lookup[OF ca_dist lveq] ca_len by simp
    thus "?sigma (cong_atoms ! k) = ?vals ! k" by simp
  qed
  have sv0: "?sigma (cong_atoms ! 0) = spira_trans ?gff" using sig_val[of 0] by simp
  have sv1: "?sigma (cong_atoms ! 1) = spira_trans ?gft" using sig_val[of 1] by simp
  have sv2: "?sigma (cong_atoms ! 2) = spira_trans ?gtf" using sig_val[of 2] by simp
  have sv3: "?sigma (cong_atoms ! 3) = spira_trans ?gtt" using sig_val[of 3] by simp
  have sv4: "?sigma (cong_atoms ! 4) = spira_trans ?Q" using sig_val[of 4] by simp
  have sv5: "?sigma (cong_atoms ! 5) = spira_trans ?R" using sig_val[of 5] by simp

  have sig_off: "\<And>v. v \<notin> set cong_atoms \<Longrightarrow> ?sigma v = Atom v"
  proof -
    fix v assume "v \<notin> set cong_atoms"
    hence "map_of (zip cong_atoms ?vals) v = None"
      by (rule map_of_zip_None_lookup)
    thus "?sigma v = Atom v" by simp
  qed
  have sig_id: "\<forall>v. v \<notin> set cong_atoms \<longrightarrow> ?sigma v = Atom v"
    using sig_off by blast
  note sig_conn = fresh_sub_conn[OF ca_disj sig_id]
  note sig_cb = fresh_sub_cb[OF ca_disj sig_id]

  \<comment> \<open>The selector-commutation tautology, substituted to the subformulas.\<close>
  have subL: "sub_formula ?sigma case_three_lhs
            = balance (balance (spira_trans ?gtt) (spira_trans ?gtf) (spira_trans ?R))
                      (balance (spira_trans ?gft) (spira_trans ?gff) (spira_trans ?R))
                      (spira_trans ?Q)"
  proof -
    have inL: "sub_formula ?sigma
                 (balance (Atom (cong_atoms ! 3)) (Atom (cong_atoms ! 2))
                          (Atom (cong_atoms ! 5)))
             = balance (spira_trans ?gtt) (spira_trans ?gtf) (spira_trans ?R)"
    proof -
      have "sub_formula ?sigma
              (balance (Atom (cong_atoms ! 3)) (Atom (cong_atoms ! 2))
                       (Atom (cong_atoms ! 5)))
          = balance (sub_formula ?sigma (Atom (cong_atoms ! 3)))
                    (sub_formula ?sigma (Atom (cong_atoms ! 2)))
                    (sub_formula ?sigma (Atom (cong_atoms ! 5)))"
        by (rule sub_formula_balance[OF sig_cb])
      thus ?thesis by (simp only: sub_formula.simps sv3 sv2 sv5)
    qed
    have inR: "sub_formula ?sigma
                 (balance (Atom (cong_atoms ! 1)) (Atom (cong_atoms ! 0))
                          (Atom (cong_atoms ! 5)))
             = balance (spira_trans ?gft) (spira_trans ?gff) (spira_trans ?R)"
    proof -
      have "sub_formula ?sigma
              (balance (Atom (cong_atoms ! 1)) (Atom (cong_atoms ! 0))
                       (Atom (cong_atoms ! 5)))
          = balance (sub_formula ?sigma (Atom (cong_atoms ! 1)))
                    (sub_formula ?sigma (Atom (cong_atoms ! 0)))
                    (sub_formula ?sigma (Atom (cong_atoms ! 5)))"
        by (rule sub_formula_balance[OF sig_cb])
      thus ?thesis by (simp only: sub_formula.simps sv1 sv0 sv5)
    qed
    have "sub_formula ?sigma case_three_lhs
        = balance (sub_formula ?sigma
                     (balance (Atom (cong_atoms ! 3)) (Atom (cong_atoms ! 2))
                              (Atom (cong_atoms ! 5))))
                  (sub_formula ?sigma
                     (balance (Atom (cong_atoms ! 1)) (Atom (cong_atoms ! 0))
                              (Atom (cong_atoms ! 5))))
                  (sub_formula ?sigma (Atom (cong_atoms ! 4)))"
      unfolding case_three_lhs_def by (rule sub_formula_balance[OF sig_cb])
    thus ?thesis by (simp only: sub_formula.simps inL inR sv4)
  qed
  have subR: "sub_formula ?sigma case_three_rhs
            = balance (balance (spira_trans ?gtt) (spira_trans ?gft) (spira_trans ?Q))
                      (balance (spira_trans ?gtf) (spira_trans ?gff) (spira_trans ?Q))
                      (spira_trans ?R)"
  proof -
    have inL: "sub_formula ?sigma
                 (balance (Atom (cong_atoms ! 3)) (Atom (cong_atoms ! 1))
                          (Atom (cong_atoms ! 4)))
             = balance (spira_trans ?gtt) (spira_trans ?gft) (spira_trans ?Q)"
    proof -
      have "sub_formula ?sigma
              (balance (Atom (cong_atoms ! 3)) (Atom (cong_atoms ! 1))
                       (Atom (cong_atoms ! 4)))
          = balance (sub_formula ?sigma (Atom (cong_atoms ! 3)))
                    (sub_formula ?sigma (Atom (cong_atoms ! 1)))
                    (sub_formula ?sigma (Atom (cong_atoms ! 4)))"
        by (rule sub_formula_balance[OF sig_cb])
      thus ?thesis by (simp only: sub_formula.simps sv3 sv1 sv4)
    qed
    have inR: "sub_formula ?sigma
                 (balance (Atom (cong_atoms ! 2)) (Atom (cong_atoms ! 0))
                          (Atom (cong_atoms ! 4)))
             = balance (spira_trans ?gtf) (spira_trans ?gff) (spira_trans ?Q)"
    proof -
      have "sub_formula ?sigma
              (balance (Atom (cong_atoms ! 2)) (Atom (cong_atoms ! 0))
                       (Atom (cong_atoms ! 4)))
          = balance (sub_formula ?sigma (Atom (cong_atoms ! 2)))
                    (sub_formula ?sigma (Atom (cong_atoms ! 0)))
                    (sub_formula ?sigma (Atom (cong_atoms ! 4)))"
        by (rule sub_formula_balance[OF sig_cb])
      thus ?thesis by (simp only: sub_formula.simps sv2 sv0 sv4)
    qed
    have "sub_formula ?sigma case_three_rhs
        = balance (sub_formula ?sigma
                     (balance (Atom (cong_atoms ! 3)) (Atom (cong_atoms ! 1))
                              (Atom (cong_atoms ! 4))))
                  (sub_formula ?sigma
                     (balance (Atom (cong_atoms ! 2)) (Atom (cong_atoms ! 0))
                              (Atom (cong_atoms ! 4))))
                  (sub_formula ?sigma (Atom (cong_atoms ! 5)))"
      unfolding case_three_rhs_def by (rule sub_formula_balance[OF sig_cb])
    thus ?thesis by (simp only: sub_formula.simps inL inR sv5)
  qed

  \<comment> \<open>Uniform size / depth budgets for the glued formulas.\<close>
  define cb where cbdef: "cb = len_formula custom_balancing"
  define dcb where dcbdef: "dcb = depth_formula custom_balancing"
  have cb1: "(1::nat) \<le> cb" unfolding cbdef by (rule len_formula_positive)
  define LS where LSdef: "LS = len_formula ?QT + len_formula ?QF
     + len_formula ?PRT + len_formula ?PRF
     + len_formula (spira_trans ?gtt) + len_formula (spira_trans ?gtf)
     + len_formula (spira_trans ?gft) + len_formula (spira_trans ?gff)
     + len_formula (spira_trans ?Q) + len_formula (spira_trans ?R)"
  define DS where DSdef: "DS = depth_formula ?QT + depth_formula ?QF
     + depth_formula ?PRT + depth_formula ?PRF
     + depth_formula (spira_trans ?gtt) + depth_formula (spira_trans ?gtf)
     + depth_formula (spira_trans ?gft) + depth_formula (spira_trans ?gff)
     + depth_formula (spira_trans ?Q) + depth_formula (spira_trans ?R)"
  define NN1 where NN1def: "NN1 = cb * (3 * LS + 1)"
  define NN where NNdef: "NN = cb * (3 * NN1 + 1)"
  define SDB1 where SDB1def: "SDB1 = dcb + 3 * DS + 1"
  define SDB where SDBdef: "SDB = dcb + 3 * SDB1 + 1"
  define DBX where DBXdef: "DBX = refl_step_depth + sym_step_depth
       + trans_step_depth + balance_cong_step_depth + case_three_step_depth
       + SDB"
  define DB where DBdef: "DB = max depQT (max depQF (max depRT (max depRF DBX)))"
  have DBX_DB: "DBX \<le> DB" unfolding DBdef by (simp add: le_max_iff_disj)
  have depQT_DB: "depQT \<le> DB" and depQF_DB: "depQF \<le> DB"
   and depRT_DB: "depRT \<le> DB" and depRF_DB: "depRF \<le> DB"
    unfolding DBdef by (simp_all add: le_max_iff_disj)

  have lQT: "len_formula ?QT \<le> LS" and lQF: "len_formula ?QF \<le> LS"
   and lPRT: "len_formula ?PRT \<le> LS" and lPRF: "len_formula ?PRF \<le> LS"
   and lgtt: "len_formula (spira_trans ?gtt) \<le> LS"
   and lgtf: "len_formula (spira_trans ?gtf) \<le> LS"
   and lgft: "len_formula (spira_trans ?gft) \<le> LS"
   and lgff: "len_formula (spira_trans ?gff) \<le> LS"
   and lQ': "len_formula (spira_trans ?Q) \<le> LS"
   and lR': "len_formula (spira_trans ?R) \<le> LS"
    unfolding LSdef by simp_all
  have pQT: "depth_formula ?QT \<le> DS" and pQF: "depth_formula ?QF \<le> DS"
   and pPRT: "depth_formula ?PRT \<le> DS" and pPRF: "depth_formula ?PRF \<le> DS"
   and pgtt: "depth_formula (spira_trans ?gtt) \<le> DS"
   and pgtf: "depth_formula (spira_trans ?gtf) \<le> DS"
   and pgft: "depth_formula (spira_trans ?gft) \<le> DS"
   and pgff: "depth_formula (spira_trans ?gff) \<le> DS"
   and pQ': "depth_formula (spira_trans ?Q) \<le> DS"
   and pR': "depth_formula (spira_trans ?R) \<le> DS"
    unfolding DSdef by simp_all
  have LS_NN1: "LS \<le> NN1" unfolding NN1def using cb1
    by (simp add: add.commute trans_le_add2 mult.commute)
  have NN1_NN: "NN1 \<le> NN" unfolding NNdef using cb1
    by (simp add: add.commute trans_le_add2 mult.commute)
  have LS_NN: "LS \<le> NN" using LS_NN1 NN1_NN by simp

  note balNN1 = balance_len_below[OF cbdef NN1def]
  note balNN = balance_len_below_step[OF cbdef NNdef]
  note dbalSDB1 = balance_depth_below[OF dcbdef SDB1def]
  note dbalSDB = balance_depth_below_step[OF dcbdef SDBdef]
  have LS1: "1 \<le> LS" unfolding LSdef using len_formula_positive[of ?QT] by simp
  have SDB1_SDB: "SDB1 \<le> SDB" unfolding SDBdef by simp
  have DS_SDB1: "DS \<le> SDB1" unfolding SDB1def by simp
  have DS_SDB: "DS \<le> SDB" using DS_SDB1 SDB1_SDB by simp

  \<comment> \<open>Size / depth of every glued formula, against NN / SDB.\<close>
  have lP: "len_formula (spira_trans P) \<le> NN1"
    using balNN1[OF lQT lQF lQ'] F2 by simp
  have lreb: "len_formula (rebalancing P pos) \<le> NN1"
    using balNN1[OF lPRT lPRF lR'] F5 by simp
  have l_ttfR: "len_formula (balance (spira_trans ?gtt) (spira_trans ?gtf)
                  (spira_trans ?R)) \<le> NN1"
    by (rule balNN1[OF lgtt lgtf lR'])
  have l_ftfR: "len_formula (balance (spira_trans ?gft) (spira_trans ?gff)
                  (spira_trans ?R)) \<le> NN1"
    by (rule balNN1[OF lgft lgff lR'])
  have l_ttQ: "len_formula (balance (spira_trans ?gtt) (spira_trans ?gft)
                  (spira_trans ?Q)) \<le> NN1"
    by (rule balNN1[OF lgtt lgft lQ'])
  have l_tfQ: "len_formula (balance (spira_trans ?gtf) (spira_trans ?gff)
                  (spira_trans ?Q)) \<le> NN1"
    by (rule balNN1[OF lgtf lgff lQ'])
  have lB1: "len_formula (balance
              (balance (spira_trans ?gtt) (spira_trans ?gtf) (spira_trans ?R))
              (balance (spira_trans ?gft) (spira_trans ?gff) (spira_trans ?R))
              (spira_trans ?Q)) \<le> NN"
    by (rule balNN[OF l_ttfR l_ftfR le_trans[OF lQ' LS_NN1]])
  have lB2: "len_formula (balance
              (balance (spira_trans ?gtt) (spira_trans ?gft) (spira_trans ?Q))
              (balance (spira_trans ?gtf) (spira_trans ?gff) (spira_trans ?Q))
              (spira_trans ?R)) \<le> NN"
    by (rule balNN[OF l_ttQ l_tfQ le_trans[OF lR' LS_NN1]])
  have pP: "depth_formula (spira_trans P) \<le> SDB1"
    using dbalSDB1[OF pQT pQF pQ'] F2 by simp
  have preb: "depth_formula (rebalancing P pos) \<le> SDB1"
    using dbalSDB1[OF pPRT pPRF pR'] F5 by simp
  have p_ttfR: "depth_formula (balance (spira_trans ?gtt) (spira_trans ?gtf)
                  (spira_trans ?R)) \<le> SDB1"
    by (rule dbalSDB1[OF pgtt pgtf pR'])
  have p_ftfR: "depth_formula (balance (spira_trans ?gft) (spira_trans ?gff)
                  (spira_trans ?R)) \<le> SDB1"
    by (rule dbalSDB1[OF pgft pgff pR'])
  have p_ttQ: "depth_formula (balance (spira_trans ?gtt) (spira_trans ?gft)
                  (spira_trans ?Q)) \<le> SDB1"
    by (rule dbalSDB1[OF pgtt pgft pQ'])
  have p_tfQ: "depth_formula (balance (spira_trans ?gtf) (spira_trans ?gff)
                  (spira_trans ?Q)) \<le> SDB1"
    by (rule dbalSDB1[OF pgtf pgff pQ'])
  have pB1: "depth_formula (balance
              (balance (spira_trans ?gtt) (spira_trans ?gtf) (spira_trans ?R))
              (balance (spira_trans ?gft) (spira_trans ?gff) (spira_trans ?R))
              (spira_trans ?Q)) \<le> SDB"
    by (rule dbalSDB[OF p_ttfR p_ftfR le_trans[OF pQ' DS_SDB1]])
  have pB2: "depth_formula (balance
              (balance (spira_trans ?gtt) (spira_trans ?gft) (spira_trans ?Q))
              (balance (spira_trans ?gtf) (spira_trans ?gff) (spira_trans ?Q))
              (spira_trans ?R)) \<le> SDB"
    by (rule dbalSDB[OF p_ttQ p_tfQ le_trans[OF pR' DS_SDB1]])

  note leafN = le_trans[OF lQT LS_NN] le_trans[OF lQF LS_NN]
               le_trans[OF lPRT LS_NN] le_trans[OF lPRF LS_NN]
               le_trans[OF lgtt LS_NN] le_trans[OF lgtf LS_NN]
               le_trans[OF lgft LS_NN] le_trans[OF lgff LS_NN]
               le_trans[OF lQ' LS_NN] le_trans[OF lR' LS_NN]
  note leafD = le_trans[OF pQT DS_SDB1] le_trans[OF pQF DS_SDB1]
               le_trans[OF pPRT DS_SDB1] le_trans[OF pPRF DS_SDB1]
               le_trans[OF pgtt DS_SDB1] le_trans[OF pgtf DS_SDB1]
               le_trans[OF pgft DS_SDB1] le_trans[OF pgff DS_SDB1]
               le_trans[OF pQ' DS_SDB1] le_trans[OF pR' DS_SDB1]
  note SDleafSDB = le_trans[OF pQT DS_SDB] le_trans[OF pQF DS_SDB]
                   le_trans[OF pPRT DS_SDB] le_trans[OF pPRF DS_SDB]
                   le_trans[OF pgtt DS_SDB] le_trans[OF pgtf DS_SDB]
                   le_trans[OF pgft DS_SDB] le_trans[OF pgff DS_SDB]
                   le_trans[OF pQ' DS_SDB] le_trans[OF pR' DS_SDB]

  \<comment> \<open>The substitution step: each congruence atom maps to a spira_trans leaf.\<close>
  have sigv_LS: "len_formula (?sigma v) \<le> LS" if "v \<in> set cong_atoms" for v
  proof -
    from that obtain k where k6: "k < 6" and vk: "cong_atoms ! k = v"
      using ca_len by (auto simp: in_set_conv_nth)
    have e: "?sigma v = ?vals ! k"
      unfolding vk[symmetric] by (rule sig_val[OF k6])
    consider "k = 0" | "k = 1" | "k = 2" | "k = 3" | "k = 4" | "k = 5"
      using k6 by linarith
    thus ?thesis using e lgff lgft lgtf lgtt lQ' lR' by cases simp_all
  qed
  have sigv_DS: "depth_formula (?sigma v) \<le> DS" if "v \<in> set cong_atoms" for v
  proof -
    from that obtain k where k6: "k < 6" and vk: "cong_atoms ! k = v"
      using ca_len by (auto simp: in_set_conv_nth)
    have e: "?sigma v = ?vals ! k"
      unfolding vk[symmetric] by (rule sig_val[OF k6])
    consider "k = 0" | "k = 1" | "k = 2" | "k = 3" | "k = 4" | "k = 5"
      using k6 by linarith
    thus ?thesis using e pgff pgft pgtf pgtt pQ' pR' by cases simp_all
  qed
  have card6: "card (set cong_atoms) = 6"
    using distinct_card[OF ca_dist] ca_len by simp
  have lsub: "len_sub (set cong_atoms) ?sigma \<le> 6 * LS"
  proof -
    have "(\<Sum>v\<in>set cong_atoms. len_formula (?sigma v))
          \<le> (\<Sum>v\<in>set cong_atoms. LS)"
      by (rule sum_mono) (rule sigv_LS)
    also have "\<dots> = 6 * LS" using card6 by simp
    finally have "(\<Sum>v\<in>set cong_atoms. len_formula (?sigma v)) \<le> 6 * LS" .
    thus ?thesis unfolding len_sub_def using LS1 by simp
  qed
  have DS1: "1 \<le> DS"
    unfolding DSdef using depth_formula_ge_1[of ?QT] by linarith
  have dsub: "depth_sub (set cong_atoms) ?sigma \<le> DS"
    unfolding depth_sub_def
  proof (rule Max.boundedI)
    show "finite (insert 1 ((\<lambda>v. depth_formula (?sigma v))
                             ` set cong_atoms))" by simp
    show "insert 1 ((\<lambda>v. depth_formula (?sigma v)) ` set cong_atoms)
          \<noteq> {}" by simp
    fix e assume "e \<in> insert 1 ((\<lambda>v. depth_formula (?sigma v))
                                 ` set cong_atoms)"
    thus "e \<le> DS" using sigv_DS DS1 by auto
  qed

  \<comment> \<open>Glue depths sit below DBX, hence below DB.\<close>
  have AXQ: "refl_step_depth + depth_formula (spira_trans ?Q) \<le> DBX"
    unfolding DBXdef using leafD(9) SDB1_SDB by linarith
  have AXR: "refl_step_depth + depth_formula (spira_trans ?R) \<le> DBX"
    unfolding DBXdef using leafD(10) SDB1_SDB by linarith
  have symX: "sym_step_depth + SDB \<le> DBX" unfolding DBXdef by linarith
  have bcsdX: "balance_cong_step_depth + SDB \<le> DBX" unfolding DBXdef by linarith
  have transX: "trans_step_depth + SDB \<le> DBX" unfolding DBXdef by linarith

  \<comment> \<open>Step 1: the t(P) opening, via balance_cong on the spira node.\<close>
  have sp1: "szQT + szQF + refl_step_len * len_formula (spira_trans ?Q)
           \<le> szQT + szQF + refl_step_len * NN"
    using mult_le_mono2[OF le_trans[OF lQ' LS_NN], of refl_step_len] by linarith
  have dp1: "max depQT (max depQF
               (refl_step_depth + depth_formula (spira_trans ?Q))) \<le> DB"
    by (intro max.boundedI depQT_DB depQF_DB le_trans[OF AXQ DBX_DB])
  have lp1: "len_formula ?QT
           + len_formula (balance (spira_trans ?gtt) (spira_trans ?gtf)
               (spira_trans ?R))
           + len_formula ?QF
           + len_formula (balance (spira_trans ?gft) (spira_trans ?gff)
               (spira_trans ?R))
           + len_formula (spira_trans ?Q) + len_formula (spira_trans ?Q)
           \<le> 6 * NN"
    using leafN(1) leafN(2) leafN(9) l_ttfR l_ftfR NN1_NN by linarith
  have pp1: "max (depth_formula ?QT)
               (max (depth_formula (balance (spira_trans ?gtt)
                       (spira_trans ?gtf) (spira_trans ?R)))
                 (max (depth_formula ?QF)
                   (max (depth_formula (balance (spira_trans ?gft)
                           (spira_trans ?gff) (spira_trans ?R)))
                     (max (depth_formula (spira_trans ?Q))
                       (depth_formula (spira_trans ?Q)))))) \<le> SDB"
    using SDleafSDB le_trans[OF p_ttfR SDB1_SDB] le_trans[OF p_ftfR SDB1_SDB]
    by (intro max.boundedI) simp_all
  note step1 = balance_cong_bnd[OF IHQT IHQF iff_refl[where A = "spira_trans ?Q"]
      sp1 dp1 lp1 pp1, folded F2]

  \<comment> \<open>Step 3: the rebalancing P pos folding, via balance_cong on the R IHs.\<close>
  have lpRT: "len_formula ?PRT
           + len_formula (balance (spira_trans ?gtt) (spira_trans ?gft)
               (spira_trans ?Q)) \<le> 2 * NN"
    using leafN(3) l_ttQ NN1_NN by linarith
  have ppRT: "max (depth_formula ?PRT)
               (depth_formula (balance (spira_trans ?gtt) (spira_trans ?gft)
                 (spira_trans ?Q))) \<le> SDB"
    using SDleafSDB(3) le_trans[OF p_ttQ SDB1_SDB]
    by (intro max.boundedI) simp_all
  note isRT = iff_sym_bnd[OF IHRT order_refl order_refl lpRT ppRT]
  have lpRF: "len_formula ?PRF
           + len_formula (balance (spira_trans ?gtf) (spira_trans ?gff)
               (spira_trans ?Q)) \<le> 2 * NN"
    using leafN(4) l_tfQ NN1_NN by linarith
  have ppRF: "max (depth_formula ?PRF)
               (depth_formula (balance (spira_trans ?gtf) (spira_trans ?gff)
                 (spira_trans ?Q))) \<le> SDB"
    using SDleafSDB(4) le_trans[OF p_tfQ SDB1_SDB]
    by (intro max.boundedI) simp_all
  note isRF = iff_sym_bnd[OF IHRF order_refl order_refl lpRF ppRF]
  have sp3: "(szRT + sym_step_len * (2 * NN)) + (szRF + sym_step_len * (2 * NN))
           + refl_step_len * len_formula (spira_trans ?R)
           \<le> (szRT + sym_step_len * (2 * NN))
              + (szRF + sym_step_len * (2 * NN)) + refl_step_len * NN"
    using mult_le_mono2[OF le_trans[OF lR' LS_NN], of refl_step_len] by linarith
  have dp3: "max (max depRT (sym_step_depth + SDB))
               (max (max depRF (sym_step_depth + SDB))
                 (refl_step_depth + depth_formula (spira_trans ?R))) \<le> DB"
    by (intro max.boundedI depRT_DB le_trans[OF symX DBX_DB] depRF_DB
              le_trans[OF symX DBX_DB] le_trans[OF AXR DBX_DB])
  have lp3: "len_formula (balance (spira_trans ?gtt) (spira_trans ?gft)
               (spira_trans ?Q))
           + len_formula ?PRT
           + len_formula (balance (spira_trans ?gtf) (spira_trans ?gff)
               (spira_trans ?Q))
           + len_formula ?PRF
           + len_formula (spira_trans ?R) + len_formula (spira_trans ?R)
           \<le> 6 * NN"
    using leafN(3) leafN(4) leafN(10) l_ttQ l_tfQ NN1_NN by linarith
  have pp3: "max (depth_formula (balance (spira_trans ?gtt)
                 (spira_trans ?gft) (spira_trans ?Q)))
               (max (depth_formula ?PRT)
                 (max (depth_formula (balance (spira_trans ?gtf)
                         (spira_trans ?gff) (spira_trans ?Q)))
                   (max (depth_formula ?PRF)
                     (max (depth_formula (spira_trans ?R))
                       (depth_formula (spira_trans ?R)))))) \<le> SDB"
    using SDleafSDB le_trans[OF p_ttQ SDB1_SDB] le_trans[OF p_tfQ SDB1_SDB]
    by (intro max.boundedI) simp_all
  note step3 = balance_cong_bnd[OF isRT isRF iff_refl[where A = "spira_trans ?R"]
      sp3 dp3 lp3 pp3, folded F5]

  \<comment> \<open>Step 2: the selector-commutation reassociation (case_three).\<close>
  have sz2: "case_three_step_len * len_sub (set cong_atoms) ?sigma
           \<le> case_three_step_len * (6 * NN)"
  proof -
    have "len_sub (set cong_atoms) ?sigma \<le> 6 * NN"
      using lsub LS_NN by simp
    thus ?thesis by (rule mult_le_mono2)
  qed
  have dep2X: "case_three_step_depth + depth_sub (set cong_atoms) ?sigma \<le> DBX"
    unfolding DBXdef using dsub DS_SDB by linarith
  have dep2: "case_three_step_depth + depth_sub (set cong_atoms) ?sigma \<le> DB"
    by (rule le_trans[OF dep2X DBX_DB])
  note step2 = provable_balanced_iff_subst[OF case_three finite_set sig_id
                                              sig_conn, unfolded subL subR]
  note step2' = provable_balanced_iff_weaken[OF step2 order_refl sz2 dep2]

  \<comment> \<open>Composition by iff_trans_bnd.\<close>
  have dpAB: "max (max DB (balance_cong_step_depth + SDB)) DB \<le> DB"
    by (intro max.boundedI order_refl le_trans[OF bcsdX DBX_DB])
  have lpAB: "len_formula (spira_trans P)
           + len_formula (balance
               (balance (spira_trans ?gtt) (spira_trans ?gtf) (spira_trans ?R))
               (balance (spira_trans ?gft) (spira_trans ?gff) (spira_trans ?R))
               (spira_trans ?Q))
           + len_formula (balance
               (balance (spira_trans ?gtt) (spira_trans ?gft) (spira_trans ?Q))
               (balance (spira_trans ?gtf) (spira_trans ?gff) (spira_trans ?Q))
               (spira_trans ?R)) \<le> 3 * NN"
    using le_trans[OF lP NN1_NN] lB1 lB2 by linarith
  have ppAB: "max (depth_formula (spira_trans P))
               (max (depth_formula (balance
                       (balance (spira_trans ?gtt) (spira_trans ?gtf)
                         (spira_trans ?R))
                       (balance (spira_trans ?gft) (spira_trans ?gff)
                         (spira_trans ?R)) (spira_trans ?Q)))
                 (depth_formula (balance
                       (balance (spira_trans ?gtt) (spira_trans ?gft)
                         (spira_trans ?Q))
                       (balance (spira_trans ?gtf) (spira_trans ?gff)
                         (spira_trans ?Q)) (spira_trans ?R)))) \<le> SDB"
    using le_trans[OF pP SDB1_SDB] pB1 pB2 by (intro max.boundedI) simp_all
  note inner = iff_trans_bnd[OF step1 step2' dpAB lpAB ppAB]
  have dpBC: "max (max DB (trans_step_depth + SDB))
               (max DB (balance_cong_step_depth + SDB)) \<le> DB"
    by (intro max.boundedI order_refl le_trans[OF transX DBX_DB]
              order_refl le_trans[OF bcsdX DBX_DB])
  have lpBC: "len_formula (spira_trans P)
           + len_formula (balance
               (balance (spira_trans ?gtt) (spira_trans ?gft) (spira_trans ?Q))
               (balance (spira_trans ?gtf) (spira_trans ?gff) (spira_trans ?Q))
               (spira_trans ?R))
           + len_formula (rebalancing P pos) \<le> 3 * NN"
    using le_trans[OF lP NN1_NN] lB2 le_trans[OF lreb NN1_NN] by linarith
  have ppBC: "max (depth_formula (spira_trans P))
               (max (depth_formula (balance
                       (balance (spira_trans ?gtt) (spira_trans ?gft)
                         (spira_trans ?Q))
                       (balance (spira_trans ?gtf) (spira_trans ?gff)
                         (spira_trans ?Q)) (spira_trans ?R)))
                 (depth_formula (rebalancing P pos))) \<le> SDB"
    using le_trans[OF pP SDB1_SDB] pB2 le_trans[OF preb SDB1_SDB]
    by (intro max.boundedI) simp_all
  note chain = iff_trans_bnd[OF inner step3 dpBC lpBC ppBC]

  \<comment> \<open>The glue size sums to at most rebal_glue_coeff3 * (LS + 1).\<close>
  note NN1_lin = NN1_linear[OF NN1def]
  note NN_lin = NN_linear[OF cb1 NN1def NNdef]
  have cgc: "(2 * refl_step_len + 72 * balance_cong_step_len
              + 6 * case_three_step_len + 4 * sym_step_len + 6 * trans_step_len)
             * (12 * (cb * cb)) \<le> rebal_glue_coeff3"
  proof -
    let ?S = "refl_step_len + sym_step_len + trans_step_len
              + balance_cong_step_len + case_three_step_len + 1"
    have c1: "2 * refl_step_len + 72 * balance_cong_step_len
              + 6 * case_three_step_len + 4 * sym_step_len + 6 * trans_step_len
              \<le> 72 * ?S" by simp
    have "(2 * refl_step_len + 72 * balance_cong_step_len
            + 6 * case_three_step_len + 4 * sym_step_len + 6 * trans_step_len)
          * (12 * (cb * cb))
          \<le> 4096 * ((cb + 1) * (cb + 1)) * ?S"
      by (rule glue_coeff_envelope[OF c1])
    also have "\<dots> = rebal_glue_coeff3"
      unfolding rebal_glue_coeff3_def cbdef by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  have glue_le: "refl_step_len * NN + refl_step_len * NN
       + balance_cong_step_len * (6 * (6 * NN))
       + balance_cong_step_len * (6 * (6 * NN))
       + case_three_step_len * (6 * NN)
       + sym_step_len * (2 * NN) + sym_step_len * (2 * NN)
       + trans_step_len * (3 * NN) + trans_step_len * (3 * NN)
       \<le> rebal_glue_coeff3 * (LS + 1)"
  proof -
    let ?C = "2 * refl_step_len + 72 * balance_cong_step_len
              + 6 * case_three_step_len + 4 * sym_step_len + 6 * trans_step_len"
    have eq: "refl_step_len * NN + refl_step_len * NN
       + balance_cong_step_len * (6 * (6 * NN))
       + balance_cong_step_len * (6 * (6 * NN))
       + case_three_step_len * (6 * NN)
       + sym_step_len * (2 * NN) + sym_step_len * (2 * NN)
       + trans_step_len * (3 * NN) + trans_step_len * (3 * NN) = ?C * NN"
      by (simp add: algebra_simps)
    have "?C * NN \<le> ?C * (12 * (cb * cb) * (LS + 1))"
      using NN_lin by (rule mult_le_mono2)
    also have "\<dots> = (?C * (12 * (cb * cb))) * (LS + 1)"
      by (simp add: algebra_simps)
    also have "\<dots> \<le> rebal_glue_coeff3 * (LS + 1)"
      using cgc by (rule mult_le_mono1)
    finally show ?thesis unfolding eq .
  qed

  \<comment> \<open>The sz glue: chain's per-line size budget, regrouped as
      szQT + szQF + szRT + szRF plus the glue sum bounded by glue_le.\<close>
  have sz_le: "szQT + szQF + refl_step_len * NN
       + balance_cong_step_len * (6 * (6 * NN))
       + case_three_step_len * (6 * NN) + trans_step_len * (3 * NN)
       + (szRT + sym_step_len * (2 * NN) + (szRF + sym_step_len * (2 * NN))
          + refl_step_len * NN + balance_cong_step_len * (6 * (6 * NN)))
       + trans_step_len * (3 * NN)
       \<le> szQT + szQF + szRT + szRF + rebal_glue_coeff3 * (LS + 1)"
  proof -
    have "szQT + szQF + refl_step_len * NN
       + balance_cong_step_len * (6 * (6 * NN))
       + case_three_step_len * (6 * NN) + trans_step_len * (3 * NN)
       + (szRT + sym_step_len * (2 * NN) + (szRF + sym_step_len * (2 * NN))
          + refl_step_len * NN + balance_cong_step_len * (6 * (6 * NN)))
       + trans_step_len * (3 * NN)
       = szQT + szQF + szRT + szRF
         + (refl_step_len * NN + refl_step_len * NN
            + balance_cong_step_len * (6 * (6 * NN))
            + balance_cong_step_len * (6 * (6 * NN))
            + case_three_step_len * (6 * NN)
            + sym_step_len * (2 * NN) + sym_step_len * (2 * NN)
            + trans_step_len * (3 * NN) + trans_step_len * (3 * NN))"
      by (simp add: algebra_simps)
    also have "\<dots> \<le> szQT + szQF + szRT + szRF + rebal_glue_coeff3 * (LS + 1)"
      by (rule add_left_mono[OF glue_le])
    finally show ?thesis .
  qed

  \<comment> \<open>The depth glue: DBX is below the rebal_dep_coeff3 envelope.\<close>
  have DBX_env: "DBX \<le> rebal_dep_coeff3 * (DS + 1)"
  proof -
    have rdc9: "9 \<le> rebal_dep_coeff3"
    proof -
      have "(9::nat) \<le> 4096 * depth_formula custom_balancing
            + 4096 * refl_step_depth + 4096 * sym_step_depth
            + 4096 * trans_step_depth + 4096 * balance_cong_step_depth
            + 4096 * case_three_step_depth + 4096" by linarith
      also have "\<dots> = rebal_dep_coeff3"
        unfolding rebal_dep_coeff3_def by (simp add: algebra_simps)
      finally show ?thesis .
    qed
    have a: "refl_step_depth + sym_step_depth + trans_step_depth
             + balance_cong_step_depth + case_three_step_depth + 4 * dcb + 4
             \<le> rebal_dep_coeff3"
    proof -
      have "refl_step_depth + sym_step_depth + trans_step_depth
            + balance_cong_step_depth + case_three_step_depth + 4 * dcb + 4
            \<le> 4096 * dcb + 4096 * refl_step_depth + 4096 * sym_step_depth
              + 4096 * trans_step_depth + 4096 * balance_cong_step_depth
              + 4096 * case_three_step_depth + 4096" by linarith
      also have "\<dots> = rebal_dep_coeff3"
        unfolding rebal_dep_coeff3_def dcbdef by (simp add: algebra_simps)
      finally show ?thesis .
    qed
    have dbx: "DBX = (refl_step_depth + sym_step_depth + trans_step_depth
             + balance_cong_step_depth + case_three_step_depth + 4 * dcb + 4)
             + 9 * DS"
      unfolding DBXdef SDBdef SDB1def by simp
    show ?thesis by (rule dep_coeff_envelope[OF dbx a rdc9])
  qed
  have DB_le: "DB \<le> max depQT (max depQF (max depRT (max depRF
                     (rebal_dep_coeff3 * (DS + 1)))))"
    unfolding DBdef by (intro max.mono order_refl DBX_env)
  have chain_dep_le: "max DB (trans_step_depth + SDB)
        \<le> max depQT (max depQF (max depRT (max depRF
            (rebal_dep_coeff3 * (DS + 1)))))"
  proof (rule max.boundedI[OF DB_le])
    have "trans_step_depth + SDB \<le> rebal_dep_coeff3 * (DS + 1)"
      using transX DBX_env by (rule le_trans)
    thus "trans_step_depth + SDB
          \<le> max depQT (max depQF (max depRT (max depRF
              (rebal_dep_coeff3 * (DS + 1)))))"
      by (simp add: le_max_iff_disj)
  qed

  show ?thesis
  proof (rule exI[where x = "szQT + szQF + szRT + szRF
                   + rebal_glue_coeff3 * (LS + 1)"],
         rule exI[where x = "max depQT (max depQF (max depRT (max depRF
                   (rebal_dep_coeff3 * (DS + 1)))))"],
         intro conjI)
    show "provable_balanced_iff (spira_trans P) (rebalancing P pos)
            (lQT + lQF + lRT + lRF + case_three_glue_lines)
            (szQT + szQF + szRT + szRF + rebal_glue_coeff3 * (LS + 1))
            (max depQT (max depQF (max depRT (max depRF
              (rebal_dep_coeff3 * (DS + 1))))))"
      \<comment> \<open>chain carries three trivially-true side premises (the premises
          of sig_conn's three-premise statement); simp discharges each.\<close>
      apply (rule provable_balanced_iff_weaken[OF chain])
           apply simp
          apply simp
         apply simp
        apply (simp add: case_three_glue_lines_def)
       apply (rule sz_le)
      apply (rule chain_dep_le)
      done
  next
    show "szQT + szQF + szRT + szRF + rebal_glue_coeff3 * (LS + 1)
          \<le> szQT + szQF + szRT + szRF + rebal_glue_coeff3
              * (len_formula ?QT + len_formula ?QF + len_formula ?PRT
                 + len_formula ?PRF + len_formula (spira_trans ?gtt)
                 + len_formula (spira_trans ?gtf)
                 + len_formula (spira_trans ?gft)
                 + len_formula (spira_trans ?gff)
                 + len_formula (spira_trans ?Q)
                 + len_formula (spira_trans ?R) + 1)"
      unfolding LSdef by simp
  next
    show "max depQT (max depQF (max depRT (max depRF
            (rebal_dep_coeff3 * (DS + 1)))))
          \<le> max depQT (max depQF (max depRT (max depRF (rebal_dep_coeff3
              * (depth_formula ?QT + depth_formula ?QF + depth_formula ?PRT
                 + depth_formula ?PRF + depth_formula (spira_trans ?gtt)
                 + depth_formula (spira_trans ?gtf)
                 + depth_formula (spira_trans ?gft)
                 + depth_formula (spira_trans ?gff)
                 + depth_formula (spira_trans ?Q)
                 + depth_formula (spira_trans ?R) + 1)))))"
      unfolding DSdef by simp
  qed
qed

(*
  The well-founded measure for Lemma 5.1's induction: the lexical pair
  (|P|, |P| - |subterm_at P pos|) linearised to a single nat. The first
  component dominates --- any drop in |P| decreases the measure regardless
  of the second component (rebal_measure_lt_of_len_lt) --- while an atom-R
  recursion keeps |P| fixed and decreases only the second.
*)
subsection \<open>The termination measure\<close>

definition rebal_measure :: "'c formula \<Rightarrow> nat list \<Rightarrow> nat" where
  "rebal_measure P pos =
     len_formula P * (len_formula P + 1)
     + (len_formula P - len_formula (subterm_at P pos))"

lemma rebal_measure_lt_of_len_lt:
  assumes "len_formula A < len_formula P"
  shows "rebal_measure A t < rebal_measure P pos"
proof -
  let ?lA = "len_formula A"
  let ?lP = "len_formula P"
  have a1: "?lA + 1 \<le> ?lP" using assms by simp
  have "rebal_measure A t \<le> ?lA * (?lA + 1) + ?lA"
    unfolding rebal_measure_def by simp
  also have "?lA * (?lA + 1) + ?lA = ?lA * (?lA + 2)"
    by (simp add: algebra_simps)
  also have "?lA * (?lA + 2) < (?lA + 1) * (?lA + 1)"
    by (simp add: algebra_simps)
  also have "(?lA + 1) * (?lA + 1) \<le> ?lP * ?lP"
    by (rule mult_le_mono[OF a1 a1])
  also have "?lP * ?lP \<le> ?lP * (?lP + 1)" by simp
  also have "?lP * (?lP + 1) \<le> rebal_measure P pos"
    unfolding rebal_measure_def by simp
  finally show ?thesis .
qed

(*
  Case 1 measure decrease: the three recursive sub-problems --- (Q, s) and
  (P_{R=b}, q) for b \<in> {True, False} --- all strictly decrease rebal_measure.
  (Q, s) shrinks |P| outright; (P_{R=b}, q) shrinks |P| unless R is a single
  node, in which case |P| is fixed but Q_{R=b} (of length \<ge> 2) replaces the
  length-1 R, so the second component drops.
*)
lemma case_one_measure:
  assumes wfP: "formula_well_formed (alphabet F) P"
      and geP: "len_formula P \<ge> spira_threshold"
      and pos_eq: "pos = spiras_sel_position P @ s"
      and s_ne: "s \<noteq> []"
      and vp: "valid_position P pos"
    shows "rebal_measure (subterm_at P (spiras_sel_position P)) s
             < rebal_measure P pos
         \<and> rebal_measure (fix_at pos True P) (spiras_sel_position P)
             < rebal_measure P pos
         \<and> rebal_measure (fix_at pos False P) (spiras_sel_position P)
             < rebal_measure P pos"
proof -
  let ?q = "spiras_sel_position P"
  let ?Q = "subterm_at P ?q"
  have ge2: "len_formula P \<ge> 2" using geP unfolding spira_threshold_def by simp
  have subQ_eq: "?Q = spiras_sel P"
    using spiras_sel_position_spec[OF wfP ge2] by simp
  have lenQ: "len_formula ?Q < len_formula P"
    using subQ_eq spiras_sel_pred_when_wf[OF wfP ge2] by simp
  have m1: "rebal_measure ?Q s < rebal_measure P pos"
    by (rule rebal_measure_lt_of_len_lt[OF lenQ])

  have split: "valid_position P ?q \<and> valid_position ?Q s"
    using vp by (simp only: pos_eq valid_position_append)

  have m2: "rebal_measure (fix_at pos b P) ?q < rebal_measure P pos" for b
  proof (cases "len_formula (fix_at pos b P) < len_formula P")
    case True
    show ?thesis by (rule rebal_measure_lt_of_len_lt[OF True])
  next
    case False
    have eqlen: "len_formula (fix_at pos b P) = len_formula P"
      using False fix_at_len_le[of pos b P] by simp
    have lenR1: "len_formula (subterm_at P pos) = 1"
    proof (rule ccontr)
      assume ne: "len_formula (subterm_at P pos) \<noteq> 1"
      have "len_formula (subterm_at P pos) \<ge> 1" by (rule len_formula_positive)
      with ne have ge2R: "len_formula (subterm_at P pos) \<ge> 2" by simp
      have "len_formula (fix_at pos b P) < len_formula P"
        using fix_at_len_strict[OF vp ge2R] .
      thus False using eqlen by simp
    qed
    have sub_eq: "subterm_at (fix_at pos b P) ?q = fix_at s b ?Q"
      using subterm_at_fix_at_prefix[OF conjunct1[OF split], of s b] pos_eq
      by simp
    have ge2Qb: "len_formula (fix_at s b ?Q) \<ge> 2"
      using fix_at_len_ge_2[OF conjunct2[OF split] s_ne] by simp
    have lenQb_le: "len_formula (fix_at s b ?Q) \<le> len_formula P"
      using fix_at_len_le[of s b ?Q] lenQ by simp
    have "rebal_measure (fix_at pos b P) ?q
        = len_formula P * (len_formula P + 1)
          + (len_formula P - len_formula (fix_at s b ?Q))"
      unfolding rebal_measure_def using eqlen sub_eq by simp
    also have "\<dots> < len_formula P * (len_formula P + 1)
                     + (len_formula P - len_formula (subterm_at P pos))"
      using lenR1 ge2Qb lenQb_le by linarith
    also have "\<dots> = rebal_measure P pos"
      unfolding rebal_measure_def by (rule refl)
    finally show ?thesis .
  qed

  show ?thesis using m1 m2[of True] m2[of False] by blast
qed

(*
  Case 2 measure decrease (Q a descendant of R). The sub-problem (R, s) shrinks
  |P| since R is a proper subformula (pos \<noteq> []); the sub-problems (P_{Q=b}, pos)
  shrink |P| because the spira node Q has length \<ge> 2, so fixing it to a
  constant strictly reduces the formula. Both go through rebal_measure_lt_of_len_lt.
*)
lemma case_two_measure:
  assumes wfP: "formula_well_formed (alphabet F) P"
      and geP: "len_formula P \<ge> spira_threshold"
      and pos_ne: "pos \<noteq> []"
      and vp: "valid_position P pos"
    shows "rebal_measure (subterm_at P pos) s < rebal_measure P pos
         \<and> rebal_measure (fix_at (spiras_sel_position P) True P) pos
             < rebal_measure P pos
         \<and> rebal_measure (fix_at (spiras_sel_position P) False P) pos
             < rebal_measure P pos"
proof -
  let ?q = "spiras_sel_position P"
  have ge2: "len_formula P \<ge> 2" using geP unfolding spira_threshold_def by simp
  have lenR: "len_formula (subterm_at P pos) < len_formula P"
    using subterm_at_len_lt[OF vp pos_ne] .
  have mR: "rebal_measure (subterm_at P pos) s < rebal_measure P pos"
    by (rule rebal_measure_lt_of_len_lt[OF lenR])
  have vpq: "valid_position P ?q"
    using spiras_sel_position_spec[OF wfP ge2] by simp
  have ge2Q: "len_formula (subterm_at P ?q) \<ge> 2"
    using spiras_sel_position_spec[OF wfP ge2]
          spiras_sel_len_ge_2_when_wf[OF wfP geP] by simp
  have mQ: "rebal_measure (fix_at ?q b P) pos < rebal_measure P pos" for b
  proof -
    have "len_formula (fix_at ?q b P) < len_formula P"
      using fix_at_len_strict[OF vpq ge2Q] .
    thus ?thesis by (rule rebal_measure_lt_of_len_lt)
  qed
  show ?thesis using mR mQ[of True] mQ[of False] by blast
qed

(*
  Case 3 measure decrease (Q and R disjoint). The sub-problems (P_{Q=b}, pos)
  shrink |P| (the spira node Q has length \<ge> 2). The sub-problems (P_{R=b}, q)
  shrink |P| unless R is a single node, in which case |P| is fixed but the
  subterm at q --- the spira node, length \<ge> 2 --- replaces the length-1 R,
  so the second measure component drops.
*)
lemma case_three_measure:
  assumes wfP: "formula_well_formed (alphabet F) P"
      and geP: "len_formula P \<ge> spira_threshold"
      and disj_pos: "positions_disjoint (spiras_sel_position P) pos"
      and vp: "valid_position P pos"
    shows "rebal_measure (fix_at (spiras_sel_position P) True P) pos
             < rebal_measure P pos
         \<and> rebal_measure (fix_at (spiras_sel_position P) False P) pos
             < rebal_measure P pos
         \<and> rebal_measure (fix_at pos True P) (spiras_sel_position P)
             < rebal_measure P pos
         \<and> rebal_measure (fix_at pos False P) (spiras_sel_position P)
             < rebal_measure P pos"
proof -
  let ?q = "spiras_sel_position P"
  have ge2: "len_formula P \<ge> 2" using geP unfolding spira_threshold_def by simp
  have vpq: "valid_position P ?q"
    using spiras_sel_position_spec[OF wfP ge2] by simp
  have subQ_eq: "subterm_at P ?q = spiras_sel P"
    using spiras_sel_position_spec[OF wfP ge2] by simp
  have ge2Q: "len_formula (subterm_at P ?q) \<ge> 2"
    using subQ_eq spiras_sel_len_ge_2_when_wf[OF wfP geP] by simp
  have ltQ: "len_formula (subterm_at P ?q) < len_formula P"
    using subQ_eq spiras_sel_pred_when_wf[OF wfP ge2] by simp

  have mQ: "rebal_measure (fix_at ?q b P) pos < rebal_measure P pos" for b
  proof -
    have "len_formula (fix_at ?q b P) < len_formula P"
      using fix_at_len_strict[OF vpq ge2Q] .
    thus ?thesis by (rule rebal_measure_lt_of_len_lt)
  qed

  have mR: "rebal_measure (fix_at pos b P) ?q < rebal_measure P pos" for b
  proof (cases "len_formula (fix_at pos b P) < len_formula P")
    case True
    show ?thesis by (rule rebal_measure_lt_of_len_lt[OF True])
  next
    case False
    have eqlen: "len_formula (fix_at pos b P) = len_formula P"
      using False fix_at_len_le[of pos b P] by simp
    have lenR1: "len_formula (subterm_at P pos) = 1"
    proof (rule ccontr)
      assume ne: "len_formula (subterm_at P pos) \<noteq> 1"
      have "len_formula (subterm_at P pos) \<ge> 1" by (rule len_formula_positive)
      with ne have ge2R: "len_formula (subterm_at P pos) \<ge> 2" by simp
      have "len_formula (fix_at pos b P) < len_formula P"
        using fix_at_len_strict[OF vp ge2R] .
      thus False using eqlen by simp
    qed
    have sub_eq: "subterm_at (fix_at pos b P) ?q = subterm_at P ?q"
      using subterm_at_fix_at_disjoint[OF disj_pos] by simp
    have "rebal_measure (fix_at pos b P) ?q
        = len_formula P * (len_formula P + 1)
          + (len_formula P - len_formula (subterm_at P ?q))"
      unfolding rebal_measure_def using eqlen sub_eq by simp
    also have "\<dots> < len_formula P * (len_formula P + 1)
                     + (len_formula P - len_formula (subterm_at P pos))"
      using lenR1 ge2Q ltQ by linarith
    also have "\<dots> = rebal_measure P pos"
      unfolding rebal_measure_def by (rule refl)
    finally show ?thesis .
  qed

  show ?thesis using mQ[of True] mQ[of False] mR[of True] mR[of False] by blast
qed

(*
  The pos = [] degenerate sub-case of Lemma 5.1 (rebalancing at the root).
  Here rebalancing P [] opens as balance true_const false_const (spira_trans P),
  and t(P) \<leftrightarrow> rebalancing P [] is the fixed mux identity
  z \<leftrightarrow> balance true_const false_const z, substituted at z := spira_trans P.
*)
subsection \<open>The pos = [] degenerate case\<close>

lemma rebalancing_at_root:
  "rebalancing P [] = balance true_const false_const (spira_trans P)"
proof -
  have thr: "spira_threshold \<ge> 2" unfolding spira_threshold_def by simp
  have tT: "spira_trans true_const = true_const"
    using spira_trans_id_when_small[OF true_const_wf] true_const_len thr by simp
  have tF: "spira_trans false_const = false_const"
    using spira_trans_id_when_small[OF false_const_wf] false_const_len thr by simp
  show ?thesis
    unfolding rebalancing_def using tT tF by simp
qed

definition pos_empty_lhs :: "'c formula" where
  "pos_empty_lhs = Atom refl_atom"

definition pos_empty_rhs :: "'c formula" where
  "pos_empty_rhs = balance true_const false_const (Atom refl_atom)"

lemma pos_empty_taut:
  "\<forall>val. eval (alphabet F) val (iff_form pos_empty_lhs pos_empty_rhs)"
proof (intro allI)
  fix val
  let ?ev = "eval (alphabet F) val"
  have rhs: "?ev pos_empty_rhs
           = (if ?ev (Atom refl_atom) then ?ev true_const else ?ev false_const)"
    unfolding pos_empty_rhs_def by (simp only: balance_eval)
  have "?ev pos_empty_lhs = ?ev pos_empty_rhs"
    unfolding pos_empty_lhs_def rhs using true_const_eval false_const_eval by simp
  thus "eval (alphabet F) val (iff_form pos_empty_lhs pos_empty_rhs)"
    by (simp add: iff_form_eval)
qed

definition pos_empty_lines :: nat where
  "pos_empty_lines =
     length (steps (taut_proof (iff_form pos_empty_lhs pos_empty_rhs)))"

definition pos_empty_step_len :: nat where
  "pos_empty_step_len =
     Max (insert 1 (len_formula ` set (steps (taut_proof
            (iff_form pos_empty_lhs pos_empty_rhs)))))"

definition pos_empty_step_depth :: nat where
  "pos_empty_step_depth =
     Max (insert 1 (depth_formula ` set (steps (taut_proof
            (iff_form pos_empty_lhs pos_empty_rhs)))))"

(*
  The mux collapse: for any formula G, G \<leftrightarrow> balance true_const false_const G
  by a balanced no-assumption proof --- the fixed mux tautology with the single
  fresh atom substituted by G. The line count is constant, the per-line size
  scales with |G| and the per-line depth is raised by depth G. This is the
  base case (pos = []) of the rebalancing equivalence.
*)
lemma mux_collapse_iff:
  "provable_balanced_iff G (balance true_const false_const G)
     pos_empty_lines
     (pos_empty_step_len * len_formula G)
     (pos_empty_step_depth + 1 + depth_formula G)"
proof -
  let ?z = "refl_atom"
  let ?sub = "\<lambda>w. if w = ?z then G else Atom w"
  have base: "provable_balanced_iff pos_empty_lhs pos_empty_rhs
                pos_empty_lines pos_empty_step_len pos_empty_step_depth"
    using iff_from_taut[OF pos_empty_taut]
    unfolding pos_empty_lines_def pos_empty_step_len_def pos_empty_step_depth_def .
  have fin: "finite {?z}" by simp
  have sig_id: "\<forall>v. v \<notin> {?z} \<longrightarrow> ?sub v = Atom v" by simp
  have sig_conn: "\<And>w. w \<in> var_set_form conn_iff \<Longrightarrow> w \<noteq> ''a'' \<Longrightarrow> w \<noteq> ''b''
                       \<Longrightarrow> ?sub w = Atom w"
    using refl_atom_not_conn_iff by auto
  have sig_cb: "\<And>v. v \<in> var_set_form custom_balancing \<Longrightarrow> v \<noteq> ''x''
                     \<Longrightarrow> v \<noteq> ''y'' \<Longrightarrow> v \<noteq> ''z'' \<Longrightarrow> ?sub v = Atom v"
    using refl_atom_fresh unfolding avoid_atoms_def by auto
  have subL: "sub_formula ?sub pos_empty_lhs = G"
    by (simp add: pos_empty_lhs_def)
  have subR: "sub_formula ?sub pos_empty_rhs = balance true_const false_const G"
  proof -
    have "sub_formula ?sub pos_empty_rhs
        = balance (sub_formula ?sub true_const) (sub_formula ?sub false_const)
                  (sub_formula ?sub (Atom ?z))"
      unfolding pos_empty_rhs_def by (rule sub_formula_balance[OF sig_cb])
    thus ?thesis by (simp add: true_const_def false_const_def)
  qed
  have lensub: "len_sub {?z} ?sub = len_formula G"
    using len_formula_positive[of G] by (simp add: len_sub_def)
  have depsub: "depth_sub {?z} ?sub \<le> 1 + depth_formula G"
    by (simp add: depth_sub_def max_def)
  have pbi: "provable_balanced_iff G (balance true_const false_const G)
               pos_empty_lines (pos_empty_step_len * len_formula G)
               (pos_empty_step_depth + depth_sub {?z} ?sub)"
    using provable_balanced_iff_subst[OF base fin sig_id sig_conn]
    by (simp add: subL subR lensub)
  show ?thesis
  proof (rule provable_balanced_iff_weaken[OF pbi order_refl order_refl])
    show "pos_empty_step_depth + depth_sub {?z} ?sub
          \<le> pos_empty_step_depth + 1 + depth_formula G"
      using depsub by linarith
  qed
qed

(*
  The construction for pos = []: t(P) \<leftrightarrow> rebalancing P [] is the mux collapse
  at G = spira_trans P, since rebalancing P [] opens as
  balance true_const false_const (spira_trans P).
*)
lemma case_pos_empty_construction:
  "provable_balanced_iff (spira_trans P) (rebalancing P [])
     pos_empty_lines
     (pos_empty_step_len * len_formula (spira_trans P))
     (pos_empty_step_depth + 1 + depth_formula (spira_trans P))"
  using mux_collapse_iff[of "spira_trans P"]
  unfolding rebalancing_at_root[symmetric] .

(*
  Context congruence at the provable_balanced_iff level: a balanced proof of
  \<phi> \<leftrightarrow> \<psi> lifts to one of (plug h \<phi> \<chi>) \<leftrightarrow> (plug h \<psi> \<chi>) --- substituting the
  proven equivalence into the single-hole context \<chi>. The line count grows by a
  polynomial in |\<chi>|, the per-line size by a polynomial in |\<phi>|+|\<psi>|+|\<chi>|, the
  per-line depth by depth \<chi> plus a constant. The congruence engine is
  iff_congruent; this wrapper combines its proof with the premise proof,
  discharging the single assumption iff_form \<phi> \<psi>.
*)
subsection \<open>Connective (slot) congruence\<close>

lemma plug_cong_exists:
  "\<exists> (congbnd :: nat poly) (congc :: nat).
     \<forall> \<phi> \<psi> \<chi> h l s d.
       provable_balanced_iff \<phi> \<psi> l s d \<and> distinguished \<chi> h
         \<and> contains_atom \<chi> h \<and> formula_well_formed (alphabet F) \<chi>
       \<longrightarrow> provable_balanced_iff (plug h \<phi> \<chi>) (plug h \<psi> \<chi>)
             (l + poly congbnd (len_formula \<chi>))
             (max s (poly congbnd
                       (max (len_formula \<phi>) (len_formula \<psi>) + len_formula \<chi>)))
             (max d (max (depth_formula \<phi>) (depth_formula \<psi>)
                     + depth_formula \<chi> + congc))"
proof -
  have fs_F: "frege_system F"
    by (meson frege_balancing_axioms frege_balancing_def)
  from iff_congruent obtain congc congbnd where IC:
    "\<forall> \<phi> \<psi> \<chi> h.
       (let sub  = \<lambda>v. if v = ''a'' then \<phi> else if v = ''b'' then \<psi> else Atom v;
            sub' = \<lambda>v. if v = ''a'' then plug h \<phi> \<chi>
                       else if v = ''b'' then plug h \<psi> \<chi> else Atom v;
            s1 = max (len_formula \<phi>) (len_formula \<psi>);
            s2 = len_formula \<chi>;
            d1 = max (depth_formula \<phi>) (depth_formula \<psi>);
            d2 = depth_formula \<chi>
        in distinguished \<chi> h \<and> contains_atom \<chi> h
             \<and> formula_well_formed (alphabet F) \<chi> \<longrightarrow>
        (\<exists> pr. valid_proof F pr \<and>
           assumptions pr = {sub_formula sub conn_iff} \<and>
           frege_proof.thesis pr = (sub_formula sub' conn_iff) \<and>
           length (steps pr) \<le> poly congbnd s2 \<and>
           (\<forall> step \<in> set (steps pr). len_formula step \<le> poly congbnd (s1 + s2) \<and>
                                     depth_formula step \<le> d1 + d2 + congc)))"
    by blast
  show ?thesis
  proof (intro exI[where x = congbnd] exI[where x = congc] allI impI)
    fix \<phi> \<psi> \<chi> :: "'c formula" and h :: string and l s d :: nat
    assume A: "provable_balanced_iff \<phi> \<psi> l s d \<and> distinguished \<chi> h
                 \<and> contains_atom \<chi> h \<and> formula_well_formed (alphabet F) \<chi>"
    hence prem: "provable_balanced_iff \<phi> \<psi> l s d"
      and dist: "distinguished \<chi> h" and cont: "contains_atom \<chi> h"
      and wfc: "formula_well_formed (alphabet F) \<chi>" by simp_all

    from prem obtain p1 where p1:
      "valid_proof F p1" "assumptions p1 = {}"
      "frege_proof.thesis p1 = iff_form \<phi> \<psi>"
      "length (steps p1) \<le> l"
      "\<forall>x \<in> set (steps p1). len_formula x \<le> s"
      "\<forall>x \<in> set (steps p1). depth_formula x \<le> d"
      unfolding provable_balanced_iff_def by blast

    have eqL: "sub_formula (\<lambda>v. if v = ''a'' then \<phi> else if v = ''b'' then \<psi>
                                else Atom v) conn_iff = iff_form \<phi> \<psi>"
      by (simp add: iff_form_def iff_sub_def)
    have eqR: "sub_formula (\<lambda>v. if v = ''a'' then plug h \<phi> \<chi>
                                else if v = ''b'' then plug h \<psi> \<chi> else Atom v) conn_iff
             = iff_form (plug h \<phi> \<chi>) (plug h \<psi> \<chi>)"
      by (simp add: iff_form_def iff_sub_def)

    have raw: "\<exists> pr. valid_proof F pr \<and>
        assumptions pr = {sub_formula (\<lambda>v. if v = ''a'' then \<phi>
                            else if v = ''b'' then \<psi> else Atom v) conn_iff} \<and>
        frege_proof.thesis pr = sub_formula (\<lambda>v. if v = ''a'' then plug h \<phi> \<chi>
                            else if v = ''b'' then plug h \<psi> \<chi> else Atom v) conn_iff \<and>
        length (steps pr) \<le> poly congbnd (len_formula \<chi>) \<and>
        (\<forall> step \<in> set (steps pr).
           len_formula step \<le> poly congbnd
             (max (len_formula \<phi>) (len_formula \<psi>) + len_formula \<chi>) \<and>
           depth_formula step \<le> max (depth_formula \<phi>) (depth_formula \<psi>)
             + depth_formula \<chi> + congc)"
      using IC[unfolded Let_def] dist cont wfc by blast
    note raw' = raw[unfolded eqL eqR]
    from raw' obtain pc where pc:
      "valid_proof F pc"
      "assumptions pc = {iff_form \<phi> \<psi>}"
      "frege_proof.thesis pc = iff_form (plug h \<phi> \<chi>) (plug h \<psi> \<chi>)"
      "length (steps pc) \<le> poly congbnd (len_formula \<chi>)"
      "\<forall>x \<in> set (steps pc). len_formula x \<le> poly congbnd
          (max (len_formula \<phi>) (len_formula \<psi>) + len_formula \<chi>)"
      "\<forall>x \<in> set (steps pc). depth_formula x \<le>
          max (depth_formula \<phi>) (depth_formula \<psi>) + depth_formula \<chi> + congc"
      by blast

    have phipsi_in: "iff_form \<phi> \<psi> \<in> set (steps p1)"
    proof -
      have ne: "steps p1 \<noteq> []" using p1(1) unfolding valid_proof_def by simp
      have "frege_proof.thesis p1 = last (steps p1)"
        using p1(1) unfolding valid_proof_def by simp
      hence "iff_form \<phi> \<psi> = last (steps p1)" using p1(3) by simp
      thus ?thesis using ne by (simp add: last_in_set)
    qed

    define cb where cb_def: "cb = combine_proofs p1 pc"
    have valid_cb: "valid_proof F cb"
      unfolding cb_def
      using frege_system.combining_valid_proofs[OF fs_F] p1(1) pc(1) by blast
    have cb_steps: "steps cb = steps p1 @ steps pc"
      unfolding cb_def by simp
    have cb_asm: "assumptions cb = {}"
    proof -
      have "assumptions cb = assumptions p1 \<union> (assumptions pc - set (steps p1))"
        unfolding cb_def by simp
      also have "\<dots> = {} \<union> ({iff_form \<phi> \<psi>} - set (steps p1))"
        using p1(2) pc(2) by simp
      also have "\<dots> = {}" using phipsi_in by blast
      finally show ?thesis .
    qed
    have cb_thesis: "frege_proof.thesis cb
                   = iff_form (plug h \<phi> \<chi>) (plug h \<psi> \<chi>)"
      unfolding cb_def using pc(3) by simp
    have cb_lines: "length (steps cb) \<le> l + poly congbnd (len_formula \<chi>)"
      using cb_steps p1(4) pc(4) by simp
    have cb_len: "\<forall>x \<in> set (steps cb). len_formula x
                    \<le> max s (poly congbnd
                        (max (len_formula \<phi>) (len_formula \<psi>) + len_formula \<chi>))"
    proof
      fix x assume "x \<in> set (steps cb)"
      hence "x \<in> set (steps p1) \<or> x \<in> set (steps pc)" using cb_steps by auto
      thus "len_formula x \<le> max s (poly congbnd
              (max (len_formula \<phi>) (len_formula \<psi>) + len_formula \<chi>))"
      proof
        assume "x \<in> set (steps p1)"
        hence "len_formula x \<le> s" using p1(5) by blast
        thus ?thesis by simp
      next
        assume "x \<in> set (steps pc)"
        hence "len_formula x \<le> poly congbnd
                 (max (len_formula \<phi>) (len_formula \<psi>) + len_formula \<chi>)"
          using pc(5) by blast
        thus ?thesis by simp
      qed
    qed
    have cb_dep: "\<forall>x \<in> set (steps cb). depth_formula x
                    \<le> max d (max (depth_formula \<phi>) (depth_formula \<psi>)
                             + depth_formula \<chi> + congc)"
    proof
      fix x assume "x \<in> set (steps cb)"
      hence "x \<in> set (steps p1) \<or> x \<in> set (steps pc)" using cb_steps by auto
      thus "depth_formula x \<le> max d (max (depth_formula \<phi>) (depth_formula \<psi>)
              + depth_formula \<chi> + congc)"
      proof
        assume "x \<in> set (steps p1)"
        hence "depth_formula x \<le> d" using p1(6) by blast
        thus ?thesis by simp
      next
        assume "x \<in> set (steps pc)"
        hence "depth_formula x \<le> max (depth_formula \<phi>) (depth_formula \<psi>)
                 + depth_formula \<chi> + congc" using pc(6) by blast
        thus ?thesis by simp
      qed
    qed

    show "provable_balanced_iff (plug h \<phi> \<chi>) (plug h \<psi> \<chi>)
            (l + poly congbnd (len_formula \<chi>))
            (max s (poly congbnd
                      (max (len_formula \<phi>) (len_formula \<psi>) + len_formula \<chi>)))
            (max d (max (depth_formula \<phi>) (depth_formula \<psi>)
                    + depth_formula \<chi> + congc))"
      unfolding provable_balanced_iff_def
      using valid_cb cb_asm cb_thesis cb_lines cb_len cb_dep by blast
  qed
qed

(*
  Naming the context-congruence cost: cong_poly bounds the line-count and
  per-line-size overhead, cong_const the per-line-depth overhead. Defined as
  SOME witnesses of plug_cong_exists, they turn that existential into the named
  lemma plug_cong with explicit, composable bounds.
*)
definition cong_body :: "nat \<Rightarrow> nat poly \<Rightarrow> bool" where
  "cong_body congc congbnd \<longleftrightarrow>
     (\<forall> \<phi> \<psi> \<chi> h l s d.
        provable_balanced_iff \<phi> \<psi> l s d \<and> distinguished \<chi> h
          \<and> contains_atom \<chi> h \<and> formula_well_formed (alphabet F) \<chi>
        \<longrightarrow> provable_balanced_iff (plug h \<phi> \<chi>) (plug h \<psi> \<chi>)
              (l + poly congbnd (len_formula \<chi>))
              (max s (poly congbnd
                        (max (len_formula \<phi>) (len_formula \<psi>) + len_formula \<chi>)))
              (max d (max (depth_formula \<phi>) (depth_formula \<psi>)
                      + depth_formula \<chi> + congc)))"

lemma cong_body_ex: "\<exists>congc congbnd. cong_body congc congbnd"
  using plug_cong_exists unfolding cong_body_def by blast

definition cong_poly :: "nat poly" where
  "cong_poly = (SOME congbnd. \<exists>congc. cong_body congc congbnd)"

definition cong_const :: nat where
  "cong_const = (SOME congc. cong_body congc cong_poly)"

lemma cong_spec: "cong_body cong_const cong_poly"
proof -
  have "\<exists>congbnd. \<exists>congc. cong_body congc congbnd" using cong_body_ex by blast
  hence "\<exists>congc. cong_body congc cong_poly"
    unfolding cong_poly_def by (rule someI_ex)
  thus ?thesis unfolding cong_const_def by (rule someI_ex)
qed

lemma plug_cong:
  assumes "provable_balanced_iff \<phi> \<psi> l s d"
      and "distinguished \<chi> h" and "contains_atom \<chi> h"
      and "formula_well_formed (alphabet F) \<chi>"
    shows "provable_balanced_iff (plug h \<phi> \<chi>) (plug h \<psi> \<chi>)
             (l + poly cong_poly (len_formula \<chi>))
             (max s (poly cong_poly
                       (max (len_formula \<phi>) (len_formula \<psi>) + len_formula \<chi>)))
             (max d (max (depth_formula \<phi>) (depth_formula \<psi>)
                     + depth_formula \<chi> + cong_const))"
  using cong_spec assms unfolding cong_body_def by blast

(*
  Per-connective reassociation: pushing a balance out through a connective.
  Placing balance p q r at argument slot i of c is equivalent to the balance
  whose two branches place p resp. q at slot i. A fixed (per c, i) tautology
  over fresh atoms; the construction below substitutes it to actual formulas.
*)
subsection \<open>Selector reassociation for a general connective\<close>

definition reassoc_conn_atoms :: "'c \<Rightarrow> string list" where
  "reassoc_conn_atoms c = fresh_atoms (arity (alphabet F) c + 3)"

definition reassoc_conn_slots :: "'c \<Rightarrow> string list" where
  "reassoc_conn_slots c = take (arity (alphabet F) c) (reassoc_conn_atoms c)"

definition reassoc_conn_p :: "'c \<Rightarrow> string" where
  "reassoc_conn_p c = reassoc_conn_atoms c ! (arity (alphabet F) c)"

definition reassoc_conn_q :: "'c \<Rightarrow> string" where
  "reassoc_conn_q c = reassoc_conn_atoms c ! (arity (alphabet F) c + 1)"

definition reassoc_conn_r :: "'c \<Rightarrow> string" where
  "reassoc_conn_r c = reassoc_conn_atoms c ! (arity (alphabet F) c + 2)"

definition reassoc_conn_lhs :: "'c \<Rightarrow> nat \<Rightarrow> 'c formula" where
  "reassoc_conn_lhs c i =
     Conn c ((map Atom (reassoc_conn_slots c))
               [i := balance (Atom (reassoc_conn_p c)) (Atom (reassoc_conn_q c))
                             (Atom (reassoc_conn_r c))])"

definition reassoc_conn_rhs :: "'c \<Rightarrow> nat \<Rightarrow> 'c formula" where
  "reassoc_conn_rhs c i =
     balance (Conn c ((map Atom (reassoc_conn_slots c))[i := Atom (reassoc_conn_p c)]))
             (Conn c ((map Atom (reassoc_conn_slots c))[i := Atom (reassoc_conn_q c)]))
             (Atom (reassoc_conn_r c))"

lemma reassoc_conn_taut:
  "\<forall>val. eval (alphabet F) val
           (iff_form (reassoc_conn_lhs c i) (reassoc_conn_rhs c i))"
proof (intro allI)
  fix val
  let ?ev = "eval (alphabet F) val"
  let ?L = "map ?ev (map Atom (reassoc_conn_slots c))"
  let ?R = "?ev (Atom (reassoc_conn_r c))"
  let ?P = "?ev (Atom (reassoc_conn_p c))"
  let ?Q = "?ev (Atom (reassoc_conn_q c))"
  have lhs: "?ev (reassoc_conn_lhs c i)
           = conn_evals (alphabet F) c (?L[i := (if ?R then ?P else ?Q)])"
    unfolding reassoc_conn_lhs_def
    by (simp add: balance_eval map_update del: balance.simps)
  have rhs: "?ev (reassoc_conn_rhs c i)
           = (if ?R then conn_evals (alphabet F) c (?L[i := ?P])
              else conn_evals (alphabet F) c (?L[i := ?Q]))"
    unfolding reassoc_conn_rhs_def
    by (simp add: balance_eval map_update del: balance.simps)
  have "?ev (reassoc_conn_lhs c i) = ?ev (reassoc_conn_rhs c i)"
    unfolding lhs rhs by (cases ?R) simp_all
  thus "?ev (iff_form (reassoc_conn_lhs c i) (reassoc_conn_rhs c i))"
    by (simp add: iff_form_eval)
qed

lemma reassoc_conn_atoms_spec:
  "length (reassoc_conn_atoms c) = arity (alphabet F) c + 3
   \<and> distinct (reassoc_conn_atoms c)
   \<and> set (reassoc_conn_atoms c) \<inter> avoid_atoms = {}"
  unfolding reassoc_conn_atoms_def
  using fresh_atoms_spec[of "arity (alphabet F) c + 3"] by simp

definition reassoc_conn_lines :: "'c \<Rightarrow> nat \<Rightarrow> nat" where
  "reassoc_conn_lines c i =
     length (steps (taut_proof (iff_form (reassoc_conn_lhs c i)
                                         (reassoc_conn_rhs c i))))"

definition reassoc_conn_step_len :: "'c \<Rightarrow> nat \<Rightarrow> nat" where
  "reassoc_conn_step_len c i =
     Max (insert 1 (len_formula ` set (steps (taut_proof
            (iff_form (reassoc_conn_lhs c i) (reassoc_conn_rhs c i))))))"

definition reassoc_conn_step_depth :: "'c \<Rightarrow> nat \<Rightarrow> nat" where
  "reassoc_conn_step_depth c i =
     Max (insert 1 (depth_formula ` set (steps (taut_proof
            (iff_form (reassoc_conn_lhs c i) (reassoc_conn_rhs c i))))))"

lemma reassoc_conn_proof:
  "provable_balanced_iff (reassoc_conn_lhs c i) (reassoc_conn_rhs c i)
     (reassoc_conn_lines c i) (reassoc_conn_step_len c i)
     (reassoc_conn_step_depth c i)"
  using iff_from_taut[OF reassoc_conn_taut]
  unfolding reassoc_conn_lines_def reassoc_conn_step_len_def
            reassoc_conn_step_depth_def .

(*
  The substitution lifting the per-connective reassociation tautology to actual
  sibling formulas: the k slot atoms map to the siblings gs, and the three mux
  atoms p, q, r map to E, F, Z respectively.
*)
definition reassoc_conn_sub ::
  "'c \<Rightarrow> 'c formula list \<Rightarrow> 'c formula \<Rightarrow> 'c formula \<Rightarrow> 'c formula
   \<Rightarrow> (string \<Rightarrow> 'c formula)" where
  "reassoc_conn_sub c gs E G Z =
     (\<lambda>v. case map_of (zip (reassoc_conn_atoms c) (gs @ [E, G, Z])) v of
            None \<Rightarrow> Atom v | Some f \<Rightarrow> f)"

lemma reassoc_conn_subst:
  assumes len_gs: "length gs = arity (alphabet F) c"
  shows "provable_balanced_iff
           (Conn c (gs[i := balance E G Z]))
           (balance (Conn c (gs[i := E])) (Conn c (gs[i := G])) Z)
           (reassoc_conn_lines c i)
           (reassoc_conn_step_len c i
              * len_sub (set (reassoc_conn_atoms c)) (reassoc_conn_sub c gs E G Z))
           (reassoc_conn_step_depth c i
              + depth_sub (set (reassoc_conn_atoms c)) (reassoc_conn_sub c gs E G Z))"
proof -
  let ?k = "arity (alphabet F) c"
  let ?atoms = "reassoc_conn_atoms c"
  let ?vals = "gs @ [E, G, Z]"
  let ?slots = "reassoc_conn_slots c"
  let ?sub = "reassoc_conn_sub c gs E G Z"

  have alen: "length ?atoms = ?k + 3" using reassoc_conn_atoms_spec by simp
  have adist: "distinct ?atoms" using reassoc_conn_atoms_spec by simp
  have adisj: "set ?atoms \<inter> avoid_atoms = {}" using reassoc_conn_atoms_spec by simp
  have vlen: "length ?vals = ?k + 3" using len_gs by simp
  have lveq: "length ?atoms = length ?vals" using alen vlen by simp
  have slots_len: "length ?slots = ?k"
    unfolding reassoc_conn_slots_def using alen by simp
  have slots_nth: "\<And>j. j < ?k \<Longrightarrow> ?slots ! j = ?atoms ! j"
    unfolding reassoc_conn_slots_def by (simp add: nth_take)

  have sub_nth: "\<And>j. j < ?k + 3 \<Longrightarrow> ?sub (?atoms ! j) = ?vals ! j"
  proof -
    fix j :: nat assume j: "j < ?k + 3"
    hence "map_of (zip ?atoms ?vals) (?atoms ! j) = Some (?vals ! j)"
      using map_of_zip_nth_lookup[OF adist lveq] alen by simp
    thus "?sub (?atoms ! j) = ?vals ! j"
      unfolding reassoc_conn_sub_def by simp
  qed
  have sub_p: "?sub (reassoc_conn_p c) = E"
  proof -
    have "?sub (reassoc_conn_p c) = ?vals ! ?k"
      using sub_nth[of ?k] unfolding reassoc_conn_p_def by simp
    thus ?thesis using len_gs by (simp add: nth_append)
  qed
  have sub_q: "?sub (reassoc_conn_q c) = G"
  proof -
    have "?sub (reassoc_conn_q c) = ?vals ! (?k + 1)"
      using sub_nth[of "?k + 1"] unfolding reassoc_conn_q_def by simp
    thus ?thesis using len_gs by (simp add: nth_append)
  qed
  have sub_r: "?sub (reassoc_conn_r c) = Z"
  proof -
    have "?sub (reassoc_conn_r c) = ?vals ! (?k + 2)"
      using sub_nth[of "?k + 2"] unfolding reassoc_conn_r_def by simp
    thus ?thesis using len_gs by (simp add: nth_append)
  qed
  have sub_slots: "map ?sub ?slots = gs"
  proof (rule nth_equalityI)
    show "length (map ?sub ?slots) = length gs" using slots_len len_gs by simp
  next
    fix j assume "j < length (map ?sub ?slots)"
    hence j: "j < ?k" using slots_len by simp
    have "map ?sub ?slots ! j = ?sub (?atoms ! j)"
      using j slots_len slots_nth[OF j] by simp
    also have "\<dots> = ?vals ! j" using sub_nth[of j] j by simp
    also have "\<dots> = gs ! j" using j len_gs by (simp add: nth_append)
    finally show "map ?sub ?slots ! j = gs ! j" .
  qed

  have sub_off: "\<And>v. v \<notin> set ?atoms \<Longrightarrow> ?sub v = Atom v"
  proof -
    fix v assume "v \<notin> set ?atoms"
    hence "map_of (zip ?atoms ?vals) v = None" by (rule map_of_zip_None_lookup)
    thus "?sub v = Atom v" unfolding reassoc_conn_sub_def by simp
  qed
  have finVS: "finite (set ?atoms)" by simp
  have sig_id: "\<forall>v. v \<notin> set ?atoms \<longrightarrow> ?sub v = Atom v" using sub_off by blast
  note sig_conn = fresh_sub_conn[OF adisj sig_id]
  note sig_cb = fresh_sub_cb[OF adisj sig_id]

  note subst_pbi = provable_balanced_iff_subst[OF reassoc_conn_proof[of c i] finVS
                                                  sig_id sig_conn]

  have mapslots: "map (sub_formula ?sub) (map Atom ?slots) = gs"
    using sub_slots by (simp add: comp_def)
  have subbal: "sub_formula ?sub (balance (Atom (reassoc_conn_p c))
                  (Atom (reassoc_conn_q c)) (Atom (reassoc_conn_r c)))
              = balance E G Z"
  proof -
    have "sub_formula ?sub (balance (Atom (reassoc_conn_p c))
            (Atom (reassoc_conn_q c)) (Atom (reassoc_conn_r c)))
        = balance (sub_formula ?sub (Atom (reassoc_conn_p c)))
                  (sub_formula ?sub (Atom (reassoc_conn_q c)))
                  (sub_formula ?sub (Atom (reassoc_conn_r c)))"
      by (rule sub_formula_balance[OF sig_cb])
    thus ?thesis by (simp only: sub_formula.simps sub_p sub_q sub_r)
  qed
  have subL: "sub_formula ?sub (reassoc_conn_lhs c i)
            = Conn c (gs[i := balance E G Z])"
    unfolding reassoc_conn_lhs_def
    by (simp only: sub_formula.simps map_update mapslots subbal)
  have subR: "sub_formula ?sub (reassoc_conn_rhs c i)
            = balance (Conn c (gs[i := E])) (Conn c (gs[i := G])) Z"
  proof -
    have eP: "sub_formula ?sub
                (Conn c ((map Atom ?slots)[i := Atom (reassoc_conn_p c)]))
            = Conn c (gs[i := E])"
      by (simp only: sub_formula.simps map_update mapslots sub_p)
    have eQ: "sub_formula ?sub
                (Conn c ((map Atom ?slots)[i := Atom (reassoc_conn_q c)]))
            = Conn c (gs[i := G])"
      by (simp only: sub_formula.simps map_update mapslots sub_q)
    have "sub_formula ?sub (reassoc_conn_rhs c i)
        = balance
            (sub_formula ?sub
               (Conn c ((map Atom ?slots)[i := Atom (reassoc_conn_p c)])))
            (sub_formula ?sub
               (Conn c ((map Atom ?slots)[i := Atom (reassoc_conn_q c)])))
            (sub_formula ?sub (Atom (reassoc_conn_r c)))"
      unfolding reassoc_conn_rhs_def by (rule sub_formula_balance[OF sig_cb])
    thus ?thesis by (simp only: eP eQ sub_formula.simps(1) sub_r)
  qed

  show ?thesis using subst_pbi[unfolded subL subR] by blast
qed

(*
  Closed forms for the substitution measures of the reassociation: the k slot
  atoms map onto the siblings gs and the three mux atoms onto E, G, Z, so the
  substitution size is just the total size of those formulas.
*)
lemma reassoc_conn_sub_map:
  assumes "length gs = arity (alphabet F) c"
  shows "map (reassoc_conn_sub c gs E G Z) (reassoc_conn_atoms c)
       = gs @ [E, G, Z]"
proof -
  have alen: "length (reassoc_conn_atoms c) = arity (alphabet F) c + 3"
    using reassoc_conn_atoms_spec by simp
  have adist: "distinct (reassoc_conn_atoms c)"
    using reassoc_conn_atoms_spec by simp
  have lveq: "length (reassoc_conn_atoms c) = length (gs @ [E, G, Z])"
    using alen assms by simp
  show ?thesis
  proof (rule nth_equalityI)
    show "length (map (reassoc_conn_sub c gs E G Z) (reassoc_conn_atoms c))
          = length (gs @ [E, G, Z])"
      using lveq by simp
  next
    fix j assume "j < length (map (reassoc_conn_sub c gs E G Z)
                               (reassoc_conn_atoms c))"
    hence j: "j < length (reassoc_conn_atoms c)" by simp
    have "map_of (zip (reassoc_conn_atoms c) (gs @ [E, G, Z]))
            (reassoc_conn_atoms c ! j) = Some ((gs @ [E, G, Z]) ! j)"
      using map_of_zip_nth_lookup[OF adist lveq] j by simp
    hence "reassoc_conn_sub c gs E G Z (reassoc_conn_atoms c ! j)
         = (gs @ [E, G, Z]) ! j"
      unfolding reassoc_conn_sub_def by simp
    thus "map (reassoc_conn_sub c gs E G Z) (reassoc_conn_atoms c) ! j
        = (gs @ [E, G, Z]) ! j" using j by simp
  qed
qed

lemma reassoc_conn_len_sub:
  assumes "length gs = arity (alphabet F) c"
  shows "len_sub (set (reassoc_conn_atoms c)) (reassoc_conn_sub c gs E G Z)
       = max 1 (sum_list (map len_formula gs)
                + len_formula E + len_formula G + len_formula Z)"
proof -
  have adist: "distinct (reassoc_conn_atoms c)"
    using reassoc_conn_atoms_spec by simp
  have mapeq: "map (\<lambda>v. len_formula (reassoc_conn_sub c gs E G Z v))
                    (reassoc_conn_atoms c)
             = map len_formula (gs @ [E, G, Z])"
  proof -
    have "map (\<lambda>v. len_formula (reassoc_conn_sub c gs E G Z v))
               (reassoc_conn_atoms c)
        = map len_formula (map (reassoc_conn_sub c gs E G Z)
                                (reassoc_conn_atoms c))"
      by simp
    thus ?thesis using reassoc_conn_sub_map[OF assms] by simp
  qed
  have "(\<Sum>v \<in> set (reassoc_conn_atoms c).
           len_formula (reassoc_conn_sub c gs E G Z v))
      = sum_list (map (\<lambda>v. len_formula (reassoc_conn_sub c gs E G Z v))
                       (reassoc_conn_atoms c))"
    by (simp add: sum_list_distinct_conv_sum_set[OF adist])
  also have "\<dots> = sum_list (map len_formula (gs @ [E, G, Z]))"
    using mapeq by simp
  also have "\<dots> = sum_list (map len_formula gs)
                  + len_formula E + len_formula G + len_formula Z"
    by simp
  finally show ?thesis unfolding len_sub_def by simp
qed

lemma reassoc_conn_depth_sub_le:
  assumes "length gs = arity (alphabet F) c"
  shows "depth_sub (set (reassoc_conn_atoms c)) (reassoc_conn_sub c gs E G Z)
       \<le> 1 + sum_list (map depth_formula gs)
            + depth_formula E + depth_formula G + depth_formula Z"
proof -
  let ?L = "map depth_formula (gs @ [E, G, Z])"
  have mapeq: "map (\<lambda>v. depth_formula (reassoc_conn_sub c gs E G Z v))
                    (reassoc_conn_atoms c)
             = map depth_formula (gs @ [E, G, Z])"
  proof -
    have "map (\<lambda>v. depth_formula (reassoc_conn_sub c gs E G Z v))
               (reassoc_conn_atoms c)
        = map depth_formula (map (reassoc_conn_sub c gs E G Z)
                                  (reassoc_conn_atoms c))"
      by simp
    thus ?thesis using reassoc_conn_sub_map[OF assms] by simp
  qed
  have key: "(\<lambda>v. depth_formula (reassoc_conn_sub c gs E G Z v))
               ` set (reassoc_conn_atoms c) = set ?L"
  proof -
    have "(\<lambda>v. depth_formula (reassoc_conn_sub c gs E G Z v))
            ` set (reassoc_conn_atoms c)
        = set (map (\<lambda>v. depth_formula (reassoc_conn_sub c gs E G Z v))
                    (reassoc_conn_atoms c))"
      by simp
    thus ?thesis using mapeq by simp
  qed
  have "depth_sub (set (reassoc_conn_atoms c)) (reassoc_conn_sub c gs E G Z)
      = Max (insert 1 (set ?L))"
    unfolding depth_sub_def using key by simp
  also have "\<dots> \<le> 1 + sum_list ?L"
  proof (rule Max.boundedI)
    show "finite (insert 1 (set ?L))" by simp
    show "insert 1 (set ?L) \<noteq> {}" by simp
    fix e assume "e \<in> insert 1 (set ?L)"
    thus "e \<le> 1 + sum_list ?L"
    proof
      assume "e = 1" thus ?thesis by simp
    next
      assume "e \<in> set ?L"
      hence "e \<le> sum_list ?L" by (rule member_le_sum_list) simp
      thus ?thesis by simp
    qed
  qed
  also have "1 + sum_list ?L
           = 1 + sum_list (map depth_formula gs)
               + depth_formula E + depth_formula G + depth_formula Z"
    by simp
  finally show ?thesis .
qed

(*
  Uniform cost bounds for the per-connective reassociation. The (c, i) index
  set is finite (finite alphabet, bounded arities), so the maxima below are
  genuine constants --- this is what lets the Shannon assembly bound proof
  sizes despite taut_proof carrying no size spec.
*)
definition reassoc_index_set :: "('c \<times> nat) set" where
  "reassoc_index_set = (SIGMA c:(UNIV :: 'c set). {..< arity (alphabet F) c})"

lemma reassoc_index_set_finite: "finite reassoc_index_set"
proof -
  have "finite (UNIV :: 'c set)"
    by (meson frege_balancing_axioms frege_balancing_def
              frege_system.finite_alphabet)
  thus ?thesis unfolding reassoc_index_set_def by simp
qed

definition reassoc_max_lines :: nat where
  "reassoc_max_lines =
     Max (insert 0 ((\<lambda>(c,i). reassoc_conn_lines c i) ` reassoc_index_set))"

definition reassoc_max_step_len :: nat where
  "reassoc_max_step_len =
     Max (insert 0 ((\<lambda>(c,i). reassoc_conn_step_len c i) ` reassoc_index_set))"

definition reassoc_max_step_depth :: nat where
  "reassoc_max_step_depth =
     Max (insert 0 ((\<lambda>(c,i). reassoc_conn_step_depth c i) ` reassoc_index_set))"

\<comment> \<open>Shared shape of the three _le bounds: f(c,i) for (c,i) in the finite
    reassoc_index_set is bounded by Max over that set.\<close>
lemma reassoc_max_ge:
  fixes f :: "'c \<Rightarrow> nat \<Rightarrow> nat"
  assumes "i < arity (alphabet F) c"
  shows "f c i \<le> Max (insert 0 ((\<lambda>(c,i). f c i) ` reassoc_index_set))"
proof -
  have "f c i \<in> insert 0 ((\<lambda>(c,i). f c i) ` reassoc_index_set)"
    using assms unfolding reassoc_index_set_def by auto
  thus ?thesis using reassoc_index_set_finite by simp
qed

lemma reassoc_conn_lines_le:
  assumes "i < arity (alphabet F) c"
  shows "reassoc_conn_lines c i \<le> reassoc_max_lines"
  using reassoc_max_ge[OF assms, of reassoc_conn_lines]
  unfolding reassoc_max_lines_def .

lemma reassoc_conn_step_len_le:
  assumes "i < arity (alphabet F) c"
  shows "reassoc_conn_step_len c i \<le> reassoc_max_step_len"
  using reassoc_max_ge[OF assms, of reassoc_conn_step_len]
  unfolding reassoc_max_step_len_def .

lemma reassoc_conn_step_depth_le:
  assumes "i < arity (alphabet F) c"
  shows "reassoc_conn_step_depth c i \<le> reassoc_max_step_depth"
  using reassoc_max_ge[OF assms, of reassoc_conn_step_depth]
  unfolding reassoc_max_step_depth_def .

(*
  Below threshold spira_trans is the identity, so rebalancing collapses to a
  plain Shannon split: balance of the two fixings over the subterm.
*)
subsection \<open>Position and size lemmas for the Shannon construction\<close>

lemma rebalancing_below_eq:
  assumes wf: "formula_well_formed (alphabet F) P"
      and small: "len_formula P < spira_threshold"
      and vp: "valid_position P pos"
    shows "rebalancing P pos
         = balance (fix_at pos True P) (fix_at pos False P) (subterm_at P pos)"
proof -
  have idT: "spira_trans (fix_at pos True P) = fix_at pos True P"
  proof (rule spira_trans_id_when_small)
    show "formula_well_formed (alphabet F) (fix_at pos True P)"
      by (rule fix_at_wf[OF wf])
    have "len_formula (fix_at pos True P) \<le> len_formula P"
      by (rule fix_at_len_le)
    thus "len_formula (fix_at pos True P) < spira_threshold" using small by simp
  qed
  have idF: "spira_trans (fix_at pos False P) = fix_at pos False P"
  proof (rule spira_trans_id_when_small)
    show "formula_well_formed (alphabet F) (fix_at pos False P)"
      by (rule fix_at_wf[OF wf])
    have "len_formula (fix_at pos False P) \<le> len_formula P"
      by (rule fix_at_len_le)
    thus "len_formula (fix_at pos False P) < spira_threshold"
      using small by simp
  qed
  have idR: "spira_trans (subterm_at P pos) = subterm_at P pos"
  proof (rule spira_trans_id_when_small)
    show "formula_well_formed (alphabet F) (subterm_at P pos)"
      by (rule subterm_at_wf[OF wf vp])
    have "len_formula (subterm_at P pos) \<le> len_formula P"
      by (rule subterm_at_len_le[OF vp])
    thus "len_formula (subterm_at P pos) < spira_threshold"
      using small by simp
  qed
  show ?thesis
    unfolding rebalancing_def using idT idF idR by simp
qed

lemma rebalancing_below_cons:
  assumes wf: "formula_well_formed (alphabet F) (Conn c fs)"
      and small: "len_formula (Conn c fs) < spira_threshold"
      and vp: "valid_position (Conn c fs) (i # rest)"
    shows "rebalancing (Conn c fs) (i # rest)
         = balance (Conn c (fs[i := fix_at rest True (fs ! i)]))
                   (Conn c (fs[i := fix_at rest False (fs ! i)]))
                   (subterm_at (fs ! i) rest)"
proof -
  have "rebalancing (Conn c fs) (i # rest)
      = balance (fix_at (i # rest) True (Conn c fs))
                (fix_at (i # rest) False (Conn c fs))
                (subterm_at (Conn c fs) (i # rest))"
    by (rule rebalancing_below_eq[OF wf small vp])
  thus ?thesis by simp
qed

lemma contains_atom_iff_var: "contains_atom g h = (h \<in> var_set_form g)"
  by (induction g) auto

lemma distinguished_of_fresh: "h \<notin> var_set_form g \<Longrightarrow> distinguished g h"
  by (induction g) (auto simp: contains_atom_iff_var)

(*
  Congruence under one argument slot of a connective: a balanced proof of
  A \<leftrightarrow> B lifts to one of Conn c (gs[i:=A]) \<leftrightarrow> Conn c (gs[i:=B]). Obtained from
  plug_cong_exists with the single-hole context Conn c (gs[i := Atom h]) for a
  fresh hole atom h.
*)
lemma sum_list_update_le:
  "i < length (xs :: nat list) \<Longrightarrow> v \<le> xs ! i
   \<Longrightarrow> sum_list (xs[i := v]) \<le> sum_list xs"
proof (induction xs arbitrary: i)
  case Nil thus ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (cases i)
    case 0
    have "v \<le> x" using Cons.prems(2) 0 by simp
    hence "v + sum_list xs \<le> x + sum_list xs" by linarith
    thus ?thesis using 0 by simp
  next
    case (Suc i')
    have "i' < length xs" using Cons.prems(1) Suc by simp
    moreover have "v \<le> xs ! i'" using Cons.prems(2) Suc by simp
    ultimately have "sum_list (xs[i' := v]) \<le> sum_list xs"
      using Cons.IH by blast
    thus ?thesis using Suc by simp
  qed
qed

lemma len_formula_conn_hole_le:
  assumes "i < length gs" and "len_formula g \<le> len_formula (gs ! i)"
  shows "len_formula (Conn c (gs[i := g])) \<le> len_formula (Conn c gs)"
proof -
  have "len_formula (Conn c (gs[i := g]))
      = 1 + sum_list ((map len_formula gs)[i := len_formula g])"
    by (simp add: map_update)
  also have "\<dots> \<le> 1 + sum_list (map len_formula gs)"
    using sum_list_update_le[of i "map len_formula gs" "len_formula g"] assms
    by simp
  also have "\<dots> = len_formula (Conn c gs)" by simp
  finally show ?thesis .
qed

lemma depth_formula_conn_hole_le:
  assumes "i < length gs" and "depth_formula g \<le> depth_formula (gs ! i)"
  shows "depth_formula (Conn c (gs[i := g])) \<le> depth_formula (Conn c gs)"
proof -
  have ne: "gs \<noteq> []" using assms(1) by auto
  have fin: "finite (set (map depth_formula gs))" by simp
  have gi_in: "depth_formula (gs ! i) \<in> set (map depth_formula gs)"
    using assms(1) by (metis length_map nth_map nth_mem)
  have dg_le: "depth_formula g \<le> Max (set (map depth_formula gs))"
    using assms(2) Max_ge[OF fin gi_in] by linarith
  have "Max (set (map depth_formula (gs[i := g])))
        \<le> Max (insert (depth_formula g) (set (map depth_formula gs)))"
  proof (rule Max_mono)
    have "set (map depth_formula (gs[i := g]))
        = set ((map depth_formula gs)[i := depth_formula g])"
      by (simp add: map_update)
    also have "\<dots> \<subseteq> insert (depth_formula g) (set (map depth_formula gs))"
      by (rule set_update_subset_insert)
    finally show "set (map depth_formula (gs[i := g]))
          \<subseteq> insert (depth_formula g) (set (map depth_formula gs))" .
    show "set (map depth_formula (gs[i := g])) \<noteq> {}" using ne by simp
    show "finite (insert (depth_formula g) (set (map depth_formula gs)))"
      by simp
  qed
  also have "\<dots> = Max (set (map depth_formula gs))"
  proof -
    have "set (map depth_formula gs) \<noteq> {}" using ne by simp
    hence "Max (insert (depth_formula g) (set (map depth_formula gs)))
         = max (depth_formula g) (Max (set (map depth_formula gs)))"
      using fin by simp
    thus ?thesis using dg_le by (simp add: max.absorb2)
  qed
  finally show ?thesis using ne by simp
qed

(*
  Size bounds for balance: it is a fixed formula (custom_balancing) with its
  three slots substituted, so its size/depth is bounded by that of
  custom_balancing scaled by the slot formulas.
*)
lemma conn_slot_cong:
  assumes prem: "provable_balanced_iff A B l s d"
      and wfgs: "formula_well_formed (alphabet F) (Conn c gs)"
      and i_lt: "i < length gs"
    shows "\<exists> lines sz dep.
             provable_balanced_iff (Conn c (gs[i := A])) (Conn c (gs[i := B]))
               lines sz dep
           \<and> lines \<le> l + poly cong_poly (len_formula (Conn c gs))
           \<and> sz \<le> max s (poly cong_poly (max (len_formula A) (len_formula B)
                                          + len_formula (Conn c gs)))
           \<and> dep \<le> max d (max (depth_formula A) (depth_formula B)
                            + depth_formula (Conn c gs) + cong_const)"
proof -
  have finS: "finite (var_set_form (Conn c gs))" by (rule var_set_form_finite)
  obtain h where h_fresh: "h \<notin> var_set_form (Conn c gs)"
    using ex_new_if_finite[OF infinite_UNIV_listI finS] by blast
  let ?chi = "Conn c (gs[i := Atom h])"

  have contains_chi: "contains_atom ?chi h"
  proof -
    have "Atom h \<in> set (gs[i := Atom h])"
      using i_lt by (metis nth_list_update_eq nth_mem length_list_update)
    hence "\<exists>f \<in> set (gs[i := Atom h]). contains_atom f h"
      by (intro bexI[where x = "Atom h"]) simp_all
    thus ?thesis by simp
  qed
  have ulen: "i < length (gs[i := Atom h])" using i_lt by simp
  have uslot: "contains_atom ((gs[i := Atom h]) ! i) h" using i_lt by simp

  have dist_chi: "distinguished ?chi h"
  proof -
    have all_dist: "\<forall>f \<in> set (gs[i := Atom h]). distinguished f h"
    proof
      fix f assume f_in: "f \<in> set (gs[i := Atom h])"
      show "distinguished f h"
      proof (cases "f = Atom h")
        case True thus ?thesis by simp
      next
        case False
        hence "f \<in> set gs" using f_in set_update_subset_insert by fastforce
        hence "h \<notin> var_set_form f" using h_fresh by auto
        thus ?thesis by (rule distinguished_of_fresh)
      qed
    qed
    have uniq: "\<exists>!j. j < length (gs[i := Atom h])
                     \<and> contains_atom ((gs[i := Atom h]) ! j) h"
    proof (rule ex1I[where a = i])
      show "i < length (gs[i := Atom h])
            \<and> contains_atom ((gs[i := Atom h]) ! i) h"
        using ulen uslot by simp
    next
      fix j assume j: "j < length (gs[i := Atom h])
                       \<and> contains_atom ((gs[i := Atom h]) ! j) h"
      show "j = i"
      proof (rule ccontr)
        assume jne: "j \<noteq> i"
        have "(gs[i := Atom h]) ! j = gs ! j"
          using jne by (simp add: nth_list_update)
        moreover have "gs ! j \<in> set gs" using j i_lt by (simp add: nth_mem)
        ultimately have "h \<notin> var_set_form ((gs[i := Atom h]) ! j)"
          using h_fresh by auto
        hence "\<not> contains_atom ((gs[i := Atom h]) ! j) h"
          by (simp add: contains_atom_iff_var)
        thus False using j by simp
      qed
    qed
    show ?thesis using contains_chi uniq all_dist by simp
  qed

  have wf_chi: "formula_well_formed (alphabet F) ?chi"
  proof -
    have "\<forall>f \<in> set (gs[i := Atom h]). formula_well_formed (alphabet F) f"
    proof
      fix f assume "f \<in> set (gs[i := Atom h])"
      thus "formula_well_formed (alphabet F) f"
      proof (cases "f = Atom h")
        case True thus ?thesis by simp
      next
        case False
        hence "f \<in> set gs"
          using \<open>f \<in> set (gs[i := Atom h])\<close> set_update_subset_insert by fastforce
        thus ?thesis using wfgs by auto
      qed
    qed
    moreover have "length (gs[i := Atom h]) = arity (alphabet F) c"
      using wfgs by auto
    ultimately show ?thesis by auto
  qed

  have plugA: "plug h A ?chi = Conn c (gs[i := A])"
  proof -
    have "plug h A ?chi
        = Conn c ((gs[i := Atom h])[i := plug h A ((gs[i := Atom h]) ! i)])"
      using plug_distinguished_unfold[OF dist_chi contains_chi ulen uslot] .
    also have "\<dots> = Conn c (gs[i := A])"
      using i_lt by (simp add: plug_def)
    finally show ?thesis .
  qed
  have plugB: "plug h B ?chi = Conn c (gs[i := B])"
  proof -
    have "plug h B ?chi
        = Conn c ((gs[i := Atom h])[i := plug h B ((gs[i := Atom h]) ! i)])"
      using plug_distinguished_unfold[OF dist_chi contains_chi ulen uslot] .
    also have "\<dots> = Conn c (gs[i := B])"
      using i_lt by (simp add: plug_def)
    finally show ?thesis .
  qed

  have pc: "provable_balanced_iff (Conn c (gs[i := A])) (Conn c (gs[i := B]))
              (l + poly cong_poly (len_formula ?chi))
              (max s (poly cong_poly
                        (max (len_formula A) (len_formula B) + len_formula ?chi)))
              (max d (max (depth_formula A) (depth_formula B)
                      + depth_formula ?chi + cong_const))"
    using plug_cong[OF prem dist_chi contains_chi wf_chi]
    unfolding plugA plugB .
  have lc: "len_formula ?chi \<le> len_formula (Conn c gs)"
    using len_formula_conn_hole_le[OF i_lt] len_formula_positive[of "gs ! i"]
    by simp
  have dc: "depth_formula ?chi \<le> depth_formula (Conn c gs)"
    using depth_formula_conn_hole_le[OF i_lt] depth_formula_ge_1[of "gs ! i"]
    by simp
  have b1: "l + poly cong_poly (len_formula ?chi)
            \<le> l + poly cong_poly (len_formula (Conn c gs))"
    using poly_nat_mono[OF lc] by simp
  have b2: "max s (poly cong_poly
              (max (len_formula A) (len_formula B) + len_formula ?chi))
            \<le> max s (poly cong_poly
              (max (len_formula A) (len_formula B) + len_formula (Conn c gs)))"
  proof -
    have "poly cong_poly (max (len_formula A) (len_formula B) + len_formula ?chi)
          \<le> poly cong_poly (max (len_formula A) (len_formula B)
                              + len_formula (Conn c gs))"
      by (rule poly_nat_mono[OF add_left_mono[OF lc]])
    thus ?thesis by (rule max.mono[OF order_refl])
  qed
  have b3: "max d (max (depth_formula A) (depth_formula B)
              + depth_formula ?chi + cong_const)
            \<le> max d (max (depth_formula A) (depth_formula B)
              + depth_formula (Conn c gs) + cong_const)"
    using dc by simp
  show ?thesis using pc b1 b2 b3 by blast
qed

(* Supporting size bounds for the Shannon assembly. *)
lemma depth_formula_le_len: "depth_formula f \<le> len_formula f"
proof (induction f)
  case (Atom v) thus ?case by simp
next
  case (Conn c fs)
  show ?case
  proof (cases "fs = []")
    case True thus ?thesis by simp
  next
    case False
    have "depth_formula (Conn c fs) = 1 + Max (set (map depth_formula fs))"
      using False by simp
    also have "Max (set (map depth_formula fs))
             \<le> sum_list (map len_formula fs)"
    proof (rule Max.boundedI)
      show "finite (set (map depth_formula fs))" by simp
      show "set (map depth_formula fs) \<noteq> {}" using False by simp
      fix e assume "e \<in> set (map depth_formula fs)"
      then obtain g where g_in: "g \<in> set fs" and e_eq: "e = depth_formula g"
        by auto
      have "e \<le> len_formula g" using e_eq Conn.IH g_in by auto
      also have "len_formula g \<le> sum_list (map len_formula fs)"
        using g_in by (induction fs) auto
      finally show "e \<le> sum_list (map len_formula fs)" .
    qed
    finally show ?thesis by simp
  qed
qed

lemma valid_position_length_le:
  "valid_position P pos \<Longrightarrow> length pos \<le> len_formula P"
proof (induction pos arbitrary: P)
  case Nil thus ?case by simp
next
  case (Cons i rest)
  obtain c fs where P_eq: "P = Conn c fs"
    using Cons.prems by (cases P) auto
  have i_lt: "i < length fs" using Cons.prems P_eq by simp
  have vp_child: "valid_position (fs ! i) rest" using Cons.prems P_eq by simp
  have "length rest \<le> len_formula (fs ! i)" using Cons.IH vp_child by blast
  also have "len_formula (fs ! i) \<le> sum_list (map len_formula fs)"
  proof -
    have "len_formula (fs ! i) \<in> set (map len_formula fs)"
      using i_lt by (metis length_map nth_map nth_mem)
    thus ?thesis by (rule member_le_sum_list) simp
  qed
  finally show ?case using P_eq by simp
qed

lemma sum_list_update_le2:
  "sum_list ((xs :: nat list)[i := v]) \<le> sum_list xs + v"
proof (induction xs arbitrary: i)
  case Nil thus ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (cases i)
    case 0 thus ?thesis by simp
  next
    case (Suc i')
    have "sum_list (xs[i' := v]) \<le> sum_list xs + v" using Cons.IH by blast
    thus ?thesis using Suc by simp
  qed
qed

lemma len_formula_conn_update_le:
  "len_formula (Conn c (gs[i := g]))
   \<le> len_formula (Conn c gs) + len_formula g"
proof -
  have "len_formula (Conn c (gs[i := g]))
      = 1 + sum_list ((map len_formula gs)[i := len_formula g])"
    by (simp add: map_update)
  also have "\<dots> \<le> 1 + (sum_list (map len_formula gs) + len_formula g)"
    using sum_list_update_le2[of "map len_formula gs" i "len_formula g"]
    by simp
  also have "\<dots> = len_formula (Conn c gs) + len_formula g" by simp
  finally show ?thesis .
qed

lemma len_rebalancing_below_le:
  assumes wf: "formula_well_formed (alphabet F) P"
      and small: "len_formula P < spira_threshold"
      and vp: "valid_position P pos"
    shows "len_formula (rebalancing P pos)
         \<le> len_formula custom_balancing * (3 * len_formula P + 1)"
proof -
  have "len_formula (rebalancing P pos)
      = len_formula (balance (fix_at pos True P) (fix_at pos False P)
                             (subterm_at P pos))"
    by (simp add: rebalancing_below_eq[OF wf small vp])
  also have "\<dots> \<le> len_formula custom_balancing
       * (len_formula (fix_at pos True P) + len_formula (fix_at pos False P)
          + len_formula (subterm_at P pos) + 1)"
    by (rule len_balance_le)
  also have "\<dots> \<le> len_formula custom_balancing * (3 * len_formula P + 1)"
  proof -
    have "len_formula (fix_at pos True P) \<le> len_formula P"
      by (rule fix_at_len_le)
    moreover have "len_formula (fix_at pos False P) \<le> len_formula P"
      by (rule fix_at_len_le)
    moreover have "len_formula (subterm_at P pos) \<le> len_formula P"
      by (rule subterm_at_len_le[OF vp])
    ultimately show ?thesis by (intro mult_le_mono2) simp
  qed
  finally show ?thesis .
qed

(*
  The Shannon construction for the below-threshold case. shannon_M is a single
  generous constant dominating the base case and every per-step glue; since a
  below-threshold formula is bounded, all the per-step costs collapse to it.
*)
subsection \<open>The below-threshold Shannon construction\<close>

definition shannon_balmax :: nat where
  "shannon_balmax = len_formula custom_balancing * (3 * spira_threshold + 1)"

definition shannon_bigarg :: nat where
  "shannon_bigarg = shannon_balmax + 4 * spira_threshold + 4"

definition shannon_M :: nat where
  "shannon_M = pos_empty_lines + pos_empty_step_len * spira_threshold
     + pos_empty_step_depth + spira_threshold + 1
     + poly cong_poly shannon_bigarg
     + reassoc_max_lines + trans_lines
     + reassoc_max_step_len * shannon_bigarg
     + trans_step_len * (3 * shannon_bigarg)
     + reassoc_max_step_depth + cong_const + trans_step_depth
     + 10 * shannon_bigarg"

lemma shannon_step:
  assumes wfP: "formula_well_formed (alphabet F) (Conn c fs)"
      and small: "len_formula (Conn c fs) < spira_threshold"
      and vp: "valid_position (Conn c fs) (i # rest)"
      and IH: "provable_balanced_iff (fs ! i) (rebalancing (fs ! i) rest)
                 lQ szQ depQ"
    shows "\<exists> lines sz dep.
             provable_balanced_iff (Conn c fs)
               (rebalancing (Conn c fs) (i # rest)) lines sz dep
           \<and> lines \<le> lQ + shannon_M
           \<and> sz \<le> szQ + shannon_M
           \<and> dep \<le> max depQ shannon_M"
proof -
  let ?A = "fix_at rest True (fs ! i)"
  let ?B = "fix_at rest False (fs ! i)"
  let ?Z = "subterm_at (fs ! i) rest"
  let ?bal = "balance ?A ?B ?Z"
  let ?mid = "Conn c (fs[i := ?bal])"
  let ?reb = "rebalancing (Conn c fs) (i # rest)"
  have i_lt: "i < length fs" using vp by simp
  have vp_child: "valid_position (fs ! i) rest" using vp by simp
  have wf_child: "formula_well_formed (alphabet F) (fs ! i)"
    using wfP nth_mem[OF i_lt] by auto
  have lenfs: "length fs = arity (alphabet F) c" using wfP by auto
  have child_le: "len_formula (fs ! i) \<le> sum_list (map len_formula fs)"
  proof -
    have "len_formula (fs ! i) \<in> set (map len_formula fs)"
      using i_lt by (metis length_map nth_map nth_mem)
    thus ?thesis by (rule member_le_sum_list) simp
  qed
  have child_lt: "len_formula (fs ! i) < len_formula (Conn c fs)"
    using child_le by simp
  have small_child: "len_formula (fs ! i) < spira_threshold"
    using child_lt small by simp

  have reb_child: "rebalancing (fs ! i) rest = ?bal"
    by (rule rebalancing_below_eq[OF wf_child small_child vp_child])
  have IH': "provable_balanced_iff (fs ! i) ?bal lQ szQ depQ"
    using IH reb_child by simp

  \<comment> \<open>Congruence: Conn c fs \<leftrightarrow> Conn c (fs[i := ?bal]).\<close>
  obtain l1 s1 d1 where csc:
      "provable_balanced_iff (Conn c (fs[i := fs ! i])) ?mid l1 s1 d1"
    and csc_l: "l1 \<le> lQ + poly cong_poly (len_formula (Conn c fs))"
    and csc_s: "s1 \<le> max szQ (poly cong_poly
                  (max (len_formula (fs ! i)) (len_formula ?bal)
                   + len_formula (Conn c fs)))"
    and csc_d: "d1 \<le> max depQ (max (depth_formula (fs ! i)) (depth_formula ?bal)
                  + depth_formula (Conn c fs) + cong_const)"
    using conn_slot_cong[OF IH' wfP i_lt] by blast
  have csc': "provable_balanced_iff (Conn c fs) ?mid l1 s1 d1"
    using csc i_lt by simp

  \<comment> \<open>Reassociation: Conn c (fs[i := ?bal]) \<leftrightarrow> rebalancing (Conn c fs) (i#rest).\<close>
  have reb_cons: "?reb = balance (Conn c (fs[i := ?A])) (Conn c (fs[i := ?B])) ?Z"
    by (rule rebalancing_below_cons[OF wfP small vp])
  have reassoc: "provable_balanced_iff ?mid ?reb
                   (reassoc_conn_lines c i)
                   (reassoc_conn_step_len c i
                      * len_sub (set (reassoc_conn_atoms c))
                                (reassoc_conn_sub c fs ?A ?B ?Z))
                   (reassoc_conn_step_depth c i
                      + depth_sub (set (reassoc_conn_atoms c))
                                  (reassoc_conn_sub c fs ?A ?B ?Z))"
    using reassoc_conn_subst[OF lenfs, of i ?A ?B ?Z] reb_cons by simp

  note chain = iff_trans[OF csc' reassoc]

  \<comment> \<open>Size bounds: every formula is bounded by shannon_bigarg / shannon_balmax.\<close>
  have lenA: "len_formula ?A \<le> len_formula (fs ! i)" by (rule fix_at_len_le)
  have lenB: "len_formula ?B \<le> len_formula (fs ! i)" by (rule fix_at_len_le)
  have lenZ: "len_formula ?Z \<le> len_formula (fs ! i)"
    by (rule subterm_at_len_le[OF vp_child])
  have lenbal: "len_formula ?bal \<le> shannon_balmax"
  proof -
    have "len_formula ?bal \<le> len_formula custom_balancing
            * (len_formula ?A + len_formula ?B + len_formula ?Z + 1)"
      by (rule len_balance_le)
    also have "\<dots> \<le> len_formula custom_balancing * (3 * spira_threshold + 1)"
      using lenA lenB lenZ small_child by (intro mult_le_mono2) simp
    finally show ?thesis unfolding shannon_balmax_def .
  qed
  have lenreb: "len_formula ?reb \<le> shannon_balmax"
  proof -
    have "len_formula ?reb
        \<le> len_formula custom_balancing * (3 * len_formula (Conn c fs) + 1)"
      by (rule len_rebalancing_below_le[OF wfP small vp])
    also have "\<dots> \<le> len_formula custom_balancing * (3 * spira_threshold + 1)"
      using small by (intro mult_le_mono2) simp
    finally show ?thesis unfolding shannon_balmax_def .
  qed
  have lenmid: "len_formula ?mid \<le> len_formula (Conn c fs) + shannon_balmax"
    using len_formula_conn_update_le[of c fs i ?bal] lenbal by simp
  have balmax_ge: "shannon_balmax \<ge> spira_threshold"
  proof -
    have "len_formula custom_balancing \<ge> 1" by (rule len_formula_positive)
    hence "shannon_balmax \<ge> 1 * (3 * spira_threshold + 1)"
      unfolding shannon_balmax_def by (rule mult_le_mono1)
    thus ?thesis by simp
  qed
  have lenP_arg: "len_formula (Conn c fs) \<le> shannon_bigarg"
    using small balmax_ge unfolding shannon_bigarg_def by simp
  have lenmid_arg: "len_formula ?mid \<le> shannon_bigarg"
    using lenmid small unfolding shannon_bigarg_def by simp
  have lenreb_arg: "len_formula ?reb \<le> shannon_bigarg"
    using lenreb unfolding shannon_bigarg_def by simp
  have csc_s_arg: "max (len_formula (fs ! i)) (len_formula ?bal)
                     + len_formula (Conn c fs) \<le> shannon_bigarg"
    using child_lt lenbal small balmax_ge unfolding shannon_bigarg_def by simp

  \<comment> \<open>The substitution-size of the reassociation.\<close>
  have lensub: "len_sub (set (reassoc_conn_atoms c))
                  (reassoc_conn_sub c fs ?A ?B ?Z) \<le> shannon_bigarg"
  proof -
    have "len_sub (set (reassoc_conn_atoms c)) (reassoc_conn_sub c fs ?A ?B ?Z)
        = max 1 (sum_list (map len_formula fs)
                 + len_formula ?A + len_formula ?B + len_formula ?Z)"
      by (rule reassoc_conn_len_sub[OF lenfs])
    also have "\<dots> \<le> shannon_bigarg"
      using child_le lenA lenB lenZ small_child small
      unfolding shannon_bigarg_def shannon_balmax_def by simp
    finally show ?thesis .
  qed
  have depthsub: "depth_sub (set (reassoc_conn_atoms c))
                    (reassoc_conn_sub c fs ?A ?B ?Z) \<le> shannon_bigarg"
  proof -
    have "depth_sub (set (reassoc_conn_atoms c)) (reassoc_conn_sub c fs ?A ?B ?Z)
        \<le> 1 + sum_list (map depth_formula fs)
            + depth_formula ?A + depth_formula ?B + depth_formula ?Z"
      by (rule reassoc_conn_depth_sub_le[OF lenfs])
    also have "\<dots> \<le> 1 + sum_list (map len_formula fs)
            + len_formula ?A + len_formula ?B + len_formula ?Z"
    proof -
      have "sum_list (map depth_formula fs) \<le> sum_list (map len_formula fs)"
        by (intro sum_list_mono) (rule depth_formula_le_len)
      thus ?thesis
        using depth_formula_le_len[of ?A] depth_formula_le_len[of ?B]
              depth_formula_le_len[of ?Z] by linarith
    qed
    also have "\<dots> \<le> shannon_bigarg"
      using child_le lenA lenB lenZ small_child small
      unfolding shannon_bigarg_def shannon_balmax_def by simp
    finally show ?thesis .
  qed

  \<comment> \<open>cong_poly is monotone, so its argument may be replaced by shannon_bigarg.\<close>
  have cong_P: "poly cong_poly (len_formula (Conn c fs))
              \<le> poly cong_poly shannon_bigarg"
    by (rule poly_nat_mono[OF lenP_arg])
  have cong_csc: "poly cong_poly
       (max (len_formula (fs ! i)) (len_formula ?bal) + len_formula (Conn c fs))
       \<le> poly cong_poly shannon_bigarg"
    by (rule poly_nat_mono[OF csc_s_arg])

  \<comment> \<open>The reassociation costs are dominated by their uniform maxima.\<close>
  have rcl: "reassoc_conn_lines c i \<le> reassoc_max_lines"
    using lenfs i_lt by (simp add: reassoc_conn_lines_le)
  have rcs: "reassoc_conn_step_len c i \<le> reassoc_max_step_len"
    using lenfs i_lt by (simp add: reassoc_conn_step_len_le)
  have rcd: "reassoc_conn_step_depth c i \<le> reassoc_max_step_depth"
    using lenfs i_lt by (simp add: reassoc_conn_step_depth_le)

  \<comment> \<open>Line count.\<close>
  have lines_le: "l1 + reassoc_conn_lines c i + trans_lines \<le> lQ + shannon_M"
  proof -
    have "l1 + reassoc_conn_lines c i + trans_lines
        \<le> (lQ + poly cong_poly shannon_bigarg) + reassoc_max_lines + trans_lines"
      using csc_l cong_P rcl by linarith
    thus ?thesis unfolding shannon_M_def by linarith
  qed

  \<comment> \<open>Per-line size.\<close>
  have sz_le: "s1 + reassoc_conn_step_len c i
                 * len_sub (set (reassoc_conn_atoms c))
                           (reassoc_conn_sub c fs ?A ?B ?Z)
               + trans_step_len
                   * (len_formula (Conn c fs) + len_formula ?mid
                      + len_formula ?reb)
             \<le> szQ + shannon_M"
  proof -
    have a1: "s1 \<le> szQ + poly cong_poly shannon_bigarg"
      using csc_s cong_csc by simp
    have a2: "reassoc_conn_step_len c i
                * len_sub (set (reassoc_conn_atoms c))
                          (reassoc_conn_sub c fs ?A ?B ?Z)
            \<le> reassoc_max_step_len * shannon_bigarg"
      using rcs lensub by (rule mult_le_mono)
    have a3: "len_formula (Conn c fs) + len_formula ?mid + len_formula ?reb
            \<le> 3 * shannon_bigarg"
      using lenP_arg lenmid_arg lenreb_arg by linarith
    have a3': "trans_step_len
                 * (len_formula (Conn c fs) + len_formula ?mid + len_formula ?reb)
             \<le> trans_step_len * (3 * shannon_bigarg)"
      using a3 by (rule mult_le_mono2)
    show ?thesis using a1 a2 a3' unfolding shannon_M_def by linarith
  qed

  \<comment> \<open>Per-line depth.\<close>
  have dep_le: "max d1 (max (reassoc_conn_step_depth c i
                  + depth_sub (set (reassoc_conn_atoms c))
                              (reassoc_conn_sub c fs ?A ?B ?Z))
                  (trans_step_depth + max (depth_formula (Conn c fs))
                     (max (depth_formula ?mid) (depth_formula ?reb))))
             \<le> max depQ shannon_M"
  proof -
    have dP: "depth_formula (Conn c fs) \<le> shannon_bigarg"
      using depth_formula_le_len[of "Conn c fs"] lenP_arg by linarith
    have dbal: "depth_formula ?bal \<le> shannon_bigarg"
      using depth_formula_le_len[of ?bal] lenbal
      unfolding shannon_bigarg_def by linarith
    have dchild: "depth_formula (fs ! i) \<le> shannon_bigarg"
      using depth_formula_le_len[of "fs ! i"] child_lt lenP_arg by linarith
    have dmid: "depth_formula ?mid \<le> shannon_bigarg"
      using depth_formula_le_len[of ?mid] lenmid_arg by linarith
    have dreb: "depth_formula ?reb \<le> shannon_bigarg"
      using depth_formula_le_len[of ?reb] lenreb_arg by linarith
    have d_csc: "d1 \<le> max depQ shannon_M"
    proof -
      have mcb: "max (depth_formula (fs ! i)) (depth_formula ?bal)
                   \<le> shannon_bigarg"
        using dchild dbal by simp
      have "d1 \<le> max depQ (max (depth_formula (fs ! i)) (depth_formula ?bal)
               + depth_formula (Conn c fs) + cong_const)"
        by (rule csc_d)
      also have "\<dots> \<le> max depQ shannon_M"
      proof (rule max.mono[OF order_refl])
        show "max (depth_formula (fs ! i)) (depth_formula ?bal)
                + depth_formula (Conn c fs) + cong_const \<le> shannon_M"
          using mcb dP unfolding shannon_M_def by linarith
      qed
      finally show ?thesis .
    qed
    have d_reassoc: "reassoc_conn_step_depth c i
                   + depth_sub (set (reassoc_conn_atoms c))
                               (reassoc_conn_sub c fs ?A ?B ?Z)
                 \<le> max depQ shannon_M"
    proof -
      have "reassoc_conn_step_depth c i
              + depth_sub (set (reassoc_conn_atoms c))
                          (reassoc_conn_sub c fs ?A ?B ?Z) \<le> shannon_M"
        using rcd depthsub unfolding shannon_M_def by linarith
      thus ?thesis by simp
    qed
    have d_trans: "trans_step_depth + max (depth_formula (Conn c fs))
                     (max (depth_formula ?mid) (depth_formula ?reb))
                 \<le> max depQ shannon_M"
    proof -
      have "max (depth_formula (Conn c fs))
              (max (depth_formula ?mid) (depth_formula ?reb)) \<le> shannon_bigarg"
        using dP dmid dreb by simp
      hence "trans_step_depth + max (depth_formula (Conn c fs))
               (max (depth_formula ?mid) (depth_formula ?reb)) \<le> shannon_M"
        unfolding shannon_M_def by linarith
      thus ?thesis by simp
    qed
    show ?thesis
      by (rule max.boundedI[OF d_csc max.boundedI[OF d_reassoc d_trans]])
  qed

  have weak: "provable_balanced_iff (Conn c fs) ?reb
                (l1 + reassoc_conn_lines c i + trans_lines)
                (s1 + reassoc_conn_step_len c i
                   * len_sub (set (reassoc_conn_atoms c))
                             (reassoc_conn_sub c fs ?A ?B ?Z)
                 + trans_step_len * (len_formula (Conn c fs)
                     + len_formula ?mid + len_formula ?reb))
                (max d1 (max (reassoc_conn_step_depth c i
                   + depth_sub (set (reassoc_conn_atoms c))
                               (reassoc_conn_sub c fs ?A ?B ?Z))
                   (trans_step_depth + max (depth_formula (Conn c fs))
                      (max (depth_formula ?mid) (depth_formula ?reb)))))"
    using chain .
  show ?thesis using weak lines_le sz_le dep_le by blast
qed

lemma shannon_construction:
  "\<exists> (shgc :: nat) (shbase :: nat).
     \<forall> P pos. formula_well_formed (alphabet F) P \<and> valid_position P pos
                \<and> len_formula P < spira_threshold
     \<longrightarrow> (\<exists> lines sz dep.
            provable_balanced_iff (spira_trans P) (rebalancing P pos)
              lines sz dep
          \<and> lines \<le> length pos * shgc + shbase
          \<and> sz \<le> length pos * shgc + shbase
          \<and> dep \<le> length pos * shgc + shbase)"
proof -
  have main: "\<And>pos P. formula_well_formed (alphabet F) P
        \<Longrightarrow> valid_position P pos \<Longrightarrow> len_formula P < spira_threshold
        \<Longrightarrow> (\<exists> lines sz dep.
               provable_balanced_iff (spira_trans P) (rebalancing P pos)
                 lines sz dep
             \<and> lines \<le> length pos * shannon_M + shannon_M
             \<and> sz \<le> length pos * shannon_M + shannon_M
             \<and> dep \<le> length pos * shannon_M + shannon_M)"
  proof -
    fix pos P
    show "formula_well_formed (alphabet F) P \<Longrightarrow> valid_position P pos
          \<Longrightarrow> len_formula P < spira_threshold
          \<Longrightarrow> (\<exists> lines sz dep.
                 provable_balanced_iff (spira_trans P) (rebalancing P pos)
                   lines sz dep
               \<and> lines \<le> length pos * shannon_M + shannon_M
               \<and> sz \<le> length pos * shannon_M + shannon_M
               \<and> dep \<le> length pos * shannon_M + shannon_M)"
    proof (induction pos arbitrary: P)
      case Nil
      have wfP: "formula_well_formed (alphabet F) P" using Nil.prems by simp
      have small: "len_formula P < spira_threshold" using Nil.prems by simp
      have st: "spira_trans P = P"
        by (rule spira_trans_id_when_small[OF wfP small])
      have mc: "provable_balanced_iff (spira_trans P) (rebalancing P [])
                  pos_empty_lines (pos_empty_step_len * len_formula (spira_trans P))
                  (pos_empty_step_depth + 1 + depth_formula (spira_trans P))"
        using case_pos_empty_construction[of P] .
      have lp: "len_formula (spira_trans P) < spira_threshold"
        using st small by simp
      have dp: "depth_formula (spira_trans P) < spira_threshold"
        using depth_formula_le_len[of "spira_trans P"] lp by simp
      have bl: "pos_empty_lines \<le> length [] * shannon_M + shannon_M"
        unfolding shannon_M_def by simp
      have bs: "pos_empty_step_len * len_formula (spira_trans P)
              \<le> length [] * shannon_M + shannon_M"
      proof -
        have "pos_empty_step_len * len_formula (spira_trans P)
            \<le> pos_empty_step_len * spira_threshold"
          using lp by (intro mult_le_mono2) simp
        thus ?thesis unfolding shannon_M_def by linarith
      qed
      have bd: "pos_empty_step_depth + 1 + depth_formula (spira_trans P)
              \<le> length [] * shannon_M + shannon_M"
        using dp unfolding shannon_M_def by linarith
      show ?case using mc bl bs bd by blast
    next
      case (Cons i rest)
      have wfP: "formula_well_formed (alphabet F) P" using Cons.prems by simp
      have vp: "valid_position P (i # rest)" using Cons.prems by simp
      have small: "len_formula P < spira_threshold" using Cons.prems by simp
      obtain c fs where P_eq: "P = Conn c fs"
        using vp by (cases P) auto
      have i_lt: "i < length fs" using vp P_eq by simp
      have vp_child: "valid_position (fs ! i) rest" using vp P_eq by simp
      have wf_child: "formula_well_formed (alphabet F) (fs ! i)"
        using wfP P_eq nth_mem[OF i_lt] by auto
      have child_le: "len_formula (fs ! i) \<le> sum_list (map len_formula fs)"
      proof -
        have "len_formula (fs ! i) \<in> set (map len_formula fs)"
          using i_lt by (metis length_map nth_map nth_mem)
        thus ?thesis by (rule member_le_sum_list) simp
      qed
      have small_child: "len_formula (fs ! i) < spira_threshold"
        using child_le small P_eq by simp
      obtain lQ szQ depQ where
          IHr: "provable_balanced_iff (spira_trans (fs ! i))
                  (rebalancing (fs ! i) rest) lQ szQ depQ"
        and IHl: "lQ \<le> length rest * shannon_M + shannon_M"
        and IHs: "szQ \<le> length rest * shannon_M + shannon_M"
        and IHd: "depQ \<le> length rest * shannon_M + shannon_M"
        using Cons.IH[OF wf_child vp_child small_child] by blast
      have st_child: "spira_trans (fs ! i) = fs ! i"
        by (rule spira_trans_id_when_small[OF wf_child small_child])
      have IH': "provable_balanced_iff (fs ! i) (rebalancing (fs ! i) rest)
                   lQ szQ depQ"
        using IHr st_child by simp
      obtain lines sz dep where
          SS: "provable_balanced_iff (Conn c fs)
                 (rebalancing (Conn c fs) (i # rest)) lines sz dep"
        and SSl: "lines \<le> lQ + shannon_M"
        and SSs: "sz \<le> szQ + shannon_M"
        and SSd: "dep \<le> max depQ shannon_M"
        using shannon_step[OF wfP[unfolded P_eq] small[unfolded P_eq]
                              vp[unfolded P_eq] IH'] by blast
      have st: "spira_trans P = P"
        by (rule spira_trans_id_when_small[OF wfP small])
      have SS': "provable_balanced_iff (spira_trans P) (rebalancing P (i # rest))
                   lines sz dep"
        using SS st P_eq by simp
      have b_lines: "lines \<le> length (i # rest) * shannon_M + shannon_M"
        using SSl IHl by simp
      have b_sz: "sz \<le> length (i # rest) * shannon_M + shannon_M"
        using SSs IHs by simp
      have b_dep: "dep \<le> length (i # rest) * shannon_M + shannon_M"
        using SSd IHd by simp
      show ?case using SS' b_lines b_sz b_dep by blast
    qed
  qed
  show ?thesis
  proof (rule exI[where x = shannon_M], rule exI[where x = shannon_M],
         intro allI impI)
    fix P :: "'c formula" and pos :: "nat list"
    assume A: "formula_well_formed (alphabet F) P \<and> valid_position P pos
                 \<and> len_formula P < spira_threshold"
    show "\<exists> lines sz dep.
            provable_balanced_iff (spira_trans P) (rebalancing P pos)
              lines sz dep
          \<and> lines \<le> length pos * shannon_M + shannon_M
          \<and> sz \<le> length pos * shannon_M + shannon_M
          \<and> dep \<le> length pos * shannon_M + shannon_M"
      using main[OF conjunct1[OF A] conjunct1[OF conjunct2[OF A]]
                    conjunct2[OF conjunct2[OF A]]] .
  qed
qed

(*
  The L(n,m) polynomial line-count bound (Lemma 5.1, Filmus section 5). The
  three case recurrences collapse, via L(n,m) = max ell(P,R), to
    L(n,m) <= O(n) + 2 L(cn,cn) + 2 L(m,cn),   cn = kk/(kk+1) * n
  where kk = max arity (the Spira contraction ratio). The closed form
  L n m = A*n^d + 2*A*m^d with d = 10*(2*kk+1) absorbs this because
  (2*kk+2)^d >= 11*(2*kk+1)^d, i.e. 10 cn^d < n^d.
*)
subsection \<open>The polynomial-bound machinery\<close>

lemma pow_succ_lower:
  fixes x :: nat
  shows "x ^ Suc n + Suc n * x ^ n \<le> (x + 1) ^ Suc n"
proof (induction n)
  case 0 thus ?case by simp
next
  case (Suc n)
  have "x ^ Suc (Suc n) + Suc (Suc n) * x ^ Suc n
        \<le> (x + 1) * (x ^ Suc n + Suc n * x ^ n)"
    by (simp add: algebra_simps)
  also have "\<dots> \<le> (x + 1) * (x + 1) ^ Suc n"
    using Suc.IH by (rule mult_le_mono2)
  also have "\<dots> = (x + 1) ^ Suc (Suc n)" by simp
  finally show ?case .
qed

lemma pow_ratio_key:
  fixes x :: nat
  assumes "x \<ge> 1"
  shows "11 * x ^ (10 * x) \<le> (x + 1) ^ (10 * x)"
proof -
  obtain e where e: "10 * x = Suc e"
    using assms by (cases "10 * x") auto
  have "x ^ (10 * x) + 10 * x * x ^ e \<le> (x + 1) ^ (10 * x)"
    using pow_succ_lower[of x e] e by simp
  moreover have "x ^ (10 * x) + 10 * x * x ^ e = 11 * x ^ (10 * x)"
  proof -
    have "x ^ (10 * x) = x * x ^ e" using e by simp
    thus ?thesis by (simp add: algebra_simps)
  qed
  ultimately show ?thesis by simp
qed

lemma pow_ratio_ge:
  fixes x :: nat
  assumes x1: "x \<ge> 1" and e: "e \<ge> 10 * x"
  shows "11 * x ^ e \<le> (x + 1) ^ e"
proof -
  have "11 * x ^ e = 11 * (x ^ (10 * x) * x ^ (e - 10 * x))"
    using e by (simp add: power_add[symmetric])
  also have "\<dots> = 11 * x ^ (10 * x) * x ^ (e - 10 * x)"
    by (simp add: mult.assoc)
  also have "\<dots> \<le> (x + 1) ^ (10 * x) * x ^ (e - 10 * x)"
    using pow_ratio_key[OF x1] by (rule mult_le_mono1)
  also have "\<dots> \<le> (x + 1) ^ (10 * x) * (x + 1) ^ (e - 10 * x)"
    by (intro mult_le_mono2 power_mono) simp_all
  also have "\<dots> = (x + 1) ^ e"
    using e by (simp add: power_add[symmetric])
  finally show ?thesis .
qed

definition rebal_kk :: nat where
  "rebal_kk = max (Max ((arity (alphabet F)) ` (UNIV :: 'c set))) 2"

\<comment> \<open>The spira_trans size polynomial, fixed globally so rebal_deg can be
    sized to dominate its degree (needed for the size bound, not just lines).\<close>
definition rebal_tb :: "nat poly" where
  "rebal_tb = (SOME p :: nat poly. \<forall> f :: 'c formula.
                 formula_well_formed (alphabet F) f \<longrightarrow>
                 len_formula (spira_trans f) \<le> poly p (len_formula f))"

lemma rebal_tb_spec:
  assumes "formula_well_formed (alphabet F) f"
  shows "len_formula (spira_trans f) \<le> poly rebal_tb (len_formula f)"
  using someI_ex[OF trans_b] assms unfolding rebal_tb_def by blast

\<comment> \<open>Leaf bounds shared by every recursive case of the main induction: the Spira
    transform of any subformula of size \<le> N has size \<le> poly rebal_tb N, and
    (given Spira's depth theorem tc_spec) depth \<le> max tc 1 * log 2 (N+1).\<close>
lemma spira_trans_len_le_tb:
  assumes "formula_well_formed (alphabet F) L" and "len_formula L \<le> N"
  shows "len_formula (spira_trans L) \<le> poly rebal_tb N"
proof -
  have "len_formula (spira_trans L) \<le> poly rebal_tb (len_formula L)"
    by (rule rebal_tb_spec[OF assms(1)])
  also have "\<dots> \<le> poly rebal_tb N" by (rule poly_nat_mono[OF assms(2)])
  finally show ?thesis .
qed

lemma spira_trans_dep_le:
  assumes tc_spec: "\<forall>f. formula_well_formed (alphabet F) f
                       \<longrightarrow> real (depth_formula (spira_trans f))
                           \<le> tc * log 2 (real (len_formula f) + 1)"
      and wfL: "formula_well_formed (alphabet F) L"
      and lLN: "len_formula L \<le> N"
    shows "real (depth_formula (spira_trans L)) \<le> max tc 1 * log 2 (real N + 1)"
proof -
  have l_pos: "(0::real) \<le> log 2 (real (len_formula L) + 1)"
  proof -
    have "(1::real) \<le> real (len_formula L) + 1"
      using len_formula_positive[of L] by simp
    hence "log 2 1 \<le> log 2 (real (len_formula L) + 1)" by (intro log_mono) auto
    thus ?thesis by simp
  qed
  have logLN: "log 2 (real (len_formula L) + 1) \<le> log 2 (real N + 1)"
    using lLN by (intro log_mono) auto
  have mtc: "(0::real) \<le> max tc 1" by (simp add: le_max_iff_disj)
  have "real (depth_formula (spira_trans L))
      \<le> tc * log 2 (real (len_formula L) + 1)"
    using tc_spec wfL by blast
  also have "\<dots> \<le> max tc 1 * log 2 (real (len_formula L) + 1)"
    using l_pos by (intro mult_right_mono) auto
  also have "\<dots> \<le> max tc 1 * log 2 (real N + 1)"
    using logLN mtc by (intro mult_left_mono)
  finally show ?thesis .
qed

definition rebal_deg :: nat where
  "rebal_deg = max (10 * (2 * rebal_kk + 1)) (degree rebal_tb)"

lemma rebal_deg_ge: "rebal_deg \<ge> 10 * (2 * rebal_kk + 1)"
  unfolding rebal_deg_def by simp

lemma rebal_deg_ge_tb: "rebal_deg \<ge> degree rebal_tb"
  unfolding rebal_deg_def by simp

lemma rebal_pow_key:
  "11 * (2 * rebal_kk + 1) ^ rebal_deg \<le> (2 * rebal_kk + 2) ^ rebal_deg"
proof -
  have "11 * (2 * rebal_kk + 1) ^ rebal_deg
        \<le> ((2 * rebal_kk + 1) + 1) ^ rebal_deg"
    using rebal_deg_ge by (intro pow_ratio_ge) simp_all
  thus ?thesis by simp
qed

\<comment> \<open>rebal_cn has additive slack 2 (not 1): the recursive sub-problem
    (fix_at pos b P, spira_pos) lands at L-second-argument |P| - |Q| + 1, and
    |P| - |Q| \<le> rebal_kk * |P| div (rebal_kk + 1) + 1 (spira_sel_lower has a
    +rebal_kk slack, fix_at adds +1) --- so +2 is needed for it to fit rebal_cn.
    The price is rebal_cn_bound's threshold rising to 4 * rebal_kk + 4.\<close>
definition rebal_cn :: "nat \<Rightarrow> nat" where
  "rebal_cn n = rebal_kk * n div (rebal_kk + 1) + 2"

lemma rebal_cn_bound:
  assumes "n \<ge> 4 * rebal_kk + 4"
  shows "(2 * rebal_kk + 2) * rebal_cn n \<le> (2 * rebal_kk + 1) * n"
proof -
  have divf: "(rebal_kk + 1) * (rebal_kk * n div (rebal_kk + 1))
              \<le> rebal_kk * n"
  proof -
    have "rebal_kk * n div (rebal_kk + 1) * (rebal_kk + 1)
            + rebal_kk * n mod (rebal_kk + 1) = rebal_kk * n"
      by (rule div_mult_mod_eq)
    thus ?thesis by (simp add: mult.commute)
  qed
  have "(2 * rebal_kk + 2) * rebal_cn n
      = 2 * ((rebal_kk + 1) * (rebal_kk * n div (rebal_kk + 1)))
        + (4 * rebal_kk + 4)"
    unfolding rebal_cn_def by (simp add: algebra_simps)
  also have "\<dots> \<le> 2 * (rebal_kk * n) + (4 * rebal_kk + 4)"
    using divf by simp
  also have "\<dots> \<le> 2 * (rebal_kk * n) + n"
    using assms by simp
  also have "\<dots> = (2 * rebal_kk + 1) * n"
    by (simp add: algebra_simps)
  finally show ?thesis .
qed

lemma max_arity_ge_1_when_wf:
  assumes wf: "formula_well_formed (alphabet F) p"
      and ge: "len_formula p \<ge> 2"
    shows "Max ((arity (alphabet F)) ` (UNIV :: 'c set)) \<ge> 1"
proof (rule ccontr)
  let ?k = "Max ((arity (alphabet F)) ` (UNIV :: 'c set))"
  assume "\<not> ?k \<ge> 1"
  hence k0: "?k = 0" by simp
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
    from fin_im x_in have "arity (alphabet F) c \<le> ?k" by (rule Max_ge)
    thus "arity (alphabet F) c = 0" using k0 by simp
  qed
  have "len_formula p \<le> 1"
    using wf all_arity_zero
  proof (induction p)
    case (Atom v) show ?case by simp
  next
    case (Conn c fs)
    from Conn.prems(1) have "length fs = arity (alphabet F) c"
      and "\<forall> g \<in> set fs. formula_well_formed (alphabet F) g"
      by auto
    with all_arity_zero have "fs = []" by simp
    thus ?case by simp
  qed
  with ge show False by simp
qed

\<comment> \<open>The two spira-node estimates share one selection predicate: the ratio
    bound (the node is not too big) and the lower bound (the node is big enough
    that |p| - |q| is itself contracted) are the two arithmetic conjuncts of the
    same SOME-witness.  Prove them together and re-export the two names.\<close>
lemma spiras_sel_pred:
  assumes wf: "formula_well_formed (alphabet F) p"
      and ge: "len_formula p \<ge> spira_threshold"
    shows "(rebal_kk + 1) * len_formula (spiras_sel p) \<le> rebal_kk * len_formula p
           \<and> len_formula p \<le> (rebal_kk + 1) * len_formula (spiras_sel p) + rebal_kk"
proof -
  let ?k = "Max ((arity (alphabet F)) ` (UNIV :: 'c set))"
  have p2: "len_formula p \<ge> 2" using ge unfolding spira_threshold_def by simp
  show ?thesis
  proof (cases "?k > 1")
    case True
    hence kk_eq: "rebal_kk = ?k" unfolding rebal_kk_def by simp
    let ?P = "\<lambda>q. is_subformula q p
              \<and> (?k + 1) * len_formula q + ?k \<ge> len_formula p
              \<and> (?k + 1) * len_formula q \<le> ?k * len_formula p"
    have ex: "\<exists>q. ?P q"
      using spiras_selection_gen[OF wf p2 refl True] by blast
    have "spiras_sel p = (SOME q. ?P q)"
      unfolding spiras_sel_def using True by (simp add: Let_def)
    hence "?P (spiras_sel p)" using someI_ex[OF ex] by simp
    thus ?thesis using kk_eq by simp
  next
    case False
    have k1: "?k = 1"
    proof -
      have "?k \<ge> 1" using max_arity_ge_1_when_wf[OF wf p2] by simp
      moreover have "?k \<le> 1" using False by simp
      ultimately show ?thesis by simp
    qed
    have kk_eq: "rebal_kk = 2" using k1 unfolding rebal_kk_def by simp
    let ?P = "\<lambda>q. is_subformula q p
              \<and> 3 * len_formula q \<ge> len_formula p
              \<and> 3 * len_formula q \<le> 2 * len_formula p"
    have ex: "\<exists>q. ?P q"
      using spiras_selection_one[OF wf p2 k1] by blast
    have "spiras_sel p = (SOME q. ?P q)"
      unfolding spiras_sel_def using False by (simp add: Let_def)
    hence "?P (spiras_sel p)" using someI_ex[OF ex] by simp
    thus ?thesis using kk_eq by simp
  qed
qed

lemmas spiras_sel_ratio = spiras_sel_pred[THEN conjunct1]
lemmas spiras_sel_lower = spiras_sel_pred[THEN conjunct2]

\<comment> \<open>The below-threshold (Shannon) bound, fixed globally as a flat constant
    (length pos \<le> spira_threshold there) so rebal_glue_K can dominate it.\<close>
definition rebal_shc :: nat where
  "rebal_shc = (SOME m. \<forall> P pos.
       formula_well_formed (alphabet F) P \<and> valid_position P pos
       \<and> len_formula P < spira_threshold
     \<longrightarrow> (\<exists> lines sz dep.
            provable_balanced_iff (spira_trans P) (rebalancing P pos)
              lines sz dep
          \<and> lines \<le> m \<and> sz \<le> m \<and> dep \<le> m))"

lemma rebal_shc_ex:
  "\<exists> m. \<forall> P pos.
       formula_well_formed (alphabet F) P \<and> valid_position P pos
       \<and> len_formula P < spira_threshold
     \<longrightarrow> (\<exists> lines sz dep.
            provable_balanced_iff (spira_trans P) (rebalancing P pos)
              lines sz dep \<and> lines \<le> m \<and> sz \<le> m \<and> dep \<le> m)"
proof -
  obtain shgc shbase :: nat where sh:
    "\<And>P pos. formula_well_formed (alphabet F) P \<Longrightarrow> valid_position P pos
       \<Longrightarrow> len_formula P < spira_threshold
     \<Longrightarrow> (\<exists> lines sz dep.
            provable_balanced_iff (spira_trans P) (rebalancing P pos)
              lines sz dep
          \<and> lines \<le> length pos * shgc + shbase
          \<and> sz \<le> length pos * shgc + shbase
          \<and> dep \<le> length pos * shgc + shbase)"
    using shannon_construction by blast
  have *: "\<exists> lines sz dep.
            provable_balanced_iff (spira_trans P) (rebalancing P pos) lines sz dep
          \<and> lines \<le> spira_threshold * shgc + shbase
          \<and> sz \<le> spira_threshold * shgc + shbase
          \<and> dep \<le> spira_threshold * shgc + shbase"
    if wf: "formula_well_formed (alphabet F) P" and vp: "valid_position P pos"
       and small: "len_formula P < spira_threshold" for P pos
  proof -
    have key: "length pos * shgc + shbase \<le> spira_threshold * shgc + shbase"
      using valid_position_length_le[OF vp] small by (simp add: mult_le_mono1)
    obtain lines sz dep where d:
        "provable_balanced_iff (spira_trans P) (rebalancing P pos) lines sz dep"
        "lines \<le> length pos * shgc + shbase"
        "sz \<le> length pos * shgc + shbase"
        "dep \<le> length pos * shgc + shbase"
      using sh[OF wf vp small] by blast
    have "lines \<le> spira_threshold * shgc + shbase"
     and "sz \<le> spira_threshold * shgc + shbase"
     and "dep \<le> spira_threshold * shgc + shbase"
      using d(2) d(3) d(4) key by linarith+
    thus ?thesis using d(1) by blast
  qed
  show ?thesis using * by blast
qed

lemma rebal_shc_spec:
  assumes "formula_well_formed (alphabet F) P" and "valid_position P pos"
      and "len_formula P < spira_threshold"
  shows "\<exists> lines sz dep.
           provable_balanced_iff (spira_trans P) (rebalancing P pos)
             lines sz dep
         \<and> lines \<le> rebal_shc \<and> sz \<le> rebal_shc \<and> dep \<le> rebal_shc"
  using someI_ex[OF rebal_shc_ex] assms unfolding rebal_shc_def by blast

\<comment> \<open>rebal_base_K: the sum of every glue / base-case constant.  rebal_glue_K
    scales it by (10 * poly rebal_tb 1 + 1) so that, against n ^ rebal_deg, all of
    them sit below rebal_glue_K * n ^ rebal_deg (see rebal_L_dom).\<close>
subsection \<open>The L(n,m) recurrence function and its bounds\<close>

definition rebal_base_K :: nat where
  "rebal_base_K = case_one_glue_lines + case_two_glue_lines
                  + case_three_glue_lines + refl_lines + pos_empty_lines
                  + refl_step_len + pos_empty_step_len + rebal_shc
                  + rebal_glue_coeff + rebal_glue_coeff3"

definition rebal_glue_K :: nat where
  "rebal_glue_K = rebal_base_K * (10 * poly rebal_tb 1 + 1) + 1"

definition rebal_A :: nat where
  "rebal_A = 2 * (2 * rebal_kk + 2) ^ rebal_deg * rebal_glue_K"

definition rebal_L :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "rebal_L n m = rebal_A * n ^ rebal_deg + 2 * rebal_A * m ^ rebal_deg"

lemma rebal_L_mono:
  assumes "n \<le> n'" and "m \<le> m'"
  shows "rebal_L n m \<le> rebal_L n' m'"
proof -
  have "n ^ rebal_deg \<le> n' ^ rebal_deg"
    using assms(1) by (rule power_mono) simp
  moreover have "m ^ rebal_deg \<le> m' ^ rebal_deg"
    using assms(2) by (rule power_mono) simp
  ultimately show ?thesis
    unfolding rebal_L_def by (simp add: add_mono mult_le_mono2)
qed

lemma rebal_L_step:
  assumes n_ge: "n \<ge> 4 * rebal_kk + 4"
      and g_le: "g \<le> rebal_glue_K * n ^ rebal_deg"
    shows "g + 2 * rebal_L (rebal_cn n) (rebal_cn n)
           + 2 * rebal_L m (rebal_cn n) \<le> rebal_L n m"
proof -
  let ?d = rebal_deg
  let ?P1 = "(2 * rebal_kk + 1) ^ ?d"
  let ?P2 = "(2 * rebal_kk + 2) ^ ?d"
  let ?cn = "rebal_cn n"
  have P2pos: "?P2 > 0" by simp
  have key: "11 * ?P1 \<le> ?P2" by (rule rebal_pow_key)
  have cnpow: "?P2 * ?cn ^ ?d \<le> ?P1 * n ^ ?d"
  proof -
    have "((2 * rebal_kk + 2) * ?cn) ^ ?d
          \<le> ((2 * rebal_kk + 1) * n) ^ ?d"
      using rebal_cn_bound[OF n_ge] by (rule power_mono) simp
    thus ?thesis by (simp only: power_mult_distrib)
  qed
  have f1: "?P2 * (rebal_glue_K * n ^ ?d) \<le> rebal_A * (?P1 * n ^ ?d)"
  proof -
    have p1: "1 \<le> ?P1" by simp
    have "?P2 * (rebal_glue_K * n ^ ?d)
          = ?P2 * (rebal_glue_K * n ^ ?d) * 1" by simp
    also have "\<dots> \<le> ?P2 * (rebal_glue_K * n ^ ?d) * (2 * ?P1)"
      using p1 by (intro mult_le_mono2) linarith
    also have "\<dots> = rebal_A * (?P1 * n ^ ?d)"
      unfolding rebal_A_def by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  have f2: "11 * (rebal_A * (?P1 * n ^ ?d)) \<le> rebal_A * (?P2 * n ^ ?d)"
  proof -
    have "(11 * ?P1) * n ^ ?d \<le> ?P2 * n ^ ?d"
      using key by (rule mult_le_mono1)
    hence "rebal_A * ((11 * ?P1) * n ^ ?d) \<le> rebal_A * (?P2 * n ^ ?d)"
      by (rule mult_le_mono2)
    thus ?thesis by (simp add: algebra_simps)
  qed
  have f3: "10 * (rebal_A * (?P2 * ?cn ^ ?d))
          \<le> 10 * (rebal_A * (?P1 * n ^ ?d))"
  proof -
    have "rebal_A * (?P2 * ?cn ^ ?d) \<le> rebal_A * (?P1 * n ^ ?d)"
      using cnpow by (rule mult_le_mono2)
    thus ?thesis by (rule mult_le_mono2)
  qed
  have eq1: "?P2 * (rebal_glue_K * n ^ ?d + 10 * rebal_A * ?cn ^ ?d)
           = ?P2 * (rebal_glue_K * n ^ ?d)
             + 10 * (rebal_A * (?P2 * ?cn ^ ?d))"
    by (simp add: algebra_simps)
  have eq2: "rebal_A * (?P2 * n ^ ?d) = ?P2 * (rebal_A * n ^ ?d)"
    by (simp add: algebra_simps)
  have "?P2 * (rebal_glue_K * n ^ ?d + 10 * rebal_A * ?cn ^ ?d)
        \<le> ?P2 * (rebal_A * n ^ ?d)"
    using f1 f2 f3 eq1 eq2 by linarith
  hence core: "rebal_glue_K * n ^ ?d + 10 * rebal_A * ?cn ^ ?d
               \<le> rebal_A * n ^ ?d"
    using P2pos by simp
  have "g + 10 * rebal_A * ?cn ^ ?d \<le> rebal_A * n ^ ?d"
    using core g_le by linarith
  thus ?thesis
    unfolding rebal_L_def by (simp add: algebra_simps)
qed

(*
  Lemma 5.1. spira_trans P and rebalancing P pos are provably equivalent by a
  balanced Frege proof: polynomially many lines, every line polynomial-size and
  of O(log |P|) depth. The proof is a well-founded induction on the lexical
  measure (|P|, |P| - |subterm_at P pos|), here linearised to a single nat.
  Two easy cases (below threshold; pos the spira position) are reflexivity;
  the three hard cases follow Filmus' R\<subset>Q, Q\<subset>R, Q\<bottom>R analysis.
*)
\<comment> \<open>The second L-parameter: max of the rebalancing target size |R| and
    |P| - |R| + 1.  Bounded by |P|, and the recursion contracts it to rebal_cn.\<close>
definition rebal_m :: "'c formula \<Rightarrow> nat list \<Rightarrow> nat" where
  "rebal_m P pos = max (len_formula (subterm_at P pos))
                       (len_formula P - len_formula (subterm_at P pos) + 1)"

lemma rebal_m_le:
  assumes "valid_position P pos"
  shows "rebal_m P pos \<le> len_formula P"
proof -
  have r1: "len_formula (subterm_at P pos) \<le> len_formula P"
    by (rule subterm_at_len_le[OF assms])
  have r2: "1 \<le> len_formula (subterm_at P pos)"
    by (rule len_formula_positive)
  show ?thesis unfolding rebal_m_def using r1 r2 by linarith
qed

\<comment> \<open>Fit rebal_m below a bound by discharging the two max-branches: the subterm
    size and the host-minus-subterm size.  Replaces the per-site rebal_m_def
    max-split unfolding in the main induction's measure-fitting steps.\<close>
lemma rebal_m_fit:
  assumes "subterm_at A pos = R"
      and "len_formula R \<le> bnd"
      and "len_formula A - len_formula R + 1 \<le> bnd"
    shows "rebal_m A pos \<le> bnd"
  using assms unfolding rebal_m_def by simp

\<comment> \<open>Every base-case constant K \<le> rebal_base_K, multiplied by poly rebal_tb n,
    sits below rebal_L n m.  This discharges the reflexivity / pos = [] / Shannon
    cases against the rebal_L invariant.\<close>
\<comment> \<open>Common shape factored out of the four bound lemmas below:
    tbpow_helper bounds poly rebal_tb n by poly rebal_tb 1 \<cdot> n^rebal_deg;
    rebal_base_to_glue absorbs the base constant into the glue constant;
    rebal_glue_to_L lifts a glue_K \<cdot> n^rebal_deg bound to rebal_L n m.\<close>
lemma tbpow_helper:
  assumes "1 \<le> n"
  shows "poly rebal_tb n \<le> poly rebal_tb 1 * n ^ rebal_deg"
proof -
  have "poly rebal_tb n \<le> poly rebal_tb 1 * n ^ (degree rebal_tb)"
    by (rule poly_le_poly1_pow[OF assms])
  also have "\<dots> \<le> poly rebal_tb 1 * n ^ rebal_deg"
    using rebal_deg_ge_tb assms by (intro mult_le_mono2 power_increasing) auto
  finally show ?thesis .
qed

lemma rebal_base_to_glue: "rebal_base_K \<le> rebal_glue_K"
proof -
  have "rebal_base_K = rebal_base_K * 1" by simp
  also have "\<dots> \<le> rebal_base_K * (10 * poly rebal_tb 1 + 1)"
    by (intro mult_le_mono2) simp
  also have "\<dots> \<le> rebal_glue_K" unfolding rebal_glue_K_def by simp
  finally show ?thesis .
qed

lemma rebal_glue_to_L:
  assumes "1 \<le> n"
  shows "rebal_glue_K * n ^ rebal_deg \<le> rebal_L n m"
proof -
  have "rebal_glue_K = 1 * rebal_glue_K" by simp
  also have "\<dots> \<le> (2 * (2 * rebal_kk + 2) ^ rebal_deg) * rebal_glue_K"
    by (intro mult_le_mono1) simp
  also have "\<dots> = rebal_A" unfolding rebal_A_def by (simp add: mult.assoc)
  finally have gA: "rebal_glue_K \<le> rebal_A" .
  have "rebal_glue_K * n ^ rebal_deg \<le> rebal_A * n ^ rebal_deg"
    using gA by (rule mult_le_mono1)
  also have "\<dots> \<le> rebal_L n m" unfolding rebal_L_def by simp
  finally show ?thesis .
qed

lemma rebal_L_dom:
  assumes Kle: "K \<le> rebal_base_K" and n1: "1 \<le> n"
  shows "K * poly rebal_tb n \<le> rebal_L n m"
proof -
  have "K * poly rebal_tb n \<le> rebal_base_K * poly rebal_tb n"
    using Kle by (rule mult_le_mono1)
  also have "\<dots> \<le> rebal_base_K * (poly rebal_tb 1 * n ^ rebal_deg)"
    using tbpow_helper[OF n1] by (rule mult_le_mono2)
  also have "\<dots> = (rebal_base_K * poly rebal_tb 1) * n ^ rebal_deg"
    by (simp add: mult.assoc)
  also have "\<dots> \<le> rebal_glue_K * n ^ rebal_deg"
  proof -
    have "rebal_base_K * poly rebal_tb 1
          \<le> rebal_base_K * (10 * poly rebal_tb 1 + 1)"
      by (intro mult_le_mono2) simp
    also have "\<dots> \<le> rebal_glue_K" unfolding rebal_glue_K_def by simp
    finally show ?thesis by (rule mult_le_mono1)
  qed
  also have "\<dots> \<le> rebal_L n m" by (rule rebal_glue_to_L[OF n1])
  finally show ?thesis .
qed

\<comment> \<open>Constant-only version: any K \<le> rebal_base_K fits in rebal_L for n \<ge> 1.\<close>
lemma rebal_L_dom_const:
  assumes Kle: "K \<le> rebal_base_K" and n1: "1 \<le> n"
  shows "K \<le> rebal_L n m"
proof -
  have "K \<le> rebal_glue_K * n ^ rebal_deg"
  proof -
    have "K \<le> rebal_glue_K" using Kle rebal_base_to_glue by linarith
    also have "\<dots> = rebal_glue_K * 1" by simp
    also have "\<dots> \<le> rebal_glue_K * n ^ rebal_deg"
      by (intro mult_le_mono2) (rule one_le_power[OF n1])
    finally show ?thesis .
  qed
  also have "\<dots> \<le> rebal_L n m" by (rule rebal_glue_to_L[OF n1])
  finally show ?thesis .
qed

\<comment> \<open>The spira node Q satisfies |Q| \<le> rebal_cn |P|: directly from spiras_sel_ratio
    (Q \<le> kk*P / (kk+1)) and rebal_cn = kk*P div (kk+1) + 2.\<close>
lemma spiras_sel_le_cn:
  assumes wf: "formula_well_formed (alphabet F) p"
      and ge: "len_formula p \<ge> spira_threshold"
    shows "len_formula (spiras_sel p) \<le> rebal_cn (len_formula p)"
proof -
  let ?kk = rebal_kk
  let ?P = "len_formula p"
  let ?Q = "len_formula (spiras_sel p)"
  let ?D = "?kk * ?P div (?kk + 1)"
  have kk_pos: "0 < ?kk + 1" by simp
  have ratio: "(?kk + 1) * ?Q \<le> ?kk * ?P"
    by (rule spiras_sel_ratio[OF wf ge])
  have eq: "?D * (?kk + 1) + (?kk * ?P) mod (?kk + 1) = ?kk * ?P"
    using div_mult_mod_eq[of "?kk * ?P" "?kk + 1"]
    by (simp add: mult.commute)
  have m_le: "(?kk * ?P) mod (?kk + 1) \<le> ?kk"
    using mod_less_divisor[OF kk_pos] by simp
  have "?Q \<le> ?D + 1"
  proof (rule ccontr)
    assume "\<not> ?Q \<le> ?D + 1"
    hence le: "?D + 2 \<le> ?Q" by simp
    have "(?D + 2) * (?kk + 1) \<le> ?Q * (?kk + 1)"
      using le by (rule mult_le_mono1)
    also have "\<dots> = (?kk + 1) * ?Q" by (simp add: mult.commute)
    also have "\<dots> \<le> ?kk * ?P" using ratio .
    finally have "(?D + 2) * (?kk + 1) \<le> ?kk * ?P" .
    moreover have "?kk * ?P \<le> ?D * (?kk + 1) + ?kk"
      using eq m_le by linarith
    ultimately have "(?D + 2) * (?kk + 1) \<le> ?D * (?kk + 1) + ?kk" by linarith
    thus False by (simp add: algebra_simps)
  qed
  also have "?D + 1 \<le> rebal_cn (len_formula p)"
    unfolding rebal_cn_def by simp
  finally show ?thesis .
qed

\<comment> \<open>The complementary bound: |P| - |Q| + 1 \<le> rebal_cn |P|.  This is the bound
    that drives the +2 in rebal_cn (instead of +1).\<close>
lemma P_minus_spira_le_cn:
  assumes wf: "formula_well_formed (alphabet F) p"
      and ge: "len_formula p \<ge> spira_threshold"
    shows "len_formula p - len_formula (spiras_sel p) + 1
         \<le> rebal_cn (len_formula p)"
proof -
  let ?kk = rebal_kk
  let ?P = "len_formula p"
  let ?Q = "len_formula (spiras_sel p)"
  let ?D = "?kk * ?P div (?kk + 1)"
  have kk_pos: "0 < ?kk + 1" by simp
  have lower: "?P \<le> (?kk + 1) * ?Q + ?kk"
    by (rule spiras_sel_lower[OF wf ge])
  have lP_ge2: "?P \<ge> 2" using ge unfolding spira_threshold_def by simp
  have lQ_lt: "?Q < ?P"
    using spiras_sel_pred_when_wf[OF wf lP_ge2] by simp
  have lQ_le: "?Q \<le> ?P" using lQ_lt by simp
  have kk_le_P: "?kk \<le> ?P"
  proof -
    have "?kk \<le> spira_threshold"
      unfolding rebal_kk_def spira_threshold_def by simp
    thus ?thesis using ge by simp
  qed

  have bnd: "(?kk + 1) * (?P - ?Q) \<le> ?kk * ?P + ?kk"
  proof -
    have "(?kk + 1) * (?P - ?Q) = (?kk + 1) * ?P - (?kk + 1) * ?Q"
      using lQ_le by (simp add: diff_mult_distrib2)
    also have "\<dots> \<le> (?kk + 1) * ?P - (?P - ?kk)"
      using lower by simp
    also have "\<dots> = ?kk * ?P + ?kk"
      using kk_le_P by (simp add: algebra_simps)
    finally show ?thesis .
  qed

  have D_lb: "(?kk + 1) * ?D + ?kk \<ge> ?kk * ?P"
  proof -
    have eq: "(?kk + 1) * ?D + (?kk * ?P) mod (?kk + 1) = ?kk * ?P"
      using div_mult_mod_eq[of "?kk * ?P" "?kk + 1"]
      by (simp add: mult.commute)
    have m_le: "(?kk * ?P) mod (?kk + 1) \<le> ?kk"
      using mod_less_divisor[OF kk_pos] by simp
    from eq m_le show ?thesis by linarith
  qed

  from bnd D_lb have step: "(?kk + 1) * (?P - ?Q) \<le> (?kk + 1) * ?D + 2 * ?kk"
    by linarith
  have pq_lt: "?P - ?Q < ?D + 2"
  proof (rule ccontr)
    assume "\<not> ?P - ?Q < ?D + 2"
    hence "?D + 2 \<le> ?P - ?Q" by simp
    hence "(?kk + 1) * (?D + 2) \<le> (?kk + 1) * (?P - ?Q)"
      by (rule mult_le_mono2)
    with step have "(?kk + 1) * (?D + 2) \<le> (?kk + 1) * ?D + 2 * ?kk"
      by linarith
    thus False by (simp add: algebra_simps)
  qed
  hence "?P - ?Q + 1 \<le> ?D + 2" by simp
  also have "?D + 2 = rebal_cn (len_formula p)"
    unfolding rebal_cn_def by simp
  finally show ?thesis .
qed

\<comment> \<open>Constant glue: K \<le> rebal_base_K is bounded by rebal_glue_K * n ^ rebal_deg
    for n \<ge> 1.  Used for the lines glue in recursive cases.\<close>
lemma rebal_glue_const_bound:
  assumes Kle: "K \<le> rebal_base_K" and n1: "1 \<le> n"
  shows "K \<le> rebal_glue_K * n ^ rebal_deg"
proof -
  have "K \<le> rebal_glue_K" using Kle rebal_base_to_glue by linarith
  also have "\<dots> = rebal_glue_K * 1" by simp
  also have "\<dots> \<le> rebal_glue_K * n ^ rebal_deg"
    by (intro mult_le_mono2) (rule one_le_power[OF n1])
  finally show ?thesis .
qed

\<comment> \<open>Polynomial glue: K * (S + 1) \<le> rebal_glue_K * n ^ rebal_deg when
    K \<le> rebal_base_K and S \<le> 10 * poly rebal_tb n.  Covers the sz glue in
    all three recursive cases (Cases 1/2 have 8 leaves, Case 3 has 10).\<close>
lemma rebal_glue_poly_bound:
  assumes Kle: "K \<le> rebal_base_K"
      and Sle: "S \<le> 10 * poly rebal_tb n"
      and n1: "1 \<le> n"
    shows "K * (S + 1) \<le> rebal_glue_K * n ^ rebal_deg"
proof -
  have tbpow: "poly rebal_tb n \<le> poly rebal_tb 1 * n ^ rebal_deg"
    by (rule tbpow_helper[OF n1])
  have npow_ge1: "1 \<le> n ^ rebal_deg" by (rule one_le_power[OF n1])
  have "K * (S + 1) = K * S + K" by (simp add: algebra_simps)
  also have "\<dots> \<le> K * (10 * poly rebal_tb n) + K"
    using Sle by simp
  also have "\<dots> \<le> K * (10 * (poly rebal_tb 1 * n ^ rebal_deg))
                + K * n ^ rebal_deg"
  proof -
    have "K * (10 * poly rebal_tb n)
        \<le> K * (10 * (poly rebal_tb 1 * n ^ rebal_deg))"
      using tbpow by simp
    moreover have "K \<le> K * n ^ rebal_deg"
      using npow_ge1 by (metis mult.right_neutral mult_le_mono2)
    ultimately show ?thesis by linarith
  qed
  also have "\<dots> = K * (10 * poly rebal_tb 1 + 1) * n ^ rebal_deg"
    by (simp add: algebra_simps)
  also have "\<dots> \<le> rebal_base_K * (10 * poly rebal_tb 1 + 1) * n ^ rebal_deg"
    using Kle by (intro mult_le_mono1)
  also have "\<dots> \<le> rebal_glue_K * n ^ rebal_deg"
    unfolding rebal_glue_K_def by (intro mult_le_mono1) simp
  finally show ?thesis .
qed

subsection \<open>The main induction (Lemma 5.1)\<close>

lemma rebalancing_provable:
  shows "\<exists> (bnd :: nat poly) (c :: real).
           \<forall> P pos. formula_well_formed (alphabet F) P \<and> valid_position P pos \<longrightarrow>
             (\<exists> lines sz dep.
                provable_balanced_iff (spira_trans P) (rebalancing P pos) lines sz dep
              \<and> lines \<le> poly bnd (len_formula P)
              \<and> sz \<le> poly bnd (len_formula P)
              \<and> real dep \<le> c * log 2 (real (len_formula P) + 1))"
proof -
  obtain tc :: real where tc_spec:
    "\<forall> f. formula_well_formed (alphabet F) f
          \<longrightarrow> real (depth_formula (spira_trans f))
              \<le> tc * log 2 (real (len_formula f) + 1)"
    using trans_c by blast
  define c :: real where
    c_def: "c = real (refl_step_depth + pos_empty_step_depth + 1)
                + max tc 1 + real rebal_shc
                + real rebal_dep_coeff * (8 * max tc 1 + 1)
                + real rebal_dep_coeff3 * (10 * max tc 1 + 1)"
  \<comment> \<open>The witness: bnd(n) = 3 * rebal_A * n^rebal_deg = rebal_L n n.\<close>
  define bnd :: "nat poly" where
    bnd_def: "bnd = monom (3 * rebal_A) rebal_deg"
  have bnd_eval: "\<And>n. poly bnd n = rebal_L n n"
    unfolding bnd_def rebal_L_def by (simp add: poly_monom)

  have c_nn: "0 \<le> c" unfolding c_def by (intro add_nonneg_nonneg) auto

  have main: "\<And>P pos. formula_well_formed (alphabet F) P \<Longrightarrow> valid_position P pos
        \<Longrightarrow> (\<exists> lines sz dep.
               provable_balanced_iff (spira_trans P) (rebalancing P pos) lines sz dep
             \<and> lines \<le> rebal_L (len_formula P) (rebal_m P pos)
             \<and> sz \<le> rebal_L (len_formula P) (rebal_m P pos)
             \<and> real dep \<le> c * log 2 (real (len_formula P) + 1))"
  proof -
    fix P pos
    show "formula_well_formed (alphabet F) P \<Longrightarrow> valid_position P pos
        \<Longrightarrow> (\<exists> lines sz dep.
               provable_balanced_iff (spira_trans P) (rebalancing P pos) lines sz dep
             \<and> lines \<le> rebal_L (len_formula P) (rebal_m P pos)
             \<and> sz \<le> rebal_L (len_formula P) (rebal_m P pos)
             \<and> real dep \<le> c * log 2 (real (len_formula P) + 1))"
    proof (induction "rebal_measure P pos" arbitrary: P pos rule: less_induct)
    case less
    have wfP: "formula_well_formed (alphabet F) P" using less.prems by simp
    have vpP: "valid_position P pos" using less.prems by simp
    have lP1: "1 \<le> len_formula P" by (rule len_formula_positive)

    have logP1: "(1::real) \<le> log 2 (real (len_formula P) + 1)"
    proof -
      have "(2::real) \<le> real (len_formula P) + 1" using lP1 by simp
      hence "log 2 (2::real) \<le> log 2 (real (len_formula P) + 1)"
        by (intro log_mono) auto
      thus ?thesis by simp
    qed

    \<comment> \<open>A constant K \<le> c is bounded by c * log |P|.\<close>
    have const_to_c: "\<And>K :: nat. real K \<le> c \<Longrightarrow>
        real K \<le> c * log 2 (real (len_formula P) + 1)"
    proof -
      fix K :: nat assume Kc: "real K \<le> c"
      have "real K \<le> c" using Kc .
      also have "\<dots> = c * 1" by simp
      also have "\<dots> \<le> c * log 2 (real (len_formula P) + 1)"
        by (rule mult_left_mono[OF logP1 c_nn])
      finally show "real K \<le> c * log 2 (real (len_formula P) + 1)" .
    qed

    \<comment> \<open>K + depth(spira_trans P) stays within c * log |P| for K up to the easy
        / pos = [] glue depth.\<close>
    have depth_to_c: "\<And>K. K \<le> refl_step_depth + pos_empty_step_depth + 1 \<Longrightarrow>
        real (K + depth_formula (spira_trans P))
          \<le> c * log 2 (real (len_formula P) + 1)"
    proof -
      fix K assume KleD: "K \<le> refl_step_depth + pos_empty_step_depth + 1"
      let ?L = "log 2 (real (len_formula P) + 1)"
      let ?D = "real (refl_step_depth + pos_empty_step_depth + 1)"
      have dc: "real (depth_formula (spira_trans P)) \<le> tc * ?L"
        using tc_spec wfP by blast
      have "real (K + depth_formula (spira_trans P))
          = real K + real (depth_formula (spira_trans P))" by simp
      also have "\<dots> \<le> ?D + max tc 1 * ?L"
      proof -
        have "real K \<le> ?D" using KleD by simp
        moreover have "real (depth_formula (spira_trans P)) \<le> max tc 1 * ?L"
        proof -
          have "tc * ?L \<le> max tc 1 * ?L" using logP1 by (intro mult_right_mono) auto
          thus ?thesis using dc by simp
        qed
        ultimately show ?thesis by simp
      qed
      also have "\<dots> \<le> ?D * ?L + max tc 1 * ?L"
      proof -
        have "?D * 1 \<le> ?D * ?L" using logP1 by (intro mult_left_mono) auto
        thus ?thesis by simp
      qed
      also have "\<dots> \<le> c * ?L"
      proof -
        have nn: "(0::real) \<le> (real rebal_shc
              + real rebal_dep_coeff * (8 * max tc 1 + 1)
              + real rebal_dep_coeff3 * (10 * max tc 1 + 1)) * ?L"
          using logP1 by (intro mult_nonneg_nonneg) auto
        thus ?thesis unfolding c_def by (simp add: algebra_simps)
      qed
      finally show "real (K + depth_formula (spira_trans P)) \<le> c * ?L" .
    qed

    \<comment> \<open>The easy case: rebalancing collapses to spira_trans P.\<close>
    have easy: "rebalancing P pos = spira_trans P \<Longrightarrow>
      (\<exists> lines sz dep.
         provable_balanced_iff (spira_trans P) (rebalancing P pos) lines sz dep
       \<and> lines \<le> rebal_L (len_formula P) (rebal_m P pos)
       \<and> sz \<le> rebal_L (len_formula P) (rebal_m P pos)
       \<and> real dep \<le> c * log 2 (real (len_formula P) + 1))"
    proof -
      assume reb_eq: "rebalancing P pos = spira_trans P"
      have pbi: "provable_balanced_iff (spira_trans P) (rebalancing P pos)
                   refl_lines (refl_step_len * len_formula (spira_trans P))
                   (refl_step_depth + depth_formula (spira_trans P))"
        using iff_refl[of "spira_trans P"] reb_eq by simp
      have lb: "refl_lines \<le> rebal_L (len_formula P) (rebal_m P pos)"
        by (rule rebal_L_dom_const[OF _ lP1]) (simp add: rebal_base_K_def)
      have sb: "refl_step_len * len_formula (spira_trans P)
              \<le> rebal_L (len_formula P) (rebal_m P pos)"
      proof -
        have b: "len_formula (spira_trans P) \<le> poly rebal_tb (len_formula P)"
          by (rule rebal_tb_spec[OF wfP])
        have "refl_step_len * len_formula (spira_trans P)
            \<le> refl_step_len * poly rebal_tb (len_formula P)"
          using b by simp
        also have "\<dots> \<le> rebal_L (len_formula P) (rebal_m P pos)"
          by (rule rebal_L_dom[OF _ lP1]) (simp add: rebal_base_K_def)
        finally show ?thesis .
      qed
      have db: "real (refl_step_depth + depth_formula (spira_trans P))
              \<le> c * log 2 (real (len_formula P) + 1)"
        by (rule depth_to_c) simp
      show ?thesis using pbi lb sb db by blast
    qed

    show ?case
    proof (cases "len_formula P < spira_threshold")
      case True
      \<comment> \<open>Below threshold: Shannon (via rebal_shc_spec).\<close>
      obtain lines sz dep where
          sc: "provable_balanced_iff (spira_trans P) (rebalancing P pos)
                 lines sz dep"
        and scl: "lines \<le> rebal_shc"
        and scs: "sz \<le> rebal_shc"
        and scd: "dep \<le> rebal_shc"
        using rebal_shc_spec[OF wfP vpP True] by blast
      have shc_L: "rebal_shc \<le> rebal_L (len_formula P) (rebal_m P pos)"
        by (rule rebal_L_dom_const[OF _ lP1]) (simp add: rebal_base_K_def)
      have lb: "lines \<le> rebal_L (len_formula P) (rebal_m P pos)"
        using scl shc_L by linarith
      have sb: "sz \<le> rebal_L (len_formula P) (rebal_m P pos)"
        using scs shc_L by linarith
      have db: "real dep \<le> c * log 2 (real (len_formula P) + 1)"
      proof -
        have "real dep \<le> real rebal_shc" using scd by simp
        also have "\<dots> \<le> c" unfolding c_def by simp
        finally have "real dep \<le> c" .
        thus ?thesis by (rule const_to_c)
      qed
      show ?thesis using sc lb sb db by blast
    next
      case bigST: False
      have geST: "len_formula P \<ge> spira_threshold" using bigST by simp

      show ?thesis
      proof (cases "len_formula P < 4 * rebal_kk + 4")
        case True
        \<comment> \<open>Gap region: empty, since spira_threshold = 4 * rebal_kk + 4.\<close>
        have "len_formula P \<ge> 4 * rebal_kk + 4"
          using geST unfolding spira_threshold_def rebal_kk_def by simp
        with True show ?thesis by simp
      next
        case bigT: False
        have geT: "len_formula P \<ge> 4 * rebal_kk + 4" using bigT by simp
        from position_trichotomy[of "spiras_sel_position P" pos]
        consider (eq) "spiras_sel_position P = pos"
          | (rbelow) "\<exists>s. s \<noteq> [] \<and> pos = spiras_sel_position P @ s"
          | (qbelow) "\<exists>s. s \<noteq> [] \<and> spiras_sel_position P = pos @ s"
          | (disj) "positions_disjoint (spiras_sel_position P) pos"
          by blast
        thus ?thesis
        proof cases
          case eq
          have "rebalancing P pos = spira_trans P"
            using rebalancing_eq_spira_trans[OF wfP geST] eq by simp
          thus ?thesis by (rule easy)
        next
          case rbelow
          \<comment> \<open>Case 1: R is a descendant of Q. Recursive via rebal_L_step.\<close>
          then obtain s where s_ne: "s \<noteq> []"
                          and pos_eq: "pos = spiras_sel_position P @ s" by blast
          have split: "valid_position P (spiras_sel_position P)
                     \<and> valid_position (subterm_at P (spiras_sel_position P)) s"
            using vpP by (simp only: pos_eq valid_position_append)
          have wfQ: "formula_well_formed (alphabet F)
                       (subterm_at P (spiras_sel_position P))"
            using subterm_at_wf[OF wfP] split by blast
          have vpT: "valid_position (fix_at pos True P) (spiras_sel_position P)"
            using valid_position_fix_at_prefix[OF vpP[unfolded pos_eq]] pos_eq by simp
          have vpF: "valid_position (fix_at pos False P) (spiras_sel_position P)"
            using valid_position_fix_at_prefix[OF vpP[unfolded pos_eq]] pos_eq by simp
          note meas = case_one_measure[OF wfP geST pos_eq s_ne vpP]
          obtain lQ szQ depQ where IH_Q:
              "provable_balanced_iff (spira_trans (subterm_at P (spiras_sel_position P)))
                 (rebalancing (subterm_at P (spiras_sel_position P)) s) lQ szQ depQ"
            and IH_Q_l: "lQ \<le> rebal_L (len_formula (subterm_at P (spiras_sel_position P)))
                                       (rebal_m (subterm_at P (spiras_sel_position P)) s)"
            and IH_Q_s: "szQ \<le> rebal_L (len_formula (subterm_at P (spiras_sel_position P)))
                                       (rebal_m (subterm_at P (spiras_sel_position P)) s)"
            and IH_Q_d: "real depQ \<le> c * log 2 (real (len_formula
                            (subterm_at P (spiras_sel_position P))) + 1)"
            using less.hyps[OF conjunct1[OF meas] wfQ conjunct2[OF split]] by blast
          obtain lT szT depT where IH_T:
              "provable_balanced_iff (spira_trans (fix_at pos True P))
                 (rebalancing (fix_at pos True P) (spiras_sel_position P)) lT szT depT"
            and IH_T_l: "lT \<le> rebal_L (len_formula (fix_at pos True P))
                                       (rebal_m (fix_at pos True P) (spiras_sel_position P))"
            and IH_T_s: "szT \<le> rebal_L (len_formula (fix_at pos True P))
                                       (rebal_m (fix_at pos True P) (spiras_sel_position P))"
            and IH_T_d: "real depT \<le> c * log 2 (real (len_formula
                            (fix_at pos True P)) + 1)"
            using less.hyps[OF conjunct1[OF conjunct2[OF meas]]
                             fix_at_wf[OF wfP] vpT] by blast
          obtain lF szF depF where IH_F:
              "provable_balanced_iff (spira_trans (fix_at pos False P))
                 (rebalancing (fix_at pos False P) (spiras_sel_position P)) lF szF depF"
            and IH_F_l: "lF \<le> rebal_L (len_formula (fix_at pos False P))
                                       (rebal_m (fix_at pos False P) (spiras_sel_position P))"
            and IH_F_s: "szF \<le> rebal_L (len_formula (fix_at pos False P))
                                       (rebal_m (fix_at pos False P) (spiras_sel_position P))"
            and IH_F_d: "real depF \<le> c * log 2 (real (len_formula
                            (fix_at pos False P)) + 1)"
            using less.hyps[OF conjunct2[OF conjunct2[OF meas]]
                             fix_at_wf[OF wfP] vpF] by blast
          let ?Q = "subterm_at P (spiras_sel_position P)"
          let ?cn = "rebal_cn (len_formula P)"
          let ?mP = "rebal_m P pos"
          let ?llsum =
            "len_formula (spira_trans (fix_at (spiras_sel_position P) True P))
           + len_formula (spira_trans (fix_at (spiras_sel_position P) False P))
           + len_formula (spira_trans (fix_at s True ?Q))
           + len_formula (spira_trans (fix_at s False ?Q))
           + len_formula (spira_trans (subterm_at P pos))
           + len_formula (spira_trans ?Q)
           + len_formula (spira_trans (fix_at pos True P))
           + len_formula (spira_trans (fix_at pos False P))"
          let ?dlsum =
            "depth_formula (spira_trans (fix_at (spiras_sel_position P) True P))
           + depth_formula (spira_trans (fix_at (spiras_sel_position P) False P))
           + depth_formula (spira_trans (fix_at s True ?Q))
           + depth_formula (spira_trans (fix_at s False ?Q))
           + depth_formula (spira_trans (subterm_at P pos))
           + depth_formula (spira_trans ?Q)
           + depth_formula (spira_trans (fix_at pos True P))
           + depth_formula (spira_trans (fix_at pos False P))"
          obtain sz dep where pbi:
              "provable_balanced_iff (spira_trans P) (rebalancing P pos)
                 (lQ + lT + lF + case_one_glue_lines) sz dep"
            and conS: "sz \<le> szQ + szT + szF + rebal_glue_coeff * (?llsum + 1)"
            and conD: "dep \<le> max depQ (max depT (max depF
                              (rebal_dep_coeff * (?dlsum + 1))))"
            using case_one_construction[OF wfP geST pos_eq vpP IH_Q IH_T IH_F] by blast
          \<comment> \<open>Lines bound via rebal_L_step.  Size inequalities below.\<close>
          have ge2: "len_formula P \<ge> 2"
            using geST unfolding spira_threshold_def by simp
          have Q_eq: "?Q = spiras_sel P"
            using spiras_sel_position_spec[OF wfP ge2] by simp
          have Q_le_cn: "len_formula ?Q \<le> ?cn"
            using Q_eq spiras_sel_le_cn[OF wfP geST] by simp
          have vp_Qs: "valid_position ?Q s" using split by simp
          have mQ_le_cn: "rebal_m ?Q s \<le> ?cn"
            using rebal_m_le[OF vp_Qs] Q_le_cn by linarith
          have R_le_P: "len_formula (subterm_at P pos) \<le> len_formula P"
            by (rule subterm_at_len_le[OF vpP])
          have R_pos: "1 \<le> len_formula (subterm_at P pos)"
            by (rule len_formula_positive)
          have fix_at_len_T: "len_formula (fix_at pos True P)
                            = len_formula P - len_formula (subterm_at P pos) + 1"
            using fix_at_len_eq[OF vpP, of True] R_le_P by linarith
          have fix_at_len_F: "len_formula (fix_at pos False P)
                            = len_formula P - len_formula (subterm_at P pos) + 1"
            using fix_at_len_eq[OF vpP, of False] R_le_P by linarith
          have fix_T_le_mP: "len_formula (fix_at pos True P) \<le> ?mP"
            using fix_at_len_T unfolding rebal_m_def by simp
          have fix_F_le_mP: "len_formula (fix_at pos False P) \<le> ?mP"
            using fix_at_len_F unfolding rebal_m_def by simp
          have vp_spiraP: "valid_position P (spiras_sel_position P)"
            using split by simp
          have sub_fix_eq_T: "subterm_at (fix_at pos True P) (spiras_sel_position P)
                            = fix_at s True ?Q"
            using subterm_at_fix_at_prefix[OF vp_spiraP, of s True] pos_eq by simp
          have sub_fix_eq_F: "subterm_at (fix_at pos False P) (spiras_sel_position P)
                            = fix_at s False ?Q"
            using subterm_at_fix_at_prefix[OF vp_spiraP, of s False] pos_eq by simp
          have sub_Qs_eq: "subterm_at ?Q s = subterm_at P pos"
            using vp_spiraP pos_eq subterm_at_append[of P "spiras_sel_position P" s]
            by simp
          have R_le_Q: "len_formula (subterm_at P pos) \<le> len_formula ?Q"
            using sub_Qs_eq subterm_at_len_le[OF vp_Qs] by simp
          have fix_sQ_len_T: "len_formula (fix_at s True ?Q)
                            = len_formula ?Q - len_formula (subterm_at P pos) + 1"
          proof -
            have "len_formula (fix_at s True ?Q) + len_formula (subterm_at ?Q s)
                = len_formula ?Q + 1"
              by (rule fix_at_len_eq[OF vp_Qs])
            hence "len_formula (fix_at s True ?Q) + len_formula (subterm_at P pos)
                 = len_formula ?Q + 1" using sub_Qs_eq by simp
            thus ?thesis using R_le_Q by linarith
          qed
          have fix_sQ_len_F: "len_formula (fix_at s False ?Q)
                            = len_formula ?Q - len_formula (subterm_at P pos) + 1"
          proof -
            have "len_formula (fix_at s False ?Q) + len_formula (subterm_at ?Q s)
                = len_formula ?Q + 1"
              by (rule fix_at_len_eq[OF vp_Qs])
            hence "len_formula (fix_at s False ?Q) + len_formula (subterm_at P pos)
                 = len_formula ?Q + 1" using sub_Qs_eq by simp
            thus ?thesis using R_le_Q by linarith
          qed
          have c2_le_cn: "len_formula P - len_formula ?Q + 1 \<le> ?cn"
            using Q_eq P_minus_spira_le_cn[OF wfP geST] by simp
          have m_fix_T_le_cn: "rebal_m (fix_at pos True P) (spiras_sel_position P)
                             \<le> ?cn"
          proof (rule rebal_m_fit[OF sub_fix_eq_T])
            show "len_formula (fix_at s True ?Q) \<le> ?cn"
              using fix_sQ_len_T R_pos R_le_Q Q_le_cn by linarith
            show "len_formula (fix_at pos True P)
                  - len_formula (fix_at s True ?Q) + 1 \<le> ?cn"
              using fix_at_len_T fix_sQ_len_T R_le_Q R_le_P c2_le_cn by linarith
          qed
          have m_fix_F_le_cn: "rebal_m (fix_at pos False P) (spiras_sel_position P)
                             \<le> ?cn"
          proof (rule rebal_m_fit[OF sub_fix_eq_F])
            show "len_formula (fix_at s False ?Q) \<le> ?cn"
              using fix_sQ_len_F R_pos R_le_Q Q_le_cn by linarith
            show "len_formula (fix_at pos False P)
                  - len_formula (fix_at s False ?Q) + 1 \<le> ?cn"
              using fix_at_len_F fix_sQ_len_F R_le_Q R_le_P c2_le_cn by linarith
          qed
          have lQ_le: "lQ \<le> rebal_L ?cn ?cn"
            using IH_Q_l rebal_L_mono[OF Q_le_cn mQ_le_cn] by (rule order_trans)
          have lT_le: "lT \<le> rebal_L ?mP ?cn"
            using IH_T_l rebal_L_mono[OF fix_T_le_mP m_fix_T_le_cn] by (rule order_trans)
          have lF_le: "lF \<le> rebal_L ?mP ?cn"
            using IH_F_l rebal_L_mono[OF fix_F_le_mP m_fix_F_le_cn] by (rule order_trans)
          have glue_le: "case_one_glue_lines
                       \<le> rebal_glue_K * (len_formula P) ^ rebal_deg"
            by (rule rebal_glue_const_bound[OF _ lP1]) (simp add: rebal_base_K_def)
          have step: "case_one_glue_lines + 2 * rebal_L ?cn ?cn
                    + 2 * rebal_L ?mP ?cn
                    \<le> rebal_L (len_formula P) ?mP"
            by (rule rebal_L_step[OF geT glue_le])
          have lines_le:
            "lQ + lT + lF + case_one_glue_lines
             \<le> rebal_L (len_formula P) ?mP"
          proof -
            have "lQ + lT + lF + case_one_glue_lines
                \<le> rebal_L ?cn ?cn + rebal_L ?mP ?cn + rebal_L ?mP ?cn
                  + case_one_glue_lines"
              using lQ_le lT_le lF_le by linarith
            also have "\<dots> = case_one_glue_lines + rebal_L ?cn ?cn
                          + 2 * rebal_L ?mP ?cn" by simp
            also have "\<dots> \<le> case_one_glue_lines + 2 * rebal_L ?cn ?cn
                          + 2 * rebal_L ?mP ?cn" by simp
            also have "\<dots> \<le> rebal_L (len_formula P) ?mP" using step .
            finally show ?thesis .
          qed
          have lQ_le_P: "len_formula ?Q \<le> len_formula P"
            using Q_eq spiras_sel_pred_when_wf[OF wfP ge2] by simp
          have lT_le_P: "len_formula (fix_at pos True P) \<le> len_formula P"
            by (rule fix_at_len_le)
          have lF_le_P: "len_formula (fix_at pos False P) \<le> len_formula P"
            by (rule fix_at_len_le)
          have lC: "len_formula (fix_at s True ?Q) \<le> len_formula P"
            using fix_at_len_le lQ_le_P by (rule order_trans)
          have lD: "len_formula (fix_at s False ?Q) \<le> len_formula P"
            using fix_at_len_le lQ_le_P by (rule order_trans)
          have leafA: "len_formula (spira_trans (fix_at (spiras_sel_position P) True P))
                     \<le> poly rebal_tb (len_formula P)"
            by (rule spira_trans_len_le_tb[OF fix_at_wf[OF wfP] fix_at_len_le])
          have leafB: "len_formula (spira_trans (fix_at (spiras_sel_position P) False P))
                     \<le> poly rebal_tb (len_formula P)"
            by (rule spira_trans_len_le_tb[OF fix_at_wf[OF wfP] fix_at_len_le])
          have leafC: "len_formula (spira_trans (fix_at s True ?Q))
                     \<le> poly rebal_tb (len_formula P)"
            by (rule spira_trans_len_le_tb[OF fix_at_wf[OF wfQ] lC])
          have leafD: "len_formula (spira_trans (fix_at s False ?Q))
                     \<le> poly rebal_tb (len_formula P)"
            by (rule spira_trans_len_le_tb[OF fix_at_wf[OF wfQ] lD])
          have leafE: "len_formula (spira_trans (subterm_at P pos))
                     \<le> poly rebal_tb (len_formula P)"
            using spira_trans_len_le_tb[OF subterm_at_wf[OF wfP vpP] R_le_P] .
          have leafF: "len_formula (spira_trans ?Q)
                     \<le> poly rebal_tb (len_formula P)"
            using spira_trans_len_le_tb[OF wfQ lQ_le_P] .
          have leafG: "len_formula (spira_trans (fix_at pos True P))
                     \<le> poly rebal_tb (len_formula P)"
            by (rule spira_trans_len_le_tb[OF fix_at_wf[OF wfP] lT_le_P])
          have leafH: "len_formula (spira_trans (fix_at pos False P))
                     \<le> poly rebal_tb (len_formula P)"
            by (rule spira_trans_len_le_tb[OF fix_at_wf[OF wfP] lF_le_P])
          have llsum_le: "?llsum \<le> 8 * poly rebal_tb (len_formula P)"
            using leafA leafB leafC leafD leafE leafF leafG leafH by simp
          have llsum_le10: "?llsum \<le> 10 * poly rebal_tb (len_formula P)"
            using llsum_le by simp
          have glue_sz: "rebal_glue_coeff * (?llsum + 1)
                       \<le> rebal_glue_K * (len_formula P) ^ rebal_deg"
            by (rule rebal_glue_poly_bound[OF _ llsum_le10 lP1])
               (simp add: rebal_base_K_def)
          have step_sz: "rebal_glue_coeff * (?llsum + 1) + 2 * rebal_L ?cn ?cn
                       + 2 * rebal_L ?mP ?cn
                       \<le> rebal_L (len_formula P) ?mP"
            by (rule rebal_L_step[OF geT glue_sz])
          have szQ_le: "szQ \<le> rebal_L ?cn ?cn"
            using IH_Q_s rebal_L_mono[OF Q_le_cn mQ_le_cn] by (rule order_trans)
          have szT_le: "szT \<le> rebal_L ?mP ?cn"
            using IH_T_s rebal_L_mono[OF fix_T_le_mP m_fix_T_le_cn] by (rule order_trans)
          have szF_le: "szF \<le> rebal_L ?mP ?cn"
            using IH_F_s rebal_L_mono[OF fix_F_le_mP m_fix_F_le_cn] by (rule order_trans)
          have sz_le: "sz \<le> rebal_L (len_formula P) ?mP"
          proof -
            have "sz \<le> szQ + szT + szF + rebal_glue_coeff * (?llsum + 1)"
              by (rule conS)
            also have "\<dots> \<le> rebal_L ?cn ?cn + rebal_L ?mP ?cn + rebal_L ?mP ?cn
                          + rebal_glue_coeff * (?llsum + 1)"
              using szQ_le szT_le szF_le by linarith
            also have "\<dots> = rebal_glue_coeff * (?llsum + 1)
                          + rebal_L ?cn ?cn + 2 * rebal_L ?mP ?cn" by simp
            also have "\<dots> \<le> rebal_glue_coeff * (?llsum + 1)
                          + 2 * rebal_L ?cn ?cn + 2 * rebal_L ?mP ?cn" by simp
            also have "\<dots> \<le> rebal_L (len_formula P) ?mP" using step_sz .
            finally show ?thesis .
          qed
          have dep_le: "real dep \<le> c * log 2 (real (len_formula P) + 1)"
          proof -
            let ?L = "log 2 (real (len_formula P) + 1)"
            have c_pos: "0 \<le> c" by (rule c_nn)
            have lQ_le_P: "len_formula ?Q \<le> len_formula P"
              using Q_eq spiras_sel_pred_when_wf[OF wfP ge2] by simp
            have lT_le_P: "len_formula (fix_at pos True P) \<le> len_formula P"
              by (rule fix_at_len_le)
            have lF_le_P: "len_formula (fix_at pos False P) \<le> len_formula P"
              by (rule fix_at_len_le)
            have log_le: "\<And>n. n \<le> len_formula P \<Longrightarrow>
                log 2 (real n + 1) \<le> ?L"
              by (intro log_mono) auto
            have ihQ: "real depQ \<le> c * ?L"
            proof -
              have "real depQ \<le> c * log 2 (real (len_formula ?Q) + 1)"
                by (rule IH_Q_d)
              also have "\<dots> \<le> c * ?L"
                using log_le[OF lQ_le_P] c_pos by (intro mult_left_mono)
              finally show ?thesis .
            qed
            have ihT: "real depT \<le> c * ?L"
            proof -
              have "real depT \<le> c * log 2 (real (len_formula (fix_at pos True P)) + 1)"
                by (rule IH_T_d)
              also have "\<dots> \<le> c * ?L"
                using log_le[OF lT_le_P] c_pos by (intro mult_left_mono)
              finally show ?thesis .
            qed
            have ihF: "real depF \<le> c * ?L"
            proof -
              have "real depF \<le> c * log 2 (real (len_formula (fix_at pos False P)) + 1)"
                by (rule IH_F_d)
              also have "\<dots> \<le> c * ?L"
                using log_le[OF lF_le_P] c_pos by (intro mult_left_mono)
              finally show ?thesis .
            qed
            have max_tc_nn: "(0::real) \<le> max tc 1" by simp
            have lC: "len_formula (fix_at s True ?Q) \<le> len_formula P"
            proof -
              have "len_formula (fix_at s True ?Q) \<le> len_formula ?Q"
                by (rule fix_at_len_le)
              also have "\<dots> \<le> len_formula P" by (rule lQ_le_P)
              finally show ?thesis .
            qed
            have lD: "len_formula (fix_at s False ?Q) \<le> len_formula P"
            proof -
              have "len_formula (fix_at s False ?Q) \<le> len_formula ?Q"
                by (rule fix_at_len_le)
              also have "\<dots> \<le> len_formula P" by (rule lQ_le_P)
              finally show ?thesis .
            qed
            have bA: "real (depth_formula (spira_trans
                       (fix_at (spiras_sel_position P) True P)))
                    \<le> max tc 1 * ?L"
              by (rule spira_trans_dep_le[OF tc_spec fix_at_wf[OF wfP] fix_at_len_le])
            have bB: "real (depth_formula (spira_trans
                       (fix_at (spiras_sel_position P) False P)))
                    \<le> max tc 1 * ?L"
              by (rule spira_trans_dep_le[OF tc_spec fix_at_wf[OF wfP] fix_at_len_le])
            have bC: "real (depth_formula (spira_trans (fix_at s True ?Q)))
                    \<le> max tc 1 * ?L"
              by (rule spira_trans_dep_le[OF tc_spec fix_at_wf[OF wfQ] lC])
            have bD: "real (depth_formula (spira_trans (fix_at s False ?Q)))
                    \<le> max tc 1 * ?L"
              by (rule spira_trans_dep_le[OF tc_spec fix_at_wf[OF wfQ] lD])
            have bE: "real (depth_formula (spira_trans (subterm_at P pos)))
                    \<le> max tc 1 * ?L"
              using spira_trans_dep_le[OF tc_spec subterm_at_wf[OF wfP vpP] R_le_P] .
            have bF: "real (depth_formula (spira_trans ?Q)) \<le> max tc 1 * ?L"
              using spira_trans_dep_le[OF tc_spec wfQ lQ_le_P] .
            have bG: "real (depth_formula (spira_trans (fix_at pos True P)))
                    \<le> max tc 1 * ?L"
              by (rule spira_trans_dep_le[OF tc_spec fix_at_wf[OF wfP] lT_le_P])
            have bH: "real (depth_formula (spira_trans (fix_at pos False P)))
                    \<le> max tc 1 * ?L"
              by (rule spira_trans_dep_le[OF tc_spec fix_at_wf[OF wfP] lF_le_P])
            have sum_le: "real ?dlsum \<le> 8 * (max tc 1 * ?L)"
              using bA bB bC bD bE bF bG bH by simp
            have glue_le: "real (rebal_dep_coeff * (?dlsum + 1)) \<le> c * ?L"
            proof -
              have h1: "real (?dlsum + 1) \<le> 8 * (max tc 1 * ?L) + 1"
                using sum_le by simp
              have c_ge: "real rebal_dep_coeff * (8 * max tc 1 + 1) \<le> c"
                unfolding c_def by simp
              have "real (rebal_dep_coeff * (?dlsum + 1))
                  = real rebal_dep_coeff * real (?dlsum + 1)"
                by (simp only: of_nat_mult)
              also have "\<dots> \<le> real rebal_dep_coeff * (8 * (max tc 1 * ?L) + 1)"
                using h1 by (intro mult_left_mono) auto
              also have "\<dots> \<le> real rebal_dep_coeff * ((8 * max tc 1 + 1) * ?L)"
              proof -
                have step3: "8 * (max tc 1 * ?L) + 1
                           \<le> (8 * max tc 1 + 1) * ?L"
                proof -
                  have "8 * (max tc 1 * ?L) + 1 \<le> 8 * (max tc 1 * ?L) + ?L"
                    using logP1 by simp
                  also have "\<dots> = (8 * max tc 1 + 1) * ?L"
                    by (simp add: algebra_simps)
                  finally show ?thesis .
                qed
                show ?thesis using step3 by (intro mult_left_mono) auto
              qed
              also have "\<dots> = (real rebal_dep_coeff * (8 * max tc 1 + 1)) * ?L"
                by (simp add: algebra_simps)
              also have "\<dots> \<le> c * ?L"
                using c_ge logP1 by (intro mult_right_mono) auto
              finally show ?thesis .
            qed
            have all4: "real (max depQ (max depT (max depF
                                  (rebal_dep_coeff * (?dlsum + 1)))))
                       \<le> c * ?L"
              using ihQ ihT ihF glue_le by (simp add: of_nat_max)
            have "real dep \<le> real (max depQ (max depT (max depF
                                       (rebal_dep_coeff * (?dlsum + 1)))))"
              using conD by simp
            also have "\<dots> \<le> c * ?L" by (rule all4)
            finally show ?thesis .
          qed
          show ?thesis using pbi lines_le sz_le dep_le by blast
        next
          case qbelow
          then obtain s where s_ne: "s \<noteq> []"
                          and pos_eq2: "spiras_sel_position P = pos @ s" by blast
          show ?thesis
          proof (cases "pos = []")
            case True
            \<comment> \<open>Degenerate: rebalancing at the root (fixed mux identity).\<close>
            have cpe: "provable_balanced_iff (spira_trans P) (rebalancing P pos)
                         pos_empty_lines
                         (pos_empty_step_len * len_formula (spira_trans P))
                         (pos_empty_step_depth + 1 + depth_formula (spira_trans P))"
              using case_pos_empty_construction[of P] True by simp
            have lb: "pos_empty_lines \<le> rebal_L (len_formula P) (rebal_m P pos)"
              by (rule rebal_L_dom_const[OF _ lP1]) (simp add: rebal_base_K_def)
            have sb: "pos_empty_step_len * len_formula (spira_trans P)
                    \<le> rebal_L (len_formula P) (rebal_m P pos)"
            proof -
              have b: "len_formula (spira_trans P) \<le> poly rebal_tb (len_formula P)"
                by (rule rebal_tb_spec[OF wfP])
              have "pos_empty_step_len * len_formula (spira_trans P)
                  \<le> pos_empty_step_len * poly rebal_tb (len_formula P)"
                using b by simp
              also have "\<dots> \<le> rebal_L (len_formula P) (rebal_m P pos)"
                by (rule rebal_L_dom[OF _ lP1]) (simp add: rebal_base_K_def)
              finally show ?thesis .
            qed
            have db: "real (pos_empty_step_depth + 1 + depth_formula (spira_trans P))
                    \<le> c * log 2 (real (len_formula P) + 1)"
              by (rule depth_to_c) simp
            show ?thesis using cpe lb sb db by blast
          next
            case pos_ne: False
            \<comment> \<open>Case 2: Q a descendant of R, non-degenerate.\<close>
            have ge2: "len_formula P \<ge> 2"
              using geST unfolding spira_threshold_def by simp
            have vpq: "valid_position P (spiras_sel_position P)"
              using spiras_sel_position_spec[OF wfP ge2] by simp
            have vpQ2: "valid_position P (pos @ s)"
              using vpq pos_eq2 by simp
            have vsplit: "valid_position P pos
                        \<and> valid_position (subterm_at P pos) s"
              using vpQ2 by (simp only: valid_position_append)
            note vp_Qb = valid_position_fix_at_prefix[OF vpQ2, folded pos_eq2]
            note meas = case_two_measure[OF wfP geST pos_ne vpP]
            obtain lR szR depR where IH_R:
                "provable_balanced_iff (spira_trans (subterm_at P pos))
                   (rebalancing (subterm_at P pos) s) lR szR depR"
              and IH_R_l: "lR \<le> rebal_L (len_formula (subterm_at P pos))
                                         (rebal_m (subterm_at P pos) s)"
              and IH_R_s: "szR \<le> rebal_L (len_formula (subterm_at P pos))
                                         (rebal_m (subterm_at P pos) s)"
              and IH_R_d: "real depR \<le> c * log 2 (real (len_formula
                              (subterm_at P pos)) + 1)"
              using less.hyps[OF conjunct1[OF meas]
                               subterm_at_wf[OF wfP vpP] conjunct2[OF vsplit]]
              by blast
            obtain lT szT depT where IH_T:
                "provable_balanced_iff
                   (spira_trans (fix_at (spiras_sel_position P) True P))
                   (rebalancing (fix_at (spiras_sel_position P) True P) pos)
                   lT szT depT"
              and IH_T_l: "lT \<le> rebal_L (len_formula
                                  (fix_at (spiras_sel_position P) True P))
                                         (rebal_m
                                  (fix_at (spiras_sel_position P) True P) pos)"
              and IH_T_s: "szT \<le> rebal_L (len_formula
                                  (fix_at (spiras_sel_position P) True P))
                                         (rebal_m
                                  (fix_at (spiras_sel_position P) True P) pos)"
              and IH_T_d: "real depT \<le> c * log 2 (real (len_formula
                              (fix_at (spiras_sel_position P) True P)) + 1)"
              using less.hyps[OF conjunct1[OF conjunct2[OF meas]]
                               fix_at_wf[OF wfP] vp_Qb] by blast
            obtain lF szF depF where IH_F:
                "provable_balanced_iff
                   (spira_trans (fix_at (spiras_sel_position P) False P))
                   (rebalancing (fix_at (spiras_sel_position P) False P) pos)
                   lF szF depF"
              and IH_F_l: "lF \<le> rebal_L (len_formula
                                  (fix_at (spiras_sel_position P) False P))
                                         (rebal_m
                                  (fix_at (spiras_sel_position P) False P) pos)"
              and IH_F_s: "szF \<le> rebal_L (len_formula
                                  (fix_at (spiras_sel_position P) False P))
                                         (rebal_m
                                  (fix_at (spiras_sel_position P) False P) pos)"
              and IH_F_d: "real depF \<le> c * log 2 (real (len_formula
                              (fix_at (spiras_sel_position P) False P)) + 1)"
              using less.hyps[OF conjunct2[OF conjunct2[OF meas]]
                               fix_at_wf[OF wfP] vp_Qb] by blast
            let ?Q = "subterm_at P (spiras_sel_position P)"
            let ?R = "subterm_at P pos"
            let ?cn = "rebal_cn (len_formula P)"
            let ?mP = "rebal_m P pos"
            let ?llsum2 =
              "len_formula (spira_trans (fix_at (spiras_sel_position P) True P))
             + len_formula (spira_trans (fix_at (spiras_sel_position P) False P))
             + len_formula (spira_trans (fix_at pos True P))
             + len_formula (spira_trans (fix_at pos False P))
             + len_formula (spira_trans (fix_at s True ?R))
             + len_formula (spira_trans (fix_at s False ?R))
             + len_formula (spira_trans ?Q)
             + len_formula (spira_trans ?R)"
            let ?dlsum2 =
              "depth_formula (spira_trans (fix_at (spiras_sel_position P) True P))
             + depth_formula (spira_trans (fix_at (spiras_sel_position P) False P))
             + depth_formula (spira_trans (fix_at pos True P))
             + depth_formula (spira_trans (fix_at pos False P))
             + depth_formula (spira_trans (fix_at s True ?R))
             + depth_formula (spira_trans (fix_at s False ?R))
             + depth_formula (spira_trans ?Q)
             + depth_formula (spira_trans ?R)"
            obtain sz dep where pbi:
                "provable_balanced_iff (spira_trans P) (rebalancing P pos)
                   (lT + lF + lR + case_two_glue_lines) sz dep"
              and conS2: "sz \<le> szT + szF + szR
                            + rebal_glue_coeff * (?llsum2 + 1)"
              and conD2: "dep \<le> max depT (max depF (max depR
                                  (rebal_dep_coeff * (?dlsum2 + 1))))"
              using case_two_construction[OF wfP geST pos_eq2 vpP IH_T IH_F IH_R]
              by blast
            \<comment> \<open>Size inequalities.\<close>
            have Q_eq: "?Q = spiras_sel P"
              using spiras_sel_position_spec[OF wfP ge2] by simp
            have Q_le_cn: "len_formula ?Q \<le> ?cn"
              using Q_eq spiras_sel_le_cn[OF wfP geST] by simp
            have Q_lt_P: "len_formula ?Q < len_formula P"
              using Q_eq spiras_sel_pred_when_wf[OF wfP ge2] by simp
            have Q_le_P: "len_formula ?Q \<le> len_formula P" using Q_lt_P by simp
            have R_le_P: "len_formula ?R \<le> len_formula P"
              by (rule subterm_at_len_le[OF vpP])
            have R_pos: "1 \<le> len_formula ?R" by (rule len_formula_positive)
            have Q_pos: "1 \<le> len_formula ?Q" by (rule len_formula_positive)
            \<comment> \<open>|R| \<ge> |Q| since R contains Q (pos is prefix of spiras_sel_position P).\<close>
            have sub_RQ: "subterm_at ?R s = ?Q"
              using vpP pos_eq2 subterm_at_append[of P pos s]
              by simp
            have Q_le_R: "len_formula ?Q \<le> len_formula ?R"
              using sub_RQ subterm_at_len_le conjunct2[OF vsplit] by metis
            \<comment> \<open>fix_at sizes.\<close>
            have fixQ_T_len: "len_formula (fix_at (spiras_sel_position P) True P)
                            = len_formula P - len_formula ?Q + 1"
              using fix_at_len_eq[OF vpq, of True] Q_le_P by linarith
            have fixQ_F_len: "len_formula (fix_at (spiras_sel_position P) False P)
                            = len_formula P - len_formula ?Q + 1"
              using fix_at_len_eq[OF vpq, of False] Q_le_P by linarith
            have fixR_T_len: "len_formula (fix_at s True ?R)
                            = len_formula ?R - len_formula ?Q + 1"
            proof -
              have "len_formula (fix_at s True ?R) + len_formula (subterm_at ?R s)
                  = len_formula ?R + 1"
                by (rule fix_at_len_eq[OF conjunct2[OF vsplit]])
              hence "len_formula (fix_at s True ?R) + len_formula ?Q
                   = len_formula ?R + 1" using sub_RQ by simp
              thus ?thesis using Q_le_R by linarith
            qed
            have fixR_F_len: "len_formula (fix_at s False ?R)
                            = len_formula ?R - len_formula ?Q + 1"
            proof -
              have "len_formula (fix_at s False ?R) + len_formula (subterm_at ?R s)
                  = len_formula ?R + 1"
                by (rule fix_at_len_eq[OF conjunct2[OF vsplit]])
              hence "len_formula (fix_at s False ?R) + len_formula ?Q
                   = len_formula ?R + 1" using sub_RQ by simp
              thus ?thesis using Q_le_R by linarith
            qed
            have fixP_T_len: "len_formula (fix_at pos True P)
                            = len_formula P - len_formula ?R + 1"
              using fix_at_len_eq[OF vpP, of True] R_le_P by linarith
            have fixP_F_len: "len_formula (fix_at pos False P)
                            = len_formula P - len_formula ?R + 1"
              using fix_at_len_eq[OF vpP, of False] R_le_P by linarith
            \<comment> \<open>IH_T/IH_F fittings (fit ?cn,?cn slot).\<close>
            have fixQ_T_le_cn: "len_formula (fix_at (spiras_sel_position P) True P)
                              \<le> ?cn"
              using fixQ_T_len Q_eq P_minus_spira_le_cn[OF wfP geST] by simp
            have fixQ_F_le_cn: "len_formula (fix_at (spiras_sel_position P) False P)
                              \<le> ?cn"
              using fixQ_F_len Q_eq P_minus_spira_le_cn[OF wfP geST] by simp
            have sub_fix_eq_T2: "subterm_at (fix_at (spiras_sel_position P) True P) pos
                              = fix_at s True ?R"
              using subterm_at_fix_at_prefix[OF vpP, of s True] pos_eq2 by simp
            have sub_fix_eq_F2: "subterm_at (fix_at (spiras_sel_position P) False P) pos
                              = fix_at s False ?R"
              using subterm_at_fix_at_prefix[OF vpP, of s False] pos_eq2 by simp
            have fixR_T_le_cn: "len_formula (fix_at s True ?R) \<le> ?cn"
            proof -
              have "len_formula (fix_at s True ?R)
                  = len_formula ?R - len_formula ?Q + 1" by (rule fixR_T_len)
              also have "\<dots> \<le> len_formula P - len_formula ?Q + 1"
                using R_le_P Q_le_R by linarith
              also have "\<dots> \<le> ?cn"
                using Q_eq P_minus_spira_le_cn[OF wfP geST] by simp
              finally show ?thesis .
            qed
            have fixR_F_le_cn: "len_formula (fix_at s False ?R) \<le> ?cn"
            proof -
              have "len_formula (fix_at s False ?R)
                  = len_formula ?R - len_formula ?Q + 1" by (rule fixR_F_len)
              also have "\<dots> \<le> len_formula P - len_formula ?Q + 1"
                using R_le_P Q_le_R by linarith
              also have "\<dots> \<le> ?cn"
                using Q_eq P_minus_spira_le_cn[OF wfP geST] by simp
              finally show ?thesis .
            qed
            have m_fixQ_T_le_cn:
              "rebal_m (fix_at (spiras_sel_position P) True P) pos \<le> ?cn"
            proof (rule rebal_m_fit[OF sub_fix_eq_T2])
              show "len_formula (fix_at s True ?R) \<le> ?cn" by (rule fixR_T_le_cn)
              have c2_eq: "len_formula (fix_at (spiras_sel_position P) True P)
                         - len_formula (fix_at s True ?R) + 1
                         = len_formula P - len_formula ?R + 1"
                using fixQ_T_len fixR_T_len Q_le_R R_le_P Q_le_P by linarith
              have c2_le: "len_formula P - len_formula ?R + 1 \<le> ?cn"
              proof -
                have "len_formula P - len_formula ?R + 1
                    \<le> len_formula P - len_formula ?Q + 1"
                  using R_le_P Q_le_R Q_pos by linarith
                also have "\<dots> \<le> ?cn"
                  using Q_eq P_minus_spira_le_cn[OF wfP geST] by simp
                finally show ?thesis .
              qed
              show "len_formula (fix_at (spiras_sel_position P) True P)
                    - len_formula (fix_at s True ?R) + 1 \<le> ?cn"
                using c2_eq c2_le by linarith
            qed
            have m_fixQ_F_le_cn:
              "rebal_m (fix_at (spiras_sel_position P) False P) pos \<le> ?cn"
            proof (rule rebal_m_fit[OF sub_fix_eq_F2])
              show "len_formula (fix_at s False ?R) \<le> ?cn" by (rule fixR_F_le_cn)
              have c2_eq: "len_formula (fix_at (spiras_sel_position P) False P)
                         - len_formula (fix_at s False ?R) + 1
                         = len_formula P - len_formula ?R + 1"
                using fixQ_F_len fixR_F_len Q_le_R R_le_P Q_le_P by linarith
              have c2_le: "len_formula P - len_formula ?R + 1 \<le> ?cn"
              proof -
                have "len_formula P - len_formula ?R + 1
                    \<le> len_formula P - len_formula ?Q + 1"
                  using R_le_P Q_le_R Q_pos by linarith
                also have "\<dots> \<le> ?cn"
                  using Q_eq P_minus_spira_le_cn[OF wfP geST] by simp
                finally show ?thesis .
              qed
              show "len_formula (fix_at (spiras_sel_position P) False P)
                    - len_formula (fix_at s False ?R) + 1 \<le> ?cn"
                using c2_eq c2_le by linarith
            qed
            \<comment> \<open>IH_R fits ?mP slot.\<close>
            have R_le_mP: "len_formula ?R \<le> ?mP"
              unfolding rebal_m_def by simp
            have mR_le_cn: "rebal_m ?R s \<le> ?cn"
            proof (rule rebal_m_fit[OF sub_RQ])
              show "len_formula ?Q \<le> ?cn" by (rule Q_le_cn)
              show "len_formula ?R - len_formula ?Q + 1 \<le> ?cn"
              proof -
                have "len_formula ?R - len_formula ?Q + 1
                    \<le> len_formula P - len_formula ?Q + 1"
                  using R_le_P Q_le_R by linarith
                also have "\<dots> \<le> ?cn"
                  using Q_eq P_minus_spira_le_cn[OF wfP geST] by simp
                finally show ?thesis .
              qed
            qed
            \<comment> \<open>IH fittings.\<close>
            have lR_le: "lR \<le> rebal_L ?mP ?cn"
              using IH_R_l rebal_L_mono[OF R_le_mP mR_le_cn] by (rule order_trans)
            have lT_le: "lT \<le> rebal_L ?cn ?cn"
              using IH_T_l rebal_L_mono[OF fixQ_T_le_cn m_fixQ_T_le_cn] by (rule order_trans)
            have lF_le: "lF \<le> rebal_L ?cn ?cn"
              using IH_F_l rebal_L_mono[OF fixQ_F_le_cn m_fixQ_F_le_cn] by (rule order_trans)
            have glue_le: "case_two_glue_lines
                         \<le> rebal_glue_K * (len_formula P) ^ rebal_deg"
              by (rule rebal_glue_const_bound[OF _ lP1])
                 (simp add: rebal_base_K_def)
            have step: "case_two_glue_lines + 2 * rebal_L ?cn ?cn
                      + 2 * rebal_L ?mP ?cn
                      \<le> rebal_L (len_formula P) ?mP"
              by (rule rebal_L_step[OF geT glue_le])
            have lines_le:
              "(lT + lF + lR + case_two_glue_lines)
               \<le> rebal_L (len_formula P) ?mP"
            proof -
              have "lT + lF + lR + case_two_glue_lines
                  \<le> rebal_L ?cn ?cn + rebal_L ?cn ?cn + rebal_L ?mP ?cn
                    + case_two_glue_lines"
                using lT_le lF_le lR_le by linarith
              also have "\<dots> = case_two_glue_lines + 2 * rebal_L ?cn ?cn
                            + rebal_L ?mP ?cn" by simp
              also have "\<dots> \<le> case_two_glue_lines + 2 * rebal_L ?cn ?cn
                            + 2 * rebal_L ?mP ?cn" by simp
              also have "\<dots> \<le> rebal_L (len_formula P) ?mP" using step .
              finally show ?thesis .
            qed
            have wfQ2: "formula_well_formed (alphabet F) ?Q"
              using subterm_at_wf[OF wfP vpq] .
            have wfR: "formula_well_formed (alphabet F) ?R"
              using subterm_at_wf[OF wfP vpP] .
            have fixQT_le_P: "len_formula (fix_at (spiras_sel_position P) True P)
                            \<le> len_formula P" by (rule fix_at_len_le)
            have fixQF_le_P: "len_formula (fix_at (spiras_sel_position P) False P)
                            \<le> len_formula P" by (rule fix_at_len_le)
            have fixPT_le_P: "len_formula (fix_at pos True P) \<le> len_formula P"
              by (rule fix_at_len_le)
            have fixPF_le_P: "len_formula (fix_at pos False P) \<le> len_formula P"
              by (rule fix_at_len_le)
            have fixRT_le_P: "len_formula (fix_at s True ?R) \<le> len_formula P"
              using fix_at_len_le R_le_P by (rule order_trans)
            have fixRF_le_P: "len_formula (fix_at s False ?R) \<le> len_formula P"
              using fix_at_len_le R_le_P by (rule order_trans)
            have leafA2: "len_formula (spira_trans (fix_at (spiras_sel_position P) True P))
                       \<le> poly rebal_tb (len_formula P)"
              by (rule spira_trans_len_le_tb[OF fix_at_wf[OF wfP] fixQT_le_P])
            have leafB2: "len_formula (spira_trans (fix_at (spiras_sel_position P) False P))
                       \<le> poly rebal_tb (len_formula P)"
              by (rule spira_trans_len_le_tb[OF fix_at_wf[OF wfP] fixQF_le_P])
            have leafC2: "len_formula (spira_trans (fix_at pos True P))
                       \<le> poly rebal_tb (len_formula P)"
              by (rule spira_trans_len_le_tb[OF fix_at_wf[OF wfP] fixPT_le_P])
            have leafD2: "len_formula (spira_trans (fix_at pos False P))
                       \<le> poly rebal_tb (len_formula P)"
              by (rule spira_trans_len_le_tb[OF fix_at_wf[OF wfP] fixPF_le_P])
            have leafE2: "len_formula (spira_trans (fix_at s True ?R))
                       \<le> poly rebal_tb (len_formula P)"
              by (rule spira_trans_len_le_tb[OF fix_at_wf[OF wfR] fixRT_le_P])
            have leafF2: "len_formula (spira_trans (fix_at s False ?R))
                       \<le> poly rebal_tb (len_formula P)"
              by (rule spira_trans_len_le_tb[OF fix_at_wf[OF wfR] fixRF_le_P])
            have leafG2: "len_formula (spira_trans ?Q)
                       \<le> poly rebal_tb (len_formula P)"
              by (rule spira_trans_len_le_tb[OF wfQ2 Q_le_P])
            have leafH2: "len_formula (spira_trans ?R)
                       \<le> poly rebal_tb (len_formula P)"
              by (rule spira_trans_len_le_tb[OF wfR R_le_P])
            have llsum2_le: "?llsum2 \<le> 8 * poly rebal_tb (len_formula P)"
              using leafA2 leafB2 leafC2 leafD2 leafE2 leafF2 leafG2 leafH2 by simp
            have llsum2_le10: "?llsum2 \<le> 10 * poly rebal_tb (len_formula P)"
              using llsum2_le by simp
            have glue_sz2: "rebal_glue_coeff * (?llsum2 + 1)
                         \<le> rebal_glue_K * (len_formula P) ^ rebal_deg"
              by (rule rebal_glue_poly_bound[OF _ llsum2_le10 lP1])
                 (simp add: rebal_base_K_def)
            have step_sz2: "rebal_glue_coeff * (?llsum2 + 1)
                          + 2 * rebal_L ?cn ?cn + 2 * rebal_L ?mP ?cn
                          \<le> rebal_L (len_formula P) ?mP"
              by (rule rebal_L_step[OF geT glue_sz2])
            have szT_le: "szT \<le> rebal_L ?cn ?cn"
              using IH_T_s rebal_L_mono[OF fixQ_T_le_cn m_fixQ_T_le_cn] by (rule order_trans)
            have szF_le: "szF \<le> rebal_L ?cn ?cn"
              using IH_F_s rebal_L_mono[OF fixQ_F_le_cn m_fixQ_F_le_cn] by (rule order_trans)
            have szR_le: "szR \<le> rebal_L ?mP ?cn"
              using IH_R_s rebal_L_mono[OF R_le_mP mR_le_cn] by (rule order_trans)
            have sz_le: "sz \<le> rebal_L (len_formula P) ?mP"
            proof -
              have "sz \<le> szT + szF + szR + rebal_glue_coeff * (?llsum2 + 1)"
                by (rule conS2)
              also have "\<dots> \<le> rebal_L ?cn ?cn + rebal_L ?cn ?cn + rebal_L ?mP ?cn
                            + rebal_glue_coeff * (?llsum2 + 1)"
                using szT_le szF_le szR_le by linarith
              also have "\<dots> = rebal_glue_coeff * (?llsum2 + 1)
                            + 2 * rebal_L ?cn ?cn + rebal_L ?mP ?cn" by simp
              also have "\<dots> \<le> rebal_glue_coeff * (?llsum2 + 1)
                            + 2 * rebal_L ?cn ?cn + 2 * rebal_L ?mP ?cn" by simp
              also have "\<dots> \<le> rebal_L (len_formula P) ?mP" using step_sz2 .
              finally show ?thesis .
            qed
            have dep_le: "real dep \<le> c * log 2 (real (len_formula P) + 1)"
            proof -
              let ?L = "log 2 (real (len_formula P) + 1)"
              have c_pos: "0 \<le> c" by (rule c_nn)
              have log_le: "\<And>n. n \<le> len_formula P \<Longrightarrow>
                  log 2 (real n + 1) \<le> ?L"
                by (intro log_mono) auto
              have ihT_d: "real depT \<le> c * ?L"
              proof -
                have "real depT \<le> c * log 2 (real (len_formula
                        (fix_at (spiras_sel_position P) True P)) + 1)" by (rule IH_T_d)
                also have "\<dots> \<le> c * ?L"
                  using log_le[OF fixQT_le_P] c_pos by (intro mult_left_mono)
                finally show ?thesis .
              qed
              have ihF_d: "real depF \<le> c * ?L"
              proof -
                have "real depF \<le> c * log 2 (real (len_formula
                        (fix_at (spiras_sel_position P) False P)) + 1)" by (rule IH_F_d)
                also have "\<dots> \<le> c * ?L"
                  using log_le[OF fixQF_le_P] c_pos by (intro mult_left_mono)
                finally show ?thesis .
              qed
              have ihR_d: "real depR \<le> c * ?L"
              proof -
                have "real depR \<le> c * log 2 (real (len_formula ?R) + 1)"
                  by (rule IH_R_d)
                also have "\<dots> \<le> c * ?L"
                  using log_le[OF R_le_P] c_pos by (intro mult_left_mono)
                finally show ?thesis .
              qed
              have max_tc_nn: "(0::real) \<le> max tc 1" by simp
              have bA2: "real (depth_formula (spira_trans
                          (fix_at (spiras_sel_position P) True P))) \<le> max tc 1 * ?L"
                by (rule spira_trans_dep_le[OF tc_spec fix_at_wf[OF wfP] fixQT_le_P])
              have bB2: "real (depth_formula (spira_trans
                          (fix_at (spiras_sel_position P) False P))) \<le> max tc 1 * ?L"
                by (rule spira_trans_dep_le[OF tc_spec fix_at_wf[OF wfP] fixQF_le_P])
              have bC2: "real (depth_formula (spira_trans (fix_at pos True P)))
                       \<le> max tc 1 * ?L"
                by (rule spira_trans_dep_le[OF tc_spec fix_at_wf[OF wfP] fixPT_le_P])
              have bD2: "real (depth_formula (spira_trans (fix_at pos False P)))
                       \<le> max tc 1 * ?L"
                by (rule spira_trans_dep_le[OF tc_spec fix_at_wf[OF wfP] fixPF_le_P])
              have bE2: "real (depth_formula (spira_trans (fix_at s True ?R)))
                       \<le> max tc 1 * ?L"
                by (rule spira_trans_dep_le[OF tc_spec fix_at_wf[OF wfR] fixRT_le_P])
              have bF2: "real (depth_formula (spira_trans (fix_at s False ?R)))
                       \<le> max tc 1 * ?L"
                by (rule spira_trans_dep_le[OF tc_spec fix_at_wf[OF wfR] fixRF_le_P])
              have bG2: "real (depth_formula (spira_trans ?Q)) \<le> max tc 1 * ?L"
                by (rule spira_trans_dep_le[OF tc_spec wfQ2 Q_le_P])
              have bH2: "real (depth_formula (spira_trans ?R)) \<le> max tc 1 * ?L"
                by (rule spira_trans_dep_le[OF tc_spec wfR R_le_P])
              have sum_le2: "real ?dlsum2 \<le> 8 * (max tc 1 * ?L)"
                using bA2 bB2 bC2 bD2 bE2 bF2 bG2 bH2 by simp
              have glue_le2: "real (rebal_dep_coeff * (?dlsum2 + 1)) \<le> c * ?L"
              proof -
                have h1: "real (?dlsum2 + 1) \<le> 8 * (max tc 1 * ?L) + 1"
                  using sum_le2 by simp
                have c_ge: "real rebal_dep_coeff * (8 * max tc 1 + 1) \<le> c"
                  unfolding c_def by simp
                have "real (rebal_dep_coeff * (?dlsum2 + 1))
                    = real rebal_dep_coeff * real (?dlsum2 + 1)"
                  by (simp only: of_nat_mult)
                also have "\<dots> \<le> real rebal_dep_coeff * (8 * (max tc 1 * ?L) + 1)"
                  using h1 by (intro mult_left_mono) auto
                also have "\<dots> \<le> real rebal_dep_coeff * ((8 * max tc 1 + 1) * ?L)"
                proof -
                  have step3: "8 * (max tc 1 * ?L) + 1
                             \<le> (8 * max tc 1 + 1) * ?L"
                  proof -
                    have "8 * (max tc 1 * ?L) + 1 \<le> 8 * (max tc 1 * ?L) + ?L"
                      using logP1 by simp
                    also have "\<dots> = (8 * max tc 1 + 1) * ?L"
                      by (simp add: algebra_simps)
                    finally show ?thesis .
                  qed
                  show ?thesis using step3 by (intro mult_left_mono) auto
                qed
                also have "\<dots> = (real rebal_dep_coeff * (8 * max tc 1 + 1)) * ?L"
                  by (simp add: algebra_simps)
                also have "\<dots> \<le> c * ?L"
                  using c_ge logP1 by (intro mult_right_mono) auto
                finally show ?thesis .
              qed
              have all4: "real (max depT (max depF (max depR
                                    (rebal_dep_coeff * (?dlsum2 + 1)))))
                         \<le> c * ?L"
                using ihT_d ihF_d ihR_d glue_le2 by (simp add: of_nat_max)
              have "real dep \<le> real (max depT (max depF (max depR
                                         (rebal_dep_coeff * (?dlsum2 + 1)))))"
                using conD2 by simp
              also have "\<dots> \<le> c * ?L" by (rule all4)
              finally show ?thesis .
            qed
            show ?thesis using pbi lines_le sz_le dep_le by blast
          qed
        next
          case disj
          \<comment> \<open>Case 3: Q and R disjoint.\<close>
          have ge2: "len_formula P \<ge> 2"
            using geST unfolding spira_threshold_def by simp
          have vpq: "valid_position P (spiras_sel_position P)"
            using spiras_sel_position_spec[OF wfP ge2] by simp
          have dpq: "positions_disjoint pos (spiras_sel_position P)"
            by (subst positions_disjoint_sym, rule disj)
          have vp_Qb: "\<And>b. valid_position (fix_at (spiras_sel_position P) b P) pos"
            by (rule valid_position_fix_at_disjoint[OF dpq vpP])
          have vp_Rb: "\<And>b. valid_position (fix_at pos b P) (spiras_sel_position P)"
            by (rule valid_position_fix_at_disjoint[OF disj vpq])
          note meas = case_three_measure[OF wfP geST disj vpP]
          obtain lQT szQT depQT where IH_QT:
              "provable_balanced_iff
                 (spira_trans (fix_at (spiras_sel_position P) True P))
                 (rebalancing (fix_at (spiras_sel_position P) True P) pos)
                 lQT szQT depQT"
            and IH_QT_l: "lQT \<le> rebal_L (len_formula
                                  (fix_at (spiras_sel_position P) True P))
                                         (rebal_m
                                  (fix_at (spiras_sel_position P) True P) pos)"
            and IH_QT_s: "szQT \<le> rebal_L (len_formula
                                  (fix_at (spiras_sel_position P) True P))
                                         (rebal_m
                                  (fix_at (spiras_sel_position P) True P) pos)"
            and IH_QT_d: "real depQT \<le> c * log 2 (real (len_formula
                              (fix_at (spiras_sel_position P) True P)) + 1)"
            using less.hyps[OF conjunct1[OF meas] fix_at_wf[OF wfP] vp_Qb] by blast
          obtain lQF szQF depQF where IH_QF:
              "provable_balanced_iff
                 (spira_trans (fix_at (spiras_sel_position P) False P))
                 (rebalancing (fix_at (spiras_sel_position P) False P) pos)
                 lQF szQF depQF"
            and IH_QF_l: "lQF \<le> rebal_L (len_formula
                                  (fix_at (spiras_sel_position P) False P))
                                         (rebal_m
                                  (fix_at (spiras_sel_position P) False P) pos)"
            and IH_QF_s: "szQF \<le> rebal_L (len_formula
                                  (fix_at (spiras_sel_position P) False P))
                                         (rebal_m
                                  (fix_at (spiras_sel_position P) False P) pos)"
            and IH_QF_d: "real depQF \<le> c * log 2 (real (len_formula
                              (fix_at (spiras_sel_position P) False P)) + 1)"
            using less.hyps[OF conjunct1[OF conjunct2[OF meas]]
                             fix_at_wf[OF wfP] vp_Qb] by blast
          obtain lRT szRT depRT where IH_RT:
              "provable_balanced_iff (spira_trans (fix_at pos True P))
                 (rebalancing (fix_at pos True P) (spiras_sel_position P))
                 lRT szRT depRT"
            and IH_RT_l: "lRT \<le> rebal_L (len_formula (fix_at pos True P))
                                         (rebal_m (fix_at pos True P) (spiras_sel_position P))"
            and IH_RT_s: "szRT \<le> rebal_L (len_formula (fix_at pos True P))
                                         (rebal_m (fix_at pos True P) (spiras_sel_position P))"
            and IH_RT_d: "real depRT \<le> c * log 2 (real (len_formula
                              (fix_at pos True P)) + 1)"
            using less.hyps[OF conjunct1[OF conjunct2[OF conjunct2[OF meas]]]
                             fix_at_wf[OF wfP] vp_Rb] by blast
          obtain lRF szRF depRF where IH_RF:
              "provable_balanced_iff (spira_trans (fix_at pos False P))
                 (rebalancing (fix_at pos False P) (spiras_sel_position P))
                 lRF szRF depRF"
            and IH_RF_l: "lRF \<le> rebal_L (len_formula (fix_at pos False P))
                                         (rebal_m (fix_at pos False P) (spiras_sel_position P))"
            and IH_RF_s: "szRF \<le> rebal_L (len_formula (fix_at pos False P))
                                         (rebal_m (fix_at pos False P) (spiras_sel_position P))"
            and IH_RF_d: "real depRF \<le> c * log 2 (real (len_formula
                              (fix_at pos False P)) + 1)"
            using less.hyps[OF conjunct2[OF conjunct2[OF conjunct2[OF meas]]]
                             fix_at_wf[OF wfP] vp_Rb] by blast
          let ?Q = "subterm_at P (spiras_sel_position P)"
          let ?R = "subterm_at P pos"
          let ?cn = "rebal_cn (len_formula P)"
          let ?mP = "rebal_m P pos"
          let ?llsum3 =
            "len_formula (spira_trans (fix_at (spiras_sel_position P) True P))
           + len_formula (spira_trans (fix_at (spiras_sel_position P) False P))
           + len_formula (spira_trans (fix_at pos True P))
           + len_formula (spira_trans (fix_at pos False P))
           + len_formula (spira_trans
               (fix_at (spiras_sel_position P) True (fix_at pos True P)))
           + len_formula (spira_trans
               (fix_at (spiras_sel_position P) True (fix_at pos False P)))
           + len_formula (spira_trans
               (fix_at (spiras_sel_position P) False (fix_at pos True P)))
           + len_formula (spira_trans
               (fix_at (spiras_sel_position P) False (fix_at pos False P)))
           + len_formula (spira_trans ?Q)
           + len_formula (spira_trans ?R)"
          let ?dlsum3 =
            "depth_formula (spira_trans (fix_at (spiras_sel_position P) True P))
           + depth_formula (spira_trans (fix_at (spiras_sel_position P) False P))
           + depth_formula (spira_trans (fix_at pos True P))
           + depth_formula (spira_trans (fix_at pos False P))
           + depth_formula (spira_trans
               (fix_at (spiras_sel_position P) True (fix_at pos True P)))
           + depth_formula (spira_trans
               (fix_at (spiras_sel_position P) True (fix_at pos False P)))
           + depth_formula (spira_trans
               (fix_at (spiras_sel_position P) False (fix_at pos True P)))
           + depth_formula (spira_trans
               (fix_at (spiras_sel_position P) False (fix_at pos False P)))
           + depth_formula (spira_trans ?Q)
           + depth_formula (spira_trans ?R)"
          obtain sz dep where pbi:
              "provable_balanced_iff (spira_trans P) (rebalancing P pos)
                 (lQT + lQF + lRT + lRF + case_three_glue_lines) sz dep"
            and conS3: "sz \<le> szQT + szQF + szRT + szRF
                             + rebal_glue_coeff3 * (?llsum3 + 1)"
            and conD3: "dep \<le> max depQT (max depQF (max depRT (max depRF
                                (rebal_dep_coeff3 * (?dlsum3 + 1)))))"
            using case_three_construction[OF wfP geST disj IH_QT IH_QF IH_RT IH_RF]
            by blast
          \<comment> \<open>Size inequalities.\<close>
          have Q_eq: "?Q = spiras_sel P"
            using spiras_sel_position_spec[OF wfP ge2] by simp
          have Q_le_cn: "len_formula ?Q \<le> ?cn"
            using Q_eq spiras_sel_le_cn[OF wfP geST] by simp
          have Q_lt_P: "len_formula ?Q < len_formula P"
            using Q_eq spiras_sel_pred_when_wf[OF wfP ge2] by simp
          have Q_le_P: "len_formula ?Q \<le> len_formula P" using Q_lt_P by simp
          have Q_pos: "1 \<le> len_formula ?Q" by (rule len_formula_positive)
          have R_le_P: "len_formula ?R \<le> len_formula P"
            by (rule subterm_at_len_le[OF vpP])
          have R_pos: "1 \<le> len_formula ?R" by (rule len_formula_positive)
          \<comment> \<open>fix_at sizes.\<close>
          have fixQ_T_len: "len_formula (fix_at (spiras_sel_position P) True P)
                          = len_formula P - len_formula ?Q + 1"
            using fix_at_len_eq[OF vpq, of True] Q_le_P by linarith
          have fixQ_F_len: "len_formula (fix_at (spiras_sel_position P) False P)
                          = len_formula P - len_formula ?Q + 1"
            using fix_at_len_eq[OF vpq, of False] Q_le_P by linarith
          have fixP_T_len: "len_formula (fix_at pos True P)
                          = len_formula P - len_formula ?R + 1"
            using fix_at_len_eq[OF vpP, of True] R_le_P by linarith
          have fixP_F_len: "len_formula (fix_at pos False P)
                          = len_formula P - len_formula ?R + 1"
            using fix_at_len_eq[OF vpP, of False] R_le_P by linarith
          \<comment> \<open>IH_QT/QF first param: |fix_at q_pos b P| \<le> ?cn.\<close>
          have fixQ_T_le_cn: "len_formula (fix_at (spiras_sel_position P) True P) \<le> ?cn"
            using fixQ_T_len Q_eq P_minus_spira_le_cn[OF wfP geST] by simp
          have fixQ_F_le_cn: "len_formula (fix_at (spiras_sel_position P) False P) \<le> ?cn"
            using fixQ_F_len Q_eq P_minus_spira_le_cn[OF wfP geST] by simp
          \<comment> \<open>IH_RT/RF first param: |fix_at pos b P| \<le> ?mP.\<close>
          have fixP_T_le_mP: "len_formula (fix_at pos True P) \<le> ?mP"
            using fixP_T_len unfolding rebal_m_def by simp
          have fixP_F_le_mP: "len_formula (fix_at pos False P) \<le> ?mP"
            using fixP_F_len unfolding rebal_m_def by simp
          \<comment> \<open>Disjoint-position lemmas for the second-param fittings.\<close>
          have sub_fixQ_T: "subterm_at (fix_at (spiras_sel_position P) True P) pos = ?R"
            using subterm_at_fix_at_disjoint[OF dpq] by simp
          have sub_fixQ_F: "subterm_at (fix_at (spiras_sel_position P) False P) pos = ?R"
            using subterm_at_fix_at_disjoint[OF dpq] by simp
          have sub_fixP_T: "subterm_at (fix_at pos True P) (spiras_sel_position P) = ?Q"
            using subterm_at_fix_at_disjoint[OF disj] by simp
          have sub_fixP_F: "subterm_at (fix_at pos False P) (spiras_sel_position P) = ?Q"
            using subterm_at_fix_at_disjoint[OF disj] by simp
          \<comment> \<open>|R| \<le> |fix_at q_pos b P|: via subterm_at_len_le on the fixed formula.\<close>
          have R_le_fixQT: "len_formula ?R
                          \<le> len_formula (fix_at (spiras_sel_position P) True P)"
          proof -
            have "len_formula ?R
                = len_formula (subterm_at (fix_at (spiras_sel_position P) True P) pos)"
              using sub_fixQ_T by simp
            also have "\<dots> \<le> len_formula (fix_at (spiras_sel_position P) True P)"
              by (rule subterm_at_len_le[OF vp_Qb])
            finally show ?thesis .
          qed
          have R_le_fixQF: "len_formula ?R
                          \<le> len_formula (fix_at (spiras_sel_position P) False P)"
          proof -
            have "len_formula ?R
                = len_formula (subterm_at (fix_at (spiras_sel_position P) False P) pos)"
              using sub_fixQ_F by simp
            also have "\<dots> \<le> len_formula (fix_at (spiras_sel_position P) False P)"
              by (rule subterm_at_len_le[OF vp_Qb])
            finally show ?thesis .
          qed
          have Q_le_fixPT: "len_formula ?Q
                          \<le> len_formula (fix_at pos True P)"
          proof -
            have "len_formula ?Q
                = len_formula (subterm_at (fix_at pos True P) (spiras_sel_position P))"
              using sub_fixP_T by simp
            also have "\<dots> \<le> len_formula (fix_at pos True P)"
              by (rule subterm_at_len_le[OF vp_Rb])
            finally show ?thesis .
          qed
          have Q_le_fixPF: "len_formula ?Q
                          \<le> len_formula (fix_at pos False P)"
          proof -
            have "len_formula ?Q
                = len_formula (subterm_at (fix_at pos False P) (spiras_sel_position P))"
              using sub_fixP_F by simp
            also have "\<dots> \<le> len_formula (fix_at pos False P)"
              by (rule subterm_at_len_le[OF vp_Rb])
            finally show ?thesis .
          qed
          \<comment> \<open>m bounds for IH_QT/QF second param.\<close>
          have m_fixQ_T_le_cn:
            "rebal_m (fix_at (spiras_sel_position P) True P) pos \<le> ?cn"
          proof (rule rebal_m_fit[OF sub_fixQ_T])
            show "len_formula ?R \<le> ?cn"
            proof -
              have "len_formula ?R \<le> len_formula (fix_at (spiras_sel_position P) True P)"
                by (rule R_le_fixQT)
              also have "\<dots> \<le> ?cn" by (rule fixQ_T_le_cn)
              finally show ?thesis .
            qed
            show "len_formula (fix_at (spiras_sel_position P) True P)
                  - len_formula ?R + 1 \<le> ?cn"
            proof -
              have "len_formula (fix_at (spiras_sel_position P) True P)
                  - len_formula ?R + 1
                  \<le> len_formula (fix_at (spiras_sel_position P) True P)"
                using R_pos R_le_fixQT by linarith
              also have "\<dots> \<le> ?cn" by (rule fixQ_T_le_cn)
              finally show ?thesis .
            qed
          qed
          have m_fixQ_F_le_cn:
            "rebal_m (fix_at (spiras_sel_position P) False P) pos \<le> ?cn"
          proof (rule rebal_m_fit[OF sub_fixQ_F])
            show "len_formula ?R \<le> ?cn"
            proof -
              have "len_formula ?R \<le> len_formula (fix_at (spiras_sel_position P) False P)"
                by (rule R_le_fixQF)
              also have "\<dots> \<le> ?cn" by (rule fixQ_F_le_cn)
              finally show ?thesis .
            qed
            show "len_formula (fix_at (spiras_sel_position P) False P)
                  - len_formula ?R + 1 \<le> ?cn"
            proof -
              have "len_formula (fix_at (spiras_sel_position P) False P)
                  - len_formula ?R + 1
                  \<le> len_formula (fix_at (spiras_sel_position P) False P)"
                using R_pos R_le_fixQF by linarith
              also have "\<dots> \<le> ?cn" by (rule fixQ_F_le_cn)
              finally show ?thesis .
            qed
          qed
          \<comment> \<open>m bounds for IH_RT/RF second param.\<close>
          have m_fixP_T_le_cn:
            "rebal_m (fix_at pos True P) (spiras_sel_position P) \<le> ?cn"
          proof (rule rebal_m_fit[OF sub_fixP_T])
            show "len_formula ?Q \<le> ?cn" by (rule Q_le_cn)
            have Q_le_PR1: "len_formula ?Q \<le> len_formula P - len_formula ?R + 1"
              using Q_le_fixPT fixP_T_len by simp
            show "len_formula (fix_at pos True P) - len_formula ?Q + 1 \<le> ?cn"
            proof -
              have "len_formula (fix_at pos True P) - len_formula ?Q + 1
                  = (len_formula P - len_formula ?R + 1) - len_formula ?Q + 1"
                using fixP_T_len by simp
              also have "\<dots> \<le> len_formula P - len_formula ?Q + 1"
                using R_pos Q_le_PR1 R_le_P Q_le_P by linarith
              also have "\<dots> \<le> ?cn"
                using Q_eq P_minus_spira_le_cn[OF wfP geST] by simp
              finally show ?thesis .
            qed
          qed
          have m_fixP_F_le_cn:
            "rebal_m (fix_at pos False P) (spiras_sel_position P) \<le> ?cn"
          proof (rule rebal_m_fit[OF sub_fixP_F])
            show "len_formula ?Q \<le> ?cn" by (rule Q_le_cn)
            have Q_le_PR1: "len_formula ?Q \<le> len_formula P - len_formula ?R + 1"
              using Q_le_fixPF fixP_F_len by simp
            show "len_formula (fix_at pos False P) - len_formula ?Q + 1 \<le> ?cn"
            proof -
              have "len_formula (fix_at pos False P) - len_formula ?Q + 1
                  = (len_formula P - len_formula ?R + 1) - len_formula ?Q + 1"
                using fixP_F_len by simp
              also have "\<dots> \<le> len_formula P - len_formula ?Q + 1"
                using R_pos Q_le_PR1 R_le_P Q_le_P by linarith
              also have "\<dots> \<le> ?cn"
                using Q_eq P_minus_spira_le_cn[OF wfP geST] by simp
              finally show ?thesis .
            qed
          qed
          \<comment> \<open>IH fittings.\<close>
          have lQT_le: "lQT \<le> rebal_L ?cn ?cn"
            using IH_QT_l rebal_L_mono[OF fixQ_T_le_cn m_fixQ_T_le_cn]
            by (rule order_trans)
          have lQF_le: "lQF \<le> rebal_L ?cn ?cn"
            using IH_QF_l rebal_L_mono[OF fixQ_F_le_cn m_fixQ_F_le_cn]
            by (rule order_trans)
          have lRT_le: "lRT \<le> rebal_L ?mP ?cn"
            using IH_RT_l rebal_L_mono[OF fixP_T_le_mP m_fixP_T_le_cn]
            by (rule order_trans)
          have lRF_le: "lRF \<le> rebal_L ?mP ?cn"
            using IH_RF_l rebal_L_mono[OF fixP_F_le_mP m_fixP_F_le_cn]
            by (rule order_trans)
          have glue_le: "case_three_glue_lines
                       \<le> rebal_glue_K * (len_formula P) ^ rebal_deg"
            by (rule rebal_glue_const_bound[OF _ lP1]) (simp add: rebal_base_K_def)
          have step: "case_three_glue_lines + 2 * rebal_L ?cn ?cn
                    + 2 * rebal_L ?mP ?cn
                    \<le> rebal_L (len_formula P) ?mP"
            by (rule rebal_L_step[OF geT glue_le])
          have lines_le:
            "(lQT + lQF + lRT + lRF + case_three_glue_lines)
             \<le> rebal_L (len_formula P) ?mP"
          proof -
            have "lQT + lQF + lRT + lRF + case_three_glue_lines
                \<le> rebal_L ?cn ?cn + rebal_L ?cn ?cn + rebal_L ?mP ?cn
                  + rebal_L ?mP ?cn + case_three_glue_lines"
              using lQT_le lQF_le lRT_le lRF_le by linarith
            also have "\<dots> = case_three_glue_lines + 2 * rebal_L ?cn ?cn
                          + 2 * rebal_L ?mP ?cn" by simp
            also have "\<dots> \<le> rebal_L (len_formula P) ?mP" using step .
            finally show ?thesis .
          qed
          have wfQ3: "formula_well_formed (alphabet F) ?Q"
            using subterm_at_wf[OF wfP vpq] .
          have wfR3: "formula_well_formed (alphabet F) ?R"
            using subterm_at_wf[OF wfP vpP] .
          have fixQT_le_P: "len_formula (fix_at (spiras_sel_position P) True P)
                          \<le> len_formula P" by (rule fix_at_len_le)
          have fixQF_le_P: "len_formula (fix_at (spiras_sel_position P) False P)
                          \<le> len_formula P" by (rule fix_at_len_le)
          have fixPT_le_P: "len_formula (fix_at pos True P) \<le> len_formula P"
            by (rule fix_at_len_le)
          have fixPF_le_P: "len_formula (fix_at pos False P) \<le> len_formula P"
            by (rule fix_at_len_le)
          have dfix_TT_le_P: "len_formula
              (fix_at (spiras_sel_position P) True (fix_at pos True P))
            \<le> len_formula P"
            using fix_at_len_le fixPT_le_P by (rule order_trans)
          have dfix_TF_le_P: "len_formula
              (fix_at (spiras_sel_position P) True (fix_at pos False P))
            \<le> len_formula P"
            using fix_at_len_le fixPF_le_P by (rule order_trans)
          have dfix_FT_le_P: "len_formula
              (fix_at (spiras_sel_position P) False (fix_at pos True P))
            \<le> len_formula P"
            using fix_at_len_le fixPT_le_P by (rule order_trans)
          have dfix_FF_le_P: "len_formula
              (fix_at (spiras_sel_position P) False (fix_at pos False P))
            \<le> len_formula P"
            using fix_at_len_le fixPF_le_P by (rule order_trans)
          have leafA3: "len_formula (spira_trans
              (fix_at (spiras_sel_position P) True P))
            \<le> poly rebal_tb (len_formula P)"
            by (rule spira_trans_len_le_tb[OF fix_at_wf[OF wfP] fixQT_le_P])
          have leafB3: "len_formula (spira_trans
              (fix_at (spiras_sel_position P) False P))
            \<le> poly rebal_tb (len_formula P)"
            by (rule spira_trans_len_le_tb[OF fix_at_wf[OF wfP] fixQF_le_P])
          have leafC3: "len_formula (spira_trans (fix_at pos True P))
            \<le> poly rebal_tb (len_formula P)"
            by (rule spira_trans_len_le_tb[OF fix_at_wf[OF wfP] fixPT_le_P])
          have leafD3: "len_formula (spira_trans (fix_at pos False P))
            \<le> poly rebal_tb (len_formula P)"
            by (rule spira_trans_len_le_tb[OF fix_at_wf[OF wfP] fixPF_le_P])
          have leafE3: "len_formula (spira_trans
              (fix_at (spiras_sel_position P) True (fix_at pos True P)))
            \<le> poly rebal_tb (len_formula P)"
            by (rule spira_trans_len_le_tb[OF fix_at_wf[OF fix_at_wf[OF wfP]] dfix_TT_le_P])
          have leafF3: "len_formula (spira_trans
              (fix_at (spiras_sel_position P) True (fix_at pos False P)))
            \<le> poly rebal_tb (len_formula P)"
            by (rule spira_trans_len_le_tb[OF fix_at_wf[OF fix_at_wf[OF wfP]] dfix_TF_le_P])
          have leafG3: "len_formula (spira_trans
              (fix_at (spiras_sel_position P) False (fix_at pos True P)))
            \<le> poly rebal_tb (len_formula P)"
            by (rule spira_trans_len_le_tb[OF fix_at_wf[OF fix_at_wf[OF wfP]] dfix_FT_le_P])
          have leafH3: "len_formula (spira_trans
              (fix_at (spiras_sel_position P) False (fix_at pos False P)))
            \<le> poly rebal_tb (len_formula P)"
            by (rule spira_trans_len_le_tb[OF fix_at_wf[OF fix_at_wf[OF wfP]] dfix_FF_le_P])
          have leafI3: "len_formula (spira_trans ?Q)
                     \<le> poly rebal_tb (len_formula P)"
            by (rule spira_trans_len_le_tb[OF wfQ3 Q_le_P])
          have leafJ3: "len_formula (spira_trans ?R)
                     \<le> poly rebal_tb (len_formula P)"
            by (rule spira_trans_len_le_tb[OF wfR3 R_le_P])
          have llsum3_le: "?llsum3 \<le> 10 * poly rebal_tb (len_formula P)"
            using leafA3 leafB3 leafC3 leafD3 leafE3 leafF3 leafG3 leafH3
                  leafI3 leafJ3 by simp
          have glue_sz3: "rebal_glue_coeff3 * (?llsum3 + 1)
                       \<le> rebal_glue_K * (len_formula P) ^ rebal_deg"
            by (rule rebal_glue_poly_bound[OF _ llsum3_le lP1])
               (simp add: rebal_base_K_def)
          have step_sz3: "rebal_glue_coeff3 * (?llsum3 + 1)
                        + 2 * rebal_L ?cn ?cn + 2 * rebal_L ?mP ?cn
                        \<le> rebal_L (len_formula P) ?mP"
            by (rule rebal_L_step[OF geT glue_sz3])
          have szQT_le: "szQT \<le> rebal_L ?cn ?cn"
            using IH_QT_s rebal_L_mono[OF fixQ_T_le_cn m_fixQ_T_le_cn]
            by (rule order_trans)
          have szQF_le: "szQF \<le> rebal_L ?cn ?cn"
            using IH_QF_s rebal_L_mono[OF fixQ_F_le_cn m_fixQ_F_le_cn]
            by (rule order_trans)
          have szRT_le: "szRT \<le> rebal_L ?mP ?cn"
            using IH_RT_s rebal_L_mono[OF fixP_T_le_mP m_fixP_T_le_cn]
            by (rule order_trans)
          have szRF_le: "szRF \<le> rebal_L ?mP ?cn"
            using IH_RF_s rebal_L_mono[OF fixP_F_le_mP m_fixP_F_le_cn]
            by (rule order_trans)
          have sz_le: "sz \<le> rebal_L (len_formula P) ?mP"
          proof -
            have "sz \<le> szQT + szQF + szRT + szRF
                       + rebal_glue_coeff3 * (?llsum3 + 1)" by (rule conS3)
            also have "\<dots> \<le> rebal_L ?cn ?cn + rebal_L ?cn ?cn
                          + rebal_L ?mP ?cn + rebal_L ?mP ?cn
                          + rebal_glue_coeff3 * (?llsum3 + 1)"
              using szQT_le szQF_le szRT_le szRF_le by linarith
            also have "\<dots> = rebal_glue_coeff3 * (?llsum3 + 1)
                          + 2 * rebal_L ?cn ?cn + 2 * rebal_L ?mP ?cn" by simp
            also have "\<dots> \<le> rebal_L (len_formula P) ?mP" using step_sz3 .
            finally show ?thesis .
          qed
          have dep_le: "real dep \<le> c * log 2 (real (len_formula P) + 1)"
          proof -
            let ?L = "log 2 (real (len_formula P) + 1)"
            have c_pos: "0 \<le> c" by (rule c_nn)
            have log_le: "\<And>n. n \<le> len_formula P \<Longrightarrow>
                log 2 (real n + 1) \<le> ?L"
              by (intro log_mono) auto
            have ihQT_d: "real depQT \<le> c * ?L"
            proof -
              have "real depQT \<le> c * log 2 (real (len_formula
                      (fix_at (spiras_sel_position P) True P)) + 1)" by (rule IH_QT_d)
              also have "\<dots> \<le> c * ?L"
                using log_le[OF fixQT_le_P] c_pos by (intro mult_left_mono)
              finally show ?thesis .
            qed
            have ihQF_d: "real depQF \<le> c * ?L"
            proof -
              have "real depQF \<le> c * log 2 (real (len_formula
                      (fix_at (spiras_sel_position P) False P)) + 1)" by (rule IH_QF_d)
              also have "\<dots> \<le> c * ?L"
                using log_le[OF fixQF_le_P] c_pos by (intro mult_left_mono)
              finally show ?thesis .
            qed
            have ihRT_d: "real depRT \<le> c * ?L"
            proof -
              have "real depRT \<le> c * log 2 (real (len_formula (fix_at pos True P)) + 1)"
                by (rule IH_RT_d)
              also have "\<dots> \<le> c * ?L"
                using log_le[OF fixPT_le_P] c_pos by (intro mult_left_mono)
              finally show ?thesis .
            qed
            have ihRF_d: "real depRF \<le> c * ?L"
            proof -
              have "real depRF \<le> c * log 2 (real (len_formula (fix_at pos False P)) + 1)"
                by (rule IH_RF_d)
              also have "\<dots> \<le> c * ?L"
                using log_le[OF fixPF_le_P] c_pos by (intro mult_left_mono)
              finally show ?thesis .
            qed
            have max_tc_nn: "(0::real) \<le> max tc 1" by simp
            have bA3: "real (depth_formula (spira_trans
                        (fix_at (spiras_sel_position P) True P))) \<le> max tc 1 * ?L"
              by (rule spira_trans_dep_le[OF tc_spec fix_at_wf[OF wfP] fixQT_le_P])
            have bB3: "real (depth_formula (spira_trans
                        (fix_at (spiras_sel_position P) False P))) \<le> max tc 1 * ?L"
              by (rule spira_trans_dep_le[OF tc_spec fix_at_wf[OF wfP] fixQF_le_P])
            have bC3: "real (depth_formula (spira_trans (fix_at pos True P)))
                     \<le> max tc 1 * ?L"
              by (rule spira_trans_dep_le[OF tc_spec fix_at_wf[OF wfP] fixPT_le_P])
            have bD3: "real (depth_formula (spira_trans (fix_at pos False P)))
                     \<le> max tc 1 * ?L"
              by (rule spira_trans_dep_le[OF tc_spec fix_at_wf[OF wfP] fixPF_le_P])
            have bE3: "real (depth_formula (spira_trans
                (fix_at (spiras_sel_position P) True (fix_at pos True P))))
              \<le> max tc 1 * ?L"
              by (rule spira_trans_dep_le[OF tc_spec fix_at_wf[OF fix_at_wf[OF wfP]] dfix_TT_le_P])
            have bF3: "real (depth_formula (spira_trans
                (fix_at (spiras_sel_position P) True (fix_at pos False P))))
              \<le> max tc 1 * ?L"
              by (rule spira_trans_dep_le[OF tc_spec fix_at_wf[OF fix_at_wf[OF wfP]] dfix_TF_le_P])
            have bG3: "real (depth_formula (spira_trans
                (fix_at (spiras_sel_position P) False (fix_at pos True P))))
              \<le> max tc 1 * ?L"
              by (rule spira_trans_dep_le[OF tc_spec fix_at_wf[OF fix_at_wf[OF wfP]] dfix_FT_le_P])
            have bH3: "real (depth_formula (spira_trans
                (fix_at (spiras_sel_position P) False (fix_at pos False P))))
              \<le> max tc 1 * ?L"
              by (rule spira_trans_dep_le[OF tc_spec fix_at_wf[OF fix_at_wf[OF wfP]] dfix_FF_le_P])
            have bI3: "real (depth_formula (spira_trans ?Q)) \<le> max tc 1 * ?L"
              by (rule spira_trans_dep_le[OF tc_spec wfQ3 Q_le_P])
            have bJ3: "real (depth_formula (spira_trans ?R)) \<le> max tc 1 * ?L"
              by (rule spira_trans_dep_le[OF tc_spec wfR3 R_le_P])
            have sum3_le: "real ?dlsum3 \<le> 10 * (max tc 1 * ?L)"
              using bA3 bB3 bC3 bD3 bE3 bF3 bG3 bH3 bI3 bJ3 by simp
            have glue_le3: "real (rebal_dep_coeff3 * (?dlsum3 + 1)) \<le> c * ?L"
            proof -
              have h1: "real (?dlsum3 + 1) \<le> 10 * (max tc 1 * ?L) + 1"
                using sum3_le by simp
              have c_ge: "real rebal_dep_coeff3 * (10 * max tc 1 + 1) \<le> c"
                unfolding c_def by simp
              have "real (rebal_dep_coeff3 * (?dlsum3 + 1))
                  = real rebal_dep_coeff3 * real (?dlsum3 + 1)"
                by (simp only: of_nat_mult)
              also have "\<dots> \<le> real rebal_dep_coeff3 * (10 * (max tc 1 * ?L) + 1)"
                using h1 by (intro mult_left_mono) auto
              also have "\<dots> \<le> real rebal_dep_coeff3 * ((10 * max tc 1 + 1) * ?L)"
              proof -
                have step3: "10 * (max tc 1 * ?L) + 1
                           \<le> (10 * max tc 1 + 1) * ?L"
                proof -
                  have "10 * (max tc 1 * ?L) + 1 \<le> 10 * (max tc 1 * ?L) + ?L"
                    using logP1 by simp
                  also have "\<dots> = (10 * max tc 1 + 1) * ?L"
                    by (simp add: algebra_simps)
                  finally show ?thesis .
                qed
                show ?thesis using step3 by (intro mult_left_mono) auto
              qed
              also have "\<dots> = (real rebal_dep_coeff3 * (10 * max tc 1 + 1)) * ?L"
                by (simp add: algebra_simps)
              also have "\<dots> \<le> c * ?L"
                using c_ge logP1 by (intro mult_right_mono) auto
              finally show ?thesis .
            qed
            have all5: "real (max depQT (max depQF (max depRT (max depRF
                                  (rebal_dep_coeff3 * (?dlsum3 + 1))))))
                       \<le> c * ?L"
              using ihQT_d ihQF_d ihRT_d ihRF_d glue_le3
              by (simp only: of_nat_max max.bounded_iff)
            have "real dep \<le> real (max depQT (max depQF (max depRT (max depRF
                                         (rebal_dep_coeff3 * (?dlsum3 + 1))))))"
              using conD3 by (simp only: of_nat_le_iff)
            from order_trans[OF this all5] show ?thesis .
          qed
          show ?thesis using pbi lines_le sz_le dep_le by blast
        qed
      qed
    qed
  qed
  qed

  show ?thesis
  proof (intro exI[where x = bnd] exI[where x = c] allI impI)
    fix P pos
    assume a: "formula_well_formed (alphabet F) P \<and> valid_position P pos"
    hence wfP: "formula_well_formed (alphabet F) P"
      and vpP: "valid_position P pos" by auto
    from main[OF wfP vpP] obtain lines sz dep where
        m: "provable_balanced_iff (spira_trans P) (rebalancing P pos) lines sz dep"
      and ml: "lines \<le> rebal_L (len_formula P) (rebal_m P pos)"
      and ms: "sz \<le> rebal_L (len_formula P) (rebal_m P pos)"
      and md: "real dep \<le> c * log 2 (real (len_formula P) + 1)"
      by blast
    have lemL: "rebal_L (len_formula P) (rebal_m P pos)
              \<le> rebal_L (len_formula P) (len_formula P)"
      using rebal_m_le[OF vpP] by (rule rebal_L_mono[OF order_refl])
    have lemL': "rebal_L (len_formula P) (len_formula P) = poly bnd (len_formula P)"
      using bnd_eval[symmetric] by simp
    have lb: "lines \<le> poly bnd (len_formula P)" using ml lemL lemL' by simp
    have sb: "sz \<le> poly bnd (len_formula P)" using ms lemL lemL' by simp
    show "\<exists> lines sz dep. provable_balanced_iff (spira_trans P) (rebalancing P pos) lines sz dep
                       \<and> lines \<le> poly bnd (len_formula P)
                       \<and> sz \<le> poly bnd (len_formula P)
                       \<and> real dep \<le> c * log 2 (real (len_formula P) + 1)"
      using m lb sb md by blast
  qed
qed

end
end
