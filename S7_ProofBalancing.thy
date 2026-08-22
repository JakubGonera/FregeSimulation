theory S7_ProofBalancing
  imports S6_Comprehension
begin

section \<open>Conclusion of the proof (Filmus section 7)\<close>

context frege_closure
begin

subsection \<open>Bounded derivations from premises\<close>

(*
  derives_balanced asms B lines sz dep: there is a Frege derivation of B from
  assumptions contained in asms, with at most "lines" steps, every step of
  length at most "sz" and depth at most "dep". This generalises
  provable_balanced_iff from no-assumption iff proofs to derivations from
  premises --- the judgment in which a rule application of the original proof
  is simulated on the balanced translations.
*)
definition derives_balanced where
  "derives_balanced asms B (lines :: nat) (sz :: nat) (dep :: nat) \<longleftrightarrow>
     (\<exists>pr. valid_proof F pr \<and> assumptions pr \<subseteq> asms
           \<and> thesis pr = B
           \<and> length (steps pr) \<le> lines
           \<and> (\<forall>s \<in> set (steps pr). len_formula s \<le> sz)
           \<and> (\<forall>s \<in> set (steps pr). depth_formula s \<le> dep)
           \<and> (\<forall>s \<in> set (steps pr). formula_well_formed (alphabet F) s))"

subsection \<open>Eliminating a proven equivalence: the modus ponens converter\<close>

(*
  The modus ponens base proof: from x and x \<longleftrightarrow> y conclude y, over the two
  fresh atoms already introduced for iff_sym. Substituting actual formulas
  for the two atoms turns a proven equivalence A \<longleftrightarrow> B into a derivation of B
  from the assumption A.
*)
definition mp_base_proof where
  "mp_base_proof =
     entails_proof {Atom sym_atom_x, iff_form (Atom sym_atom_x) (Atom sym_atom_y)}
                   (Atom sym_atom_y)"

lemma mp_base_proof_spec:
  "valid_proof F mp_base_proof
   \<and> assumptions mp_base_proof
       = {Atom sym_atom_x, iff_form (Atom sym_atom_x) (Atom sym_atom_y)}
   \<and> thesis mp_base_proof = Atom sym_atom_y
   \<and> (\<forall>st \<in> set (steps mp_base_proof). formula_well_formed (alphabet F) st)"
proof -
  have sem: "\<forall>val. (\<forall>f \<in> {Atom sym_atom_x, iff_form (Atom sym_atom_x) (Atom sym_atom_y)}.
                eval (alphabet F) val f)
              \<longrightarrow> eval (alphabet F) val (Atom sym_atom_y)"
    using iff_form_eval by auto
  have wf_fs: "\<forall>f \<in> {Atom sym_atom_x, iff_form (Atom sym_atom_x) (Atom sym_atom_y)}.
                 formula_well_formed (alphabet F) f"
    by (auto intro: iff_form_wf)
  have wf_th: "formula_well_formed (alphabet F) (Atom sym_atom_y)" by simp
  show ?thesis
    unfolding mp_base_proof_def
    using entails_proof_spec[OF wf_fs wf_th sem] .
qed

definition mp_lines where
  "mp_lines = length (steps mp_base_proof)"

definition mp_step_len where
  "mp_step_len = Max (insert 1 (len_formula ` set (steps mp_base_proof)))"

definition mp_step_depth where
  "mp_step_depth = Max (insert 1 (depth_formula ` set (steps mp_base_proof)))"

(*
  The converter: a no-assumption proof of A \<longleftrightarrow> B followed by the substituted
  modus ponens base proof is a derivation of B from the single assumption A.
*)
lemma iff_elimination:
  assumes "provable_balanced_iff A B l s d"
      and wfA: "formula_well_formed (alphabet F) A"
      and wfB: "formula_well_formed (alphabet F) B"
  shows "\<exists>cv. valid_proof F cv \<and> assumptions cv \<subseteq> {A}
            \<and> frege_proof.thesis cv = B
            \<and> length (steps cv) \<le> l + mp_lines
            \<and> (\<forall>st \<in> set (steps cv).
                 len_formula st
                   \<le> max s (mp_step_len * (len_formula A + len_formula B)))
            \<and> (\<forall>st \<in> set (steps cv).
                 depth_formula st
                   \<le> max d (mp_step_depth
                        + max (depth_formula A) (depth_formula B)))
            \<and> (\<forall>st \<in> set (steps cv). formula_well_formed (alphabet F) st)"
proof -
  have fs_F: "frege_system F"
    by (meson frege_balancing_axioms frege_balancing_def)
  let ?x = "sym_atom_x" and ?y = "sym_atom_y"
  let ?sub = "\<lambda>w. if w = ?x then A else if w = ?y then B else Atom w"
  have neq: "?x \<noteq> ?y" using sym_atoms_spec by blast
  from assms(1) obtain pAB where pAB:
    "valid_proof F pAB" "assumptions pAB = {}"
    "frege_proof.thesis pAB = iff_form A B"
    "length (steps pAB) \<le> l"
    "\<forall>st \<in> set (steps pAB). len_formula st \<le> s"
    "\<forall>st \<in> set (steps pAB). depth_formula st \<le> d"
    "\<forall>st \<in> set (steps pAB). formula_well_formed (alphabet F) st"
    unfolding provable_balanced_iff_def by blast
  have sub_conn_iff:
    "\<And>w. w \<in> var_set_form conn_iff \<Longrightarrow> w \<noteq> ''a'' \<Longrightarrow> w \<noteq> ''b''
           \<Longrightarrow> ?sub w = Atom w"
  proof -
    fix w assume w_ci: "w \<in> var_set_form conn_iff" and "w \<noteq> ''a''" and "w \<noteq> ''b''"
    have "w \<in> avoid_atoms" using w_ci unfolding avoid_atoms_def by blast
    hence "w \<noteq> ?x \<and> w \<noteq> ?y" using sym_atoms_spec by blast
    thus "?sub w = Atom w" by simp
  qed
  have sub_id: "\<forall>v. v \<notin> {?x, ?y} \<longrightarrow> ?sub v = Atom v" by auto
  have fin_xy: "finite {?x, ?y}" by simp
  define mi where mi_def: "mi = sub_proof ?sub mp_base_proof"
  have valid_mi: "valid_proof F mi"
    unfolding mi_def
    using frege_system.proof_substitution[OF fs_F] mp_base_proof_spec by blast
  have mi_steps: "steps mi = map (sub_formula ?sub) (steps mp_base_proof)"
    unfolding mi_def by simp
  have mi_thesis: "frege_proof.thesis mi = B"
  proof -
    have "frege_proof.thesis mi = sub_formula ?sub (Atom ?y)"
      unfolding mi_def using mp_base_proof_spec by simp
    thus ?thesis using neq by simp
  qed
  have mi_asm: "assumptions mi = {A, iff_form A B}"
  proof -
    have sub_iff: "sub_formula ?sub (iff_form (Atom ?x) (Atom ?y)) = iff_form A B"
    proof -
      have "sub_formula ?sub (iff_form (Atom ?x) (Atom ?y))
          = iff_form (sub_formula ?sub (Atom ?x)) (sub_formula ?sub (Atom ?y))"
        by (rule sub_formula_iff_form[OF sub_conn_iff])
      also have "\<dots> = iff_form A B" using neq by simp
      finally show ?thesis .
    qed
    have "assumptions mi = (sub_formula ?sub) ` (assumptions mp_base_proof)"
      unfolding mi_def by simp
    also have "\<dots> = (sub_formula ?sub) `
         {Atom ?x, iff_form (Atom ?x) (Atom ?y)}"
      using mp_base_proof_spec by simp
    also have "\<dots> = {A, iff_form A B}" using sub_iff by simp
    finally show ?thesis .
  qed
  have mi_lines: "length (steps mi) = mp_lines"
    using mi_steps by (simp add: mp_lines_def)
  have len_sub_eq: "len_sub {?x, ?y} ?sub = len_formula A + len_formula B"
  proof -
    have "(\<Sum>v \<in> {?x, ?y}. len_formula (?sub v)) = len_formula A + len_formula B"
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
  define cv where cv_def: "cv = combine_proofs pAB mi"
  have valid_cv: "valid_proof F cv"
    unfolding cv_def
    using frege_system.combining_valid_proofs[OF fs_F] pAB(1) valid_mi by blast
  have iffin: "iff_form A B \<in> set (steps pAB)"
  proof -
    have ne: "steps pAB \<noteq> []" using pAB(1) unfolding valid_proof_def by simp
    have "frege_proof.thesis pAB = last (steps pAB)"
      using pAB(1) unfolding valid_proof_def by simp
    hence "iff_form A B = last (steps pAB)" using pAB(3) by simp
    moreover have "last (steps pAB) \<in> set (steps pAB)" using ne by (rule last_in_set)
    ultimately show ?thesis by simp
  qed
  have cv_asm: "assumptions cv \<subseteq> {A}"
  proof -
    have "assumptions cv = assumptions pAB \<union> (assumptions mi - set (steps pAB))"
      unfolding cv_def by simp
    also have "\<dots> = {A, iff_form A B} - set (steps pAB)"
      using pAB(2) mi_asm by simp
    also have "\<dots> \<subseteq> {A}" using iffin by blast
    finally show ?thesis .
  qed
  have cv_thesis: "frege_proof.thesis cv = B"
    unfolding cv_def using mi_thesis by simp
  have cv_steps: "steps cv = steps pAB @ steps mi"
    unfolding cv_def by simp
  have cv_lines: "length (steps cv) \<le> l + mp_lines"
    using cv_steps pAB(4) mi_lines by simp
  have fin_ml: "finite (insert 1 (len_formula ` set (steps mp_base_proof)))" by simp
  have fin_md: "finite (insert 1 (depth_formula ` set (steps mp_base_proof)))" by simp
  have cv_len: "\<forall>st \<in> set (steps cv).
                  len_formula st
                    \<le> max s (mp_step_len * (len_formula A + len_formula B))"
  proof
    fix st assume "st \<in> set (steps cv)"
    hence "st \<in> set (steps pAB) \<or> st \<in> set (steps mi)" using cv_steps by auto
    thus "len_formula st \<le> max s (mp_step_len * (len_formula A + len_formula B))"
    proof (elim disjE)
      assume "st \<in> set (steps pAB)"
      hence "len_formula st \<le> s" using pAB(5) by blast
      thus ?thesis by simp
    next
      assume "st \<in> set (steps mi)"
      then obtain st0 where st0_in: "st0 \<in> set (steps mp_base_proof)"
                        and st_eq: "st = sub_formula ?sub st0"
        using mi_steps by auto
      have "len_formula st \<le> len_formula st0 * len_sub {?x, ?y} ?sub"
        using st_eq sub_formula_bound[OF fin_xy sub_id] by simp
      also have "\<dots> = len_formula st0 * (len_formula A + len_formula B)"
        using len_sub_eq by simp
      also have "\<dots> \<le> mp_step_len * (len_formula A + len_formula B)"
      proof -
        have "len_formula st0 \<in> insert 1 (len_formula ` set (steps mp_base_proof))"
          using st0_in by simp
        hence "len_formula st0 \<le> mp_step_len"
          unfolding mp_step_len_def using Max_ge[OF fin_ml] by blast
        thus ?thesis by (rule mult_le_mono1)
      qed
      finally show ?thesis by simp
    qed
  qed
  have cv_dep: "\<forall>st \<in> set (steps cv).
                  depth_formula st
                    \<le> max d (mp_step_depth
                         + max (depth_formula A) (depth_formula B))"
  proof
    fix st assume "st \<in> set (steps cv)"
    hence "st \<in> set (steps pAB) \<or> st \<in> set (steps mi)" using cv_steps by auto
    thus "depth_formula st
            \<le> max d (mp_step_depth + max (depth_formula A) (depth_formula B))"
    proof (elim disjE)
      assume "st \<in> set (steps pAB)"
      hence "depth_formula st \<le> d" using pAB(6) by blast
      thus ?thesis by simp
    next
      assume "st \<in> set (steps mi)"
      then obtain st0 where st0_in: "st0 \<in> set (steps mp_base_proof)"
                        and st_eq: "st = sub_formula ?sub st0"
        using mi_steps by auto
      have "depth_formula st \<le> depth_formula st0 + depth_sub {?x, ?y} ?sub"
        using st_eq sub_formula_depth_bound[OF fin_xy sub_id] by simp
      also have "\<dots> \<le> mp_step_depth + max (depth_formula A) (depth_formula B)"
      proof -
        have "depth_formula st0 \<in> insert 1 (depth_formula ` set (steps mp_base_proof))"
          using st0_in by simp
        hence dst0: "depth_formula st0 \<le> mp_step_depth"
          unfolding mp_step_depth_def using Max_ge[OF fin_md] by blast
        show ?thesis by (rule add_le_mono[OF dst0 depth_sub_le])
      qed
      finally show ?thesis by simp
    qed
  qed
  have sub_wf: "\<And>w. formula_well_formed (alphabet F) (?sub w)"
    using wfA wfB by simp
  have mi_wf: "\<forall>st \<in> set (steps mi). formula_well_formed (alphabet F) st"
  proof
    fix st assume "st \<in> set (steps mi)"
    then obtain st0 where st0_in: "st0 \<in> set (steps mp_base_proof)"
      and st_eq: "st = sub_formula ?sub st0" using mi_steps by auto
    have "formula_well_formed (alphabet F) st0"
      using mp_base_proof_spec st0_in by blast
    thus "formula_well_formed (alphabet F) st"
      unfolding st_eq by (rule sub_formula_well_formed[OF _ sub_wf])
  qed
  have cv_wf: "\<forall>st \<in> set (steps cv). formula_well_formed (alphabet F) st"
  proof
    fix st assume "st \<in> set (steps cv)"
    hence "st \<in> set (steps pAB) \<or> st \<in> set (steps mi)" using cv_steps by auto
    thus "formula_well_formed (alphabet F) st"
      using pAB(7) mi_wf by (elim disjE) blast+
  qed
  show ?thesis
    using valid_cv cv_asm cv_thesis cv_lines cv_len cv_dep cv_wf by blast
qed

subsection \<open>Folding derivations that carry assumptions\<close>

(*
  combine_fold_spec generalised: the folded proofs may carry assumptions.
  The fold is valid, proves the base's thesis, and assumes at most the union
  of the folded proofs' assumptions plus whatever base assumptions no folded
  proof establishes as a step.
*)
lemma combine_fold_asms:
  shows "valid_proof F base \<longrightarrow> (\<forall>p \<in> set ps. valid_proof F p) \<longrightarrow>
         (valid_proof F (foldr combine_proofs ps base)
          \<and> assumptions (foldr combine_proofs ps base)
              \<subseteq> (\<Union>p \<in> set ps. assumptions p)
                \<union> (assumptions base - (\<Union>p \<in> set ps. set (steps p)))
          \<and> frege_proof.thesis (foldr combine_proofs ps base)
              = frege_proof.thesis base
          \<and> steps (foldr combine_proofs ps base)
              = concat (map steps ps) @ steps base)"
proof (induction ps)
  case Nil
  show ?case by simp
next
  case (Cons p ps)
  show ?case
  proof (intro impI)
    assume vbase: "valid_proof F base"
    assume hyps: "\<forall>q \<in> set (p # ps). valid_proof F q"
    have fs: "frege_system F" by (meson frege_balancing_axioms frege_balancing_def)
    have vp: "valid_proof F p" using hyps by simp
    have vps: "\<forall>q \<in> set ps. valid_proof F q" using hyps by simp
    have cp_th: "\<And>X. frege_proof.thesis (combine_proofs p X) = frege_proof.thesis X"
      by simp
    have cp_st: "\<And>X. steps (combine_proofs p X) = steps p @ steps X" by simp
    have cp_as: "\<And>X. assumptions (combine_proofs p X)
                       = assumptions p \<union> (assumptions X - set (steps p))" by simp
    have inner: "valid_proof F (foldr combine_proofs ps base)
          \<and> assumptions (foldr combine_proofs ps base)
              \<subseteq> (\<Union>q \<in> set ps. assumptions q)
                \<union> (assumptions base - (\<Union>q \<in> set ps. set (steps q)))
          \<and> frege_proof.thesis (foldr combine_proofs ps base)
              = frege_proof.thesis base
          \<and> steps (foldr combine_proofs ps base) = concat (map steps ps) @ steps base"
      using Cons.IH vbase vps by blast
    have vin: "valid_proof F (foldr combine_proofs ps base)" using inner by blast
    have fcons: "foldr combine_proofs (p # ps) base
                 = combine_proofs p (foldr combine_proofs ps base)"
      by (simp del: combine_proofs.simps)
    show "valid_proof F (foldr combine_proofs (p # ps) base)
          \<and> assumptions (foldr combine_proofs (p # ps) base)
              \<subseteq> (\<Union>q \<in> set (p # ps). assumptions q)
                \<union> (assumptions base - (\<Union>q \<in> set (p # ps). set (steps q)))
          \<and> frege_proof.thesis (foldr combine_proofs (p # ps) base)
              = frege_proof.thesis base
          \<and> steps (foldr combine_proofs (p # ps) base)
              = concat (map steps (p # ps)) @ steps base"
      unfolding fcons
    proof (intro conjI)
      show "valid_proof F (combine_proofs p (foldr combine_proofs ps base))"
        using frege_system.combining_valid_proofs[OF fs] vp vin by blast
    next
      have e2: "assumptions (foldr combine_proofs ps base)
              \<subseteq> (\<Union>q \<in> set ps. assumptions q)
                \<union> (assumptions base - (\<Union>q \<in> set ps. set (steps q)))"
        using inner by blast
      show "assumptions (combine_proofs p (foldr combine_proofs ps base))
              \<subseteq> (\<Union>q \<in> set (p # ps). assumptions q)
                \<union> (assumptions base - (\<Union>q \<in> set (p # ps). set (steps q)))"
        unfolding cp_as using e2 by auto
    next
      show "frege_proof.thesis (combine_proofs p (foldr combine_proofs ps base))
            = frege_proof.thesis base"
        using cp_th inner by (simp del: combine_proofs.simps)
    next
      show "steps (combine_proofs p (foldr combine_proofs ps base))
            = concat (map steps (p # ps)) @ steps base"
        using cp_st inner by (simp del: combine_proofs.simps)
    qed
  qed
qed

subsection \<open>The instantiated rule step\<close>

(*
  Applying a rule of F under a substitution as a single derivation step: the
  instantiated premises are assumptions, the instantiated conclusion follows
  by the rule itself.
*)
lemma rule_step_proof:
  assumes rin: "r \<in> rules F"
  shows "\<exists>pr. valid_proof F pr
            \<and> assumptions pr = set (map (sub_formula sb) (prems r))
            \<and> frege_proof.thesis pr = sub_formula sb (concl r)
            \<and> steps pr = map (sub_formula sb) (prems r) @ [sub_formula sb (concl r)]"
proof -
  define Bs where "Bs = map (sub_formula sb) (prems r)"
  define CB where "CB = sub_formula sb (concl r)"
  define pr where "pr = \<lparr>assumptions = set Bs, thesis = CB, steps = Bs @ [CB]\<rparr>"
  have stps: "steps pr = Bs @ [CB]" unfolding pr_def by simp
  have der: "derived (rules F) Bs CB"
  proof -
    have c: "concl (sub_rule sb r) = CB" unfolding CB_def by simp
    have p: "\<forall>f1 \<in> set (prems (sub_rule sb r)). \<exists>f2 \<in> set Bs. f1 = f2"
      unfolding Bs_def by simp
    have "let sub_r = sub_rule sb r in
            concl sub_r = CB \<and> (\<forall>f1 \<in> set (prems sub_r). \<exists>f2 \<in> set Bs. f1 = f2)"
      unfolding Let_def using c p by blast
    thus ?thesis unfolding derived_def using rin by blast
  qed
  have v1: "frege_proof.thesis pr = last (steps pr)" unfolding pr_def by simp
  have v2: "steps pr \<noteq> []" unfolding pr_def by simp
  have v3: "\<And>i. i < length (steps pr) \<Longrightarrow>
              steps pr ! i \<in> assumptions pr
              \<or> derived (rules F) (take i (steps pr)) (steps pr ! i)"
  proof -
    fix i assume ilt: "i < length (steps pr)"
    have ilen: "i < length Bs + 1" using ilt stps by simp
    show "steps pr ! i \<in> assumptions pr
          \<or> derived (rules F) (take i (steps pr)) (steps pr ! i)"
    proof (cases "i < length Bs")
      case True
      have "steps pr ! i = Bs ! i" using stps True by (simp add: nth_append)
      hence "steps pr ! i \<in> set Bs" using True nth_mem by simp
      thus ?thesis unfolding pr_def by simp
    next
      case False
      hence ieq: "i = length Bs" using ilen by simp
      have "steps pr ! i = CB" using stps ieq by simp
      moreover have "take i (steps pr) = Bs" using stps ieq by simp
      ultimately show ?thesis using der by simp
    qed
  qed
  have val: "valid_proof F pr"
    unfolding valid_proof_def using v1 v2 v3 by blast
  have a: "assumptions pr = set (map (sub_formula sb) (prems r))"
    unfolding pr_def Bs_def by simp
  have t: "frege_proof.thesis pr = sub_formula sb (concl r)"
    unfolding pr_def CB_def by simp
  have s: "steps pr = map (sub_formula sb) (prems r) @ [sub_formula sb (concl r)]"
    unfolding pr_def Bs_def CB_def by simp
  show ?thesis using val a t s by blast
qed

subsection \<open>Auxiliary bounds\<close>

lemma length_le_sum_list_len:
  "length xs \<le> sum_list (map len_formula xs)"
proof (induction xs)
  case Nil
  show ?case by simp
next
  case (Cons x xs)
  thus ?case using len_formula_positive[of x] by simp
qed

lemma var_set_rule_finite: "finite (var_set_rule r)"
  by (simp add: var_set_form_finite)

lemma member_len_le_sum:
  assumes "finite vs" and "v \<in> vs"
  shows "len_formula (sub v) \<le> (\<Sum> w \<in> vs. len_formula (sub w))"
proof -
  have "(\<Sum> w \<in> vs. len_formula (sub w))
        = len_formula (sub v) + (\<Sum> w \<in> vs - {v}. len_formula (sub w))"
    using sum.remove[OF assms] .
  thus ?thesis by simp
qed

lemma log_two_square_le:
  "log 2 (real (M * M) + 1) \<le> 2 * log 2 (real (M::nat) + 1)"
proof -
  have le: "real (M * M) + 1 \<le> (real M + 1) ^ 2"
    by (simp add: power2_eq_square algebra_simps)
  have pos: "(0::real) < real (M * M) + 1"
    by (intro add_nonneg_pos) simp_all
  have "log 2 (real (M * M) + 1) \<le> log 2 ((real M + 1) ^ 2)"
    using le pos by (intro log_mono) auto
  also have "\<dots> = 2 * log 2 (real M + 1)"
    by (simp add: log_nat_power)
  finally show ?thesis .
qed

lemma rebal_tb_ge_one:
  assumes "1 \<le> (N::nat)"
  shows "1 \<le> poly rebal_tb N"
proof -
  have wfa: "formula_well_formed (alphabet F) (Atom ''a'')" by simp
  have "1 \<le> len_formula (spira_trans (Atom ''a''))"
    by (rule len_formula_positive)
  also have "len_formula (spira_trans (Atom ''a'')) \<le> poly rebal_tb 1"
    using rebal_tb_spec[OF wfa] by simp
  also have "poly rebal_tb 1 \<le> poly rebal_tb N"
    using assms by (rule poly_nat_mono)
  finally show ?thesis .
qed

subsection \<open>Lemma 7.1: simulating one rule application on balanced translations\<close>

(*
  Filmus' Lemma 7.1. A rule P_1(xs), ..., P_k(xs) / Q(xs) of F, instantiated
  by a substitution sub (Filmus' formulas R_1, ..., R_n for the variables xs),
  lifts to the balanced translations: from the premise translations
  t(P_j(R_1,...,R_n)) the system derives t(Q(R_1,...,R_n)) with at most
  poly bnd M lines, each of length at most poly bnd M and of depth at most
  c * log 2 (M + 1), where M = sum_j |P_j| + |Q| + sum_i |R_i| and bnd, c are
  uniform over all rules of F and all substitutions.
*)
lemma transform_rule_simulation:
  shows "\<exists> (bnd :: nat poly) (c :: real).
           \<forall> r sub. r \<in> rules F
                    \<and> (\<forall> p \<in> set (prems r). formula_well_formed (alphabet F) p)
                    \<and> formula_well_formed (alphabet F) (concl r)
                    \<and> (\<forall> f' \<in> range sub. formula_well_formed (alphabet F) f') \<longrightarrow>
             (let M = sum_list (map len_formula (prems r)) + len_formula (concl r)
                      + (\<Sum> v \<in> var_set_rule r. len_formula (sub v))
              in (\<exists> lines sz dep.
                    derives_balanced
                      ((\<lambda> p. spira_trans (sub_formula sub p)) ` set (prems r))
                      (spira_trans (sub_formula sub (concl r))) lines sz dep
                  \<and> lines \<le> poly bnd M
                  \<and> sz \<le> poly bnd M
                  \<and> real dep \<le> c * log 2 (real M + 1)))"
proof -
  have fs_F: "frege_system F"
    by (meson frege_balancing_axioms frege_balancing_def)
  obtain bnd64 c64 where TCF:
    "\<forall> f sub. formula_well_formed (alphabet F) f
              \<and> (\<forall>f' \<in> range sub. formula_well_formed (alphabet F) f') \<longrightarrow>
       (let M = len_formula f + (\<Sum> v \<in> var_set_form f. len_formula (sub v))
        in (\<exists> lines sz dep.
              provable_balanced_iff (spira_trans (sub_formula sub f))
                (sub_formula (\<lambda> v. spira_trans (sub v)) f) lines sz dep
            \<and> lines \<le> poly bnd64 M
            \<and> sz \<le> poly bnd64 M
            \<and> real dep \<le> real (depth_formula f) + c64 * log 2 (real M + 1)))"
    using transform_commutes_form by blast
  obtain tc :: real where tcf:
    "\<forall>f. formula_well_formed (alphabet F) f \<longrightarrow>
       real (depth_formula (spira_trans f)) \<le> tc * log 2 (real (len_formula f) + 1)"
    using trans_c by blast
  obtain tcm :: real where tcm1: "1 \<le> tcm" and dstr:
    "\<forall>g sub. (\<forall>v. formula_well_formed (alphabet F) (sub v)) \<longrightarrow>
       real (depth_formula (sub_formula (\<lambda>v. spira_trans (sub v)) g))
       \<le> real (depth_formula g)
          + tcm * log 2 (real (len_formula g
                          + (\<Sum>w\<in>var_set_form g. len_formula (sub w))) + 1)"
    using depth_strans_le by blast
  have finrules: "finite (rules F)" using frege_system.finite[OF fs_F] .

  \<comment> \<open>The uniform depth budget for rule formulas, a constant by finiteness.\<close>
  define DR :: nat where
    "DR = Max (insert 1
            ((\<lambda>r. max (Max (insert 1 (depth_formula ` set (prems r))))
                      (depth_formula (concl r))) ` rules F))"
  have DRfin: "finite (insert 1
            ((\<lambda>r. max (Max (insert 1 (depth_formula ` set (prems r))))
                      (depth_formula (concl r))) ` rules F))"
    using finrules by simp
  have DRentry: "\<And>r. r \<in> rules F \<Longrightarrow>
        max (Max (insert 1 (depth_formula ` set (prems r))))
            (depth_formula (concl r)) \<le> DR"
  proof -
    fix r assume "r \<in> rules F"
    hence "max (Max (insert 1 (depth_formula ` set (prems r))))
               (depth_formula (concl r))
           \<in> insert 1
               ((\<lambda>r. max (Max (insert 1 (depth_formula ` set (prems r))))
                         (depth_formula (concl r))) ` rules F)"
      by blast
    thus "max (Max (insert 1 (depth_formula ` set (prems r))))
              (depth_formula (concl r)) \<le> DR"
      unfolding DR_def using Max_ge[OF DRfin] by blast
  qed
  have dprem: "\<And>r p. r \<in> rules F \<Longrightarrow> p \<in> set (prems r) \<Longrightarrow> depth_formula p \<le> DR"
  proof -
    fix r p assume rin: "r \<in> rules F" and pin: "p \<in> set (prems r)"
    have "depth_formula p \<le> Max (insert 1 (depth_formula ` set (prems r)))"
      using pin by (intro Max_ge) auto
    also have "\<dots> \<le> max (Max (insert 1 (depth_formula ` set (prems r))))
                        (depth_formula (concl r))" by simp
    also have "\<dots> \<le> DR" using DRentry[OF rin] .
    finally show "depth_formula p \<le> DR" .
  qed
  have dconcl: "\<And>r. r \<in> rules F \<Longrightarrow> depth_formula (concl r) \<le> DR"
  proof -
    fix r assume rin: "r \<in> rules F"
    have "depth_formula (concl r)
          \<le> max (Max (insert 1 (depth_formula ` set (prems r))))
                (depth_formula (concl r))" by simp
    also have "\<dots> \<le> DR" using DRentry[OF rin] .
    finally show "depth_formula (concl r) \<le> DR" .
  qed

  \<comment> \<open>The uniform constants and the polynomial envelope.\<close>
  define CC :: real where
    "CC = \<bar>c64\<bar> + 2 * max tc 1 + tcm
          + real mp_step_depth + real sym_step_depth + 1"
  define cF :: real where "cF = real DR + CC"
  define KK :: nat where "KK = mp_step_len + sym_step_len + 1"
  define BNDF :: "nat poly" where
    "BNDF = monom 1 1 * bnd64 + bnd64
          + Polynomial.smult KK (pcompose rebal_tb (monom 1 2))
          + Polynomial.smult KK (monom 1 1 * rebal_tb)
          + Polynomial.smult (mp_lines + 1) (monom 1 1)
          + [: sym_lines + mp_lines + 1 :]"
  have KKmp: "mp_step_len \<le> KK" unfolding KK_def by linarith
  have KKsym: "sym_step_len \<le> KK" unfolding KK_def by linarith
  have KK1: "1 \<le> KK" unfolding KK_def by linarith
  have mt1: "(1::real) \<le> max tc 1" by simp
  have mt0: "(0::real) \<le> max tc 1" by simp
  have tcm0: "(0::real) \<le> tcm" using tcm1 by linarith
  have c640: "(0::real) \<le> \<bar>c64\<bar>" by simp
  have mpsd0: "(0::real) \<le> real mp_step_depth" by simp
  have symsd0: "(0::real) \<le> real sym_step_depth" by simp
  have DR0r: "(0::real) \<le> real DR" by simp
  have CCc64: "\<bar>c64\<bar> \<le> CC"
    unfolding CC_def using mt0 tcm0 mpsd0 symsd0 by linarith
  have CCtcm: "tcm \<le> CC"
    unfolding CC_def using c640 mt0 mpsd0 symsd0 by linarith
  have CCmp: "2 * max tc 1 + tcm + real mp_step_depth \<le> CC"
    unfolding CC_def using c640 symsd0 by linarith
  have CCsym: "2 * max tc 1 + tcm + real sym_step_depth \<le> CC"
    unfolding CC_def using c640 mpsd0 by linarith
  have CC0: "(0::real) \<le> CC"
    unfolding CC_def using c640 mt0 tcm0 mpsd0 symsd0 by linarith
  have BNDFval: "\<And>N. poly BNDF N
      = N * poly bnd64 N + poly bnd64 N
        + KK * poly rebal_tb (N * N) + KK * (N * poly rebal_tb N)
        + (N * mp_lines + N) + (sym_lines + mp_lines + 1)"
    unfolding BNDF_def
    by (simp add: poly_monom poly_pcompose power2_eq_square algebra_simps)

  show ?thesis
  proof (intro exI[where x = BNDF] exI[where x = cF] allI impI)
    fix r :: "'a rule" and sub :: "string \<Rightarrow> 'a formula"
    assume H: "r \<in> rules F
               \<and> (\<forall> p \<in> set (prems r). formula_well_formed (alphabet F) p)
               \<and> formula_well_formed (alphabet F) (concl r)
               \<and> (\<forall> f' \<in> range sub. formula_well_formed (alphabet F) f')"
    have rin: "r \<in> rules F" using H by blast
    have wfprems: "\<forall>p \<in> set (prems r). formula_well_formed (alphabet F) p"
      using H by blast
    have wfconcl: "formula_well_formed (alphabet F) (concl r)" using H by blast
    have wfrange: "\<forall>f' \<in> range sub. formula_well_formed (alphabet F) f'"
      using H by blast
    have wfsubv: "\<And>v. formula_well_formed (alphabet F) (sub v)"
      using wfrange by blast

    define M where "M = sum_list (map len_formula (prems r)) + len_formula (concl r)
              + (\<Sum> v \<in> var_set_rule r. len_formula (sub v))"
    let ?LG = "log 2 (real M + 1)"
    let ?RD = "real DR + CC * ?LG"
    let ?PB = "poly bnd64 M"
    let ?RT1 = "poly rebal_tb M"
    let ?RT2 = "poly rebal_tb (M * M)"
    let ?LL = "?RT2 + M * ?RT1"
    let ?SZB = "?PB + KK * ?LL"
    let ?AA = "\<lambda> p. spira_trans (sub_formula sub p)"
    let ?BB = "\<lambda> p. sub_formula (\<lambda>v. spira_trans (sub v)) p"
    let ?RFs = "insert (concl r) (set (prems r))"

    have M1: "1 \<le> M"
      unfolding M_def using len_formula_positive[of "concl r"] by linarith
    have LG1: "1 \<le> ?LG" using M1 by (simp add: le_log_iff)
    have LG0: "(0::real) \<le> ?LG" using LG1 by linarith

    \<comment> \<open>Uniform facts about the rule formulas.\<close>
    have rfwf: "\<And>q. q \<in> ?RFs \<Longrightarrow> formula_well_formed (alphabet F) q"
      using wfprems wfconcl by blast
    have rfvars: "\<And>q. q \<in> ?RFs \<Longrightarrow> var_set_form q \<subseteq> var_set_rule r"
      by auto
    have rfM: "\<And>q. q \<in> ?RFs \<Longrightarrow>
        len_formula q + (\<Sum>v\<in>var_set_form q. len_formula (sub v)) \<le> M"
    proof -
      fix q assume qin: "q \<in> ?RFs"
      have lq: "len_formula q
                \<le> sum_list (map len_formula (prems r)) + len_formula (concl r)"
      proof (cases "q = concl r")
        case True
        thus ?thesis by simp
      next
        case False
        hence "q \<in> set (prems r)" using qin by simp
        hence "len_formula q \<in> set (map len_formula (prems r))" by simp
        hence "len_formula q \<le> sum_list (map len_formula (prems r))"
          by (rule member_le_sum_list) simp
        thus ?thesis by linarith
      qed
      have sq: "(\<Sum>v\<in>var_set_form q. len_formula (sub v))
                \<le> (\<Sum>v\<in>var_set_rule r. len_formula (sub v))"
        by (rule sum_mono2[OF var_set_rule_finite rfvars[OF qin]]) simp
      show "len_formula q + (\<Sum>v\<in>var_set_form q. len_formula (sub v)) \<le> M"
        unfolding M_def using lq sq by linarith
    qed
    have rflen: "\<And>q. q \<in> ?RFs \<Longrightarrow> len_formula q \<le> M"
    proof -
      fix q assume qin: "q \<in> ?RFs"
      show "len_formula q \<le> M" using rfM[OF qin] by linarith
    qed
    have rfdep: "\<And>q. q \<in> ?RFs \<Longrightarrow> depth_formula q \<le> DR"
      using dprem[OF rin] dconcl[OF rin] by blast
    have subvM: "\<And>v. v \<in> var_set_rule r \<Longrightarrow> len_formula (sub v) \<le> M"
    proof -
      fix v assume vin: "v \<in> var_set_rule r"
      have "len_formula (sub v) \<le> (\<Sum>w\<in>var_set_rule r. len_formula (sub w))"
        by (rule member_len_le_sum[OF var_set_rule_finite vin])
      thus "len_formula (sub v) \<le> M" unfolding M_def by linarith
    qed

    \<comment> \<open>Sizes and depths of the two translated instances of each rule formula.\<close>
    have wfsubq: "\<And>q. q \<in> ?RFs \<Longrightarrow>
        formula_well_formed (alphabet F) (sub_formula sub q)"
    proof -
      fix q assume qin: "q \<in> ?RFs"
      show "formula_well_formed (alphabet F) (sub_formula sub q)"
        by (rule sub_formula_wf[OF rfwf[OF qin] wfsubv])
    qed
    have lsubq: "\<And>q. q \<in> ?RFs \<Longrightarrow> len_formula (sub_formula sub q) \<le> M * M"
    proof -
      fix q assume qin: "q \<in> ?RFs"
      have "len_formula (sub_formula sub q)
            \<le> len_formula q
              * (len_formula q + (\<Sum>v\<in>var_set_form q. len_formula (sub v)))"
        by (rule len_sub_form_le)
      also have "\<dots> \<le> M * M"
        by (rule mult_le_mono[OF rflen[OF qin] rfM[OF qin]])
      finally show "len_formula (sub_formula sub q) \<le> M * M" .
    qed
    have AAlen: "\<And>q. q \<in> ?RFs \<Longrightarrow> len_formula (?AA q) \<le> ?RT2"
    proof -
      fix q assume qin: "q \<in> ?RFs"
      show "len_formula (?AA q) \<le> ?RT2"
        by (rule spira_trans_len_le_tb[OF wfsubq[OF qin] lsubq[OF qin]])
    qed
    have BBlen: "\<And>q. q \<in> ?RFs \<Longrightarrow> len_formula (?BB q) \<le> M * ?RT1"
    proof -
      fix q assume qin: "q \<in> ?RFs"
      have cap: "\<And>v. v \<in> var_set_form q \<Longrightarrow>
          len_formula (spira_trans (sub v)) \<le> ?RT1"
      proof -
        fix v assume vq: "v \<in> var_set_form q"
        have vr: "v \<in> var_set_rule r" using vq rfvars[OF qin] by blast
        show "len_formula (spira_trans (sub v)) \<le> ?RT1"
          by (rule spira_trans_len_le_tb[OF wfsubv subvM[OF vr]])
      qed
      have "len_formula (?BB q) \<le> ?RT1 * len_formula q"
        by (rule len_strans_cap[OF cap rebal_tb_ge_one[OF M1]])
      also have "\<dots> \<le> ?RT1 * M" using rflen[OF qin] by (rule mult_le_mono2)
      also have "\<dots> = M * ?RT1" by (simp add: mult.commute)
      finally show "len_formula (?BB q) \<le> M * ?RT1" .
    qed
    have AAdep: "\<And>q. q \<in> ?RFs \<Longrightarrow>
        real (depth_formula (?AA q)) \<le> 2 * max tc 1 * ?LG"
    proof -
      fix q assume qin: "q \<in> ?RFs"
      have "real (depth_formula (?AA q))
            \<le> max tc 1 * log 2 (real (M * M) + 1)"
        by (rule spira_trans_dep_le[OF tcf wfsubq[OF qin] lsubq[OF qin]])
      also have "\<dots> \<le> max tc 1 * (2 * ?LG)"
        by (rule mult_left_mono[OF log_two_square_le mt0])
      also have "\<dots> = 2 * max tc 1 * ?LG" by (simp add: algebra_simps)
      finally show "real (depth_formula (?AA q)) \<le> 2 * max tc 1 * ?LG" .
    qed
    have logMq: "\<And>q. q \<in> ?RFs \<Longrightarrow>
        log 2 (real (len_formula q
                 + (\<Sum>w\<in>var_set_form q. len_formula (sub w))) + 1) \<le> ?LG"
    proof -
      fix q assume qin: "q \<in> ?RFs"
      have pos: "(0::real) < real (len_formula q
                   + (\<Sum>w\<in>var_set_form q. len_formula (sub w))) + 1"
        by (intro add_nonneg_pos) (simp_all del: of_nat_add of_nat_sum)
      have le0: "real (len_formula q
                   + (\<Sum>w\<in>var_set_form q. len_formula (sub w))) \<le> real M"
        using rfM[OF qin] by (simp del: of_nat_add of_nat_sum)
      have le: "real (len_formula q
                  + (\<Sum>w\<in>var_set_form q. len_formula (sub w))) + 1 \<le> real M + 1"
        using le0 by linarith
      show "log 2 (real (len_formula q
                    + (\<Sum>w\<in>var_set_form q. len_formula (sub w))) + 1) \<le> ?LG"
        using le pos by (intro log_mono) auto
    qed
    have BBdep: "\<And>q. q \<in> ?RFs \<Longrightarrow>
        real (depth_formula (?BB q)) \<le> real DR + tcm * ?LG"
    proof -
      fix q assume qin: "q \<in> ?RFs"
      have "real (depth_formula (?BB q))
            \<le> real (depth_formula q)
              + tcm * log 2 (real (len_formula q
                  + (\<Sum>w\<in>var_set_form q. len_formula (sub w))) + 1)"
        using dstr wfsubv by blast
      also have "\<dots> \<le> real DR + tcm * ?LG"
      proof -
        have h1: "real (depth_formula q) \<le> real DR" using rfdep[OF qin] by simp
        have h2: "tcm * log 2 (real (len_formula q
                    + (\<Sum>w\<in>var_set_form q. len_formula (sub w))) + 1) \<le> tcm * ?LG"
          by (rule mult_left_mono[OF logMq[OF qin] tcm0])
        show ?thesis using h1 h2 by linarith
      qed
      finally show "real (depth_formula (?BB q)) \<le> real DR + tcm * ?LG" .
    qed

    \<comment> \<open>Lemma 6.4 at each rule formula, with uniform envelopes.\<close>
    have PBIq: "\<And>q. q \<in> ?RFs \<Longrightarrow>
        \<exists>l s d. provable_balanced_iff (?AA q) (?BB q) l s d
              \<and> l \<le> ?PB \<and> s \<le> ?PB \<and> real d \<le> real DR + \<bar>c64\<bar> * ?LG"
    proof -
      fix q assume qin: "q \<in> ?RFs"
      have "\<exists>l s d. provable_balanced_iff (?AA q) (?BB q) l s d
              \<and> l \<le> poly bnd64 (len_formula q
                      + (\<Sum>v\<in>var_set_form q. len_formula (sub v)))
              \<and> s \<le> poly bnd64 (len_formula q
                      + (\<Sum>v\<in>var_set_form q. len_formula (sub v)))
              \<and> real d \<le> real (depth_formula q)
                  + c64 * log 2 (real (len_formula q
                      + (\<Sum>v\<in>var_set_form q. len_formula (sub v))) + 1)"
        using TCF rfwf[OF qin] wfrange unfolding Let_def by blast
      then obtain l s d where pbi: "provable_balanced_iff (?AA q) (?BB q) l s d"
          and lb: "l \<le> poly bnd64 (len_formula q
                        + (\<Sum>v\<in>var_set_form q. len_formula (sub v)))"
          and sbd: "s \<le> poly bnd64 (len_formula q
                        + (\<Sum>v\<in>var_set_form q. len_formula (sub v)))"
          and db: "real d \<le> real (depth_formula q)
                    + c64 * log 2 (real (len_formula q
                        + (\<Sum>v\<in>var_set_form q. len_formula (sub v))) + 1)"
        by blast
      have pmono: "poly bnd64 (len_formula q
                     + (\<Sum>v\<in>var_set_form q. len_formula (sub v))) \<le> ?PB"
        by (rule poly_nat_mono[OF rfM[OF qin]])
      have lb': "l \<le> ?PB" using lb pmono by linarith
      have sb': "s \<le> ?PB" using sbd pmono by linarith
      have db': "real d \<le> real DR + \<bar>c64\<bar> * ?LG"
      proof -
        have Mq1: "1 \<le> len_formula q + (\<Sum>v\<in>var_set_form q. len_formula (sub v))"
          using len_formula_positive[of q] by linarith
        have lgq0: "(0::real) \<le> log 2 (real (len_formula q
                      + (\<Sum>v\<in>var_set_form q. len_formula (sub v))) + 1)"
        proof -
          have b1: "(1::real) < 2" by simp
          have p1: "(0::real) < real (len_formula q
                       + (\<Sum>v\<in>var_set_form q. len_formula (sub v))) + 1"
            by (simp del: of_nat_add of_nat_sum)
          have g1: "(1::real) \<le> real (len_formula q
                       + (\<Sum>v\<in>var_set_form q. len_formula (sub v))) + 1"
            by (simp del: of_nat_add of_nat_sum)
          from zero_le_log_cancel_iff[OF b1 p1] g1 show ?thesis by blast
        qed
        have c1: "c64 * log 2 (real (len_formula q
                    + (\<Sum>v\<in>var_set_form q. len_formula (sub v))) + 1)
                  \<le> \<bar>c64\<bar> * log 2 (real (len_formula q
                    + (\<Sum>v\<in>var_set_form q. len_formula (sub v))) + 1)"
          by (rule mult_right_mono[OF abs_ge_self lgq0])
        have c2: "\<bar>c64\<bar> * log 2 (real (len_formula q
                    + (\<Sum>v\<in>var_set_form q. len_formula (sub v))) + 1)
                  \<le> \<bar>c64\<bar> * ?LG"
          by (rule mult_left_mono[OF logMq[OF qin] c640])
        have h1: "real (depth_formula q) \<le> real DR" using rfdep[OF qin] by simp
        show ?thesis using db c1 c2 h1 by linarith
      qed
      show "\<exists>l s d. provable_balanced_iff (?AA q) (?BB q) l s d
              \<and> l \<le> ?PB \<and> s \<le> ?PB \<and> real d \<le> real DR + \<bar>c64\<bar> * ?LG"
        using pbi lb' sb' db' by blast
    qed

    \<comment> \<open>Depth absorption: every step-depth bound collapses into ?RD.\<close>
    have ABbnd: "\<And>q. q \<in> ?RFs \<Longrightarrow>
        max (real (depth_formula (?AA q))) (real (depth_formula (?BB q)))
        \<le> real DR + (2 * max tc 1 + tcm) * ?LG"
    proof -
      fix q assume qin: "q \<in> ?RFs"
      have e: "(2 * max tc 1 + tcm) * ?LG = 2 * max tc 1 * ?LG + tcm * ?LG"
        by (simp add: distrib_right)
      have mt0': "(0::real) \<le> 2 * max tc 1" using mt0 by linarith
      have n1: "(0::real) \<le> 2 * max tc 1 * ?LG"
        using mt0' LG0 by (rule mult_nonneg_nonneg)
      have n2: "(0::real) \<le> tcm * ?LG" using tcm0 LG0 by (rule mult_nonneg_nonneg)
      show "max (real (depth_formula (?AA q))) (real (depth_formula (?BB q)))
            \<le> real DR + (2 * max tc 1 + tcm) * ?LG"
      proof (rule max.boundedI)
        show "real (depth_formula (?AA q)) \<le> real DR + (2 * max tc 1 + tcm) * ?LG"
          using AAdep[OF qin] n2 e DR0r by linarith
      next
        show "real (depth_formula (?BB q)) \<le> real DR + (2 * max tc 1 + tcm) * ?LG"
          using BBdep[OF qin] n1 e by linarith
      qed
    qed
    have absorb: "\<And>(s::nat) (dd::real).
        dd \<le> real DR + (2 * max tc 1 + tcm) * ?LG \<Longrightarrow>
        2 * max tc 1 + tcm + real s \<le> CC \<Longrightarrow> real s + dd \<le> ?RD"
    proof -
      fix s :: nat and dd :: real
      assume h1: "dd \<le> real DR + (2 * max tc 1 + tcm) * ?LG"
         and h2: "2 * max tc 1 + tcm + real s \<le> CC"
      have s1: "real s * 1 \<le> real s * ?LG"
        by (rule mult_left_mono[OF LG1]) simp
      hence s1': "real s \<le> real s * ?LG" by simp
      have step2: "real DR + (2 * max tc 1 + tcm) * ?LG + real s * ?LG
                   = real DR + (2 * max tc 1 + tcm + real s) * ?LG"
        by (simp add: distrib_right)
      have step3: "(2 * max tc 1 + tcm + real s) * ?LG \<le> CC * ?LG"
        by (rule mult_right_mono[OF h2 LG0])
      show "real s + dd \<le> ?RD" using h1 s1' step2 step3 by linarith
    qed
    have c64RD: "real DR + \<bar>c64\<bar> * ?LG \<le> ?RD"
    proof -
      have "\<bar>c64\<bar> * ?LG \<le> CC * ?LG" by (rule mult_right_mono[OF CCc64 LG0])
      thus ?thesis by linarith
    qed
    have BBRD: "\<And>q. q \<in> ?RFs \<Longrightarrow> real (depth_formula (?BB q)) \<le> ?RD"
    proof -
      fix q assume qin: "q \<in> ?RFs"
      have "tcm * ?LG \<le> CC * ?LG" by (rule mult_right_mono[OF CCtcm LG0])
      thus "real (depth_formula (?BB q)) \<le> ?RD" using BBdep[OF qin] by linarith
    qed

    \<comment> \<open>The premise converters: t(P_j(R_1..)) entails P_j(t(R_1)..), uniformly bounded.\<close>
    have conv_prem: "\<And>q. q \<in> set (prems r) \<Longrightarrow>
        \<exists>cv. valid_proof F cv \<and> assumptions cv \<subseteq> {?AA q}
           \<and> frege_proof.thesis cv = ?BB q
           \<and> length (steps cv) \<le> ?PB + mp_lines
           \<and> (\<forall>st \<in> set (steps cv). len_formula st \<le> ?SZB)
           \<and> (\<forall>st \<in> set (steps cv). real (depth_formula st) \<le> ?RD)
           \<and> (\<forall>st \<in> set (steps cv). formula_well_formed (alphabet F) st)"
    proof -
      fix q assume qpin: "q \<in> set (prems r)"
      have qin: "q \<in> ?RFs" using qpin by simp
      have wfq: "formula_well_formed (alphabet F) q" using wfprems qpin by blast
      have wf_AAq: "formula_well_formed (alphabet F) (?AA q)"
        by (rule spira_trans_wf[OF sub_formula_well_formed[OF wfq wfsubv]])
      have wf_BBq: "formula_well_formed (alphabet F) (?BB q)"
        by (rule sub_formula_well_formed[OF wfq]) (rule spira_trans_wf[OF wfsubv])
      obtain l s d where pbi: "provable_balanced_iff (?AA q) (?BB q) l s d"
          and lb: "l \<le> ?PB" and sbd: "s \<le> ?PB"
          and db: "real d \<le> real DR + \<bar>c64\<bar> * ?LG"
        using PBIq[OF qin] by blast
      obtain cv where cv:
        "valid_proof F cv" "assumptions cv \<subseteq> {?AA q}"
        "frege_proof.thesis cv = ?BB q"
        "length (steps cv) \<le> l + mp_lines"
        "\<forall>st \<in> set (steps cv). len_formula st
           \<le> max s (mp_step_len * (len_formula (?AA q) + len_formula (?BB q)))"
        "\<forall>st \<in> set (steps cv). depth_formula st
           \<le> max d (mp_step_depth
                + max (depth_formula (?AA q)) (depth_formula (?BB q)))"
        "\<forall>st \<in> set (steps cv). formula_well_formed (alphabet F) st"
        using iff_elimination[OF pbi wf_AAq wf_BBq] by blast
      have l': "length (steps cv) \<le> ?PB + mp_lines" using cv(4) lb by linarith
      have ab: "len_formula (?AA q) + len_formula (?BB q) \<le> ?LL"
        using AAlen[OF qin] BBlen[OF qin] by (rule add_mono)
      have s': "\<forall>st \<in> set (steps cv). len_formula st \<le> ?SZB"
      proof
        fix st assume stin: "st \<in> set (steps cv)"
        have b1: "s \<le> ?SZB" using sbd by linarith
        have b2: "mp_step_len * (len_formula (?AA q) + len_formula (?BB q)) \<le> ?SZB"
        proof -
          have "mp_step_len * (len_formula (?AA q) + len_formula (?BB q)) \<le> KK * ?LL"
            by (rule mult_le_mono[OF KKmp ab])
          thus ?thesis by linarith
        qed
        have "max s (mp_step_len * (len_formula (?AA q) + len_formula (?BB q)))
              \<le> ?SZB" using b1 b2 by (rule max.boundedI)
        thus "len_formula st \<le> ?SZB" using cv(5) stin by (blast intro: le_trans)
      qed
      have d': "\<forall>st \<in> set (steps cv). real (depth_formula st) \<le> ?RD"
      proof
        fix st assume stin: "st \<in> set (steps cv)"
        have h: "depth_formula st
            \<le> max d (mp_step_depth
                 + max (depth_formula (?AA q)) (depth_formula (?BB q)))"
          using cv(6) stin by blast
        have hr: "real (depth_formula st)
            \<le> max (real d) (real mp_step_depth
                 + max (real (depth_formula (?AA q))) (real (depth_formula (?BB q))))"
          using of_nat_mono[OF h] by (simp add: of_nat_max)
        have br1: "real d \<le> ?RD" using db c64RD by linarith
        have br2: "real mp_step_depth
            + max (real (depth_formula (?AA q))) (real (depth_formula (?BB q))) \<le> ?RD"
          by (rule absorb[OF ABbnd[OF qin] CCmp])
        have "max (real d) (real mp_step_depth
                + max (real (depth_formula (?AA q))) (real (depth_formula (?BB q))))
              \<le> ?RD" using br1 br2 by (rule max.boundedI)
        thus "real (depth_formula st) \<le> ?RD" using hr by linarith
      qed
      show "\<exists>cv. valid_proof F cv \<and> assumptions cv \<subseteq> {?AA q}
              \<and> frege_proof.thesis cv = ?BB q
              \<and> length (steps cv) \<le> ?PB + mp_lines
              \<and> (\<forall>st \<in> set (steps cv). len_formula st \<le> ?SZB)
              \<and> (\<forall>st \<in> set (steps cv). real (depth_formula st) \<le> ?RD)
              \<and> (\<forall>st \<in> set (steps cv). formula_well_formed (alphabet F) st)"
        using cv(1,2,3,7) l' s' d' by blast
    qed
    have "\<forall>q. \<exists>cv. q \<in> set (prems r) \<longrightarrow>
        (valid_proof F cv \<and> assumptions cv \<subseteq> {?AA q}
         \<and> frege_proof.thesis cv = ?BB q
         \<and> length (steps cv) \<le> ?PB + mp_lines
         \<and> (\<forall>st \<in> set (steps cv). len_formula st \<le> ?SZB)
         \<and> (\<forall>st \<in> set (steps cv). real (depth_formula st) \<le> ?RD)
         \<and> (\<forall>st \<in> set (steps cv). formula_well_formed (alphabet F) st))"
      using conv_prem by blast
    then have "\<exists>cvf. \<forall>q. q \<in> set (prems r) \<longrightarrow>
        (valid_proof F (cvf q) \<and> assumptions (cvf q) \<subseteq> {?AA q}
         \<and> frege_proof.thesis (cvf q) = ?BB q
         \<and> length (steps (cvf q)) \<le> ?PB + mp_lines
         \<and> (\<forall>st \<in> set (steps (cvf q)). len_formula st \<le> ?SZB)
         \<and> (\<forall>st \<in> set (steps (cvf q)). real (depth_formula st) \<le> ?RD)
         \<and> (\<forall>st \<in> set (steps (cvf q)). formula_well_formed (alphabet F) st))"
      by (rule choice)
    then obtain cvf where cvf: "\<forall>q. q \<in> set (prems r) \<longrightarrow>
        (valid_proof F (cvf q) \<and> assumptions (cvf q) \<subseteq> {?AA q}
         \<and> frege_proof.thesis (cvf q) = ?BB q
         \<and> length (steps (cvf q)) \<le> ?PB + mp_lines
         \<and> (\<forall>st \<in> set (steps (cvf q)). len_formula st \<le> ?SZB)
         \<and> (\<forall>st \<in> set (steps (cvf q)). real (depth_formula st) \<le> ?RD)
         \<and> (\<forall>st \<in> set (steps (cvf q)). formula_well_formed (alphabet F) st))"
      by blast
    have cvf_wf: "\<And>q. q \<in> set (prems r) \<Longrightarrow>
        \<forall>st \<in> set (steps (cvf q)). formula_well_formed (alphabet F) st"
      using cvf by blast
    have cvf_valid: "\<And>q. q \<in> set (prems r) \<Longrightarrow> valid_proof F (cvf q)"
      using cvf by blast
    have cvf_asm: "\<And>q. q \<in> set (prems r) \<Longrightarrow> assumptions (cvf q) \<subseteq> {?AA q}"
      using cvf by blast
    have cvf_th: "\<And>q. q \<in> set (prems r) \<Longrightarrow> frege_proof.thesis (cvf q) = ?BB q"
      using cvf by blast
    have cvf_lines: "\<And>q. q \<in> set (prems r) \<Longrightarrow>
        length (steps (cvf q)) \<le> ?PB + mp_lines"
      using cvf by blast
    have cvf_len: "\<And>q st. q \<in> set (prems r) \<Longrightarrow> st \<in> set (steps (cvf q)) \<Longrightarrow>
        len_formula st \<le> ?SZB"
      using cvf by blast
    have cvf_dep: "\<And>q st. q \<in> set (prems r) \<Longrightarrow> st \<in> set (steps (cvf q)) \<Longrightarrow>
        real (depth_formula st) \<le> ?RD"
      using cvf by blast

    \<comment> \<open>The rule application on the translated arguments.\<close>
    obtain prule where prule:
      "valid_proof F prule"
      "assumptions prule = set (map (sub_formula (\<lambda>v. spira_trans (sub v))) (prems r))"
      "frege_proof.thesis prule = sub_formula (\<lambda>v. spira_trans (sub v)) (concl r)"
      "steps prule = map (sub_formula (\<lambda>v. spira_trans (sub v))) (prems r)
                     @ [sub_formula (\<lambda>v. spira_trans (sub v)) (concl r)]"
      using rule_step_proof[OF rin] by blast

    \<comment> \<open>The conclusion converter: Q(t(R_1)..) entails t(Q(R_1..)).\<close>
    have cin: "concl r \<in> ?RFs" by simp
    obtain lQ sQ dQ where pbiQ:
        "provable_balanced_iff (?AA (concl r)) (?BB (concl r)) lQ sQ dQ"
        and lQb: "lQ \<le> ?PB" and sQb: "sQ \<le> ?PB"
        and dQb: "real dQ \<le> real DR + \<bar>c64\<bar> * ?LG"
      using PBIq[OF cin] by blast
    have wf_AA_concl: "formula_well_formed (alphabet F) (?AA (concl r))"
      by (rule spira_trans_wf[OF sub_formula_well_formed[OF wfconcl wfsubv]])
    have wf_BB_concl: "formula_well_formed (alphabet F) (?BB (concl r))"
      by (rule sub_formula_well_formed[OF wfconcl]) (rule spira_trans_wf[OF wfsubv])
    have pbiQ': "provable_balanced_iff (?BB (concl r)) (?AA (concl r))
        (lQ + sym_lines)
        (sQ + sym_step_len
           * (len_formula (?AA (concl r)) + len_formula (?BB (concl r))))
        (max dQ (sym_step_depth
           + max (depth_formula (?AA (concl r))) (depth_formula (?BB (concl r)))))"
      by (rule iff_sym[OF pbiQ wf_AA_concl wf_BB_concl])
    obtain cvQ where cvQ:
      "valid_proof F cvQ" "assumptions cvQ \<subseteq> {?BB (concl r)}"
      "frege_proof.thesis cvQ = ?AA (concl r)"
      "length (steps cvQ) \<le> (lQ + sym_lines) + mp_lines"
      "\<forall>st \<in> set (steps cvQ). len_formula st
         \<le> max (sQ + sym_step_len
              * (len_formula (?AA (concl r)) + len_formula (?BB (concl r))))
            (mp_step_len
              * (len_formula (?BB (concl r)) + len_formula (?AA (concl r))))"
      "\<forall>st \<in> set (steps cvQ). depth_formula st
         \<le> max (max dQ (sym_step_depth
              + max (depth_formula (?AA (concl r))) (depth_formula (?BB (concl r)))))
            (mp_step_depth
              + max (depth_formula (?BB (concl r))) (depth_formula (?AA (concl r))))"
      "\<forall>st \<in> set (steps cvQ). formula_well_formed (alphabet F) st"
      using iff_elimination[OF pbiQ' wf_BB_concl wf_AA_concl] by blast
    have cvQlines: "length (steps cvQ) \<le> ?PB + sym_lines + mp_lines"
      using cvQ(4) lQb by linarith
    have abQ: "len_formula (?AA (concl r)) + len_formula (?BB (concl r)) \<le> ?LL"
      using AAlen[OF cin] BBlen[OF cin] by (rule add_mono)
    have abQ': "len_formula (?BB (concl r)) + len_formula (?AA (concl r)) \<le> ?LL"
      using abQ by linarith
    have cvQlen: "\<forall>st \<in> set (steps cvQ). len_formula st \<le> ?SZB"
    proof
      fix st assume stin: "st \<in> set (steps cvQ)"
      have b1: "sQ + sym_step_len
          * (len_formula (?AA (concl r)) + len_formula (?BB (concl r))) \<le> ?SZB"
        using add_mono[OF sQb mult_le_mono[OF KKsym abQ]] .
      have b2: "mp_step_len
          * (len_formula (?BB (concl r)) + len_formula (?AA (concl r))) \<le> ?SZB"
      proof -
        have "mp_step_len
            * (len_formula (?BB (concl r)) + len_formula (?AA (concl r))) \<le> KK * ?LL"
          by (rule mult_le_mono[OF KKmp abQ'])
        thus ?thesis by linarith
      qed
      have "max (sQ + sym_step_len
              * (len_formula (?AA (concl r)) + len_formula (?BB (concl r))))
            (mp_step_len
              * (len_formula (?BB (concl r)) + len_formula (?AA (concl r)))) \<le> ?SZB"
        using b1 b2 by (rule max.boundedI)
      thus "len_formula st \<le> ?SZB" using cvQ(5) stin by (blast intro: le_trans)
    qed
    have cvQdep: "\<forall>st \<in> set (steps cvQ). real (depth_formula st) \<le> ?RD"
    proof
      fix st assume stin: "st \<in> set (steps cvQ)"
      have h: "depth_formula st
         \<le> max (max dQ (sym_step_depth
              + max (depth_formula (?AA (concl r))) (depth_formula (?BB (concl r)))))
            (mp_step_depth
              + max (depth_formula (?BB (concl r))) (depth_formula (?AA (concl r))))"
        using cvQ(6) stin by blast
      have hr: "real (depth_formula st)
         \<le> max (max (real dQ) (real sym_step_depth
              + max (real (depth_formula (?AA (concl r))))
                    (real (depth_formula (?BB (concl r))))))
            (real mp_step_depth
              + max (real (depth_formula (?BB (concl r))))
                    (real (depth_formula (?AA (concl r)))))"
        using of_nat_mono[OF h] by (simp add: of_nat_max)
      have br1: "real dQ \<le> ?RD" using dQb c64RD by linarith
      have br2: "real sym_step_depth
          + max (real (depth_formula (?AA (concl r))))
                (real (depth_formula (?BB (concl r)))) \<le> ?RD"
        by (rule absorb[OF ABbnd[OF cin] CCsym])
      have comm: "max (real (depth_formula (?BB (concl r))))
                      (real (depth_formula (?AA (concl r))))
                  = max (real (depth_formula (?AA (concl r))))
                        (real (depth_formula (?BB (concl r))))"
        by (rule max.commute)
      have br3: "real mp_step_depth
          + max (real (depth_formula (?BB (concl r))))
                (real (depth_formula (?AA (concl r)))) \<le> ?RD"
        unfolding comm by (rule absorb[OF ABbnd[OF cin] CCmp])
      have "max (max (real dQ) (real sym_step_depth
              + max (real (depth_formula (?AA (concl r))))
                    (real (depth_formula (?BB (concl r))))))
            (real mp_step_depth
              + max (real (depth_formula (?BB (concl r))))
                    (real (depth_formula (?AA (concl r)))))
            \<le> ?RD"
        using max.boundedI[OF br1 br2] br3 by (rule max.boundedI)
      thus "real (depth_formula st) \<le> ?RD" using hr by linarith
    qed

    \<comment> \<open>Assemble: converters, rule step, conclusion converter.\<close>
    define base where "base = combine_proofs prule cvQ"
    have bvalid: "valid_proof F base"
      unfolding base_def
      using frege_system.combining_valid_proofs[OF fs_F] prule(1) cvQ(1) by blast
    have bsteps: "steps base = steps prule @ steps cvQ"
      unfolding base_def by simp
    have bthesis: "frege_proof.thesis base = ?AA (concl r)"
      unfolding base_def using cvQ(3) by simp
    have BBc_in: "?BB (concl r) \<in> set (steps prule)" using prule(4) by simp
    have basm: "assumptions base \<subseteq> ?BB ` set (prems r)"
    proof -
      have "assumptions base
            = assumptions prule \<union> (assumptions cvQ - set (steps prule))"
        unfolding base_def by simp
      also have "\<dots> \<subseteq> set (map (sub_formula (\<lambda>v. spira_trans (sub v))) (prems r))
                      \<union> ({?BB (concl r)} - set (steps prule))"
        using prule(2) cvQ(2) by blast
      also have "\<dots> \<subseteq> ?BB ` set (prems r)" using BBc_in by auto
      finally show ?thesis .
    qed
    define cvs where "cvs = map cvf (prems r)"
    have cvsv: "\<forall>p \<in> set cvs. valid_proof F p"
    proof
      fix p assume "p \<in> set cvs"
      then obtain q where "q \<in> set (prems r)" and "p = cvf q"
        unfolding cvs_def by auto
      thus "valid_proof F p" using cvf_valid by blast
    qed
    define FP where "FP = foldr combine_proofs cvs base"
    have fold: "valid_proof F FP
          \<and> assumptions FP \<subseteq> (\<Union>p \<in> set cvs. assumptions p)
              \<union> (assumptions base - (\<Union>p \<in> set cvs. set (steps p)))
          \<and> frege_proof.thesis FP = frege_proof.thesis base
          \<and> steps FP = concat (map steps cvs) @ steps base"
      unfolding FP_def using combine_fold_asms bvalid cvsv by blast
    have FPvalid: "valid_proof F FP" using fold by blast
    have FPthesis: "frege_proof.thesis FP = ?AA (concl r)"
    proof -
      have "frege_proof.thesis FP = frege_proof.thesis base" using fold by blast
      thus ?thesis using bthesis by simp
    qed
    have FPsteps: "steps FP = concat (map steps cvs) @ steps prule @ steps cvQ"
    proof -
      have "steps FP = concat (map steps cvs) @ steps base" using fold by blast
      thus ?thesis using bsteps by simp
    qed
    have FPasm: "assumptions FP \<subseteq> (\<lambda> p. spira_trans (sub_formula sub p)) ` set (prems r)"
    proof
      fix x assume xin: "x \<in> assumptions FP"
      have un1: "(\<Union>p \<in> set cvs. assumptions p) \<subseteq> ?AA ` set (prems r)"
      proof
        fix y assume "y \<in> (\<Union>p \<in> set cvs. assumptions p)"
        then obtain p where pin: "p \<in> set cvs" and yin: "y \<in> assumptions p" by blast
        obtain q where qin: "q \<in> set (prems r)" and pq: "p = cvf q"
          using pin unfolding cvs_def by auto
        have "y \<in> {?AA q}" using yin pq cvf_asm[OF qin] by blast
        thus "y \<in> ?AA ` set (prems r)" using qin by blast
      qed
      have un2: "assumptions base - (\<Union>p \<in> set cvs. set (steps p)) = {}"
      proof -
        have bbsub: "?BB ` set (prems r) \<subseteq> (\<Union>p \<in> set cvs. set (steps p))"
        proof
          fix y assume "y \<in> ?BB ` set (prems r)"
          then obtain q where qin: "q \<in> set (prems r)" and yq: "y = ?BB q" by blast
          have vq: "valid_proof F (cvf q)" using cvf_valid[OF qin] .
          have ne: "steps (cvf q) \<noteq> []" using vq unfolding valid_proof_def by simp
          have "frege_proof.thesis (cvf q) = last (steps (cvf q))"
            using vq unfolding valid_proof_def by simp
          hence "?BB q = last (steps (cvf q))" using cvf_th[OF qin] by simp
          hence yin: "?BB q \<in> set (steps (cvf q))" using last_in_set[OF ne] by simp
          have "cvf q \<in> set cvs" using qin unfolding cvs_def by simp
          thus "y \<in> (\<Union>p \<in> set cvs. set (steps p))" using yin yq by blast
        qed
        have "assumptions base \<subseteq> (\<Union>p \<in> set cvs. set (steps p))"
          using subset_trans[OF basm bbsub] .
        thus ?thesis by (simp add: Diff_eq_empty_iff)
      qed
      from fold have subFP: "assumptions FP
            \<subseteq> (\<Union>p \<in> set cvs. assumptions p)
              \<union> (assumptions base - (\<Union>p \<in> set cvs. set (steps p)))"
        by blast
      from xin subFP have "x \<in> (\<Union>p \<in> set cvs. assumptions p)
              \<union> (assumptions base - (\<Union>p \<in> set cvs. set (steps p)))"
        by blast
      hence "x \<in> (\<Union>p \<in> set cvs. assumptions p)" using un2 by simp
      thus "x \<in> (\<lambda> p. spira_trans (sub_formula sub p)) ` set (prems r)"
        using un1 by blast
    qed

    \<comment> \<open>Counting lines.\<close>
    have kM: "length (prems r) \<le> M"
      unfolding M_def using length_le_sum_list_len[of "prems r"] by linarith
    have lc: "length cvs = length (prems r)" unfolding cvs_def by simp
    have cvslen: "length (concat (map steps cvs))
                  \<le> length (prems r) * (?PB + mp_lines)"
    proof -
      have "length (concat (map steps cvs))
            = sum_list (map (length \<circ> steps) cvs)"
        by (simp add: length_concat)
      also have "\<dots> \<le> length cvs * (?PB + mp_lines)"
      proof (rule sum_list_map_le)
        show "\<forall>p \<in> set cvs. (length \<circ> steps) p \<le> ?PB + mp_lines"
        proof
          fix p assume "p \<in> set cvs"
          then obtain q where qin: "q \<in> set (prems r)" and pq: "p = cvf q"
            unfolding cvs_def by auto
          show "(length \<circ> steps) p \<le> ?PB + mp_lines"
            using cvf_lines[OF qin] pq by simp
        qed
      qed
      also have "\<dots> = length (prems r) * (?PB + mp_lines)" by (simp add: lc)
      finally show ?thesis .
    qed
    have prlen: "length (steps prule) = length (prems r) + 1"
      using prule(4) by simp
    have FPlines: "length (steps FP) \<le> poly BNDF M"
    proof -
      have "length (steps FP)
            = length (concat (map steps cvs)) + length (steps prule)
              + length (steps cvQ)"
        using FPsteps by simp
      also have "\<dots> \<le> length (prems r) * (?PB + mp_lines)
                      + (length (prems r) + 1) + (?PB + sym_lines + mp_lines)"
        using cvslen prlen cvQlines by linarith
      also have "\<dots> \<le> M * (?PB + mp_lines) + (M + 1) + (?PB + sym_lines + mp_lines)"
      proof -
        have p1: "length (prems r) * (?PB + mp_lines) \<le> M * (?PB + mp_lines)"
          by (rule mult_le_mono1[OF kM])
        show ?thesis using p1 kM by linarith
      qed
      also have "\<dots> \<le> poly BNDF M"
      proof -
        have e: "M * (?PB + mp_lines) = M * ?PB + M * mp_lines"
          by (simp add: distrib_left)
        show ?thesis using BNDFval[of M] e by linarith
      qed
      finally show ?thesis .
    qed

    \<comment> \<open>Bounding step sizes.\<close>
    have szSZB: "?SZB \<le> poly BNDF M"
    proof -
      have e: "KK * ?LL = KK * ?RT2 + KK * (M * ?RT1)"
        by (simp add: distrib_left)
      show ?thesis using BNDFval[of M] e by linarith
    qed
    have MRT1SZB: "M * ?RT1 \<le> ?SZB"
    proof -
      have h0: "1 * ?LL \<le> KK * ?LL" by (rule mult_le_mono1[OF KK1])
      hence "?LL \<le> KK * ?LL" by simp
      thus ?thesis by linarith
    qed
    have prSZ: "\<forall>st \<in> set (steps prule). len_formula st \<le> ?SZB"
    proof
      fix st assume "st \<in> set (steps prule)"
      hence "st \<in> ?BB ` ?RFs" using prule(4) by auto
      then obtain q where qin: "q \<in> ?RFs" and st_eq: "st = ?BB q" by blast
      have "len_formula st \<le> M * ?RT1" using BBlen[OF qin] st_eq by simp
      thus "len_formula st \<le> ?SZB" using MRT1SZB by linarith
    qed
    have FPlen: "\<forall>st \<in> set (steps FP). len_formula st \<le> poly BNDF M"
    proof
      fix st assume "st \<in> set (steps FP)"
      hence "st \<in> set (concat (map steps cvs)) \<or> st \<in> set (steps prule)
             \<or> st \<in> set (steps cvQ)"
        using FPsteps by auto
      hence "len_formula st \<le> ?SZB"
      proof (elim disjE)
        assume "st \<in> set (concat (map steps cvs))"
        then obtain p where pin: "p \<in> set cvs" and stp: "st \<in> set (steps p)" by auto
        obtain q where qin: "q \<in> set (prems r)" and pq: "p = cvf q"
          using pin unfolding cvs_def by auto
        show "len_formula st \<le> ?SZB" using cvf_len[OF qin] stp pq by blast
      next
        assume "st \<in> set (steps prule)"
        thus "len_formula st \<le> ?SZB" using prSZ by blast
      next
        assume "st \<in> set (steps cvQ)"
        thus "len_formula st \<le> ?SZB" using cvQlen by blast
      qed
      thus "len_formula st \<le> poly BNDF M" using szSZB by linarith
    qed

    \<comment> \<open>Bounding step depths.\<close>
    have prDP: "\<forall>st \<in> set (steps prule). real (depth_formula st) \<le> ?RD"
    proof
      fix st assume "st \<in> set (steps prule)"
      hence "st \<in> ?BB ` ?RFs" using prule(4) by auto
      then obtain q where qin: "q \<in> ?RFs" and st_eq: "st = ?BB q" by blast
      show "real (depth_formula st) \<le> ?RD" using BBRD[OF qin] st_eq by simp
    qed
    have FPdep: "\<forall>st \<in> set (steps FP). real (depth_formula st) \<le> ?RD"
    proof
      fix st assume "st \<in> set (steps FP)"
      hence "st \<in> set (concat (map steps cvs)) \<or> st \<in> set (steps prule)
             \<or> st \<in> set (steps cvQ)"
        using FPsteps by auto
      thus "real (depth_formula st) \<le> ?RD"
      proof (elim disjE)
        assume "st \<in> set (concat (map steps cvs))"
        then obtain p where pin: "p \<in> set cvs" and stp: "st \<in> set (steps p)" by auto
        obtain q where qin: "q \<in> set (prems r)" and pq: "p = cvf q"
          using pin unfolding cvs_def by auto
        show "real (depth_formula st) \<le> ?RD" using cvf_dep[OF qin] stp pq by blast
      next
        assume "st \<in> set (steps prule)"
        thus "real (depth_formula st) \<le> ?RD" using prDP by blast
      next
        assume "st \<in> set (steps cvQ)"
        thus "real (depth_formula st) \<le> ?RD" using cvQdep by blast
      qed
    qed

    \<comment> \<open>Pack the depth into a nat witness and finish.\<close>
    have RD0: "0 \<le> ?RD"
      using DR0r mult_nonneg_nonneg[OF CC0 LG0] by linarith
    define DEP where "DEP = nat \<lfloor>?RD\<rfloor>"
    have DEPst: "\<forall>st \<in> set (steps FP). depth_formula st \<le> DEP"
    proof
      fix st assume "st \<in> set (steps FP)"
      hence "real (depth_formula st) \<le> ?RD" using FPdep by blast
      thus "depth_formula st \<le> DEP" unfolding DEP_def by (rule nat_le_floor)
    qed
    have DEPle: "real DEP \<le> cF * ?LG"
    proof -
      have fl0: "0 \<le> \<lfloor>?RD\<rfloor>"
      proof -
        have "\<lfloor>(0::real)\<rfloor> \<le> \<lfloor>?RD\<rfloor>" using RD0 by (rule floor_mono)
        thus ?thesis by simp
      qed
      have "real DEP = real_of_int \<lfloor>?RD\<rfloor>" unfolding DEP_def using fl0 by simp
      also have "\<dots> \<le> ?RD" by (rule of_int_floor_le)
      also have "\<dots> \<le> cF * ?LG"
      proof -
        have "real DR * 1 \<le> real DR * ?LG"
          by (rule mult_left_mono[OF LG1]) simp
        hence h: "real DR \<le> real DR * ?LG" by simp
        have e: "cF * ?LG = real DR * ?LG + CC * ?LG"
          unfolding cF_def by (simp add: distrib_right)
        show ?thesis using h e by linarith
      qed
      finally show ?thesis .
    qed
    have prule_wf: "\<forall>st \<in> set (steps prule). formula_well_formed (alphabet F) st"
    proof
      fix st assume "st \<in> set (steps prule)"
      hence "st \<in> ?BB ` ?RFs" using prule(4) by auto
      then obtain q where qin: "q \<in> ?RFs" and steq: "st = ?BB q" by auto
      have wfq: "formula_well_formed (alphabet F) q"
        using qin wfprems wfconcl by auto
      show "formula_well_formed (alphabet F) st"
        unfolding steq
        by (rule sub_formula_well_formed[OF wfq]) (rule spira_trans_wf[OF wfsubv])
    qed
    have FPwf: "\<forall>st \<in> set (steps FP). formula_well_formed (alphabet F) st"
    proof
      fix st assume "st \<in> set (steps FP)"
      hence "st \<in> set (concat (map steps cvs)) \<or> st \<in> set (steps prule)
             \<or> st \<in> set (steps cvQ)"
        using FPsteps by auto
      thus "formula_well_formed (alphabet F) st"
      proof (elim disjE)
        assume "st \<in> set (concat (map steps cvs))"
        then obtain p where pin: "p \<in> set cvs" and stp: "st \<in> set (steps p)" by auto
        obtain q where qin: "q \<in> set (prems r)" and pq: "p = cvf q"
          using pin unfolding cvs_def by auto
        show ?thesis using cvf_wf[OF qin] stp pq by blast
      next
        assume "st \<in> set (steps prule)" thus ?thesis using prule_wf by blast
      next
        assume "st \<in> set (steps cvQ)" thus ?thesis using cvQ(7) by blast
      qed
    qed
    have db: "derives_balanced ((\<lambda> p. spira_trans (sub_formula sub p)) ` set (prems r))
                (spira_trans (sub_formula sub (concl r)))
                (poly BNDF M) (poly BNDF M) DEP"
      unfolding derives_balanced_def
      using FPvalid FPasm FPthesis FPlines FPlen DEPst FPwf by blast
    have triv: "poly BNDF M \<le> poly BNDF M" by simp
    show "let M = sum_list (map len_formula (prems r)) + len_formula (concl r)
                  + (\<Sum> v \<in> var_set_rule r. len_formula (sub v))
          in (\<exists> lines sz dep.
                derives_balanced
                  ((\<lambda> p. spira_trans (sub_formula sub p)) ` set (prems r))
                  (spira_trans (sub_formula sub (concl r))) lines sz dep
              \<and> lines \<le> poly BNDF M
              \<and> sz \<le> poly BNDF M
              \<and> real dep \<le> cF * log 2 (real M + 1))"
      unfolding Let_def M_def[symmetric] using db triv DEPle by blast
  qed
qed

subsection \<open>Foundational helpers for the final assembly\<close>

(*
  Substitution preserves the connective skeleton: if the substituted formula is
  well-formed, the original (un-substituted) formula has correct arities.
*)
lemma sub_formula_wf_skeleton:
  assumes "formula_well_formed alph (sub_formula sb f)"
  shows "formula_well_formed alph f"
  using assms
proof (induction f)
  case (Atom a)
  show ?case by simp
next
  case (Conn c fs)
  have len_eq: "length fs = arity alph c" using Conn.prems by simp
  have allwf: "\<forall>g' \<in> set (map (sub_formula sb) fs). formula_well_formed alph g'"
    using Conn.prems by simp
  have "\<forall>g \<in> set fs. formula_well_formed alph g"
  proof
    fix g assume gin: "g \<in> set fs"
    have "sub_formula sb g \<in> set (map (sub_formula sb) fs)" using gin by simp
    hence "formula_well_formed alph (sub_formula sb g)" using allwf by blast
    thus "formula_well_formed alph g" using Conn.IH gin by blast
  qed
  thus ?case using len_eq by simp
qed

(*
  Substitution preserves well-formedness of the values it plugs into a formula:
  if sub_formula sb f is well-formed and v occurs in f, then sb v is well-formed.
*)
lemma sub_formula_wf_value:
  assumes "formula_well_formed alph (sub_formula sb f)"
      and "v \<in> var_set_form f"
  shows "formula_well_formed alph (sb v)"
  using assms
proof (induction f)
  case (Atom a)
  have "v = a" using Atom.prems(2) by simp
  thus ?case using Atom.prems(1) by simp
next
  case (Conn c fs)
  have allwf: "\<forall>g' \<in> set (map (sub_formula sb) fs). formula_well_formed alph g'"
    using Conn.prems(1) by simp
  obtain g where gin: "g \<in> set fs" and vg: "v \<in> var_set_form g"
    using Conn.prems(2) by auto
  have "sub_formula sb g \<in> set (map (sub_formula sb) fs)" using gin by simp
  hence "formula_well_formed alph (sub_formula sb g)" using allwf by blast
  thus ?case using Conn.IH gin vg by blast
qed

(*
  A substituted value is no larger than the whole substituted formula whenever
  the variable occurs in the formula.
*)
lemma len_sub_value_le:
  assumes "v \<in> var_set_form f"
  shows "len_formula (sb v) \<le> len_formula (sub_formula sb f)"
  using assms
proof (induction f)
  case (Atom a)
  have "v = a" using Atom.prems by simp
  thus ?case by simp
next
  case (Conn c fs)
  obtain g where gin: "g \<in> set fs" and vg: "v \<in> var_set_form g"
    using Conn.prems by auto
  have step: "len_formula (sb v) \<le> len_formula (sub_formula sb g)"
    using Conn.IH gin vg by blast
  have mem: "len_formula (sub_formula sb g)
             \<in> set (map len_formula (map (sub_formula sb) fs))"
    using gin by auto
  have lt: "len_formula (sub_formula sb g) < len_formula (sub_formula sb (Conn c fs))"
  proof -
    have "len_formula (sub_formula sb g)
          \<le> sum_list (map len_formula (map (sub_formula sb) fs))"
      using mem by (rule member_le_sum_list) simp
    also have "\<dots> < len_formula (sub_formula sb (Conn c fs))" by simp
    finally show ?thesis .
  qed
  show ?case using step lt by linarith
qed

(*
  The set of variables of a formula is no larger than its size.
*)
lemma card_var_set_le_len:
  "card (var_set_form f) \<le> len_formula f"
proof (induction f)
  case (Atom a)
  show ?case by simp
next
  case (Conn c fs)
  have inner: "card (\<Union>g \<in> set gs. var_set_form g)
               \<le> sum_list (map (\<lambda>g. card (var_set_form g)) gs)"
    for gs :: "'c formula list"
  proof (induction gs)
    case Nil
    show ?case by simp
  next
    case (Cons a as)
    have "card (\<Union>g \<in> set (a # as). var_set_form g)
          = card (var_set_form a \<union> (\<Union>g \<in> set as. var_set_form g))" by simp
    also have "\<dots> \<le> card (var_set_form a) + card (\<Union>g \<in> set as. var_set_form g)"
      by (rule card_Un_le)
    also have "\<dots> \<le> card (var_set_form a)
                     + sum_list (map (\<lambda>g. card (var_set_form g)) as)"
      using Cons.IH by simp
    also have "\<dots> = sum_list (map (\<lambda>g. card (var_set_form g)) (a # as))" by simp
    finally show ?case .
  qed
  have "card (var_set_form (Conn c fs)) = card (\<Union>g \<in> set fs. var_set_form g)"
    by simp
  also have "\<dots> \<le> sum_list (map (\<lambda>g. card (var_set_form g)) fs)"
    by (rule inner)
  also have "\<dots> \<le> sum_list (map len_formula fs)"
    using Conn.IH by (auto intro: sum_list_mono)
  also have "\<dots> \<le> len_formula (Conn c fs)" by simp
  finally show ?case .
qed

(*
  The identity substitution leaves a formula unchanged.
*)
lemma sub_formula_atom_id: "sub_formula Atom f = f"
proof (induction f)
  case (Atom a)
  show ?case by simp
next
  case (Conn c fs)
  have pw: "\<forall>g \<in> set fs. sub_formula Atom g = g" using Conn.IH by blast
  have "map (sub_formula Atom) fs = fs" using pw by (induction fs) auto
  thus ?case by simp
qed

(*
  Chained combination. Folding a list of proofs (each first proof's steps
  precede the later ones) discharges every proof's assumptions against the
  steps of the proofs that come earlier in the fold, leaving only the genuinely
  external assumptions "outer". This is the discharge that combine_fold_asms
  does not perform (it only discharges the base's assumptions).
*)
lemma chain_combine:
  assumes vbase: "valid_proof F base"
  shows "(\<forall>p \<in> set ps. valid_proof F p) \<longrightarrow>
         (\<forall>i < length ps. assumptions (ps ! i)
              \<subseteq> outer \<union> (\<Union>q \<in> set (take i ps). set (steps q))) \<longrightarrow>
         assumptions base \<subseteq> outer \<union> (\<Union>q \<in> set ps. set (steps q)) \<longrightarrow>
         (valid_proof F (foldr combine_proofs ps base)
          \<and> assumptions (foldr combine_proofs ps base) \<subseteq> outer
          \<and> frege_proof.thesis (foldr combine_proofs ps base)
              = frege_proof.thesis base
          \<and> steps (foldr combine_proofs ps base)
              = concat (map steps ps) @ steps base)"
proof (induction ps arbitrary: outer)
  case Nil
  show ?case
  proof (intro impI)
    assume "assumptions base \<subseteq> outer \<union> (\<Union>q \<in> set []. set (steps q))"
    hence "assumptions base \<subseteq> outer" by simp
    thus "valid_proof F (foldr combine_proofs [] base)
          \<and> assumptions (foldr combine_proofs [] base) \<subseteq> outer
          \<and> frege_proof.thesis (foldr combine_proofs [] base)
              = frege_proof.thesis base
          \<and> steps (foldr combine_proofs [] base)
              = concat (map steps []) @ steps base"
      using vbase by simp
  qed
next
  case (Cons p ps)
  show ?case
  proof (intro impI)
    assume vps: "\<forall>q \<in> set (p # ps). valid_proof F q"
    assume hps: "\<forall>i < length (p # ps). assumptions ((p # ps) ! i)
                    \<subseteq> outer \<union> (\<Union>q \<in> set (take i (p # ps)). set (steps q))"
    assume hbase: "assumptions base \<subseteq> outer \<union> (\<Union>q \<in> set (p # ps). set (steps q))"
    have fs: "frege_system F" by (meson frege_balancing_axioms frege_balancing_def)
    have vp: "valid_proof F p" using vps by simp
    have vps': "\<forall>q \<in> set ps. valid_proof F q" using vps by simp
    have cp_th: "\<And>X. frege_proof.thesis (combine_proofs p X) = frege_proof.thesis X"
      by simp
    have cp_st: "\<And>X. steps (combine_proofs p X) = steps p @ steps X" by simp
    define outer' where "outer' = outer \<union> set (steps p)"
    have hps': "\<forall>i < length ps. assumptions (ps ! i)
                  \<subseteq> outer' \<union> (\<Union>q \<in> set (take i ps). set (steps q))"
    proof (intro allI impI)
      fix i assume ilt: "i < length ps"
      have "Suc i < length (p # ps)" using ilt by simp
      hence sub: "assumptions ((p # ps) ! Suc i)
              \<subseteq> outer \<union> (\<Union>q \<in> set (take (Suc i) (p # ps)). set (steps q))"
        using hps by blast
      have e1: "(p # ps) ! Suc i = ps ! i" by simp
      have e2: "set (take (Suc i) (p # ps)) = insert p (set (take i ps))" by simp
      show "assumptions (ps ! i)
              \<subseteq> outer' \<union> (\<Union>q \<in> set (take i ps). set (steps q))"
        using sub unfolding e1 e2 outer'_def by auto
    qed
    have hbase': "assumptions base \<subseteq> outer' \<union> (\<Union>q \<in> set ps. set (steps q))"
      using hbase unfolding outer'_def by auto
    have inner: "valid_proof F (foldr combine_proofs ps base)
          \<and> assumptions (foldr combine_proofs ps base) \<subseteq> outer'
          \<and> frege_proof.thesis (foldr combine_proofs ps base)
              = frege_proof.thesis base
          \<and> steps (foldr combine_proofs ps base)
              = concat (map steps ps) @ steps base"
      using Cons.IH[of outer'] vps' hps' hbase' by blast
    have vin: "valid_proof F (foldr combine_proofs ps base)" using inner by blast
    have ain: "assumptions (foldr combine_proofs ps base) \<subseteq> outer'" using inner by blast
    have ap: "assumptions p \<subseteq> outer"
    proof -
      have "0 < length (p # ps)" by simp
      hence "assumptions ((p # ps) ! 0)
              \<subseteq> outer \<union> (\<Union>q \<in> set (take 0 (p # ps)). set (steps q))"
        using hps by blast
      thus ?thesis by simp
    qed
    have fcons: "foldr combine_proofs (p # ps) base
                 = combine_proofs p (foldr combine_proofs ps base)"
      by (simp del: combine_proofs.simps)
    show "valid_proof F (foldr combine_proofs (p # ps) base)
          \<and> assumptions (foldr combine_proofs (p # ps) base) \<subseteq> outer
          \<and> frege_proof.thesis (foldr combine_proofs (p # ps) base)
              = frege_proof.thesis base
          \<and> steps (foldr combine_proofs (p # ps) base)
              = concat (map steps (p # ps)) @ steps base"
      unfolding fcons
    proof (intro conjI)
      show "valid_proof F (combine_proofs p (foldr combine_proofs ps base))"
        using frege_system.combining_valid_proofs[OF fs] vp vin by blast
    next
      have "assumptions (combine_proofs p (foldr combine_proofs ps base))
            = assumptions p \<union> (assumptions (foldr combine_proofs ps base) - set (steps p))"
        by simp
      also have "\<dots> \<subseteq> outer"
      proof -
        have "assumptions (foldr combine_proofs ps base) - set (steps p) \<subseteq> outer"
          using ain unfolding outer'_def by blast
        thus ?thesis using ap by blast
      qed
      finally show "assumptions (combine_proofs p (foldr combine_proofs ps base))
                    \<subseteq> outer" .
    next
      show "frege_proof.thesis (combine_proofs p (foldr combine_proofs ps base))
            = frege_proof.thesis base"
        using cp_th inner by (simp del: combine_proofs.simps)
    next
      show "steps (combine_proofs p (foldr combine_proofs ps base))
            = concat (map steps (p # ps)) @ steps base"
        using cp_st inner by (simp del: combine_proofs.simps)
    qed
  qed
qed

subsection \<open>Per-line simulation: a balanced sub-derivation for each original line\<close>

(*
  For each line L_i of a no-assumption (well-formed) proof, Lemma 7.1 yields a
  balanced sub-derivation of t(L_i) from { t(L_j) : j a premise of the rule
  application, j < i }, hence from { t(L_j) : j < i }.  The size and line bounds
  collapse to a single polynomial in len_proof pr (because the rule data is
  uniformly bounded over the finite rule set), and the depth bound collapses to
  cc * log (len_proof pr + 1).
*)
lemma per_line_simulation:
  shows "\<exists>(bnd :: nat poly) (cc :: real). 0 \<le> cc \<and>
           (\<forall>pr. valid_proof F pr \<and> assumptions pr = {}
                 \<and> (\<forall>s \<in> set (steps pr). formula_well_formed (alphabet F) s) \<longrightarrow>
             (\<forall>i < length (steps pr). \<exists>D.
                  valid_proof F D
                \<and> assumptions D \<subseteq> spira_trans ` set (take i (steps pr))
                \<and> frege_proof.thesis D = spira_trans (steps pr ! i)
                \<and> length (steps D) \<le> poly bnd (len_proof pr)
                \<and> (\<forall>s \<in> set (steps D). len_formula s \<le> poly bnd (len_proof pr))
                \<and> (\<forall>s \<in> set (steps D). real (depth_formula s)
                      \<le> cc * log 2 (real (len_proof pr) + 1))
                \<and> (\<forall>s \<in> set (steps D). formula_well_formed (alphabet F) s)))"
proof -
  have fs_F: "frege_system F" by (meson frege_balancing_axioms frege_balancing_def)
  obtain B71 C71 where T71:
    "\<forall>r sub. r \<in> rules F
             \<and> (\<forall>p \<in> set (prems r). formula_well_formed (alphabet F) p)
             \<and> formula_well_formed (alphabet F) (concl r)
             \<and> (\<forall>f' \<in> range sub. formula_well_formed (alphabet F) f') \<longrightarrow>
        (let M = sum_list (map len_formula (prems r)) + len_formula (concl r)
                 + (\<Sum>v \<in> var_set_rule r. len_formula (sub v))
         in (\<exists>lines sz dep.
               derives_balanced
                 ((\<lambda>p. spira_trans (sub_formula sub p)) ` set (prems r))
                 (spira_trans (sub_formula sub (concl r))) lines sz dep
             \<and> lines \<le> poly B71 M \<and> sz \<le> poly B71 M
             \<and> real dep \<le> C71 * log 2 (real M + 1)))"
    using transform_rule_simulation by blast
  define RuleSz where "RuleSz = Max (insert 1
        ((\<lambda>r. sum_list (map len_formula (prems r)) + len_formula (concl r)) ` rules F))"
  define RuleVars where "RuleVars = Max (insert 1
        ((\<lambda>r. card (var_set_rule r)) ` rules F))"
  define KM where "KM = RuleSz + RuleVars"
  define cc' where "cc' = max C71 0"
  define ccfin where "ccfin = cc' * (log 2 (real KM + 1) + 1)"
  define bndfin where "bndfin = pcompose B71 (Polynomial.smult KM (monom 1 1))"
  have finRuleSz: "finite (insert 1
        ((\<lambda>r. sum_list (map len_formula (prems r)) + len_formula (concl r)) ` rules F))"
    using frege_system.finite[OF fs_F] by simp
  have finRuleVars: "finite (insert 1 ((\<lambda>r. card (var_set_rule r)) ` rules F))"
    using frege_system.finite[OF fs_F] by simp
  have KM1: "1 \<le> KM"
  proof -
    have "(1::nat) \<le> RuleSz" unfolding RuleSz_def by (rule Max_ge[OF finRuleSz, OF insertI1])
    thus ?thesis unfolding KM_def by simp
  qed
  have c'0: "0 \<le> cc'" unfolding cc'_def by simp
  have ccfin0: "0 \<le> ccfin"
  proof -
    have "0 \<le> log 2 (real KM + 1) + 1" by simp
    thus ?thesis unfolding ccfin_def using c'0 by simp
  qed
  have bndfin_eval: "\<And>N. poly bndfin N = poly B71 (KM * N)"
    unfolding bndfin_def by (simp add: poly_pcompose poly_monom)
  show ?thesis
  proof (intro exI[where x = bndfin] exI[where x = ccfin] conjI)
    show "0 \<le> ccfin" using ccfin0 .
  next
    show "\<forall>pr. valid_proof F pr \<and> assumptions pr = {}
                \<and> (\<forall>s \<in> set (steps pr). formula_well_formed (alphabet F) s) \<longrightarrow>
            (\<forall>i < length (steps pr). \<exists>D.
                 valid_proof F D
               \<and> assumptions D \<subseteq> spira_trans ` set (take i (steps pr))
               \<and> frege_proof.thesis D = spira_trans (steps pr ! i)
               \<and> length (steps D) \<le> poly bndfin (len_proof pr)
               \<and> (\<forall>s \<in> set (steps D). len_formula s \<le> poly bndfin (len_proof pr))
               \<and> (\<forall>s \<in> set (steps D). real (depth_formula s)
                     \<le> ccfin * log 2 (real (len_proof pr) + 1))
               \<and> (\<forall>s \<in> set (steps D). formula_well_formed (alphabet F) s))"
    proof (intro allI impI)
      fix pr i
      assume A: "valid_proof F pr \<and> assumptions pr = {}
                        \<and> (\<forall>s \<in> set (steps pr). formula_well_formed (alphabet F) s)"
      assume ilt: "i < length (steps pr)"
      have vpr: "valid_proof F pr" using A by blast
      have noasm: "assumptions pr = {}" using A by blast
      have wfsteps: "\<forall>s \<in> set (steps pr). formula_well_formed (alphabet F) s"
        using A by blast
      have lp1: "1 \<le> len_proof pr" using len_proof_positive[OF vpr] .
      define Li where "Li = steps pr ! i"
    have Li_in: "Li \<in> set (steps pr)" unfolding Li_def using ilt by simp
    have wfLi: "formula_well_formed (alphabet F) Li" using wfsteps Li_in by blast
    have der: "derived (rules F) (take i (steps pr)) Li"
    proof -
      have "steps pr ! i \<in> assumptions pr
            \<or> derived (rules F) (take i (steps pr)) (steps pr ! i)"
        using vpr ilt unfolding valid_proof_def by blast
      thus ?thesis using noasm unfolding Li_def by simp
    qed
    have ex_rsb: "\<exists>r sb. r \<in> rules F \<and> sub_formula sb (concl r) = Li
                    \<and> (\<forall>p \<in> set (prems r). sub_formula sb p \<in> set (take i (steps pr)))"
    proof -
      from der obtain r sb where rin: "r \<in> rules F"
          and ce: "concl (sub_rule sb r) = Li"
          and pe: "\<forall>f1 \<in> set (prems (sub_rule sb r)). \<exists>f2 \<in> set (take i (steps pr)). f1 = f2"
        unfolding derived_def by auto
      have ce': "sub_formula sb (concl r) = Li" using ce by simp
      have pe': "\<forall>p \<in> set (prems r). sub_formula sb p \<in> set (take i (steps pr))"
      proof
        fix p assume pp: "p \<in> set (prems r)"
        hence "sub_formula sb p \<in> set (prems (sub_rule sb r))" by simp
        then obtain f2 where f2in: "f2 \<in> set (take i (steps pr))"
            and "sub_formula sb p = f2" using pe by blast
        thus "sub_formula sb p \<in> set (take i (steps pr))" using f2in by simp
      qed
      show ?thesis using rin ce' pe' by blast
    qed
    obtain r sb where rin: "r \<in> rules F"
        and concl_eq: "sub_formula sb (concl r) = Li"
        and prem_in: "\<forall>p \<in> set (prems r). sub_formula sb p \<in> set (take i (steps pr))"
      using ex_rsb by blast
    have wfsubconcl: "formula_well_formed (alphabet F) (sub_formula sb (concl r))"
      using wfLi concl_eq by simp
    have wfconcl: "formula_well_formed (alphabet F) (concl r)"
      using sub_formula_wf_skeleton[OF wfsubconcl] .
    have wfsubprem: "\<And>p. p \<in> set (prems r) \<Longrightarrow>
        formula_well_formed (alphabet F) (sub_formula sb p)"
    proof -
      fix p assume pp: "p \<in> set (prems r)"
      have "sub_formula sb p \<in> set (take i (steps pr))" using prem_in pp by blast
      hence "sub_formula sb p \<in> set (steps pr)"
        using set_take_subset[of i "steps pr"] by blast
      thus "formula_well_formed (alphabet F) (sub_formula sb p)" using wfsteps by blast
    qed
    have wfprems: "\<forall>p \<in> set (prems r). formula_well_formed (alphabet F) p"
      using sub_formula_wf_skeleton wfsubprem by blast
    have wfsbv: "\<And>v. v \<in> var_set_rule r \<Longrightarrow> formula_well_formed (alphabet F) (sb v)"
    proof -
      fix v assume "v \<in> var_set_rule r"
      hence vr: "v \<in> (\<Union>p \<in> set (prems r). var_set_form p) \<union> var_set_form (concl r)"
        by simp
      thus "formula_well_formed (alphabet F) (sb v)"
      proof
        assume "v \<in> (\<Union>p \<in> set (prems r). var_set_form p)"
        then obtain p where pp: "p \<in> set (prems r)" and vp: "v \<in> var_set_form p" by blast
        show ?thesis using sub_formula_wf_value[OF wfsubprem[OF pp] vp] .
      next
        assume vc: "v \<in> var_set_form (concl r)"
        show ?thesis using sub_formula_wf_value[OF wfsubconcl vc] .
      qed
    qed
    define sigma where "sigma = (\<lambda>v. if v \<in> var_set_rule r then sb v else Atom ''a'')"
    have wfsigma: "\<And>v. formula_well_formed (alphabet F) (sigma v)"
    proof -
      fix v show "formula_well_formed (alphabet F) (sigma v)"
        unfolding sigma_def using wfsbv by (cases "v \<in> var_set_rule r") auto
    qed
    have wfsigma_range: "\<forall>f' \<in> range sigma. formula_well_formed (alphabet F) f'"
      using wfsigma by blast
    have sigma_concl: "sub_formula sigma (concl r) = Li"
    proof -
      have "sub_formula sigma (concl r) = sub_formula sb (concl r)"
      proof (rule sub_formula_agree)
        show "\<forall>v \<in> var_set_form (concl r). sigma v = sb v"
        proof
          fix v assume "v \<in> var_set_form (concl r)"
          hence "v \<in> var_set_rule r" by simp
          thus "sigma v = sb v" unfolding sigma_def by simp
        qed
      qed
      thus ?thesis using concl_eq by simp
    qed
    have sigma_prem: "\<And>p. p \<in> set (prems r) \<Longrightarrow> sub_formula sigma p = sub_formula sb p"
    proof -
      fix p assume pp: "p \<in> set (prems r)"
      show "sub_formula sigma p = sub_formula sb p"
      proof (rule sub_formula_agree)
        show "\<forall>v \<in> var_set_form p. sigma v = sb v"
        proof
          fix v assume "v \<in> var_set_form p"
          hence "v \<in> var_set_rule r" using pp by auto
          thus "sigma v = sb v" unfolding sigma_def by simp
        qed
      qed
    qed
    have preconds: "r \<in> rules F
        \<and> (\<forall>p \<in> set (prems r). formula_well_formed (alphabet F) p)
        \<and> formula_well_formed (alphabet F) (concl r)
        \<and> (\<forall>f' \<in> range sigma. formula_well_formed (alphabet F) f')"
      using rin wfprems wfconcl wfsigma_range by blast
    define Mi where "Mi = sum_list (map len_formula (prems r)) + len_formula (concl r)
                    + (\<Sum>v \<in> var_set_rule r. len_formula (sigma v))"
    have T71i: "\<exists>lines sz dep.
          derives_balanced
            ((\<lambda>p. spira_trans (sub_formula sigma p)) ` set (prems r))
            (spira_trans (sub_formula sigma (concl r))) lines sz dep
          \<and> lines \<le> poly B71 Mi \<and> sz \<le> poly B71 Mi
          \<and> real dep \<le> C71 * log 2 (real Mi + 1)"
      using T71 preconds unfolding Let_def Mi_def by blast
    obtain lines sz dep where
        db: "derives_balanced
              ((\<lambda>p. spira_trans (sub_formula sigma p)) ` set (prems r))
              (spira_trans (sub_formula sigma (concl r))) lines sz dep"
        and lines_b: "lines \<le> poly B71 Mi"
        and sz_b: "sz \<le> poly B71 Mi"
        and dep_b: "real dep \<le> C71 * log 2 (real Mi + 1)"
      using T71i by blast
    \<comment> \<open>The arithmetic envelope: Mi is linearly bounded by len_proof pr.\<close>
    have Mi_le: "Mi \<le> KM * len_proof pr"
    proof -
      have part1: "sum_list (map len_formula (prems r)) + len_formula (concl r) \<le> RuleSz"
      proof -
        have "sum_list (map len_formula (prems r)) + len_formula (concl r)
              \<in> insert 1 ((\<lambda>r. sum_list (map len_formula (prems r))
                              + len_formula (concl r)) ` rules F)"
          using rin by blast
        thus ?thesis unfolding RuleSz_def using Max_ge[OF finRuleSz] by blast
      qed
      have sbv_le: "\<And>v. v \<in> var_set_rule r \<Longrightarrow> len_formula (sb v) \<le> len_proof pr"
      proof -
        fix v assume "v \<in> var_set_rule r"
        hence vr: "v \<in> (\<Union>p \<in> set (prems r). var_set_form p) \<union> var_set_form (concl r)"
          by simp
        show "len_formula (sb v) \<le> len_proof pr"
        proof (cases "v \<in> var_set_form (concl r)")
          case True
          have "len_formula (sb v) \<le> len_formula (sub_formula sb (concl r))"
            using len_sub_value_le[OF True] .
          also have "\<dots> = len_formula Li" using concl_eq by simp
          also have "len_formula Li \<le> len_proof pr"
          proof -
            have "len_formula Li \<in> set (map len_formula (steps pr))" using Li_in by simp
            hence "len_formula Li \<le> sum_list (map len_formula (steps pr))"
              by (rule member_le_sum_list) simp
            thus ?thesis by simp
          qed
          finally show ?thesis .
        next
          case False
          then obtain p where pp: "p \<in> set (prems r)" and vp: "v \<in> var_set_form p"
            using vr by blast
          have "len_formula (sb v) \<le> len_formula (sub_formula sb p)"
            using len_sub_value_le[OF vp] .
          also have "len_formula (sub_formula sb p) \<le> len_proof pr"
          proof -
            have "sub_formula sb p \<in> set (take i (steps pr))" using prem_in pp by blast
            hence "sub_formula sb p \<in> set (steps pr)"
              using set_take_subset[of i "steps pr"] by blast
            hence "len_formula (sub_formula sb p) \<in> set (map len_formula (steps pr))"
              by simp
            hence "len_formula (sub_formula sb p) \<le> sum_list (map len_formula (steps pr))"
              by (rule member_le_sum_list) simp
            thus ?thesis by simp
          qed
          finally show ?thesis .
        qed
      qed
      have sum_le: "(\<Sum>v \<in> var_set_rule r. len_formula (sigma v))
                    \<le> RuleVars * len_proof pr"
      proof -
        have "(\<Sum>v \<in> var_set_rule r. len_formula (sigma v))
              = (\<Sum>v \<in> var_set_rule r. len_formula (sb v))"
        proof (rule sum.cong)
          show "var_set_rule r = var_set_rule r" by simp
          fix v assume "v \<in> var_set_rule r"
          thus "len_formula (sigma v) = len_formula (sb v)" unfolding sigma_def by simp
        qed
        also have "\<dots> \<le> card (var_set_rule r) * len_proof pr"
        proof -
          have "(\<Sum>v \<in> var_set_rule r. len_formula (sb v))
                \<le> of_nat (card (var_set_rule r)) * len_proof pr"
            using sbv_le by (intro sum_bounded_above)
          thus ?thesis by simp
        qed
        also have "\<dots> \<le> RuleVars * len_proof pr"
        proof -
          have "card (var_set_rule r) \<le> RuleVars"
          proof -
            have "card (var_set_rule r) \<in> insert 1 ((\<lambda>r. card (var_set_rule r)) ` rules F)"
              using rin by blast
            thus ?thesis unfolding RuleVars_def using Max_ge[OF finRuleVars] by blast
          qed
          thus ?thesis by (rule mult_le_mono1)
        qed
        finally show ?thesis .
      qed
      have "Mi = (sum_list (map len_formula (prems r)) + len_formula (concl r))
                 + (\<Sum>v \<in> var_set_rule r. len_formula (sigma v))"
        unfolding Mi_def by simp
      also have "\<dots> \<le> RuleSz + RuleVars * len_proof pr" using part1 sum_le by linarith
      also have "\<dots> \<le> KM * len_proof pr"
      proof -
        have "RuleSz \<le> RuleSz * len_proof pr" using mult_le_mono2[OF lp1, of RuleSz] by simp
        hence "RuleSz + RuleVars * len_proof pr
               \<le> RuleSz * len_proof pr + RuleVars * len_proof pr" by linarith
        also have "\<dots> = KM * len_proof pr" unfolding KM_def by (simp add: add_mult_distrib)
        finally show ?thesis .
      qed
      finally show ?thesis .
    qed
    \<comment> \<open>The depth envelope: collapse C71*log(Mi+1) to ccfin*log(len_proof pr+1).\<close>
    have dep_fin: "real dep \<le> ccfin * log 2 (real (len_proof pr) + 1)"
    proof -
      have logMi0: "0 \<le> log 2 (real Mi + 1)"
      proof -
        have "(1::real) \<le> real Mi + 1" by simp
        hence "log 2 (1::real) \<le> log 2 (real Mi + 1)" by (intro log_mono) auto
        thus ?thesis by simp
      qed
      have step1: "C71 * log 2 (real Mi + 1) \<le> cc' * log 2 (real Mi + 1)"
      proof -
        have "C71 \<le> cc'" unfolding cc'_def by simp
        thus ?thesis using mult_right_mono[OF _ logMi0] by blast
      qed
      have Mi_real: "real Mi + 1 \<le> real (KM * len_proof pr) + 1"
      proof -
        have "real Mi \<le> real (KM * len_proof pr)" by (rule of_nat_mono[OF Mi_le])
        thus ?thesis by simp
      qed
      have logMi_le: "log 2 (real Mi + 1) \<le> log 2 (real (KM * len_proof pr) + 1)"
      proof -
        have "(0::real) < real Mi + 1" by simp
        thus ?thesis using Mi_real by (intro log_mono) auto
      qed
      have step2: "cc' * log 2 (real Mi + 1)
                   \<le> cc' * log 2 (real (KM * len_proof pr) + 1)"
        using mult_left_mono[OF logMi_le c'0] .
      have step3: "cc' * log 2 (real (KM * len_proof pr) + 1)
                   \<le> ccfin * log 2 (real (len_proof pr) + 1)"
      proof -
        have KMr1: "1 \<le> real KM" using KM1 by simp
        have Sr0: "0 \<le> real (len_proof pr)" by simp
        have prod_ge: "real (KM * len_proof pr) + 1
                       \<le> (real KM + 1) * (real (len_proof pr) + 1)"
        proof -
          have "(real KM + 1) * (real (len_proof pr) + 1)
                = real KM * real (len_proof pr) + real KM + real (len_proof pr) + 1"
            by (simp add: algebra_simps)
          moreover have "real (KM * len_proof pr) = real KM * real (len_proof pr)"
            by simp
          ultimately show ?thesis using KMr1 Sr0 by simp
        qed
        have pos1: "0 < real (KM * len_proof pr) + 1" by (simp add: add_nonneg_pos)
        have logprod: "log 2 (real (KM * len_proof pr) + 1)
                       \<le> log 2 ((real KM + 1) * (real (len_proof pr) + 1))"
          using prod_ge pos1 by (intro log_mono) auto
        have posKM: "0 < real KM + 1" using KMr1 by simp
        have posS: "0 < real (len_proof pr) + 1" by (simp add: add_nonneg_pos)
        have logsplit: "log 2 ((real KM + 1) * (real (len_proof pr) + 1))
                        = log 2 (real KM + 1) + log 2 (real (len_proof pr) + 1)"
          using posKM posS by (simp add: log_mult)
        have logKM0: "0 \<le> log 2 (real KM + 1)"
        proof -
          have "log 2 (1::real) \<le> log 2 (real KM + 1)" using KMr1 by (intro log_mono) auto
          thus ?thesis by simp
        qed
        have logS1: "1 \<le> log 2 (real (len_proof pr) + 1)"
        proof -
          have "(2::real) \<le> real (len_proof pr) + 1" using lp1 by simp
          hence "log 2 (2::real) \<le> log 2 (real (len_proof pr) + 1)" by (intro log_mono) auto
          thus ?thesis by simp
        qed
        have "log 2 (real (KM * len_proof pr) + 1)
              \<le> log 2 (real KM + 1) + log 2 (real (len_proof pr) + 1)"
          using logprod logsplit by simp
        also have "\<dots> \<le> (log 2 (real KM + 1) + 1) * log 2 (real (len_proof pr) + 1)"
        proof -
          have h: "log 2 (real KM + 1)
                   \<le> log 2 (real KM + 1) * log 2 (real (len_proof pr) + 1)"
            using mult_left_mono[OF logS1 logKM0] by simp
          have "(log 2 (real KM + 1) + 1) * log 2 (real (len_proof pr) + 1)
                = log 2 (real KM + 1) * log 2 (real (len_proof pr) + 1)
                  + log 2 (real (len_proof pr) + 1)"
            by (simp add: algebra_simps)
          thus ?thesis using h by linarith
        qed
        finally have key: "log 2 (real (KM * len_proof pr) + 1)
              \<le> (log 2 (real KM + 1) + 1) * log 2 (real (len_proof pr) + 1)" .
        have "cc' * log 2 (real (KM * len_proof pr) + 1)
              \<le> cc' * ((log 2 (real KM + 1) + 1) * log 2 (real (len_proof pr) + 1))"
          using mult_left_mono[OF key c'0] .
        also have "\<dots> = ccfin * log 2 (real (len_proof pr) + 1)"
          unfolding ccfin_def by (simp add: algebra_simps)
        finally show ?thesis .
      qed
      show ?thesis using dep_b step1 step2 step3 by linarith
    qed
    \<comment> \<open>Extract the proof object and package the bounds.\<close>
    obtain D where Dvalid: "valid_proof F D"
        and Dasm: "assumptions D
              \<subseteq> (\<lambda>p. spira_trans (sub_formula sigma p)) ` set (prems r)"
        and Dth: "frege_proof.thesis D = spira_trans (sub_formula sigma (concl r))"
        and Dlen: "length (steps D) \<le> lines"
        and Dsz: "\<forall>s \<in> set (steps D). len_formula s \<le> sz"
        and Ddep: "\<forall>s \<in> set (steps D). depth_formula s \<le> dep"
        and Dwf: "\<forall>s \<in> set (steps D). formula_well_formed (alphabet F) s"
      using db unfolding derives_balanced_def by blast
    have asm_sub: "assumptions D \<subseteq> spira_trans ` set (take i (steps pr))"
    proof -
      have "(\<lambda>p. spira_trans (sub_formula sigma p)) ` set (prems r)
            \<subseteq> spira_trans ` set (take i (steps pr))"
      proof
        fix x assume "x \<in> (\<lambda>p. spira_trans (sub_formula sigma p)) ` set (prems r)"
        then obtain p where pp: "p \<in> set (prems r)"
            and xeq: "x = spira_trans (sub_formula sigma p)" by blast
        have "sub_formula sigma p = sub_formula sb p" using sigma_prem[OF pp] .
        moreover have "sub_formula sb p \<in> set (take i (steps pr))" using prem_in pp by blast
        ultimately have "x = spira_trans (sub_formula sb p)
              \<and> sub_formula sb p \<in> set (take i (steps pr))" using xeq by simp
        thus "x \<in> spira_trans ` set (take i (steps pr))" by blast
      qed
      thus ?thesis using Dasm by blast
    qed
    have Dth': "frege_proof.thesis D = spira_trans (steps pr ! i)"
      using Dth sigma_concl unfolding Li_def by simp
    have Dlen': "length (steps D) \<le> poly bndfin (len_proof pr)"
    proof -
      have "lines \<le> poly B71 Mi" using lines_b .
      also have "\<dots> \<le> poly B71 (KM * len_proof pr)" using poly_nat_mono[OF Mi_le] .
      also have "\<dots> = poly bndfin (len_proof pr)" using bndfin_eval by simp
      finally show ?thesis using Dlen by linarith
    qed
    have Dsz': "\<forall>s \<in> set (steps D). len_formula s \<le> poly bndfin (len_proof pr)"
    proof
      fix s assume "s \<in> set (steps D)"
      hence "len_formula s \<le> sz" using Dsz by blast
      also have "sz \<le> poly B71 Mi" using sz_b .
      also have "\<dots> \<le> poly B71 (KM * len_proof pr)" using poly_nat_mono[OF Mi_le] .
      also have "\<dots> = poly bndfin (len_proof pr)" using bndfin_eval by simp
      finally show "len_formula s \<le> poly bndfin (len_proof pr)" .
    qed
    have Ddep': "\<forall>s \<in> set (steps D).
        real (depth_formula s) \<le> ccfin * log 2 (real (len_proof pr) + 1)"
    proof
      fix s assume "s \<in> set (steps D)"
      hence "depth_formula s \<le> dep" using Ddep by blast
      hence "real (depth_formula s) \<le> real dep" by simp
      also have "\<dots> \<le> ccfin * log 2 (real (len_proof pr) + 1)" using dep_fin .
      finally show "real (depth_formula s) \<le> ccfin * log 2 (real (len_proof pr) + 1)" .
    qed
    have Dconj: "valid_proof F D
            \<and> assumptions D \<subseteq> spira_trans ` set (take i (steps pr))
            \<and> frege_proof.thesis D = spira_trans (steps pr ! i)
            \<and> length (steps D) \<le> poly bndfin (len_proof pr)
            \<and> (\<forall>s \<in> set (steps D). len_formula s \<le> poly bndfin (len_proof pr))
            \<and> (\<forall>s \<in> set (steps D). real (depth_formula s)
                  \<le> ccfin * log 2 (real (len_proof pr) + 1))
            \<and> (\<forall>s \<in> set (steps D). formula_well_formed (alphabet F) s)"
      by (rule conjI[OF Dvalid conjI[OF asm_sub conjI[OF Dth'
            conjI[OF Dlen' conjI[OF Dsz' conjI[OF Ddep' Dwf]]]]]])
    show "\<exists>D. valid_proof F D
            \<and> assumptions D \<subseteq> spira_trans ` set (take i (steps pr))
            \<and> frege_proof.thesis D = spira_trans (steps pr ! i)
            \<and> length (steps D) \<le> poly bndfin (len_proof pr)
            \<and> (\<forall>s \<in> set (steps D). len_formula s \<le> poly bndfin (len_proof pr))
            \<and> (\<forall>s \<in> set (steps D). real (depth_formula s)
                  \<le> ccfin * log 2 (real (len_proof pr) + 1))
            \<and> (\<forall>s \<in> set (steps D). formula_well_formed (alphabet F) s)"
      using Dconj by (rule exI)
    qed
  qed
qed

subsection \<open>Final conversion: from t(phi) back to phi\<close>

(*
  Lemma 6.4 instantiated with the variables of phi (sub = Atom) proves
  t(phi) <-> phi; the modus ponens converter then derives phi from the single
  assumption t(phi).  All bounds are polynomial / logarithmic in len phi.
*)
lemma final_conversion:
  shows "\<exists>(bnd :: nat poly) (c :: real). 0 \<le> c \<and>
           (\<forall>phi. formula_well_formed (alphabet F) phi \<longrightarrow>
             (\<exists>cv. valid_proof F cv
                 \<and> assumptions cv \<subseteq> {spira_trans phi}
                 \<and> frege_proof.thesis cv = phi
                 \<and> length (steps cv) \<le> poly bnd (len_formula phi)
                 \<and> (\<forall>s \<in> set (steps cv). len_formula s \<le> poly bnd (len_formula phi))
                 \<and> (\<forall>s \<in> set (steps cv). real (depth_formula s)
                       \<le> real (depth_formula phi)
                         + c * log 2 (real (len_formula phi) + 1))
                 \<and> (\<forall>s \<in> set (steps cv). formula_well_formed (alphabet F) s)))"
proof -
  obtain bnd64 c64 where TCF:
    "\<forall>f sub. formula_well_formed (alphabet F) f
             \<and> (\<forall>f' \<in> range sub. formula_well_formed (alphabet F) f') \<longrightarrow>
       (let M = len_formula f + (\<Sum>v \<in> var_set_form f. len_formula (sub v))
        in (\<exists>lines sz dep.
              provable_balanced_iff (spira_trans (sub_formula sub f))
                (sub_formula (\<lambda>v. spira_trans (sub v)) f) lines sz dep
            \<and> lines \<le> poly bnd64 M \<and> sz \<le> poly bnd64 M
            \<and> real dep \<le> real (depth_formula f) + c64 * log 2 (real M + 1)))"
    using transform_commutes_form by blast
  obtain tc where TC: "\<forall>f. formula_well_formed (alphabet F) f \<longrightarrow>
       real (depth_formula (spira_trans f)) \<le> tc * log 2 (real (len_formula f) + 1)"
    using trans_c by blast
  define c64' where "c64' = max c64 0"
  define tc' where "tc' = max tc 0"
  define cfin where "cfin = 2 * c64' + tc' + real mp_step_depth + 1"
  define bndfin where "bndfin = pcompose bnd64 (monom 2 1)
                              + Polynomial.smult mp_step_len (rebal_tb + monom 1 1)
                              + [: mp_lines + 1 :]"
  have c64'0: "0 \<le> c64'" unfolding c64'_def by simp
  have tc'0: "0 \<le> tc'" unfolding tc'_def by simp
  have cfin0: "0 \<le> cfin" unfolding cfin_def using c64'0 tc'0 by simp
  have bndfin_eval: "\<And>N. poly bndfin N
      = poly bnd64 (2 * N) + mp_step_len * (poly rebal_tb N + N) + (mp_lines + 1)"
    unfolding bndfin_def by (simp add: poly_pcompose poly_monom)
  show ?thesis
  proof (intro exI[where x = bndfin] exI[where x = cfin] conjI)
    show "0 \<le> cfin" using cfin0 .
  next
    show "\<forall>phi. formula_well_formed (alphabet F) phi \<longrightarrow>
            (\<exists>cv. valid_proof F cv
                \<and> assumptions cv \<subseteq> {spira_trans phi}
                \<and> frege_proof.thesis cv = phi
                \<and> length (steps cv) \<le> poly bndfin (len_formula phi)
                \<and> (\<forall>s \<in> set (steps cv). len_formula s \<le> poly bndfin (len_formula phi))
                \<and> (\<forall>s \<in> set (steps cv). real (depth_formula s)
                      \<le> real (depth_formula phi)
                        + cfin * log 2 (real (len_formula phi) + 1))
                \<and> (\<forall>s \<in> set (steps cv). formula_well_formed (alphabet F) s))"
    proof (intro allI impI)
      fix phi assume wfphi: "formula_well_formed (alphabet F) phi"
      have lenphi1: "1 \<le> len_formula phi" by (rule len_formula_positive)
  let ?N = "len_formula phi"
  have logN0: "0 \<le> log 2 (real ?N + 1)"
  proof -
    have "log 2 (1::real) \<le> log 2 (real ?N + 1)" by (intro log_mono) auto
    thus ?thesis by simp
  qed
  have logN1: "1 \<le> log 2 (real ?N + 1)"
  proof -
    have "(2::real) \<le> real ?N + 1" using lenphi1 by simp
    hence "log 2 (2::real) \<le> log 2 (real ?N + 1)" by (intro log_mono) auto
    thus ?thesis by simp
  qed
  \<comment> \<open>Lemma 6.4 at phi with the identity substitution.  We instantiate Lemma 6.4
      at the opaque substitution idsub = Atom so the blast that solves it does not
      blow up on the constructor Atom; the identity facts are recovered afterwards.\<close>
  define idsub :: "string \<Rightarrow> 'a formula" where "idsub = Atom"
  have precondphi: "formula_well_formed (alphabet F) phi
        \<and> (\<forall>f' \<in> range idsub. formula_well_formed (alphabet F) f')"
    using wfphi unfolding idsub_def by auto
  define Mphi where
    "Mphi = len_formula phi + (\<Sum>v \<in> var_set_form phi. len_formula (idsub v))"
  have tcf_ex: "\<exists>lines sz dep.
        provable_balanced_iff (spira_trans (sub_formula idsub phi))
          (sub_formula (\<lambda>v. spira_trans (idsub v)) phi) lines sz dep
      \<and> lines \<le> poly bnd64 Mphi \<and> sz \<le> poly bnd64 Mphi
      \<and> real dep \<le> real (depth_formula phi) + c64 * log 2 (real Mphi + 1)"
    using TCF precondphi unfolding Let_def Mphi_def by blast
  obtain lines sz dep where
      pbi0: "provable_balanced_iff (spira_trans (sub_formula idsub phi))
               (sub_formula (\<lambda>v. spira_trans (idsub v)) phi) lines sz dep"
      and lines_b: "lines \<le> poly bnd64 Mphi"
      and sz_b: "sz \<le> poly bnd64 Mphi"
      and dep_b: "real dep \<le> real (depth_formula phi) + c64 * log 2 (real Mphi + 1)"
    using tcf_ex by blast
  have form_eq1: "spira_trans (sub_formula idsub phi) = spira_trans phi"
  proof -
    have "sub_formula idsub phi = phi" unfolding idsub_def by (rule sub_formula_atom_id)
    thus ?thesis by simp
  qed
  have sta: "\<And>v. spira_trans (Atom v) = Atom v"
  proof -
    fix v
    show "spira_trans (Atom v) = Atom v"
    proof (rule spira_trans_id_when_small)
      show "formula_well_formed (alphabet F) (Atom v)" by simp
      show "len_formula (Atom v) < spira_threshold"
        unfolding spira_threshold_def by simp
    qed
  qed
  have form_eq2: "sub_formula (\<lambda>v. spira_trans (idsub v)) phi = phi"
  proof -
    have "sub_formula (\<lambda>v. spira_trans (idsub v)) phi = sub_formula Atom phi"
      unfolding idsub_def by (rule sub_formula_agree) (simp add: sta)
    also have "\<dots> = phi" by (rule sub_formula_atom_id)
    finally show ?thesis .
  qed
  have pbi: "provable_balanced_iff (spira_trans phi) phi lines sz dep"
    using pbi0 form_eq1 form_eq2 by simp
  have Mphi_le: "Mphi \<le> 2 * len_formula phi"
  proof -
    have "(\<Sum>v \<in> var_set_form phi. len_formula (idsub v))
          = (\<Sum>v \<in> var_set_form phi. 1)"
      unfolding idsub_def by simp
    also have "\<dots> = card (var_set_form phi)" by simp
    also have "\<dots> \<le> len_formula phi" by (rule card_var_set_le_len)
    finally show ?thesis unfolding Mphi_def by simp
  qed
  \<comment> \<open>The modus ponens converter.\<close>
  have wf_sphi: "formula_well_formed (alphabet F) (spira_trans phi)"
    by (rule spira_trans_wf[OF wfphi])
  obtain cv where cv:
      "valid_proof F cv" "assumptions cv \<subseteq> {spira_trans phi}"
      "frege_proof.thesis cv = phi"
      "length (steps cv) \<le> lines + mp_lines"
      "\<forall>st \<in> set (steps cv). len_formula st
         \<le> max sz (mp_step_len * (len_formula (spira_trans phi) + len_formula phi))"
      "\<forall>st \<in> set (steps cv). depth_formula st
         \<le> max dep (mp_step_depth
              + max (depth_formula (spira_trans phi)) (depth_formula phi))"
      "\<forall>st \<in> set (steps cv). formula_well_formed (alphabet F) st"
    using iff_elimination[OF pbi wf_sphi wfphi] by blast
  \<comment> \<open>Size envelope.\<close>
  have lsp: "len_formula (spira_trans phi) \<le> poly rebal_tb (len_formula phi)"
    using spira_trans_len_le_tb[OF wfphi order_refl] .
  have sz_env: "sz \<le> poly bndfin (len_formula phi)"
  proof -
    have "sz \<le> poly bnd64 Mphi" using sz_b .
    also have "\<dots> \<le> poly bnd64 (2 * len_formula phi)" using poly_nat_mono[OF Mphi_le] .
    also have "\<dots> \<le> poly bndfin (len_formula phi)"
      using bndfin_eval[of "len_formula phi"] by linarith
    finally show ?thesis .
  qed
  have cv_lines: "length (steps cv) \<le> poly bndfin (len_formula phi)"
  proof -
    have "length (steps cv) \<le> lines + mp_lines" using cv(4) .
    also have "\<dots> \<le> poly bnd64 Mphi + mp_lines" using lines_b by simp
    also have "\<dots> \<le> poly bnd64 (2 * len_formula phi) + mp_lines"
      using poly_nat_mono[OF Mphi_le] by simp
    also have "\<dots> \<le> poly bndfin (len_formula phi)"
      using bndfin_eval[of "len_formula phi"] by linarith
    finally show ?thesis .
  qed
  have cv_len: "\<forall>s \<in> set (steps cv). len_formula s \<le> poly bndfin (len_formula phi)"
  proof
    fix s assume "s \<in> set (steps cv)"
    hence "len_formula s
           \<le> max sz (mp_step_len * (len_formula (spira_trans phi) + len_formula phi))"
      using cv(5) by blast
    also have "\<dots> \<le> poly bndfin (len_formula phi)"
    proof (rule max.boundedI)
      show "sz \<le> poly bndfin (len_formula phi)" using sz_env .
    next
      have "mp_step_len * (len_formula (spira_trans phi) + len_formula phi)
            \<le> mp_step_len * (poly rebal_tb (len_formula phi) + len_formula phi)"
        using lsp by (simp add: mult_le_mono2)
      also have "\<dots> \<le> poly bndfin (len_formula phi)"
        using bndfin_eval[of "len_formula phi"] by linarith
      finally show "mp_step_len * (len_formula (spira_trans phi) + len_formula phi)
                    \<le> poly bndfin (len_formula phi)" .
    qed
    finally show "len_formula s \<le> poly bndfin (len_formula phi)" .
  qed
  \<comment> \<open>Depth envelope.\<close>
  have log2N: "log 2 (real (2 * len_formula phi) + 1) \<le> 2 * log 2 (real (len_formula phi) + 1)"
  proof -
    have "real (2 * len_formula phi) + 1 \<le> (real (len_formula phi) + 1)^2"
      by (simp add: power2_eq_square algebra_simps)
    moreover have "0 < real (2 * len_formula phi) + 1" by (simp add: add_nonneg_pos)
    ultimately have "log 2 (real (2 * len_formula phi) + 1)
                     \<le> log 2 ((real (len_formula phi) + 1)^2)"
      by (intro log_mono) auto
    also have "\<dots> = 2 * log 2 (real (len_formula phi) + 1)"
      by (simp add: log_nat_power)
    finally show ?thesis .
  qed
  have dsp: "real (depth_formula (spira_trans phi)) \<le> tc' * log 2 (real (len_formula phi) + 1)"
  proof -
    have "real (depth_formula (spira_trans phi)) \<le> tc * log 2 (real (len_formula phi) + 1)"
      using TC wfphi by blast
    also have "\<dots> \<le> tc' * log 2 (real (len_formula phi) + 1)"
      using mult_right_mono[OF _ logN0] tc'_def by simp
    finally show ?thesis .
  qed
  have dep_branch: "real dep
      \<le> real (depth_formula phi) + cfin * log 2 (real (len_formula phi) + 1)"
  proof -
    have logMphi0: "0 \<le> log 2 (real Mphi + 1)"
    proof -
      have "log 2 (1::real) \<le> log 2 (real Mphi + 1)" by (intro log_mono) auto
      thus ?thesis by simp
    qed
    have c1: "c64 * log 2 (real Mphi + 1) \<le> c64' * log 2 (real Mphi + 1)"
      using mult_right_mono[OF _ logMphi0] c64'_def by simp
    have logMphi_le: "log 2 (real Mphi + 1) \<le> log 2 (real (2 * len_formula phi) + 1)"
    proof -
      have "real Mphi + 1 \<le> real (2 * len_formula phi) + 1"
        using of_nat_mono[OF Mphi_le] by simp
      moreover have "0 < real Mphi + 1" by (simp add: add_nonneg_pos)
      ultimately show ?thesis by (intro log_mono) auto
    qed
    have c2: "c64' * log 2 (real Mphi + 1)
              \<le> c64' * (2 * log 2 (real (len_formula phi) + 1))"
      using mult_left_mono[OF order_trans[OF logMphi_le log2N] c64'0] .
    have "c64 * log 2 (real Mphi + 1) \<le> 2 * c64' * log 2 (real (len_formula phi) + 1)"
      using c1 c2 by simp
    moreover have "2 * c64' * log 2 (real (len_formula phi) + 1)
                   \<le> cfin * log 2 (real (len_formula phi) + 1)"
      using mult_right_mono[of "2 * c64'" cfin "log 2 (real (len_formula phi) + 1)"]
            logN0 cfin_def tc'0 by simp
    ultimately show ?thesis using dep_b by linarith
  qed
  have other_branch: "real mp_step_depth
        + max (real (depth_formula (spira_trans phi))) (real (depth_formula phi))
      \<le> real (depth_formula phi) + cfin * log 2 (real (len_formula phi) + 1)"
  proof -
    have maxle: "max (real (depth_formula (spira_trans phi))) (real (depth_formula phi))
          \<le> real (depth_formula phi) + tc' * log 2 (real (len_formula phi) + 1)"
    proof (rule max.boundedI)
      have "0 \<le> tc' * log 2 (real (len_formula phi) + 1)"
        using tc'0 logN0 by (rule mult_nonneg_nonneg)
      thus "real (depth_formula (spira_trans phi))
            \<le> real (depth_formula phi) + tc' * log 2 (real (len_formula phi) + 1)"
        using dsp by linarith
    next
      have "0 \<le> tc' * log 2 (real (len_formula phi) + 1)"
        using tc'0 logN0 by (rule mult_nonneg_nonneg)
      thus "real (depth_formula phi)
            \<le> real (depth_formula phi) + tc' * log 2 (real (len_formula phi) + 1)"
        by linarith
    qed
    have mpd: "real mp_step_depth
               \<le> real mp_step_depth * log 2 (real (len_formula phi) + 1)"
      using mult_left_mono[OF logN1, of "real mp_step_depth"] by simp
    have "real mp_step_depth
          + max (real (depth_formula (spira_trans phi))) (real (depth_formula phi))
          \<le> real mp_step_depth * log 2 (real (len_formula phi) + 1)
            + real (depth_formula phi) + tc' * log 2 (real (len_formula phi) + 1)"
      using maxle mpd by linarith
    also have "\<dots> = real (depth_formula phi)
          + (real mp_step_depth + tc') * log 2 (real (len_formula phi) + 1)"
      by (simp add: algebra_simps)
    also have "\<dots> \<le> real (depth_formula phi)
          + cfin * log 2 (real (len_formula phi) + 1)"
    proof -
      have "(real mp_step_depth + tc') * log 2 (real (len_formula phi) + 1)
            \<le> cfin * log 2 (real (len_formula phi) + 1)"
        using mult_right_mono[of "real mp_step_depth + tc'" cfin
                "log 2 (real (len_formula phi) + 1)"] logN0 cfin_def c64'0 by simp
      thus ?thesis by linarith
    qed
    finally show ?thesis .
  qed
  have cv_dep: "\<forall>s \<in> set (steps cv). real (depth_formula s)
        \<le> real (depth_formula phi) + cfin * log 2 (real (len_formula phi) + 1)"
  proof
    fix s assume "s \<in> set (steps cv)"
    hence h: "depth_formula s
        \<le> max dep (mp_step_depth
             + max (depth_formula (spira_trans phi)) (depth_formula phi))"
      using cv(6) by blast
    have hr: "real (depth_formula s)
        \<le> max (real dep) (real mp_step_depth
             + max (real (depth_formula (spira_trans phi))) (real (depth_formula phi)))"
      using of_nat_mono[OF h] by (simp add: of_nat_max)
    have "max (real dep) (real mp_step_depth
             + max (real (depth_formula (spira_trans phi))) (real (depth_formula phi)))
          \<le> real (depth_formula phi) + cfin * log 2 (real (len_formula phi) + 1)"
      using dep_branch other_branch by (rule max.boundedI)
    thus "real (depth_formula s)
          \<le> real (depth_formula phi) + cfin * log 2 (real (len_formula phi) + 1)"
      using hr by linarith
  qed
      show "\<exists>cv. valid_proof F cv \<and> assumptions cv \<subseteq> {spira_trans phi}
              \<and> frege_proof.thesis cv = phi
              \<and> length (steps cv) \<le> poly bndfin (len_formula phi)
              \<and> (\<forall>s \<in> set (steps cv). len_formula s \<le> poly bndfin (len_formula phi))
              \<and> (\<forall>s \<in> set (steps cv). real (depth_formula s)
                    \<le> real (depth_formula phi)
                      + cfin * log 2 (real (len_formula phi) + 1))
              \<and> (\<forall>s \<in> set (steps cv). formula_well_formed (alphabet F) s)"
        using cv(1,2,3,7) cv_lines cv_len cv_dep by blast
    qed
  qed
qed

(* theorem 1.1 *)
subsection \<open>Proof balancing (final theorem)\<close>

theorem proof_balancing:
  shows "\<exists> bound :: nat poly. \<exists> c :: real.
           \<forall> pr. valid_proof F pr \<and> assumptions pr = {}
                 \<and> (\<forall> s \<in> set (steps pr). formula_well_formed (alphabet F) s) \<longrightarrow>
             (\<exists> pr'. valid_proof F pr'
                   \<and> assumptions pr' = {}
                   \<and> thesis pr' = thesis pr
                   \<and> len_proof pr' \<le> poly bound (len_proof pr)
                   \<and> (\<forall> line \<in> set (steps pr').
                        real (depth_formula line)
                        \<le> real (depth_formula (thesis pr))
                          + c * log 2 (real (len_proof pr) + 1))
                   \<and> (\<forall> line \<in> set (steps pr'). formula_well_formed (alphabet F) line))"
proof -
  have fs_F: "frege_system F" by (meson frege_balancing_axioms frege_balancing_def)
  obtain Bpl ccpl where ccpl0: "0 \<le> ccpl" and PL:
    "\<forall>pr. valid_proof F pr \<and> assumptions pr = {}
          \<and> (\<forall>s \<in> set (steps pr). formula_well_formed (alphabet F) s) \<longrightarrow>
       (\<forall>i < length (steps pr). \<exists>D. valid_proof F D
          \<and> assumptions D \<subseteq> spira_trans ` set (take i (steps pr))
          \<and> frege_proof.thesis D = spira_trans (steps pr ! i)
          \<and> length (steps D) \<le> poly Bpl (len_proof pr)
          \<and> (\<forall>s \<in> set (steps D). len_formula s \<le> poly Bpl (len_proof pr))
          \<and> (\<forall>s \<in> set (steps D). real (depth_formula s)
                \<le> ccpl * log 2 (real (len_proof pr) + 1))
          \<and> (\<forall>s \<in> set (steps D). formula_well_formed (alphabet F) s))"
    using per_line_simulation by blast
  obtain Bfc cfc where cfc0: "0 \<le> cfc" and FC:
    "\<forall>phi. formula_well_formed (alphabet F) phi \<longrightarrow>
       (\<exists>cv. valid_proof F cv \<and> assumptions cv \<subseteq> {spira_trans phi}
          \<and> frege_proof.thesis cv = phi
          \<and> length (steps cv) \<le> poly Bfc (len_formula phi)
          \<and> (\<forall>s \<in> set (steps cv). len_formula s \<le> poly Bfc (len_formula phi))
          \<and> (\<forall>s \<in> set (steps cv). real (depth_formula s)
                \<le> real (depth_formula phi) + cfc * log 2 (real (len_formula phi) + 1))
          \<and> (\<forall>s \<in> set (steps cv). formula_well_formed (alphabet F) s))"
    using final_conversion by blast
  define boundfin where "boundfin = (monom 1 1 * Bpl + Bfc) * (Bpl + Bfc)"
  define cfin where "cfin = max ccpl cfc"
  show ?thesis
  proof (intro exI[where x = boundfin] exI[where x = cfin] allI impI)
    fix pr assume A: "valid_proof F pr \<and> assumptions pr = {}
                      \<and> (\<forall>s \<in> set (steps pr). formula_well_formed (alphabet F) s)"
    have vpr: "valid_proof F pr" using A by blast
    have noasm: "assumptions pr = {}" using A by blast
    have wfsteps: "\<forall>s \<in> set (steps pr). formula_well_formed (alphabet F) s" using A by blast
    have ne: "steps pr \<noteq> []" using vpr unfolding valid_proof_def by simp
    have thesis_eq_last: "thesis pr = last (steps pr)"
      using vpr unfolding valid_proof_def by simp
    define m where "m = length (steps pr)"
    define S where "S = len_proof pr"
    have m1: "1 \<le> m" unfolding m_def using ne by (cases "steps pr") auto
    have mS: "m \<le> S"
      using length_le_sum_list_len[of "steps pr"] unfolding m_def S_def by simp
    have thesis_in: "thesis pr \<in> set (steps pr)"
      using thesis_eq_last last_in_set[OF ne] by simp
    have wfthesis: "formula_well_formed (alphabet F) (thesis pr)"
      using wfsteps thesis_in by blast
    have lenthesis_le_S: "len_formula (thesis pr) \<le> S"
    proof -
      have "len_formula (thesis pr) \<in> set (map len_formula (steps pr))"
        using thesis_in by simp
      hence "len_formula (thesis pr) \<le> sum_list (map len_formula (steps pr))"
        by (rule member_le_sum_list) simp
      thus ?thesis unfolding S_def by simp
    qed
    have stepm1: "steps pr ! (m - 1) = thesis pr"
    proof -
      have "steps pr ! (m - 1) = last (steps pr)"
        unfolding m_def using last_conv_nth[OF ne] by simp
      thus ?thesis using thesis_eq_last by simp
    qed
    \<comment> \<open>The per-line sub-derivations, instantiated for pr and indexed by a function.\<close>
    have plpr: "\<forall>i \<in> {0..<m}. \<exists>D. valid_proof F D
          \<and> assumptions D \<subseteq> spira_trans ` set (take i (steps pr))
          \<and> frege_proof.thesis D = spira_trans (steps pr ! i)
          \<and> length (steps D) \<le> poly Bpl S
          \<and> (\<forall>s \<in> set (steps D). len_formula s \<le> poly Bpl S)
          \<and> (\<forall>s \<in> set (steps D). real (depth_formula s) \<le> ccpl * log 2 (real S + 1))
          \<and> (\<forall>s \<in> set (steps D). formula_well_formed (alphabet F) s)"
      using PL A unfolding m_def S_def by simp
    obtain DD where DD: "\<forall>i \<in> {0..<m}. valid_proof F (DD i)
          \<and> assumptions (DD i) \<subseteq> spira_trans ` set (take i (steps pr))
          \<and> frege_proof.thesis (DD i) = spira_trans (steps pr ! i)
          \<and> length (steps (DD i)) \<le> poly Bpl S
          \<and> (\<forall>s \<in> set (steps (DD i)). len_formula s \<le> poly Bpl S)
          \<and> (\<forall>s \<in> set (steps (DD i)). real (depth_formula s) \<le> ccpl * log 2 (real S + 1))
          \<and> (\<forall>s \<in> set (steps (DD i)). formula_well_formed (alphabet F) s)"
      using bchoice[OF plpr] by blast
    have wf_DD: "\<And>k. k < m \<Longrightarrow> \<forall>s \<in> set (steps (DD k)). formula_well_formed (alphabet F) s"
      using DD by simp
    have valid_DD: "\<And>k. k < m \<Longrightarrow> valid_proof F (DD k)" using DD by simp
    have thesis_DD: "\<And>k. k < m \<Longrightarrow> frege_proof.thesis (DD k) = spira_trans (steps pr ! k)"
      using DD by simp
    have thesis_in_steps: "\<And>k. k < m \<Longrightarrow> spira_trans (steps pr ! k) \<in> set (steps (DD k))"
    proof -
      fix k assume km: "k < m"
      have vk: "valid_proof F (DD k)" using valid_DD[OF km] .
      have nek: "steps (DD k) \<noteq> []" using vk unfolding valid_proof_def by simp
      have "frege_proof.thesis (DD k) = last (steps (DD k))"
        using vk unfolding valid_proof_def by simp
      hence "spira_trans (steps pr ! k) = last (steps (DD k))"
        using thesis_DD[OF km] by simp
      thus "spira_trans (steps pr ! k) \<in> set (steps (DD k))"
        using last_in_set[OF nek] by simp
    qed
    have asm_chain: "\<And>j. j < m \<Longrightarrow>
        assumptions (DD j) \<subseteq> (\<Union>k \<in> {0..<j}. set (steps (DD k)))"
    proof -
      fix j assume jm: "j < m"
      have "assumptions (DD j) \<subseteq> spira_trans ` set (take j (steps pr))"
        using DD jm by simp
      also have "\<dots> \<subseteq> (\<Union>k \<in> {0..<j}. set (steps (DD k)))"
      proof
        fix x assume "x \<in> spira_trans ` set (take j (steps pr))"
        then obtain y where yin: "y \<in> set (take j (steps pr))"
            and xy: "x = spira_trans y" by blast
        from yin obtain k where klt: "k < length (take j (steps pr))"
            and yk: "(take j (steps pr)) ! k = y"
          using in_set_conv_nth[of y "take j (steps pr)"] by blast
        have kmin: "k < min j (length (steps pr))" using klt by simp
        have kj: "k < j" using kmin by simp
        have km: "k < m" using kmin unfolding m_def by simp
        have "steps pr ! k = y" using yk kj by simp
        hence "x = spira_trans (steps pr ! k)" using xy by simp
        hence "x \<in> set (steps (DD k))" using thesis_in_steps[OF km] by simp
        thus "x \<in> (\<Union>k \<in> {0..<j}. set (steps (DD k)))" using kj by auto
      qed
      finally show "assumptions (DD j) \<subseteq> (\<Union>k \<in> {0..<j}. set (steps (DD k)))" .
    qed
    \<comment> \<open>Glue the sub-derivations into a no-assumption proof of t(thesis pr).\<close>
    define cvs where "cvs = map DD [0..<(m - 1)]"
    define base where "base = DD (m - 1)"
    define G where "G = foldr combine_proofs cvs base"
    have cvs_set: "set cvs = DD ` {0..<(m - 1)}" unfolding cvs_def by simp
    have cvs_len: "length cvs = m - 1" unfolding cvs_def by simp
    have cvs_take: "\<And>i. i \<le> m - 1 \<Longrightarrow> set (take i cvs) = DD ` {0..<i}"
    proof -
      fix i assume "i \<le> m - 1"
      hence "take i cvs = map DD [0..<i]"
        unfolding cvs_def by (simp add: take_map)
      thus "set (take i cvs) = DD ` {0..<i}" by simp
    qed
    have vbase: "valid_proof F base"
      unfolding base_def using valid_DD m1 by simp
    have cc_v: "\<forall>p \<in> set cvs. valid_proof F p"
    proof
      fix p assume "p \<in> set cvs"
      then obtain k where "k \<in> {0..<(m - 1)}" and "p = DD k" using cvs_set by auto
      hence "k < m" by auto
      thus "valid_proof F p" using valid_DD \<open>p = DD k\<close> by simp
    qed
    have cc_h1: "\<forall>i < length cvs. assumptions (cvs ! i)
                  \<subseteq> {} \<union> (\<Union>q \<in> set (take i cvs). set (steps q))"
    proof (intro allI impI)
      fix i assume "i < length cvs"
      hence ilt: "i < m - 1" using cvs_len by simp
      have nthi: "cvs ! i = DD i" unfolding cvs_def using ilt by simp
      have "set (take i cvs) = DD ` {0..<i}" using cvs_take ilt by simp
      hence un: "(\<Union>q \<in> set (take i cvs). set (steps q))
                  = (\<Union>k \<in> {0..<i}. set (steps (DD k)))" by auto
      have "i < m" using ilt by simp
      hence "assumptions (DD i) \<subseteq> (\<Union>k \<in> {0..<i}. set (steps (DD k)))"
        using asm_chain by simp
      thus "assumptions (cvs ! i) \<subseteq> {} \<union> (\<Union>q \<in> set (take i cvs). set (steps q))"
        using nthi un by simp
    qed
    have cc_h2: "assumptions base \<subseteq> {} \<union> (\<Union>q \<in> set cvs. set (steps q))"
    proof -
      have un: "(\<Union>q \<in> set cvs. set (steps q))
                 = (\<Union>k \<in> {0..<(m - 1)}. set (steps (DD k)))"
        using cvs_set by auto
      have "m - 1 < m" using m1 by simp
      hence "assumptions (DD (m - 1)) \<subseteq> (\<Union>k \<in> {0..<(m - 1)}. set (steps (DD k)))"
        using asm_chain by simp
      thus ?thesis unfolding base_def using un by simp
    qed
    have chain: "valid_proof F G \<and> assumptions G \<subseteq> {}
          \<and> frege_proof.thesis G = frege_proof.thesis base
          \<and> steps G = concat (map steps cvs) @ steps base"
      unfolding G_def
      using chain_combine[OF vbase, where ps = cvs and outer = "{}"] cc_v cc_h1 cc_h2
      by blast
    have Gvalid: "valid_proof F G" using chain by blast
    have Gasm: "assumptions G = {}" using chain by blast
    have Gsteps: "steps G = concat (map steps cvs) @ steps base" using chain by blast
    have Gthesis: "frege_proof.thesis G = spira_trans (thesis pr)"
    proof -
      have "frege_proof.thesis G = frege_proof.thesis base" using chain by blast
      also have "\<dots> = frege_proof.thesis (DD (m - 1))" unfolding base_def by simp
      also have "\<dots> = spira_trans (steps pr ! (m - 1))"
        using thesis_DD m1 by simp
      also have "\<dots> = spira_trans (thesis pr)" using stepm1 by simp
      finally show ?thesis .
    qed
    have Gne: "steps G \<noteq> []" using Gvalid unfolding valid_proof_def by simp
    have Gthesis_last: "frege_proof.thesis G = last (steps G)"
      using Gvalid unfolding valid_proof_def by simp
    \<comment> \<open>Convert t(thesis pr) back to thesis pr.\<close>
    have fcthesis: "\<exists>cv. valid_proof F cv \<and> assumptions cv \<subseteq> {spira_trans (thesis pr)}
          \<and> frege_proof.thesis cv = thesis pr
          \<and> length (steps cv) \<le> poly Bfc (len_formula (thesis pr))
          \<and> (\<forall>s \<in> set (steps cv). len_formula s \<le> poly Bfc (len_formula (thesis pr)))
          \<and> (\<forall>s \<in> set (steps cv). real (depth_formula s)
                \<le> real (depth_formula (thesis pr))
                  + cfc * log 2 (real (len_formula (thesis pr)) + 1))
          \<and> (\<forall>s \<in> set (steps cv). formula_well_formed (alphabet F) s)"
      using FC[THEN spec, of "thesis pr"] wfthesis by (rule mp)
    define cvf where "cvf =
        (SOME cv. valid_proof F cv \<and> assumptions cv \<subseteq> {spira_trans (thesis pr)}
         \<and> frege_proof.thesis cv = thesis pr
         \<and> length (steps cv) \<le> poly Bfc (len_formula (thesis pr))
         \<and> (\<forall>s \<in> set (steps cv). len_formula s \<le> poly Bfc (len_formula (thesis pr)))
         \<and> (\<forall>s \<in> set (steps cv). real (depth_formula s)
               \<le> real (depth_formula (thesis pr))
                 + cfc * log 2 (real (len_formula (thesis pr)) + 1))
         \<and> (\<forall>s \<in> set (steps cv). formula_well_formed (alphabet F) s))"
    have cvfC: "valid_proof F cvf \<and> assumptions cvf \<subseteq> {spira_trans (thesis pr)}
         \<and> frege_proof.thesis cvf = thesis pr
         \<and> length (steps cvf) \<le> poly Bfc (len_formula (thesis pr))
         \<and> (\<forall>s \<in> set (steps cvf). len_formula s \<le> poly Bfc (len_formula (thesis pr)))
         \<and> (\<forall>s \<in> set (steps cvf). real (depth_formula s)
               \<le> real (depth_formula (thesis pr))
                 + cfc * log 2 (real (len_formula (thesis pr)) + 1))
         \<and> (\<forall>s \<in> set (steps cvf). formula_well_formed (alphabet F) s)"
      unfolding cvf_def by (rule someI_ex[OF fcthesis])
    note cvf = cvfC[THEN conjunct1]
               cvfC[THEN conjunct2, THEN conjunct1]
               cvfC[THEN conjunct2, THEN conjunct2, THEN conjunct1]
               cvfC[THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
               cvfC[THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
               cvfC[THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
               cvfC[THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2]
    define pbal where "pbal = combine_proofs G cvf"
    have pbal_valid: "valid_proof F pbal"
      unfolding pbal_def
      by (rule frege_system.combining_valid_proofs[OF fs_F,
            OF conjI[OF Gvalid cvf(1)] refl])
    have pbal_thesis: "frege_proof.thesis pbal = thesis pr"
      unfolding pbal_def using cvf(3) by simp
    have pbal_steps: "steps pbal = steps G @ steps cvf" unfolding pbal_def by simp
    have G_wf: "\<forall>s \<in> set (steps G). formula_well_formed (alphabet F) s"
    proof
      fix s assume "s \<in> set (steps G)"
      hence "s \<in> set (concat (map steps cvs)) \<or> s \<in> set (steps base)"
        using Gsteps by auto
      thus "formula_well_formed (alphabet F) s"
      proof
        assume "s \<in> set (concat (map steps cvs))"
        then obtain p where pin: "p \<in> set cvs" and sp: "s \<in> set (steps p)" by auto
        obtain k where kk: "k \<in> {0..<(m - 1)}" and pk: "p = DD k" using cvs_set pin by auto
        have "k < m" using kk by auto
        thus ?thesis using wf_DD sp pk by blast
      next
        assume "s \<in> set (steps base)"
        thus ?thesis using wf_DD[of "m - 1"] m1 unfolding base_def by simp
      qed
    qed
    have pbal_wf: "\<forall>line \<in> set (steps pbal). formula_well_formed (alphabet F) line"
      using pbal_steps G_wf cvf(7) by auto
    have pbal_asm: "assumptions pbal = {}"
    proof -
      have xin: "spira_trans (thesis pr) \<in> set (steps G)"
        using Gthesis Gthesis_last last_in_set[OF Gne] by simp
      have "assumptions cvf \<subseteq> set (steps G)"
      proof
        fix y assume "y \<in> assumptions cvf"
        hence "y = spira_trans (thesis pr)" using cvf(2) by auto
        thus "y \<in> set (steps G)" using xin by simp
      qed
      hence diff: "assumptions cvf - set (steps G) = {}" by blast
      have "assumptions pbal = assumptions G \<union> (assumptions cvf - set (steps G))"
        unfolding pbal_def by simp
      thus ?thesis using Gasm diff by simp
    qed
    \<comment> \<open>Every line of G comes from some sub-derivation; cvf lines are bounded too.\<close>
    have Gline: "\<And>line. line \<in> set (steps G) \<Longrightarrow> \<exists>k < m. line \<in> set (steps (DD k))"
    proof -
      fix line assume "line \<in> set (steps G)"
      hence "line \<in> set (concat (map steps cvs)) \<or> line \<in> set (steps base)"
        using Gsteps by auto
      thus "\<exists>k < m. line \<in> set (steps (DD k))"
      proof
        assume "line \<in> set (concat (map steps cvs))"
        then obtain q where qin: "q \<in> set cvs" and lq: "line \<in> set (steps q)" by auto
        obtain k where "k \<in> {0..<(m - 1)}" and qk: "q = DD k" using cvs_set qin by auto
        hence "k < m" by auto
        thus ?thesis using lq qk by auto
      next
        assume "line \<in> set (steps base)"
        hence "line \<in> set (steps (DD (m - 1)))" unfolding base_def by simp
        moreover have "m - 1 < m" using m1 by simp
        ultimately show ?thesis by auto
      qed
    qed
    \<comment> \<open>Size bound.\<close>
    let ?P1 = "poly Bpl S" and ?P2 = "poly Bfc S"
    have boundfin_eval: "poly boundfin S = (S * ?P1 + ?P2) * (?P1 + ?P2)"
      unfolding boundfin_def by (simp add: poly_monom)
    have line_len: "\<forall>line \<in> set (steps pbal). len_formula line \<le> ?P1 + ?P2"
    proof
      fix line assume "line \<in> set (steps pbal)"
      hence "line \<in> set (steps G) \<or> line \<in> set (steps cvf)"
        using pbal_steps by auto
      thus "len_formula line \<le> ?P1 + ?P2"
      proof
        assume "line \<in> set (steps G)"
        then obtain k where km: "k < m" and "line \<in> set (steps (DD k))"
          using Gline by blast
        hence "len_formula line \<le> ?P1" using DD km by simp
        thus ?thesis by simp
      next
        assume lc: "line \<in> set (steps cvf)"
        have "len_formula line \<le> poly Bfc (len_formula (thesis pr))"
          using bspec[OF cvf(5) lc] .
        also have "\<dots> \<le> ?P2" using poly_nat_mono[OF lenthesis_le_S] .
        finally show ?thesis by simp
      qed
    qed
    have count: "length (steps pbal) \<le> S * ?P1 + ?P2"
    proof -
      have "length (concat (map steps cvs)) = sum_list (map length (map steps cvs))"
        by (simp add: length_concat)
      also have "\<dots> \<le> length (map steps cvs) * ?P1"
      proof (rule sum_list_map_le)
        show "\<forall>x \<in> set (map steps cvs). length x \<le> ?P1"
        proof
          fix x assume "x \<in> set (map steps cvs)"
          then obtain q where qin: "q \<in> set cvs" and xq: "x = steps q" by auto
          obtain k where "k \<in> {0..<(m - 1)}" and qk: "q = DD k" using cvs_set qin by auto
          hence "k < m" by auto
          thus "length x \<le> ?P1" using DD xq qk by simp
        qed
      qed
      also have "\<dots> = (m - 1) * ?P1" using cvs_len by simp
      finally have c1: "length (concat (map steps cvs)) \<le> (m - 1) * ?P1" .
      have c2: "length (steps base) \<le> ?P1"
        unfolding base_def using DD m1 by simp
      have "length (steps G) = length (concat (map steps cvs)) + length (steps base)"
        using Gsteps by simp
      also have "\<dots> \<le> (m - 1) * ?P1 + ?P1" using c1 c2 by linarith
      also have "\<dots> = m * ?P1" using m1 by (simp add: mult_eq_if)
      also have "\<dots> \<le> S * ?P1" using mS by (rule mult_le_mono1)
      finally have cG: "length (steps G) \<le> S * ?P1" .
      have cC: "length (steps cvf) \<le> ?P2"
      proof -
        have "length (steps cvf) \<le> poly Bfc (len_formula (thesis pr))" using cvf(4) .
        also have "\<dots> \<le> ?P2" using poly_nat_mono[OF lenthesis_le_S] .
        finally show ?thesis .
      qed
      have "length (steps pbal) = length (steps G) + length (steps cvf)"
        using pbal_steps by simp
      also have "\<dots> \<le> S * ?P1 + ?P2" using cG cC by linarith
      finally show ?thesis .
    qed
    have pbal_size: "len_proof pbal \<le> poly boundfin S"
    proof -
      have "len_proof pbal = sum_list (map len_formula (steps pbal))" by simp
      also have "\<dots> \<le> length (steps pbal) * (?P1 + ?P2)"
        using line_len by (rule sum_list_map_le)
      also have "\<dots> \<le> (S * ?P1 + ?P2) * (?P1 + ?P2)"
        using count by (rule mult_le_mono1)
      also have "\<dots> = poly boundfin S" using boundfin_eval by simp
      finally show ?thesis .
    qed
    \<comment> \<open>Depth bound.\<close>
    have logS0: "0 \<le> log 2 (real S + 1)"
    proof -
      have "log 2 (1::real) \<le> log 2 (real S + 1)" by (intro log_mono) auto
      thus ?thesis by simp
    qed
    have line_dep: "\<forall>line \<in> set (steps pbal). real (depth_formula line)
          \<le> real (depth_formula (thesis pr)) + cfin * log 2 (real S + 1)"
    proof
      fix line assume "line \<in> set (steps pbal)"
      hence "line \<in> set (steps G) \<or> line \<in> set (steps cvf)"
        using pbal_steps by auto
      thus "real (depth_formula line)
            \<le> real (depth_formula (thesis pr)) + cfin * log 2 (real S + 1)"
      proof
        assume "line \<in> set (steps G)"
        then obtain k where km: "k < m" and "line \<in> set (steps (DD k))"
          using Gline by blast
        hence "real (depth_formula line) \<le> ccpl * log 2 (real S + 1)" using DD km by simp
        also have "\<dots> \<le> cfin * log 2 (real S + 1)"
          using mult_right_mono[of ccpl cfin "log 2 (real S + 1)"] logS0
          unfolding cfin_def by simp
        also have "\<dots> \<le> real (depth_formula (thesis pr)) + cfin * log 2 (real S + 1)"
          by simp
        finally show ?thesis .
      next
        assume lc: "line \<in> set (steps cvf)"
        have "real (depth_formula line)
               \<le> real (depth_formula (thesis pr))
                 + cfc * log 2 (real (len_formula (thesis pr)) + 1)"
          using bspec[OF cvf(6) lc] .
        also have "\<dots> \<le> real (depth_formula (thesis pr)) + cfin * log 2 (real S + 1)"
        proof -
          have "cfc * log 2 (real (len_formula (thesis pr)) + 1)
                \<le> cfc * log 2 (real S + 1)"
          proof (rule mult_left_mono)
            have "real (len_formula (thesis pr)) + 1 \<le> real S + 1"
              using lenthesis_le_S by simp
            moreover have "0 < real (len_formula (thesis pr)) + 1"
              by (simp add: add_nonneg_pos)
            ultimately show "log 2 (real (len_formula (thesis pr)) + 1)
                             \<le> log 2 (real S + 1)" by (intro log_mono) auto
            show "0 \<le> cfc" using cfc0 .
          qed
          also have "\<dots> \<le> cfin * log 2 (real S + 1)"
            using mult_right_mono[of cfc cfin "log 2 (real S + 1)"] logS0
            unfolding cfin_def by simp
          finally show ?thesis by simp
        qed
        finally show ?thesis .
      qed
    qed
    \<comment> \<open>Assemble.\<close>
    have pbalBC: "valid_proof F pbal \<and> assumptions pbal = {} \<and> thesis pbal = thesis pr
          \<and> len_proof pbal \<le> poly boundfin (len_proof pr)
          \<and> (\<forall>line \<in> set (steps pbal). real (depth_formula line)
               \<le> real (depth_formula (thesis pr))
                 + cfin * log 2 (real (len_proof pr) + 1))
          \<and> (\<forall>line \<in> set (steps pbal). formula_well_formed (alphabet F) line)"
      using pbal_valid pbal_asm pbal_thesis pbal_size line_dep pbal_wf
      unfolding S_def by simp
    show "\<exists>pr'. valid_proof F pr' \<and> assumptions pr' = {} \<and> thesis pr' = thesis pr
            \<and> len_proof pr' \<le> poly boundfin (len_proof pr)
            \<and> (\<forall>line \<in> set (steps pr'). real (depth_formula line)
                 \<le> real (depth_formula (thesis pr))
                   + cfin * log 2 (real (len_proof pr) + 1))
            \<and> (\<forall>line \<in> set (steps pr'). formula_well_formed (alphabet F) line)"
      using pbalBC by (rule exI)
  qed
qed


end
end
