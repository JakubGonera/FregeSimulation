theory Section6
  imports FregeCompleteness Section5 "HOL-Types_To_Sets.Types_To_Sets"
begin

section \<open>Pushing the balancing translation through connectives (Filmus section 6)\<close>

subsection \<open>Setting: connective closure and slot-fixing\<close>

(* as in a closure of all connectives *)
definition conn_closed :: "'c alphabet \<Rightarrow> bool" where
  "conn_closed alph \<longleftrightarrow>
    (\<forall>c i b. arity alph c = 0 \<or> (i < arity alph c \<longrightarrow>
       (\<exists>c'. arity alph c' = arity alph c - 1 \<and>
             (\<forall>args. length args = arity alph c - 1 \<longrightarrow>
                conn_evals alph c' args
                  = conn_evals alph c (take i args @ b # drop i args)))))"

fun rename_conn :: "('c1 \<Rightarrow> 'c2) \<Rightarrow> 'c1 formula \<Rightarrow> 'c2 formula" where
  "rename_conn phi (Atom a) = Atom a"
| "rename_conn phi (Conn c fs) = Conn (phi c) (map (rename_conn phi) fs)"

lemma rename_conn_len [simp]:
  "len_formula (rename_conn phi f) = len_formula f"
proof (induction f)
  case (Atom a)
  show ?case by simp
next
  case (Conn c fs)
  have m: "map len_formula (map (rename_conn phi) fs) = map len_formula fs"
    using Conn.IH by simp
  show ?case by (simp only: rename_conn.simps len_formula.simps m)
qed

lemma rename_conn_equiv:
  assumes "\<And>c. conns_equiv c a1 (phi c) a2"
  shows "formulas_equiv f a1 (rename_conn phi f) a2"
proof (induction f)
  case (Atom a)
  show ?case by (simp add: formulas_equiv_def)
next
  case (Conn c fs)
  from conjunct2[OF assms[of c, unfolded conns_equiv_def]]
  have ce: "\<And>val fs1 fs2. length fs1 = length fs2 \<Longrightarrow>
              (\<forall>i<length fs1. formulas_equiv (fs1 ! i) a1 (fs2 ! i) a2) \<Longrightarrow>
              eval a1 val (Conn c fs1) = eval a2 val (Conn (phi c) fs2)"
    by blast
  show ?case
    unfolding formulas_equiv_def
  proof (intro allI)
    fix val
    have ptw: "\<forall>i<length fs. formulas_equiv (fs ! i) a1 (map (rename_conn phi) fs ! i) a2"
    proof (intro allI impI)
      fix i assume i: "i < length fs"
      have "formulas_equiv (fs ! i) a1 (rename_conn phi (fs ! i)) a2"
        using Conn.IH[OF nth_mem[OF i]] .
      then show "formulas_equiv (fs ! i) a1 (map (rename_conn phi) fs ! i) a2"
        using i by simp
    qed
    have "eval a1 val (Conn c fs) = eval a2 val (Conn (phi c) (map (rename_conn phi) fs))"
      by (rule ce[OF _ ptw]) simp
    then show "eval a1 val (Conn c fs) = eval a2 val (rename_conn phi (Conn c fs))"
      by simp
  qed
qed

definition rename_rule :: "('c1 \<Rightarrow> 'c2) \<Rightarrow> 'c1 rule \<Rightarrow> 'c2 rule" where
  "rename_rule phi r = \<lparr> prems = map (rename_conn phi) (prems r),
                         concl = rename_conn phi (concl r) \<rparr>"

lemma sub_rename_commute:
  "sub_formula (\<lambda>a. rename_conn phi (sub a)) (rename_conn phi t)
   = rename_conn phi (sub_formula sub t)"
proof (induction t)
  case (Atom a)
  show ?case by simp
next
  case (Conn c ts)
  have m: "map (sub_formula (\<lambda>a. rename_conn phi (sub a)) \<circ> rename_conn phi) ts
           = map (rename_conn phi \<circ> sub_formula sub) ts"
    by (rule map_cong[OF refl]) (simp add: comp_def Conn.IH)
  show ?case
    by (simp only: rename_conn.simps sub_formula.simps map_map m)
qed

lemma derived_rename:
  assumes "derived rs fs f"
  shows "derived (rename_rule phi ` rs) (map (rename_conn phi) fs) (rename_conn phi f)"
proof -
  from assms obtain r sub where
    r_in: "r \<in> rs"
    and concl_eq: "concl (sub_rule sub r) = f"
    and prems_in: "\<forall>p \<in> set (prems (sub_rule sub r)). \<exists>q \<in> set fs. p = q"
    unfolding derived_def by auto
  let ?sub' = "\<lambda>a. rename_conn phi (sub a)"
  have r'_in: "rename_rule phi r \<in> rename_rule phi ` rs" using r_in by simp
  have concl': "concl (sub_rule ?sub' (rename_rule phi r)) = rename_conn phi f"
  proof -
    have "concl (sub_rule ?sub' (rename_rule phi r))
          = sub_formula ?sub' (rename_conn phi (concl r))"
      by (simp add: rename_rule_def)
    also have "\<dots> = rename_conn phi (sub_formula sub (concl r))"
      by (rule sub_rename_commute)
    also have "\<dots> = rename_conn phi f" using concl_eq by simp
    finally show ?thesis .
  qed
  have prems': "\<forall>p \<in> set (prems (sub_rule ?sub' (rename_rule phi r))).
                   \<exists>q \<in> set (map (rename_conn phi) fs). p = q"
  proof
    fix p assume "p \<in> set (prems (sub_rule ?sub' (rename_rule phi r)))"
    then have "p \<in> set (map (sub_formula ?sub') (map (rename_conn phi) (prems r)))"
      by (simp add: rename_rule_def)
    then obtain t where t_in: "t \<in> set (prems r)"
      and p_eq: "p = sub_formula ?sub' (rename_conn phi t)" by auto
    have p_eq2: "p = rename_conn phi (sub_formula sub t)"
      using p_eq by (simp add: sub_rename_commute)
    have "sub_formula sub t \<in> set (prems (sub_rule sub r))" using t_in by simp
    then obtain q where "q \<in> set fs" and "sub_formula sub t = q" using prems_in by blast
    thus "\<exists>q \<in> set (map (rename_conn phi) fs). p = q" using p_eq2 by auto
  qed
  show ?thesis
    unfolding derived_def
  proof (intro bexI[where x = "rename_rule phi r"] exI[where x = "?sub'"])
    show "let sub_r = sub_rule ?sub' (rename_rule phi r)
          in concl sub_r = rename_conn phi f \<and>
             (\<forall>f1\<in>set (prems sub_r). \<exists>f2\<in>set (map (rename_conn phi) fs). f1 = f2)"
      unfolding Let_def using concl' prems' by blast
  next
    show "rename_rule phi r \<in> rename_rule phi ` rs" by (rule r'_in)
  qed
qed

lemma derived_mono_rules:
  assumes "rs \<subseteq> rs'" and "derived rs fs f"
  shows "derived rs' fs f"
proof -
  from assms(2) obtain r sub where
    "r \<in> rs" "concl (sub_rule sub r) = f"
    "\<forall>p\<in>set (prems (sub_rule sub r)). \<exists>q\<in>set fs. p = q"
    unfolding derived_def by auto
  thus ?thesis using assms(1) unfolding derived_def by auto
qed

lemma valid_proof_mono_rules:
  assumes "rules F \<subseteq> rules G" and "valid_proof F pr"
  shows "valid_proof G pr"
proof -
  have "\<forall>i<length (steps pr). steps pr ! i \<in> assumptions pr \<or>
          derived (rules G) (take i (steps pr)) (steps pr ! i)"
  proof (intro allI impI)
    fix i assume "i < length (steps pr)"
    with assms(2) have "steps pr ! i \<in> assumptions pr \<or>
            derived (rules F) (take i (steps pr)) (steps pr ! i)"
      unfolding valid_proof_def by simp
    thus "steps pr ! i \<in> assumptions pr \<or> derived (rules G) (take i (steps pr)) (steps pr ! i)"
      using derived_mono_rules[OF assms(1)] by blast
  qed
  thus ?thesis using assms(2) unfolding valid_proof_def by simp
qed

lemma rename_conn_well_formed:
  assumes "\<And>c. arity a2 (phi c) = arity a1 c"
    and "formula_well_formed a1 g"
  shows "formula_well_formed a2 (rename_conn phi g)"
  using assms(2)
proof (induction g)
  case (Atom a)
  show ?case by simp
next
  case (Conn c gs)
  have len: "length gs = arity a1 c" and all: "\<forall>g'\<in>set gs. formula_well_formed a1 g'"
    using Conn.prems by auto
  have "formula_well_formed a2 (rename_conn phi g')" if "g' \<in> set gs" for g'
    using Conn.IH that all by blast
  thus ?case using len assms(1)[of c] by auto
qed

text \<open>Every functionally complete finite connective alphabet (with the boolean
  constants) carries a complete sound Frege system.  This is
  \<open>frege_system_over_complete_alphabet\<close>, proven in theory \<open>FregeCompleteness\<close>
  by bridging the completeness of the AFP Hilbert calculus.\<close>




locale closure_of =
  fixes F1 :: "'c1 frege"
    and F2 :: "'c2 frege"
    and phi :: "'c1 \<Rightarrow> 'c2"
  assumes frege_system_F1: "frege_system F1"
    and frege_system_F2: "frege_system F2"
    and conn_closed_F2: "conn_closed (alphabet F2)"
    and conns_equiv_phi: "\<And>c. conns_equiv c (alphabet F1) (phi c) (alphabet F2)"
    and rule_simulation:
      "\<And>fs f. derived (rules F1) fs f
                \<Longrightarrow> derived (rules F2) (map (rename_conn phi) fs) (rename_conn phi f)"
begin

lemma extended_frege_translation_triv:
  assumes "valid_proof F1 pr1"
  shows "\<exists> pr2. equiv_proofs pr1 F1 pr2 F2 \<and> len_proof pr1 = len_proof pr2"
proof -
  define pr2 where
    "pr2 = \<lparr> assumptions = rename_conn phi ` assumptions pr1,
             thesis = rename_conn phi (thesis pr1),
             steps = map (rename_conn phi) (steps pr1) \<rparr>"
  have steps2: "steps pr2 = map (rename_conn phi) (steps pr1)" by (simp add: pr2_def)
  have assm2: "assumptions pr2 = rename_conn phi ` assumptions pr1" by (simp add: pr2_def)
  have th2: "thesis pr2 = rename_conn phi (thesis pr1)" by (simp add: pr2_def)

  have vp1: "valid_proof F1 pr1" by (rule assms)
  have ne1: "steps pr1 \<noteq> []" using vp1 unfolding valid_proof_def by simp
  have thlast: "thesis pr1 = last (steps pr1)" using vp1 unfolding valid_proof_def by simp

  note equiv_f = rename_conn_equiv[OF conns_equiv_phi]

  have len_steps: "length (steps pr2) = length (steps pr1)" by (simp add: steps2)

  have vp2: "valid_proof F2 pr2"
    unfolding valid_proof_def
  proof (intro conjI)
    show "thesis pr2 = last (steps pr2)"
    proof -
      have "last (steps pr2) = rename_conn phi (last (steps pr1))"
        using ne1 by (simp add: steps2 last_map)
      thus ?thesis using th2 thlast by simp
    qed
    show "steps pr2 \<noteq> []" using steps2 ne1 by simp
    show "\<forall>i<length (steps pr2). steps pr2 ! i \<in> assumptions pr2 \<or>
            derived (rules F2) (take i (steps pr2)) (steps pr2 ! i)"
    proof (intro allI impI)
      fix i assume i: "i < length (steps pr2)"
      hence i1: "i < length (steps pr1)" by (simp add: len_steps)
      have step_i: "steps pr2 ! i = rename_conn phi (steps pr1 ! i)"
        using i1 by (simp add: steps2)
      from vp1 i1 have
        "steps pr1 ! i \<in> assumptions pr1 \<or>
           derived (rules F1) (take i (steps pr1)) (steps pr1 ! i)"
        unfolding valid_proof_def by simp
      thus "steps pr2 ! i \<in> assumptions pr2 \<or>
              derived (rules F2) (take i (steps pr2)) (steps pr2 ! i)"
      proof
        assume "steps pr1 ! i \<in> assumptions pr1"
        hence "rename_conn phi (steps pr1 ! i) \<in> assumptions pr2"
          using assm2 by blast
        thus ?thesis using step_i by simp
      next
        assume "derived (rules F1) (take i (steps pr1)) (steps pr1 ! i)"
        from rule_simulation[OF this]
        have d: "derived (rules F2)
                   (map (rename_conn phi) (take i (steps pr1))) (rename_conn phi (steps pr1 ! i))" .
        have "map (rename_conn phi) (take i (steps pr1)) = take i (steps pr2)"
          by (simp add: steps2 take_map)
        with d have "derived (rules F2) (take i (steps pr2)) (rename_conn phi (steps pr1 ! i))"
          by simp
        thus ?thesis using step_i by simp
      qed
    qed
  qed

  have efs: "equiv_formula_sets (assumptions pr1) (alphabet F1) (assumptions pr2) (alphabet F2)"
    unfolding equiv_formula_sets_def
  proof (intro conjI ballI)
    fix f1 assume "f1 \<in> assumptions pr1"
    hence "rename_conn phi f1 \<in> assumptions pr2" using assm2 by blast
    thus "\<exists>f2\<in>assumptions pr2. formulas_equiv f1 (alphabet F1) f2 (alphabet F2)"
      using equiv_f[of f1] by blast
  next
    fix f2 assume "f2 \<in> assumptions pr2"
    then obtain f1 where f1: "f1 \<in> assumptions pr1" and f2eq: "f2 = rename_conn phi f1"
      using assm2 by blast
    have "formulas_equiv f2 (alphabet F2) f1 (alphabet F1)"
      using equiv_f[of f1] f2eq unfolding formulas_equiv_def by auto
    thus "\<exists>f1\<in>assumptions pr1. formulas_equiv f2 (alphabet F2) f1 (alphabet F1)"
      using f1 by blast
  qed

  have th_equiv: "formulas_equiv (thesis pr1) (alphabet F1) (thesis pr2) (alphabet F2)"
    using equiv_f[of "thesis pr1"] by (simp add: th2)

  have len_eq: "len_proof pr1 = len_proof pr2"
    by (simp add: steps2 comp_def)

  have "equiv_proofs pr1 F1 pr2 F2"
    unfolding equiv_proofs_def
    using frege_system_F1 vp1 frege_system_F2 vp2 efs th_equiv by blast
  thus ?thesis using len_eq by blast
qed

end

subsection \<open>Existence of the closure (via Types-To-Sets)\<close>

text \<open>Up to semantics a connective is determined by its arity together with its
  truth function, so the connectives needed to close an alphabet under fixing one
  argument to a constant form a subset of the ambient type
  nat * (bool list => bool).  This carrier is finite, and the Types-To-Sets
  local-typedef rule then provides a finite connective type in bijection with it.\<close>

inductive_set closure_carrier :: "'c alphabet \<Rightarrow> (nat \<times> (bool list \<Rightarrow> bool)) set"
  for a1 :: "'c alphabet" where
  base: "(arity a1 c, conn_evals a1 c) \<in> closure_carrier a1"
| fix_slot: "\<lbrakk> (Suc n, g) \<in> closure_carrier a1; i \<le> n \<rbrakk>
               \<Longrightarrow> (n, \<lambda>args. g (take i args @ b # drop i args)) \<in> closure_carrier a1"

fun fix_one :: "(nat \<times> (bool list \<Rightarrow> bool)) \<Rightarrow> (nat \<times> bool) \<Rightarrow> (nat \<times> (bool list \<Rightarrow> bool))" where
  "fix_one (n, g) (i, b) = (n - 1, \<lambda>args. g (take i args @ b # drop i args))"

lemma fst_foldl_fix_one:
  "fst (foldl fix_one p ops) = fst p - length ops"
proof (induction ops arbitrary: p)
  case Nil
  thus ?case by simp
next
  case (Cons op ops)
  obtain n g where p: "p = (n, g)" by (cases p)
  obtain i b where op: "op = (i, b)" by (cases op)
  have "fst (foldl fix_one p (op # ops)) = fst (foldl fix_one (fix_one p op) ops)" by simp
  also have "\<dots> = fst (fix_one p op) - length ops" by (rule Cons.IH)
  also have "fst (fix_one p op) = fst p - 1" using p op by simp
  finally show ?case by simp
qed

lemma closure_carrier_finite:
  assumes "frege_system F1"
  shows "finite (closure_carrier (alphabet F1))"
proof -
  note finU = frege_system.finite_alphabet[OF assms]
  define a where "a = alphabet F1"
  define M where "M = Max (arity a ` UNIV)"
  have finA: "finite (arity a ` UNIV)" using finU by (rule finite_imageI)
  have arity_le: "arity a c \<le> M" for c
    unfolding M_def by (rule Max_ge[OF finA]) simp
  define base_conn where "base_conn = (\<lambda>c. (arity a c, conn_evals a c))"
  define G where
    "G = (\<lambda>(c, ops). foldl fix_one (base_conn c) ops) `
           (UNIV \<times> {ops. set ops \<subseteq> {0..M} \<times> UNIV \<and> length ops \<le> M})"
  have finG: "finite G"
    unfolding G_def
    by (intro finite_imageI finite_cartesian_product[OF finU] finite_lists_length_le) simp
  have sub: "closure_carrier a \<subseteq> G"
  proof (rule subsetI)
    fix x assume xin: "x \<in> closure_carrier a"
    obtain n0 g0 where x: "x = (n0, g0)" by (cases x)
    with xin have "(n0, g0) \<in> closure_carrier a" by simp
    then have "(n0, g0) \<in> G"
    proof (induction rule: closure_carrier.induct)
      case (base c)
      have "(arity a c, conn_evals a c) = (\<lambda>(c, ops). foldl fix_one (base_conn c) ops) (c, [])"
        by (simp add: base_conn_def)
      moreover have "(c, []) \<in> UNIV \<times> {ops. set ops \<subseteq> {0..M} \<times> UNIV \<and> length ops \<le> M}"
        by simp
      ultimately show ?case unfolding G_def by (rule image_eqI)
    next
      case (fix_slot n g i b)
      from fix_slot.IH obtain c ops where
        eq: "(Suc n, g) = foldl fix_one (base_conn c) ops"
        and setM: "set ops \<subseteq> {0..M} \<times> UNIV"
        and lenM: "length ops \<le> M"
        unfolding G_def by auto
      have fst_eq: "arity a c - length ops = Suc n"
      proof -
        have "arity a c - length ops = fst (base_conn c) - length ops"
          by (simp add: base_conn_def)
        also have "\<dots> = fst (foldl fix_one (base_conn c) ops)"
          by (rule fst_foldl_fix_one[symmetric])
        also have "\<dots> = fst (Suc n, g)" using eq by simp
        finally show ?thesis by simp
      qed
      have le1: "length ops \<le> arity a c"
      proof (rule ccontr)
        assume "\<not> length ops \<le> arity a c"
        hence "arity a c - length ops = 0" by simp
        with fst_eq show False by simp
      qed
      have arity_c: "arity a c = Suc n + length ops"
        using fst_eq le1 by linarith
      have iM: "i \<le> M"
        using \<open>i \<le> n\<close> arity_c arity_le[of c] by linarith
      have l1: "length ops + 1 \<le> M"
        using arity_c arity_le[of c] by linarith
      have setM': "set (ops @ [(i, b)]) \<subseteq> {0..M} \<times> UNIV"
        using setM iM by auto
      have fold_eq: "foldl fix_one (base_conn c) (ops @ [(i, b)])
                     = (n, \<lambda>args. g (take i args @ b # drop i args))"
      proof -
        have "foldl fix_one (base_conn c) (ops @ [(i, b)]) = fix_one (Suc n, g) (i, b)"
          using eq[symmetric] by simp
        also have "\<dots> = (n, \<lambda>args. g (take i args @ b # drop i args))" by simp
        finally show ?thesis .
      qed
      have "(n, \<lambda>args. g (take i args @ b # drop i args))
            = (\<lambda>(c, ops). foldl fix_one (base_conn c) ops) (c, ops @ [(i, b)])"
        using fold_eq by simp
      moreover have "(c, ops @ [(i, b)]) \<in> UNIV \<times> {ops. set ops \<subseteq> {0..M} \<times> UNIV \<and> length ops \<le> M}"
        using setM' l1 by simp
      ultimately show ?case unfolding G_def by (rule image_eqI)
    qed
    thus "x \<in> G" using x by simp
  qed
  have "finite (closure_carrier a)" using sub finG by (rule finite_subset)
  thus ?thesis by (simp add: a_def)
qed

text \<open>With the finite carrier realised as a connective type 'c2 (the
  type_definition hypothesis being discharged by the Types-To-Sets local-typedef
  rule together with closure_carrier_finite), the closed extension and a
  witnessing renaming exist.\<close>

lemma extended_frege_exists:
  fixes Rep :: "'c2 \<Rightarrow> (nat \<times> (bool list \<Rightarrow> bool))"
    and Abs :: "(nat \<times> (bool list \<Rightarrow> bool)) \<Rightarrow> 'c2"
  assumes "frege_system F1"
    and td: "type_definition Rep Abs (closure_carrier (alphabet F1))"
  shows "\<exists> (F2 :: 'c2 frege) phi. closure_of F1 F2 phi"
proof -
  interpret td: type_definition Rep Abs "closure_carrier (alphabet F1)" by (rule td)
  define phi where "phi = (\<lambda>c. Abs (arity (alphabet F1) c, conn_evals (alphabet F1) c))"
  define alph2 where "alph2 = \<lparr> arity = fst \<circ> Rep, conn_evals = snd \<circ> Rep \<rparr>"
  have arity2: "arity alph2 x = fst (Rep x)" for x by (simp add: alph2_def)
  have eval2: "conn_evals alph2 x = snd (Rep x)" for x by (simp add: alph2_def)
  have rep_in: "Rep x \<in> closure_carrier (alphabet F1)" for x by (rule td.Rep)
  have rep_phi: "Rep (phi c) = (arity (alphabet F1) c, conn_evals (alphabet F1) c)" for c
    unfolding phi_def by (rule td.Abs_inverse) (rule closure_carrier.base)
  have arity_phi: "arity alph2 (phi c) = arity (alphabet F1) c" for c
    by (simp add: arity2 rep_phi)

  \<comment> \<open>@{term phi} maps each connective to a semantically equal closure connective\<close>
  have cev: "conns_equiv c (alphabet F1) (phi c) alph2" for c
  proof -
    have ar: "arity (alphabet F1) c = arity alph2 (phi c)" by (simp add: arity_phi)
    have ev: "conn_evals alph2 (phi c) = conn_evals (alphabet F1) c"
      by (simp add: eval2 rep_phi)
    have bigeq: "\<forall>val fs1 fs2. length fs1 = length fs2 \<longrightarrow>
            (\<forall>i<length fs1. formulas_equiv (fs1 ! i) (alphabet F1) (fs2 ! i) alph2) \<longrightarrow>
            eval (alphabet F1) val (Conn c fs1) = eval alph2 val (Conn (phi c) fs2)"
    proof (intro allI impI)
      fix val fs1 fs2
      assume len: "length fs1 = length fs2"
        and ptw: "\<forall>i<length fs1. formulas_equiv (fs1 ! i) (alphabet F1) (fs2 ! i) alph2"
      have "map (eval (alphabet F1) val) fs1 = map (eval alph2 val) fs2"
      proof (rule nth_equalityI)
        show "length (map (eval (alphabet F1) val) fs1) = length (map (eval alph2 val) fs2)"
          using len by simp
        fix i assume "i < length (map (eval (alphabet F1) val) fs1)"
        hence i: "i < length fs1" by simp
        hence "formulas_equiv (fs1 ! i) (alphabet F1) (fs2 ! i) alph2" using ptw by simp
        hence "eval (alphabet F1) val (fs1 ! i) = eval alph2 val (fs2 ! i)"
          unfolding formulas_equiv_def by simp
        thus "map (eval (alphabet F1) val) fs1 ! i = map (eval alph2 val) fs2 ! i"
          using i len by simp
      qed
      thus "eval (alphabet F1) val (Conn c fs1) = eval alph2 val (Conn (phi c) fs2)"
        by (simp add: ev)
    qed
    show ?thesis unfolding conns_equiv_def using ar bigeq by blast
  qed
  have eval_rename: "eval alph2 val (rename_conn phi t) = eval (alphabet F1) val t" for val t
    using rename_conn_equiv[OF cev, of t] by (simp add: formulas_equiv_def)

  \<comment> \<open>the closure alphabet is closed under fixing one argument to a constant\<close>
  have ccl: "conn_closed alph2"
    unfolding conn_closed_def
  proof (intro allI)
    fix x i b
    show "arity alph2 x = 0 \<or> (i < arity alph2 x \<longrightarrow>
            (\<exists>c'. arity alph2 c' = arity alph2 x - 1 \<and>
              (\<forall>args. length args = arity alph2 x - 1 \<longrightarrow>
                 conn_evals alph2 c' args = conn_evals alph2 x (take i args @ b # drop i args))))"
    proof (cases "arity alph2 x = 0")
      case True thus ?thesis by simp
    next
      case False
      show ?thesis
      proof (rule disjI2, rule impI)
        assume ix: "i < arity alph2 x"
        obtain n g where ng: "Rep x = (n, g)" by (cases "Rep x")
        have "n \<noteq> 0" using False ng by (simp add: arity2)
        then obtain m where "n = Suc m" using not0_implies_Suc by blast
        with ng have rx: "Rep x = (Suc m, g)" by simp
        have m_eq: "arity alph2 x = Suc m" using rx by (simp add: arity2)
        have im: "i \<le> m" using ix m_eq by simp
        let ?g' = "\<lambda>args. g (take i args @ b # drop i args)"
        have incarr: "(m, ?g') \<in> closure_carrier (alphabet F1)"
        proof -
          have "(Suc m, g) \<in> closure_carrier (alphabet F1)" using rx rep_in[of x] by simp
          thus ?thesis using im by (rule closure_carrier.fix_slot)
        qed
        have rep_c': "Rep (Abs (m, ?g')) = (m, ?g')" using incarr by (rule td.Abs_inverse)
        have "arity alph2 (Abs (m, ?g')) = arity alph2 x - 1"
          using rep_c' m_eq by (simp add: arity2)
        moreover have "\<forall>args. length args = arity alph2 x - 1 \<longrightarrow>
              conn_evals alph2 (Abs (m, ?g')) args = conn_evals alph2 x (take i args @ b # drop i args)"
          using rep_c' rx by (simp add: eval2)
        ultimately show "\<exists>c'. arity alph2 c' = arity alph2 x - 1 \<and>
              (\<forall>args. length args = arity alph2 x - 1 \<longrightarrow>
                 conn_evals alph2 c' args = conn_evals alph2 x (take i args @ b # drop i args))"
          by blast
      qed
    qed
  qed

  \<comment> \<open>alphabet-level Frege-system requirements for the closure alphabet\<close>
  have finUNIV2: "finite (UNIV :: 'c2 set)"
  proof -
    have "finite (Abs ` closure_carrier (alphabet F1))"
      using closure_carrier_finite[OF assms(1)] by simp
    thus ?thesis using td.Abs_image by simp
  qed
  have fcomp: "\<forall>f :: dm_conn formula. \<exists> f' :: 'c2 formula.
                  formula_well_formed alph2 f' \<and> formulas_equiv f dm_alphabet f' alph2"
  proof
    fix f :: "dm_conn formula"
    obtain g where g_wf: "formula_well_formed (alphabet F1) g"
      and g_eq: "formulas_equiv f dm_alphabet g (alphabet F1)"
      using frege_system.func_complete[OF assms(1)] by blast
    have "formula_well_formed alph2 (rename_conn phi g)"
      by (rule rename_conn_well_formed[OF arity_phi g_wf])
    moreover have "formulas_equiv f dm_alphabet (rename_conn phi g) alph2"
      using g_eq rename_conn_equiv[OF cev, of g] by (auto simp: formulas_equiv_def)
    ultimately show "\<exists> f' :: 'c2 formula. formula_well_formed alph2 f' \<and> formulas_equiv f dm_alphabet f' alph2"
      by blast
  qed
  have htop: "\<exists> t. arity alph2 t = 0 \<and> (\<forall> val. eval alph2 val (Conn t []) = True)"
  proof -
    obtain t0 where t0: "arity (alphabet F1) t0 = 0"
      "\<forall>val. eval (alphabet F1) val (Conn t0 []) = True"
      using frege_system.has_top[OF assms(1)] by blast
    have "arity alph2 (phi t0) = 0" using t0(1) by (simp add: arity_phi)
    moreover have "\<forall>val. eval alph2 val (Conn (phi t0) []) = True"
    proof
      fix val
      have "eval alph2 val (Conn (phi t0) []) = eval alph2 val (rename_conn phi (Conn t0 []))" by simp
      also have "\<dots> = eval (alphabet F1) val (Conn t0 [])" by (rule eval_rename)
      also have "\<dots> = True" using t0(2) by simp
      finally show "eval alph2 val (Conn (phi t0) []) = True" .
    qed
    ultimately show ?thesis by blast
  qed
  have hbot: "\<exists> b. arity alph2 b = 0 \<and> (\<forall> val. eval alph2 val (Conn b []) = False)"
  proof -
    obtain b0 where b0: "arity (alphabet F1) b0 = 0"
      "\<forall>val. eval (alphabet F1) val (Conn b0 []) = False"
      using frege_system.has_bot[OF assms(1)] by blast
    have "arity alph2 (phi b0) = 0" using b0(1) by (simp add: arity_phi)
    moreover have "\<forall>val. eval alph2 val (Conn (phi b0) []) = False"
    proof
      fix val
      have "eval alph2 val (Conn (phi b0) []) = eval alph2 val (rename_conn phi (Conn b0 []))" by simp
      also have "\<dots> = eval (alphabet F1) val (Conn b0 [])" by (rule eval_rename)
      also have "\<dots> = False" using b0(2) by simp
      finally show "eval alph2 val (Conn (phi b0) []) = False" .
    qed
    ultimately show ?thesis by blast
  qed

  \<comment> \<open>a complete Frege system over the closure alphabet exists; @{term F2} adds the
      renamed @{term F1} rules to it\<close>
  obtain Fc :: "'c2 frege" where fc: "frege_system Fc" and fc_alph: "alphabet Fc = alph2"
    using frege_system_over_complete_alphabet[OF finUNIV2 fcomp htop hbot] by blast
  define F2 where "F2 = \<lparr> rules = rules Fc \<union> rename_rule phi ` rules F1, alphabet = alph2 \<rparr>"
  have alphF2: "alphabet F2 = alph2" by (simp add: F2_def)
  have rules_sub: "rename_rule phi ` rules F1 \<subseteq> rules F2" by (auto simp: F2_def)
  have rulesFc_sub: "rules Fc \<subseteq> rules F2" by (auto simp: F2_def)

  have fsF2: "frege_system F2"
  proof (rule frege_system.intro)
    show "\<forall>r\<in>rules F2. sound_rule F2 r"
    proof
      fix r assume "r \<in> rules F2"
      hence "r \<in> rules Fc \<or> r \<in> rename_rule phi ` rules F1" by (auto simp: F2_def)
      thus "sound_rule F2 r"
      proof
        assume "r \<in> rules Fc"
        hence "sound_rule Fc r" using frege_system.sound[OF fc] by blast
        thus "sound_rule F2 r" by (simp add: sound_rule_def alphF2 fc_alph)
      next
        assume "r \<in> rename_rule phi ` rules F1"
        then obtain r0 where r0: "r0 \<in> rules F1" and r_eq: "r = rename_rule phi r0" by auto
        have "sound_rule F1 r0" using frege_system.sound[OF assms(1)] r0 by blast
        thus "sound_rule F2 r"
          using r_eq by (auto simp: sound_rule_def rename_rule_def alphF2 eval_rename)
      qed
    qed
  next
    show "\<forall>fs th. (\<forall>f\<in>fs. formula_well_formed (alphabet F2) f) \<longrightarrow>
            formula_well_formed (alphabet F2) th \<longrightarrow>
            (\<forall>val. (\<forall>f\<in>fs. eval (alphabet F2) val f) \<longrightarrow> eval (alphabet F2) val th) \<longrightarrow>
            (\<exists>pr. valid_proof F2 pr \<and> assumptions pr = fs \<and> thesis pr = th
                \<and> (\<forall> st \<in> set (steps pr). formula_well_formed (alphabet F2) st))"
    proof (intro allI impI)
      fix fs th
      assume wf_fs: "\<forall>f\<in>fs. formula_well_formed (alphabet F2) f"
      assume wf_th: "formula_well_formed (alphabet F2) th"
      assume "\<forall>val. (\<forall>f\<in>fs. eval (alphabet F2) val f) \<longrightarrow> eval (alphabet F2) val th"
      hence semFc: "\<forall>val. (\<forall>f\<in>fs. eval (alphabet Fc) val f) \<longrightarrow> eval (alphabet Fc) val th"
        by (simp add: alphF2 fc_alph)
      have wf_fsFc: "\<forall>f\<in>fs. formula_well_formed (alphabet Fc) f"
        using wf_fs by (simp add: alphF2 fc_alph)
      have wf_thFc: "formula_well_formed (alphabet Fc) th"
        using wf_th by (simp add: alphF2 fc_alph)
      have exFc: "\<exists>pr. valid_proof Fc pr \<and> assumptions pr = fs \<and> thesis pr = th
                    \<and> (\<forall> st \<in> set (steps pr). formula_well_formed (alphabet Fc) st)"
        using frege_system.impl_complete[OF fc, THEN spec[where x = fs], THEN spec[where x = th]]
              wf_fsFc wf_thFc semFc by blast
      then obtain pr where prFc: "valid_proof Fc pr" "assumptions pr = fs"
        "frege_proof.thesis pr = th"
        "\<forall> st \<in> set (steps pr). formula_well_formed (alphabet Fc) st"
        by blast
      have "valid_proof F2 pr"
        using prFc(1) valid_proof_mono_rules[OF rulesFc_sub] by blast
      thus "\<exists>pr. valid_proof F2 pr \<and> assumptions pr = fs \<and> thesis pr = th
               \<and> (\<forall> st \<in> set (steps pr). formula_well_formed (alphabet F2) st)"
        using prFc(2,3,4) by (auto simp add: alphF2 fc_alph)
    qed
  next
    show "finite (rules F2)"
      using frege_system.finite[OF fc] frege_system.finite[OF assms(1)] by (simp add: F2_def)
  next
    show "finite (UNIV :: 'c2 set)" by (rule finUNIV2)
  next
    show "\<forall>f :: dm_conn formula. \<exists> f' :: 'c2 formula.
            formula_well_formed (alphabet F2) f' \<and> formulas_equiv f dm_alphabet f' (alphabet F2)"
      using fcomp by (simp add: alphF2)
  next
    show "\<exists> t. arity (alphabet F2) t = 0 \<and> (\<forall> val. eval (alphabet F2) val (Conn t []) = True)"
      using htop by (simp add: alphF2)
  next
    show "\<exists> b. arity (alphabet F2) b = 0 \<and> (\<forall> val. eval (alphabet F2) val (Conn b []) = False)"
      using hbot by (simp add: alphF2)
  qed

  have rsim: "derived (rules F2) (map (rename_conn phi) fs) (rename_conn phi f)"
    if "derived (rules F1) fs f" for fs f
    using derived_mono_rules[OF rules_sub derived_rename[OF that]] .

  have "closure_of F1 F2 phi"
  proof (rule closure_of.intro)
    show "frege_system F1" by (rule assms(1))
    show "frege_system F2" by (rule fsF2)
    show "conn_closed (alphabet F2)" using ccl by (simp add: alphF2)
    show "\<And>c. conns_equiv c (alphabet F1) (phi c) (alphabet F2)" using cev by (simp add: alphF2)
    show "\<And>fs f. derived (rules F1) fs f
            \<Longrightarrow> derived (rules F2) (map (rename_conn phi) fs) (rename_conn phi f)"
      by (rule rsim)
  qed
  thus ?thesis by blast
qed

  

locale frege_closure = frege_balancing +
  assumes conn_closed_alphabet: "conn_closed (alphabet F)"
begin

definition conn_fix where
  "conn_fix c i b =
     (SOME c'. arity (alphabet F) c' = arity (alphabet F) c - 1
        \<and> (\<forall>args. length args = arity (alphabet F) c - 1 \<longrightarrow>
             conn_evals (alphabet F) c' args
               = conn_evals (alphabet F) c (take i args @ b # drop i args)))"

lemma conn_fix_spec:
  assumes "i < arity (alphabet F) c"
  shows "arity (alphabet F) (conn_fix c i b) = arity (alphabet F) c - 1
       \<and> (\<forall>args. length args = arity (alphabet F) c - 1 \<longrightarrow>
            conn_evals (alphabet F) (conn_fix c i b) args
              = conn_evals (alphabet F) c (take i args @ b # drop i args))"
proof -
  have ex: "\<exists>c'. arity (alphabet F) c' = arity (alphabet F) c - 1
       \<and> (\<forall>args. length args = arity (alphabet F) c - 1 \<longrightarrow>
            conn_evals (alphabet F) c' args
              = conn_evals (alphabet F) c (take i args @ b # drop i args))"
  proof -
    have "arity (alphabet F) c = 0
        \<or> (i < arity (alphabet F) c \<longrightarrow> (\<exists>c'. arity (alphabet F) c' = arity (alphabet F) c - 1
             \<and> (\<forall>args. length args = arity (alphabet F) c - 1 \<longrightarrow>
                  conn_evals (alphabet F) c' args
                    = conn_evals (alphabet F) c (take i args @ b # drop i args))))"
      using conn_closed_alphabet unfolding conn_closed_def by blast
    thus ?thesis using assms by auto
  qed
  show ?thesis unfolding conn_fix_def by (rule someI_ex[OF ex])
qed

lemma fix_at_zero:
  "fix_at [0] b (Conn c (q # qs))
     = Conn c ((if b then true_const else false_const) # qs)"
  by simp

lemma fix_at_zero_suc:
  "fix_at [Suc n] b (Conn c (a # as))
     = Conn c (a # as[n := (if b then true_const else false_const)])"
  by simp

lemma len_true_false_const:
  "len_formula (if b then true_const else false_const) = 1"
  by (cases b) (simp_all add: true_const_len false_const_len)

lemma spira_trans_true_false_const:
  "spira_trans (if b then true_const else false_const)
     = (if b then true_const else false_const)"
proof -
  have thr: "spira_threshold \<ge> 2" unfolding spira_threshold_def by simp
  have tT: "spira_trans true_const = true_const"
    using spira_trans_id_when_small[OF true_const_wf] true_const_len thr by simp
  have tF: "spira_trans false_const = false_const"
    using spira_trans_id_when_small[OF false_const_wf] false_const_len thr by simp
  show ?thesis by (cases b) (simp_all add: tT tF)
qed

lemma spira_trans_true_const: "spira_trans true_const = true_const"
  using spira_trans_true_false_const[of True] by simp

lemma spira_trans_false_const: "spira_trans false_const = false_const"
  using spira_trans_true_false_const[of False] by simp

subsection \<open>Constant elimination: the reduce identity\<close>

definition reduce_atoms where
  "reduce_atoms c = fresh_atoms (arity (alphabet F) c - 1)"

definition reduce_lhs where
  "reduce_lhs c b =
     Conn c ((if b then true_const else false_const) # map Atom (reduce_atoms c))"

definition reduce_rhs where
  "reduce_rhs c b = Conn (conn_fix c 0 b) (map Atom (reduce_atoms c))"

lemma reduce_atoms_spec:
  "length (reduce_atoms c) = arity (alphabet F) c - 1
   \<and> distinct (reduce_atoms c)
   \<and> set (reduce_atoms c) \<inter> avoid_atoms = {}"
  unfolding reduce_atoms_def
  using fresh_atoms_spec[of "arity (alphabet F) c - 1"] by simp

lemma reduce_taut:
  assumes "arity (alphabet F) c \<ge> 1"
  shows "\<forall>val. eval (alphabet F) val (iff_form (reduce_lhs c b) (reduce_rhs c b))"
proof (intro allI)
  fix val
  let ?ev = "eval (alphabet F) val"
  let ?ys = "reduce_atoms c"
  have ylen: "length ?ys = arity (alphabet F) c - 1" using reduce_atoms_spec by simp
  have a1: "0 < arity (alphabet F) c" using assms by simp
  have evcomp: "?ev \<circ> Atom = val" by (simp add: fun_eq_iff)
  have spec2: "conn_evals (alphabet F) (conn_fix c 0 b) (map val ?ys)
             = conn_evals (alphabet F) c (take 0 (map val ?ys) @ b # drop 0 (map val ?ys))"
    using conn_fix_spec[of 0 c b] a1 ylen by simp
  have lhs: "?ev (reduce_lhs c b) = conn_evals (alphabet F) c (b # map val ?ys)"
  proof -
    have "?ev (if b then true_const else false_const) = b"
      by (cases b) (simp_all add: true_const_eval false_const_eval)
    thus ?thesis unfolding reduce_lhs_def using evcomp by simp
  qed
  have rhs: "?ev (reduce_rhs c b) = conn_evals (alphabet F) c (b # map val ?ys)"
  proof -
    have "?ev (reduce_rhs c b)
        = conn_evals (alphabet F) (conn_fix c 0 b) (map val ?ys)"
      unfolding reduce_rhs_def using evcomp by simp
    thus ?thesis using spec2 by simp
  qed
  show "?ev (iff_form (reduce_lhs c b) (reduce_rhs c b))"
    using lhs rhs by (simp add: iff_form_eval)
qed

definition reduce_lines where
  "reduce_lines c b =
     length (steps (taut_proof (iff_form (reduce_lhs c b) (reduce_rhs c b))))"

definition reduce_step_len where
  "reduce_step_len c b =
     Max (insert 1 (len_formula ` set (steps (taut_proof
            (iff_form (reduce_lhs c b) (reduce_rhs c b))))))"

definition reduce_step_depth where
  "reduce_step_depth c b =
     Max (insert 1 (depth_formula ` set (steps (taut_proof
            (iff_form (reduce_lhs c b) (reduce_rhs c b))))))"

lemma reduce_proof:
  assumes "arity (alphabet F) c \<ge> 1"
  shows "provable_balanced_iff (reduce_lhs c b) (reduce_rhs c b)
           (reduce_lines c b) (reduce_step_len c b) (reduce_step_depth c b)"
proof -
  have cf_ar: "arity (alphabet F) (conn_fix c 0 b) = arity (alphabet F) c - 1"
    using conn_fix_spec[of 0 c b] assms by simp
  have wf_lhs: "formula_well_formed (alphabet F) (reduce_lhs c b)"
    unfolding reduce_lhs_def using reduce_atoms_spec assms
    by (cases b) (auto simp: true_const_wf false_const_wf)
  have wf_rhs: "formula_well_formed (alphabet F) (reduce_rhs c b)"
    unfolding reduce_rhs_def using reduce_atoms_spec cf_ar by simp
  show ?thesis
    using iff_from_taut[OF wf_lhs wf_rhs reduce_taut[OF assms]]
    unfolding reduce_lines_def reduce_step_len_def reduce_step_depth_def .
qed

definition reduce_sub where
  "reduce_sub c qs =
     (\<lambda>v. case map_of (zip (reduce_atoms c) qs) v of None \<Rightarrow> Atom v | Some f \<Rightarrow> f)"

lemma reduce_subst:
  assumes ar: "arity (alphabet F) c \<ge> 1"
      and len_qs: "length qs = arity (alphabet F) c - 1"
      and wf_qs: "\<And>q. q \<in> set qs \<Longrightarrow> formula_well_formed (alphabet F) q"
  shows "provable_balanced_iff
           (Conn c ((if b then true_const else false_const) # qs))
           (Conn (conn_fix c 0 b) qs)
           (reduce_lines c b)
           (reduce_step_len c b * len_sub (set (reduce_atoms c)) (reduce_sub c qs))
           (reduce_step_depth c b + depth_sub (set (reduce_atoms c)) (reduce_sub c qs))"
proof -
  let ?atoms = "reduce_atoms c"
  let ?sub = "reduce_sub c qs"
  have adist: "distinct ?atoms" using reduce_atoms_spec by simp
  have adisj: "set ?atoms \<inter> avoid_atoms = {}" using reduce_atoms_spec by simp
  have lveq: "length ?atoms = length qs" using reduce_atoms_spec len_qs by simp
  have sub_nth: "\<And>j. j < length ?atoms \<Longrightarrow> ?sub (?atoms ! j) = qs ! j"
  proof -
    fix j assume j: "j < length ?atoms"
    have "map_of (zip ?atoms qs) (?atoms ! j) = Some (qs ! j)"
      using map_of_zip_nth_lookup[OF adist lveq j] .
    thus "?sub (?atoms ! j) = qs ! j" unfolding reduce_sub_def by simp
  qed
  have sub_slots: "map ?sub ?atoms = qs"
  proof (rule nth_equalityI)
    show "length (map ?sub ?atoms) = length qs" using lveq by simp
  next
    fix j assume "j < length (map ?sub ?atoms)"
    hence j: "j < length ?atoms" by simp
    show "map ?sub ?atoms ! j = qs ! j" using j sub_nth[OF j] by simp
  qed
  have sig_id: "\<forall>v. v \<notin> set ?atoms \<longrightarrow> ?sub v = Atom v"
  proof (intro allI impI)
    fix v assume "v \<notin> set ?atoms"
    hence "map_of (zip ?atoms qs) v = None" by (rule map_of_zip_None_lookup)
    thus "?sub v = Atom v" unfolding reduce_sub_def by simp
  qed
  have finVS: "finite (set ?atoms)" by simp
  note sig_conn = fresh_sub_conn[OF adisj sig_id]
  have sig_wf: "\<And>v. v \<in> set ?atoms \<Longrightarrow> formula_well_formed (alphabet F) (?sub v)"
  proof -
    fix v assume v_in: "v \<in> set ?atoms"
    hence "\<exists>j. j < length ?atoms \<and> ?atoms ! j = v" by (simp add: in_set_conv_nth)
    then obtain j where j_lt: "j < length ?atoms" and jv: "?atoms ! j = v" by blast
    have subv: "?sub v = qs ! j" using sub_nth[OF j_lt] jv by simp
    have j_lt_qs: "j < length qs" using j_lt lveq by simp
    have "qs ! j \<in> set qs" using j_lt_qs by (rule nth_mem)
    thus "formula_well_formed (alphabet F) (?sub v)"
      using wf_qs by (simp add: subv)
  qed
  note subst_pbi =
    provable_balanced_iff_subst[OF reduce_proof[where b = b, OF ar] finVS sig_id sig_conn sig_wf]
  have mapslots: "map (sub_formula ?sub) (map Atom ?atoms) = qs"
    using sub_slots by (simp add: comp_def)
  have cb_sub: "sub_formula ?sub (if b then true_const else false_const)
              = (if b then true_const else false_const)"
    by (simp add: true_const_def false_const_def)
  have subL: "sub_formula ?sub (reduce_lhs c b)
            = Conn c ((if b then true_const else false_const) # qs)"
    unfolding reduce_lhs_def
    by (simp only: sub_formula.simps list.map mapslots cb_sub)
  have subR: "sub_formula ?sub (reduce_rhs c b) = Conn (conn_fix c 0 b) qs"
    unfolding reduce_rhs_def
    by (simp only: sub_formula.simps mapslots)
  show ?thesis using subst_pbi[unfolded subL subR] by blast
qed

subsection \<open>Shannon expansion: the multiplexer identity\<close>

definition shc_atoms where
  "shc_atoms d = fresh_atoms (arity (alphabet F) d + 1)"

definition shc_slots where
  "shc_slots d = take (arity (alphabet F) d) (shc_atoms d)"

definition shc_z where
  "shc_z d = shc_atoms d ! (arity (alphabet F) d)"

definition shc_lhs where
  "shc_lhs d i =
     balance (Conn d ((map Atom (shc_slots d))[i := true_const]))
             (Conn d ((map Atom (shc_slots d))[i := false_const]))
             (Atom (shc_z d))"

definition shc_rhs where
  "shc_rhs d i = Conn d ((map Atom (shc_slots d))[i := Atom (shc_z d)])"

lemma shc_atoms_spec:
  "length (shc_atoms d) = arity (alphabet F) d + 1
   \<and> distinct (shc_atoms d)
   \<and> set (shc_atoms d) \<inter> avoid_atoms = {}"
  unfolding shc_atoms_def
  using fresh_atoms_spec[of "arity (alphabet F) d + 1"] by simp

lemma shc_slots_len: "length (shc_slots d) = arity (alphabet F) d"
  unfolding shc_slots_def using shc_atoms_spec by simp

lemma shc_taut:
  assumes "i < arity (alphabet F) d"
  shows "\<forall>val. eval (alphabet F) val (iff_form (shc_lhs d i) (shc_rhs d i))"
proof (intro allI)
  fix val
  let ?ev = "eval (alphabet F) val"
  let ?S = "map val (shc_slots d)"
  have slen: "length (shc_slots d) = arity (alphabet F) d" by (rule shc_slots_len)
  have evcomp: "?ev \<circ> Atom = val" by (simp add: fun_eq_iff)
  have lhs: "?ev (shc_lhs d i)
           = (if val (shc_z d)
              then conn_evals (alphabet F) d (?S[i := True])
              else conn_evals (alphabet F) d (?S[i := False]))"
    unfolding shc_lhs_def
    by (simp add: balance_eval map_update true_const_eval false_const_eval evcomp
          del: balance.simps)
  have rhs: "?ev (shc_rhs d i)
           = conn_evals (alphabet F) d (?S[i := val (shc_z d)])"
    unfolding shc_rhs_def by (simp add: map_update evcomp)
  show "?ev (iff_form (shc_lhs d i) (shc_rhs d i))"
    unfolding lhs rhs iff_form_eval by (cases "val (shc_z d)") simp_all
qed

definition shc_lines where
  "shc_lines d i =
     length (steps (taut_proof (iff_form (shc_lhs d i) (shc_rhs d i))))"

definition shc_step_len where
  "shc_step_len d i =
     Max (insert 1 (len_formula ` set (steps (taut_proof
            (iff_form (shc_lhs d i) (shc_rhs d i))))))"

definition shc_step_depth where
  "shc_step_depth d i =
     Max (insert 1 (depth_formula ` set (steps (taut_proof
            (iff_form (shc_lhs d i) (shc_rhs d i))))))"

lemma shc_proof:
  assumes "i < arity (alphabet F) d"
  shows "provable_balanced_iff (shc_lhs d i) (shc_rhs d i)
           (shc_lines d i) (shc_step_len d i) (shc_step_depth d i)"
proof -
  have conn_slot_wf:
    "formula_well_formed (alphabet F) (Conn d ((map Atom (shc_slots d))[i := X]))"
    if "formula_well_formed (alphabet F) X" for X
  proof -
    have len: "length ((map Atom (shc_slots d))[i := X]) = arity (alphabet F) d"
      using shc_slots_len by simp
    have "\<forall>g\<in>set ((map Atom (shc_slots d))[i := X]).
            formula_well_formed (alphabet F) g"
    proof
      fix g
      assume "g \<in> set ((map Atom (shc_slots d))[i := X])"
      hence "g \<in> insert X (set (map Atom (shc_slots d)))"
        using set_update_subset_insert by fastforce
      thus "formula_well_formed (alphabet F) g" using that by auto
    qed
    thus ?thesis using len by simp
  qed
  have wf_lhs: "formula_well_formed (alphabet F) (shc_lhs d i)"
    unfolding shc_lhs_def
    by (intro balance_wf conn_slot_wf) (auto simp: true_const_wf false_const_wf)
  have wf_rhs: "formula_well_formed (alphabet F) (shc_rhs d i)"
    unfolding shc_rhs_def by (rule conn_slot_wf) simp
  show ?thesis
    using iff_from_taut[OF wf_lhs wf_rhs shc_taut[OF assms]]
    unfolding shc_lines_def shc_step_len_def shc_step_depth_def .
qed

definition shc_sub where
  "shc_sub d gs Z =
     (\<lambda>v. case map_of (zip (shc_atoms d) (gs @ [Z])) v of None \<Rightarrow> Atom v | Some f \<Rightarrow> f)"

lemma shc_subst:
  assumes ar: "i < arity (alphabet F) d"
      and len_gs: "length gs = arity (alphabet F) d"
      and wf_gs: "\<And>g. g \<in> set gs \<Longrightarrow> formula_well_formed (alphabet F) g"
      and wfZ: "formula_well_formed (alphabet F) Z"
  shows "provable_balanced_iff
           (balance (Conn d (gs[i := true_const])) (Conn d (gs[i := false_const])) Z)
           (Conn d (gs[i := Z]))
           (shc_lines d i)
           (shc_step_len d i * len_sub (set (shc_atoms d)) (shc_sub d gs Z))
           (shc_step_depth d i + depth_sub (set (shc_atoms d)) (shc_sub d gs Z))"
proof -
  let ?k = "arity (alphabet F) d"
  let ?atoms = "shc_atoms d"
  let ?slots = "shc_slots d"
  let ?vals = "gs @ [Z]"
  let ?sub = "shc_sub d gs Z"
  have alen: "length ?atoms = ?k + 1" using shc_atoms_spec by simp
  have adist: "distinct ?atoms" using shc_atoms_spec by simp
  have adisj: "set ?atoms \<inter> avoid_atoms = {}" using shc_atoms_spec by simp
  have slen: "length ?slots = ?k" by (rule shc_slots_len)
  have vlen: "length ?vals = ?k + 1" using len_gs by simp
  have lveq: "length ?atoms = length ?vals" using alen vlen by simp
  have slots_nth: "\<And>j. j < ?k \<Longrightarrow> ?slots ! j = ?atoms ! j"
    unfolding shc_slots_def by simp
  have sub_nth: "\<And>j. j < ?k + 1 \<Longrightarrow> ?sub (?atoms ! j) = ?vals ! j"
  proof -
    fix j assume j: "j < ?k + 1"
    hence "map_of (zip ?atoms ?vals) (?atoms ! j) = Some (?vals ! j)"
      using map_of_zip_nth_lookup[OF adist lveq] alen by simp
    thus "?sub (?atoms ! j) = ?vals ! j" unfolding shc_sub_def by simp
  qed
  have sub_z: "?sub (shc_z d) = Z"
  proof -
    have "?sub (shc_z d) = ?vals ! ?k" using sub_nth[of ?k] unfolding shc_z_def by simp
    thus ?thesis using len_gs by (simp add: nth_append)
  qed
  have sub_slots: "map ?sub ?slots = gs"
  proof (rule nth_equalityI)
    show "length (map ?sub ?slots) = length gs" using slen len_gs by simp
  next
    fix j assume "j < length (map ?sub ?slots)"
    hence j: "j < ?k" using slen by simp
    have "map ?sub ?slots ! j = ?sub (?atoms ! j)" using j slen slots_nth[OF j] by simp
    also have "\<dots> = ?vals ! j" using sub_nth[of j] j by simp
    also have "\<dots> = gs ! j" using j len_gs by (simp add: nth_append)
    finally show "map ?sub ?slots ! j = gs ! j" .
  qed
  have sig_id: "\<forall>v. v \<notin> set ?atoms \<longrightarrow> ?sub v = Atom v"
  proof (intro allI impI)
    fix v assume "v \<notin> set ?atoms"
    hence "map_of (zip ?atoms ?vals) v = None" by (rule map_of_zip_None_lookup)
    thus "?sub v = Atom v" unfolding shc_sub_def by simp
  qed
  have finVS: "finite (set ?atoms)" by simp
  note sig_conn = fresh_sub_conn[OF adisj sig_id]
  note sig_cb = fresh_sub_cb[OF adisj sig_id]
  have sig_wf: "\<And>v. v \<in> set ?atoms \<Longrightarrow> formula_well_formed (alphabet F) (?sub v)"
  proof -
    fix v assume v_in: "v \<in> set ?atoms"
    hence "\<exists>j. j < length ?atoms \<and> ?atoms ! j = v" by (simp add: in_set_conv_nth)
    then obtain j where j_lt: "j < length ?atoms" and jv: "?atoms ! j = v" by blast
    have subv: "?sub v = ?vals ! j" using sub_nth[of j] j_lt alen jv by simp
    have j_lt_vals: "j < length ?vals" using j_lt lveq by simp
    have "?vals ! j \<in> set ?vals" using j_lt_vals by (rule nth_mem)
    hence "?vals ! j \<in> set gs \<union> {Z}" by auto
    thus "formula_well_formed (alphabet F) (?sub v)"
      using wf_gs wfZ by (auto simp: subv)
  qed
  note subst_pbi =
    provable_balanced_iff_subst[OF shc_proof[OF ar] finVS sig_id sig_conn sig_wf]
  have mapslots: "map (sub_formula ?sub) (map Atom ?slots) = gs"
    using sub_slots by (simp add: comp_def)
  have tc: "sub_formula ?sub true_const = true_const" by (simp add: true_const_def)
  have fc: "sub_formula ?sub false_const = false_const" by (simp add: false_const_def)
  have subL: "sub_formula ?sub (shc_lhs d i)
            = balance (Conn d (gs[i := true_const])) (Conn d (gs[i := false_const])) Z"
  proof -
    have "sub_formula ?sub (shc_lhs d i)
        = balance (sub_formula ?sub (Conn d ((map Atom ?slots)[i := true_const])))
                  (sub_formula ?sub (Conn d ((map Atom ?slots)[i := false_const])))
                  (sub_formula ?sub (Atom (shc_z d)))"
      unfolding shc_lhs_def by (rule sub_formula_balance[OF sig_cb])
    thus ?thesis
      by (simp only: sub_formula.simps map_update mapslots tc fc sub_z)
  qed
  have subR: "sub_formula ?sub (shc_rhs d i) = Conn d (gs[i := Z])"
    unfolding shc_rhs_def
    by (simp only: sub_formula.simps map_update mapslots sub_z)
  show ?thesis using subst_pbi[unfolded subL subR] by blast
qed

subsection \<open>Uniform cost bounds for the schematic proofs\<close>

definition shc_max_lines where
  "shc_max_lines = Max (insert 0 ((\<lambda>(d,i). shc_lines d i) ` reassoc_index_set))"
definition shc_max_step_len where
  "shc_max_step_len = Max (insert 0 ((\<lambda>(d,i). shc_step_len d i) ` reassoc_index_set))"
definition shc_max_step_depth where
  "shc_max_step_depth = Max (insert 0 ((\<lambda>(d,i). shc_step_depth d i) ` reassoc_index_set))"

lemma shc_lines_le:
  assumes "i < arity (alphabet F) d" shows "shc_lines d i \<le> shc_max_lines"
  using reassoc_max_ge[OF assms, of shc_lines] unfolding shc_max_lines_def .
lemma shc_step_len_le:
  assumes "i < arity (alphabet F) d" shows "shc_step_len d i \<le> shc_max_step_len"
  using reassoc_max_ge[OF assms, of shc_step_len] unfolding shc_max_step_len_def .
lemma shc_step_depth_le:
  assumes "i < arity (alphabet F) d" shows "shc_step_depth d i \<le> shc_max_step_depth"
  using reassoc_max_ge[OF assms, of shc_step_depth] unfolding shc_max_step_depth_def .

definition reduce_max_lines where
  "reduce_max_lines =
     Max (insert 0 ((\<lambda>c. max (reduce_lines c True) (reduce_lines c False)) ` UNIV))"
definition reduce_max_step_len where
  "reduce_max_step_len =
     Max (insert 0 ((\<lambda>c. max (reduce_step_len c True) (reduce_step_len c False)) ` UNIV))"
definition reduce_max_step_depth where
  "reduce_max_step_depth =
     Max (insert 0 ((\<lambda>c. max (reduce_step_depth c True) (reduce_step_depth c False)) ` UNIV))"

lemma reduce_lines_le: "reduce_lines c b \<le> reduce_max_lines"
proof -
  have fs: "frege_system F" by (meson frege_balancing_axioms frege_balancing_def)
  have fin: "finite (insert 0 ((\<lambda>c. max (reduce_lines c True) (reduce_lines c False)) ` UNIV))"
    using frege_system.finite_alphabet[OF fs] by simp
  have "max (reduce_lines c True) (reduce_lines c False) \<le> reduce_max_lines"
    unfolding reduce_max_lines_def by (rule Max_ge[OF fin]) simp
  thus ?thesis by (cases b) simp_all
qed
lemma reduce_step_len_le: "reduce_step_len c b \<le> reduce_max_step_len"
proof -
  have fs: "frege_system F" by (meson frege_balancing_axioms frege_balancing_def)
  have fin: "finite (insert 0 ((\<lambda>c. max (reduce_step_len c True) (reduce_step_len c False)) ` UNIV))"
    using frege_system.finite_alphabet[OF fs] by simp
  have "max (reduce_step_len c True) (reduce_step_len c False) \<le> reduce_max_step_len"
    unfolding reduce_max_step_len_def by (rule Max_ge[OF fin]) simp
  thus ?thesis by (cases b) simp_all
qed
lemma reduce_step_depth_le: "reduce_step_depth c b \<le> reduce_max_step_depth"
proof -
  have fs: "frege_system F" by (meson frege_balancing_axioms frege_balancing_def)
  have fin: "finite (insert 0 ((\<lambda>c. max (reduce_step_depth c True) (reduce_step_depth c False)) ` UNIV))"
    using frege_system.finite_alphabet[OF fs] by simp
  have "max (reduce_step_depth c True) (reduce_step_depth c False) \<le> reduce_max_step_depth"
    unfolding reduce_max_step_depth_def by (rule Max_ge[OF fin]) simp
  thus ?thesis by (cases b) simp_all
qed

lemma reduce_sub_map:
  assumes "length qs = arity (alphabet F) c - 1"
  shows "map (reduce_sub c qs) (reduce_atoms c) = qs"
proof (rule nth_equalityI)
  have alen: "length (reduce_atoms c) = arity (alphabet F) c - 1" using reduce_atoms_spec by simp
  show "length (map (reduce_sub c qs) (reduce_atoms c)) = length qs" using alen assms by simp
next
  fix j assume "j < length (map (reduce_sub c qs) (reduce_atoms c))"
  hence j: "j < length (reduce_atoms c)" by simp
  have adist: "distinct (reduce_atoms c)" using reduce_atoms_spec by simp
  have lveq: "length (reduce_atoms c) = length qs" using reduce_atoms_spec assms by simp
  have "map_of (zip (reduce_atoms c) qs) (reduce_atoms c ! j) = Some (qs ! j)"
    using map_of_zip_nth_lookup[OF adist lveq j] .
  hence "reduce_sub c qs (reduce_atoms c ! j) = qs ! j" unfolding reduce_sub_def by simp
  thus "map (reduce_sub c qs) (reduce_atoms c) ! j = qs ! j" using j by simp
qed

lemma shc_sub_map:
  assumes "length gs = arity (alphabet F) d"
  shows "map (shc_sub d gs Z) (shc_atoms d) = gs @ [Z]"
proof (rule nth_equalityI)
  have alen: "length (shc_atoms d) = arity (alphabet F) d + 1" using shc_atoms_spec by simp
  show "length (map (shc_sub d gs Z) (shc_atoms d)) = length (gs @ [Z])" using alen assms by simp
next
  fix j assume "j < length (map (shc_sub d gs Z) (shc_atoms d))"
  hence j: "j < length (shc_atoms d)" by simp
  have adist: "distinct (shc_atoms d)" using shc_atoms_spec by simp
  have lveq: "length (shc_atoms d) = length (gs @ [Z])" using shc_atoms_spec assms by simp
  have "map_of (zip (shc_atoms d) (gs @ [Z])) (shc_atoms d ! j) = Some ((gs @ [Z]) ! j)"
    using map_of_zip_nth_lookup[OF adist lveq j] .
  hence "shc_sub d gs Z (shc_atoms d ! j) = (gs @ [Z]) ! j" unfolding shc_sub_def by simp
  thus "map (shc_sub d gs Z) (shc_atoms d) ! j = (gs @ [Z]) ! j" using j by simp
qed

lemma reduce_len_sub:
  assumes "length qs = arity (alphabet F) c - 1"
  shows "len_sub (set (reduce_atoms c)) (reduce_sub c qs)
       = max 1 (sum_list (map len_formula qs))"
proof -
  have adist: "distinct (reduce_atoms c)" using reduce_atoms_spec by simp
  have "(\<Sum>v\<in>set (reduce_atoms c). len_formula (reduce_sub c qs v))
      = sum_list (map len_formula (map (reduce_sub c qs) (reduce_atoms c)))"
    by (simp add: sum_list_distinct_conv_sum_set[OF adist] comp_def)
  also have "\<dots> = sum_list (map len_formula qs)" using reduce_sub_map[OF assms] by simp
  finally show ?thesis unfolding len_sub_def by simp
qed

lemma shc_len_sub:
  assumes "length gs = arity (alphabet F) d"
  shows "len_sub (set (shc_atoms d)) (shc_sub d gs Z)
       = max 1 (sum_list (map len_formula gs) + len_formula Z)"
proof -
  have adist: "distinct (shc_atoms d)" using shc_atoms_spec by simp
  have "(\<Sum>v\<in>set (shc_atoms d). len_formula (shc_sub d gs Z v))
      = sum_list (map len_formula (map (shc_sub d gs Z) (shc_atoms d)))"
    by (simp add: sum_list_distinct_conv_sum_set[OF adist] comp_def)
  also have "\<dots> = sum_list (map len_formula (gs @ [Z]))" using shc_sub_map[OF assms] by simp
  also have "\<dots> = sum_list (map len_formula gs) + len_formula Z" by simp
  finally show ?thesis unfolding len_sub_def by simp
qed

lemma reduce_depth_sub:
  assumes "length qs = arity (alphabet F) c - 1"
  shows "depth_sub (set (reduce_atoms c)) (reduce_sub c qs)
       = Max (insert 1 (depth_formula ` set qs))"
proof -
  have "(\<lambda>v. depth_formula (reduce_sub c qs v)) ` set (reduce_atoms c) = depth_formula ` set qs"
  proof -
    have "(\<lambda>v. depth_formula (reduce_sub c qs v)) ` set (reduce_atoms c)
        = depth_formula ` ((reduce_sub c qs) ` set (reduce_atoms c))" by (simp add: image_image)
    also have "(reduce_sub c qs) ` set (reduce_atoms c)
             = set (map (reduce_sub c qs) (reduce_atoms c))" by simp
    also have "\<dots> = set qs" using reduce_sub_map[OF assms] by simp
    finally show ?thesis .
  qed
  thus ?thesis unfolding depth_sub_def by simp
qed

lemma shc_depth_sub:
  assumes "length gs = arity (alphabet F) d"
  shows "depth_sub (set (shc_atoms d)) (shc_sub d gs Z)
       = Max (insert 1 (depth_formula ` set (gs @ [Z])))"
proof -
  have "(\<lambda>v. depth_formula (shc_sub d gs Z v)) ` set (shc_atoms d)
      = depth_formula ` set (gs @ [Z])"
  proof -
    have "(\<lambda>v. depth_formula (shc_sub d gs Z v)) ` set (shc_atoms d)
        = depth_formula ` ((shc_sub d gs Z) ` set (shc_atoms d))" by (simp add: image_image)
    also have "(shc_sub d gs Z) ` set (shc_atoms d) = set (map (shc_sub d gs Z) (shc_atoms d))"
      by simp
    also have "\<dots> = set (gs @ [Z])" using shc_sub_map[OF assms] by simp
    finally show ?thesis .
  qed
  thus ?thesis unfolding depth_sub_def by simp
qed

subsection \<open>Arithmetic and depth infrastructure\<close>

lemma arity_le_max:
  "arity (alphabet F) c \<le> Max (arity (alphabet F) ` UNIV)"
proof -
  have fs: "frege_system F" by (meson frege_balancing_axioms frege_balancing_def)
  have fin: "finite (arity (alphabet F) ` UNIV)"
    using frege_system.finite_alphabet[OF fs] by simp
  show ?thesis using Max_ge[OF fin] by simp
qed

lemma sum_list_update_lt:
  fixes xs :: "nat list"
  assumes "j < length xs" and "y < xs ! j"
  shows "sum_list (xs[j := y]) < sum_list xs"
  using assms
proof (induction xs arbitrary: j)
  case Nil thus ?case by simp
next
  case (Cons x xs')
  show ?case
  proof (cases j)
    case 0 thus ?thesis using Cons.prems by simp
  next
    case (Suc j')
    have "j' < length xs'" and "y < xs' ! j'" using Cons.prems Suc by auto
    hence "sum_list (xs'[j' := y]) < sum_list xs'" by (rule Cons.IH)
    thus ?thesis using Suc by simp
  qed
qed

lemma len_formula_ge_1: "1 \<le> len_formula f"
  by (cases f) simp_all

definition count_big :: "'c formula list \<Rightarrow> nat" where
  "count_big qs = length (filter (\<lambda>q. 2 \<le> len_formula q) qs)"

lemma count_big_update:
  assumes "j < length qs" and "2 \<le> len_formula (qs ! j)" and "len_formula v < 2"
  shows "Suc (count_big (qs[j := v])) = count_big qs"
  using assms unfolding count_big_def
proof (induction qs arbitrary: j)
  case Nil thus ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (cases j)
    case 0 thus ?thesis using Cons.prems by simp
  next
    case (Suc j')
    have "j' < length xs" and "2 \<le> len_formula (xs ! j')" and "len_formula v < 2"
      using Cons.prems Suc by auto
    hence "Suc (length (filter (\<lambda>q. 2 \<le> len_formula q) (xs[j' := v])))
         = length (filter (\<lambda>q. 2 \<le> len_formula q) xs)"
      using Cons.IH by blast
    thus ?thesis using Suc by simp
  qed
qed

lemma sum_list_map_eq_length:
  assumes "\<forall>x\<in>set xs. f x = (1::nat)"
  shows "sum_list (map f xs) = length xs"
  using assms by (induct xs) auto

lemma sum_list_map_le:
  assumes "\<forall>x\<in>set xs. f x \<le> (k::nat)"
  shows "sum_list (map f xs) \<le> length xs * k"
  using assms by (induct xs) (auto simp: add_le_mono)

lemma real_Max_depth_le:
  assumes "ds \<noteq> []" and "\<forall>g\<in>set ds. real (depth_formula g) \<le> B"
  shows "real (Max (set (map depth_formula ds))) \<le> B"
proof -
  have "Max (set (map depth_formula ds)) \<in> set (map depth_formula ds)"
    using assms(1) by (intro Max_in) auto
  then obtain g where "g \<in> set ds" and "Max (set (map depth_formula ds)) = depth_formula g"
    by auto
  thus ?thesis using assms(2) by auto
qed

lemma conn_dep_le:
  assumes "\<forall>g\<in>set ds. real (depth_formula g) \<le> B" and "0 \<le> B"
  shows "real (depth_formula (Conn c ds)) \<le> B + 1"
proof (cases "ds = []")
  case True thus ?thesis using assms(2) by simp
next
  case False
  have "real (depth_formula (Conn c ds)) = 1 + real (Max (set (map depth_formula ds)))"
    using False by simp
  also have "real (Max (set (map depth_formula ds))) \<le> B"
    using False assms(1) by (rule real_Max_depth_le)
  finally show ?thesis by simp
qed

lemma balance_dep_le:
  assumes "real (depth_formula x) \<le> B" and "real (depth_formula y) \<le> B"
      and "real (depth_formula z) \<le> B" and "(1::real) \<le> B"
  shows "real (depth_formula (balance x y z)) \<le> real (depth_formula custom_balancing) + B"
proof -
  have m: "real (Max (insert 1 {depth_formula x, depth_formula y, depth_formula z})) \<le> B"
  proof -
    have "Max (insert 1 {depth_formula x, depth_formula y, depth_formula z})
            \<in> insert 1 {depth_formula x, depth_formula y, depth_formula z}"
      by (intro Max_in) auto
    thus ?thesis using assms by auto
  qed
  have "real (depth_formula (balance x y z))
      \<le> real (depth_formula custom_balancing
               + Max (insert 1 {depth_formula x, depth_formula y, depth_formula z}))"
    using balance_depth_bound[of x y z] by simp
  also have "\<dots> = real (depth_formula custom_balancing)
      + real (Max (insert 1 {depth_formula x, depth_formula y, depth_formula z}))" by simp
  also have "\<dots> \<le> real (depth_formula custom_balancing) + B" using m by simp
  finally show ?thesis .
qed

lemma real_of_nat_max_le:
  assumes "real m \<le> B" and "real n \<le> B"
  shows "real (max m n) \<le> B"
  using assms by (simp add: of_nat_max)

lemma depth_elt_le_conn:
  assumes "g \<in> set ds"
  shows "depth_formula g \<le> depth_formula (Conn c ds)"
proof -
  have ne: "0 < length ds" using assms by (cases ds) auto
  have eq: "depth_formula (Conn c ds) = 1 + Max (set (map depth_formula ds))"
    using ne by simp
  have "depth_formula g \<le> Max (set (map depth_formula ds))"
    using assms by (intro Max_ge) auto
  thus ?thesis unfolding eq by linarith
qed

lemma conn_dep_le_nat:
  assumes "\<forall>g\<in>set ds. depth_formula g \<le> B"
  shows "depth_formula (Conn c ds) \<le> B + 1"
proof (cases "ds = []")
  case True thus ?thesis by simp
next
  case False
  have "Max (set (map depth_formula ds)) \<le> B"
    using assms False by (intro Max.boundedI) auto
  thus ?thesis using False by simp
qed

lemma prod_le_36W:
  fixes A B Cc LL W :: nat
  assumes A: "A \<le> Cc" and B: "B \<le> 36 * (Cc * LL)" and Wdef: "W = Cc * Cc * (LL + 1)"
  shows "A * B \<le> 36 * W"
proof -
  have "A * B \<le> Cc * (36 * (Cc * LL))" by (rule mult_le_mono[OF A B])
  also have "\<dots> = 36 * (Cc * Cc * LL)" by (simp add: ac_simps)
  also have "Cc * Cc * LL \<le> Cc * Cc * (LL + 1)" by (rule mult_le_mono2) simp
  hence "36 * (Cc * Cc * LL) \<le> 36 * (Cc * Cc * (LL + 1))" by (rule mult_le_mono2)
  finally show ?thesis unfolding Wdef .
qed

lemma nat_le_real_KcDL:
  fixes leaf Kc DL :: nat
  assumes "leaf \<le> Kc * (DL + 1)"
  shows "real leaf \<le> real Kc * (real DL + 1)"
proof -
  have "real leaf \<le> real (Kc * (DL + 1))" using assms by (simp only: of_nat_le_iff)
  also have "real (Kc * (DL + 1)) = real Kc * (real DL + 1)" by (simp add: distrib_left)
  finally show ?thesis .
qed

lemma kc_dist: "(K::nat) * (D + 1) = K + K * D"
  by (simp add: distrib_left)

lemma leaf_log_bound:
  fixes leaf :: nat and K M cc LG :: real
  assumes "real leaf \<le> K + M * LG" and "0 \<le> K" and "0 \<le> M"
      and "1 \<le> LG" and "K + M \<le> cc"
  shows "real leaf \<le> cc * LG"
proof -
  have kL: "K \<le> K * LG" using mult_left_mono[OF assms(4) assms(2)] by simp
  have "real leaf \<le> K + M * LG" by (rule assms(1))
  also have "\<dots> \<le> K * LG + M * LG" using kL by simp
  also have "\<dots> = (K + M) * LG" by (simp add: distrib_right)
  also have "\<dots> \<le> cc * LG" using assms(4,5) by (intro mult_right_mono) auto
  finally show ?thesis .
qed

lemma sz_scale:
  fixes B Cc LL :: nat
  assumes "B \<le> 36 * LL" and "1 \<le> Cc"
  shows "B \<le> 36 * (Cc * LL)"
proof -
  have "B \<le> 36 * LL" by (rule assms(1))
  also have "LL \<le> Cc * LL" using mult_le_mono1[OF assms(2), of LL] by simp
  hence "36 * LL \<le> 36 * (Cc * LL)" by (rule mult_le_mono2)
  finally show ?thesis .
qed

lemma prod_le_kV:
  fixes A B Cc MA prt m V :: nat
  assumes "A \<le> Cc" and "B \<le> m * (Cc * (MA + 1) * (prt + 1))"
      and "V = Cc * Cc * (MA + 1) * (prt + 1)"
  shows "A * B \<le> m * V"
proof -
  have "A * B \<le> Cc * (m * (Cc * (MA + 1) * (prt + 1)))"
    by (rule mult_le_mono[OF assms(1) assms(2)])
  also have "Cc * (m * (Cc * (MA + 1) * (prt + 1))) = m * (Cc * Cc * (MA + 1) * (prt + 1))"
    by (simp only: ac_simps)
  finally show ?thesis unfolding assms(3) .
qed

lemma len_le_via_cb:
  fixes L cb inner Cc MA prt k :: nat
  assumes "L \<le> cb * inner" and "cb \<le> Cc" and "inner \<le> k * ((MA + 1) * (prt + 1))"
  shows "L \<le> k * (Cc * (MA + 1) * (prt + 1))"
proof -
  have "L \<le> Cc * (k * ((MA + 1) * (prt + 1)))"
    by (rule order_trans[OF assms(1) mult_le_mono[OF assms(2) assms(3)]])
  also have "Cc * (k * ((MA + 1) * (prt + 1))) = k * (Cc * (MA + 1) * (prt + 1))"
    by (simp only: ac_simps)
  finally show ?thesis .
qed

lemma scale_MA_prt:
  fixes inner k MA prt :: nat
  assumes "inner \<le> k * (prt + 1)"
  shows "inner \<le> k * ((MA + 1) * (prt + 1))"
proof -
  have "1 * (prt + 1) \<le> (MA + 1) * (prt + 1)" by (rule mult_le_mono1) simp
  hence "(prt + 1) \<le> (MA + 1) * (prt + 1)" by simp
  hence "k * (prt + 1) \<le> k * ((MA + 1) * (prt + 1))" by (rule mult_le_mono2)
  thus ?thesis using assms by linarith
qed

lemma budget_bounds:
  fixes p Cc MA :: nat
  assumes "1 \<le> Cc"
  shows "p \<le> Cc * (MA + 1) * (p + 1)"
    and "1 + MA * p \<le> Cc * (MA + 1) * (p + 1)"
    and "1 + (MA + 1) * p \<le> Cc * (MA + 1) * (p + 1)"
proof -
  have scale: "(MA + 1) * (p + 1) \<le> Cc * (MA + 1) * (p + 1)"
  proof -
    have "(MA + 1) * (p + 1) = 1 * ((MA + 1) * (p + 1))" by simp
    also have "\<dots> \<le> Cc * ((MA + 1) * (p + 1))" by (rule mult_le_mono1[OF assms])
    also have "Cc * ((MA + 1) * (p + 1)) = Cc * (MA + 1) * (p + 1)" by (simp only: mult.assoc)
    finally show ?thesis .
  qed
  have b1: "p \<le> (MA + 1) * (p + 1)" by (simp add: algebra_simps)
  have b2: "1 + MA * p \<le> (MA + 1) * (p + 1)" by (simp add: algebra_simps)
  have b3: "1 + (MA + 1) * p \<le> (MA + 1) * (p + 1)" by (simp add: algebra_simps)
  show "p \<le> Cc * (MA + 1) * (p + 1)" using b1 scale by (rule order_trans)
  show "1 + MA * p \<le> Cc * (MA + 1) * (p + 1)" using b2 scale by (rule order_trans)
  show "1 + (MA + 1) * p \<le> Cc * (MA + 1) * (p + 1)" using b3 scale by (rule order_trans)
qed

subsection \<open>The bounded comprehension engine (commutes_aux)\<close>

lemma commutes_aux:
  shows "\<exists> (SL :: nat poly) (DD :: real) (DDC :: real). \<forall> c b qs N.
           1 \<le> arity (alphabet F) c
         \<and> (\<forall>q\<in>set qs. formula_well_formed (alphabet F) q)
         \<and> length qs = arity (alphabet F) c - 1
         \<and> len_formula (Conn c ((if b then true_const else false_const) # qs)) \<le> N
       \<longrightarrow> (\<exists> lines sz dep. provable_balanced_iff
              (spira_trans (Conn c ((if b then true_const else false_const) # qs)))
              (Conn (conn_fix c 0 b) (map spira_trans qs)) lines sz dep
            \<and> lines \<le> poly SL N * 4 ^ count_big qs
            \<and> sz \<le> poly SL N * 4 ^ count_big qs
            \<and> real dep \<le> DD * log 2 (real N + 1) + DDC)"
proof -
  obtain bnd_reb c_reb where reb:
    "\<forall>P pos. formula_well_formed (alphabet F) P \<and> valid_position P pos \<longrightarrow>
       (\<exists>lines sz dep. provable_balanced_iff (spira_trans P) (rebalancing P pos) lines sz dep
          \<and> lines \<le> poly bnd_reb (len_formula P) \<and> sz \<le> poly bnd_reb (len_formula P)
          \<and> real dep \<le> c_reb * log 2 (real (len_formula P) + 1))"
    using rebalancing_provable by blast
  obtain tc where tc:
    "\<forall>f. formula_well_formed (alphabet F) f \<longrightarrow>
       real (depth_formula (spira_trans f)) \<le> tc * log 2 (real (len_formula f) + 1)"
    using trans_c by blast
  define MA where "MA = Max (arity (alphabet F) ` UNIV)"
  define Cc :: nat where
    "Cc = (reduce_max_lines + reduce_max_step_len + reduce_max_step_depth
         + shc_max_lines + shc_max_step_len + shc_max_step_depth
         + balance_cong_lines + balance_cong_step_len + balance_cong_step_depth
         + trans_lines + trans_step_len + trans_step_depth
         + refl_lines + refl_step_len + refl_step_depth
         + len_formula custom_balancing + depth_formula custom_balancing + 1) * 10000"
  define SL :: "nat poly" where
    "SL = bnd_reb + Polynomial.smult (Cc * Cc * Cc * (MA + 1)) rebal_tb
        + Polynomial.monom (Cc * Cc * Cc * (MA + 1)) 1 + [: Cc * Cc * Cc * (MA + 1) :]"
  define DD :: real where "DD = max c_reb (max tc 1)"
  define DDC :: real where "DDC = real (2 * Cc + spira_threshold) + 2"
  have polySL: "\<And>n. poly SL n
      = poly bnd_reb n + (Cc * Cc * Cc * (MA + 1)) * poly rebal_tb n
        + (Cc * Cc * Cc * (MA + 1)) * n + Cc * Cc * Cc * (MA + 1)"
    unfolding SL_def by (simp add: poly_monom)
  have Ccge1: "1 \<le> Cc" unfolding Cc_def by simp
  have Ccbig: "1000 \<le> Cc" unfolding Cc_def by simp
  have Cc_red_l: "reduce_max_lines \<le> Cc" unfolding Cc_def by simp
  have Cc_red_s: "reduce_max_step_len \<le> Cc" unfolding Cc_def by simp
  have Cc_red_d: "reduce_max_step_depth \<le> Cc" unfolding Cc_def by simp
  have Cc_shc_s: "shc_max_step_len \<le> Cc" unfolding Cc_def by simp
  have Cc_shc_d: "shc_max_step_depth \<le> Cc" unfolding Cc_def by simp
  have Cc_bcsl: "balance_cong_step_len \<le> Cc" unfolding Cc_def by simp
  have Cc_bcsd: "balance_cong_step_depth \<le> Cc" unfolding Cc_def by simp
  have Cc_tsl: "trans_step_len \<le> Cc" unfolding Cc_def by simp
  have Cc_tsd: "trans_step_depth \<le> Cc" unfolding Cc_def by simp
  have Cc_rfsl: "refl_step_len \<le> Cc" unfolding Cc_def by simp
  have Cc_rfsd: "refl_step_depth \<le> Cc" unfolding Cc_def by simp
  have Cc_cbl: "len_formula custom_balancing \<le> Cc" unfolding Cc_def by simp
  have Cc_cbd: "depth_formula custom_balancing \<le> Cc" unfolding Cc_def by simp
  have SLge: "\<And>n. Cc * Cc * Cc * (MA + 1) \<le> poly SL n" using polySL by simp
  have CcMA: "Cc \<le> Cc * Cc * Cc * (MA + 1)"
  proof -
    have "Cc * 1 * 1 * 1 \<le> Cc * Cc * Cc * (MA + 1)"
      by (intro mult_le_mono) (use Ccge1 in simp_all)
    thus ?thesis by simp
  qed
  have CcSL: "\<And>n. Cc \<le> poly SL n" using CcMA SLge order_trans by blast
  have Cc1SL: "\<And>n. Cc * (n + 1) \<le> poly SL n"
  proof -
    fix n
    have "Cc * (n + 1) = Cc * n + Cc" by simp
    also have "\<dots> \<le> (Cc * Cc * Cc * (MA + 1)) * n + Cc * Cc * Cc * (MA + 1)"
      using CcMA by (simp add: add_mono mult_le_mono1)
    also have "\<dots> \<le> poly SL n" using polySL[of n] by simp
    finally show "Cc * (n + 1) \<le> poly SL n" .
  qed
  have SLpow: "\<And>n m. poly SL n \<le> poly SL n * 4 ^ m"
  proof -
    fix n m :: nat
    show "poly SL n \<le> poly SL n * 4 ^ m"
      using mult_le_mono2[of 1 "4 ^ m" "poly SL n"] by simp
  qed
  have main: "\<And> c b N qs. 1 \<le> arity (alphabet F) c \<Longrightarrow>
       ((\<forall>q\<in>set qs. formula_well_formed (alphabet F) q)
        \<and> length qs = arity (alphabet F) c - 1
        \<and> len_formula (Conn c ((if b then true_const else false_const) # qs)) \<le> N)
       \<longrightarrow> (\<exists> lines sz dep. provable_balanced_iff
              (spira_trans (Conn c ((if b then true_const else false_const) # qs)))
              (Conn (conn_fix c 0 b) (map spira_trans qs)) lines sz dep
            \<and> lines \<le> poly SL N * 4 ^ count_big qs
            \<and> sz \<le> poly SL N * 4 ^ count_big qs
            \<and> real dep \<le> DD * log 2 (real N + 1) + DDC)"
  proof -
    fix c b N qs
    assume ar: "1 \<le> arity (alphabet F) c"
    show "((\<forall>q\<in>set qs. formula_well_formed (alphabet F) q)
        \<and> length qs = arity (alphabet F) c - 1
        \<and> len_formula (Conn c ((if b then true_const else false_const) # qs)) \<le> N)
       \<longrightarrow> (\<exists> lines sz dep. provable_balanced_iff
              (spira_trans (Conn c ((if b then true_const else false_const) # qs)))
              (Conn (conn_fix c 0 b) (map spira_trans qs)) lines sz dep
            \<and> lines \<le> poly SL N * 4 ^ count_big qs
            \<and> sz \<le> poly SL N * 4 ^ count_big qs
            \<and> real dep \<le> DD * log 2 (real N + 1) + DDC)"
    proof (induction "sum_list (map len_formula qs)" arbitrary: qs rule: less_induct)
      case less
      let ?cb = "if b then true_const else false_const"
      let ?N1 = "Conn c (?cb # qs)"
      show ?case
      proof (rule impI)
        assume A: "(\<forall>q\<in>set qs. formula_well_formed (alphabet F) q)
                 \<and> length qs = arity (alphabet F) c - 1 \<and> len_formula ?N1 \<le> N"
        from A have wfqs: "\<forall>q\<in>set qs. formula_well_formed (alphabet F) q"
          and lenqs: "length qs = arity (alphabet F) c - 1" and lenN: "len_formula ?N1 \<le> N"
          by auto
        have cb_wf: "formula_well_formed (alphabet F) ?cb"
          by (cases b) (simp_all add: true_const_wf false_const_wf)
        have wfN1: "formula_well_formed (alphabet F) ?N1" using ar wfqs lenqs cb_wf by auto
        show "\<exists> lines sz dep. provable_balanced_iff (spira_trans ?N1)
                (Conn (conn_fix c 0 b) (map spira_trans qs)) lines sz dep
              \<and> lines \<le> poly SL N * 4 ^ count_big qs
              \<and> sz \<le> poly SL N * 4 ^ count_big qs
              \<and> real dep \<le> DD * log 2 (real N + 1) + DDC"
        proof (cases "len_formula ?N1 < spira_threshold")
          case True
          have idN1: "spira_trans ?N1 = ?N1"
            by (rule spira_trans_id_when_small[OF wfN1 True])
          have idqs: "map spira_trans qs = qs"
          proof (rule map_idI)
            fix q assume q: "q \<in> set qs"
            have mem: "len_formula q \<in> set (map len_formula qs)" using q by simp
            hence "len_formula q \<le> sum_list (map len_formula qs)"
              by (auto intro: member_le_sum_list)
            also have "\<dots> < len_formula ?N1" by (simp add: len_true_false_const)
            finally have "len_formula q < spira_threshold" using True by simp
            thus "spira_trans q = q" using spira_trans_id_when_small wfqs q by blast
          qed
          have sumle: "sum_list (map len_formula qs) \<le> N"
            using lenN by (simp add: len_true_false_const)
          have wfq': "\<And>q. q \<in> set qs \<Longrightarrow> formula_well_formed (alphabet F) q"
            using wfqs by blast
          have pbi: "provable_balanced_iff (spira_trans ?N1)
                  (Conn (conn_fix c 0 b) (map spira_trans qs))
                  (reduce_lines c b)
                  (reduce_step_len c b * len_sub (set (reduce_atoms c)) (reduce_sub c qs))
                  (reduce_step_depth c b + depth_sub (set (reduce_atoms c)) (reduce_sub c qs))"
            unfolding idN1 idqs using reduce_subst[OF ar lenqs wfq'] .
          \<comment> \<open>lines bound\<close>
          have BL: "reduce_lines c b \<le> poly SL N * 4 ^ count_big qs"
            using order_trans[OF reduce_lines_le Cc_red_l] order_trans[OF CcSL SLpow]
            by (rule order_trans)
          \<comment> \<open>size bound\<close>
          have BS: "reduce_step_len c b * len_sub (set (reduce_atoms c)) (reduce_sub c qs)
                  \<le> poly SL N * 4 ^ count_big qs"
          proof -
            have rs: "reduce_step_len c b \<le> Cc"
              by (rule order_trans[OF reduce_step_len_le Cc_red_s])
            have ls: "len_sub (set (reduce_atoms c)) (reduce_sub c qs) \<le> N + 1"
              using reduce_len_sub[OF lenqs] sumle by simp
            show ?thesis
              using order_trans[OF mult_le_mono[OF rs ls] Cc1SL] SLpow
              by (rule order_trans)
          qed
          \<comment> \<open>depth bound\<close>
          have BD: "real (reduce_step_depth c b
                       + depth_sub (set (reduce_atoms c)) (reduce_sub c qs))
                  \<le> DD * log 2 (real N + 1) + DDC"
          proof -
            have dsub: "depth_sub (set (reduce_atoms c)) (reduce_sub c qs) \<le> spira_threshold"
            proof -
              have "depth_sub (set (reduce_atoms c)) (reduce_sub c qs)
                  = Max (insert 1 (depth_formula ` set qs))"
                by (rule reduce_depth_sub[OF lenqs])
              moreover have "\<forall>x\<in>insert 1 (depth_formula ` set qs). x \<le> spira_threshold"
              proof
                fix x assume "x \<in> insert 1 (depth_formula ` set qs)"
                moreover have "spira_threshold \<ge> 2" unfolding spira_threshold_def by simp
                ultimately consider "x = 1" | q where "q \<in> set qs" "x = depth_formula q" by auto
                thus "x \<le> spira_threshold"
                proof cases
                  case 1 thus ?thesis using \<open>spira_threshold \<ge> 2\<close> by simp
                next
                  case 2
                  have "depth_formula q \<le> len_formula q" by (rule depth_formula_le_len)
                  also have "len_formula q \<le> sum_list (map len_formula qs)"
                    using 2 by (auto intro: member_le_sum_list)
                  also have "\<dots> < len_formula ?N1" by (simp add: len_true_false_const)
                  finally show ?thesis using True 2 by simp
                qed
              qed
              ultimately show ?thesis by simp
            qed
            have rd: "reduce_step_depth c b \<le> Cc"
              by (rule order_trans[OF reduce_step_depth_le Cc_red_d])
            have "reduce_step_depth c b
                 + depth_sub (set (reduce_atoms c)) (reduce_sub c qs)
                \<le> Cc + spira_threshold" by (rule add_le_mono[OF rd dsub])
            hence "real (reduce_step_depth c b
                       + depth_sub (set (reduce_atoms c)) (reduce_sub c qs))
                 \<le> real (Cc + spira_threshold)" by simp
            also have "\<dots> \<le> DDC" unfolding DDC_def by simp
            also have "\<dots> \<le> DD * log 2 (real N + 1) + DDC"
            proof -
              have "0 \<le> DD" unfolding DD_def by simp
              moreover have "0 \<le> log 2 (real N + 1)" by simp
              ultimately show ?thesis by simp
            qed
            finally show ?thesis .
          qed
          show ?thesis using pbi BL BS BD by blast
        next
          case False
          \<comment> \<open>above threshold: a size-\<ge>2 argument slot exists\<close>
          have big: "\<exists>j < length qs. 2 \<le> len_formula (qs ! j)"
          proof (rule ccontr)
            assume nobig: "\<not> (\<exists>j < length qs. 2 \<le> len_formula (qs ! j))"
            have small': "\<forall>x\<in>set qs. len_formula x = 1"
            proof
              fix x assume "x \<in> set qs"
              hence "\<exists>k < length qs. qs ! k = x" by (simp add: in_set_conv_nth)
              then obtain k where k: "k < length qs" and kx: "qs ! k = x" by blast
              have "\<not> 2 \<le> len_formula (qs ! k)" using nobig k by blast
              moreover have "1 \<le> len_formula (qs ! k)" by (rule len_formula_ge_1)
              ultimately show "len_formula x = 1" using kx by simp
            qed
            have "sum_list (map len_formula qs) = length qs"
              by (rule sum_list_map_eq_length[OF small'])
            hence "len_formula ?N1 = arity (alphabet F) c + 1"
              using lenqs ar by (simp add: len_true_false_const)
            moreover have "arity (alphabet F) c + 1 < spira_threshold"
              using arity_le_max[of c] unfolding spira_threshold_def by simp
            ultimately show False using False by simp
          qed
          then obtain j where j_lt: "j < length qs" and j_big: "2 \<le> len_formula (qs ! j)"
            by blast
          have ar0: "0 < arity (alphabet F) c" using ar by simp
          have cf_ar: "arity (alphabet F) (conn_fix c 0 b) = arity (alphabet F) c - 1"
            using conn_fix_spec[of 0 c b] ar0 by simp
          have jc: "j < arity (alphabet F) (conn_fix c 0 b)" using j_lt lenqs cf_ar by simp
          let ?gbar = "map spira_trans qs"
          have gbar_len: "length ?gbar = arity (alphabet F) c - 1" using lenqs by simp
          have gbar_j: "?gbar ! j = spira_trans (qs ! j)" using j_lt by simp
          define m where "m = count_big (qs[j := true_const])"
          have tlt: "len_formula true_const < 2" using true_const_len by simp
          have flt: "len_formula false_const < 2" using false_const_len by simp
          have cbqs: "count_big qs = Suc m"
            unfolding m_def using count_big_update[OF j_lt j_big tlt] by simp
          have cbF: "count_big (qs[j := false_const]) = m"
            using count_big_update[OF j_lt j_big flt] cbqs by simp
          \<comment> \<open>rebalancing of N1 at the chosen slot, and the engine (Lemma 5.1)\<close>
          have rebeq: "rebalancing ?N1 [Suc j]
              = balance (spira_trans (Conn c (?cb # qs[j := true_const])))
                        (spira_trans (Conn c (?cb # qs[j := false_const])))
                        (spira_trans (qs ! j))"
            unfolding rebalancing_def by (simp add: fix_at_zero_suc)
          have validpos: "valid_position ?N1 [Suc j]" using j_lt by simp
          have lenN1_le: "len_formula ?N1 \<le> N" using lenN by simp
          obtain l0 s0 d0 where P0:
            "provable_balanced_iff (spira_trans ?N1) (rebalancing ?N1 [Suc j]) l0 s0 d0"
            and P0l: "l0 \<le> poly bnd_reb (len_formula ?N1)"
            and P0s: "s0 \<le> poly bnd_reb (len_formula ?N1)"
            and P0d: "real d0 \<le> c_reb * log 2 (real (len_formula ?N1) + 1)"
            using reb wfN1 validpos by blast
          \<comment> \<open>the two arms by the induction hypothesis, with their bounds\<close>
          have armB: "\<And>bb. \<exists> l s d. provable_balanced_iff
                  (spira_trans (Conn c (?cb # qs[j := (if bb then true_const else false_const)])))
                  (Conn (conn_fix c 0 b) (?gbar[j := (if bb then true_const else false_const)])) l s d
                \<and> l \<le> poly SL N * 4 ^ m \<and> s \<le> poly SL N * 4 ^ m
                \<and> real d \<le> DD * log 2 (real N + 1) + DDC"
          proof -
            fix bb
            let ?cbb = "if bb then true_const else false_const"
            let ?qsa = "qs[j := ?cbb]"
            have cblt: "len_formula ?cbb < 2" using len_true_false_const by simp
            have meas: "sum_list (map len_formula ?qsa) < sum_list (map len_formula qs)"
            proof -
              have eq: "map len_formula ?qsa = (map len_formula qs)[j := 1]"
                by (simp add: map_update true_const_len false_const_len)
              have "j < length (map len_formula qs)" using j_lt by simp
              moreover have "1 < (map len_formula qs) ! j" using j_lt j_big by simp
              ultimately show ?thesis using eq sum_list_update_lt by simp
            qed
            have wf': "\<forall>q\<in>set ?qsa. formula_well_formed (alphabet F) q"
            proof
              fix q assume "q \<in> set ?qsa"
              hence "q \<in> insert ?cbb (set qs)"
                using set_update_subset_insert by fastforce
              thus "formula_well_formed (alphabet F) q"
                using wfqs by (cases bb) (auto simp: true_const_wf false_const_wf)
            qed
            have len': "length ?qsa = arity (alphabet F) c - 1" using lenqs by simp
            have lenN': "len_formula (Conn c (?cb # ?qsa)) \<le> N"
              using meas lenN by simp
            have cbm: "count_big ?qsa = m"
              unfolding m_def using count_big_update[OF j_lt j_big cblt]
                count_big_update[OF j_lt j_big tlt] by simp
            have "\<exists> lines sz dep. provable_balanced_iff
                    (spira_trans (Conn c (?cb # ?qsa)))
                    (Conn (conn_fix c 0 b) (map spira_trans ?qsa)) lines sz dep
                  \<and> lines \<le> poly SL N * 4 ^ count_big ?qsa
                  \<and> sz \<le> poly SL N * 4 ^ count_big ?qsa
                  \<and> real dep \<le> DD * log 2 (real N + 1) + DDC"
              using less.hyps[OF meas] wf' len' lenN' by blast
            moreover have "map spira_trans ?qsa = ?gbar[j := ?cbb]"
              by (simp add: map_update spira_trans_true_const spira_trans_false_const)
            ultimately show "\<exists> l s d. provable_balanced_iff
                  (spira_trans (Conn c (?cb # ?qsa)))
                  (Conn (conn_fix c 0 b) (?gbar[j := ?cbb])) l s d
                \<and> l \<le> poly SL N * 4 ^ m \<and> s \<le> poly SL N * 4 ^ m
                \<and> real d \<le> DD * log 2 (real N + 1) + DDC"
              using cbm by simp
          qed
          from armB[of True] obtain lT sT dT where PT:
            "provable_balanced_iff (spira_trans (Conn c (?cb # qs[j := true_const])))
               (Conn (conn_fix c 0 b) (?gbar[j := true_const])) lT sT dT"
            and PTl: "lT \<le> poly SL N * 4 ^ m" and PTs: "sT \<le> poly SL N * 4 ^ m"
            and PTd: "real dT \<le> DD * log 2 (real N + 1) + DDC" by auto
          from armB[of False] obtain lF sF dF where PF:
            "provable_balanced_iff (spira_trans (Conn c (?cb # qs[j := false_const])))
               (Conn (conn_fix c 0 b) (?gbar[j := false_const])) lF sF dF"
            and PFl: "lF \<le> poly SL N * 4 ^ m" and PFs: "sF \<le> poly SL N * 4 ^ m"
            and PFd: "real dF \<le> DD * log 2 (real N + 1) + DDC" by auto
          \<comment> \<open>assemble: substitute the arms into the rebalanced selector, then collapse\<close>
          have gbar_len_c: "length ?gbar = arity (alphabet F) (conn_fix c 0 b)"
            using gbar_len cf_ar by simp
          have wf_qsj: "formula_well_formed (alphabet F) (qs ! j)"
            using wfqs j_lt by (simp add: nth_mem)
          have wf_stqsj: "formula_well_formed (alphabet F) (spira_trans (qs ! j))"
            by (rule spira_trans_wf[OF wf_qsj])
          have wf_gbar: "\<And>g. g \<in> set ?gbar \<Longrightarrow> formula_well_formed (alphabet F) g"
          proof -
            fix g assume "g \<in> set ?gbar"
            then obtain q where q: "q \<in> set qs" and geq: "g = spira_trans q" by auto
            from q wfqs have "formula_well_formed (alphabet F) q" by blast
            thus "formula_well_formed (alphabet F) g" unfolding geq by (rule spira_trans_wf)
          qed
          have wf_arm_lhs: "formula_well_formed (alphabet F)
                (spira_trans (Conn c (?cb # qs[j := bc])))"
            if bcwf: "formula_well_formed (alphabet F) bc" for bc
          proof (rule spira_trans_wf)
            have L: "length (?cb # qs[j := bc]) = arity (alphabet F) c"
              using lenqs ar by simp
            have "\<And>f. f \<in> set (?cb # qs[j := bc]) \<Longrightarrow> formula_well_formed (alphabet F) f"
            proof -
              fix f assume "f \<in> set (?cb # qs[j := bc])"
              hence "f = ?cb \<or> f \<in> set (qs[j := bc])" by auto
              thus "formula_well_formed (alphabet F) f"
              proof
                assume "f = ?cb" thus ?thesis using cb_wf by simp
              next
                assume "f \<in> set (qs[j := bc])"
                hence "f \<in> insert bc (set qs)" using set_update_subset_insert by fastforce
                thus ?thesis using wfqs bcwf by auto
              qed
            qed
            with L show "formula_well_formed (alphabet F) (Conn c (?cb # qs[j := bc]))"
              by auto
          qed
          have wf_arm_rhs: "formula_well_formed (alphabet F)
                (Conn (conn_fix c 0 b) (?gbar[j := bc]))"
            if bcwf: "formula_well_formed (alphabet F) bc" for bc
          proof -
            have L: "length (?gbar[j := bc]) = arity (alphabet F) (conn_fix c 0 b)"
              using gbar_len_c by simp
            have "\<And>f. f \<in> set (?gbar[j := bc]) \<Longrightarrow> formula_well_formed (alphabet F) f"
            proof -
              fix f assume "f \<in> set (?gbar[j := bc])"
              hence "f \<in> insert bc (set ?gbar)" using set_update_subset_insert by fastforce
              thus "formula_well_formed (alphabet F) f" using wf_gbar bcwf by auto
            qed
            with L show ?thesis by auto
          qed
          have wf_stN1: "formula_well_formed (alphabet F) (spira_trans ?N1)"
            by (rule spira_trans_wf[OF wfN1])
          have wf_reb: "formula_well_formed (alphabet F) (rebalancing ?N1 [Suc j])"
            by (rule rebalancing_wf[OF wfN1 validpos])
          have wf_balC: "formula_well_formed (alphabet F)
                (balance (Conn (conn_fix c 0 b) (?gbar[j := true_const]))
                         (Conn (conn_fix c 0 b) (?gbar[j := false_const]))
                         (spira_trans (qs ! j)))"
            by (rule balance_wf[OF wf_arm_rhs[OF true_const_wf]
                                   wf_arm_rhs[OF false_const_wf] wf_stqsj])
          have wf_conn_gbar: "formula_well_formed (alphabet F) (Conn (conn_fix c 0 b) ?gbar)"
            using gbar_len_c wf_gbar by auto
          note PB = balance_cong[OF PT PF iff_refl[OF wf_stqsj]
                       wf_arm_lhs[OF true_const_wf] wf_arm_rhs[OF true_const_wf]
                       wf_arm_lhs[OF false_const_wf] wf_arm_rhs[OF false_const_wf]
                       wf_stqsj wf_stqsj]
          note PB' = PB[folded rebeq]
          note shc = shc_subst[OF jc gbar_len_c wf_gbar wf_stqsj]
          have gupd: "?gbar[j := spira_trans (qs ! j)] = ?gbar" using gbar_j[symmetric] by simp
          note shc' = shc[unfolded gupd]
          note comp = iff_trans[OF iff_trans[OF P0 PB' wf_stN1 wf_reb wf_balC]
                                   shc' wf_stN1 wf_balC wf_conn_gbar]
          \<comment> \<open>--- bounds ---\<close>
          have ASLB: "poly SL N \<le> poly SL N * 4 ^ m" by (rule SLpow)
          have Teq: "poly SL N * 4 ^ count_big qs = 4 * (poly SL N * 4 ^ m)"
            using cbqs by simp
          have l0SL: "l0 \<le> poly SL N"
          proof -
            have "l0 \<le> poly bnd_reb N" using P0l poly_nat_mono[OF lenN1_le] order_trans by blast
            thus ?thesis using polySL[of N] by simp
          qed
          have s0SL: "s0 \<le> poly SL N"
          proof -
            have "s0 \<le> poly bnd_reb N" using P0s poly_nat_mono[OF lenN1_le] order_trans by blast
            thus ?thesis using polySL[of N] by simp
          qed
          \<comment> \<open>lines\<close>
          have Lconst: "refl_lines + balance_cong_lines
                      + shc_lines (conn_fix c 0 b) j + 2 * trans_lines \<le> poly SL N"
          proof -
            have "refl_lines + balance_cong_lines + shc_lines (conn_fix c 0 b) j + 2 * trans_lines
                \<le> refl_lines + balance_cong_lines + shc_max_lines + 2 * trans_lines"
              using shc_lines_le[OF jc] by simp
            also have "\<dots> \<le> Cc" unfolding Cc_def by simp
            also have "\<dots> \<le> poly SL N" by (rule CcSL)
            finally show ?thesis .
          qed
          \<comment> \<open>size: bound each formula appearing in the composed proof\<close>
          have wfqsj: "formula_well_formed (alphabet F) (qs ! j)" using wfqs j_lt by simp
          have lenqsj_N: "len_formula (qs ! j) \<le> N"
          proof -
            have "len_formula (qs ! j) \<le> sum_list (map len_formula qs)"
              using j_lt by (auto intro: member_le_sum_list)
            also have "\<dots> \<le> len_formula ?N1" by (simp add: len_true_false_const)
            finally show ?thesis using lenN by simp
          qed
          have szZ: "len_formula (spira_trans (qs ! j)) \<le> poly rebal_tb N"
            by (rule spira_trans_len_le_tb[OF wfqsj lenqsj_N])
          have szN1: "len_formula (spira_trans ?N1) \<le> poly rebal_tb N"
            by (rule spira_trans_len_le_tb[OF wfN1 lenN1_le])
          have gbar_each: "\<And>g. g \<in> set ?gbar \<Longrightarrow> len_formula g \<le> poly rebal_tb N"
          proof -
            fix g assume "g \<in> set ?gbar"
            then obtain i where i: "i < length qs" and gi: "g = spira_trans (qs ! i)"
              by (auto simp: in_set_conv_nth)
            have "formula_well_formed (alphabet F) (qs ! i)" using wfqs i by simp
            moreover have "len_formula (qs ! i) \<le> N"
            proof -
              have "len_formula (qs ! i) \<le> sum_list (map len_formula qs)"
                using i by (auto intro: member_le_sum_list)
              also have "\<dots> \<le> len_formula ?N1" by (simp add: len_true_false_const)
              finally show ?thesis using lenN by simp
            qed
            ultimately show "len_formula g \<le> poly rebal_tb N"
              using gi spira_trans_len_le_tb by blast
          qed
          have gbar_len_MA: "length ?gbar \<le> MA"
            using gbar_len arity_le_max[of c] unfolding MA_def by simp
          have gbar_sum: "sum_list (map len_formula ?gbar) \<le> MA * poly rebal_tb N"
          proof -
            have "sum_list (map len_formula ?gbar) \<le> length ?gbar * poly rebal_tb N"
              by (rule sum_list_map_le) (use gbar_each in simp)
            also have "\<dots> \<le> MA * poly rebal_tb N"
              using gbar_len_MA by (rule mult_le_mono1)
            finally show ?thesis .
          qed
          \<comment> \<open>--- size bounds for every formula in the composed proof ---\<close>
          let ?SU = "(MA + 1) * (poly rebal_tb N + 1)"
          have argupd_T: "sum_list (map len_formula (qs[j := true_const]))
                        \<le> sum_list (map len_formula qs)"
          proof -
            have "map len_formula (qs[j := true_const]) = (map len_formula qs)[j := 1]"
              using true_const_len by (simp add: map_update)
            moreover have "j < length (map len_formula qs)" using j_lt by simp
            moreover have "1 < (map len_formula qs) ! j" using j_lt j_big by simp
            ultimately show ?thesis using sum_list_update_lt by (simp add: less_imp_le)
          qed
          have argupd_F: "sum_list (map len_formula (qs[j := false_const]))
                        \<le> sum_list (map len_formula qs)"
          proof -
            have "map len_formula (qs[j := false_const]) = (map len_formula qs)[j := 1]"
              using false_const_len by (simp add: map_update)
            moreover have "j < length (map len_formula qs)" using j_lt by simp
            moreover have "1 < (map len_formula qs) ! j" using j_lt j_big by simp
            ultimately show ?thesis using sum_list_update_lt by (simp add: less_imp_le)
          qed
          have lenA3: "len_formula (Conn c (?cb # qs[j := true_const])) \<le> N"
          proof -
            have "len_formula (Conn c (?cb # qs[j := true_const])) \<le> len_formula ?N1"
              using argupd_T by simp
            thus ?thesis using lenN by simp
          qed
          have lenA4: "len_formula (Conn c (?cb # qs[j := false_const])) \<le> N"
          proof -
            have "len_formula (Conn c (?cb # qs[j := false_const])) \<le> len_formula ?N1"
              using argupd_F by simp
            thus ?thesis using lenN by simp
          qed
          have wfAe: "\<And>e. formula_well_formed (alphabet F) e \<Longrightarrow>
                  formula_well_formed (alphabet F) (Conn c (?cb # qs[j := e]))"
          proof -
            fix e assume we: "formula_well_formed (alphabet F) e"
            have sub: "set (qs[j := e]) \<subseteq> insert e (set qs)"
              by (rule set_update_subset_insert)
            have "\<forall>g\<in>set (?cb # qs[j := e]). formula_well_formed (alphabet F) g"
              using sub cb_wf we wfqs by auto
            moreover have "length (?cb # qs[j := e]) = arity (alphabet F) c"
              using lenqs ar by simp
            ultimately show "formula_well_formed (alphabet F) (Conn c (?cb # qs[j := e]))"
              by simp
          qed
          have wfA3: "formula_well_formed (alphabet F) (Conn c (?cb # qs[j := true_const]))"
            using wfAe true_const_wf by simp
          have wfA4: "formula_well_formed (alphabet F) (Conn c (?cb # qs[j := false_const]))"
            using wfAe false_const_wf by simp
          have szA3: "len_formula (spira_trans (Conn c (?cb # qs[j := true_const]))) \<le> poly rebal_tb N"
            using spira_trans_len_le_tb[OF wfA3 lenA3] .
          have szA4: "len_formula (spira_trans (Conn c (?cb # qs[j := false_const]))) \<le> poly rebal_tb N"
            using spira_trans_len_le_tb[OF wfA4 lenA4] .
          have gbarT_each: "\<forall>d\<in>set (?gbar[j := true_const]). len_formula d \<le> poly rebal_tb N + 1"
          proof
            fix d assume "d \<in> set (?gbar[j := true_const])"
            hence "d \<in> insert true_const (set ?gbar)" using set_update_subset_insert by fastforce
            thus "len_formula d \<le> poly rebal_tb N + 1"
            proof
              assume "d = true_const" thus ?thesis using true_const_len by simp
            next
              assume dg: "d \<in> set ?gbar"
              have "len_formula d \<le> poly rebal_tb N" using gbar_each[OF dg] .
              thus ?thesis by simp
            qed
          qed
          have gbarF_each: "\<forall>d\<in>set (?gbar[j := false_const]). len_formula d \<le> poly rebal_tb N + 1"
          proof
            fix d assume "d \<in> set (?gbar[j := false_const])"
            hence "d \<in> insert false_const (set ?gbar)" using set_update_subset_insert by fastforce
            thus "len_formula d \<le> poly rebal_tb N + 1"
            proof
              assume "d = false_const" thus ?thesis using false_const_len by simp
            next
              assume dg: "d \<in> set ?gbar"
              have "len_formula d \<le> poly rebal_tb N" using gbar_each[OF dg] .
              thus ?thesis by simp
            qed
          qed
          have szB1: "len_formula (Conn (conn_fix c 0 b) (?gbar[j := true_const])) \<le> ?SU"
          proof -
            have "sum_list (map len_formula (?gbar[j := true_const]))
                \<le> length (?gbar[j := true_const]) * (poly rebal_tb N + 1)"
              by (rule sum_list_map_le[OF gbarT_each])
            also have "\<dots> \<le> MA * (poly rebal_tb N + 1)"
              by (rule mult_le_mono1) (use gbar_len_MA in simp)
            finally show ?thesis by simp
          qed
          have szB2: "len_formula (Conn (conn_fix c 0 b) (?gbar[j := false_const])) \<le> ?SU"
          proof -
            have "sum_list (map len_formula (?gbar[j := false_const]))
                \<le> length (?gbar[j := false_const]) * (poly rebal_tb N + 1)"
              by (rule sum_list_map_le[OF gbarF_each])
            also have "\<dots> \<le> MA * (poly rebal_tb N + 1)"
              by (rule mult_le_mono1) (use gbar_len_MA in simp)
            finally show ?thesis by simp
          qed
          have szB3: "len_formula (Conn (conn_fix c 0 b) ?gbar) \<le> ?SU"
            using gbar_sum by simp
          have szSU: "poly rebal_tb N \<le> ?SU" by simp
          have SU1: "1 \<le> ?SU" by simp
          have szC1: "len_formula (rebalancing ?N1 [Suc j]) \<le> Cc * (4 * ?SU)"
          proof -
            have "len_formula (rebalancing ?N1 [Suc j])
                = len_formula (balance (spira_trans (Conn c (?cb # qs[j := true_const])))
                                       (spira_trans (Conn c (?cb # qs[j := false_const])))
                                       (spira_trans (qs ! j)))" using rebeq by simp
            also have "\<dots> \<le> len_formula custom_balancing
                  * (len_formula (spira_trans (Conn c (?cb # qs[j := true_const])))
                     + len_formula (spira_trans (Conn c (?cb # qs[j := false_const])))
                     + len_formula (spira_trans (qs ! j)) + 1)" by (rule len_balance_le)
            also have "\<dots> \<le> Cc * (4 * ?SU)"
            proof (rule mult_le_mono[OF Cc_cbl])
              show "len_formula (spira_trans (Conn c (?cb # qs[j := true_const])))
                  + len_formula (spira_trans (Conn c (?cb # qs[j := false_const])))
                  + len_formula (spira_trans (qs ! j)) + 1 \<le> 4 * ?SU"
                using szA3 szA4 szZ szSU SU1 by linarith
            qed
            finally show ?thesis .
          qed
          have szC2: "len_formula (balance (Conn (conn_fix c 0 b) (?gbar[j := true_const]))
                                           (Conn (conn_fix c 0 b) (?gbar[j := false_const]))
                                           (spira_trans (qs ! j))) \<le> Cc * (4 * ?SU)"
          proof -
            have "len_formula (balance (Conn (conn_fix c 0 b) (?gbar[j := true_const]))
                                       (Conn (conn_fix c 0 b) (?gbar[j := false_const]))
                                       (spira_trans (qs ! j)))
                \<le> len_formula custom_balancing
                  * (len_formula (Conn (conn_fix c 0 b) (?gbar[j := true_const]))
                     + len_formula (Conn (conn_fix c 0 b) (?gbar[j := false_const]))
                     + len_formula (spira_trans (qs ! j)) + 1)" by (rule len_balance_le)
            also have "\<dots> \<le> Cc * (4 * ?SU)"
            proof (rule mult_le_mono[OF Cc_cbl])
              show "len_formula (Conn (conn_fix c 0 b) (?gbar[j := true_const]))
                  + len_formula (Conn (conn_fix c 0 b) (?gbar[j := false_const]))
                  + len_formula (spira_trans (qs ! j)) + 1 \<le> 4 * ?SU"
                using szB1 szB2 szZ szSU SU1 by linarith
            qed
            finally show ?thesis .
          qed
          have szLsub: "len_sub (set (shc_atoms (conn_fix c 0 b)))
                          (shc_sub (conn_fix c 0 b) ?gbar (spira_trans (qs ! j))) \<le> ?SU"
          proof -
            have "len_sub (set (shc_atoms (conn_fix c 0 b)))
                    (shc_sub (conn_fix c 0 b) ?gbar (spira_trans (qs ! j)))
                = max 1 (sum_list (map len_formula ?gbar) + len_formula (spira_trans (qs ! j)))"
              by (rule shc_len_sub[OF gbar_len_c])
            also have "\<dots> \<le> ?SU" using gbar_sum szZ by simp
            finally show ?thesis .
          qed
          \<comment> \<open>--- products: each summand of the composed size bound ---\<close>
          have W: "?SU \<le> Cc * ?SU" using mult_le_mono1[OF Ccge1, of ?SU] by simp
          have lenZ_SU: "len_formula (spira_trans (qs ! j)) \<le> ?SU" using szZ szSU by simp
          have lenN1_SU: "len_formula (spira_trans ?N1) \<le> ?SU" using szN1 szSU by simp
          have A3_SU: "len_formula (spira_trans (Conn c (?cb # qs[j := true_const]))) \<le> ?SU"
            using szA3 szSU by simp
          have A4_SU: "len_formula (spira_trans (Conn c (?cb # qs[j := false_const]))) \<le> ?SU"
            using szA4 szSU by simp
          have ccfour: "Cc * (4 * ?SU) = 4 * (Cc * ?SU)" by (rule mult.left_commute)
          have lenC1_4: "len_formula (rebalancing ?N1 [Suc j]) \<le> 4 * (Cc * ?SU)"
            by (rule szC1[unfolded ccfour])
          have lenC2_4: "len_formula (balance (Conn (conn_fix c 0 b) (?gbar[j := true_const]))
                                              (Conn (conn_fix c 0 b) (?gbar[j := false_const]))
                                              (spira_trans (qs ! j))) \<le> 4 * (Cc * ?SU)"
            by (rule szC2[unfolded ccfour])
          have shc_sl_Cc: "shc_step_len (conn_fix c 0 b) j \<le> Cc"
            using shc_step_len_le[OF jc] Cc_shc_s by (rule order_trans)
          \<comment> \<open>combos (the parenthesised size sums) are all \<le> 36 (Cc \<cdot> SU)\<close>
          have combo1: "len_formula (spira_trans (qs ! j)) \<le> 36 * (Cc * ?SU)"
            using lenZ_SU W by linarith
          have combo2: "6 * (len_formula (spira_trans (Conn c (?cb # qs[j := true_const])))
                            + len_formula (Conn (conn_fix c 0 b) (?gbar[j := true_const]))
                            + len_formula (spira_trans (Conn c (?cb # qs[j := false_const])))
                            + len_formula (Conn (conn_fix c 0 b) (?gbar[j := false_const]))
                            + len_formula (spira_trans (qs ! j))
                            + len_formula (spira_trans (qs ! j))) \<le> 36 * (Cc * ?SU)"
          proof -
            have "len_formula (spira_trans (Conn c (?cb # qs[j := true_const])))
                + len_formula (Conn (conn_fix c 0 b) (?gbar[j := true_const]))
                + len_formula (spira_trans (Conn c (?cb # qs[j := false_const])))
                + len_formula (Conn (conn_fix c 0 b) (?gbar[j := false_const]))
                + len_formula (spira_trans (qs ! j))
                + len_formula (spira_trans (qs ! j))
                \<le> ?SU + ?SU + ?SU + ?SU + ?SU + ?SU"
              by (intro add_mono A3_SU szB1 A4_SU szB2 lenZ_SU)
            hence "6 * (len_formula (spira_trans (Conn c (?cb # qs[j := true_const])))
                + len_formula (Conn (conn_fix c 0 b) (?gbar[j := true_const]))
                + len_formula (spira_trans (Conn c (?cb # qs[j := false_const])))
                + len_formula (Conn (conn_fix c 0 b) (?gbar[j := false_const]))
                + len_formula (spira_trans (qs ! j))
                + len_formula (spira_trans (qs ! j)))
                \<le> 6 * (?SU + ?SU + ?SU + ?SU + ?SU + ?SU)" by (rule mult_le_mono2)
            also have "6 * (?SU + ?SU + ?SU + ?SU + ?SU + ?SU) = 36 * ?SU" by simp
            also have "36 * ?SU \<le> 36 * (Cc * ?SU)" by (rule mult_le_mono2[OF W])
            finally show ?thesis .
          qed
          have combo3: "len_formula (spira_trans ?N1) + len_formula (rebalancing ?N1 [Suc j])
                      + len_formula (balance (Conn (conn_fix c 0 b) (?gbar[j := true_const]))
                                             (Conn (conn_fix c 0 b) (?gbar[j := false_const]))
                                             (spira_trans (qs ! j))) \<le> 36 * (Cc * ?SU)"
          proof -
            have a: "len_formula (spira_trans ?N1) \<le> Cc * ?SU"
              using lenN1_SU W by (rule order_trans)
            have "len_formula (spira_trans ?N1) + len_formula (rebalancing ?N1 [Suc j])
                + len_formula (balance (Conn (conn_fix c 0 b) (?gbar[j := true_const]))
                                       (Conn (conn_fix c 0 b) (?gbar[j := false_const]))
                                       (spira_trans (qs ! j)))
                \<le> Cc * ?SU + 4 * (Cc * ?SU) + 4 * (Cc * ?SU)"
              by (rule add_mono[OF add_mono[OF a lenC1_4] lenC2_4])
            also have "\<dots> = 9 * (Cc * ?SU)" by simp
            also have "\<dots> \<le> 36 * (Cc * ?SU)" by simp
            finally show ?thesis .
          qed
          have combo4: "len_sub (set (shc_atoms (conn_fix c 0 b)))
                          (shc_sub (conn_fix c 0 b) ?gbar (spira_trans (qs ! j))) \<le> 36 * (Cc * ?SU)"
          proof -
            have "len_sub (set (shc_atoms (conn_fix c 0 b)))
                    (shc_sub (conn_fix c 0 b) ?gbar (spira_trans (qs ! j))) \<le> Cc * ?SU"
              using szLsub W by (rule order_trans)
            also have "Cc * ?SU \<le> 36 * (Cc * ?SU)" by simp
            finally show ?thesis .
          qed
          have combo5: "len_formula (spira_trans ?N1)
                      + len_formula (balance (Conn (conn_fix c 0 b) (?gbar[j := true_const]))
                                             (Conn (conn_fix c 0 b) (?gbar[j := false_const]))
                                             (spira_trans (qs ! j)))
                      + len_formula (Conn (conn_fix c 0 b) ?gbar) \<le> 36 * (Cc * ?SU)"
          proof -
            have a: "len_formula (spira_trans ?N1) \<le> Cc * ?SU"
              using lenN1_SU W by (rule order_trans)
            have b: "len_formula (Conn (conn_fix c 0 b) ?gbar) \<le> Cc * ?SU"
              using szB3 W by (rule order_trans)
            have "len_formula (spira_trans ?N1)
                + len_formula (balance (Conn (conn_fix c 0 b) (?gbar[j := true_const]))
                                       (Conn (conn_fix c 0 b) (?gbar[j := false_const]))
                                       (spira_trans (qs ! j)))
                + len_formula (Conn (conn_fix c 0 b) ?gbar)
                \<le> Cc * ?SU + 4 * (Cc * ?SU) + Cc * ?SU"
              by (rule add_mono[OF add_mono[OF a lenC2_4] b])
            also have "\<dots> = 6 * (Cc * ?SU)" by simp
            also have "\<dots> \<le> 36 * (Cc * ?SU)" by simp
            finally show ?thesis .
          qed
          have P1: "refl_step_len * len_formula (spira_trans (qs ! j)) \<le> 36 * (Cc * (Cc * ?SU))"
            using mult_le_mono[OF Cc_rfsl combo1] by (simp add: ac_simps)
          have P2: "balance_cong_step_len
                    * (6 * (len_formula (spira_trans (Conn c (?cb # qs[j := true_const])))
                            + len_formula (Conn (conn_fix c 0 b) (?gbar[j := true_const]))
                            + len_formula (spira_trans (Conn c (?cb # qs[j := false_const])))
                            + len_formula (Conn (conn_fix c 0 b) (?gbar[j := false_const]))
                            + len_formula (spira_trans (qs ! j))
                            + len_formula (spira_trans (qs ! j))))
                  \<le> 36 * (Cc * (Cc * ?SU))"
            using mult_le_mono[OF Cc_bcsl combo2] by (simp add: ac_simps)
          have P3: "trans_step_len * (len_formula (spira_trans ?N1)
                      + len_formula (rebalancing ?N1 [Suc j])
                      + len_formula (balance (Conn (conn_fix c 0 b) (?gbar[j := true_const]))
                                             (Conn (conn_fix c 0 b) (?gbar[j := false_const]))
                                             (spira_trans (qs ! j))))
                  \<le> 36 * (Cc * (Cc * ?SU))"
            using mult_le_mono[OF Cc_tsl combo3] by (simp add: ac_simps)
          have P4: "shc_step_len (conn_fix c 0 b) j
                    * len_sub (set (shc_atoms (conn_fix c 0 b)))
                              (shc_sub (conn_fix c 0 b) ?gbar (spira_trans (qs ! j)))
                  \<le> 36 * (Cc * (Cc * ?SU))"
            using mult_le_mono[OF shc_sl_Cc combo4] by (simp add: ac_simps)
          have P5: "trans_step_len * (len_formula (spira_trans ?N1)
                      + len_formula (balance (Conn (conn_fix c 0 b) (?gbar[j := true_const]))
                                             (Conn (conn_fix c 0 b) (?gbar[j := false_const]))
                                             (spira_trans (qs ! j)))
                      + len_formula (Conn (conn_fix c 0 b) ?gbar))
                  \<le> 36 * (Cc * (Cc * ?SU))"
            using mult_le_mono[OF Cc_tsl combo5] by (simp add: ac_simps)
          have SZclean: "5 * (36 * (Cc * (Cc * ?SU))) \<le> poly SL N"
          proof -
            have "5 * (36 * (Cc * (Cc * ?SU))) \<le> Cc * (Cc * (Cc * ?SU))"
              using Ccbig by (simp add: mult_le_mono1 mult.assoc)
            also have "Cc * (Cc * (Cc * ?SU))
                     = Cc * Cc * Cc * (MA + 1) * poly rebal_tb N + Cc * Cc * Cc * (MA + 1)"
              by (simp add: algebra_simps)
            also have "\<dots> \<le> poly SL N" using polySL[of N] by simp
            finally show ?thesis .
          qed
          \<comment> \<open>--- depth bound ---\<close>
          let ?LGN = "DD * log 2 (real N + 1)"
          have N2: "2 \<le> N" using j_big lenqsj_N by linarith
          have logpos: "0 \<le> log 2 (real N + 1)" by simp
          have log1: "1 \<le> log 2 (real N + 1)"
          proof -
            have "(2::real) \<le> real N + 1" using N2 by simp
            hence "log 2 2 \<le> log 2 (real N + 1)" by (intro log_mono) auto
            thus ?thesis by simp
          qed
          have DD1: "1 \<le> DD" unfolding DD_def by simp
          have DDtc: "max tc 1 \<le> DD" unfolding DD_def by simp
          have DDcreb: "c_reb \<le> DD" unfolding DD_def by simp
          have DDpos: "0 \<le> DD" using DD1 by simp
          have LGNpos: "0 \<le> ?LGN" using DD1 logpos by simp
          have LGN1: "1 \<le> ?LGN" using mult_mono[OF DD1 log1 DDpos zero_le_one] by simp
          \<comment> \<open>t-image depths\<close>
          have dN1: "real (depth_formula (spira_trans ?N1)) \<le> ?LGN"
            by (rule order_trans[OF spira_trans_dep_le[OF tc wfN1 lenN1_le]
                                    mult_right_mono[OF DDtc logpos]])
          have dZ: "real (depth_formula (spira_trans (qs ! j))) \<le> ?LGN"
            by (rule order_trans[OF spira_trans_dep_le[OF tc wfqsj lenqsj_N]
                                    mult_right_mono[OF DDtc logpos]])
          have dA3: "real (depth_formula (spira_trans (Conn c (?cb # qs[j := true_const])))) \<le> ?LGN"
            by (rule order_trans[OF spira_trans_dep_le[OF tc wfA3 lenA3]
                                    mult_right_mono[OF DDtc logpos]])
          have dA4: "real (depth_formula (spira_trans (Conn c (?cb # qs[j := false_const])))) \<le> ?LGN"
            by (rule order_trans[OF spira_trans_dep_le[OF tc wfA4 lenA4]
                                    mult_right_mono[OF DDtc logpos]])
          \<comment> \<open>connective-node depths\<close>
          have gbar_dep: "\<And>g. g \<in> set ?gbar \<Longrightarrow> real (depth_formula g) \<le> ?LGN"
          proof -
            fix g assume "g \<in> set ?gbar"
            then obtain i where i: "i < length qs" and gi: "g = spira_trans (qs ! i)"
              by (auto simp: in_set_conv_nth)
            have wfi: "formula_well_formed (alphabet F) (qs ! i)" using wfqs i by simp
            have leni: "len_formula (qs ! i) \<le> N"
            proof -
              have "len_formula (qs ! i) \<le> sum_list (map len_formula qs)"
                using i by (auto intro: member_le_sum_list)
              thus ?thesis using lenN by simp
            qed
            show "real (depth_formula g) \<le> ?LGN" unfolding gi
              by (rule order_trans[OF spira_trans_dep_le[OF tc wfi leni]
                                      mult_right_mono[OF DDtc logpos]])
          qed
          have gbar_dep_all: "\<forall>g\<in>set ?gbar. real (depth_formula g) \<le> ?LGN"
            using gbar_dep by blast
          have tc_dep_le: "depth_formula true_const \<le> 1"
            using depth_formula_le_len[of true_const] true_const_len by simp
          have fc_dep_le: "depth_formula false_const \<le> 1"
            using depth_formula_le_len[of false_const] false_const_len by simp
          have gbarT_dep: "\<forall>g\<in>set (?gbar[j := true_const]). real (depth_formula g) \<le> ?LGN + 1"
          proof
            fix g assume "g \<in> set (?gbar[j := true_const])"
            hence "g \<in> insert true_const (set ?gbar)" using set_update_subset_insert by fastforce
            thus "real (depth_formula g) \<le> ?LGN + 1"
            proof
              assume "g = true_const"
              hence "real (depth_formula g) \<le> 1" using tc_dep_le by simp
              thus ?thesis using LGNpos by simp
            next
              assume "g \<in> set ?gbar" thus ?thesis using gbar_dep[of g] by simp
            qed
          qed
          have gbarF_dep: "\<forall>g\<in>set (?gbar[j := false_const]). real (depth_formula g) \<le> ?LGN + 1"
          proof
            fix g assume "g \<in> set (?gbar[j := false_const])"
            hence "g \<in> insert false_const (set ?gbar)" using set_update_subset_insert by fastforce
            thus "real (depth_formula g) \<le> ?LGN + 1"
            proof
              assume "g = false_const"
              hence "real (depth_formula g) \<le> 1" using fc_dep_le by simp
              thus ?thesis using LGNpos by simp
            next
              assume "g \<in> set ?gbar" thus ?thesis using gbar_dep[of g] by simp
            qed
          qed
          have dB1: "real (depth_formula (Conn (conn_fix c 0 b) (?gbar[j := true_const]))) \<le> ?LGN + 2"
          proof -
            have "0 \<le> ?LGN + 1" using LGNpos by simp
            from conn_dep_le[OF gbarT_dep this] show ?thesis by simp
          qed
          have dB2: "real (depth_formula (Conn (conn_fix c 0 b) (?gbar[j := false_const]))) \<le> ?LGN + 2"
          proof -
            have "0 \<le> ?LGN + 1" using LGNpos by simp
            from conn_dep_le[OF gbarF_dep this] show ?thesis by simp
          qed
          have dB3: "real (depth_formula (Conn (conn_fix c 0 b) ?gbar)) \<le> ?LGN + 2"
          proof -
            from conn_dep_le[OF gbar_dep_all LGNpos] show ?thesis by simp
          qed
          \<comment> \<open>balance-node depths\<close>
          have dreb: "real (depth_formula (rebalancing ?N1 [Suc j]))
                    \<le> real (depth_formula custom_balancing) + ?LGN"
          proof -
            have "real (depth_formula (rebalancing ?N1 [Suc j]))
                = real (depth_formula (balance (spira_trans (Conn c (?cb # qs[j := true_const])))
                                               (spira_trans (Conn c (?cb # qs[j := false_const])))
                                               (spira_trans (qs ! j))))" using rebeq by simp
            also have "\<dots> \<le> real (depth_formula custom_balancing) + ?LGN"
              by (rule balance_dep_le[OF dA3 dA4 dZ LGN1])
            finally show ?thesis .
          qed
          have dZ2: "real (depth_formula (spira_trans (qs ! j))) \<le> ?LGN + 2" using dZ by simp
          have LGN2_1: "(1::real) \<le> ?LGN + 2" using LGNpos by simp
          have dC2: "real (depth_formula (balance (Conn (conn_fix c 0 b) (?gbar[j := true_const]))
                                                  (Conn (conn_fix c 0 b) (?gbar[j := false_const]))
                                                  (spira_trans (qs ! j))))
                   \<le> real (depth_formula custom_balancing) + (?LGN + 2)"
            by (rule balance_dep_le[OF dB1 dB2 dZ2 LGN2_1])
          \<comment> \<open>the shc substitution depth\<close>
          have ddsub: "real (depth_sub (set (shc_atoms (conn_fix c 0 b)))
                              (shc_sub (conn_fix c 0 b) ?gbar (spira_trans (qs ! j)))) \<le> ?LGN + 1"
          proof -
            have eq: "depth_sub (set (shc_atoms (conn_fix c 0 b)))
                        (shc_sub (conn_fix c 0 b) ?gbar (spira_trans (qs ! j)))
                    = Max (insert 1 (depth_formula ` set (?gbar @ [spira_trans (qs ! j)])))"
              by (rule shc_depth_sub[OF gbar_len_c])
            have bnd: "\<forall>x\<in>insert 1 (depth_formula ` set (?gbar @ [spira_trans (qs ! j)])).
                         real x \<le> ?LGN + 1"
            proof
              fix x assume "x \<in> insert 1 (depth_formula ` set (?gbar @ [spira_trans (qs ! j)]))"
              then consider "x = 1"
                | g where "g \<in> set (?gbar @ [spira_trans (qs ! j)])" "x = depth_formula g" by auto
              thus "real x \<le> ?LGN + 1"
              proof cases
                case 1 thus ?thesis using LGNpos by simp
              next
                case 2
                have "g \<in> set ?gbar \<or> g = spira_trans (qs ! j)" using 2(1) by auto
                thus ?thesis
                proof
                  assume "g \<in> set ?gbar" thus ?thesis using gbar_dep[of g] 2(2) by simp
                next
                  assume "g = spira_trans (qs ! j)" thus ?thesis using dZ 2(2) by simp
                qed
              qed
            qed
            have "Max (insert 1 (depth_formula ` set (?gbar @ [spira_trans (qs ! j)])))
                    \<in> insert 1 (depth_formula ` set (?gbar @ [spira_trans (qs ! j)]))"
              by (intro Max_in) auto
            hence "real (Max (insert 1 (depth_formula ` set (?gbar @ [spira_trans (qs ! j)]))))
                 \<le> ?LGN + 1" using bnd by blast
            thus ?thesis unfolding eq .
          qed
          \<comment> \<open>the rebalancing engine's depth d0\<close>
          have D_d0: "real d0 \<le> ?LGN"
          proof -
            have lN1: "log 2 (real (len_formula ?N1) + 1) \<le> log 2 (real N + 1)"
              using lenN1_le by (intro log_mono) auto
            have lN1pos: "0 \<le> log 2 (real (len_formula ?N1) + 1)"
            proof -
              have "(1::real) \<le> real (len_formula ?N1) + 1" by simp
              hence "log 2 1 \<le> log 2 (real (len_formula ?N1) + 1)" by (intro log_mono) auto
              thus ?thesis by simp
            qed
            have "real d0 \<le> c_reb * log 2 (real (len_formula ?N1) + 1)" by (rule P0d)
            also have "\<dots> \<le> ?LGN"
            proof (cases "c_reb \<le> 0")
              case True
              have "c_reb * log 2 (real (len_formula ?N1) + 1) \<le> 0"
                using True lN1pos mult_nonpos_nonneg by blast
              thus ?thesis using LGNpos by simp
            next
              case False
              hence cpos: "0 \<le> c_reb" by simp
              have "c_reb * log 2 (real (len_formula ?N1) + 1) \<le> c_reb * log 2 (real N + 1)"
                using lN1 cpos by (rule mult_left_mono)
              also have "\<dots> \<le> ?LGN" using DDcreb logpos by (rule mult_right_mono)
              finally show ?thesis .
            qed
            finally show ?thesis .
          qed
          \<comment> \<open>constant additive budgets, all absorbed by DDC\<close>
          have DDCpos: "0 \<le> DDC" unfolding DDC_def by simp
          have crefl: "real refl_step_depth \<le> DDC"
            using Cc_rfsd unfolding DDC_def by simp
          have cbcsd2: "real balance_cong_step_depth + 2 \<le> DDC"
            using Cc_bcsd unfolding DDC_def by simp
          have ctsd_cb2: "real trans_step_depth + real (depth_formula custom_balancing) + 2 \<le> DDC"
          proof -
            have "trans_step_depth + depth_formula custom_balancing \<le> 2 * Cc"
              using Cc_tsd Cc_cbd by linarith
            thus ?thesis unfolding DDC_def by simp
          qed
          have cshc1: "real (shc_step_depth (conn_fix c 0 b) j) + 1 \<le> DDC"
          proof -
            have "shc_step_depth (conn_fix c 0 b) j \<le> Cc"
              by (rule order_trans[OF shc_step_depth_le[OF jc] Cc_shc_d])
            thus ?thesis unfolding DDC_def by simp
          qed
          \<comment> \<open>leaf bounds: every leaf of comp's depth is \<le> ?LGN + DDC\<close>
          have DL1: "real d0 \<le> ?LGN + DDC" using D_d0 DDCpos by simp
          have DL2: "real dT \<le> ?LGN + DDC" by (rule PTd)
          have DL3: "real dF \<le> ?LGN + DDC" by (rule PFd)
          have DL4: "real (refl_step_depth + depth_formula (spira_trans (qs ! j))) \<le> ?LGN + DDC"
          proof -
            have "real (refl_step_depth + depth_formula (spira_trans (qs ! j)))
                = real refl_step_depth + real (depth_formula (spira_trans (qs ! j)))" by simp
            also have "\<dots> \<le> DDC + ?LGN" using crefl dZ by linarith
            finally show ?thesis by (simp add: add.commute)
          qed
          have dA3w: "real (depth_formula (spira_trans (Conn c (?cb # qs[j := true_const]))))
                      \<le> ?LGN + 2" using dA3 by simp
          have dA4w: "real (depth_formula (spira_trans (Conn c (?cb # qs[j := false_const]))))
                      \<le> ?LGN + 2" using dA4 by simp
          have dZw: "real (depth_formula (spira_trans (qs ! j))) \<le> ?LGN + 2"
            using dZ by simp
          have dmax6: "real (max (depth_formula (spira_trans (Conn c (?cb # qs[j := true_const]))))
                  (max (depth_formula (Conn (conn_fix c 0 b) (?gbar[j := true_const])))
                  (max (depth_formula (spira_trans (Conn c (?cb # qs[j := false_const]))))
                  (max (depth_formula (Conn (conn_fix c 0 b) (?gbar[j := false_const])))
                  (max (depth_formula (spira_trans (qs ! j)))
                       (depth_formula (spira_trans (qs ! j))))))))
                \<le> ?LGN + 2"
            by (rule real_of_nat_max_le dA3w dB1 dA4w dB2 dZw)+
          have DL5: "real (balance_cong_step_depth
                  + max (depth_formula (spira_trans (Conn c (?cb # qs[j := true_const]))))
                  (max (depth_formula (Conn (conn_fix c 0 b) (?gbar[j := true_const])))
                  (max (depth_formula (spira_trans (Conn c (?cb # qs[j := false_const]))))
                  (max (depth_formula (Conn (conn_fix c 0 b) (?gbar[j := false_const])))
                  (max (depth_formula (spira_trans (qs ! j)))
                       (depth_formula (spira_trans (qs ! j)))))))) \<le> ?LGN + DDC"
          proof -
            have "real (balance_cong_step_depth + max (depth_formula (spira_trans (Conn c (?cb # qs[j := true_const]))))
                  (max (depth_formula (Conn (conn_fix c 0 b) (?gbar[j := true_const])))
                  (max (depth_formula (spira_trans (Conn c (?cb # qs[j := false_const]))))
                  (max (depth_formula (Conn (conn_fix c 0 b) (?gbar[j := false_const])))
                  (max (depth_formula (spira_trans (qs ! j)))
                       (depth_formula (spira_trans (qs ! j))))))))
                = real balance_cong_step_depth
                  + real (max (depth_formula (spira_trans (Conn c (?cb # qs[j := true_const]))))
                  (max (depth_formula (Conn (conn_fix c 0 b) (?gbar[j := true_const])))
                  (max (depth_formula (spira_trans (Conn c (?cb # qs[j := false_const]))))
                  (max (depth_formula (Conn (conn_fix c 0 b) (?gbar[j := false_const])))
                  (max (depth_formula (spira_trans (qs ! j)))
                       (depth_formula (spira_trans (qs ! j))))))))" by (rule of_nat_add)
            also have "\<dots> \<le> ?LGN + DDC" using dmax6 cbcsd2 by linarith
            finally show ?thesis .
          qed
          have DL6: "real (trans_step_depth + max (depth_formula (spira_trans ?N1))
                  (max (depth_formula (rebalancing ?N1 [Suc j]))
                       (depth_formula (balance (Conn (conn_fix c 0 b) (?gbar[j := true_const]))
                                               (Conn (conn_fix c 0 b) (?gbar[j := false_const]))
                                               (spira_trans (qs ! j)))))) \<le> ?LGN + DDC"
          proof -
            have dN1_M: "real (depth_formula (spira_trans ?N1))
                       \<le> real (depth_formula custom_balancing) + (?LGN + 2)" using dN1 by simp
            have dreb_M: "real (depth_formula (rebalancing ?N1 [Suc j]))
                        \<le> real (depth_formula custom_balancing) + (?LGN + 2)" using dreb by simp
            have "real (max (depth_formula (spira_trans ?N1))
                  (max (depth_formula (rebalancing ?N1 [Suc j]))
                       (depth_formula (balance (Conn (conn_fix c 0 b) (?gbar[j := true_const]))
                                               (Conn (conn_fix c 0 b) (?gbar[j := false_const]))
                                               (spira_trans (qs ! j))))))
                \<le> real (depth_formula custom_balancing) + (?LGN + 2)"
              using dN1_M dreb_M dC2 by (simp add: of_nat_max)
            hence "real (trans_step_depth + max (depth_formula (spira_trans ?N1))
                  (max (depth_formula (rebalancing ?N1 [Suc j]))
                       (depth_formula (balance (Conn (conn_fix c 0 b) (?gbar[j := true_const]))
                                               (Conn (conn_fix c 0 b) (?gbar[j := false_const]))
                                               (spira_trans (qs ! j))))))
                \<le> real trans_step_depth + (real (depth_formula custom_balancing) + (?LGN + 2))"
              by simp
            also have "\<dots> \<le> ?LGN + DDC" using ctsd_cb2 by linarith
            finally show ?thesis .
          qed
          have DL7: "real (shc_step_depth (conn_fix c 0 b) j
                  + depth_sub (set (shc_atoms (conn_fix c 0 b)))
                              (shc_sub (conn_fix c 0 b) ?gbar (spira_trans (qs ! j)))) \<le> ?LGN + DDC"
          proof -
            have "real (shc_step_depth (conn_fix c 0 b) j
                  + depth_sub (set (shc_atoms (conn_fix c 0 b)))
                              (shc_sub (conn_fix c 0 b) ?gbar (spira_trans (qs ! j))))
                = real (shc_step_depth (conn_fix c 0 b) j)
                  + real (depth_sub (set (shc_atoms (conn_fix c 0 b)))
                              (shc_sub (conn_fix c 0 b) ?gbar (spira_trans (qs ! j))))" by simp
            also have "\<dots> \<le> ?LGN + DDC" using ddsub cshc1 by linarith
            finally show ?thesis .
          qed
          have DL8: "real (trans_step_depth + max (depth_formula (spira_trans ?N1))
                  (max (depth_formula (balance (Conn (conn_fix c 0 b) (?gbar[j := true_const]))
                                               (Conn (conn_fix c 0 b) (?gbar[j := false_const]))
                                               (spira_trans (qs ! j))))
                       (depth_formula (Conn (conn_fix c 0 b) ?gbar)))) \<le> ?LGN + DDC"
          proof -
            have dN1_M: "real (depth_formula (spira_trans ?N1))
                       \<le> real (depth_formula custom_balancing) + (?LGN + 2)" using dN1 by simp
            have dB3_M: "real (depth_formula (Conn (conn_fix c 0 b) ?gbar))
                       \<le> real (depth_formula custom_balancing) + (?LGN + 2)" using dB3 by simp
            have "real (max (depth_formula (spira_trans ?N1))
                  (max (depth_formula (balance (Conn (conn_fix c 0 b) (?gbar[j := true_const]))
                                               (Conn (conn_fix c 0 b) (?gbar[j := false_const]))
                                               (spira_trans (qs ! j))))
                       (depth_formula (Conn (conn_fix c 0 b) ?gbar))))
                \<le> real (depth_formula custom_balancing) + (?LGN + 2)"
              using dN1_M dC2 dB3_M by (simp add: of_nat_max)
            hence "real (trans_step_depth + max (depth_formula (spira_trans ?N1))
                  (max (depth_formula (balance (Conn (conn_fix c 0 b) (?gbar[j := true_const]))
                                               (Conn (conn_fix c 0 b) (?gbar[j := false_const]))
                                               (spira_trans (qs ! j))))
                       (depth_formula (Conn (conn_fix c 0 b) ?gbar))))
                \<le> real trans_step_depth + (real (depth_formula custom_balancing) + (?LGN + 2))"
              by simp
            also have "\<dots> \<le> ?LGN + DDC" using ctsd_cb2 by linarith
            finally show ?thesis .
          qed
          \<comment> \<open>assemble the witness from comp and discharge the three bounds\<close>
          show ?thesis
            apply (intro exI conjI)
                 apply (rule comp)
                apply blast
               apply (use l0SL PTl PFl Lconst ASLB Teq in linarith)
              apply (use P1 P2 P3 P4 P5 SZclean s0SL PTs PFs ASLB Teq in linarith)
             apply (rule real_of_nat_max_le DL1 DL2 DL3 DL4 DL5 DL6 DL7 DL8)+
            done
        qed
      qed
    qed
  qed
  show ?thesis using main by blast
qed

subsection \<open>Bounded collapse\<close>

lemma collapse:
  shows "\<exists> Kc :: nat. \<forall> c gbar z.
           1 \<le> arity (alphabet F) c \<and> length gbar = arity (alphabet F) c - 1
           \<and> (\<forall>g\<in>set gbar. formula_well_formed (alphabet F) g)
           \<and> formula_well_formed (alphabet F) z
         \<longrightarrow> (\<exists> lines sz dep. provable_balanced_iff
                (balance (Conn (conn_fix c 0 True) gbar) (Conn (conn_fix c 0 False) gbar) z)
                (Conn c (z # gbar)) lines sz dep
              \<and> lines \<le> Kc
              \<and> sz \<le> Kc * (len_formula (Conn c (z # gbar)) + 1)
              \<and> real dep \<le> real Kc * (real (depth_formula (Conn c (z # gbar))) + 1))"
proof -
  define Cc :: nat where
    "Cc = reduce_max_lines + reduce_max_step_len + reduce_max_step_depth
        + shc_max_lines + shc_max_step_len + shc_max_step_depth
        + balance_cong_lines + balance_cong_step_len + balance_cong_step_depth
        + trans_lines + trans_step_len + trans_step_depth
        + refl_lines + refl_step_len + refl_step_depth
        + sym_lines + sym_step_len + sym_step_depth
        + len_formula custom_balancing + depth_formula custom_balancing + 1"
  define Kc :: nat where "Kc = 1000 * Cc * Cc"
  have Ccge1: "1 \<le> Cc" unfolding Cc_def by simp
  have C_rml: "reduce_max_lines \<le> Cc" unfolding Cc_def by simp
  have C_rmsl: "reduce_max_step_len \<le> Cc" unfolding Cc_def by simp
  have C_rmsd: "reduce_max_step_depth \<le> Cc" unfolding Cc_def by simp
  have C_smll: "shc_max_lines \<le> Cc" unfolding Cc_def by simp
  have C_smsl: "shc_max_step_len \<le> Cc" unfolding Cc_def by simp
  have C_smsd: "shc_max_step_depth \<le> Cc" unfolding Cc_def by simp
  have C_bcl: "balance_cong_lines \<le> Cc" unfolding Cc_def by simp
  have C_bcsl: "balance_cong_step_len \<le> Cc" unfolding Cc_def by simp
  have C_bcsd: "balance_cong_step_depth \<le> Cc" unfolding Cc_def by simp
  have C_tl: "trans_lines \<le> Cc" unfolding Cc_def by simp
  have C_tsl: "trans_step_len \<le> Cc" unfolding Cc_def by simp
  have C_tsd: "trans_step_depth \<le> Cc" unfolding Cc_def by simp
  have C_rfl: "refl_lines \<le> Cc" unfolding Cc_def by simp
  have C_rfsl: "refl_step_len \<le> Cc" unfolding Cc_def by simp
  have C_rfsd: "refl_step_depth \<le> Cc" unfolding Cc_def by simp
  have C_syl: "sym_lines \<le> Cc" unfolding Cc_def by simp
  have C_sysl: "sym_step_len \<le> Cc" unfolding Cc_def by simp
  have C_sysd: "sym_step_depth \<le> Cc" unfolding Cc_def by simp
  have C_cb: "len_formula custom_balancing \<le> Cc" unfolding Cc_def by simp
  have C_dcb: "depth_formula custom_balancing \<le> Cc" unfolding Cc_def by simp
  have h1: "(1::nat) \<le> 1000 * Cc"
  proof -
    have "(1::nat) \<le> 1000 * 1" by simp
    also have "(1000::nat) * 1 \<le> 1000 * Cc" using Ccge1 by (rule mult_le_mono2)
    finally show ?thesis .
  qed
  have CcKc: "Cc \<le> Kc"
  proof -
    have "Cc * 1 \<le> Cc * (1000 * Cc)" using h1 by (rule mult_le_mono2)
    thus ?thesis unfolding Kc_def by (simp add: ac_simps)
  qed
  have Kcbig: "1000 \<le> Kc"
  proof -
    have "1 \<le> Cc * Cc" using mult_le_mono[OF Ccge1 Ccge1] by simp
    hence "1000 * 1 \<le> 1000 * (Cc * Cc)" by (rule mult_le_mono2)
    thus ?thesis unfolding Kc_def by (simp add: mult.assoc)
  qed
  have Kcge3: "3 \<le> Kc" using Kcbig by simp
  have C8: "8 * Cc \<le> Kc"
  proof -
    have "(1000 * Cc) * 1 \<le> (1000 * Cc) * Cc" using Ccge1 by (rule mult_le_mono2)
    hence "1000 * Cc \<le> 1000 * Cc * Cc" by (simp add: mult.assoc)
    moreover have "8 * Cc \<le> 1000 * Cc" by simp
    ultimately show ?thesis unfolding Kc_def by linarith
  qed
  have main: "\<And> c gbar z. 1 \<le> arity (alphabet F) c \<Longrightarrow>
       length gbar = arity (alphabet F) c - 1 \<Longrightarrow>
       (\<forall>g\<in>set gbar. formula_well_formed (alphabet F) g) \<Longrightarrow>
       formula_well_formed (alphabet F) z \<Longrightarrow>
       (\<exists> lines sz dep. provable_balanced_iff
          (balance (Conn (conn_fix c 0 True) gbar) (Conn (conn_fix c 0 False) gbar) z)
          (Conn c (z # gbar)) lines sz dep
        \<and> lines \<le> Kc
        \<and> sz \<le> Kc * (len_formula (Conn c (z # gbar)) + 1)
        \<and> real dep \<le> real Kc * (real (depth_formula (Conn c (z # gbar))) + 1))"
  proof -
    fix c :: 'a and gbar :: "'a formula list" and z :: "'a formula"
    assume ar: "1 \<le> arity (alphabet F) c"
      and len: "length gbar = arity (alphabet F) c - 1"
      and wfgbar: "\<forall>g\<in>set gbar. formula_well_formed (alphabet F) g"
      and wfz: "formula_well_formed (alphabet F) z"
    have wfgbar': "\<And>g. g \<in> set gbar \<Longrightarrow> formula_well_formed (alphabet F) g"
      using wfgbar by blast
    have wfzgbar: "\<And>g. g \<in> set (z # gbar) \<Longrightarrow> formula_well_formed (alphabet F) g"
      using wfz wfgbar by auto
    have ar0: "0 < arity (alphabet F) c" using ar by simp
    have lenz: "length (z # gbar) = arity (alphabet F) c" using len ar by simp
    let ?LL = "len_formula (Conn c (z # gbar))"
    let ?DL = "depth_formula (Conn c (z # gbar))"
    define W :: nat where "W = Cc * Cc * (?LL + 1)"
    \<comment> \<open>length facts\<close>
    have LLval: "?LL = Suc (len_formula z + sum_list (map len_formula gbar))"
      by simp
    have SGle: "sum_list (map len_formula gbar) \<le> ?LL" using LLval by simp
    have lenZle: "len_formula z \<le> ?LL" using LLval by simp
    have Lv_tg: "len_formula (Conn c (true_const # gbar))
                   = 2 + sum_list (map len_formula gbar)" by (simp add: true_const_len)
    have Lv_fg: "len_formula (Conn c (false_const # gbar))
                   = 2 + sum_list (map len_formula gbar)" by (simp add: false_const_len)
    have Lv_cftg: "len_formula (Conn (conn_fix c 0 True) gbar)
                     = 1 + sum_list (map len_formula gbar)" by simp
    have Lv_cffg: "len_formula (Conn (conn_fix c 0 False) gbar)
                     = 1 + sum_list (map len_formula gbar)" by simp
    \<comment> \<open>depth facts\<close>
    have DLge1: "1 \<le> ?DL" by simp
    have dz: "depth_formula z \<le> ?DL"
      using depth_elt_le_conn[of z "z # gbar" c] by simp
    have dg: "\<forall>g\<in>set gbar. depth_formula g \<le> ?DL"
    proof
      fix g assume "g \<in> set gbar"
      hence "g \<in> set (z # gbar)" by simp
      thus "depth_formula g \<le> ?DL" using depth_elt_le_conn[of g "z # gbar" c] by simp
    qed
    have d_tg: "depth_formula (Conn c (true_const # gbar)) \<le> ?DL + 1"
    proof (rule conn_dep_le_nat)
      show "\<forall>g\<in>set (true_const # gbar). depth_formula g \<le> ?DL"
      proof
        fix g assume "g \<in> set (true_const # gbar)"
        then consider "g = true_const" | "g \<in> set gbar" by auto
        thus "depth_formula g \<le> ?DL"
        proof cases
          case 1
          have "depth_formula true_const \<le> 1"
            using depth_formula_le_len[of true_const] true_const_len by simp
          thus ?thesis using 1 DLge1 by simp
        next
          case 2 thus ?thesis using dg by simp
        qed
      qed
    qed
    have d_fg: "depth_formula (Conn c (false_const # gbar)) \<le> ?DL + 1"
    proof (rule conn_dep_le_nat)
      show "\<forall>g\<in>set (false_const # gbar). depth_formula g \<le> ?DL"
      proof
        fix g assume "g \<in> set (false_const # gbar)"
        then consider "g = false_const" | "g \<in> set gbar" by auto
        thus "depth_formula g \<le> ?DL"
        proof cases
          case 1
          have "depth_formula false_const \<le> 1"
            using depth_formula_le_len[of false_const] false_const_len by simp
          thus ?thesis using 1 DLge1 by simp
        next
          case 2 thus ?thesis using dg by simp
        qed
      qed
    qed
    have d_cftg: "depth_formula (Conn (conn_fix c 0 True) gbar) \<le> ?DL + 1"
      by (rule conn_dep_le_nat) (use dg in simp)
    have d_cffg: "depth_formula (Conn (conn_fix c 0 False) gbar) \<le> ?DL + 1"
      by (rule conn_dep_le_nat) (use dg in simp)
    have dsub_red: "depth_sub (set (reduce_atoms c)) (reduce_sub c gbar) \<le> ?DL"
    proof -
      have "depth_sub (set (reduce_atoms c)) (reduce_sub c gbar)
              = Max (insert 1 (depth_formula ` set gbar))" by (rule reduce_depth_sub[OF len])
      also have "\<dots> \<le> ?DL" by (rule Max.boundedI) (use dg DLge1 in auto)
      finally show ?thesis .
    qed
    have dsub_shc: "depth_sub (set (shc_atoms c)) (shc_sub c (z # gbar) z) \<le> ?DL"
    proof -
      have "depth_sub (set (shc_atoms c)) (shc_sub c (z # gbar) z)
              = Max (insert 1 (depth_formula ` set ((z # gbar) @ [z])))"
        by (rule shc_depth_sub[OF lenz])
      also have "\<dots> \<le> ?DL"
        by (rule Max.boundedI) (use dz dg DLge1 in auto)
      finally show ?thesis .
    qed
    have d_F2: "depth_formula (balance (Conn (conn_fix c 0 True) gbar)
                  (Conn (conn_fix c 0 False) gbar) z)
                \<le> depth_formula custom_balancing + (3 * ?DL + 3)"
    proof -
      have "depth_formula (balance (Conn (conn_fix c 0 True) gbar)
              (Conn (conn_fix c 0 False) gbar) z)
            \<le> depth_formula custom_balancing
              + (depth_formula (Conn (conn_fix c 0 True) gbar)
                 + depth_formula (Conn (conn_fix c 0 False) gbar) + depth_formula z + 1)"
        by (rule depth_balance_le)
      also have "\<dots> \<le> depth_formula custom_balancing + (3 * ?DL + 3)"
        using d_cftg d_cffg dz by linarith
      finally show ?thesis .
    qed
    have d_F3: "depth_formula (balance (Conn c (true_const # gbar))
                  (Conn c (false_const # gbar)) z)
                \<le> depth_formula custom_balancing + (3 * ?DL + 3)"
    proof -
      have "depth_formula (balance (Conn c (true_const # gbar))
              (Conn c (false_const # gbar)) z)
            \<le> depth_formula custom_balancing
              + (depth_formula (Conn c (true_const # gbar))
                 + depth_formula (Conn c (false_const # gbar)) + depth_formula z + 1)"
        by (rule depth_balance_le)
      also have "\<dots> \<le> depth_formula custom_balancing + (3 * ?DL + 3)"
        using d_tg d_fg dz by linarith
      finally show ?thesis .
    qed
    \<comment> \<open>the construction, kept explicit for bounds\<close>
    have cfT_ar: "arity (alphabet F) (conn_fix c 0 True) = arity (alphabet F) c - 1"
      using conn_fix_spec[of 0 c True] ar0 by simp
    have cfF_ar: "arity (alphabet F) (conn_fix c 0 False) = arity (alphabet F) c - 1"
      using conn_fix_spec[of 0 c False] ar0 by simp
    have lenTg: "length (true_const # gbar) = arity (alphabet F) c" using len ar by simp
    have lenFg: "length (false_const # gbar) = arity (alphabet F) c" using len ar by simp
    have wf_Ttg: "formula_well_formed (alphabet F) (Conn c (true_const # gbar))"
      using lenTg true_const_wf wfgbar by auto
    have wf_Ffg: "formula_well_formed (alphabet F) (Conn c (false_const # gbar))"
      using lenFg false_const_wf wfgbar by auto
    have wf_cfT: "formula_well_formed (alphabet F) (Conn (conn_fix c 0 True) gbar)"
      using cfT_ar len wfgbar by auto
    have wf_cfF: "formula_well_formed (alphabet F) (Conn (conn_fix c 0 False) gbar)"
      using cfF_ar len wfgbar by auto
    have redT: "provable_balanced_iff (Conn c (true_const # gbar))
        (Conn (conn_fix c 0 True) gbar) (reduce_lines c True)
        (reduce_step_len c True * len_sub (set (reduce_atoms c)) (reduce_sub c gbar))
        (reduce_step_depth c True + depth_sub (set (reduce_atoms c)) (reduce_sub c gbar))"
      using reduce_subst[where b = True, OF ar len wfgbar'] by simp
    have redF: "provable_balanced_iff (Conn c (false_const # gbar))
        (Conn (conn_fix c 0 False) gbar) (reduce_lines c False)
        (reduce_step_len c False * len_sub (set (reduce_atoms c)) (reduce_sub c gbar))
        (reduce_step_depth c False + depth_sub (set (reduce_atoms c)) (reduce_sub c gbar))"
      using reduce_subst[where b = False, OF ar len wfgbar'] by simp
    note rT = iff_sym[OF redT wf_Ttg wf_cfT]
    note rF = iff_sym[OF redF wf_Ffg wf_cfF]
    note PB2 = balance_cong[OF rT rF iff_refl[OF wfz]
                 wf_cfT wf_Ttg wf_cfF wf_Ffg wfz wfz]
    have shc': "provable_balanced_iff
        (balance (Conn c (true_const # gbar)) (Conn c (false_const # gbar)) z)
        (Conn c (z # gbar)) (shc_lines c 0)
        (shc_step_len c 0 * len_sub (set (shc_atoms c)) (shc_sub c (z # gbar) z))
        (shc_step_depth c 0 + depth_sub (set (shc_atoms c)) (shc_sub c (z # gbar) z))"
      using shc_subst[where d = c and i = 0 and gs = "z # gbar" and Z = z,
                      OF ar0 lenz wfzgbar wfz] by simp
    have wf_balT: "formula_well_formed (alphabet F)
        (balance (Conn c (true_const # gbar)) (Conn c (false_const # gbar)) z)"
      by (rule balance_wf[OF wf_Ttg wf_Ffg wfz])
    have wf_balCF: "formula_well_formed (alphabet F)
        (balance (Conn (conn_fix c 0 True) gbar) (Conn (conn_fix c 0 False) gbar) z)"
      by (rule balance_wf[OF wf_cfT wf_cfF wfz])
    have wf_zgbar: "formula_well_formed (alphabet F) (Conn c (z # gbar))"
      using lenz wfzgbar by auto
    note COL = iff_trans[OF PB2 shc' wf_balCF wf_balT wf_zgbar]
    \<comment> \<open>budget facts\<close>
    have WKc: "288 * W \<le> Kc * (?LL + 1)"
    proof -
      have "288 * W = 288 * (Cc * Cc * (?LL + 1))" unfolding W_def by simp
      also have "\<dots> \<le> 1000 * (Cc * Cc * (?LL + 1))" by simp
      also have "\<dots> = Kc * (?LL + 1)" unfolding Kc_def by (simp only: ac_simps)
      finally show ?thesis .
    qed
    have leafbnd: "10 * Cc + 3 * ?DL \<le> Kc * (?DL + 1)"
    proof -
      have a1: "10 * Cc \<le> Kc"
      proof -
        have "(10::nat) \<le> 1000 * Cc"
        proof -
          have "(10::nat) \<le> 1000 * 1" by simp
          also have "(1000::nat) * 1 \<le> 1000 * Cc" using Ccge1 by (rule mult_le_mono2)
          finally show ?thesis .
        qed
        hence "Cc * 10 \<le> Cc * (1000 * Cc)" by (rule mult_le_mono2)
        thus ?thesis unfolding Kc_def by (simp add: ac_simps)
      qed
      have a2: "3 * ?DL \<le> Kc * ?DL" by (rule mult_le_mono1[OF Kcge3])
      have "10 * Cc + 3 * ?DL \<le> Kc + Kc * ?DL" using a1 a2 by linarith
      also have "Kc + Kc * ?DL = Kc * (?DL + 1)" by (rule kc_dist[symmetric])
      finally show ?thesis .
    qed
    \<comment> \<open>size product bounds (each maximal product term in COL.sz is \<le> 36 * W)\<close>
    have rdLenB: "len_sub (set (reduce_atoms c)) (reduce_sub c gbar) \<le> 36 * (Cc * ?LL)"
    proof -
      have "len_sub (set (reduce_atoms c)) (reduce_sub c gbar) \<le> 36 * ?LL"
      proof -
        have "len_sub (set (reduce_atoms c)) (reduce_sub c gbar)
                = max 1 (sum_list (map len_formula gbar))" by (rule reduce_len_sub[OF len])
        also have "max 1 (sum_list (map len_formula gbar)) \<le> 36 * ?LL"
        proof (rule max.boundedI)
          show "1 \<le> 36 * ?LL" using LLval by linarith
          show "sum_list (map len_formula gbar) \<le> 36 * ?LL" using LLval SGle by linarith
        qed
        finally show ?thesis .
      qed
      thus ?thesis using Ccge1 by (rule sz_scale)
    qed
    have sz1: "reduce_step_len c True * len_sub (set (reduce_atoms c)) (reduce_sub c gbar) \<le> 36 * W"
    proof (rule prod_le_36W[OF _ _ W_def])
      show "reduce_step_len c True \<le> Cc" using reduce_step_len_le[of c True] C_rmsl by simp
      show "len_sub (set (reduce_atoms c)) (reduce_sub c gbar) \<le> 36 * (Cc * ?LL)" by (rule rdLenB)
    qed
    have sz3: "reduce_step_len c False * len_sub (set (reduce_atoms c)) (reduce_sub c gbar) \<le> 36 * W"
    proof (rule prod_le_36W[OF _ _ W_def])
      show "reduce_step_len c False \<le> Cc" using reduce_step_len_le[of c False] C_rmsl by simp
      show "len_sub (set (reduce_atoms c)) (reduce_sub c gbar) \<le> 36 * (Cc * ?LL)" by (rule rdLenB)
    qed
    have sz7: "shc_step_len c 0 * len_sub (set (shc_atoms c)) (shc_sub c (z # gbar) z) \<le> 36 * W"
    proof (rule prod_le_36W[OF _ _ W_def])
      show "shc_step_len c 0 \<le> Cc" using shc_step_len_le[OF ar0] C_smsl by simp
      have "len_sub (set (shc_atoms c)) (shc_sub c (z # gbar) z) \<le> 36 * ?LL"
      proof -
        have "len_sub (set (shc_atoms c)) (shc_sub c (z # gbar) z)
                = max 1 (sum_list (map len_formula (z # gbar)) + len_formula z)"
          by (rule shc_len_sub[OF lenz])
        also have "max 1 (sum_list (map len_formula (z # gbar)) + len_formula z) \<le> 36 * ?LL"
        proof (rule max.boundedI)
          show "1 \<le> 36 * ?LL" using LLval by linarith
          show "sum_list (map len_formula (z # gbar)) + len_formula z \<le> 36 * ?LL"
            using LLval by simp
        qed
        finally show ?thesis .
      qed
      thus "len_sub (set (shc_atoms c)) (shc_sub c (z # gbar) z) \<le> 36 * (Cc * ?LL)"
        using Ccge1 by (rule sz_scale)
    qed
    have sz2: "sym_step_len * (len_formula (Conn c (true_const # gbar))
                + len_formula (Conn (conn_fix c 0 True) gbar)) \<le> 36 * W"
    proof (rule prod_le_36W[OF _ _ W_def])
      show "sym_step_len \<le> Cc" using C_sysl by simp
      have "len_formula (Conn c (true_const # gbar)) + len_formula (Conn (conn_fix c 0 True) gbar)
              \<le> 36 * ?LL" using Lv_tg Lv_cftg LLval by linarith
      thus "len_formula (Conn c (true_const # gbar)) + len_formula (Conn (conn_fix c 0 True) gbar)
              \<le> 36 * (Cc * ?LL)" using Ccge1 by (rule sz_scale)
    qed
    have sz4: "sym_step_len * (len_formula (Conn c (false_const # gbar))
                + len_formula (Conn (conn_fix c 0 False) gbar)) \<le> 36 * W"
    proof (rule prod_le_36W[OF _ _ W_def])
      show "sym_step_len \<le> Cc" using C_sysl by simp
      have "len_formula (Conn c (false_const # gbar)) + len_formula (Conn (conn_fix c 0 False) gbar)
              \<le> 36 * ?LL" using Lv_fg Lv_cffg LLval by linarith
      thus "len_formula (Conn c (false_const # gbar)) + len_formula (Conn (conn_fix c 0 False) gbar)
              \<le> 36 * (Cc * ?LL)" using Ccge1 by (rule sz_scale)
    qed
    have sz5: "refl_step_len * len_formula z \<le> 36 * W"
    proof (rule prod_le_36W[OF _ _ W_def])
      show "refl_step_len \<le> Cc" using C_rfsl by simp
      have "len_formula z \<le> 36 * ?LL" using lenZle LLval by linarith
      thus "len_formula z \<le> 36 * (Cc * ?LL)" using Ccge1 by (rule sz_scale)
    qed
    have sz6: "balance_cong_step_len * (6 * (len_formula (Conn (conn_fix c 0 True) gbar)
                + len_formula (Conn c (true_const # gbar))
                + len_formula (Conn (conn_fix c 0 False) gbar)
                + len_formula (Conn c (false_const # gbar))
                + len_formula z + len_formula z)) \<le> 36 * W"
    proof (rule prod_le_36W[OF _ _ W_def])
      show "balance_cong_step_len \<le> Cc" using C_bcsl by simp
      have "6 * (len_formula (Conn (conn_fix c 0 True) gbar)
              + len_formula (Conn c (true_const # gbar))
              + len_formula (Conn (conn_fix c 0 False) gbar)
              + len_formula (Conn c (false_const # gbar))
              + len_formula z + len_formula z) \<le> 36 * ?LL"
        unfolding Lv_tg Lv_fg Lv_cftg Lv_cffg LLval by simp
      thus "6 * (len_formula (Conn (conn_fix c 0 True) gbar)
              + len_formula (Conn c (true_const # gbar))
              + len_formula (Conn (conn_fix c 0 False) gbar)
              + len_formula (Conn c (false_const # gbar))
              + len_formula z + len_formula z) \<le> 36 * (Cc * ?LL)"
        using Ccge1 by (rule sz_scale)
    qed
    have sz8: "trans_step_len * (len_formula (balance (Conn (conn_fix c 0 True) gbar)
                  (Conn (conn_fix c 0 False) gbar) z)
                + len_formula (balance (Conn c (true_const # gbar)) (Conn c (false_const # gbar)) z)
                + len_formula (Conn c (z # gbar))) \<le> 36 * W"
    proof (rule prod_le_36W[OF _ _ W_def])
      show "trans_step_len \<le> Cc" using C_tsl by simp
      have lF2: "len_formula (balance (Conn (conn_fix c 0 True) gbar)
                   (Conn (conn_fix c 0 False) gbar) z) \<le> 3 * (Cc * ?LL)"
      proof -
        have "len_formula (balance (Conn (conn_fix c 0 True) gbar)
                (Conn (conn_fix c 0 False) gbar) z)
              \<le> len_formula custom_balancing
                 * (len_formula (Conn (conn_fix c 0 True) gbar)
                    + len_formula (Conn (conn_fix c 0 False) gbar) + len_formula z + 1)"
          by (rule len_balance_le)
        also have "\<dots> \<le> Cc * (3 * ?LL)"
        proof (rule mult_le_mono)
          show "len_formula custom_balancing \<le> Cc" using C_cb by simp
          show "len_formula (Conn (conn_fix c 0 True) gbar)
                  + len_formula (Conn (conn_fix c 0 False) gbar) + len_formula z + 1 \<le> 3 * ?LL"
            using Lv_cftg Lv_cffg LLval lenZle by linarith
        qed
        also have "\<dots> = 3 * (Cc * ?LL)" by (simp only: ac_simps)
        finally show ?thesis .
      qed
      have lF3: "len_formula (balance (Conn c (true_const # gbar))
                   (Conn c (false_const # gbar)) z) \<le> 5 * (Cc * ?LL)"
      proof -
        have "len_formula (balance (Conn c (true_const # gbar)) (Conn c (false_const # gbar)) z)
              \<le> len_formula custom_balancing
                 * (len_formula (Conn c (true_const # gbar))
                    + len_formula (Conn c (false_const # gbar)) + len_formula z + 1)"
          by (rule len_balance_le)
        also have "\<dots> \<le> Cc * (5 * ?LL)"
        proof (rule mult_le_mono)
          show "len_formula custom_balancing \<le> Cc" using C_cb by simp
          show "len_formula (Conn c (true_const # gbar))
                  + len_formula (Conn c (false_const # gbar)) + len_formula z + 1 \<le> 5 * ?LL"
            using Lv_tg Lv_fg LLval lenZle by linarith
        qed
        also have "\<dots> = 5 * (Cc * ?LL)" by (simp only: ac_simps)
        finally show ?thesis .
      qed
      have lF4: "len_formula (Conn c (z # gbar)) \<le> Cc * ?LL"
        using mult_le_mono1[OF Ccge1, of "len_formula (Conn c (z # gbar))"] by simp
      show "len_formula (balance (Conn (conn_fix c 0 True) gbar)
              (Conn (conn_fix c 0 False) gbar) z)
            + len_formula (balance (Conn c (true_const # gbar)) (Conn c (false_const # gbar)) z)
            + len_formula (Conn c (z # gbar)) \<le> 36 * (Cc * ?LL)"
        using lF2 lF3 lF4 by linarith
    qed
    \<comment> \<open>depth leaf bounds (each leaf of COL.dep is \<le> real Kc * (real ?DL + 1))\<close>
    have DLa: "real (reduce_step_depth c True
                 + depth_sub (set (reduce_atoms c)) (reduce_sub c gbar))
               \<le> real Kc * (real ?DL + 1)"
    proof (rule nat_le_real_KcDL)
      have "reduce_step_depth c True + depth_sub (set (reduce_atoms c)) (reduce_sub c gbar)
              \<le> 10 * Cc + 3 * ?DL"
        using reduce_step_depth_le[of c True] C_rmsd dsub_red Ccge1 by linarith
      thus "reduce_step_depth c True + depth_sub (set (reduce_atoms c)) (reduce_sub c gbar)
              \<le> Kc * (?DL + 1)" using leafbnd by linarith
    qed
    have DLc: "real (reduce_step_depth c False
                 + depth_sub (set (reduce_atoms c)) (reduce_sub c gbar))
               \<le> real Kc * (real ?DL + 1)"
    proof (rule nat_le_real_KcDL)
      have "reduce_step_depth c False + depth_sub (set (reduce_atoms c)) (reduce_sub c gbar)
              \<le> 10 * Cc + 3 * ?DL"
        using reduce_step_depth_le[of c False] C_rmsd dsub_red Ccge1 by linarith
      thus "reduce_step_depth c False + depth_sub (set (reduce_atoms c)) (reduce_sub c gbar)
              \<le> Kc * (?DL + 1)" using leafbnd by linarith
    qed
    have DLb: "real (sym_step_depth + max (depth_formula (Conn c (true_const # gbar)))
                 (depth_formula (Conn (conn_fix c 0 True) gbar)))
               \<le> real Kc * (real ?DL + 1)"
    proof (rule nat_le_real_KcDL)
      have "max (depth_formula (Conn c (true_const # gbar)))
              (depth_formula (Conn (conn_fix c 0 True) gbar)) \<le> ?DL + 1"
        using d_tg d_cftg by simp
      hence "sym_step_depth + max (depth_formula (Conn c (true_const # gbar)))
              (depth_formula (Conn (conn_fix c 0 True) gbar)) \<le> 10 * Cc + 3 * ?DL"
        using C_sysd Ccge1 by linarith
      thus "sym_step_depth + max (depth_formula (Conn c (true_const # gbar)))
              (depth_formula (Conn (conn_fix c 0 True) gbar)) \<le> Kc * (?DL + 1)"
        using leafbnd by linarith
    qed
    have DLd: "real (sym_step_depth + max (depth_formula (Conn c (false_const # gbar)))
                 (depth_formula (Conn (conn_fix c 0 False) gbar)))
               \<le> real Kc * (real ?DL + 1)"
    proof (rule nat_le_real_KcDL)
      have "max (depth_formula (Conn c (false_const # gbar)))
              (depth_formula (Conn (conn_fix c 0 False) gbar)) \<le> ?DL + 1"
        using d_fg d_cffg by simp
      hence "sym_step_depth + max (depth_formula (Conn c (false_const # gbar)))
              (depth_formula (Conn (conn_fix c 0 False) gbar)) \<le> 10 * Cc + 3 * ?DL"
        using C_sysd Ccge1 by linarith
      thus "sym_step_depth + max (depth_formula (Conn c (false_const # gbar)))
              (depth_formula (Conn (conn_fix c 0 False) gbar)) \<le> Kc * (?DL + 1)"
        using leafbnd by linarith
    qed
    have DLe: "real (refl_step_depth + depth_formula z) \<le> real Kc * (real ?DL + 1)"
    proof (rule nat_le_real_KcDL)
      have "refl_step_depth + depth_formula z \<le> 10 * Cc + 3 * ?DL"
        using C_rfsd dz Ccge1 by linarith
      thus "refl_step_depth + depth_formula z \<le> Kc * (?DL + 1)" using leafbnd by linarith
    qed
    have DLf: "real (balance_cong_step_depth
                 + max (depth_formula (Conn (conn_fix c 0 True) gbar))
                   (max (depth_formula (Conn c (true_const # gbar)))
                     (max (depth_formula (Conn (conn_fix c 0 False) gbar))
                       (max (depth_formula (Conn c (false_const # gbar)))
                         (max (depth_formula z) (depth_formula z))))))
               \<le> real Kc * (real ?DL + 1)"
    proof (rule nat_le_real_KcDL)
      have "max (depth_formula (Conn (conn_fix c 0 True) gbar))
              (max (depth_formula (Conn c (true_const # gbar)))
                (max (depth_formula (Conn (conn_fix c 0 False) gbar))
                  (max (depth_formula (Conn c (false_const # gbar)))
                    (max (depth_formula z) (depth_formula z))))) \<le> ?DL + 1"
        by (intro max.boundedI) (use d_cftg d_tg d_cffg d_fg dz in auto)
      hence "balance_cong_step_depth
              + max (depth_formula (Conn (conn_fix c 0 True) gbar))
                (max (depth_formula (Conn c (true_const # gbar)))
                  (max (depth_formula (Conn (conn_fix c 0 False) gbar))
                    (max (depth_formula (Conn c (false_const # gbar)))
                      (max (depth_formula z) (depth_formula z))))) \<le> 10 * Cc + 3 * ?DL"
        using C_bcsd Ccge1 by linarith
      thus "balance_cong_step_depth
              + max (depth_formula (Conn (conn_fix c 0 True) gbar))
                (max (depth_formula (Conn c (true_const # gbar)))
                  (max (depth_formula (Conn (conn_fix c 0 False) gbar))
                    (max (depth_formula (Conn c (false_const # gbar)))
                      (max (depth_formula z) (depth_formula z))))) \<le> Kc * (?DL + 1)"
        using leafbnd by linarith
    qed
    have DLg: "real (shc_step_depth c 0
                 + depth_sub (set (shc_atoms c)) (shc_sub c (z # gbar) z))
               \<le> real Kc * (real ?DL + 1)"
    proof (rule nat_le_real_KcDL)
      have "shc_step_depth c 0 + depth_sub (set (shc_atoms c)) (shc_sub c (z # gbar) z)
              \<le> 10 * Cc + 3 * ?DL"
        using shc_step_depth_le[OF ar0] C_smsd dsub_shc Ccge1 by linarith
      thus "shc_step_depth c 0 + depth_sub (set (shc_atoms c)) (shc_sub c (z # gbar) z)
              \<le> Kc * (?DL + 1)" using leafbnd by linarith
    qed
    have DLh: "real (trans_step_depth
                 + max (depth_formula (balance (Conn (conn_fix c 0 True) gbar)
                          (Conn (conn_fix c 0 False) gbar) z))
                   (max (depth_formula (balance (Conn c (true_const # gbar))
                            (Conn c (false_const # gbar)) z))
                     (depth_formula (Conn c (z # gbar)))))
               \<le> real Kc * (real ?DL + 1)"
    proof (rule nat_le_real_KcDL)
      have "max (depth_formula (balance (Conn (conn_fix c 0 True) gbar)
                (Conn (conn_fix c 0 False) gbar) z))
              (max (depth_formula (balance (Conn c (true_const # gbar))
                      (Conn c (false_const # gbar)) z))
                (depth_formula (Conn c (z # gbar))))
            \<le> depth_formula custom_balancing + (3 * ?DL + 3)"
      proof (rule max.boundedI)
        show "depth_formula (balance (Conn (conn_fix c 0 True) gbar)
                (Conn (conn_fix c 0 False) gbar) z)
              \<le> depth_formula custom_balancing + (3 * ?DL + 3)" by (rule d_F2)
        show "max (depth_formula (balance (Conn c (true_const # gbar))
                  (Conn c (false_const # gbar)) z)) (depth_formula (Conn c (z # gbar)))
              \<le> depth_formula custom_balancing + (3 * ?DL + 3)"
        proof (rule max.boundedI)
          show "depth_formula (balance (Conn c (true_const # gbar))
                  (Conn c (false_const # gbar)) z)
                \<le> depth_formula custom_balancing + (3 * ?DL + 3)" by (rule d_F3)
          show "depth_formula (Conn c (z # gbar))
                \<le> depth_formula custom_balancing + (3 * ?DL + 3)" by linarith
        qed
      qed
      hence "trans_step_depth
              + max (depth_formula (balance (Conn (conn_fix c 0 True) gbar)
                       (Conn (conn_fix c 0 False) gbar) z))
                (max (depth_formula (balance (Conn c (true_const # gbar))
                         (Conn c (false_const # gbar)) z))
                  (depth_formula (Conn c (z # gbar)))) \<le> 10 * Cc + 3 * ?DL"
        using C_tsd C_dcb Ccge1 by linarith
      thus "trans_step_depth
              + max (depth_formula (balance (Conn (conn_fix c 0 True) gbar)
                       (Conn (conn_fix c 0 False) gbar) z))
                (max (depth_formula (balance (Conn c (true_const # gbar))
                         (Conn c (false_const # gbar)) z))
                  (depth_formula (Conn c (z # gbar)))) \<le> Kc * (?DL + 1)"
        using leafbnd by linarith
    qed
    \<comment> \<open>assemble\<close>
    show "\<exists> lines sz dep. provable_balanced_iff
            (balance (Conn (conn_fix c 0 True) gbar) (Conn (conn_fix c 0 False) gbar) z)
            (Conn c (z # gbar)) lines sz dep
          \<and> lines \<le> Kc
          \<and> sz \<le> Kc * (len_formula (Conn c (z # gbar)) + 1)
          \<and> real dep \<le> real Kc * (real (depth_formula (Conn c (z # gbar))) + 1)"
      apply (intro exI conjI)
          apply (rule COL)
         apply (use C_rml C_smll C_bcl C_tl C_rfl C_syl C8
                    reduce_lines_le[of c True] reduce_lines_le[of c False]
                    shc_lines_le[OF ar0] in linarith)
        apply (use sz1 sz2 sz3 sz4 sz5 sz6 sz7 sz8 WKc in linarith)
       apply (rule real_of_nat_max_le DLa DLb DLc DLd DLe DLf DLg DLh)+
      done
  qed
  show ?thesis using main by blast
qed

subsection \<open>Bounded commutation: Lemma 6.2 (transform_commutes_conn)\<close>

lemma transform_commutes_conn:
  shows "\<exists> (bnd :: nat poly) (c :: real).
           \<forall> conn ps. (\<forall>p \<in> set ps. formula_well_formed (alphabet F) p) \<and>
                      length ps = arity (alphabet F) conn \<longrightarrow>
             (\<exists> lines sz dep.
                provable_balanced_iff (spira_trans (Conn conn ps)) (Conn conn (map spira_trans ps)) lines sz dep
              \<and> lines \<le> poly bnd (len_formula (Conn conn ps))
              \<and> sz \<le> poly bnd (len_formula (Conn conn ps))
              \<and> real dep \<le> c * log 2 (real (len_formula (Conn conn ps)) + 1))"
proof -
  obtain bnd_reb c_reb where reb:
    "\<forall>P pos. formula_well_formed (alphabet F) P \<and> valid_position P pos \<longrightarrow>
       (\<exists>lines sz dep. provable_balanced_iff (spira_trans P) (rebalancing P pos) lines sz dep
          \<and> lines \<le> poly bnd_reb (len_formula P) \<and> sz \<le> poly bnd_reb (len_formula P)
          \<and> real dep \<le> c_reb * log 2 (real (len_formula P) + 1))"
    using rebalancing_provable by blast
  obtain SL DD DDC where caux:
    "\<forall> c b qs N. 1 \<le> arity (alphabet F) c
         \<and> (\<forall>q\<in>set qs. formula_well_formed (alphabet F) q)
         \<and> length qs = arity (alphabet F) c - 1
         \<and> len_formula (Conn c ((if b then true_const else false_const) # qs)) \<le> N
       \<longrightarrow> (\<exists> lines sz dep. provable_balanced_iff
              (spira_trans (Conn c ((if b then true_const else false_const) # qs)))
              (Conn (conn_fix c 0 b) (map spira_trans qs)) lines sz dep
            \<and> lines \<le> poly SL N * 4 ^ count_big qs
            \<and> sz \<le> poly SL N * 4 ^ count_big qs
            \<and> real dep \<le> DD * log 2 (real N + 1) + DDC)"
    using commutes_aux by blast
  obtain Kc where coll:
    "\<forall> c gbar z. 1 \<le> arity (alphabet F) c \<and> length gbar = arity (alphabet F) c - 1
           \<and> (\<forall>g\<in>set gbar. formula_well_formed (alphabet F) g)
           \<and> formula_well_formed (alphabet F) z
         \<longrightarrow> (\<exists> lines sz dep. provable_balanced_iff
                (balance (Conn (conn_fix c 0 True) gbar) (Conn (conn_fix c 0 False) gbar) z)
                (Conn c (z # gbar)) lines sz dep
              \<and> lines \<le> Kc
              \<and> sz \<le> Kc * (len_formula (Conn c (z # gbar)) + 1)
              \<and> real dep \<le> real Kc * (real (depth_formula (Conn c (z # gbar))) + 1))"
    using collapse by blast
  obtain tc :: real where tc:
    "\<forall>f. formula_well_formed (alphabet F) f \<longrightarrow>
       real (depth_formula (spira_trans f)) \<le> tc * log 2 (real (len_formula f) + 1)"
    using trans_c by blast
  define MA where "MA = Max (arity (alphabet F) ` UNIV)"
  define Cc :: nat where
    "Cc = reduce_max_lines + reduce_max_step_len + reduce_max_step_depth
         + shc_max_lines + shc_max_step_len + shc_max_step_depth
         + balance_cong_lines + balance_cong_step_len + balance_cong_step_depth
         + trans_lines + trans_step_len + trans_step_depth
         + refl_lines + refl_step_len + refl_step_depth
         + sym_lines + sym_step_len + sym_step_depth
         + len_formula custom_balancing + depth_formula custom_balancing + Kc + 1"
  define bnd :: "nat poly" where
    "bnd = bnd_reb + Polynomial.smult (2 * 4 ^ MA) SL
         + Polynomial.smult (100 * Cc * Cc * (MA + 1)) rebal_tb
         + [: 100 * Cc * Cc * (MA + 1) :]"
  define tcm :: real where "tcm = max tc 1"
  define cc :: real where
    "cc = \<bar>c_reb\<bar> + \<bar>DD\<bar> + \<bar>DDC\<bar> + real Kc * (tcm + 3) + tcm * 10
        + real (refl_step_depth + balance_cong_step_depth + trans_step_depth
                + depth_formula custom_balancing + 10)"
  have tcm1: "1 \<le> tcm" unfolding tcm_def by simp
  have Ccge1: "1 \<le> Cc" unfolding Cc_def by simp
  have Cc100: "100 * Cc \<le> 100 * Cc * Cc * (MA + 1)"
  proof -
    have a: "(1::nat) \<le> Cc * (MA + 1)"
    proof -
      have "1 * 1 \<le> Cc * (MA + 1)" by (rule mult_le_mono[OF Ccge1]) simp
      thus ?thesis by simp
    qed
    have "100 * Cc = 100 * Cc * 1" by simp
    also have "100 * Cc * 1 \<le> 100 * Cc * (Cc * (MA + 1))" by (rule mult_le_mono2[OF a])
    also have "100 * Cc * (Cc * (MA + 1)) = 100 * Cc * Cc * (MA + 1)"
      by (simp only: mult.assoc)
    finally show ?thesis .
  qed
  have polybnd: "\<And>n. poly bnd n = poly bnd_reb n + 2 * 4 ^ MA * poly SL n
      + 100 * Cc * Cc * (MA + 1) * poly rebal_tb n + 100 * Cc * Cc * (MA + 1)"
    unfolding bnd_def by (simp add: poly_monom)
  have CcMA: "Cc \<le> 100 * Cc * Cc * (MA + 1)"
  proof -
    have "Cc \<le> 100 * Cc" using Ccge1 by simp
    thus ?thesis using Cc100 by linarith
  qed
  have Cc_le_bnd: "\<And>n. Cc \<le> poly bnd n"
  proof -
    fix n
    have "Cc \<le> 100 * Cc * Cc * (MA + 1)" by (rule CcMA)
    also have "\<dots> \<le> poly bnd n" using polybnd[of n] by simp
    finally show "Cc \<le> poly bnd n" .
  qed
  have ccnn: "0 \<le> \<bar>c_reb\<bar>" "0 \<le> \<bar>DD\<bar>" "0 \<le> \<bar>DDC\<bar>"
             "0 \<le> real Kc * (tcm + 3)" "0 \<le> tcm * 10"
    using tcm1 by (auto intro: mult_nonneg_nonneg)
  have ccpos: "0 \<le> cc"
  proof -
    have "0 \<le> real (refl_step_depth + balance_cong_step_depth + trans_step_depth
                     + depth_formula custom_balancing + 10)" by simp
    thus ?thesis unfolding cc_def using ccnn by linarith
  qed
  have ccexp: "cc = \<bar>c_reb\<bar> + \<bar>DD\<bar> + \<bar>DDC\<bar> + real Kc * (tcm + 3) + tcm * 10
      + real refl_step_depth + real balance_cong_step_depth + real trans_step_depth
      + real (depth_formula custom_balancing) + 10"
    unfolding cc_def by simp
  have ccnn2: "0 \<le> real refl_step_depth" "0 \<le> real balance_cong_step_depth"
              "0 \<le> real trans_step_depth" "0 \<le> real (depth_formula custom_balancing)"
    by simp_all
  have main: "\<And> conn ps. (\<forall>p\<in>set ps. formula_well_formed (alphabet F) p)
       \<Longrightarrow> length ps = arity (alphabet F) conn
       \<Longrightarrow> (\<exists> lines sz dep. provable_balanced_iff
              (spira_trans (Conn conn ps)) (Conn conn (map spira_trans ps)) lines sz dep
            \<and> lines \<le> poly bnd (len_formula (Conn conn ps))
            \<and> sz \<le> poly bnd (len_formula (Conn conn ps))
            \<and> real dep \<le> cc * log 2 (real (len_formula (Conn conn ps)) + 1))"
  proof -
    fix conn :: 'a and ps :: "'a formula list"
    assume wfps: "\<forall>p\<in>set ps. formula_well_formed (alphabet F) p"
      and lenps: "length ps = arity (alphabet F) conn"
    show "\<exists> lines sz dep. provable_balanced_iff
              (spira_trans (Conn conn ps)) (Conn conn (map spira_trans ps)) lines sz dep
            \<and> lines \<le> poly bnd (len_formula (Conn conn ps))
            \<and> sz \<le> poly bnd (len_formula (Conn conn ps))
            \<and> real dep \<le> cc * log 2 (real (len_formula (Conn conn ps)) + 1)"
    proof (cases "arity (alphabet F) conn = 0")
      case True
      hence pnil: "ps = []" using lenps by simp
      have wf0: "formula_well_formed (alphabet F) (Conn conn [])" using True by simp
      have small0: "len_formula (Conn conn []) < spira_threshold"
        unfolding spira_threshold_def by simp
      have id0: "spira_trans (Conn conn []) = Conn conn []"
        by (rule spira_trans_id_when_small[OF wf0 small0])
      show ?thesis
      proof (intro exI conjI)
        show "provable_balanced_iff (spira_trans (Conn conn ps)) (Conn conn (map spira_trans ps))
                refl_lines (refl_step_len * len_formula (Conn conn []))
                (refl_step_depth + depth_formula (Conn conn []))"
          using iff_refl[OF wf0] id0 pnil by simp
        show "refl_lines \<le> poly bnd (len_formula (Conn conn ps))"
        proof -
          have "refl_lines \<le> Cc" unfolding Cc_def by simp
          thus ?thesis using Cc_le_bnd[of "len_formula (Conn conn ps)"] by linarith
        qed
        show "refl_step_len * len_formula (Conn conn []) \<le> poly bnd (len_formula (Conn conn ps))"
        proof -
          have "refl_step_len * len_formula (Conn conn []) \<le> Cc"
            unfolding Cc_def by simp
          thus ?thesis using Cc_le_bnd[of "len_formula (Conn conn ps)"] by linarith
        qed
        show "real (refl_step_depth + depth_formula (Conn conn []))
              \<le> cc * log 2 (real (len_formula (Conn conn ps)) + 1)"
        proof -
          have logge1: "1 \<le> log 2 (real (len_formula (Conn conn ps)) + 1)"
          proof -
            have "(2::real) \<le> real (len_formula (Conn conn ps)) + 1" by simp
            hence "log 2 2 \<le> log 2 (real (len_formula (Conn conn ps)) + 1)"
              by (intro log_mono) auto
            thus ?thesis by simp
          qed
          have "real (refl_step_depth + depth_formula (Conn conn []))
                  = real refl_step_depth + 1" by simp
          also have "\<dots> \<le> real (refl_step_depth + balance_cong_step_depth + trans_step_depth
                              + depth_formula custom_balancing + 10)" by simp
          also have "\<dots> \<le> cc" unfolding cc_def using ccnn by linarith
          also have "cc = cc * 1" by simp
          also have "cc * 1 \<le> cc * log 2 (real (len_formula (Conn conn ps)) + 1)"
            by (rule mult_left_mono[OF logge1 ccpos])
          finally show ?thesis .
        qed
      qed
    next
      case False
      hence ar: "1 \<le> arity (alphabet F) conn" by simp
      obtain Q1 rest where ps_eq: "ps = Q1 # rest"
        using False lenps by (cases ps) auto
      have wfQ1: "formula_well_formed (alphabet F) Q1" using wfps ps_eq by simp
      have wfrest: "\<forall>q\<in>set rest. formula_well_formed (alphabet F) q"
        using wfps ps_eq by simp
      have lenrest: "length rest = arity (alphabet F) conn - 1"
        using lenps ps_eq by simp
      have wfN: "formula_well_formed (alphabet F) (Conn conn ps)"
        using wfps lenps by simp
      have rebeq: "rebalancing (Conn conn ps) [0]
          = balance (spira_trans (Conn conn (true_const # rest)))
                    (spira_trans (Conn conn (false_const # rest)))
                    (spira_trans Q1)"
        unfolding rebalancing_def ps_eq by (simp add: fix_at_zero)
      have validpos: "valid_position (Conn conn ps) [0]" using ps_eq by simp
      \<comment> \<open>rebalance the whole formula at slot 0\<close>
      obtain l0 s0 d0 where P0:
          "provable_balanced_iff (spira_trans (Conn conn ps)) (rebalancing (Conn conn ps) [0]) l0 s0 d0"
        and P0l: "l0 \<le> poly bnd_reb (len_formula (Conn conn ps))"
        and P0s: "s0 \<le> poly bnd_reb (len_formula (Conn conn ps))"
        and P0d: "real d0 \<le> c_reb * log 2 (real (len_formula (Conn conn ps)) + 1)"
        using reb wfN validpos by blast
      \<comment> \<open>the two arms, by the bounded comprehension lemma\<close>
      have ATex: "\<exists>lines sz dep. provable_balanced_iff
            (spira_trans (Conn conn (true_const # rest)))
            (Conn (conn_fix conn 0 True) (map spira_trans rest)) lines sz dep
          \<and> lines \<le> poly SL (len_formula (Conn conn (true_const # rest))) * 4 ^ count_big rest
          \<and> sz \<le> poly SL (len_formula (Conn conn (true_const # rest))) * 4 ^ count_big rest
          \<and> real dep \<le> DD * log 2 (real (len_formula (Conn conn (true_const # rest))) + 1) + DDC"
      proof -
        have "1 \<le> arity (alphabet F) conn
            \<and> (\<forall>q\<in>set rest. formula_well_formed (alphabet F) q)
            \<and> length rest = arity (alphabet F) conn - 1
            \<and> len_formula (Conn conn ((if True then true_const else false_const) # rest))
               \<le> len_formula (Conn conn (true_const # rest))"
          using ar wfrest lenrest by simp
        from caux[rule_format, OF this] show ?thesis by simp
      qed
      obtain lT sT dT where AT:
          "provable_balanced_iff (spira_trans (Conn conn (true_const # rest)))
             (Conn (conn_fix conn 0 True) (map spira_trans rest)) lT sT dT"
        and ATl: "lT \<le> poly SL (len_formula (Conn conn (true_const # rest))) * 4 ^ count_big rest"
        and ATs: "sT \<le> poly SL (len_formula (Conn conn (true_const # rest))) * 4 ^ count_big rest"
        and ATd: "real dT \<le> DD * log 2 (real (len_formula (Conn conn (true_const # rest))) + 1) + DDC"
        using ATex by blast
      have AFex: "\<exists>lines sz dep. provable_balanced_iff
            (spira_trans (Conn conn (false_const # rest)))
            (Conn (conn_fix conn 0 False) (map spira_trans rest)) lines sz dep
          \<and> lines \<le> poly SL (len_formula (Conn conn (false_const # rest))) * 4 ^ count_big rest
          \<and> sz \<le> poly SL (len_formula (Conn conn (false_const # rest))) * 4 ^ count_big rest
          \<and> real dep \<le> DD * log 2 (real (len_formula (Conn conn (false_const # rest))) + 1) + DDC"
      proof -
        have "1 \<le> arity (alphabet F) conn
            \<and> (\<forall>q\<in>set rest. formula_well_formed (alphabet F) q)
            \<and> length rest = arity (alphabet F) conn - 1
            \<and> len_formula (Conn conn ((if False then true_const else false_const) # rest))
               \<le> len_formula (Conn conn (false_const # rest))"
          using ar wfrest lenrest by simp
        from caux[rule_format, OF this] show ?thesis by simp
      qed
      obtain lF sF dF where AF:
          "provable_balanced_iff (spira_trans (Conn conn (false_const # rest)))
             (Conn (conn_fix conn 0 False) (map spira_trans rest)) lF sF dF"
        and AFl: "lF \<le> poly SL (len_formula (Conn conn (false_const # rest))) * 4 ^ count_big rest"
        and AFs: "sF \<le> poly SL (len_formula (Conn conn (false_const # rest))) * 4 ^ count_big rest"
        and AFd: "real dF \<le> DD * log 2 (real (len_formula (Conn conn (false_const # rest))) + 1) + DDC"
        using AFex by blast
      \<comment> \<open>well-formedness facts for the assembly\<close>
      have ar0c: "0 < arity (alphabet F) conn" using ar by simp
      have wf_stQ1: "formula_well_formed (alphabet F) (spira_trans Q1)"
        by (rule spira_trans_wf[OF wfQ1])
      have wf_strest: "\<forall>g\<in>set (map spira_trans rest). formula_well_formed (alphabet F) g"
      proof
        fix g assume "g \<in> set (map spira_trans rest)"
        then obtain r where r: "r \<in> set rest" and geq: "g = spira_trans r" by auto
        from r wfrest have "formula_well_formed (alphabet F) r" by blast
        thus "formula_well_formed (alphabet F) g" unfolding geq by (rule spira_trans_wf)
      qed
      have cfTr_ar: "arity (alphabet F) (conn_fix conn 0 True) = arity (alphabet F) conn - 1"
        using conn_fix_spec[of 0 conn True] ar0c by simp
      have cfFr_ar: "arity (alphabet F) (conn_fix conn 0 False) = arity (alphabet F) conn - 1"
        using conn_fix_spec[of 0 conn False] ar0c by simp
      have wf_cfTr: "formula_well_formed (alphabet F)
            (Conn (conn_fix conn 0 True) (map spira_trans rest))"
        using cfTr_ar lenrest wf_strest by auto
      have wf_cfFr: "formula_well_formed (alphabet F)
            (Conn (conn_fix conn 0 False) (map spira_trans rest))"
        using cfFr_ar lenrest wf_strest by auto
      have wfstT: "formula_well_formed (alphabet F)
            (spira_trans (Conn conn (true_const # rest)))"
        by (rule spira_trans_wf) (use true_const_wf wfrest lenrest ar in auto)
      have wfstF: "formula_well_formed (alphabet F)
            (spira_trans (Conn conn (false_const # rest)))"
        by (rule spira_trans_wf) (use false_const_wf wfrest lenrest ar in auto)
      have wf_stN: "formula_well_formed (alphabet F) (spira_trans (Conn conn ps))"
        by (rule spira_trans_wf[OF wfN])
      have wf_rebN: "formula_well_formed (alphabet F) (rebalancing (Conn conn ps) [0])"
        by (rule rebalancing_wf[OF wfN validpos])
      have wf_balR: "formula_well_formed (alphabet F)
          (balance (Conn (conn_fix conn 0 True) (map spira_trans rest))
                   (Conn (conn_fix conn 0 False) (map spira_trans rest)) (spira_trans Q1))"
        by (rule balance_wf[OF wf_cfTr wf_cfFr wf_stQ1])
      have wf_result: "formula_well_formed (alphabet F)
          (Conn conn (spira_trans Q1 # map spira_trans rest))"
        using lenrest ar wf_stQ1 wf_strest by auto
      \<comment> \<open>the collapse step\<close>
      obtain l4 s4 d4 where COL:
          "provable_balanced_iff
             (balance (Conn (conn_fix conn 0 True) (map spira_trans rest))
                      (Conn (conn_fix conn 0 False) (map spira_trans rest))
                      (spira_trans Q1))
             (Conn conn (spira_trans Q1 # map spira_trans rest)) l4 s4 d4"
        and COLl: "l4 \<le> Kc"
        and COLs: "s4 \<le> Kc * (len_formula (Conn conn (spira_trans Q1 # map spira_trans rest)) + 1)"
        and COLd: "real d4 \<le> real Kc * (real (depth_formula (Conn conn (spira_trans Q1 # map spira_trans rest))) + 1)"
      proof -
        have "1 \<le> arity (alphabet F) conn
              \<and> length (map spira_trans rest) = arity (alphabet F) conn - 1
              \<and> (\<forall>g\<in>set (map spira_trans rest). formula_well_formed (alphabet F) g)
              \<and> formula_well_formed (alphabet F) (spira_trans Q1)"
          using ar lenrest wf_strest wf_stQ1 by simp
        from coll[rule_format, OF this] show thesis
          using that by blast
      qed
      note PB = balance_cong[OF AT AF iff_refl[OF wf_stQ1]
                   wfstT wf_cfTr wfstF wf_cfFr wf_stQ1 wf_stQ1]
      note PB' = PB[folded rebeq]
      note final = iff_trans[OF iff_trans[OF P0 PB' wf_stN wf_rebN wf_balR]
                               COL wf_stN wf_balR wf_result]
      have mapeq: "map spira_trans ps = spira_trans Q1 # map spira_trans rest"
        unfolding ps_eq by simp
      let ?N = "len_formula (Conn conn ps)"
      \<comment> \<open>length facts\<close>
      have lenQ1N: "len_formula Q1 \<le> ?N" unfolding ps_eq by simp
      have NTle: "len_formula (Conn conn (true_const # rest)) \<le> ?N"
        using len_formula_ge_1[of Q1] unfolding ps_eq by (simp add: true_const_len)
      have NFle: "len_formula (Conn conn (false_const # rest)) \<le> ?N"
        using len_formula_ge_1[of Q1] unfolding ps_eq by (simp add: false_const_len)
      have restN: "\<And>r. r \<in> set rest \<Longrightarrow> len_formula r \<le> ?N"
      proof -
        fix r assume r: "r \<in> set rest"
        have "len_formula r \<le> sum_list (map len_formula rest)"
          using r by (auto intro: member_le_sum_list)
        also have "\<dots> \<le> ?N" unfolding ps_eq by simp
        finally show "len_formula r \<le> ?N" .
      qed
      have wfTrest: "formula_well_formed (alphabet F) (Conn conn (true_const # rest))"
        using true_const_wf wfrest lenrest ar by auto
      have wfFrest: "formula_well_formed (alphabet F) (Conn conn (false_const # rest))"
        using false_const_wf wfrest lenrest ar by auto
      have lenrest_MA: "length rest \<le> MA"
        unfolding MA_def using lenrest arity_le_max[of conn] by simp
      \<comment> \<open>Spira-transform length bounds\<close>
      have LQ1: "len_formula (spira_trans Q1) \<le> poly rebal_tb ?N"
        by (rule spira_trans_len_le_tb[OF wfQ1 lenQ1N])
      have LtN: "len_formula (spira_trans (Conn conn ps)) \<le> poly rebal_tb ?N"
        by (rule spira_trans_len_le_tb[OF wfN order_refl])
      have LTr: "len_formula (spira_trans (Conn conn (true_const # rest))) \<le> poly rebal_tb ?N"
        by (rule spira_trans_len_le_tb[OF wfTrest NTle])
      have LFr: "len_formula (spira_trans (Conn conn (false_const # rest))) \<le> poly rebal_tb ?N"
        by (rule spira_trans_len_le_tb[OF wfFrest NFle])
      have rest_each: "\<forall>r\<in>set rest. len_formula (spira_trans r) \<le> poly rebal_tb ?N"
      proof
        fix r assume r: "r \<in> set rest"
        have "formula_well_formed (alphabet F) r" using wfrest r by blast
        thus "len_formula (spira_trans r) \<le> poly rebal_tb ?N"
          by (rule spira_trans_len_le_tb[OF _ restN[OF r]])
      qed
      have Lrestsum: "sum_list (map len_formula (map spira_trans rest)) \<le> MA * poly rebal_tb ?N"
      proof -
        have eq: "sum_list (map len_formula (map spira_trans rest))
                = sum_list (map (\<lambda>r. len_formula (spira_trans r)) rest)" by (simp add: comp_def)
        have "sum_list (map (\<lambda>r. len_formula (spira_trans r)) rest) \<le> length rest * poly rebal_tb ?N"
          by (rule sum_list_map_le[OF rest_each])
        also have "\<dots> \<le> MA * poly rebal_tb ?N" by (rule mult_le_mono1[OF lenrest_MA])
        finally show ?thesis unfolding eq .
      qed
      have Lcft: "len_formula (Conn (conn_fix conn 0 True) (map spira_trans rest))
                  \<le> 1 + MA * poly rebal_tb ?N" using Lrestsum by simp
      have Lcff: "len_formula (Conn (conn_fix conn 0 False) (map spira_trans rest))
                  \<le> 1 + MA * poly rebal_tb ?N" using Lrestsum by simp
      have Lres: "len_formula (Conn conn (spira_trans Q1 # map spira_trans rest))
                  \<le> 1 + (MA + 1) * poly rebal_tb ?N"
        using LQ1 Lrestsum by (simp add: add_mult_distrib)
      \<comment> \<open>4^count_big rest \<le> 4^MA\<close>
      have cbrest_MA: "count_big rest \<le> MA"
      proof -
        have "count_big rest \<le> length rest" unfolding count_big_def by simp
        thus ?thesis using lenrest_MA by linarith
      qed
      have cbrest4: "(4::nat) ^ count_big rest \<le> 4 ^ MA"
        using cbrest_MA by (rule power_increasing) simp
      \<comment> \<open>lines / size bounds of the two arms, lifted to \<le> 4^MA * poly SL N\<close>
      have armbnd: "\<And>L M. L \<le> poly SL M * 4 ^ count_big rest \<Longrightarrow> M \<le> ?N
                     \<Longrightarrow> L \<le> 4 ^ MA * poly SL ?N"
      proof -
        fix L M
        assume aL: "L \<le> poly SL M * 4 ^ count_big rest" and aM: "M \<le> ?N"
        have "L \<le> poly SL M * 4 ^ count_big rest" by (rule aL)
        also have "\<dots> \<le> poly SL ?N * 4 ^ MA"
          by (rule mult_le_mono[OF poly_nat_mono[OF aM] cbrest4])
        also have "poly SL ?N * 4 ^ MA = 4 ^ MA * poly SL ?N" by (rule mult.commute)
        finally show "L \<le> 4 ^ MA * poly SL ?N" .
      qed
      have lTbnd: "lT \<le> 4 ^ MA * poly SL ?N" by (rule armbnd[OF ATl NTle])
      have lFbnd: "lF \<le> 4 ^ MA * poly SL ?N" by (rule armbnd[OF AFl NFle])
      have sTbnd: "sT \<le> 4 ^ MA * poly SL ?N" by (rule armbnd[OF ATs NTle])
      have sFbnd: "sF \<le> 4 ^ MA * poly SL ?N" by (rule armbnd[OF AFs NFle])
      \<comment> \<open>the constant pieces fit the big constant\<close>
      have lines_const: "refl_lines + balance_cong_lines + trans_lines + trans_lines + l4
                          \<le> 100 * Cc * Cc * (MA + 1)"
      proof -
        have "refl_lines \<le> Cc" unfolding Cc_def by simp
        moreover have "balance_cong_lines \<le> Cc" unfolding Cc_def by simp
        moreover have "trans_lines \<le> Cc" unfolding Cc_def by simp
        moreover have "l4 \<le> Cc" using COLl unfolding Cc_def by simp
        ultimately have "refl_lines + balance_cong_lines + trans_lines + trans_lines + l4 \<le> 5 * Cc"
          by linarith
        also have "5 * Cc \<le> 100 * Cc * Cc * (MA + 1)" using Cc100 by linarith
        finally show ?thesis .
      qed
      have rebal_nn: "0 \<le> 100 * Cc * Cc * (MA + 1) * poly rebal_tb ?N" by simp
      \<comment> \<open>------- size budget and the five rebalancing-side product pieces -------\<close>
      define V :: nat where "V = Cc * Cc * (MA + 1) * (poly rebal_tb ?N + 1)"
      define U :: nat where "U = Cc * (MA + 1) * (poly rebal_tb ?N + 1)"
      have V100: "100 * V = 100 * Cc * Cc * (MA + 1) * poly rebal_tb ?N + 100 * Cc * Cc * (MA + 1)"
        unfolding V_def by (simp add: distrib_left mult.assoc)
      have Uge1: "1 \<le> U"
      proof -
        have "1 * 1 * 1 \<le> Cc * (MA + 1) * (poly rebal_tb ?N + 1)"
          by (intro mult_le_mono) (use Ccge1 in simp_all)
        thus ?thesis unfolding U_def by simp
      qed
      have cb_Cc: "len_formula custom_balancing \<le> Cc" unfolding Cc_def by simp
      have rsl_Cc: "refl_step_len \<le> Cc" unfolding Cc_def by simp
      have bcsl_Cc: "balance_cong_step_len \<le> Cc" unfolding Cc_def by simp
      have tsl_Cc: "trans_step_len \<le> Cc" unfolding Cc_def by simp
      have Kc_Cc: "Kc \<le> Cc" unfolding Cc_def by simp
      \<comment> \<open>base bounds in multiples of the opaque budget U\<close>
      have base_G: "poly rebal_tb ?N \<le> U" unfolding U_def by (rule budget_bounds(1)[OF Ccge1])
      have mid_cf: "1 + MA * poly rebal_tb ?N \<le> U" unfolding U_def
        by (rule budget_bounds(2)[OF Ccge1])
      have mid_res: "1 + (MA + 1) * poly rebal_tb ?N \<le> U" unfolding U_def
        by (rule budget_bounds(3)[OF Ccge1])
      \<comment> \<open>each formula's length, bounded by a multiple of U\<close>
      have LB_tN: "len_formula (spira_trans (Conn conn ps)) \<le> U" using LtN base_G by linarith
      have LB_Q1: "len_formula (spira_trans Q1) \<le> U" using LQ1 base_G by linarith
      have LB_Tr: "len_formula (spira_trans (Conn conn (true_const # rest))) \<le> U"
        using LTr base_G by linarith
      have LB_Fr: "len_formula (spira_trans (Conn conn (false_const # rest))) \<le> U"
        using LFr base_G by linarith
      have LB_cft: "len_formula (Conn (conn_fix conn 0 True) (map spira_trans rest)) \<le> U"
        using Lcft mid_cf by linarith
      have LB_cff: "len_formula (Conn (conn_fix conn 0 False) (map spira_trans rest)) \<le> U"
        using Lcff mid_cf by linarith
      have LB_res: "len_formula (Conn conn (spira_trans Q1 # map spira_trans rest)) \<le> U"
        using Lres mid_res by linarith
      have LB_rebal: "len_formula (rebalancing (Conn conn ps) [0]) \<le> 3 * U"
        unfolding U_def
      proof (rule len_le_via_cb[OF _ cb_Cc])
        have "len_formula (rebalancing (Conn conn ps) [0])
              = len_formula (balance (spira_trans (Conn conn (true_const # rest)))
                                     (spira_trans (Conn conn (false_const # rest)))
                                     (spira_trans Q1))" unfolding rebeq ..
        also have "\<dots> \<le> len_formula custom_balancing
              * (len_formula (spira_trans (Conn conn (true_const # rest)))
                 + len_formula (spira_trans (Conn conn (false_const # rest)))
                 + len_formula (spira_trans Q1) + 1)" by (rule len_balance_le)
        also have "\<dots> \<le> len_formula custom_balancing * (3 * poly rebal_tb ?N + 1)"
          by (rule mult_le_mono2) (use LTr LFr LQ1 in linarith)
        finally show "len_formula (rebalancing (Conn conn ps) [0])
              \<le> len_formula custom_balancing * (3 * poly rebal_tb ?N + 1)" .
        show "3 * poly rebal_tb ?N + 1 \<le> 3 * ((MA + 1) * (poly rebal_tb ?N + 1))"
          by (rule scale_MA_prt) simp
      qed
      have LB_C1: "len_formula (balance (Conn (conn_fix conn 0 True) (map spira_trans rest))
                     (Conn (conn_fix conn 0 False) (map spira_trans rest)) (spira_trans Q1)) \<le> 3 * U"
        unfolding U_def
      proof (rule len_le_via_cb[OF _ cb_Cc])
        have "len_formula (balance (Conn (conn_fix conn 0 True) (map spira_trans rest))
                (Conn (conn_fix conn 0 False) (map spira_trans rest)) (spira_trans Q1))
              \<le> len_formula custom_balancing
              * (len_formula (Conn (conn_fix conn 0 True) (map spira_trans rest))
                 + len_formula (Conn (conn_fix conn 0 False) (map spira_trans rest))
                 + len_formula (spira_trans Q1) + 1)" by (rule len_balance_le)
        also have "\<dots> \<le> len_formula custom_balancing * ((3 * MA + 3) * poly rebal_tb ?N + 3)"
          by (rule mult_le_mono2) (use Lcft Lcff LQ1 in \<open>simp add: add_mult_distrib\<close>)
        finally show "len_formula (balance (Conn (conn_fix conn 0 True) (map spira_trans rest))
                (Conn (conn_fix conn 0 False) (map spira_trans rest)) (spira_trans Q1))
              \<le> len_formula custom_balancing * ((3 * MA + 3) * poly rebal_tb ?N + 3)" .
        show "(3 * MA + 3) * poly rebal_tb ?N + 3 \<le> 3 * ((MA + 1) * (poly rebal_tb ?N + 1))"
          by (simp add: algebra_simps)
      qed
      \<comment> \<open>the five product pieces, each \<le> a multiple of V (sums bounded with U opaque)\<close>
      have P_refl: "refl_step_len * len_formula (spira_trans Q1) \<le> 1 * V"
      proof -
        have h: "len_formula (spira_trans Q1) \<le> 1 * U" using LB_Q1 by simp
        show ?thesis by (rule prod_le_kV[OF rsl_Cc h[unfolded U_def] V_def])
      qed
      have P_bc: "balance_cong_step_len * (6 * (len_formula (spira_trans (Conn conn (true_const # rest)))
                   + len_formula (Conn (conn_fix conn 0 True) (map spira_trans rest))
                   + len_formula (spira_trans (Conn conn (false_const # rest)))
                   + len_formula (Conn (conn_fix conn 0 False) (map spira_trans rest))
                   + len_formula (spira_trans Q1) + len_formula (spira_trans Q1))) \<le> 36 * V"
      proof -
        have s6: "len_formula (spira_trans (Conn conn (true_const # rest)))
                   + len_formula (Conn (conn_fix conn 0 True) (map spira_trans rest))
                   + len_formula (spira_trans (Conn conn (false_const # rest)))
                   + len_formula (Conn (conn_fix conn 0 False) (map spira_trans rest))
                   + len_formula (spira_trans Q1) + len_formula (spira_trans Q1) \<le> 6 * U"
          using LB_Tr LB_Fr LB_cft LB_cff LB_Q1 by linarith
        have h: "6 * (len_formula (spira_trans (Conn conn (true_const # rest)))
                   + len_formula (Conn (conn_fix conn 0 True) (map spira_trans rest))
                   + len_formula (spira_trans (Conn conn (false_const # rest)))
                   + len_formula (Conn (conn_fix conn 0 False) (map spira_trans rest))
                   + len_formula (spira_trans Q1) + len_formula (spira_trans Q1)) \<le> 36 * U"
          using mult_le_mono2[OF s6, of 6] by simp
        show ?thesis by (rule prod_le_kV[OF bcsl_Cc h[unfolded U_def] V_def])
      qed
      have P_t1: "trans_step_len * (len_formula (spira_trans (Conn conn ps))
                   + len_formula (rebalancing (Conn conn ps) [0])
                   + len_formula (balance (Conn (conn_fix conn 0 True) (map spira_trans rest))
                       (Conn (conn_fix conn 0 False) (map spira_trans rest)) (spira_trans Q1)))
                   \<le> 7 * V"
      proof -
        have h: "len_formula (spira_trans (Conn conn ps))
                   + len_formula (rebalancing (Conn conn ps) [0])
                   + len_formula (balance (Conn (conn_fix conn 0 True) (map spira_trans rest))
                       (Conn (conn_fix conn 0 False) (map spira_trans rest)) (spira_trans Q1)) \<le> 7 * U"
          using LB_tN LB_rebal LB_C1 by linarith
        show ?thesis by (rule prod_le_kV[OF tsl_Cc h[unfolded U_def] V_def])
      qed
      have P_t2: "trans_step_len * (len_formula (spira_trans (Conn conn ps))
                   + len_formula (balance (Conn (conn_fix conn 0 True) (map spira_trans rest))
                       (Conn (conn_fix conn 0 False) (map spira_trans rest)) (spira_trans Q1))
                   + len_formula (Conn conn (spira_trans Q1 # map spira_trans rest))) \<le> 5 * V"
      proof -
        have h: "len_formula (spira_trans (Conn conn ps))
                   + len_formula (balance (Conn (conn_fix conn 0 True) (map spira_trans rest))
                       (Conn (conn_fix conn 0 False) (map spira_trans rest)) (spira_trans Q1))
                   + len_formula (Conn conn (spira_trans Q1 # map spira_trans rest)) \<le> 5 * U"
          using LB_tN LB_C1 LB_res by linarith
        show ?thesis by (rule prod_le_kV[OF tsl_Cc h[unfolded U_def] V_def])
      qed
      have P_s4: "s4 \<le> 2 * V"
      proof -
        have b: "len_formula (Conn conn (spira_trans Q1 # map spira_trans rest)) + 1 \<le> 2 * U"
          using LB_res Uge1 by linarith
        have "s4 \<le> Kc * (len_formula (Conn conn (spira_trans Q1 # map spira_trans rest)) + 1)"
          by (rule COLs)
        also have "\<dots> \<le> 2 * V" by (rule prod_le_kV[OF Kc_Cc b[unfolded U_def] V_def])
        finally show ?thesis .
      qed
      \<comment> \<open>collect the pieces and the budget relation\<close>
      have Vfit: "1 * V + 36 * V + 7 * V + 5 * V + 2 * V
                  \<le> 100 * Cc * Cc * (MA + 1) * poly rebal_tb ?N + 100 * Cc * Cc * (MA + 1)"
        using V100 by linarith
      \<comment> \<open>------- depth facts (real, logarithmic) -------\<close>
      have logge1: "1 \<le> log 2 (real ?N + 1)"
      proof -
        have "(2::real) \<le> real ?N + 1" by simp
        hence "log 2 2 \<le> log 2 (real ?N + 1)" by (intro log_mono) auto
        thus ?thesis by simp
      qed
      have LGpos: "0 \<le> log 2 (real ?N + 1)" using logge1 by simp
      have LGtcm_nn: "0 \<le> tcm * log 2 (real ?N + 1)" using tcm1 LGpos by simp
      have B1real: "1 \<le> tcm * log 2 (real ?N + 1)"
        using mult_mono[OF tcm1 logge1] LGpos tcm1 by simp
      have DQ1r: "real (depth_formula (spira_trans Q1)) \<le> tcm * log 2 (real ?N + 1)"
        unfolding tcm_def by (rule spira_trans_dep_le[OF tc wfQ1 lenQ1N])
      have DtNr: "real (depth_formula (spira_trans (Conn conn ps))) \<le> tcm * log 2 (real ?N + 1)"
        unfolding tcm_def by (rule spira_trans_dep_le[OF tc wfN order_refl])
      have DTrr: "real (depth_formula (spira_trans (Conn conn (true_const # rest))))
                  \<le> tcm * log 2 (real ?N + 1)"
        unfolding tcm_def by (rule spira_trans_dep_le[OF tc wfTrest NTle])
      have DFrr: "real (depth_formula (spira_trans (Conn conn (false_const # rest))))
                  \<le> tcm * log 2 (real ?N + 1)"
        unfolding tcm_def by (rule spira_trans_dep_le[OF tc wfFrest NFle])
      have Drest_each: "\<forall>g\<in>set (map spira_trans rest). real (depth_formula g)
                        \<le> tcm * log 2 (real ?N + 1)"
      proof
        fix g assume "g \<in> set (map spira_trans rest)"
        then obtain r where r: "r \<in> set rest" and g: "g = spira_trans r" by auto
        have "real (depth_formula (spira_trans r)) \<le> max tc 1 * log 2 (real ?N + 1)"
          by (rule spira_trans_dep_le[OF tc _ restN[OF r]]) (use wfrest r in blast)
        thus "real (depth_formula g) \<le> tcm * log 2 (real ?N + 1)" unfolding g tcm_def .
      qed
      have Dcftr: "real (depth_formula (Conn (conn_fix conn 0 True) (map spira_trans rest)))
                   \<le> tcm * log 2 (real ?N + 1) + 1"
        by (rule conn_dep_le[OF Drest_each LGtcm_nn])
      have Dcffr: "real (depth_formula (Conn (conn_fix conn 0 False) (map spira_trans rest)))
                   \<le> tcm * log 2 (real ?N + 1) + 1"
        by (rule conn_dep_le[OF Drest_each LGtcm_nn])
      have Dres_each: "\<forall>g\<in>set (spira_trans Q1 # map spira_trans rest).
                        real (depth_formula g) \<le> tcm * log 2 (real ?N + 1)"
        using DQ1r Drest_each by auto
      have Dresr: "real (depth_formula (Conn conn (spira_trans Q1 # map spira_trans rest)))
                   \<le> tcm * log 2 (real ?N + 1) + 1"
        by (rule conn_dep_le[OF Dres_each LGtcm_nn])
      have Drebalr: "real (depth_formula (rebalancing (Conn conn ps) [0]))
                     \<le> real (depth_formula custom_balancing) + tcm * log 2 (real ?N + 1)"
      proof -
        have "real (depth_formula (rebalancing (Conn conn ps) [0]))
              = real (depth_formula (balance (spira_trans (Conn conn (true_const # rest)))
                       (spira_trans (Conn conn (false_const # rest))) (spira_trans Q1)))"
          unfolding rebeq ..
        also have "\<dots> \<le> real (depth_formula custom_balancing) + tcm * log 2 (real ?N + 1)"
          by (rule balance_dep_le[OF DTrr DFrr DQ1r B1real])
        finally show ?thesis .
      qed
      have DQ1r1: "real (depth_formula (spira_trans Q1)) \<le> tcm * log 2 (real ?N + 1) + 1"
        using DQ1r by simp
      have B1real1: "1 \<le> tcm * log 2 (real ?N + 1) + 1" using B1real by simp
      have DC1r: "real (depth_formula (balance (Conn (conn_fix conn 0 True) (map spira_trans rest))
                    (Conn (conn_fix conn 0 False) (map spira_trans rest)) (spira_trans Q1)))
                  \<le> real (depth_formula custom_balancing) + (tcm * log 2 (real ?N + 1) + 1)"
        by (rule balance_dep_le[OF Dcftr Dcffr DQ1r1 B1real1])
      have DTrr1: "real (depth_formula (spira_trans (Conn conn (true_const # rest))))
                   \<le> tcm * log 2 (real ?N + 1) + 1" using DTrr by simp
      have DFrr1: "real (depth_formula (spira_trans (Conn conn (false_const # rest))))
                   \<le> tcm * log 2 (real ?N + 1) + 1" using DFrr by simp
      \<comment> \<open>coefficient bounds: every leaf coefficient is \<le> cc\<close>
      have KcD: "real Kc * (tcm + 3) = real Kc * tcm + 3 * real Kc" by (simp add: distrib_left)
      have ccL1: "\<bar>c_reb\<bar> \<le> cc" unfolding ccexp using ccnn ccnn2 tcm1 by linarith
      have ccL2: "\<bar>DDC\<bar> + \<bar>DD\<bar> \<le> cc" unfolding ccexp using ccnn ccnn2 tcm1 by linarith
      have ccL4: "real refl_step_depth + tcm \<le> cc"
        unfolding ccexp using ccnn ccnn2 tcm1 by linarith
      have ccL5: "real balance_cong_step_depth + 1 + tcm \<le> cc"
        unfolding ccexp using ccnn ccnn2 tcm1 by linarith
      have ccL6: "real trans_step_depth + real (depth_formula custom_balancing) + 1 + tcm \<le> cc"
        unfolding ccexp using ccnn ccnn2 tcm1 by linarith
      have ccL7: "2 * real Kc + real Kc * tcm \<le> cc"
        unfolding ccexp using KcD ccnn ccnn2 tcm1 by linarith
      have logNT: "log 2 (real (len_formula (Conn conn (true_const # rest))) + 1)
                   \<le> log 2 (real ?N + 1)" using NTle by (intro log_mono) auto
      have logNF: "log 2 (real (len_formula (Conn conn (false_const # rest))) + 1)
                   \<le> log 2 (real ?N + 1)" using NFle by (intro log_mono) auto
      have logNTpos: "0 \<le> log 2 (real (len_formula (Conn conn (true_const # rest))) + 1)"
      proof -
        have "(1::real) \<le> real (len_formula (Conn conn (true_const # rest))) + 1" by simp
        hence "log 2 1 \<le> log 2 (real (len_formula (Conn conn (true_const # rest))) + 1)"
          by (intro log_mono) auto
        thus ?thesis by simp
      qed
      have logNFpos: "0 \<le> log 2 (real (len_formula (Conn conn (false_const # rest))) + 1)"
      proof -
        have "(1::real) \<le> real (len_formula (Conn conn (false_const # rest))) + 1" by simp
        hence "log 2 1 \<le> log 2 (real (len_formula (Conn conn (false_const # rest))) + 1)"
          by (intro log_mono) auto
        thus ?thesis by simp
      qed
      \<comment> \<open>------- the eight depth leaves -------\<close>
      have DL1: "real d0 \<le> cc * log 2 (real ?N + 1)"
      proof (rule leaf_log_bound[where K = 0 and M = "\<bar>c_reb\<bar>"])
        have "real d0 \<le> c_reb * log 2 (real ?N + 1)" by (rule P0d)
        also have "\<dots> \<le> \<bar>c_reb\<bar> * log 2 (real ?N + 1)"
          using LGpos by (intro mult_right_mono) auto
        finally show "real d0 \<le> 0 + \<bar>c_reb\<bar> * log 2 (real ?N + 1)" by simp
      qed (use logge1 ccL1 in simp_all)
      have DL2: "real dT \<le> cc * log 2 (real ?N + 1)"
      proof (rule leaf_log_bound[where K = "\<bar>DDC\<bar>" and M = "\<bar>DD\<bar>"])
        have "real dT \<le> DD * log 2 (real (len_formula (Conn conn (true_const # rest))) + 1) + DDC"
          by (rule ATd)
        also have "\<dots> \<le> \<bar>DD\<bar> * log 2 (real (len_formula (Conn conn (true_const # rest))) + 1) + \<bar>DDC\<bar>"
          by (rule add_mono[OF mult_right_mono[OF abs_ge_self logNTpos] abs_ge_self])
        also have "\<dots> \<le> \<bar>DD\<bar> * log 2 (real ?N + 1) + \<bar>DDC\<bar>"
          using logNT by (intro add_right_mono mult_left_mono) auto
        finally show "real dT \<le> \<bar>DDC\<bar> + \<bar>DD\<bar> * log 2 (real ?N + 1)" by simp
      qed (use logge1 ccL2 in simp_all)
      have DL3: "real dF \<le> cc * log 2 (real ?N + 1)"
      proof (rule leaf_log_bound[where K = "\<bar>DDC\<bar>" and M = "\<bar>DD\<bar>"])
        have "real dF \<le> DD * log 2 (real (len_formula (Conn conn (false_const # rest))) + 1) + DDC"
          by (rule AFd)
        also have "\<dots> \<le> \<bar>DD\<bar> * log 2 (real (len_formula (Conn conn (false_const # rest))) + 1) + \<bar>DDC\<bar>"
          by (rule add_mono[OF mult_right_mono[OF abs_ge_self logNFpos] abs_ge_self])
        also have "\<dots> \<le> \<bar>DD\<bar> * log 2 (real ?N + 1) + \<bar>DDC\<bar>"
          using logNF by (intro add_right_mono mult_left_mono) auto
        finally show "real dF \<le> \<bar>DDC\<bar> + \<bar>DD\<bar> * log 2 (real ?N + 1)" by simp
      qed (use logge1 ccL2 in simp_all)
      have DL4: "real (refl_step_depth + depth_formula (spira_trans Q1))
                 \<le> cc * log 2 (real ?N + 1)"
      proof (rule leaf_log_bound[where K = "real refl_step_depth" and M = tcm])
        have "real (refl_step_depth + depth_formula (spira_trans Q1))
              = real refl_step_depth + real (depth_formula (spira_trans Q1))" by simp
        also have "\<dots> \<le> real refl_step_depth + tcm * log 2 (real ?N + 1)" using DQ1r by simp
        finally show "real (refl_step_depth + depth_formula (spira_trans Q1))
              \<le> real refl_step_depth + tcm * log 2 (real ?N + 1)" .
      qed (use logge1 tcm1 ccL4 in simp_all)
      have DL5: "real (balance_cong_step_depth
                 + max (depth_formula (spira_trans (Conn conn (true_const # rest))))
                   (max (depth_formula (Conn (conn_fix conn 0 True) (map spira_trans rest)))
                     (max (depth_formula (spira_trans (Conn conn (false_const # rest))))
                       (max (depth_formula (Conn (conn_fix conn 0 False) (map spira_trans rest)))
                         (max (depth_formula (spira_trans Q1)) (depth_formula (spira_trans Q1)))))))
                 \<le> cc * log 2 (real ?N + 1)"
      proof (rule leaf_log_bound[where K = "real balance_cong_step_depth + 1" and M = tcm])
        have m6: "real (max (depth_formula (spira_trans (Conn conn (true_const # rest))))
                   (max (depth_formula (Conn (conn_fix conn 0 True) (map spira_trans rest)))
                     (max (depth_formula (spira_trans (Conn conn (false_const # rest))))
                       (max (depth_formula (Conn (conn_fix conn 0 False) (map spira_trans rest)))
                         (max (depth_formula (spira_trans Q1)) (depth_formula (spira_trans Q1)))))))
                 \<le> tcm * log 2 (real ?N + 1) + 1"
          by (rule real_of_nat_max_le DTrr1 Dcftr DFrr1 Dcffr DQ1r1)+
        have "real (balance_cong_step_depth + max (depth_formula (spira_trans (Conn conn (true_const # rest))))
                   (max (depth_formula (Conn (conn_fix conn 0 True) (map spira_trans rest)))
                     (max (depth_formula (spira_trans (Conn conn (false_const # rest))))
                       (max (depth_formula (Conn (conn_fix conn 0 False) (map spira_trans rest)))
                         (max (depth_formula (spira_trans Q1)) (depth_formula (spira_trans Q1)))))))
              = real balance_cong_step_depth
                + real (max (depth_formula (spira_trans (Conn conn (true_const # rest))))
                   (max (depth_formula (Conn (conn_fix conn 0 True) (map spira_trans rest)))
                     (max (depth_formula (spira_trans (Conn conn (false_const # rest))))
                       (max (depth_formula (Conn (conn_fix conn 0 False) (map spira_trans rest)))
                         (max (depth_formula (spira_trans Q1)) (depth_formula (spira_trans Q1)))))))"
          by (rule of_nat_add)
        also have "\<dots> \<le> (real balance_cong_step_depth + 1) + tcm * log 2 (real ?N + 1)"
          using m6 by linarith
        finally show "real (balance_cong_step_depth + max (depth_formula (spira_trans (Conn conn (true_const # rest))))
                   (max (depth_formula (Conn (conn_fix conn 0 True) (map spira_trans rest)))
                     (max (depth_formula (spira_trans (Conn conn (false_const # rest))))
                       (max (depth_formula (Conn (conn_fix conn 0 False) (map spira_trans rest)))
                         (max (depth_formula (spira_trans Q1)) (depth_formula (spira_trans Q1)))))))
              \<le> (real balance_cong_step_depth + 1) + tcm * log 2 (real ?N + 1)" .
      qed (use logge1 tcm1 ccL5 in simp_all)
      have DL6: "real (trans_step_depth + max (depth_formula (spira_trans (Conn conn ps)))
                   (max (depth_formula (rebalancing (Conn conn ps) [0]))
                     (depth_formula (balance (Conn (conn_fix conn 0 True) (map spira_trans rest))
                       (Conn (conn_fix conn 0 False) (map spira_trans rest)) (spira_trans Q1)))))
                 \<le> cc * log 2 (real ?N + 1)"
      proof (rule leaf_log_bound[where K = "real trans_step_depth + real (depth_formula custom_balancing) + 1" and M = tcm])
        have dN1: "real (depth_formula (spira_trans (Conn conn ps)))
                   \<le> real (depth_formula custom_balancing) + tcm * log 2 (real ?N + 1) + 1"
          using DtNr by simp
        have dreb: "real (depth_formula (rebalancing (Conn conn ps) [0]))
                   \<le> real (depth_formula custom_balancing) + tcm * log 2 (real ?N + 1) + 1"
          using Drebalr by simp
        have dC1: "real (depth_formula (balance (Conn (conn_fix conn 0 True) (map spira_trans rest))
                       (Conn (conn_fix conn 0 False) (map spira_trans rest)) (spira_trans Q1)))
                   \<le> real (depth_formula custom_balancing) + tcm * log 2 (real ?N + 1) + 1"
          using DC1r by simp
        have m3: "real (max (depth_formula (spira_trans (Conn conn ps)))
                   (max (depth_formula (rebalancing (Conn conn ps) [0]))
                     (depth_formula (balance (Conn (conn_fix conn 0 True) (map spira_trans rest))
                       (Conn (conn_fix conn 0 False) (map spira_trans rest)) (spira_trans Q1)))))
                 \<le> real (depth_formula custom_balancing) + tcm * log 2 (real ?N + 1) + 1"
          by (rule real_of_nat_max_le dN1 dreb dC1)+
        have "real (trans_step_depth + max (depth_formula (spira_trans (Conn conn ps)))
                   (max (depth_formula (rebalancing (Conn conn ps) [0]))
                     (depth_formula (balance (Conn (conn_fix conn 0 True) (map spira_trans rest))
                       (Conn (conn_fix conn 0 False) (map spira_trans rest)) (spira_trans Q1)))))
              = real trans_step_depth + real (max (depth_formula (spira_trans (Conn conn ps)))
                   (max (depth_formula (rebalancing (Conn conn ps) [0]))
                     (depth_formula (balance (Conn (conn_fix conn 0 True) (map spira_trans rest))
                       (Conn (conn_fix conn 0 False) (map spira_trans rest)) (spira_trans Q1)))))" by simp
        also have "\<dots> \<le> (real trans_step_depth + real (depth_formula custom_balancing) + 1)
                        + tcm * log 2 (real ?N + 1)" using m3 by simp
        finally show "real (trans_step_depth + max (depth_formula (spira_trans (Conn conn ps)))
                   (max (depth_formula (rebalancing (Conn conn ps) [0]))
                     (depth_formula (balance (Conn (conn_fix conn 0 True) (map spira_trans rest))
                       (Conn (conn_fix conn 0 False) (map spira_trans rest)) (spira_trans Q1)))))
              \<le> (real trans_step_depth + real (depth_formula custom_balancing) + 1)
                 + tcm * log 2 (real ?N + 1)" .
      qed (use logge1 tcm1 ccL6 in simp_all)
      have DL7: "real d4 \<le> cc * log 2 (real ?N + 1)"
      proof (rule leaf_log_bound[where K = "2 * real Kc" and M = "real Kc * tcm"])
        have "real d4 \<le> real Kc * (real (depth_formula (Conn conn (spira_trans Q1 # map spira_trans rest))) + 1)"
          by (rule COLd)
        also have "\<dots> \<le> real Kc * (tcm * log 2 (real ?N + 1) + 2)"
          using Dresr by (intro mult_left_mono) auto
        also have "\<dots> = 2 * real Kc + real Kc * tcm * log 2 (real ?N + 1)"
          by (simp add: distrib_left mult.assoc)
        finally show "real d4 \<le> 2 * real Kc + real Kc * tcm * log 2 (real ?N + 1)" .
      qed (use logge1 tcm1 ccL7 in simp_all)
      have DL8: "real (trans_step_depth + max (depth_formula (spira_trans (Conn conn ps)))
                   (max (depth_formula (balance (Conn (conn_fix conn 0 True) (map spira_trans rest))
                       (Conn (conn_fix conn 0 False) (map spira_trans rest)) (spira_trans Q1)))
                     (depth_formula (Conn conn (spira_trans Q1 # map spira_trans rest)))))
                 \<le> cc * log 2 (real ?N + 1)"
      proof (rule leaf_log_bound[where K = "real trans_step_depth + real (depth_formula custom_balancing) + 1" and M = tcm])
        have dN1: "real (depth_formula (spira_trans (Conn conn ps)))
                   \<le> real (depth_formula custom_balancing) + tcm * log 2 (real ?N + 1) + 1"
          using DtNr by simp
        have dC1: "real (depth_formula (balance (Conn (conn_fix conn 0 True) (map spira_trans rest))
                       (Conn (conn_fix conn 0 False) (map spira_trans rest)) (spira_trans Q1)))
                   \<le> real (depth_formula custom_balancing) + tcm * log 2 (real ?N + 1) + 1"
          using DC1r by simp
        have dres: "real (depth_formula (Conn conn (spira_trans Q1 # map spira_trans rest)))
                   \<le> real (depth_formula custom_balancing) + tcm * log 2 (real ?N + 1) + 1"
          using Dresr by simp
        have m3: "real (max (depth_formula (spira_trans (Conn conn ps)))
                   (max (depth_formula (balance (Conn (conn_fix conn 0 True) (map spira_trans rest))
                       (Conn (conn_fix conn 0 False) (map spira_trans rest)) (spira_trans Q1)))
                     (depth_formula (Conn conn (spira_trans Q1 # map spira_trans rest)))))
                 \<le> real (depth_formula custom_balancing) + tcm * log 2 (real ?N + 1) + 1"
          by (rule real_of_nat_max_le dN1 dC1 dres)+
        have "real (trans_step_depth + max (depth_formula (spira_trans (Conn conn ps)))
                   (max (depth_formula (balance (Conn (conn_fix conn 0 True) (map spira_trans rest))
                       (Conn (conn_fix conn 0 False) (map spira_trans rest)) (spira_trans Q1)))
                     (depth_formula (Conn conn (spira_trans Q1 # map spira_trans rest)))))
              = real trans_step_depth + real (max (depth_formula (spira_trans (Conn conn ps)))
                   (max (depth_formula (balance (Conn (conn_fix conn 0 True) (map spira_trans rest))
                       (Conn (conn_fix conn 0 False) (map spira_trans rest)) (spira_trans Q1)))
                     (depth_formula (Conn conn (spira_trans Q1 # map spira_trans rest)))))" by simp
        also have "\<dots> \<le> (real trans_step_depth + real (depth_formula custom_balancing) + 1)
                        + tcm * log 2 (real ?N + 1)" using m3 by simp
        finally show "real (trans_step_depth + max (depth_formula (spira_trans (Conn conn ps)))
                   (max (depth_formula (balance (Conn (conn_fix conn 0 True) (map spira_trans rest))
                       (Conn (conn_fix conn 0 False) (map spira_trans rest)) (spira_trans Q1)))
                     (depth_formula (Conn conn (spira_trans Q1 # map spira_trans rest)))))
              \<le> (real trans_step_depth + real (depth_formula custom_balancing) + 1)
                 + tcm * log 2 (real ?N + 1)" .
      qed (use logge1 tcm1 ccL6 in simp_all)
      \<comment> \<open>------- assemble -------\<close>
      define G1 where "G1 = depth_formula (spira_trans (Conn conn ps))"
      define G2 where "G2 = depth_formula (rebalancing (Conn conn ps) [0])"
      define G3 where "G3 = depth_formula (balance (Conn (conn_fix conn 0 True) (map spira_trans rest))
                          (Conn (conn_fix conn 0 False) (map spira_trans rest)) (spira_trans Q1))"
      define G4 where "G4 = depth_formula (Conn conn (spira_trans Q1 # map spira_trans rest))"
      define G5 where "G5 = depth_formula (spira_trans (Conn conn (true_const # rest)))"
      define G6 where "G6 = depth_formula (Conn (conn_fix conn 0 True) (map spira_trans rest))"
      define G7 where "G7 = depth_formula (spira_trans (Conn conn (false_const # rest)))"
      define G8 where "G8 = depth_formula (Conn (conn_fix conn 0 False) (map spira_trans rest))"
      define G9 where "G9 = depth_formula (spira_trans Q1)"
      note DLs = DL1 DL2 DL3 DL4 DL5 DL6 DL7 DL8
      note DLf = DLs[folded G1_def G2_def G3_def G4_def G5_def G6_def G7_def G8_def G9_def]
      have depF: "real (max (max d0
                     (max (max dT
                            (max dF
                              (max (refl_step_depth + G9)
                                (balance_cong_step_depth +
                                 max G5 (max G6 (max G7 (max G8 (max G9 G9))))))))
                       (trans_step_depth + max G1 (max G2 G3))))
                (max d4 (trans_step_depth + max G1 (max G3 G4))))
              \<le> cc * log 2 (real (len_formula (Conn conn ps)) + 1)"
        by (rule real_of_nat_max_le DLf)+
      have twoSL: "2 * 4 ^ MA * poly SL ?N = 4 ^ MA * poly SL ?N + 4 ^ MA * poly SL ?N"
        by (simp add: algebra_simps)
      show ?thesis
        apply (unfold mapeq)
        apply (intro exI conjI)
            apply (rule final)
          apply (fold G1_def G2_def G3_def G4_def G5_def G6_def G7_def G8_def G9_def)
          apply (rule depF
                 | (use P0l lTbnd lFbnd lines_const P0s sTbnd sFbnd
                        P_refl P_bc P_t1 P_t2 P_s4 Vfit polybnd[of ?N] twoSL rebal_nn in linarith))+
        done
    qed
  qed
  show ?thesis using main by blast
qed

subsection \<open>Structural commutation: Lemma 6.4 (transform_commutes_form)\<close>

subsubsection \<open>A depth-tight connective congruence\<close>

definition conn_cong_atoms where
  "conn_cong_atoms c = fresh_atoms (2 * arity (alphabet F) c)"

lemma conn_cong_atoms_spec:
  "length (conn_cong_atoms c) = 2 * arity (alphabet F) c
   \<and> distinct (conn_cong_atoms c)
   \<and> set (conn_cong_atoms c) \<inter> avoid_atoms = {}"
  unfolding conn_cong_atoms_def
  using fresh_atoms_spec[of "2 * arity (alphabet F) c"] by simp

definition conn_cong_lhs where
  "conn_cong_lhs c =
     Conn c (map Atom (take (arity (alphabet F) c) (conn_cong_atoms c)))"

definition conn_cong_rhs where
  "conn_cong_rhs c =
     Conn c (map Atom (drop (arity (alphabet F) c) (conn_cong_atoms c)))"

definition conn_cong_asms where
  "conn_cong_asms c =
     (\<lambda>i. iff_form (Atom (conn_cong_atoms c ! i))
                   (Atom (conn_cong_atoms c ! (arity (alphabet F) c + i))))
       ` {..< arity (alphabet F) c}"

definition conn_cong_base_proof where
  "conn_cong_base_proof c =
     entails_proof (conn_cong_asms c) (iff_form (conn_cong_lhs c) (conn_cong_rhs c))"

lemma conn_cong_taut:
  "\<forall>val. (\<forall>f \<in> conn_cong_asms c. eval (alphabet F) val f)
         \<longrightarrow> eval (alphabet F) val (iff_form (conn_cong_lhs c) (conn_cong_rhs c))"
proof (intro allI impI)
  fix val
  let ?k = "arity (alphabet F) c"
  let ?as = "take ?k (conn_cong_atoms c)"
  let ?bs = "drop ?k (conn_cong_atoms c)"
  have lenat: "length (conn_cong_atoms c) = 2 * ?k" using conn_cong_atoms_spec by simp
  have lena: "length ?as = ?k" using lenat by simp
  have lenb: "length ?bs = ?k" using lenat by simp
  assume hyp: "\<forall>f \<in> conn_cong_asms c. eval (alphabet F) val f"
  have eqi: "\<And>i. i < ?k \<Longrightarrow> val (?as ! i) = val (?bs ! i)"
  proof -
    fix i assume i: "i < ?k"
    have asi: "?as ! i = conn_cong_atoms c ! i" using i lena by simp
    have bsi: "?bs ! i = conn_cong_atoms c ! (?k + i)" using i lenb by simp
    have "iff_form (Atom (conn_cong_atoms c ! i)) (Atom (conn_cong_atoms c ! (?k + i)))
          \<in> conn_cong_asms c"
      unfolding conn_cong_asms_def using i by blast
    hence "eval (alphabet F) val
             (iff_form (Atom (conn_cong_atoms c ! i)) (Atom (conn_cong_atoms c ! (?k + i))))"
      using hyp by blast
    hence "val (conn_cong_atoms c ! i) = val (conn_cong_atoms c ! (?k + i))"
      by (simp add: iff_form_eval)
    thus "val (?as ! i) = val (?bs ! i)" using asi bsi by simp
  qed
  have mapeq: "map val ?as = map val ?bs"
  proof (rule nth_equalityI)
    show "length (map val ?as) = length (map val ?bs)" using lena lenb by simp
  next
    fix i assume "i < length (map val ?as)"
    hence "i < ?k" using lena by simp
    thus "map val ?as ! i = map val ?bs ! i" using eqi lena lenb by simp
  qed
  have "eval (alphabet F) val (conn_cong_lhs c)
        = conn_evals (alphabet F) c (map val ?as)"
    unfolding conn_cong_lhs_def by (simp add: comp_def)
  also have "\<dots> = conn_evals (alphabet F) c (map val ?bs)" using mapeq by simp
  also have "\<dots> = eval (alphabet F) val (conn_cong_rhs c)"
    unfolding conn_cong_rhs_def by (simp add: comp_def)
  finally show "eval (alphabet F) val (iff_form (conn_cong_lhs c) (conn_cong_rhs c))"
    by (simp add: iff_form_eval)
qed

lemma conn_cong_base_proof_spec:
  "valid_proof F (conn_cong_base_proof c)
   \<and> assumptions (conn_cong_base_proof c) = conn_cong_asms c
   \<and> thesis (conn_cong_base_proof c) = iff_form (conn_cong_lhs c) (conn_cong_rhs c)
   \<and> (\<forall> st \<in> set (steps (conn_cong_base_proof c)). formula_well_formed (alphabet F) st)"
proof -
  have wf_asms: "\<forall>f \<in> conn_cong_asms c. formula_well_formed (alphabet F) f"
    unfolding conn_cong_asms_def by (auto intro: iff_form_wf)
  have wf_lhs: "formula_well_formed (alphabet F) (conn_cong_lhs c)"
    unfolding conn_cong_lhs_def using conn_cong_atoms_spec by auto
  have wf_rhs: "formula_well_formed (alphabet F) (conn_cong_rhs c)"
    unfolding conn_cong_rhs_def using conn_cong_atoms_spec by auto
  have wf_th: "formula_well_formed (alphabet F)
                 (iff_form (conn_cong_lhs c) (conn_cong_rhs c))"
    by (rule iff_form_wf[OF wf_lhs wf_rhs])
  show ?thesis
    unfolding conn_cong_base_proof_def
    using entails_proof_spec[OF wf_asms wf_th conn_cong_taut] .
qed

definition conn_cong_lines where
  "conn_cong_lines c = length (steps (conn_cong_base_proof c))"
definition conn_cong_step_len where
  "conn_cong_step_len c =
     Max (insert 1 (len_formula ` set (steps (conn_cong_base_proof c))))"
definition conn_cong_step_depth where
  "conn_cong_step_depth c =
     Max (insert 1 (depth_formula ` set (steps (conn_cong_base_proof c))))"

definition conn_cong_max_lines where
  "conn_cong_max_lines = Max (insert 0 (conn_cong_lines ` UNIV))"
definition conn_cong_max_step_len where
  "conn_cong_max_step_len = Max (insert 0 (conn_cong_step_len ` UNIV))"
definition conn_cong_max_step_depth where
  "conn_cong_max_step_depth = Max (insert 0 (conn_cong_step_depth ` UNIV))"

lemma conn_cong_max_ge:
  "conn_cong_lines c \<le> conn_cong_max_lines
   \<and> conn_cong_step_len c \<le> conn_cong_max_step_len
   \<and> conn_cong_step_depth c \<le> conn_cong_max_step_depth"
proof -
  have fs: "frege_system F" by (meson frege_balancing_axioms frege_balancing_def)
  have f1: "finite (insert 0 (conn_cong_lines ` UNIV))"
    using frege_system.finite_alphabet[OF fs] by simp
  have f2: "finite (insert 0 (conn_cong_step_len ` UNIV))"
    using frege_system.finite_alphabet[OF fs] by simp
  have f3: "finite (insert 0 (conn_cong_step_depth ` UNIV))"
    using frege_system.finite_alphabet[OF fs] by simp
  have "conn_cong_lines c \<le> conn_cong_max_lines"
    unfolding conn_cong_max_lines_def by (rule Max_ge[OF f1]) simp
  moreover have "conn_cong_step_len c \<le> conn_cong_max_step_len"
    unfolding conn_cong_max_step_len_def by (rule Max_ge[OF f2]) simp
  moreover have "conn_cong_step_depth c \<le> conn_cong_max_step_depth"
    unfolding conn_cong_max_step_depth_def by (rule Max_ge[OF f3]) simp
  ultimately show ?thesis by blast
qed

lemma combine_fold_spec:
  assumes vbase: "valid_proof F base"
  shows "(\<forall>p \<in> set ps. valid_proof F p \<and> assumptions p = {}) \<longrightarrow>
         (valid_proof F (foldr combine_proofs ps base)
          \<and> assumptions (foldr combine_proofs ps base)
              = assumptions base - (\<Union>p \<in> set ps. set (steps p))
          \<and> thesis (foldr combine_proofs ps base) = thesis base
          \<and> steps (foldr combine_proofs ps base) = concat (map steps ps) @ steps base)"
proof (induction ps)
  case Nil
  show ?case using vbase by simp
next
  case (Cons p ps)
  show ?case
  proof (intro impI)
    assume hyps: "\<forall>q \<in> set (p # ps). valid_proof F q \<and> assumptions q = {}"
    have fs: "frege_system F" by (meson frege_balancing_axioms frege_balancing_def)
    have vp: "valid_proof F p" and ap: "assumptions p = {}" using hyps by auto
    have cp_th: "\<And>X. thesis (combine_proofs p X) = thesis X" by simp
    have cp_st: "\<And>X. steps (combine_proofs p X) = steps p @ steps X" by simp
    have cp_as: "\<And>X. assumptions (combine_proofs p X)
                       = assumptions p \<union> (assumptions X - set (steps p))" by simp
    have inner: "valid_proof F (foldr combine_proofs ps base)
          \<and> assumptions (foldr combine_proofs ps base)
              = assumptions base - (\<Union>q \<in> set ps. set (steps q))
          \<and> thesis (foldr combine_proofs ps base) = thesis base
          \<and> steps (foldr combine_proofs ps base) = concat (map steps ps) @ steps base"
      using Cons.IH hyps by (auto simp del: combine_proofs.simps)
    have vin: "valid_proof F (foldr combine_proofs ps base)" using inner by blast
    have fcons: "foldr combine_proofs (p # ps) base
                 = combine_proofs p (foldr combine_proofs ps base)"
      by (simp del: combine_proofs.simps)
    show "valid_proof F (foldr combine_proofs (p # ps) base)
          \<and> assumptions (foldr combine_proofs (p # ps) base)
              = assumptions base - (\<Union>q \<in> set (p # ps). set (steps q))
          \<and> thesis (foldr combine_proofs (p # ps) base) = thesis base
          \<and> steps (foldr combine_proofs (p # ps) base)
              = concat (map steps (p # ps)) @ steps base"
      unfolding fcons
    proof (intro conjI)
      show "valid_proof F (combine_proofs p (foldr combine_proofs ps base))"
        using frege_system.combining_valid_proofs[OF fs] vp vin by blast
    next
      show "assumptions (combine_proofs p (foldr combine_proofs ps base))
            = assumptions base - (\<Union>q \<in> set (p # ps). set (steps q))"
        using cp_as ap inner by (auto simp del: combine_proofs.simps)
    next
      show "thesis (combine_proofs p (foldr combine_proofs ps base)) = thesis base"
        using cp_th inner by (simp del: combine_proofs.simps)
    next
      show "steps (combine_proofs p (foldr combine_proofs ps base))
            = concat (map steps (p # ps)) @ steps base"
        using cp_st inner by (simp del: combine_proofs.simps)
    qed
  qed
qed

lemma conn_cong:
  fixes Sc Dc :: nat and lf :: "nat \<Rightarrow> nat"
  assumes len_eq: "length Bs = length As"
      and ar: "length As = arity (alphabet F) c"
      and wfAs: "\<And>a. a \<in> set As \<Longrightarrow> formula_well_formed (alphabet F) a"
      and wfBs: "\<And>b. b \<in> set Bs \<Longrightarrow> formula_well_formed (alphabet F) b"
      and prem: "\<And>i. i < length As \<Longrightarrow>
                   \<exists>l s d. provable_balanced_iff (As ! i) (Bs ! i) l s d
                            \<and> l \<le> lf i \<and> s \<le> Sc \<and> d \<le> Dc"
    shows "\<exists>lines sz dep.
             provable_balanced_iff (Conn c As) (Conn c Bs) lines sz dep
           \<and> lines \<le> sum_list (map lf [0..< length As]) + conn_cong_max_lines
           \<and> sz \<le> Sc + conn_cong_max_step_len
                    * (2 * length As
                       * (len_formula (Conn c As) + len_formula (Conn c Bs)) + 1)
           \<and> dep \<le> max Dc (conn_cong_max_step_depth
                    + max (depth_formula (Conn c As)) (depth_formula (Conn c Bs)))"
proof -
  have fs_F: "frege_system F" by (meson frege_balancing_axioms frege_balancing_def)
  define kk where "kk = arity (alphabet F) c"
  define atoms where "atoms = conn_cong_atoms c"
  define vals where "vals = As @ Bs"
  define csub where "csub = (\<lambda>v. case map_of (zip atoms vals) v of
                                  None \<Rightarrow> Atom v | Some f \<Rightarrow> f)"
  define LAB where "LAB = len_formula (Conn c As) + len_formula (Conn c Bs)"
  define DAB where "DAB = max (depth_formula (Conn c As)) (depth_formula (Conn c Bs))"

  have atlen: "length atoms = 2 * kk"
    unfolding atoms_def kk_def using conn_cong_atoms_spec by simp
  have atdist: "distinct atoms" unfolding atoms_def using conn_cong_atoms_spec by simp
  have atdisj: "set atoms \<inter> avoid_atoms = {}"
    unfolding atoms_def using conn_cong_atoms_spec by simp
  have askk: "length As = kk" using ar kk_def by simp
  have bskk: "length Bs = kk" using len_eq askk by simp
  have vallen: "length vals = 2 * kk" unfolding vals_def using askk bskk by simp
  have lveq: "length atoms = length vals" using atlen vallen by simp
  have fin_at: "finite (set atoms)" by simp

  have csub_nth: "\<And>j. j < 2 * kk \<Longrightarrow> csub (atoms ! j) = vals ! j"
  proof -
    fix j assume j: "j < 2 * kk"
    have "map_of (zip atoms vals) (atoms ! j) = Some (vals ! j)"
      using map_of_zip_nth_lookup[OF atdist lveq] atlen j by simp
    thus "csub (atoms ! j) = vals ! j" unfolding csub_def by simp
  qed
  have sub_id: "\<forall>v. v \<notin> set atoms \<longrightarrow> csub v = Atom v"
  proof (intro allI impI)
    fix v assume "v \<notin> set atoms"
    hence "map_of (zip atoms vals) v = None" by (rule map_of_zip_None_lookup)
    thus "csub v = Atom v" unfolding csub_def by simp
  qed
  note csub_conn = fresh_sub_conn[OF atdisj sub_id]
  have csub_in_vals: "\<And>v. v \<in> set atoms \<Longrightarrow> csub v \<in> set vals"
  proof -
    fix v assume "v \<in> set atoms"
    hence "\<exists>w. map_of (zip atoms vals) v = Some w"
      using map_of_zip_is_Some[OF lveq] by blast
    then obtain w where w: "map_of (zip atoms vals) v = Some w" by blast
    hence "(v, w) \<in> set (zip atoms vals)" by (rule map_of_SomeD)
    hence "w \<in> set vals" by (rule set_zip_rightD)
    thus "csub v \<in> set vals" using w unfolding csub_def by simp
  qed
  have val_in: "\<And>v. v \<in> set atoms \<Longrightarrow> csub v \<in> set As \<or> csub v \<in> set Bs"
    using csub_in_vals unfolding vals_def by auto

  \<comment> \<open>substitution size facts\<close>
  have csub_len_le: "\<And>v. v \<in> set atoms \<Longrightarrow> len_formula (csub v) \<le> LAB"
  proof -
    fix v assume vin: "v \<in> set atoms"
    have "csub v \<in> set As \<or> csub v \<in> set Bs" using val_in[OF vin] .
    thus "len_formula (csub v) \<le> LAB"
    proof (elim disjE)
      assume "csub v \<in> set As"
      hence "len_formula (csub v) \<le> sum_list (map len_formula As)"
        by (auto intro: member_le_sum_list)
      thus ?thesis unfolding LAB_def by simp
    next
      assume "csub v \<in> set Bs"
      hence "len_formula (csub v) \<le> sum_list (map len_formula Bs)"
        by (auto intro: member_le_sum_list)
      thus ?thesis unfolding LAB_def by simp
    qed
  qed
  have csub_dep_le: "\<And>v. v \<in> set atoms \<Longrightarrow> depth_formula (csub v) \<le> DAB"
  proof -
    fix v assume vin: "v \<in> set atoms"
    have "csub v \<in> set As \<or> csub v \<in> set Bs" using val_in[OF vin] .
    thus "depth_formula (csub v) \<le> DAB"
    proof (elim disjE)
      assume vAs: "csub v \<in> set As"
      hence ne: "As \<noteq> []" by auto
      have "depth_formula (csub v) \<le> Max (set (map depth_formula As))"
        using vAs by simp
      also have "\<dots> \<le> depth_formula (Conn c As)"
      proof -
        have "depth_formula (Conn c As) = 1 + Max (set (map depth_formula As))"
          using ne by simp
        thus ?thesis by linarith
      qed
      also have "\<dots> \<le> DAB" unfolding DAB_def by simp
      finally show ?thesis .
    next
      assume vBs: "csub v \<in> set Bs"
      hence ne: "Bs \<noteq> []" by auto
      have "depth_formula (csub v) \<le> Max (set (map depth_formula Bs))"
        using vBs by simp
      also have "\<dots> \<le> depth_formula (Conn c Bs)"
      proof -
        have "depth_formula (Conn c Bs) = 1 + Max (set (map depth_formula Bs))"
          using ne by simp
        thus ?thesis by linarith
      qed
      also have "\<dots> \<le> DAB" unfolding DAB_def by simp
      finally show ?thesis .
    qed
  qed
  have len_sub_le: "len_sub (set atoms) csub \<le> 2 * kk * LAB + 1"
  proof -
    have "(\<Sum>v \<in> set atoms. len_formula (csub v))
        = sum_list (map (\<lambda>v. len_formula (csub v)) atoms)"
      by (simp add: sum_list_distinct_conv_sum_set[OF atdist])
    also have "\<dots> \<le> sum_list (map (\<lambda>v. LAB) atoms)"
      by (rule sum_list_mono[OF csub_len_le])
    also have "\<dots> = length atoms * LAB" by (simp add: sum_list_triv)
    also have "\<dots> = 2 * kk * LAB" using atlen by simp
    finally have "(\<Sum>v \<in> set atoms. len_formula (csub v)) \<le> 2 * kk * LAB" .
    thus ?thesis unfolding len_sub_def by (simp add: max_def)
  qed
  have dep_sub_le: "depth_sub (set atoms) csub \<le> DAB"
    unfolding depth_sub_def
  proof (rule Max.boundedI)
    show "finite (insert 1 ((\<lambda>v. depth_formula (csub v)) ` set atoms))" by simp
    show "insert 1 ((\<lambda>v. depth_formula (csub v)) ` set atoms) \<noteq> {}" by simp
    fix e assume "e \<in> insert 1 ((\<lambda>v. depth_formula (csub v)) ` set atoms)"
    thus "e \<le> DAB"
    proof
      assume "e = 1"
      thus ?thesis unfolding DAB_def
        using depth_formula_ge_1[of "Conn c As"]
        by (simp add: le_max_iff_disj)
    next
      assume "e \<in> (\<lambda>v. depth_formula (csub v)) ` set atoms"
      then obtain v where "v \<in> set atoms" "e = depth_formula (csub v)" by auto
      thus ?thesis using csub_dep_le by simp
    qed
  qed

  \<comment> \<open>the substituted base proof\<close>
  define ci where "ci = sub_proof csub (conn_cong_base_proof c)"
  have valid_ci: "valid_proof F ci"
    unfolding ci_def
    using frege_system.proof_substitution[OF fs_F] conn_cong_base_proof_spec by blast
  have ci_steps: "steps ci = map (sub_formula csub) (steps (conn_cong_base_proof c))"
    unfolding ci_def by simp
  have csub_wf: "\<And>v. formula_well_formed (alphabet F) (csub v)"
  proof -
    fix v
    show "formula_well_formed (alphabet F) (csub v)"
    proof (cases "v \<in> set atoms")
      case True
      have "csub v \<in> set As \<or> csub v \<in> set Bs" using val_in[OF True] .
      thus ?thesis using wfAs wfBs by auto
    next
      case False
      thus ?thesis using sub_id by simp
    qed
  qed
  have ci_wf: "\<forall>s \<in> set (steps ci). formula_well_formed (alphabet F) s"
  proof
    fix s assume "s \<in> set (steps ci)"
    then obtain s0 where s0: "s0 \<in> set (steps (conn_cong_base_proof c))"
      and seq: "s = sub_formula csub s0" using ci_steps by auto
    have "formula_well_formed (alphabet F) s0"
      using conn_cong_base_proof_spec s0 by blast
    thus "formula_well_formed (alphabet F) s"
      unfolding seq by (rule sub_formula_well_formed[OF _ csub_wf])
  qed
  have ci_lines: "length (steps ci) = conn_cong_lines c"
    using ci_steps by (simp add: conn_cong_lines_def)
  have map_lhs: "map csub (take kk atoms) = As"
  proof (rule nth_equalityI)
    show "length (map csub (take kk atoms)) = length As" using atlen askk by simp
  next
    fix i assume "i < length (map csub (take kk atoms))"
    hence i: "i < kk" using atlen by simp
    have "map csub (take kk atoms) ! i = csub (atoms ! i)"
      using i atlen by simp
    also have "\<dots> = vals ! i" using csub_nth i by simp
    also have "\<dots> = As ! i" using i askk unfolding vals_def by (simp add: nth_append)
    finally show "map csub (take kk atoms) ! i = As ! i" .
  qed
  have map_rhs: "map csub (drop kk atoms) = Bs"
  proof (rule nth_equalityI)
    show "length (map csub (drop kk atoms)) = length Bs" using atlen bskk by simp
  next
    fix i assume "i < length (map csub (drop kk atoms))"
    hence i: "i < kk" using atlen by simp
    have "map csub (drop kk atoms) ! i = csub (atoms ! (kk + i))"
      using i atlen by simp
    also have "\<dots> = vals ! (kk + i)" using csub_nth i by simp
    also have "\<dots> = Bs ! i" using i askk bskk unfolding vals_def by (simp add: nth_append)
    finally show "map csub (drop kk atoms) ! i = Bs ! i" .
  qed
  have sub_lhs: "sub_formula csub (conn_cong_lhs c) = Conn c As"
    unfolding conn_cong_lhs_def atoms_def[symmetric] kk_def[symmetric]
    by (simp only: sub_formula.simps list.map map_map comp_def map_lhs)
  have sub_rhs: "sub_formula csub (conn_cong_rhs c) = Conn c Bs"
    unfolding conn_cong_rhs_def atoms_def[symmetric] kk_def[symmetric]
    by (simp only: sub_formula.simps list.map map_map comp_def map_rhs)
  have ci_thesis: "thesis ci = iff_form (Conn c As) (Conn c Bs)"
  proof -
    have "thesis ci = sub_formula csub (iff_form (conn_cong_lhs c) (conn_cong_rhs c))"
      unfolding ci_def using conn_cong_base_proof_spec by simp
    also have "\<dots> = iff_form (sub_formula csub (conn_cong_lhs c))
                              (sub_formula csub (conn_cong_rhs c))"
      by (rule sub_formula_iff_form[OF csub_conn])
    also have "\<dots> = iff_form (Conn c As) (Conn c Bs)" using sub_lhs sub_rhs by simp
    finally show ?thesis .
  qed
  have ci_asm: "assumptions ci = (\<lambda>i. iff_form (As ! i) (Bs ! i)) ` {..< kk}"
  proof -
    have "assumptions ci = sub_formula csub ` (conn_cong_asms c)"
      unfolding ci_def using conn_cong_base_proof_spec by simp
    also have "\<dots> = (\<lambda>i. iff_form (As ! i) (Bs ! i)) ` {..< kk}"
    proof -
      have "\<And>i. i < kk \<Longrightarrow>
              sub_formula csub (iff_form (Atom (atoms ! i)) (Atom (atoms ! (kk + i))))
              = iff_form (As ! i) (Bs ! i)"
      proof -
        fix i assume i: "i < kk"
        have "sub_formula csub (iff_form (Atom (atoms ! i)) (Atom (atoms ! (kk + i))))
            = iff_form (sub_formula csub (Atom (atoms ! i)))
                       (sub_formula csub (Atom (atoms ! (kk + i))))"
          by (rule sub_formula_iff_form[OF csub_conn])
        moreover have "csub (atoms ! i) = As ! i"
          using csub_nth i askk unfolding vals_def by (simp add: nth_append)
        moreover have "csub (atoms ! (kk + i)) = Bs ! i"
          using csub_nth i askk bskk unfolding vals_def by (simp add: nth_append)
        ultimately show "sub_formula csub (iff_form (Atom (atoms ! i)) (Atom (atoms ! (kk + i))))
                         = iff_form (As ! i) (Bs ! i)" by simp
      qed
      thus ?thesis unfolding conn_cong_asms_def atoms_def[symmetric] kk_def[symmetric]
        by (auto simp: image_image)
    qed
    finally show ?thesis .
  qed

  \<comment> \<open>step bounds for the substituted proof\<close>
  have ci_len: "\<And>s. s \<in> set (steps ci)
                 \<Longrightarrow> len_formula s \<le> conn_cong_max_step_len * (2 * kk * LAB + 1)"
  proof -
    fix s assume "s \<in> set (steps ci)"
    then obtain s0 where s0: "s0 \<in> set (steps (conn_cong_base_proof c))"
                     and s_eq: "s = sub_formula csub s0" using ci_steps by auto
    have "len_formula s \<le> len_formula s0 * len_sub (set atoms) csub"
      using s_eq sub_formula_bound[OF fin_at sub_id] by simp
    also have "\<dots> \<le> len_formula s0 * (2 * kk * LAB + 1)"
      using len_sub_le by (rule mult_le_mono2)
    also have "\<dots> \<le> conn_cong_max_step_len * (2 * kk * LAB + 1)"
    proof (rule mult_le_mono1)
      have "len_formula s0 \<le> conn_cong_step_len c"
        unfolding conn_cong_step_len_def using s0 by simp
      thus "len_formula s0 \<le> conn_cong_max_step_len"
        using conn_cong_max_ge[of c] by linarith
    qed
    finally show "len_formula s \<le> conn_cong_max_step_len * (2 * kk * LAB + 1)" .
  qed
  have ci_dep: "\<And>s. s \<in> set (steps ci) \<Longrightarrow> depth_formula s \<le> conn_cong_max_step_depth + DAB"
  proof -
    fix s assume "s \<in> set (steps ci)"
    then obtain s0 where s0: "s0 \<in> set (steps (conn_cong_base_proof c))"
                     and s_eq: "s = sub_formula csub s0" using ci_steps by auto
    have "depth_formula s \<le> depth_formula s0 + depth_sub (set atoms) csub"
      using s_eq sub_formula_depth_bound[OF fin_at sub_id] by simp
    also have "\<dots> \<le> conn_cong_step_depth c + DAB"
    proof -
      have "depth_formula s0 \<le> conn_cong_step_depth c"
        unfolding conn_cong_step_depth_def using s0 by simp
      thus ?thesis using dep_sub_le by linarith
    qed
    also have "\<dots> \<le> conn_cong_max_step_depth + DAB"
      using conn_cong_max_ge[of c] by linarith
    finally show "depth_formula s \<le> conn_cong_max_step_depth + DAB" .
  qed

  \<comment> \<open>the input proofs and the cut\<close>
  define ip where "ip = (\<lambda>i. SOME pr. valid_proof F pr \<and> assumptions pr = {}
        \<and> frege_proof.thesis pr = iff_form (As ! i) (Bs ! i)
        \<and> length (steps pr) \<le> lf i
        \<and> (\<forall>s \<in> set (steps pr). len_formula s \<le> Sc)
        \<and> (\<forall>s \<in> set (steps pr). depth_formula s \<le> Dc)
        \<and> (\<forall>s \<in> set (steps pr). formula_well_formed (alphabet F) s))"
  have ip_spec: "\<And>i. i < kk \<Longrightarrow>
       valid_proof F (ip i) \<and> assumptions (ip i) = {}
       \<and> frege_proof.thesis (ip i) = iff_form (As ! i) (Bs ! i)
       \<and> length (steps (ip i)) \<le> lf i
       \<and> (\<forall>s \<in> set (steps (ip i)). len_formula s \<le> Sc)
       \<and> (\<forall>s \<in> set (steps (ip i)). depth_formula s \<le> Dc)
       \<and> (\<forall>s \<in> set (steps (ip i)). formula_well_formed (alphabet F) s)"
  proof -
    fix i assume i: "i < kk"
    hence "i < length As" using askk by simp
    then obtain l s d where pbi: "provable_balanced_iff (As ! i) (Bs ! i) l s d"
      and lLc: "l \<le> lf i" and sSc: "s \<le> Sc" and dDc: "d \<le> Dc" using prem by blast
    from pbi obtain pr where pr: "valid_proof F pr" "assumptions pr = {}"
        "frege_proof.thesis pr = iff_form (As ! i) (Bs ! i)" "length (steps pr) \<le> l"
        "\<forall>s' \<in> set (steps pr). len_formula s' \<le> s"
        "\<forall>s' \<in> set (steps pr). depth_formula s' \<le> d"
        "\<forall>s' \<in> set (steps pr). formula_well_formed (alphabet F) s'"
      unfolding provable_balanced_iff_def by blast
    have ex: "\<exists>pr. valid_proof F pr \<and> assumptions pr = {}
          \<and> frege_proof.thesis pr = iff_form (As ! i) (Bs ! i)
          \<and> length (steps pr) \<le> lf i
          \<and> (\<forall>s \<in> set (steps pr). len_formula s \<le> Sc)
          \<and> (\<forall>s \<in> set (steps pr). depth_formula s \<le> Dc)
          \<and> (\<forall>s \<in> set (steps pr). formula_well_formed (alphabet F) s)"
    proof (intro exI[where x = pr] conjI)
      show "valid_proof F pr" by (rule pr(1))
      show "assumptions pr = {}" by (rule pr(2))
      show "frege_proof.thesis pr = iff_form (As ! i) (Bs ! i)" by (rule pr(3))
      show "length (steps pr) \<le> lf i" using pr(4) lLc by linarith
      show "\<forall>s \<in> set (steps pr). len_formula s \<le> Sc" using pr(5) sSc by force
      show "\<forall>s \<in> set (steps pr). depth_formula s \<le> Dc" using pr(6) dDc by force
      show "\<forall>s \<in> set (steps pr). formula_well_formed (alphabet F) s" by (rule pr(7))
    qed
    show "valid_proof F (ip i) \<and> assumptions (ip i) = {}
       \<and> frege_proof.thesis (ip i) = iff_form (As ! i) (Bs ! i)
       \<and> length (steps (ip i)) \<le> lf i
       \<and> (\<forall>s \<in> set (steps (ip i)). len_formula s \<le> Sc)
       \<and> (\<forall>s \<in> set (steps (ip i)). depth_formula s \<le> Dc)
       \<and> (\<forall>s \<in> set (steps (ip i)). formula_well_formed (alphabet F) s)"
      unfolding ip_def by (rule someI_ex[OF ex])
  qed
  define ps where "ps = map ip [0..< kk]"
  have ps_elem: "\<And>p. p \<in> set ps \<Longrightarrow> \<exists>i. i < kk \<and> p = ip i"
  proof -
    fix p assume "p \<in> set ps"
    then obtain i where "i \<in> set [0..< kk]" "p = ip i" unfolding ps_def by auto
    thus "\<exists>i. i < kk \<and> p = ip i" by auto
  qed
  have ps_valid: "\<forall>p \<in> set ps. valid_proof F p \<and> assumptions p = {}"
  proof
    fix p assume "p \<in> set ps"
    then obtain i where "i < kk" "p = ip i" using ps_elem by blast
    thus "valid_proof F p \<and> assumptions p = {}" using ip_spec by simp
  qed
  define cb where "cb = foldr combine_proofs ps ci"
  have cb_spec: "valid_proof F cb
       \<and> assumptions cb = assumptions ci - (\<Union>p \<in> set ps. set (steps p))
       \<and> frege_proof.thesis cb = frege_proof.thesis ci
       \<and> steps cb = concat (map steps ps) @ steps ci"
    unfolding cb_def
    by (rule mp[OF combine_fold_spec[OF valid_ci] ps_valid])
  have thesis_in: "\<And>i. i < kk \<Longrightarrow>
       iff_form (As ! i) (Bs ! i) \<in> (\<Union>p \<in> set ps. set (steps p))"
  proof -
    fix i assume i: "i < kk"
    have ipin: "ip i \<in> set ps" using i by (simp add: ps_def)
    have ne: "steps (ip i) \<noteq> []" using ip_spec[OF i] unfolding valid_proof_def by simp
    have "frege_proof.thesis (ip i) = last (steps (ip i))"
      using ip_spec[OF i] unfolding valid_proof_def by simp
    hence "iff_form (As ! i) (Bs ! i) = last (steps (ip i))" using ip_spec[OF i] by simp
    hence "iff_form (As ! i) (Bs ! i) \<in> set (steps (ip i))"
      using ne by simp
    thus "iff_form (As ! i) (Bs ! i) \<in> (\<Union>p \<in> set ps. set (steps p))" using ipin by blast
  qed
  have sub_asm: "assumptions ci \<subseteq> (\<Union>p \<in> set ps. set (steps p))"
  proof
    fix x assume "x \<in> assumptions ci"
    then obtain i where "i < kk" "x = iff_form (As ! i) (Bs ! i)"
      using ci_asm by auto
    thus "x \<in> (\<Union>p \<in> set ps. set (steps p))" using thesis_in by auto
  qed
  have cb_asm: "assumptions cb = {}"
  proof -
    have "assumptions cb = assumptions ci - (\<Union>p \<in> set ps. set (steps p))"
      using cb_spec by simp
    thus ?thesis using sub_asm by (simp add: Diff_eq_empty_iff)
  qed
  have cb_thesis: "frege_proof.thesis cb = iff_form (Conn c As) (Conn c Bs)"
    using cb_spec ci_thesis by simp
  have len_ps: "length ps = kk" unfolding ps_def by simp
  have cb_lines: "length (steps cb) \<le> sum_list (map lf [0..< length As]) + conn_cong_max_lines"
  proof -
    have "length (steps cb) = length (concat (map steps ps)) + length (steps ci)"
      using cb_spec by simp
    also have "length (concat (map steps ps)) = sum_list (map (length \<circ> steps) ps)"
      by (simp add: length_concat comp_def)
    also have "sum_list (map (length \<circ> steps) ps)
               = sum_list (map (\<lambda>i. length (steps (ip i))) [0..< kk])"
      unfolding ps_def by (simp add: comp_def)
    also have "\<dots> \<le> sum_list (map lf [0..< kk])"
    proof (rule sum_list_mono)
      fix i assume "i \<in> set [0..< kk]"
      hence "i < kk" by simp
      thus "length (steps (ip i)) \<le> lf i" using ip_spec by simp
    qed
    finally have lcb: "length (steps cb) \<le> sum_list (map lf [0..< kk]) + length (steps ci)"
      by simp
    have "length (steps ci) \<le> conn_cong_max_lines"
      using ci_lines conn_cong_max_ge[of c] by simp
    moreover have "sum_list (map lf [0..< kk]) = sum_list (map lf [0..< length As])"
      using askk by simp
    ultimately show ?thesis using lcb by linarith
  qed
  have cb_len: "\<forall>s \<in> set (steps cb). len_formula s
                  \<le> Sc + conn_cong_max_step_len * (2 * kk * LAB + 1)"
  proof
    fix s assume "s \<in> set (steps cb)"
    hence "s \<in> set (concat (map steps ps)) \<or> s \<in> set (steps ci)" using cb_spec by auto
    thus "len_formula s \<le> Sc + conn_cong_max_step_len * (2 * kk * LAB + 1)"
    proof
      assume "s \<in> set (concat (map steps ps))"
      then obtain p where pps: "p \<in> set ps" and sp: "s \<in> set (steps p)" by auto
      obtain i where "i < kk" "p = ip i" using ps_elem[OF pps] by blast
      hence "len_formula s \<le> Sc" using ip_spec sp by simp
      thus ?thesis by linarith
    next
      assume "s \<in> set (steps ci)"
      hence "len_formula s \<le> conn_cong_max_step_len * (2 * kk * LAB + 1)"
        using ci_len by simp
      thus ?thesis by linarith
    qed
  qed
  have cb_dep: "\<forall>s \<in> set (steps cb). depth_formula s
                  \<le> max Dc (conn_cong_max_step_depth + DAB)"
  proof
    fix s assume "s \<in> set (steps cb)"
    hence "s \<in> set (concat (map steps ps)) \<or> s \<in> set (steps ci)" using cb_spec by auto
    thus "depth_formula s \<le> max Dc (conn_cong_max_step_depth + DAB)"
    proof
      assume "s \<in> set (concat (map steps ps))"
      then obtain p where pps: "p \<in> set ps" and sp: "s \<in> set (steps p)" by auto
      obtain i where "i < kk" "p = ip i" using ps_elem[OF pps] by blast
      hence "depth_formula s \<le> Dc" using ip_spec sp by simp
      thus ?thesis by simp
    next
      assume "s \<in> set (steps ci)"
      hence "depth_formula s \<le> conn_cong_max_step_depth + DAB" using ci_dep by simp
      thus ?thesis by simp
    qed
  qed
  have cb_wf: "\<forall>s \<in> set (steps cb). formula_well_formed (alphabet F) s"
  proof
    fix s assume "s \<in> set (steps cb)"
    hence "s \<in> set (concat (map steps ps)) \<or> s \<in> set (steps ci)" using cb_spec by auto
    thus "formula_well_formed (alphabet F) s"
    proof
      assume "s \<in> set (concat (map steps ps))"
      then obtain p where pps: "p \<in> set ps" and sp: "s \<in> set (steps p)" by auto
      obtain i where "i < kk" "p = ip i" using ps_elem[OF pps] by blast
      thus ?thesis using ip_spec sp by blast
    next
      assume "s \<in> set (steps ci)" thus ?thesis using ci_wf by blast
    qed
  qed
  have main: "provable_balanced_iff (Conn c As) (Conn c Bs)
          (sum_list (map lf [0..< length As]) + conn_cong_max_lines)
          (Sc + conn_cong_max_step_len * (2 * kk * LAB + 1))
          (max Dc (conn_cong_max_step_depth + DAB))"
    unfolding provable_balanced_iff_def
  proof (intro exI[where x = cb] conjI)
    show "valid_proof F cb" using cb_spec by simp
    show "assumptions cb = {}" using cb_asm .
    show "frege_proof.thesis cb = iff_form (Conn c As) (Conn c Bs)" using cb_thesis .
    show "length (steps cb) \<le> sum_list (map lf [0..< length As]) + conn_cong_max_lines"
      using cb_lines .
    show "\<forall>s \<in> set (steps cb). len_formula s
            \<le> Sc + conn_cong_max_step_len * (2 * kk * LAB + 1)" using cb_len .
    show "\<forall>s \<in> set (steps cb). depth_formula s
            \<le> max Dc (conn_cong_max_step_depth + DAB)" using cb_dep .
    show "\<forall>s \<in> set (steps cb). formula_well_formed (alphabet F) s" using cb_wf .
  qed
  show ?thesis
    using main[unfolded askk[symmetric] LAB_def DAB_def] by blast
qed

subsubsection \<open>Size and depth bounds for substitution\<close>

lemma occ_len_le:
  assumes "v \<in> var_set_form g"
  shows "len_formula (sub v) \<le> (\<Sum> w \<in> var_set_form g. len_formula (sub w))"
proof -
  have fin: "finite (var_set_form g)" by (rule var_set_form_finite)
  have "(\<Sum> w \<in> var_set_form g. len_formula (sub w))
        = len_formula (sub v) + (\<Sum> w \<in> var_set_form g - {v}. len_formula (sub w))"
    using sum.remove[OF fin assms] .
  thus ?thesis by simp
qed

lemma len_strans_cap:
  assumes cap: "\<And>v. v \<in> var_set_form g \<Longrightarrow> len_formula (spira_trans (sub v)) \<le> MM"
      and mm1: "1 \<le> MM"
  shows "len_formula (sub_formula (\<lambda>v. spira_trans (sub v)) g) \<le> MM * len_formula g"
  using cap
proof (induction g)
  case (Atom a)
  have "a \<in> var_set_form (Atom a)" by simp
  thus ?case using Atom.prems by simp
next
  case (Conn c gs)
  have "len_formula (sub_formula (\<lambda>v. spira_trans (sub v)) (Conn c gs))
        = 1 + (\<Sum>x \<leftarrow> gs. len_formula (sub_formula (\<lambda>v. spira_trans (sub v)) x))"
    by (simp add: comp_def)
  also have "\<dots> \<le> 1 + (\<Sum>x \<leftarrow> gs. MM * len_formula x)"
  proof -
    have "(\<Sum>x \<leftarrow> gs. len_formula (sub_formula (\<lambda>v. spira_trans (sub v)) x))
          \<le> (\<Sum>x \<leftarrow> gs. MM * len_formula x)"
    proof (rule sum_list_mono)
      fix x assume x: "x \<in> set gs"
      have "\<And>v. v \<in> var_set_form x \<Longrightarrow> len_formula (spira_trans (sub v)) \<le> MM"
        using x Conn.prems by auto
      thus "len_formula (sub_formula (\<lambda>v. spira_trans (sub v)) x) \<le> MM * len_formula x"
        using Conn.IH x by blast
    qed
    thus ?thesis by simp
  qed
  also have "1 + (\<Sum>x \<leftarrow> gs. MM * len_formula x)
             = 1 + MM * (\<Sum>x \<leftarrow> gs. len_formula x)"
    by (simp add: sum_list_const_mult)
  also have "\<dots> \<le> MM * (1 + (\<Sum>x \<leftarrow> gs. len_formula x))"
    using mm1 by (simp add: distrib_left)
  also have "\<dots> = MM * len_formula (Conn c gs)" by simp
  finally show ?case .
qed

lemma depth_strans_le:
  shows "\<exists>tcm::real. 1 \<le> tcm \<and> (\<forall>g sub. (\<forall>v. formula_well_formed (alphabet F) (sub v)) \<longrightarrow>
           real (depth_formula (sub_formula (\<lambda>v. spira_trans (sub v)) g))
           \<le> real (depth_formula g)
              + tcm * log 2 (real (len_formula g
                              + (\<Sum>w\<in>var_set_form g. len_formula (sub w))) + 1))"
proof -
  obtain tc :: real where tc:
    "\<forall>f. formula_well_formed (alphabet F) f \<longrightarrow>
       real (depth_formula (spira_trans f)) \<le> tc * log 2 (real (len_formula f) + 1)"
    using trans_c by blast
  define tcm where "tcm = max tc 1"
  have tcm1: "1 \<le> tcm" unfolding tcm_def by simp
  have "\<forall>g sub. (\<forall>v. formula_well_formed (alphabet F) (sub v)) \<longrightarrow>
           real (depth_formula (sub_formula (\<lambda>v. spira_trans (sub v)) g))
           \<le> real (depth_formula g)
              + tcm * log 2 (real (len_formula g
                              + (\<Sum>w\<in>var_set_form g. len_formula (sub w))) + 1)"
  proof (intro allI impI)
    fix g :: "'a formula" and sub :: "string \<Rightarrow> 'a formula"
    assume wfsub: "\<forall>v. formula_well_formed (alphabet F) (sub v)"
    define M :: nat where "M = len_formula g + (\<Sum>w\<in>var_set_form g. len_formula (sub w))"
    have Mge: "1 \<le> M" unfolding M_def using len_formula_ge_1[of g] by simp
    let ?sub2 = "\<lambda>v. if v \<in> var_set_form g then spira_trans (sub v) else Atom v"
    have agree: "sub_formula (\<lambda>v. spira_trans (sub v)) g = sub_formula ?sub2 g"
      by (rule sub_formula_agree) simp
    have fin: "finite (var_set_form g)" by (rule var_set_form_finite)
    have id_off: "\<forall>v. v \<notin> var_set_form g \<longrightarrow> ?sub2 v = Atom v" by simp
    have db: "depth_formula (sub_formula ?sub2 g)
              \<le> depth_formula g + depth_sub (var_set_form g) ?sub2"
      by (rule sub_formula_depth_bound[OF fin id_off])
    \<comment> \<open>bound the substitution depth by tcm * log2 (M+1)\<close>
    have dsub_le: "real (depth_sub (var_set_form g) ?sub2) \<le> tcm * log 2 (real M + 1)"
    proof -
      have logge: "1 \<le> log 2 (real M + 1)"
        using Mge by (simp add: le_log_iff)
      have "depth_sub (var_set_form g) ?sub2
            \<in> insert 1 ((\<lambda>v. depth_formula (?sub2 v)) ` var_set_form g)"
        unfolding depth_sub_def by (rule Max_in) (use fin in auto)
      then consider "depth_sub (var_set_form g) ?sub2 = 1"
        | v where "v \<in> var_set_form g"
                  "depth_sub (var_set_form g) ?sub2 = depth_formula (?sub2 v)" by auto
      thus ?thesis
      proof cases
        case 1
        have "real 1 \<le> 1 * log 2 (real M + 1)" using logge by simp
        also have "\<dots> \<le> tcm * log 2 (real M + 1)"
          using tcm1 logge by (simp add: mult_right_mono)
        finally show ?thesis using 1 by simp
      next
        case (2 v)
        have wfv: "formula_well_formed (alphabet F) (sub v)" using wfsub by simp
        have "real (depth_formula (?sub2 v)) = real (depth_formula (spira_trans (sub v)))"
          using 2 by simp
        also have "\<dots> \<le> tc * log 2 (real (len_formula (sub v)) + 1)"
          using tc wfv by simp
        also have "\<dots> \<le> tcm * log 2 (real (len_formula (sub v)) + 1)"
        proof (rule mult_right_mono)
          show "tc \<le> tcm" unfolding tcm_def by simp
          show "0 \<le> log 2 (real (len_formula (sub v)) + 1)"
            using len_formula_ge_1[of "sub v"] by (simp add: le_log_iff)
        qed
        also have "\<dots> \<le> tcm * log 2 (real M + 1)"
        proof (rule mult_left_mono)
          have vin: "v \<in> var_set_form g" using 2 by simp
          have "len_formula (sub v) \<le> (\<Sum>w\<in>var_set_form g. len_formula (sub w))"
            by (rule occ_len_le[OF vin])
          hence "len_formula (sub v) \<le> M" unfolding M_def by simp
          thus "log 2 (real (len_formula (sub v)) + 1) \<le> log 2 (real M + 1)"
            by simp
          show "0 \<le> tcm" using tcm1 by simp
        qed
        finally show ?thesis using 2 by simp
      qed
    qed
    have "real (depth_formula (sub_formula (\<lambda>v. spira_trans (sub v)) g))
          = real (depth_formula (sub_formula ?sub2 g))" using agree by simp
    also have "\<dots> \<le> real (depth_formula g + depth_sub (var_set_form g) ?sub2)"
      using db by simp
    also have "\<dots> = real (depth_formula g) + real (depth_sub (var_set_form g) ?sub2)"
      by simp
    also have "\<dots> \<le> real (depth_formula g) + tcm * log 2 (real M + 1)"
      using dsub_le by simp
    finally show "real (depth_formula (sub_formula (\<lambda>v. spira_trans (sub v)) g))
                  \<le> real (depth_formula g)
                     + tcm * log 2 (real (len_formula g
                                     + (\<Sum>w\<in>var_set_form g. len_formula (sub w))) + 1)"
      unfolding M_def .
  qed
  thus ?thesis using tcm1 by blast
qed

lemma len_sub_form_le:
  shows "len_formula (sub_formula sub f)
         \<le> len_formula f * (len_formula f + (\<Sum>v\<in>var_set_form f. len_formula (sub v)))"
proof -
  let ?sub2 = "\<lambda>v. if v \<in> var_set_form f then sub v else Atom v"
  have agree: "sub_formula sub f = sub_formula ?sub2 f"
    by (rule sub_formula_agree) simp
  have fin: "finite (var_set_form f)" by (rule var_set_form_finite)
  have id_off: "\<forall>v. v \<notin> var_set_form f \<longrightarrow> ?sub2 v = Atom v" by simp
  have "len_formula (sub_formula ?sub2 f)
        \<le> len_formula f * len_sub (var_set_form f) ?sub2"
    by (rule sub_formula_bound[OF fin id_off])
  also have "\<dots> \<le> len_formula f
                  * (len_formula f + (\<Sum>v\<in>var_set_form f. len_formula (sub v)))"
  proof (rule mult_le_mono2)
    have eq: "(\<Sum>v\<in>var_set_form f. len_formula (?sub2 v))
              = (\<Sum>v\<in>var_set_form f. len_formula (sub v))"
      by (rule sum.cong) auto
    have "len_sub (var_set_form f) ?sub2
          = max 1 (\<Sum>v\<in>var_set_form f. len_formula (sub v))"
      unfolding len_sub_def using eq by simp
    thus "len_sub (var_set_form f) ?sub2
          \<le> len_formula f + (\<Sum>v\<in>var_set_form f. len_formula (sub v))"
      using len_formula_ge_1[of f] by simp
  qed
  finally show ?thesis using agree by simp
qed

lemma nat_le_floor:
  assumes "real n \<le> x" shows "n \<le> nat \<lfloor>x\<rfloor>"
proof -
  have "int n \<le> \<lfloor>x\<rfloor>" using assms by (simp add: le_floor_iff)
  from nat_mono[OF this] show ?thesis by simp
qed

subsubsection \<open>Lemma 6.4: the bounded structural commutation\<close>

(* M = |P| + Sum |Qi| = len f + (sum v in var_set_form f. |sub v|), the input-size
   measure.  Bounds: lines/size <= poly bnd M (= M^O(1)); depth <= depth f + c*log2(M+1)
   (the +depth f is forced since thesis = last step makes dep >= depth (S' f) >= depth f). *)
lemma transform_commutes_form:
  shows "\<exists> (bnd :: nat poly) (c :: real).
           \<forall> f sub. formula_well_formed (alphabet F) f
                    \<and> (\<forall>f' \<in> range sub. formula_well_formed (alphabet F) f') \<longrightarrow>
             (let M = len_formula f + (\<Sum> v \<in> var_set_form f. len_formula (sub v))
              in (\<exists> lines sz dep.
                    provable_balanced_iff (spira_trans (sub_formula sub f))
                      (sub_formula (\<lambda> v. spira_trans (sub v)) f) lines sz dep
                  \<and> lines \<le> poly bnd M
                  \<and> sz \<le> poly bnd M
                  \<and> real dep \<le> real (depth_formula f) + c * log 2 (real M + 1)))"
proof -
  obtain bnd62 c62 where tcc:
    "\<forall>conn ps. (\<forall>p \<in> set ps. formula_well_formed (alphabet F) p)
               \<and> length ps = arity (alphabet F) conn \<longrightarrow>
       (\<exists>lines sz dep. provable_balanced_iff (spira_trans (Conn conn ps))
            (Conn conn (map spira_trans ps)) lines sz dep
          \<and> lines \<le> poly bnd62 (len_formula (Conn conn ps))
          \<and> sz \<le> poly bnd62 (len_formula (Conn conn ps))
          \<and> real dep \<le> c62 * log 2 (real (len_formula (Conn conn ps)) + 1))"
    using transform_commutes_conn by blast
  obtain tc :: real where tc:
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
  define MA where "MA = Max (arity (alphabet F) ` UNIV)"
  define BIGC :: nat where
    "BIGC = 2 * (conn_cong_max_step_len + conn_cong_max_lines + trans_step_len + trans_lines
             + refl_step_len + refl_lines + 1) * (MA + 1) * (MA + 1)"
  define PP :: "nat poly" where
    "PP = pcompose bnd62 (monom 1 2)
        + Polynomial.smult BIGC (pcompose rebal_tb (monom 1 2))
        + Polynomial.smult BIGC (monom 1 1 * rebal_tb)
        + [: BIGC :]"
  define cc :: real where
    "cc = real (conn_cong_max_step_depth + trans_step_depth + refl_step_depth + 1)
          + 3 * \<bar>c62\<bar> + 4 * \<bar>tc\<bar> + 3 * tcm + 5"
  have ppval: "\<And>M. poly PP M = poly bnd62 (M^2) + BIGC * poly rebal_tb (M^2)
                     + BIGC * (M * poly rebal_tb M) + BIGC"
  proof -
    fix M :: nat
    have t1: "poly (pcompose bnd62 (monom 1 2)) M = poly bnd62 (M^2)"
      by (simp add: poly_pcompose poly_monom)
    have t2: "poly (Polynomial.smult BIGC (pcompose rebal_tb (monom 1 2))) M
              = BIGC * poly rebal_tb (M^2)"
      by (simp add: poly_pcompose poly_monom)
    have t3: "poly (Polynomial.smult BIGC (monom 1 1 * rebal_tb)) M
              = BIGC * (M * poly rebal_tb M)"
      by (simp add: poly_monom)
    show "poly PP M = poly bnd62 (M^2) + BIGC * poly rebal_tb (M^2)
                      + BIGC * (M * poly rebal_tb M) + BIGC"
      unfolding PP_def by (simp only: poly_add t1 t2 t3 poly_pCons poly_0 mult_zero_right
                                       add_0 add.assoc)
  qed
  have ppBIGC: "\<And>M. BIGC \<le> poly PP M" using ppval by simp
  have ppRT: "\<And>M. 1 \<le> M \<Longrightarrow> BIGC * poly rebal_tb M \<le> poly PP M"
  proof -
    fix M :: nat assume "1 \<le> M"
    have "BIGC * poly rebal_tb M \<le> BIGC * (M * poly rebal_tb M)"
      using \<open>1 \<le> M\<close> by (simp add: mult_le_mono2)
    also have "\<dots> \<le> poly PP M" using ppval[of M] by simp
    finally show "BIGC * poly rebal_tb M \<le> poly PP M" .
  qed
  have bigS: "conn_cong_max_step_len + conn_cong_max_lines + trans_step_len + trans_lines
              + refl_step_len + refl_lines + 1 \<le> BIGC"
  proof -
    let ?S = "conn_cong_max_step_len + conn_cong_max_lines + trans_step_len + trans_lines
              + refl_step_len + refl_lines + 1"
    have "?S * 1 \<le> ?S * (2 * ((MA + 1) * (MA + 1)))" by (rule mult_le_mono2) simp
    thus ?thesis unfolding BIGC_def by (simp add: algebra_simps)
  qed
  have ppL: "\<And>M N C. N \<le> M * M \<Longrightarrow> C \<le> BIGC \<Longrightarrow> poly bnd62 N + C \<le> poly PP M"
  proof -
    fix M N C :: nat assume h1: "N \<le> M * M" and h2: "C \<le> BIGC"
    have "poly bnd62 N \<le> poly bnd62 (M * M)" using h1 by (rule poly_nat_mono)
    moreover have "poly PP M = poly bnd62 (M * M) + BIGC * poly rebal_tb (M * M)
                               + BIGC * (M * poly rebal_tb M) + BIGC"
      using ppval[of M] by (simp add: power2_eq_square)
    ultimately show "poly bnd62 N + C \<le> poly PP M" using h2 by linarith
  qed
  have main: "\<And>f sub. formula_well_formed (alphabet F) f
       \<Longrightarrow> (\<forall>v. formula_well_formed (alphabet F) (sub v))
       \<Longrightarrow> (\<exists>lines sz dep.
              provable_balanced_iff (spira_trans (sub_formula sub f))
                (sub_formula (\<lambda>v. spira_trans (sub v)) f) lines sz dep
            \<and> lines \<le> len_formula (sub_formula sub f)
                * poly PP (len_formula f + (\<Sum>v\<in>var_set_form f. len_formula (sub v)))
            \<and> sz \<le> len_formula (sub_formula sub f)
                * poly PP (len_formula f + (\<Sum>v\<in>var_set_form f. len_formula (sub v)))
            \<and> real dep \<le> real (depth_formula f)
                + cc * log 2 (real (len_formula f
                                + (\<Sum>v\<in>var_set_form f. len_formula (sub v))) + 1))"
  proof -
    fix f0 :: "'a formula" and sub :: "string \<Rightarrow> 'a formula"
    have ind: "formula_well_formed (alphabet F) f0
        \<longrightarrow> (\<forall>v. formula_well_formed (alphabet F) (sub v))
        \<longrightarrow> (\<exists>lines sz dep.
               provable_balanced_iff (spira_trans (sub_formula sub f0))
                 (sub_formula (\<lambda>v. spira_trans (sub v)) f0) lines sz dep
             \<and> lines \<le> len_formula (sub_formula sub f0)
                 * poly PP (len_formula f0 + (\<Sum>v\<in>var_set_form f0. len_formula (sub v)))
             \<and> sz \<le> len_formula (sub_formula sub f0)
                 * poly PP (len_formula f0 + (\<Sum>v\<in>var_set_form f0. len_formula (sub v)))
             \<and> real dep \<le> real (depth_formula f0)
                 + cc * log 2 (real (len_formula f0
                                 + (\<Sum>v\<in>var_set_form f0. len_formula (sub v))) + 1))"
    proof (induction f0)
      case (Atom a)
      show ?case
      proof (intro impI)
        assume "formula_well_formed (alphabet F) (Atom a)"
        assume wfs: "\<forall>v. formula_well_formed (alphabet F) (sub v)"
        have wfsa: "formula_well_formed (alphabet F) (sub a)" using wfs by simp
        define MM where "MM = len_formula (Atom a)
                              + (\<Sum>v\<in>var_set_form (Atom a). len_formula (sub v))"
        have Meq: "MM = 1 + len_formula (sub a)" unfolding MM_def by simp
        have lensa: "1 \<le> len_formula (sub a)" by (rule len_formula_ge_1)
        have Mge: "1 \<le> MM" using Meq by simp
        have SS: "sub_formula sub (Atom a) = sub a" by simp
        have SS': "sub_formula (\<lambda>v. spira_trans (sub v)) (Atom a) = spira_trans (sub a)" by simp
        have refl: "provable_balanced_iff (spira_trans (sub a)) (spira_trans (sub a))
                      refl_lines (refl_step_len * len_formula (spira_trans (sub a)))
                      (refl_step_depth + depth_formula (spira_trans (sub a)))"
          by (rule iff_refl[OF spira_trans_wf[OF wfsa]])
        \<comment> \<open>@{term BIGC} dominates the reflexivity constants\<close>
        have reflB: "refl_lines \<le> BIGC \<and> refl_step_len \<le> BIGC" using bigS by linarith
        \<comment> \<open>lines bound\<close>
        have b1: "refl_lines \<le> len_formula (sub a) * poly PP MM"
        proof -
          have "refl_lines \<le> BIGC" using reflB by simp
          also have "\<dots> \<le> poly PP MM" by (rule ppBIGC)
          also have "\<dots> \<le> len_formula (sub a) * poly PP MM"
            using mult_le_mono1[OF lensa] by simp
          finally show ?thesis .
        qed
        \<comment> \<open>size bound\<close>
        have ltsa: "len_formula (spira_trans (sub a)) \<le> poly rebal_tb (len_formula (sub a))"
          by (rule spira_trans_len_le_tb[OF wfsa order_refl])
        have b2: "refl_step_len * len_formula (spira_trans (sub a))
                  \<le> len_formula (sub a) * poly PP MM"
        proof -
          have "refl_step_len * len_formula (spira_trans (sub a))
                \<le> refl_step_len * poly rebal_tb (len_formula (sub a))"
            using ltsa by (rule mult_le_mono2)
          also have "\<dots> \<le> BIGC * poly rebal_tb MM"
          proof (rule mult_le_mono)
            show "refl_step_len \<le> BIGC" using reflB by simp
            show "poly rebal_tb (len_formula (sub a)) \<le> poly rebal_tb MM"
              using Meq by (simp add: poly_nat_mono)
          qed
          also have "\<dots> \<le> poly PP MM" using ppRT[OF Mge] .
          also have "\<dots> \<le> len_formula (sub a) * poly PP MM"
            using mult_le_mono1[OF lensa] by simp
          finally show ?thesis .
        qed
        \<comment> \<open>depth bound\<close>
        have b3: "real (refl_step_depth + depth_formula (spira_trans (sub a)))
                  \<le> real (depth_formula (Atom a)) + cc * log 2 (real MM + 1)"
        proof -
          have logge: "1 \<le> log 2 (real MM + 1)" using Mge by (simp add: le_log_iff)
          have dtsa: "real (depth_formula (spira_trans (sub a)))
                      \<le> tc * log 2 (real (len_formula (sub a)) + 1)" using tc wfsa by simp
          have logmono: "log 2 (real (len_formula (sub a)) + 1) \<le> log 2 (real MM + 1)"
            using Meq by simp
          have logsann: "0 \<le> log 2 (real (len_formula (sub a)) + 1)"
            using len_formula_ge_1[of "sub a"] by (simp add: le_log_iff)
          have dts: "real (depth_formula (spira_trans (sub a))) \<le> \<bar>tc\<bar> * log 2 (real MM + 1)"
          proof -
            have "tc * log 2 (real (len_formula (sub a)) + 1)
                  \<le> \<bar>tc\<bar> * log 2 (real (len_formula (sub a)) + 1)"
              using logsann by (simp add: mult_right_mono)
            also have "\<dots> \<le> \<bar>tc\<bar> * log 2 (real MM + 1)"
              using logmono by (simp add: mult_left_mono)
            finally show ?thesis using dtsa by linarith
          qed
          have rsd_le: "real refl_step_depth \<le> cc - \<bar>tc\<bar>"
          proof -
            have dec: "real (conn_cong_max_step_depth + trans_step_depth + refl_step_depth + 1)
                       = real conn_cong_max_step_depth + real trans_step_depth
                         + real refl_step_depth + 1" by simp
            have nn1: "(0::real) \<le> real conn_cong_max_step_depth" by simp
            have nn2: "(0::real) \<le> real trans_step_depth" by simp
            show ?thesis unfolding cc_def dec
              using tcm1 abs_ge_zero[of c62] abs_ge_zero[of tc] nn1 nn2 by linarith
          qed
          have tc_le_cc: "\<bar>tc\<bar> \<le> cc"
          proof -
            have "0 \<le> real refl_step_depth" by simp
            thus ?thesis using rsd_le by linarith
          qed
          have rsdb: "real refl_step_depth \<le> (cc - \<bar>tc\<bar>) * log 2 (real MM + 1)"
          proof -
            have "real refl_step_depth = real refl_step_depth * 1" by simp
            also have "\<dots> \<le> (cc - \<bar>tc\<bar>) * log 2 (real MM + 1)"
            proof (rule mult_mono)
              show "real refl_step_depth \<le> cc - \<bar>tc\<bar>" by (rule rsd_le)
              show "(1::real) \<le> log 2 (real MM + 1)" by (rule logge)
              show "(0::real) \<le> cc - \<bar>tc\<bar>" using tc_le_cc by simp
              show "(0::real) \<le> 1" by simp
            qed
            finally show ?thesis .
          qed
          have distrib: "(cc - \<bar>tc\<bar>) * log 2 (real MM + 1) + \<bar>tc\<bar> * log 2 (real MM + 1)
                         = cc * log 2 (real MM + 1)" by (simp add: algebra_simps)
          have "real (refl_step_depth + depth_formula (spira_trans (sub a)))
                = real refl_step_depth + real (depth_formula (spira_trans (sub a)))" by simp
          also have "\<dots> \<le> (cc - \<bar>tc\<bar>) * log 2 (real MM + 1) + \<bar>tc\<bar> * log 2 (real MM + 1)"
            using rsdb dts by linarith
          also have "\<dots> = cc * log 2 (real MM + 1)" using distrib .
          finally show ?thesis by simp
        qed
        show "\<exists>lines sz dep.
                provable_balanced_iff (spira_trans (sub_formula sub (Atom a)))
                  (sub_formula (\<lambda>v. spira_trans (sub v)) (Atom a)) lines sz dep
              \<and> lines \<le> len_formula (sub_formula sub (Atom a))
                  * poly PP (len_formula (Atom a)
                             + (\<Sum>v\<in>var_set_form (Atom a). len_formula (sub v)))
              \<and> sz \<le> len_formula (sub_formula sub (Atom a))
                  * poly PP (len_formula (Atom a)
                             + (\<Sum>v\<in>var_set_form (Atom a). len_formula (sub v)))
              \<and> real dep \<le> real (depth_formula (Atom a))
                  + cc * log 2 (real (len_formula (Atom a)
                                  + (\<Sum>v\<in>var_set_form (Atom a). len_formula (sub v))) + 1)"
        proof (rule exI[of _ refl_lines],
               rule exI[of _ "refl_step_len * len_formula (spira_trans (sub a))"],
               rule exI[of _ "refl_step_depth + depth_formula (spira_trans (sub a))"], intro conjI)
          show "provable_balanced_iff (spira_trans (sub_formula sub (Atom a)))
                  (sub_formula (\<lambda>v. spira_trans (sub v)) (Atom a))
                  refl_lines (refl_step_len * len_formula (spira_trans (sub a)))
                  (refl_step_depth + depth_formula (spira_trans (sub a)))"
            using refl unfolding SS SS' by simp
          show "refl_lines \<le> len_formula (sub_formula sub (Atom a))
                  * poly PP (len_formula (Atom a)
                             + (\<Sum>v\<in>var_set_form (Atom a). len_formula (sub v)))"
            using b1 unfolding SS MM_def by simp
          show "refl_step_len * len_formula (spira_trans (sub a))
                \<le> len_formula (sub_formula sub (Atom a))
                  * poly PP (len_formula (Atom a)
                             + (\<Sum>v\<in>var_set_form (Atom a). len_formula (sub v)))"
            using b2 unfolding SS MM_def by simp
          show "real (refl_step_depth + depth_formula (spira_trans (sub a)))
                \<le> real (depth_formula (Atom a))
                  + cc * log 2 (real (len_formula (Atom a)
                                  + (\<Sum>v\<in>var_set_form (Atom a). len_formula (sub v))) + 1)"
            using b3 unfolding MM_def by simp
        qed
      qed
    next
      case (Conn cc0 fs)
      show ?case
      proof (intro impI)
        assume wfC: "formula_well_formed (alphabet F) (Conn cc0 fs)"
        assume wfs: "\<forall>v. formula_well_formed (alphabet F) (sub v)"
        have arEq: "length fs = arity (alphabet F) cc0" using wfC by simp
        have wfsi: "\<And>x. x \<in> set fs \<Longrightarrow> formula_well_formed (alphabet F) x" using wfC by simp
        have wfsv: "\<And>v. formula_well_formed (alphabet F) (sub v)" using wfs by simp
        define MF where "MF = len_formula (Conn cc0 fs)
                              + (\<Sum>v\<in>var_set_form (Conn cc0 fs). len_formula (sub v))"
        let ?As = "map (\<lambda>x. spira_trans (sub_formula sub x)) fs"
        let ?Bs = "map (sub_formula (\<lambda>v. spira_trans (sub v))) fs"
        let ?MID = "Conn cc0 ?As"
        let ?BB = "Conn cc0 ?Bs"
        let ?A0 = "spira_trans (Conn cc0 (map (sub_formula sub) fs))"
        let ?LS = "len_formula (sub_formula sub (Conn cc0 fs))"
        let ?SUML = "sum_list (map (\<lambda>x. len_formula (sub_formula sub x)) fs)"
        let ?lf = "\<lambda>i. len_formula (sub_formula sub (fs ! i)) * poly PP MF"
        let ?Sc = "?SUML * poly PP MF"
        let ?Dc = "nat \<lfloor>real (depth_formula (Conn cc0 fs)) + cc * log 2 (real MF + 1)\<rfloor>"
        have ccnn: "0 \<le> cc" unfolding cc_def
          using tcm1 abs_ge_zero[of c62] abs_ge_zero[of tc] by simp
        have sumlmem: "\<And>x. x \<in> set fs \<Longrightarrow> len_formula (sub_formula sub x) \<le> ?SUML"
          by (auto intro: member_le_sum_list)
        \<comment> \<open>well-formedness of the substituted arguments\<close>
        have wfps: "\<forall>p\<in>set (map (sub_formula sub) fs). formula_well_formed (alphabet F) p"
        proof
          fix p assume "p \<in> set (map (sub_formula sub) fs)"
          then obtain x where x: "x \<in> set fs" "p = sub_formula sub x" by auto
          show "formula_well_formed (alphabet F) p"
            unfolding x(2) by (rule sub_formula_wf[OF wfsi[OF x(1)] wfsv])
        qed
        have lenps: "length (map (sub_formula sub) fs) = arity (alphabet F) cc0"
          using arEq by simp
        \<comment> \<open>pA: Lemma 6.2 pushes the transform through @{term cc0}\<close>
        obtain lA sA dA where pA:
            "provable_balanced_iff ?A0 ?MID lA sA dA"
            "lA \<le> poly bnd62 ?LS" "sA \<le> poly bnd62 ?LS"
            "real dA \<le> c62 * log 2 (real ?LS + 1)"
        proof -
          obtain lines sz dep where
              e1: "provable_balanced_iff (spira_trans (Conn cc0 (map (sub_formula sub) fs)))
                     (Conn cc0 (map spira_trans (map (sub_formula sub) fs))) lines sz dep"
            and e2: "lines \<le> poly bnd62 (len_formula (Conn cc0 (map (sub_formula sub) fs)))"
            and e3: "sz \<le> poly bnd62 (len_formula (Conn cc0 (map (sub_formula sub) fs)))"
            and e4: "real dep
                     \<le> c62 * log 2 (real (len_formula (Conn cc0 (map (sub_formula sub) fs))) + 1)"
            using tcc wfps lenps by blast
          have m1: "Conn cc0 (map spira_trans (map (sub_formula sub) fs)) = ?MID" by simp
          have m2: "len_formula (Conn cc0 (map (sub_formula sub) fs)) = ?LS" by simp
          show ?thesis
            by (rule that[of lines sz dep])
               (use e1 e2 e3 e4 in \<open>simp_all only: m1 m2\<close>)
        qed
        \<comment> \<open>prem: each argument commutes (induction hypothesis); bounds deferred\<close>
        have prem: "\<And>i. i < length ?As \<Longrightarrow>
            \<exists>l s d. provable_balanced_iff (?As ! i) (?Bs ! i) l s d
                     \<and> l \<le> ?lf i \<and> s \<le> ?Sc \<and> d \<le> ?Dc"
        proof -
          fix i assume "i < length ?As"
          hence iL: "i < length fs" by simp
          have mem: "fs ! i \<in> set fs" using iL by simp
          let ?Mi = "len_formula (fs ! i) + (\<Sum>v\<in>var_set_form (fs ! i). len_formula (sub v))"
          obtain l s d where
              ih1: "provable_balanced_iff (spira_trans (sub_formula sub (fs ! i)))
                       (sub_formula (\<lambda>v. spira_trans (sub v)) (fs ! i)) l s d"
            and ih2: "l \<le> len_formula (sub_formula sub (fs ! i)) * poly PP ?Mi"
            and ih3: "s \<le> len_formula (sub_formula sub (fs ! i)) * poly PP ?Mi"
            and ih4: "real d \<le> real (depth_formula (fs ! i)) + cc * log 2 (real ?Mi + 1)"
            using Conn.IH[OF mem] wfsi[OF mem] wfs by blast
          \<comment> \<open>@{term ?Mi} \<le> @{term MF}\<close>
          have lenmem: "len_formula (fs ! i) \<in> set (map len_formula fs)" using mem by simp
          have lenle: "len_formula (fs ! i) \<le> len_formula (Conn cc0 fs)"
          proof -
            have "len_formula (fs ! i) \<le> sum_list (map len_formula fs)"
              using lenmem by (auto intro: member_le_sum_list)
            thus ?thesis by simp
          qed
          have varsub: "var_set_form (fs ! i) \<subseteq> var_set_form (Conn cc0 fs)"
            using mem by auto
          have sumle: "(\<Sum>v\<in>var_set_form (fs ! i). len_formula (sub v))
                       \<le> (\<Sum>v\<in>var_set_form (Conn cc0 fs). len_formula (sub v))"
            by (rule sum_mono2[OF var_set_form_finite varsub]) simp
          have MiMF: "?Mi \<le> MF" unfolding MF_def using lenle sumle by simp
          have ppMi: "poly PP ?Mi \<le> poly PP MF" using MiMF by (rule poly_nat_mono)
          have lenSUML: "len_formula (sub_formula sub (fs ! i)) \<le> ?SUML"
            by (rule sumlmem[OF mem])
          \<comment> \<open>depth of @{term "fs ! i"} \<le> depth of the whole formula\<close>
          have dconn: "depth_formula (Conn cc0 fs) = 1 + Max (set (map depth_formula fs))"
          proof -
            have "0 < length fs" using iL by linarith
            thus ?thesis by simp
          qed
          have depthle: "depth_formula (fs ! i) \<le> depth_formula (Conn cc0 fs)"
          proof -
            have "depth_formula (fs ! i) \<in> set (map depth_formula fs)" using mem by simp
            hence "depth_formula (fs ! i) \<le> Max (set (map depth_formula fs))"
              by simp
            thus ?thesis using dconn by simp
          qed
          \<comment> \<open>convert the bounds\<close>
          have c1: "l \<le> ?lf i"
          proof -
            have "l \<le> len_formula (sub_formula sub (fs ! i)) * poly PP ?Mi" by (rule ih2)
            also have "\<dots> \<le> len_formula (sub_formula sub (fs ! i)) * poly PP MF"
              using ppMi by (rule mult_le_mono2)
            finally show ?thesis .
          qed
          have c2: "s \<le> ?Sc"
          proof -
            have "s \<le> len_formula (sub_formula sub (fs ! i)) * poly PP ?Mi" by (rule ih3)
            also have "\<dots> \<le> ?SUML * poly PP MF" by (rule mult_le_mono[OF lenSUML ppMi])
            finally show ?thesis .
          qed
          have argReal: "real ?Mi + 1 \<le> real MF + 1"
          proof -
            have "real ?Mi \<le> real MF" by (rule of_nat_mono[OF MiMF])
            thus ?thesis by simp
          qed
          have logle: "log 2 (real ?Mi + 1) \<le> log 2 (real MF + 1)"
          proof (rule log_le_cancel_iff[THEN iffD2])
            show "(1::real) < 2" by simp
            show "0 < real ?Mi + 1" by (simp del: of_nat_add)
            show "0 < real MF + 1" by simp
            show "real ?Mi + 1 \<le> real MF + 1" by (rule argReal)
          qed
          have c3: "d \<le> ?Dc"
          proof (rule nat_le_floor)
            have step: "real d \<le> real (depth_formula (fs ! i)) + cc * log 2 (real ?Mi + 1)"
              by (rule ih4)
            have cle: "cc * log 2 (real ?Mi + 1) \<le> cc * log 2 (real MF + 1)"
              using logle ccnn by (rule mult_left_mono)
            have dle: "real (depth_formula (fs ! i)) \<le> real (depth_formula (Conn cc0 fs))"
              using depthle by simp
            from step cle dle
            show "real d \<le> real (depth_formula (Conn cc0 fs)) + cc * log 2 (real MF + 1)"
              by linarith
          qed
          have nthAs: "?As ! i = spira_trans (sub_formula sub (fs ! i))" using iL by simp
          have nthBs: "?Bs ! i = sub_formula (\<lambda>v. spira_trans (sub v)) (fs ! i)" using iL by simp
          show "\<exists>l s d. provable_balanced_iff (?As ! i) (?Bs ! i) l s d
                         \<and> l \<le> ?lf i \<and> s \<le> ?Sc \<and> d \<le> ?Dc"
            using ih1 c1 c2 c3 unfolding nthAs nthBs by blast
        qed
        have leneq: "length ?Bs = length ?As" by simp
        have areq: "length ?As = arity (alphabet F) cc0" using arEq by simp
        have sv_wf: "\<And>v. formula_well_formed (alphabet F) (spira_trans (sub v))"
          using spira_trans_wf[OF wfsv] .
        have wfAs': "\<And>a. a \<in> set ?As \<Longrightarrow> formula_well_formed (alphabet F) a"
        proof -
          fix a assume "a \<in> set ?As"
          then obtain x where x: "x \<in> set fs"
            and aeq: "a = spira_trans (sub_formula sub x)" by auto
          have "formula_well_formed (alphabet F) (sub_formula sub x)"
            by (rule sub_formula_well_formed[OF wfsi[OF x] wfsv])
          thus "formula_well_formed (alphabet F) a"
            unfolding aeq by (rule spira_trans_wf)
        qed
        have wfBs': "\<And>b. b \<in> set ?Bs \<Longrightarrow> formula_well_formed (alphabet F) b"
        proof -
          fix b assume "b \<in> set ?Bs"
          then obtain x where x: "x \<in> set fs"
            and beq: "b = sub_formula (\<lambda>v. spira_trans (sub v)) x" by auto
          show "formula_well_formed (alphabet F) b"
            unfolding beq by (rule sub_formula_well_formed[OF wfsi[OF x] sv_wf])
        qed
        \<comment> \<open>pB: congruence over @{term cc0} from the argument commutations\<close>
        obtain lB sB dB where
            pBpbi: "provable_balanced_iff ?MID ?BB lB sB dB"
          and pBl: "lB \<le> sum_list (map ?lf [0..< length ?As]) + conn_cong_max_lines"
          and pBs: "sB \<le> ?Sc + conn_cong_max_step_len
                          * (2 * length ?As * (len_formula ?MID + len_formula ?BB) + 1)"
          and pBd: "dB \<le> max ?Dc (conn_cong_max_step_depth
                          + max (depth_formula ?MID) (depth_formula ?BB))"
          using conn_cong[OF leneq areq wfAs' wfBs' prem] by blast
        \<comment> \<open>pC: transitivity glues pA and pB\<close>
        have wf_A0: "formula_well_formed (alphabet F) ?A0"
        proof (rule spira_trans_wf)
          show "formula_well_formed (alphabet F) (Conn cc0 (map (sub_formula sub) fs))"
            using wfps lenps by auto
        qed
        have wf_MID: "formula_well_formed (alphabet F) ?MID"
          using wfAs' areq by auto
        have wf_BB: "formula_well_formed (alphabet F) ?BB"
          using wfBs' leneq areq by auto
        note pC = iff_trans[OF pA(1) pBpbi wf_A0 wf_MID wf_BB]
        \<comment> \<open>shared measure facts\<close>
        have lenLS: "?LS = 1 + ?SUML" by (simp add: o_def)
        have MFgeC: "len_formula (Conn cc0 fs) \<le> MF" by (simp add: MF_def)
        have LSsq: "?LS \<le> MF * MF"
        proof -
          have a: "?LS \<le> len_formula (Conn cc0 fs) * MF"
            using len_sub_form_le[of sub "Conn cc0 fs"] by (simp add: MF_def)
          from a mult_le_mono1[OF MFgeC] show ?thesis by (rule le_trans)
        qed
        have sumlf: "sum_list (map ?lf [0..< length ?As]) = ?SUML * poly PP MF"
        proof -
          have mapeq: "map ?lf [0..< length ?As]
                = map (\<lambda>x. len_formula (sub_formula sub x) * poly PP MF) fs"
          proof (rule nth_equalityI)
            show "length (map ?lf [0..< length ?As])
                  = length (map (\<lambda>x. len_formula (sub_formula sub x) * poly PP MF) fs)" by simp
            fix i assume "i < length (map ?lf [0..< length ?As])"
            hence "i < length fs" by simp
            thus "map ?lf [0..< length ?As] ! i
                  = map (\<lambda>x. len_formula (sub_formula sub x) * poly PP MF) fs ! i" by simp
          qed
          show ?thesis unfolding mapeq by (simp add: sum_list_mult_const)
        qed
        \<comment> \<open>final envelope bounds\<close>
        have B1: "lA + lB + trans_lines \<le> ?LS * poly PP MF"
        proof -
          have cml: "conn_cong_max_lines + trans_lines \<le> BIGC" using bigS by linarith
          have "lA + lB + trans_lines
                \<le> poly bnd62 ?LS + (?SUML * poly PP MF + conn_cong_max_lines) + trans_lines"
            using pA(2) pBl unfolding sumlf by linarith
          also have "\<dots> = ?SUML * poly PP MF
                           + (poly bnd62 ?LS + (conn_cong_max_lines + trans_lines))" by simp
          also have "\<dots> \<le> ?SUML * poly PP MF + poly PP MF"
            using ppL[OF LSsq cml] by linarith
          also have "\<dots> = (1 + ?SUML) * poly PP MF" by (simp add: algebra_simps)
          also have "\<dots> = ?LS * poly PP MF" using lenLS by simp
          finally show ?thesis .
        qed
        \<comment> \<open>length bounds for the size estimate\<close>
        have fsF: "frege_system F" by (meson frege_balancing_axioms frege_balancing_def)
        have finUNIV: "finite (UNIV :: 'a set)"
          using frege_system.finite_alphabet[OF fsF] by simp
        have arMA: "arity (alphabet F) cc0 \<le> MA"
          unfolding MA_def by (rule Max_ge[OF finite_imageI[OF finUNIV]]) simp
        have fsMA: "length fs \<le> MA" using arEq arMA by simp
        have wfL: "formula_well_formed (alphabet F) (Conn cc0 (map (sub_formula sub) fs))"
          using sub_formula_wf[OF wfC wfsv] by simp
        have rebalge1: "1 \<le> poly rebal_tb MF"
        proof -
          have wfa: "formula_well_formed (alphabet F) (Atom undefined)" by simp
          have la: "len_formula (Atom undefined) \<le> MF" by (simp add: MF_def)
          have "len_formula (spira_trans (Atom undefined)) \<le> poly rebal_tb MF"
            by (rule spira_trans_len_le_tb[OF wfa la])
          thus ?thesis using len_formula_ge_1[of "spira_trans (Atom undefined)"] by linarith
        qed
        have lenA0: "len_formula ?A0 \<le> poly rebal_tb (MF * MF)"
        proof -
          have "len_formula ?A0
                \<le> poly rebal_tb (len_formula (Conn cc0 (map (sub_formula sub) fs)))"
            by (rule spira_trans_len_le_tb[OF wfL order_refl])
          also have "\<dots> \<le> poly rebal_tb (MF * MF)"
          proof (rule poly_nat_mono)
            show "len_formula (Conn cc0 (map (sub_formula sub) fs)) \<le> MF * MF" using LSsq by simp
          qed
          finally show ?thesis .
        qed
        have childlen: "\<And>x. x \<in> set fs \<Longrightarrow> len_formula (sub_formula sub x) \<le> MF * MF"
        proof -
          fix x assume xs: "x \<in> set fs"
          have "len_formula (sub_formula sub x) \<le> ?SUML" by (rule sumlmem[OF xs])
          also have "?SUML \<le> MF * MF" using LSsq lenLS by simp
          finally show "len_formula (sub_formula sub x) \<le> MF * MF" .
        qed
        have childtrans: "\<And>x. x \<in> set fs
              \<Longrightarrow> len_formula (spira_trans (sub_formula sub x)) \<le> poly rebal_tb (MF * MF)"
        proof -
          fix x assume xs: "x \<in> set fs"
          have wfx: "formula_well_formed (alphabet F) (sub_formula sub x)"
            by (rule sub_formula_wf[OF wfsi[OF xs] wfsv])
          show "len_formula (spira_trans (sub_formula sub x)) \<le> poly rebal_tb (MF * MF)"
            by (rule spira_trans_len_le_tb[OF wfx childlen[OF xs]])
        qed
        have lenMID: "len_formula ?MID \<le> 1 + MA * poly rebal_tb (MF * MF)"
        proof -
          have "sum_list (map len_formula ?As)
                = sum_list (map (\<lambda>x. len_formula (spira_trans (sub_formula sub x))) fs)"
            by (simp add: o_def)
          also have "\<dots> \<le> sum_list (map (\<lambda>_. poly rebal_tb (MF * MF)) fs)"
            by (rule sum_list_mono) (simp add: childtrans)
          also have "\<dots> = length fs * poly rebal_tb (MF * MF)" by (simp add: sum_list_triv)
          also have "\<dots> \<le> MA * poly rebal_tb (MF * MF)" using fsMA by (rule mult_le_mono1)
          finally have "sum_list (map len_formula ?As) \<le> MA * poly rebal_tb (MF * MF)" .
          thus ?thesis by simp
        qed
        have lenBB: "len_formula ?BB \<le> MF * poly rebal_tb MF"
        proof -
          have capv: "\<And>v. v \<in> var_set_form (Conn cc0 fs)
                \<Longrightarrow> len_formula (spira_trans (sub v)) \<le> poly rebal_tb MF"
          proof -
            fix v assume vin: "v \<in> var_set_form (Conn cc0 fs)"
            have lv: "len_formula (sub v) \<le> MF"
            proof -
              have "len_formula (sub v)
                    \<le> (\<Sum>w\<in>var_set_form (Conn cc0 fs). len_formula (sub w))"
                using occ_len_le[OF vin] .
              thus ?thesis by (simp add: MF_def)
            qed
            show "len_formula (spira_trans (sub v)) \<le> poly rebal_tb MF"
              by (rule spira_trans_len_le_tb[OF wfsv lv])
          qed
          have "len_formula (sub_formula (\<lambda>v. spira_trans (sub v)) (Conn cc0 fs))
                \<le> poly rebal_tb MF * len_formula (Conn cc0 fs)"
            by (rule len_strans_cap[OF capv rebalge1])
          also have "\<dots> \<le> poly rebal_tb MF * MF" using MFgeC by (rule mult_le_mono2)
          also have "\<dots> = MF * poly rebal_tb MF" by (simp add: mult.commute)
          finally show ?thesis by simp
        qed
        have B2: "sA + sB + trans_step_len * (len_formula ?A0 + len_formula ?MID + len_formula ?BB)
                  \<le> ?LS * poly PP MF"
        proof -
          define R2 where "R2 = poly rebal_tb (MF * MF)"
          define R1 where "R1 = MF * poly rebal_tb MF"
          have a: "len_formula ?A0 \<le> R2" using lenA0 unfolding R2_def by simp
          have m: "len_formula ?MID \<le> 1 + MA * R2" using lenMID unfolding R2_def by simp
          have b: "len_formula ?BB \<le> R1" using lenBB unfolding R1_def by simp
          have la2: "2 * length ?As \<le> 2 * MA" using fsMA by simp
          have ppMF: "poly PP MF = poly bnd62 (MF * MF) + BIGC * R2 + BIGC * R1 + BIGC"
            using ppval[of MF] unfolding R2_def R1_def by (simp add: power2_eq_square)
          \<comment> \<open>nonlinear building blocks over @{term "(MA+1)*(MA+1)"}\<close>
          have kSq: "MA * MA \<le> (MA + 1) * (MA + 1)" by (rule mult_le_mono) simp_all
          have kMA: "MA \<le> (MA + 1) * (MA + 1)"
            using mult_le_mono2[of 1 "MA + 1" "MA + 1"] by simp
          have kp1: "MA + 1 \<le> (MA + 1) * (MA + 1)"
            using mult_le_mono2[of 1 "MA + 1" "MA + 1"] by simp
          have k2: "2 * MA + 1 \<le> 2 * ((MA + 1) * (MA + 1))" using kp1 by simp
          have kp2: "MA + 1 \<le> 2 * ((MA + 1) * (MA + 1))" using kp1 by simp
          have kone: "(1::nat) \<le> 2 * ((MA + 1) * (MA + 1))" by simp
          have q2: "2 * MA * MA * conn_cong_max_step_len
                    \<le> 2 * conn_cong_max_step_len * ((MA + 1) * (MA + 1))"
            using mult_le_mono2[OF kSq, of "2 * conn_cong_max_step_len"] by (simp add: algebra_simps)
          have qMAc: "2 * MA * conn_cong_max_step_len
                      \<le> 2 * conn_cong_max_step_len * ((MA + 1) * (MA + 1))"
            using mult_le_mono2[OF kMA, of "2 * conn_cong_max_step_len"] by (simp add: algebra_simps)
          have qc0: "2 * MA * conn_cong_max_step_len + conn_cong_max_step_len
                     \<le> 2 * conn_cong_max_step_len * ((MA + 1) * (MA + 1))"
          proof -
            have "2 * MA * conn_cong_max_step_len + conn_cong_max_step_len
                  = conn_cong_max_step_len * (2 * MA + 1)" by (simp add: algebra_simps)
            also have "\<dots> \<le> conn_cong_max_step_len * (2 * ((MA + 1) * (MA + 1)))"
              using k2 by (rule mult_le_mono2)
            also have "\<dots> = 2 * conn_cong_max_step_len * ((MA + 1) * (MA + 1))"
              by (simp add: algebra_simps)
            finally show ?thesis .
          qed
          have qt: "trans_step_len + trans_step_len * MA
                    \<le> 2 * trans_step_len * ((MA + 1) * (MA + 1))"
          proof -
            have "trans_step_len + trans_step_len * MA = trans_step_len * (MA + 1)"
              by (simp add: algebra_simps)
            also have "\<dots> \<le> trans_step_len * (2 * ((MA + 1) * (MA + 1)))"
              by (rule mult_le_mono2[OF kp2])
            also have "\<dots> = 2 * trans_step_len * ((MA + 1) * (MA + 1))" by (simp add: algebra_simps)
            finally show ?thesis .
          qed
          have qt1: "trans_step_len \<le> 2 * trans_step_len * ((MA + 1) * (MA + 1))"
          proof -
            have "trans_step_len = trans_step_len * 1" by simp
            also have "\<dots> \<le> trans_step_len * (2 * ((MA + 1) * (MA + 1)))"
              by (rule mult_le_mono2[OF kone])
            also have "\<dots> = 2 * trans_step_len * ((MA + 1) * (MA + 1))" by (simp add: algebra_simps)
            finally show ?thesis .
          qed
          have domUB: "2 * conn_cong_max_step_len * ((MA + 1) * (MA + 1))
                       + 2 * trans_step_len * ((MA + 1) * (MA + 1)) \<le> BIGC"
          proof -
            have "2 * conn_cong_max_step_len * ((MA + 1) * (MA + 1))
                  + 2 * trans_step_len * ((MA + 1) * (MA + 1))
                  = 2 * (conn_cong_max_step_len + trans_step_len) * ((MA + 1) * (MA + 1))"
              by (simp add: algebra_simps)
            also have "\<dots> \<le> 2 * (conn_cong_max_step_len + conn_cong_max_lines + trans_step_len
                                + trans_lines + refl_step_len + refl_lines + 1)
                              * ((MA + 1) * (MA + 1))"
              by (rule mult_le_mono1) simp
            also have "\<dots> = BIGC" unfolding BIGC_def by (simp add: algebra_simps)
            finally show ?thesis .
          qed
          \<comment> \<open>the three coefficient dominances\<close>
          have dR2: "2 * MA * MA * conn_cong_max_step_len + trans_step_len + trans_step_len * MA \<le> BIGC"
            using q2 qt domUB by linarith
          have dR1: "2 * MA * conn_cong_max_step_len + trans_step_len \<le> BIGC"
            using qMAc qt1 domUB by linarith
          have dconst: "2 * MA * conn_cong_max_step_len + conn_cong_max_step_len + trans_step_len \<le> BIGC"
            using qc0 qt1 domUB by linarith
          \<comment> \<open>bound the per-level size overhead by @{term "poly PP MF"}\<close>
          have P1: "2 * length ?As * (len_formula ?MID + len_formula ?BB)
                    \<le> 2 * MA * (1 + MA * R2 + R1)"
          proof -
            have "2 * length ?As * (len_formula ?MID + len_formula ?BB)
                  \<le> 2 * MA * (len_formula ?MID + len_formula ?BB)"
              by (rule mult_le_mono1[OF la2])
            also have "\<dots> \<le> 2 * MA * (1 + MA * R2 + R1)"
              by (rule mult_le_mono2) (use m b in linarith)
            finally show ?thesis .
          qed
          have step1: "conn_cong_max_step_len
                         * (2 * length ?As * (len_formula ?MID + len_formula ?BB) + 1)
                       + trans_step_len * (len_formula ?A0 + len_formula ?MID + len_formula ?BB)
                       \<le> conn_cong_max_step_len * (2 * MA * (1 + MA * R2 + R1) + 1)
                         + trans_step_len * (R2 + (1 + MA * R2) + R1)"
          proof -
            have t1: "conn_cong_max_step_len
                        * (2 * length ?As * (len_formula ?MID + len_formula ?BB) + 1)
                      \<le> conn_cong_max_step_len * (2 * MA * (1 + MA * R2 + R1) + 1)"
              by (rule mult_le_mono2) (use P1 in linarith)
            have t2: "trans_step_len * (len_formula ?A0 + len_formula ?MID + len_formula ?BB)
                      \<le> trans_step_len * (R2 + (1 + MA * R2) + R1)"
              by (rule mult_le_mono2) (use a m b in linarith)
            from t1 t2 show ?thesis by linarith
          qed
          have ovEq: "conn_cong_max_step_len * (2 * MA * (1 + MA * R2 + R1) + 1)
                      + trans_step_len * (R2 + (1 + MA * R2) + R1)
                      = (2 * MA * MA * conn_cong_max_step_len + trans_step_len + trans_step_len * MA) * R2
                        + (2 * MA * conn_cong_max_step_len + trans_step_len) * R1
                        + (2 * MA * conn_cong_max_step_len + conn_cong_max_step_len + trans_step_len)"
            by (simp add: algebra_simps)
          have ovBIGC: "(2 * MA * MA * conn_cong_max_step_len + trans_step_len + trans_step_len * MA) * R2
                        + (2 * MA * conn_cong_max_step_len + trans_step_len) * R1
                        + (2 * MA * conn_cong_max_step_len + conn_cong_max_step_len + trans_step_len)
                        \<le> BIGC * R2 + BIGC * R1 + BIGC"
            using mult_le_mono1[OF dR2, of R2] mult_le_mono1[OF dR1, of R1] dconst by linarith
          have ovPP: "poly bnd62 ?LS
                       + (conn_cong_max_step_len
                            * (2 * length ?As * (len_formula ?MID + len_formula ?BB) + 1)
                          + trans_step_len * (len_formula ?A0 + len_formula ?MID + len_formula ?BB))
                      \<le> poly PP MF"
          proof -
            have "conn_cong_max_step_len
                    * (2 * length ?As * (len_formula ?MID + len_formula ?BB) + 1)
                  + trans_step_len * (len_formula ?A0 + len_formula ?MID + len_formula ?BB)
                  \<le> BIGC * R2 + BIGC * R1 + BIGC"
              using step1 ovEq ovBIGC by linarith
            moreover have "poly bnd62 ?LS \<le> poly bnd62 (MF * MF)"
              using LSsq by (rule poly_nat_mono)
            ultimately show ?thesis using ppMF by linarith
          qed
          \<comment> \<open>assemble\<close>
          have ScVal: "?Sc = ?SUML * poly PP MF" by simp
          have "sA + sB + trans_step_len * (len_formula ?A0 + len_formula ?MID + len_formula ?BB)
                \<le> poly bnd62 ?LS
                  + (?SUML * poly PP MF
                     + conn_cong_max_step_len
                         * (2 * length ?As * (len_formula ?MID + len_formula ?BB) + 1))
                  + trans_step_len * (len_formula ?A0 + len_formula ?MID + len_formula ?BB)"
            using pA(3) pBs ScVal by linarith
          also have "\<dots> = ?SUML * poly PP MF
                           + (poly bnd62 ?LS
                              + (conn_cong_max_step_len
                                   * (2 * length ?As * (len_formula ?MID + len_formula ?BB) + 1)
                                 + trans_step_len
                                     * (len_formula ?A0 + len_formula ?MID + len_formula ?BB)))"
            by (simp add: algebra_simps)
          also have "\<dots> \<le> ?SUML * poly PP MF + poly PP MF" using ovPP by linarith
          also have "\<dots> = (1 + ?SUML) * poly PP MF" by (simp add: algebra_simps)
          also have "\<dots> = ?LS * poly PP MF" using lenLS by simp
          finally show ?thesis .
        qed
        have B3: "real (max dA (max dB (trans_step_depth
                       + max (depth_formula ?A0) (max (depth_formula ?MID) (depth_formula ?BB)))))
                  \<le> real (depth_formula (Conn cc0 fs)) + cc * log 2 (real MF + 1)"
        proof -
          have MFge1: "1 \<le> MF" by (simp add: MF_def)
          have lgn1: "1 \<le> log 2 (real MF + 1)" using MFge1 by (simp add: le_log_iff)
          have lgn0: "0 \<le> log 2 (real MF + 1)" using lgn1 by simp
          have logmono2: "\<And>x y. 0 < x \<Longrightarrow> x \<le> y \<Longrightarrow> log 2 x \<le> log 2 y"
          proof -
            fix x y :: real assume xy: "0 < x" "x \<le> y"
            have "0 < y" using xy by simp
            thus "log 2 x \<le> log 2 y" using xy by simp
          qed
          have logge0: "\<And>N::nat. 0 \<le> log 2 (real N + 1)"
          proof -
            fix N :: nat
            have "(1::real) \<le> real N + 1" by simp
            thus "0 \<le> log 2 (real N + 1)" by (simp add: le_log_iff)
          qed
          have lsLGN: "log 2 (real ?LS + 1) \<le> 2 * log 2 (real MF + 1)"
          proof -
            have lsq: "real ?LS \<le> real MF * real MF"
            proof -
              have "real ?LS \<le> real (MF * MF)" using LSsq by (rule of_nat_mono)
              thus ?thesis by (simp only: of_nat_mult)
            qed
            have exp: "(real MF + 1) * (real MF + 1) = real MF * real MF + 2 * real MF + 1"
              by (simp add: algebra_simps)
            have leq: "real ?LS + 1 \<le> (real MF + 1) * (real MF + 1)"
              using lsq exp by simp
            have "log 2 (real ?LS + 1) \<le> log 2 ((real MF + 1) * (real MF + 1))"
              by (rule logmono2[OF _ leq]) simp
            also have "\<dots> = log 2 (real MF + 1) + log 2 (real MF + 1)"
              by (rule log_mult_pos) simp_all
            also have "\<dots> = 2 * log 2 (real MF + 1)" by simp
            finally show ?thesis .
          qed
          \<comment> \<open>shared "scale a real coefficient by the log envelope" step\<close>
          have absLog: "\<And>(K::real) N. real N \<le> real ?LS
                \<Longrightarrow> K * log 2 (real N + 1) \<le> \<bar>K\<bar> * (2 * log 2 (real MF + 1))"
          proof -
            fix K :: real and N :: nat assume Nle: "real N \<le> real ?LS"
            have "K * log 2 (real N + 1) \<le> \<bar>K\<bar> * log 2 (real N + 1)"
              by (rule mult_right_mono[OF abs_ge_self logge0])
            also have "\<dots> \<le> \<bar>K\<bar> * (2 * log 2 (real MF + 1))"
            proof (rule mult_left_mono)
              have "log 2 (real N + 1) \<le> log 2 (real ?LS + 1)"
                by (rule logmono2) (use Nle in simp)+
              thus "log 2 (real N + 1) \<le> 2 * log 2 (real MF + 1)" using lsLGN by linarith
              show "0 \<le> \<bar>K\<bar>" by simp
            qed
            finally show "K * log 2 (real N + 1) \<le> \<bar>K\<bar> * (2 * log 2 (real MF + 1))" .
          qed
          \<comment> \<open>per-node depth bounds (all O(log M) except @{term ?BB} which carries +depth)\<close>
          have dA_b: "real dA \<le> \<bar>c62\<bar> * (2 * log 2 (real MF + 1))"
          proof -
            have "real dA \<le> c62 * log 2 (real ?LS + 1)" by (rule pA(4))
            also have "\<dots> \<le> \<bar>c62\<bar> * (2 * log 2 (real MF + 1))" by (rule absLog) simp
            finally show ?thesis .
          qed
          have A0_b: "real (depth_formula ?A0) \<le> \<bar>tc\<bar> * (2 * log 2 (real MF + 1))"
          proof -
            have "real (depth_formula ?A0)
                  \<le> tc * log 2 (real (len_formula (Conn cc0 (map (sub_formula sub) fs))) + 1)"
              using tc wfL by blast
            also have "\<dots> = tc * log 2 (real ?LS + 1)" by (simp only: sub_formula.simps)
            also have "\<dots> \<le> \<bar>tc\<bar> * (2 * log 2 (real MF + 1))" by (rule absLog) simp
            finally show ?thesis .
          qed
          have MID_b: "real (depth_formula ?MID) \<le> 1 + \<bar>tc\<bar> * (2 * log 2 (real MF + 1))"
          proof (cases "fs = []")
            case True thus ?thesis by simp
          next
            case False
            have dM: "depth_formula ?MID = 1 + Max (set (map depth_formula ?As))"
              using False by simp
            have ch: "\<And>d. d \<in> set (map depth_formula ?As)
                      \<Longrightarrow> real d \<le> \<bar>tc\<bar> * (2 * log 2 (real MF + 1))"
            proof -
              fix d assume "d \<in> set (map depth_formula ?As)"
              then obtain x where x: "x \<in> set fs"
                  "d = depth_formula (spira_trans (sub_formula sub x))" by auto
              have wfx: "formula_well_formed (alphabet F) (sub_formula sub x)"
                by (rule sub_formula_wf[OF wfsi[OF x(1)] wfsv])
              have lxLS: "len_formula (sub_formula sub x) \<le> ?LS"
              proof -
                have "len_formula (sub_formula sub x) \<le> ?SUML" by (rule sumlmem[OF x(1)])
                thus ?thesis using lenLS by simp
              qed
              have "real d \<le> tc * log 2 (real (len_formula (sub_formula sub x)) + 1)"
                unfolding x(2) using tc wfx by blast
              also have "\<dots> \<le> \<bar>tc\<bar> * (2 * log 2 (real MF + 1))"
                by (rule absLog[OF of_nat_mono[OF lxLS]])
              finally show "real d \<le> \<bar>tc\<bar> * (2 * log 2 (real MF + 1))" .
            qed
            have "Max (set (map depth_formula ?As)) \<in> set (map depth_formula ?As)"
              using False by simp
            hence "real (Max (set (map depth_formula ?As)))
                   \<le> \<bar>tc\<bar> * (2 * log 2 (real MF + 1))" using ch by blast
            thus ?thesis using dM by simp
          qed
          have BB_b: "real (depth_formula ?BB)
                      \<le> real (depth_formula (Conn cc0 fs)) + tcm * log 2 (real MF + 1)"
          proof -
            have eqBB: "?BB = sub_formula (\<lambda>v. spira_trans (sub v)) (Conn cc0 fs)"
              by (simp only: sub_formula.simps)
            have "real (depth_formula ?BB)
                  \<le> real (depth_formula (Conn cc0 fs))
                    + tcm * log 2 (real (len_formula (Conn cc0 fs)
                          + (\<Sum>w\<in>var_set_form (Conn cc0 fs). len_formula (sub w))) + 1)"
              unfolding eqBB using dstr wfs by blast
            also have "\<dots> = real (depth_formula (Conn cc0 fs)) + tcm * log 2 (real MF + 1)"
              by (simp only: MF_def[symmetric])
            finally show ?thesis .
          qed
          have Dc_b: "real ?Dc \<le> real (depth_formula (Conn cc0 fs)) + cc * log 2 (real MF + 1)"
          proof -
            have nn: "0 \<le> real (depth_formula (Conn cc0 fs)) + cc * log 2 (real MF + 1)"
              using lgn0 ccnn by simp
            thus ?thesis by linarith
          qed
          \<comment> \<open>combine the depth max-tree against the target\<close>
          have dcnn: "0 \<le> real (depth_formula (Conn cc0 fs))" by simp
          have nnc: "(0::real) \<le> real conn_cong_max_step_depth"
                    "(0::real) \<le> real trans_step_depth" by simp_all
          have dec: "cc = real conn_cong_max_step_depth + real trans_step_depth
                          + real refl_step_depth + 1 + 3 * \<bar>c62\<bar> + 4 * \<bar>tc\<bar> + 3 * tcm + 5"
            unfolding cc_def by simp
          have ccC: "2 * \<bar>c62\<bar> \<le> cc"
            using dec tcm1 abs_ge_zero[of c62] abs_ge_zero[of tc] nnc by linarith
          have ccT: "real trans_step_depth + 1 + 2 * \<bar>tc\<bar> + tcm \<le> cc"
            using dec tcm1 abs_ge_zero[of c62] abs_ge_zero[of tc] nnc by linarith
          have ccCm: "real conn_cong_max_step_depth + 1 + 2 * \<bar>tc\<bar> + tcm \<le> cc"
            using dec tcm1 abs_ge_zero[of c62] abs_ge_zero[of tc] nnc by linarith
          have ccLC: "2 * \<bar>c62\<bar> * log 2 (real MF + 1) \<le> cc * log 2 (real MF + 1)"
            by (rule mult_right_mono[OF ccC lgn0])
          have ccLT: "(real trans_step_depth + 1 + 2 * \<bar>tc\<bar> + tcm) * log 2 (real MF + 1)
                      \<le> cc * log 2 (real MF + 1)"
            by (rule mult_right_mono[OF ccT lgn0])
          have ccLCm: "(real conn_cong_max_step_depth + 1 + 2 * \<bar>tc\<bar> + tcm) * log 2 (real MF + 1)
                       \<le> cc * log 2 (real MF + 1)"
            by (rule mult_right_mono[OF ccCm lgn0])
          have dA2: "\<bar>tc\<bar> * (2 * log 2 (real MF + 1)) = 2 * \<bar>tc\<bar> * log 2 (real MF + 1)"
            by (simp add: algebra_simps)
          have dC2: "\<bar>c62\<bar> * (2 * log 2 (real MF + 1)) = 2 * \<bar>c62\<bar> * log 2 (real MF + 1)"
            by (simp add: algebra_simps)
          have dT: "(real trans_step_depth + 1 + 2 * \<bar>tc\<bar> + tcm) * log 2 (real MF + 1)
                    = real trans_step_depth * log 2 (real MF + 1) + log 2 (real MF + 1)
                      + 2 * \<bar>tc\<bar> * log 2 (real MF + 1) + tcm * log 2 (real MF + 1)"
            by (simp add: algebra_simps)
          have dCm: "(real conn_cong_max_step_depth + 1 + 2 * \<bar>tc\<bar> + tcm) * log 2 (real MF + 1)
                     = real conn_cong_max_step_depth * log 2 (real MF + 1) + log 2 (real MF + 1)
                       + 2 * \<bar>tc\<bar> * log 2 (real MF + 1) + tcm * log 2 (real MF + 1)"
            by (simp add: algebra_simps)
          have tsdL: "real trans_step_depth \<le> real trans_step_depth * log 2 (real MF + 1)"
            using mult_left_mono[of 1 "log 2 (real MF + 1)" "real trans_step_depth"] lgn1 by simp
          have cmL: "real conn_cong_max_step_depth
                     \<le> real conn_cong_max_step_depth * log 2 (real MF + 1)"
            using mult_left_mono[of 1 "log 2 (real MF + 1)" "real conn_cong_max_step_depth"] lgn1 by simp
          have tcmL0: "0 \<le> tcm * log 2 (real MF + 1)" using tcm1 lgn0 by simp
          have tcL0: "0 \<le> 2 * \<bar>tc\<bar> * log 2 (real MF + 1)" using lgn0 by simp
          have iA0: "real (depth_formula ?A0)
                     \<le> real (depth_formula (Conn cc0 fs))
                        + 2 * \<bar>tc\<bar> * log 2 (real MF + 1) + tcm * log 2 (real MF + 1) + 1"
            using A0_b dA2 tcmL0 dcnn by linarith
          have iMID: "real (depth_formula ?MID)
                      \<le> real (depth_formula (Conn cc0 fs))
                         + 2 * \<bar>tc\<bar> * log 2 (real MF + 1) + tcm * log 2 (real MF + 1) + 1"
            using MID_b dA2 tcmL0 dcnn by linarith
          have iBB: "real (depth_formula ?BB)
                     \<le> real (depth_formula (Conn cc0 fs))
                        + 2 * \<bar>tc\<bar> * log 2 (real MF + 1) + tcm * log 2 (real MF + 1) + 1"
            using BB_b tcL0 by linarith
          have L_trans: "real trans_step_depth
                         + max (real (depth_formula ?A0))
                               (max (real (depth_formula ?MID)) (real (depth_formula ?BB)))
                         \<le> real (depth_formula (Conn cc0 fs)) + cc * log 2 (real MF + 1)"
          proof -
            have inner: "max (real (depth_formula ?A0))
                             (max (real (depth_formula ?MID)) (real (depth_formula ?BB)))
                         \<le> real (depth_formula (Conn cc0 fs))
                            + 2 * \<bar>tc\<bar> * log 2 (real MF + 1) + tcm * log 2 (real MF + 1) + 1"
              using iA0 iMID iBB by simp
            have "real trans_step_depth
                  + (real (depth_formula (Conn cc0 fs))
                     + 2 * \<bar>tc\<bar> * log 2 (real MF + 1) + tcm * log 2 (real MF + 1) + 1)
                  \<le> real (depth_formula (Conn cc0 fs)) + cc * log 2 (real MF + 1)"
              using ccLT dT tsdL lgn1 by linarith
            thus ?thesis using inner by linarith
          qed
          have L_ccmsd: "real conn_cong_max_step_depth
                         + max (real (depth_formula ?MID)) (real (depth_formula ?BB))
                         \<le> real (depth_formula (Conn cc0 fs)) + cc * log 2 (real MF + 1)"
          proof -
            have inner: "max (real (depth_formula ?MID)) (real (depth_formula ?BB))
                         \<le> real (depth_formula (Conn cc0 fs))
                            + 2 * \<bar>tc\<bar> * log 2 (real MF + 1) + tcm * log 2 (real MF + 1) + 1"
              using iMID iBB by simp
            have "real conn_cong_max_step_depth
                  + (real (depth_formula (Conn cc0 fs))
                     + 2 * \<bar>tc\<bar> * log 2 (real MF + 1) + tcm * log 2 (real MF + 1) + 1)
                  \<le> real (depth_formula (Conn cc0 fs)) + cc * log 2 (real MF + 1)"
              using ccLCm dCm cmL lgn1 by linarith
            thus ?thesis using inner by linarith
          qed
          have L_dA: "real dA \<le> real (depth_formula (Conn cc0 fs)) + cc * log 2 (real MF + 1)"
            using dA_b dC2 ccLC dcnn by linarith
          have dB_le: "real dB \<le> real (depth_formula (Conn cc0 fs)) + cc * log 2 (real MF + 1)"
          proof -
            have "real dB
                  \<le> real (max ?Dc (conn_cong_max_step_depth
                              + max (depth_formula ?MID) (depth_formula ?BB)))"
              using pBd by (simp only: of_nat_le_iff)
            also have "\<dots> = max (real ?Dc) (real conn_cong_max_step_depth
                              + max (real (depth_formula ?MID)) (real (depth_formula ?BB)))"
              by (simp add: of_nat_max)
            also have "\<dots> \<le> real (depth_formula (Conn cc0 fs)) + cc * log 2 (real MF + 1)"
              using Dc_b L_ccmsd by (simp only: max.bounded_iff)
            finally show ?thesis .
          qed
          have e: "real (max dA (max dB (trans_step_depth
                       + max (depth_formula ?A0) (max (depth_formula ?MID) (depth_formula ?BB)))))
                   = max (real dA) (max (real dB) (real trans_step_depth
                       + max (real (depth_formula ?A0))
                             (max (real (depth_formula ?MID)) (real (depth_formula ?BB)))))"
            by (simp only: of_nat_max of_nat_add)
          show ?thesis unfolding e by (intro max.boundedI L_dA dB_le L_trans)
        qed
        show "\<exists>lines sz dep.
                provable_balanced_iff (spira_trans (sub_formula sub (Conn cc0 fs)))
                  (sub_formula (\<lambda>v. spira_trans (sub v)) (Conn cc0 fs)) lines sz dep
              \<and> lines \<le> len_formula (sub_formula sub (Conn cc0 fs))
                  * poly PP (len_formula (Conn cc0 fs)
                             + (\<Sum>v\<in>var_set_form (Conn cc0 fs). len_formula (sub v)))
              \<and> sz \<le> len_formula (sub_formula sub (Conn cc0 fs))
                  * poly PP (len_formula (Conn cc0 fs)
                             + (\<Sum>v\<in>var_set_form (Conn cc0 fs). len_formula (sub v)))
              \<and> real dep \<le> real (depth_formula (Conn cc0 fs))
                  + cc * log 2 (real (len_formula (Conn cc0 fs)
                                  + (\<Sum>v\<in>var_set_form (Conn cc0 fs). len_formula (sub v))) + 1)"
        proof (rule exI[of _ "lA + lB + trans_lines"],
               rule exI[of _ "sA + sB + trans_step_len
                              * (len_formula ?A0 + len_formula ?MID + len_formula ?BB)"],
               rule exI[of _ "max dA (max dB (trans_step_depth
                              + max (depth_formula ?A0)
                                    (max (depth_formula ?MID) (depth_formula ?BB))))"],
               intro conjI)
          show "provable_balanced_iff (spira_trans (sub_formula sub (Conn cc0 fs)))
                  (sub_formula (\<lambda>v. spira_trans (sub v)) (Conn cc0 fs))
                  (lA + lB + trans_lines)
                  (sA + sB + trans_step_len * (len_formula ?A0 + len_formula ?MID + len_formula ?BB))
                  (max dA (max dB (trans_step_depth
                       + max (depth_formula ?A0) (max (depth_formula ?MID) (depth_formula ?BB)))))"
            using pC by (simp only: sub_formula.simps)
          show "lA + lB + trans_lines
                \<le> len_formula (sub_formula sub (Conn cc0 fs))
                  * poly PP (len_formula (Conn cc0 fs)
                             + (\<Sum>v\<in>var_set_form (Conn cc0 fs). len_formula (sub v)))"
            by (rule B1[unfolded MF_def])
          show "sA + sB + trans_step_len * (len_formula ?A0 + len_formula ?MID + len_formula ?BB)
                \<le> len_formula (sub_formula sub (Conn cc0 fs))
                  * poly PP (len_formula (Conn cc0 fs)
                             + (\<Sum>v\<in>var_set_form (Conn cc0 fs). len_formula (sub v)))"
            by (rule B2[unfolded MF_def])
          show "real (max dA (max dB (trans_step_depth
                     + max (depth_formula ?A0) (max (depth_formula ?MID) (depth_formula ?BB)))))
                \<le> real (depth_formula (Conn cc0 fs))
                  + cc * log 2 (real (len_formula (Conn cc0 fs)
                                  + (\<Sum>v\<in>var_set_form (Conn cc0 fs). len_formula (sub v))) + 1)"
            by (rule B3[unfolded MF_def])
        qed
      qed
    qed
    thus "formula_well_formed (alphabet F) f0
       \<Longrightarrow> (\<forall>v. formula_well_formed (alphabet F) (sub v))
       \<Longrightarrow> (\<exists>lines sz dep.
              provable_balanced_iff (spira_trans (sub_formula sub f0))
                (sub_formula (\<lambda>v. spira_trans (sub v)) f0) lines sz dep
            \<and> lines \<le> len_formula (sub_formula sub f0)
                * poly PP (len_formula f0 + (\<Sum>v\<in>var_set_form f0. len_formula (sub v)))
            \<and> sz \<le> len_formula (sub_formula sub f0)
                * poly PP (len_formula f0 + (\<Sum>v\<in>var_set_form f0. len_formula (sub v)))
            \<and> real dep \<le> real (depth_formula f0)
                + cc * log 2 (real (len_formula f0
                                + (\<Sum>v\<in>var_set_form f0. len_formula (sub v))) + 1))"
      by blast
  qed
  show ?thesis
  proof (intro exI[where x = "monom 1 2 * PP"] exI[where x = cc] allI impI)
    fix f :: "'a formula" and sub :: "string \<Rightarrow> 'a formula"
    assume A: "formula_well_formed (alphabet F) f
               \<and> (\<forall>f'\<in>range sub. formula_well_formed (alphabet F) f')"
    have wff: "formula_well_formed (alphabet F) f" using A by simp
    have wfs: "\<forall>v. formula_well_formed (alphabet F) (sub v)" using A by blast
    let ?M = "len_formula f + (\<Sum>v\<in>var_set_form f. len_formula (sub v))"
    obtain lines sz dep where M:
      "provable_balanced_iff (spira_trans (sub_formula sub f))
         (sub_formula (\<lambda>v. spira_trans (sub v)) f) lines sz dep"
      "lines \<le> len_formula (sub_formula sub f) * poly PP ?M"
      "sz \<le> len_formula (sub_formula sub f) * poly PP ?M"
      "real dep \<le> real (depth_formula f) + cc * log 2 (real ?M + 1)"
      using main[OF wff wfs] by blast
    have lensq: "len_formula (sub_formula sub f) \<le> ?M * ?M"
    proof -
      have "len_formula (sub_formula sub f) \<le> len_formula f * ?M"
        by (rule len_sub_form_le)
      also have "\<dots> \<le> ?M * ?M" by (rule mult_le_mono1) simp
      finally show ?thesis .
    qed
    have monomval: "poly (monom (1::nat) 2) ?M = ?M * ?M"
      by (simp add: poly_monom power2_eq_square)
    have polyeq: "poly (monom 1 2 * PP) ?M = ?M * ?M * poly PP ?M"
    proof -
      have "poly (monom 1 2 * PP) ?M = poly (monom (1::nat) 2) ?M * poly PP ?M"
        by (rule poly_mult)
      from this[unfolded monomval] show ?thesis .
    qed
    have envl: "\<And>x. x \<le> len_formula (sub_formula sub f) * poly PP ?M
                  \<Longrightarrow> x \<le> poly (monom 1 2 * PP) ?M"
    proof -
      fix x assume "x \<le> len_formula (sub_formula sub f) * poly PP ?M"
      also have "len_formula (sub_formula sub f) * poly PP ?M \<le> (?M * ?M) * poly PP ?M"
        using lensq by (rule mult_le_mono1)
      also have "\<dots> = poly (monom 1 2 * PP) ?M" by (rule polyeq[symmetric])
      finally show "x \<le> poly (monom 1 2 * PP) ?M" .
    qed
    show "let M = len_formula f + (\<Sum>v\<in>var_set_form f. len_formula (sub v))
          in (\<exists>lines sz dep. provable_balanced_iff (spira_trans (sub_formula sub f))
                (sub_formula (\<lambda>v. spira_trans (sub v)) f) lines sz dep
              \<and> lines \<le> poly (monom 1 2 * PP) M \<and> sz \<le> poly (monom 1 2 * PP) M
              \<and> real dep \<le> real (depth_formula f) + cc * log 2 (real M + 1))"
      unfolding Let_def
      using M(1) envl[OF M(2)] envl[OF M(3)] M(4) by blast
  qed
qed
end
end