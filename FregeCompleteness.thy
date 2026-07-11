theory FregeCompleteness
  imports
    "Propositional_Proof_Systems.HC_Compl_Consistency"
    "Propositional_Proof_Systems.Compactness"
    Frege
begin

text \<open>Completeness of Frege systems over a functionally complete alphabet,
  bridged from the AFP entry @{theory Propositional_Proof_Systems.HC} (a Hilbert
  calculus) and its completeness/compactness.  This discharges the one remaining
  obligation of the closure construction in Section6.\<close>

subsection \<open>Big conjunction/disjunction over AFP formulas\<close>

fun big_or :: "'a Formulas.formula list \<Rightarrow> 'a Formulas.formula" where
  "big_or [] = Formulas.Bot"
| "big_or (F # Fs) = Formulas.Or F (big_or Fs)"

fun big_and :: "'a Formulas.formula list \<Rightarrow> 'a Formulas.formula" where
  "big_and [] = Formulas.Not Formulas.Bot"
| "big_and (F # Fs) = Formulas.And F (big_and Fs)"

lemma big_or_sema:
  "formula_semantics A (big_or Fs) \<longleftrightarrow> (\<exists>F\<in>set Fs. formula_semantics A F)"
  by (induction Fs) auto

lemma big_and_sema:
  "formula_semantics A (big_and Fs) \<longleftrightarrow> (\<forall>F\<in>set Fs. formula_semantics A F)"
  by (induction Fs) auto

subsection \<open>Truth table of a connective as an AFP formula\<close>

definition lit :: "bool \<Rightarrow> 'a Formulas.formula \<Rightarrow> 'a Formulas.formula" where
  "lit b F = (if b then F else Formulas.Not F)"

lemma lit_sema: "formula_semantics A (lit b F) \<longleftrightarrow> (b = formula_semantics A F)"
  by (auto simp: lit_def)

definition mk_conn :: "(bool list \<Rightarrow> bool) \<Rightarrow> 'a Formulas.formula list \<Rightarrow> 'a Formulas.formula" where
  "mk_conn g args =
     big_or (map (\<lambda>v. big_and (map (\<lambda>i. lit (v ! i) (args ! i)) [0..<length args]))
                 (filter g (List.n_lists (length args) [True, False])))"

lemma mk_conn_sema:
  "formula_semantics A (mk_conn g args) \<longleftrightarrow> g (map (formula_semantics A) args)"
proof -
  let ?n = "length args"
  let ?w = "map (formula_semantics A) args"
  have band: "formula_semantics A (big_and (map (\<lambda>i. lit (v ! i) (args ! i)) [0..<?n])) \<longleftrightarrow> v = ?w"
    if "v \<in> set (List.n_lists ?n [True, False])" for v
  proof -
    from that have lv: "length v = ?n" by (simp add: set_n_lists)
    have "formula_semantics A (big_and (map (\<lambda>i. lit (v ! i) (args ! i)) [0..<?n]))
          \<longleftrightarrow> (\<forall>i<?n. v ! i = formula_semantics A (args ! i))"
      by (auto simp: big_and_sema lit_sema)
    also have "\<dots> \<longleftrightarrow> v = ?w" using lv by (auto intro!: nth_equalityI)
    finally show ?thesis .
  qed
  have "formula_semantics A (mk_conn g args)
        \<longleftrightarrow> (\<exists>v \<in> set (filter g (List.n_lists ?n [True, False])).
              formula_semantics A (big_and (map (\<lambda>i. lit (v ! i) (args ! i)) [0..<?n])))"
    unfolding mk_conn_def by (simp add: big_or_sema)
  also have "\<dots> \<longleftrightarrow> (\<exists>v \<in> set (List.n_lists ?n [True, False]). g v \<and> v = ?w)"
    using band by auto
  also have "\<dots> \<longleftrightarrow> g ?w"
    by (auto simp: set_n_lists)
  finally show ?thesis .
qed

subsection \<open>Translating Frege formulas to AFP formulas (semantics preserving)\<close>

fun tr :: "'c alphabet \<Rightarrow> 'c formula \<Rightarrow> string Formulas.formula" where
  "tr alph (Atom a) = Formulas.Atom a"
| "tr alph (Conn c args) = mk_conn (conn_evals alph c) (map (tr alph) args)"

lemma tr_sema: "formula_semantics val (tr alph f) \<longleftrightarrow> eval alph val f"
proof (induction f)
  case (Atom a)
  show ?case by simp
next
  case (Conn c args)
  have mapeq: "map (formula_semantics val) (map (tr alph) args) = map (eval alph val) args"
    by (simp add: Conn.IH)
  have "formula_semantics val (tr alph (Conn c args))
        = conn_evals alph c (map (formula_semantics val) (map (tr alph) args))"
    by (simp add: mk_conn_sema)
  also have "\<dots> = conn_evals alph c (map (eval alph val) args)"
    by (simp only: mapeq)
  also have "\<dots> = eval alph val (Conn c args)" by simp
  finally show ?case .
qed

subsection \<open>From semantic entailment to a finite Hilbert derivation\<close>

lemma imps_sema:
  "formula_semantics A (foldr Formulas.Imp ds G)
   \<longleftrightarrow> ((\<forall>d\<in>set ds. formula_semantics A d) \<longrightarrow> formula_semantics A G)"
  by (induction ds) auto

lemma HC_peel:
  "AX10 \<union> \<Delta> \<turnstile>\<^sub>H foldr Formulas.Imp ds G \<Longrightarrow> AX10 \<union> \<Delta> \<union> set ds \<turnstile>\<^sub>H G"
proof (induction ds arbitrary: \<Delta> G)
  case Nil
  thus ?case by simp
next
  case (Cons d ds)
  have "AX10 \<union> insert d \<Delta> \<turnstile>\<^sub>H foldr Formulas.Imp ds G"
  proof -
    have "AX10 \<union> \<Delta> \<turnstile>\<^sub>H Formulas.Imp d (foldr Formulas.Imp ds G)"
      using Cons.prems by simp
    hence "AX10 \<union> insert d \<Delta> \<turnstile>\<^sub>H Formulas.Imp d (foldr Formulas.Imp ds G)"
      by (rule HC_mono) auto
    moreover have "AX10 \<union> insert d \<Delta> \<turnstile>\<^sub>H d" by (rule HC.Ax) simp
    ultimately show ?thesis using MP by blast
  qed
  from Cons.IH[OF this] have "AX10 \<union> insert d \<Delta> \<union> set ds \<turnstile>\<^sub>H G" .
  moreover have "AX10 \<union> insert d \<Delta> \<union> set ds = AX10 \<union> \<Delta> \<union> set (d # ds)" by auto
  ultimately show ?case by simp
qed

lemma finite_entailment_HC:
  fixes G :: "('a :: countable) Formulas.formula"
  assumes "finite \<Delta>" and "entailment \<Delta> G"
  shows "AX10 \<union> \<Delta> \<turnstile>\<^sub>H G"
proof -
  from assms(1) obtain ds where ds: "set ds = \<Delta>" using finite_list by blast
  have "\<forall>A. formula_semantics A (foldr Formulas.Imp ds G)"
    using assms(2) ds by (auto simp: entailment_def imps_sema)
  hence "AX10 \<turnstile>\<^sub>H foldr Formulas.Imp ds G" by (rule HC_complete)
  hence "AX10 \<union> {} \<turnstile>\<^sub>H foldr Formulas.Imp ds G" by simp
  from HC_peel[OF this] have "AX10 \<union> {} \<union> set ds \<turnstile>\<^sub>H G" .
  thus ?thesis using ds by simp
qed

lemma entailment_finite:
  fixes \<Gamma> :: "('a :: countable) Formulas.formula set"
  assumes "entailment \<Gamma> G"
  shows "\<exists>\<Delta>. finite \<Delta> \<and> \<Delta> \<subseteq> \<Gamma> \<and> entailment \<Delta> G"
proof -
  have "\<not> sat (\<Gamma> \<union> {Formulas.Not G})"
    using assms by (auto simp: entailment_def sat_def)
  hence "\<not> fin_sat (\<Gamma> \<union> {Formulas.Not G})" by (simp add: compactness)
  then obtain s where s: "s \<subseteq> \<Gamma> \<union> {Formulas.Not G}" "finite s" "\<not> sat s"
    by (auto simp: fin_sat_def)
  let ?\<Delta> = "s - {Formulas.Not G}"
  have "finite ?\<Delta>" using s(2) by simp
  moreover have "?\<Delta> \<subseteq> \<Gamma>" using s(1) by auto
  moreover have "entailment ?\<Delta> G"
    unfolding entailment_def
  proof (intro allI impI)
    fix A assume a: "\<forall>H\<in>?\<Delta>. formula_semantics A H"
    show "formula_semantics A G"
    proof (rule ccontr)
      assume "\<not> formula_semantics A G"
      hence "\<forall>F\<in>s. formula_semantics A F" using a s(1) by auto
      thus False using s(3) by (auto simp: sat_def)
    qed
  qed
  ultimately show ?thesis by blast
qed

lemma entailment_HC:
  fixes \<Gamma> :: "('a :: countable) Formulas.formula set"
  assumes "entailment \<Gamma> G"
  shows "\<exists>\<Delta>. finite \<Delta> \<and> \<Delta> \<subseteq> \<Gamma> \<and> (AX10 \<union> \<Delta> \<turnstile>\<^sub>H G)"
proof -
  from entailment_finite[OF assms] obtain \<Delta>
    where "finite \<Delta>" "\<Delta> \<subseteq> \<Gamma>" "entailment \<Delta> G" by blast
  thus ?thesis using finite_entailment_HC by blast
qed

subsection \<open>Substitution semantics (Frege side)\<close>

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

lemma sub_formula_compose:
  "sub_formula g (sub_formula h f) = sub_formula (\<lambda>s. sub_formula g (h s)) f"
  by (induction f) auto

lemma sub_formula_cong:
  assumes "\<And>v. v \<in> var_set_form f \<Longrightarrow> s1 v = s2 v"
  shows "sub_formula s1 f = sub_formula s2 f"
  using assms by (induction f) auto

lemma var_set_sub:
  "var_set_form (sub_formula s f) = (\<Union>a\<in>var_set_form f. var_set_form (s a))"
  by (induction f) auto


subsection \<open>A locale fixing the alphabet and its standard connectives\<close>

locale fc_alph =
  fixes alph :: "'c alphabet"
    and cimp :: "'c formula \<Rightarrow> 'c formula \<Rightarrow> 'c formula"
    and cand :: "'c formula \<Rightarrow> 'c formula \<Rightarrow> 'c formula"
    and cor  :: "'c formula \<Rightarrow> 'c formula \<Rightarrow> 'c formula"
    and cneg :: "'c formula \<Rightarrow> 'c formula"
    and cfls :: "'c formula"
  assumes fin: "finite (UNIV :: 'c set)"
    and cimp_eval: "eval alph val (cimp \<phi> \<psi>) = (eval alph val \<phi> \<longrightarrow> eval alph val \<psi>)"
    and cand_eval: "eval alph val (cand \<phi> \<psi>) = (eval alph val \<phi> \<and> eval alph val \<psi>)"
    and cor_eval:  "eval alph val (cor \<phi> \<psi>)  = (eval alph val \<phi> \<or> eval alph val \<psi>)"
    and cneg_eval: "eval alph val (cneg \<phi>) = (\<not> eval alph val \<phi>)"
    and cfls_eval: "eval alph val cfls = False"
    and func_complete: "\<forall>f :: dm_conn formula. \<exists>f' :: 'c formula.
            formula_well_formed alph f' \<and> formulas_equiv f dm_alphabet f' alph"
    and htop: "\<exists>t. arity alph t = 0 \<and> (\<forall>val. eval alph val (Conn t []) = True)"
    and hbot: "\<exists>b. arity alph b = 0 \<and> (\<forall>val. eval alph val (Conn b []) = False)"
begin

fun bt :: "string Formulas.formula \<Rightarrow> 'c formula" where
  "bt (Formulas.Atom a) = Atom a"
| "bt Formulas.Bot = cfls"
| "bt (Formulas.Not G) = cneg (bt G)"
| "bt (Formulas.And G H) = cand (bt G) (bt H)"
| "bt (Formulas.Or G H) = cor (bt G) (bt H)"
| "bt (Formulas.Imp G H) = cimp (bt G) (bt H)"

lemma bt_eval: "eval alph val (bt G) = formula_semantics val G"
  by (induction G) (simp_all add: cimp_eval cand_eval cor_eval cneg_eval cfls_eval)

subsection \<open>A 'c-level DNF (mirror of mk_conn) and bi-implication\<close>

definition ciff :: "'c formula \<Rightarrow> 'c formula \<Rightarrow> 'c formula" where
  "ciff a b = cand (cimp a b) (cimp b a)"

definition clit :: "bool \<Rightarrow> 'c formula \<Rightarrow> 'c formula" where
  "clit b \<phi> = (if b then \<phi> else cneg \<phi>)"

lemma clit_eval: "eval alph val (clit b \<phi>) = (b = eval alph val \<phi>)"
  by (auto simp: clit_def cneg_eval)

fun cbig_and :: "'c formula list \<Rightarrow> 'c formula" where
  "cbig_and [] = cneg cfls"
| "cbig_and (\<phi> # \<phi>s) = cand \<phi> (cbig_and \<phi>s)"

lemma cbig_and_eval: "eval alph val (cbig_and \<phi>s) = (\<forall>\<phi>\<in>set \<phi>s. eval alph val \<phi>)"
  by (induction \<phi>s) (auto simp: cand_eval cneg_eval cfls_eval)

fun cbig_or :: "'c formula list \<Rightarrow> 'c formula" where
  "cbig_or [] = cfls"
| "cbig_or (\<phi> # \<phi>s) = cor \<phi> (cbig_or \<phi>s)"

lemma cbig_or_eval: "eval alph val (cbig_or \<phi>s) = (\<exists>\<phi>\<in>set \<phi>s. eval alph val \<phi>)"
  by (induction \<phi>s) (auto simp: cor_eval cfls_eval)

definition cmk_conn :: "(bool list \<Rightarrow> bool) \<Rightarrow> 'c formula list \<Rightarrow> 'c formula" where
  "cmk_conn g args =
     cbig_or (map (\<lambda>v. cbig_and (map (\<lambda>i. clit (v ! i) (args ! i)) [0..<length args]))
                  (filter g (List.n_lists (length args) [True, False])))"

lemma cmk_conn_eval:
  "eval alph val (cmk_conn g args) = g (map (eval alph val) args)"
proof -
  let ?n = "length args"
  let ?w = "map (eval alph val) args"
  have band: "eval alph val (cbig_and (map (\<lambda>i. clit (v ! i) (args ! i)) [0..<?n])) \<longleftrightarrow> v = ?w"
    if "v \<in> set (List.n_lists ?n [True, False])" for v
  proof -
    from that have lv: "length v = ?n" by (simp add: set_n_lists)
    have "eval alph val (cbig_and (map (\<lambda>i. clit (v ! i) (args ! i)) [0..<?n]))
          \<longleftrightarrow> (\<forall>i<?n. v ! i = eval alph val (args ! i))"
      by (auto simp: cbig_and_eval clit_eval)
    also have "\<dots> \<longleftrightarrow> v = ?w" using lv by (auto intro!: nth_equalityI)
    finally show ?thesis .
  qed
  have "eval alph val (cmk_conn g args)
        \<longleftrightarrow> (\<exists>v \<in> set (filter g (List.n_lists ?n [True, False])).
              eval alph val (cbig_and (map (\<lambda>i. clit (v ! i) (args ! i)) [0..<?n])))"
    unfolding cmk_conn_def by (simp add: cbig_or_eval)
  also have "\<dots> \<longleftrightarrow> (\<exists>v \<in> set (List.n_lists ?n [True, False]). g v \<and> v = ?w)"
    using band by auto
  also have "\<dots> \<longleftrightarrow> g ?w"
    by (auto simp: set_n_lists)
  finally show ?thesis .
qed

lemma bt_big_or: "bt (big_or Fs) = cbig_or (map bt Fs)"
  by (induction Fs) auto

lemma bt_big_and: "bt (big_and Fs) = cbig_and (map bt Fs)"
  by (induction Fs) auto

lemma bt_lit: "bt (lit b F) = clit b (bt F)"
  by (simp add: lit_def clit_def)

lemma bt_mk_conn: "bt (mk_conn g afps) = cmk_conn g (map bt afps)"
proof -
  have "bt (mk_conn g afps)
      = cbig_or (map (\<lambda>v. cbig_and (map (\<lambda>i. clit (v ! i) (bt (afps ! i))) [0..<length afps]))
                     (filter g (List.n_lists (length afps) [True, False])))"
    unfolding mk_conn_def by (simp add: bt_big_or bt_big_and bt_lit o_def)
  also have "\<dots> = cmk_conn g (map bt afps)"
  proof -
    have "(\<lambda>v. cbig_and (map (\<lambda>i. clit (v ! i) (bt (afps ! i))) [0..<length afps]))
        = (\<lambda>v. cbig_and (map (\<lambda>i. clit (v ! i) (map bt afps ! i)) [0..<length afps]))"
    proof (rule ext)
      fix v
      have eq: "map (\<lambda>i. clit (v ! i) (bt (afps ! i))) [0..<length afps]
          = map (\<lambda>i. clit (v ! i) (map bt afps ! i)) [0..<length afps]"
        by (intro map_cong refl) simp
      show "cbig_and (map (\<lambda>i. clit (v ! i) (bt (afps ! i))) [0..<length afps])
          = cbig_and (map (\<lambda>i. clit (v ! i) (map bt afps ! i)) [0..<length afps])"
        by (rule arg_cong[OF eq])
    qed
    thus ?thesis unfolding cmk_conn_def by simp
  qed
  finally show ?thesis .
qed

subsection \<open>Commuting the DNF constructions with substitution\<close>

text \<open>These lemmas push a substitution through the derived constructions, given that
  it commutes with the primitive connectives.  They are used to realise the axiom
  schemas as concrete Frege rules over marker atoms.\<close>

lemma clit_sub:
  assumes cn: "\<And>a. sub_formula sub (cneg a) = cneg (sub_formula sub a)"
  shows "sub_formula sub (clit b \<phi>) = clit b (sub_formula sub \<phi>)"
  by (cases b) (simp_all add: clit_def cn)

lemma cbig_and_sub:
  assumes ca: "\<And>a b. sub_formula sub (cand a b) = cand (sub_formula sub a) (sub_formula sub b)"
    and cn: "\<And>a. sub_formula sub (cneg a) = cneg (sub_formula sub a)"
    and cf: "sub_formula sub cfls = cfls"
  shows "sub_formula sub (cbig_and \<phi>s) = cbig_and (map (sub_formula sub) \<phi>s)"
  by (induction \<phi>s) (simp_all add: ca cn cf)

lemma cbig_or_sub:
  assumes co: "\<And>a b. sub_formula sub (cor a b) = cor (sub_formula sub a) (sub_formula sub b)"
    and cf: "sub_formula sub cfls = cfls"
  shows "sub_formula sub (cbig_or \<phi>s) = cbig_or (map (sub_formula sub) \<phi>s)"
  by (induction \<phi>s) (simp_all add: co cf)

lemma cmk_conn_sub:
  assumes ca: "\<And>a b. sub_formula sub (cand a b) = cand (sub_formula sub a) (sub_formula sub b)"
    and co: "\<And>a b. sub_formula sub (cor a b) = cor (sub_formula sub a) (sub_formula sub b)"
    and cn: "\<And>a. sub_formula sub (cneg a) = cneg (sub_formula sub a)"
    and cf: "sub_formula sub cfls = cfls"
  shows "sub_formula sub (cmk_conn g args) = cmk_conn g (map (sub_formula sub) args)"
proof -
  let ?n = "length args"
  let ?F = "filter g (List.n_lists ?n [True, False])"
  have inner: "sub_formula sub (cbig_and (map (\<lambda>i. clit (v ! i) (args ! i)) [0..<?n]))
             = cbig_and (map (\<lambda>i. clit (v ! i) (map (sub_formula sub) args ! i)) [0..<?n])" for v
  proof -
    have "sub_formula sub (cbig_and (map (\<lambda>i. clit (v ! i) (args ! i)) [0..<?n]))
        = cbig_and (map (sub_formula sub) (map (\<lambda>i. clit (v ! i) (args ! i)) [0..<?n]))"
      by (rule cbig_and_sub[OF ca cn cf])
    also have "\<dots> = cbig_and (map (\<lambda>i. clit (v ! i) (map (sub_formula sub) args ! i)) [0..<?n])"
    proof -
      have "map (sub_formula sub) (map (\<lambda>i. clit (v ! i) (args ! i)) [0..<?n])
          = map (\<lambda>i. clit (v ! i) (sub_formula sub (args ! i))) [0..<?n]"
        by (simp add: clit_sub[OF cn] o_def)
      also have "\<dots> = map (\<lambda>i. clit (v ! i) (map (sub_formula sub) args ! i)) [0..<?n]"
        by (intro map_cong refl) simp
      finally show ?thesis by (rule arg_cong)
    qed
    finally show ?thesis .
  qed
  have "sub_formula sub (cmk_conn g args)
      = cbig_or (map (sub_formula sub)
                     (map (\<lambda>v. cbig_and (map (\<lambda>i. clit (v ! i) (args ! i)) [0..<?n])) ?F))"
    unfolding cmk_conn_def by (rule cbig_or_sub[OF co cf])
  also have "\<dots> = cbig_or (map (\<lambda>v. cbig_and (map (\<lambda>i. clit (v ! i) (map (sub_formula sub) args ! i)) [0..<?n])) ?F)"
    by (simp add: inner o_def)
  also have "\<dots> = cmk_conn g (map (sub_formula sub) args)"
    unfolding cmk_conn_def by simp
  finally show ?thesis .
qed

lemma ciff_sub:
  assumes ci: "\<And>a b. sub_formula sub (cimp a b) = cimp (sub_formula sub a) (sub_formula sub b)"
    and ca: "\<And>a b. sub_formula sub (cand a b) = cand (sub_formula sub a) (sub_formula sub b)"
  shows "sub_formula sub (ciff a b) = ciff (sub_formula sub a) (sub_formula sub b)"
  by (simp add: ciff_def ca ci)


subsection \<open>A 'c-level Hilbert calculus mirroring AX10\<close>

inductive_set cAX :: "'c formula set" where
  cK:     "cimp F (cimp G F) \<in> cAX"
| cS:     "cimp (cimp F (cimp G H)) (cimp (cimp F G) (cimp F H)) \<in> cAX"
| cOrI1:  "cimp F (cor F G) \<in> cAX"
| cOrI2:  "cimp G (cor F G) \<in> cAX"
| cOrE:   "cimp (cimp F H) (cimp (cimp G H) (cimp (cor F G) H)) \<in> cAX"
| cAndE1: "cimp (cand F G) F \<in> cAX"
| cAndE2: "cimp (cand F G) G \<in> cAX"
| cAndI:  "cimp F (cimp G (cand F G)) \<in> cAX"
| cNotI:  "cimp (cimp F cfls) (cneg F) \<in> cAX"
| cNotE:  "cimp (cneg F) (cimp F cfls) \<in> cAX"
| cRAA:   "cimp (cimp (cneg F) cfls) F \<in> cAX"
| cDef:   "length xs = arity alph c \<Longrightarrow>
             ciff (Conn c xs) (cmk_conn (conn_evals alph c) xs) \<in> cAX"

lemma cAX_tautology: "\<phi> \<in> cAX \<Longrightarrow> eval alph val \<phi>"
  by (induction rule: cAX.induct)
     (auto simp: ciff_def cimp_eval cand_eval cor_eval cneg_eval cfls_eval cmk_conn_eval)

inductive cder :: "'c formula set \<Rightarrow> 'c formula \<Rightarrow> bool" for \<Gamma> where
  cAx:     "\<phi> \<in> \<Gamma> \<Longrightarrow> cder \<Gamma> \<phi>"
| cAxiom:  "\<phi> \<in> cAX \<Longrightarrow> cder \<Gamma> \<phi>"
| cMP:     "cder \<Gamma> \<phi> \<Longrightarrow> cder \<Gamma> (cimp \<phi> \<psi>) \<Longrightarrow> cder \<Gamma> \<psi>"

lemma cder_weaken: "cder \<Gamma> \<phi> \<Longrightarrow> \<Gamma> \<subseteq> \<Gamma>' \<Longrightarrow> cder \<Gamma>' \<phi>"
  by (induction rule: cder.induct) (auto intro: cder.intros)

lemma cder_sound:
  assumes "cder \<Gamma> \<phi>"
  shows "(\<forall>g\<in>\<Gamma>. eval alph val g) \<Longrightarrow> eval alph val \<phi>"
  using assms by (induction rule: cder.induct) (auto simp: cAX_tautology cimp_eval)

lemma cI: "cder \<Gamma> (cimp F F)"
proof -
  have s: "cder \<Gamma> (cimp (cimp F (cimp (cimp F F) F)) (cimp (cimp F (cimp F F)) (cimp F F)))"
    by (rule cder.cAxiom[OF cAX.cS])
  have k1: "cder \<Gamma> (cimp F (cimp (cimp F F) F))" by (rule cder.cAxiom[OF cAX.cK])
  have step: "cder \<Gamma> (cimp (cimp F (cimp F F)) (cimp F F))" using cder.cMP[OF k1 s] .
  have k2: "cder \<Gamma> (cimp F (cimp F F))" by (rule cder.cAxiom[OF cAX.cK])
  show ?thesis using cder.cMP[OF k2 step] .
qed

lemma cder_deduction:
  assumes "cder (insert a \<Gamma>) \<phi>"
  shows "cder \<Gamma> (cimp a \<phi>)"
  using assms
proof (induction rule: cder.induct)
  case (cAx \<phi>)
  show ?case
  proof (cases "\<phi> = a")
    case True
    thus ?thesis using cI by simp
  next
    case False
    hence "\<phi> \<in> \<Gamma>" using cAx by simp
    hence "cder \<Gamma> \<phi>" by (rule cder.cAx)
    moreover have "cder \<Gamma> (cimp \<phi> (cimp a \<phi>))" by (rule cder.cAxiom[OF cAX.cK])
    ultimately show ?thesis using cder.cMP by blast
  qed
next
  case (cAxiom \<phi>)
  hence "cder \<Gamma> \<phi>" by (rule cder.cAxiom)
  moreover have "cder \<Gamma> (cimp \<phi> (cimp a \<phi>))" by (rule cder.cAxiom[OF cAX.cK])
  ultimately show ?case using cder.cMP by blast
next
  case (cMP \<phi> \<psi>)
  have s: "cder \<Gamma> (cimp (cimp a (cimp \<phi> \<psi>)) (cimp (cimp a \<phi>) (cimp a \<psi>)))"
    by (rule cder.cAxiom[OF cAX.cS])
  have step1: "cder \<Gamma> (cimp (cimp a \<phi>) (cimp a \<psi>))"
    using cder.cMP[OF cMP.IH(2) s] .
  show ?case using cder.cMP[OF cMP.IH(1) step1] .
qed

lemma cder_cut:
  assumes "cder (insert a \<Gamma>) \<phi>" and "cder \<Gamma> a"
  shows "cder \<Gamma> \<phi>"
  using cder_deduction[OF assms(1)] assms(2) cder.cMP by blast

subsection \<open>Natural-deduction toolkit for cder\<close>

lemma cder_mp: "cder \<Gamma> (cimp a b) \<Longrightarrow> cder \<Gamma> a \<Longrightarrow> cder \<Gamma> b"
  using cder.cMP by blast

lemma cand_intro: "cder \<Gamma> a \<Longrightarrow> cder \<Gamma> b \<Longrightarrow> cder \<Gamma> (cand a b)"
  using cder.cAxiom[OF cAX.cAndI] cder.cMP by blast

lemma cand_elim1: "cder \<Gamma> (cand a b) \<Longrightarrow> cder \<Gamma> a"
  using cder.cAxiom[OF cAX.cAndE1] cder.cMP by blast

lemma cand_elim2: "cder \<Gamma> (cand a b) \<Longrightarrow> cder \<Gamma> b"
  using cder.cAxiom[OF cAX.cAndE2] cder.cMP by blast

lemma cor_intro1: "cder \<Gamma> a \<Longrightarrow> cder \<Gamma> (cor a b)"
  using cder.cAxiom[OF cAX.cOrI1] cder.cMP by blast

lemma cor_intro2: "cder \<Gamma> b \<Longrightarrow> cder \<Gamma> (cor a b)"
  using cder.cAxiom[OF cAX.cOrI2] cder.cMP by blast

lemma cor_elim:
  assumes "cder \<Gamma> (cor a b)" and "cder (insert a \<Gamma>) \<phi>" and "cder (insert b \<Gamma>) \<phi>"
  shows "cder \<Gamma> \<phi>"
proof -
  from assms(2) have 1: "cder \<Gamma> (cimp a \<phi>)" by (rule cder_deduction)
  from assms(3) have 2: "cder \<Gamma> (cimp b \<phi>)" by (rule cder_deduction)
  have "cder \<Gamma> (cimp (cimp a \<phi>) (cimp (cimp b \<phi>) (cimp (cor a b) \<phi>)))"
    by (rule cder.cAxiom[OF cAX.cOrE])
  hence "cder \<Gamma> (cimp (cimp b \<phi>) (cimp (cor a b) \<phi>))" using 1 cder.cMP by blast
  hence "cder \<Gamma> (cimp (cor a b) \<phi>)" using 2 cder.cMP by blast
  thus "cder \<Gamma> \<phi>" using assms(1) cder.cMP by blast
qed

lemma cfls_elim: "cder \<Gamma> cfls \<Longrightarrow> cder \<Gamma> \<phi>"
proof -
  assume f: "cder \<Gamma> cfls"
  have "cder \<Gamma> (cimp cfls (cimp (cneg \<phi>) cfls))" by (rule cder.cAxiom[OF cAX.cK])
  hence "cder \<Gamma> (cimp (cneg \<phi>) cfls)" using f cder.cMP by blast
  moreover have "cder \<Gamma> (cimp (cimp (cneg \<phi>) cfls) \<phi>)" by (rule cder.cAxiom[OF cAX.cRAA])
  ultimately show "cder \<Gamma> \<phi>" using cder.cMP by blast
qed

lemma cneg_intro: "cder (insert a \<Gamma>) cfls \<Longrightarrow> cder \<Gamma> (cneg a)"
proof -
  assume "cder (insert a \<Gamma>) cfls"
  hence "cder \<Gamma> (cimp a cfls)" by (rule cder_deduction)
  moreover have "cder \<Gamma> (cimp (cimp a cfls) (cneg a))" by (rule cder.cAxiom[OF cAX.cNotI])
  ultimately show "cder \<Gamma> (cneg a)" using cder.cMP by blast
qed

lemma cneg_mp: "cder \<Gamma> (cneg a) \<Longrightarrow> cder \<Gamma> a \<Longrightarrow> cder \<Gamma> \<phi>"
proof -
  assume n: "cder \<Gamma> (cneg a)" and a: "cder \<Gamma> a"
  have "cder \<Gamma> (cimp (cneg a) (cimp a cfls))" by (rule cder.cAxiom[OF cAX.cNotE])
  hence "cder \<Gamma> (cimp a cfls)" using n cder.cMP by blast
  hence "cder \<Gamma> cfls" using a cder.cMP by blast
  thus "cder \<Gamma> \<phi>" by (rule cfls_elim)
qed

\<comment> \<open>\<open>ciff\<close> defined earlier (before \<open>cAX\<close>)\<close>

lemma ciff_mp1: "cder \<Gamma> (ciff a b) \<Longrightarrow> cder \<Gamma> a \<Longrightarrow> cder \<Gamma> b"
  unfolding ciff_def using cand_elim1 cder_mp by blast

lemma ciff_mp2: "cder \<Gamma> (ciff a b) \<Longrightarrow> cder \<Gamma> b \<Longrightarrow> cder \<Gamma> a"
  unfolding ciff_def using cand_elim2 cder_mp by blast

lemma ciff_refl: "cder \<Gamma> (ciff a a)"
  unfolding ciff_def using cand_intro cI by blast

lemma ciff_sym: "cder \<Gamma> (ciff a b) \<Longrightarrow> cder \<Gamma> (ciff b a)"
  unfolding ciff_def using cand_intro cand_elim1 cand_elim2 by blast

lemma ciff_intro: "cder \<Gamma> (cimp a b) \<Longrightarrow> cder \<Gamma> (cimp b a) \<Longrightarrow> cder \<Gamma> (ciff a b)"
  unfolding ciff_def using cand_intro by blast

lemma ciff_trans:
  assumes "cder \<Gamma> (ciff a b)" and "cder \<Gamma> (ciff b c)"
  shows "cder \<Gamma> (ciff a c)"
proof (rule ciff_intro)
  show "cder \<Gamma> (cimp a c)"
  proof (rule cder_deduction)
    have iab: "cder (insert a \<Gamma>) (ciff a b)" by (rule cder_weaken[OF assms(1)]) auto
    have ibc: "cder (insert a \<Gamma>) (ciff b c)" by (rule cder_weaken[OF assms(2)]) auto
    have "cder (insert a \<Gamma>) a" by (rule cder.cAx) simp
    hence "cder (insert a \<Gamma>) b" by (rule ciff_mp1[OF iab])
    thus "cder (insert a \<Gamma>) c" by (rule ciff_mp1[OF ibc])
  qed
next
  show "cder \<Gamma> (cimp c a)"
  proof (rule cder_deduction)
    have iab: "cder (insert c \<Gamma>) (ciff a b)" by (rule cder_weaken[OF assms(1)]) auto
    have ibc: "cder (insert c \<Gamma>) (ciff b c)" by (rule cder_weaken[OF assms(2)]) auto
    have "cder (insert c \<Gamma>) c" by (rule cder.cAx) simp
    hence "cder (insert c \<Gamma>) b" by (rule ciff_mp2[OF ibc])
    thus "cder (insert c \<Gamma>) a" by (rule ciff_mp2[OF iab])
  qed
qed

lemma cneg_cong:
  assumes "cder \<Gamma> (ciff a a')"
  shows "cder \<Gamma> (ciff (cneg a) (cneg a'))"
proof (rule ciff_intro)
  show "cder \<Gamma> (cimp (cneg a) (cneg a'))"
  proof (rule cder_deduction, rule cneg_intro, rule cneg_mp[where a = a])
    show "cder (insert a' (insert (cneg a) \<Gamma>)) (cneg a)" by (rule cder.cAx) simp
    have ia: "cder (insert a' (insert (cneg a) \<Gamma>)) (ciff a a')"
      by (rule cder_weaken[OF assms]) auto
    have "cder (insert a' (insert (cneg a) \<Gamma>)) a'" by (rule cder.cAx) simp
    thus "cder (insert a' (insert (cneg a) \<Gamma>)) a" by (rule ciff_mp2[OF ia])
  qed
next
  show "cder \<Gamma> (cimp (cneg a') (cneg a))"
  proof (rule cder_deduction, rule cneg_intro, rule cneg_mp[where a = a'])
    show "cder (insert a (insert (cneg a') \<Gamma>)) (cneg a')" by (rule cder.cAx) simp
    have ia: "cder (insert a (insert (cneg a') \<Gamma>)) (ciff a a')"
      by (rule cder_weaken[OF assms]) auto
    have "cder (insert a (insert (cneg a') \<Gamma>)) a" by (rule cder.cAx) simp
    thus "cder (insert a (insert (cneg a') \<Gamma>)) a'" by (rule ciff_mp1[OF ia])
  qed
qed

lemma cand_cong:
  assumes "cder \<Gamma> (ciff a a')" and "cder \<Gamma> (ciff b b')"
  shows "cder \<Gamma> (ciff (cand a b) (cand a' b'))"
proof (rule ciff_intro)
  show "cder \<Gamma> (cimp (cand a b) (cand a' b'))"
  proof (rule cder_deduction)
    have ab: "cder (insert (cand a b) \<Gamma>) (cand a b)" by (rule cder.cAx) simp
    have ia: "cder (insert (cand a b) \<Gamma>) (ciff a a')" by (rule cder_weaken[OF assms(1)]) auto
    have ib: "cder (insert (cand a b) \<Gamma>) (ciff b b')" by (rule cder_weaken[OF assms(2)]) auto
    have "cder (insert (cand a b) \<Gamma>) a'" by (rule ciff_mp1[OF ia cand_elim1[OF ab]])
    moreover have "cder (insert (cand a b) \<Gamma>) b'" by (rule ciff_mp1[OF ib cand_elim2[OF ab]])
    ultimately show "cder (insert (cand a b) \<Gamma>) (cand a' b')" by (rule cand_intro)
  qed
next
  show "cder \<Gamma> (cimp (cand a' b') (cand a b))"
  proof (rule cder_deduction)
    have ab: "cder (insert (cand a' b') \<Gamma>) (cand a' b')" by (rule cder.cAx) simp
    have ia: "cder (insert (cand a' b') \<Gamma>) (ciff a a')" by (rule cder_weaken[OF assms(1)]) auto
    have ib: "cder (insert (cand a' b') \<Gamma>) (ciff b b')" by (rule cder_weaken[OF assms(2)]) auto
    have "cder (insert (cand a' b') \<Gamma>) a" by (rule ciff_mp2[OF ia cand_elim1[OF ab]])
    moreover have "cder (insert (cand a' b') \<Gamma>) b" by (rule ciff_mp2[OF ib cand_elim2[OF ab]])
    ultimately show "cder (insert (cand a' b') \<Gamma>) (cand a b)" by (rule cand_intro)
  qed
qed

lemma cor_cong:
  assumes "cder \<Gamma> (ciff a a')" and "cder \<Gamma> (ciff b b')"
  shows "cder \<Gamma> (ciff (cor a b) (cor a' b'))"
proof (rule ciff_intro)
  show "cder \<Gamma> (cimp (cor a b) (cor a' b'))"
  proof (rule cder_deduction, rule cor_elim[where a = a and b = b])
    show "cder (insert (cor a b) \<Gamma>) (cor a b)" by (rule cder.cAx) simp
  next
    have ia: "cder (insert a (insert (cor a b) \<Gamma>)) (ciff a a')" by (rule cder_weaken[OF assms(1)]) auto
    have "cder (insert a (insert (cor a b) \<Gamma>)) a'"
      by (rule ciff_mp1[OF ia]) (rule cder.cAx, simp)
    thus "cder (insert a (insert (cor a b) \<Gamma>)) (cor a' b')" by (rule cor_intro1)
  next
    have ib: "cder (insert b (insert (cor a b) \<Gamma>)) (ciff b b')" by (rule cder_weaken[OF assms(2)]) auto
    have "cder (insert b (insert (cor a b) \<Gamma>)) b'"
      by (rule ciff_mp1[OF ib]) (rule cder.cAx, simp)
    thus "cder (insert b (insert (cor a b) \<Gamma>)) (cor a' b')" by (rule cor_intro2)
  qed
next
  show "cder \<Gamma> (cimp (cor a' b') (cor a b))"
  proof (rule cder_deduction, rule cor_elim[where a = a' and b = b'])
    show "cder (insert (cor a' b') \<Gamma>) (cor a' b')" by (rule cder.cAx) simp
  next
    have ia: "cder (insert a' (insert (cor a' b') \<Gamma>)) (ciff a a')" by (rule cder_weaken[OF assms(1)]) auto
    have "cder (insert a' (insert (cor a' b') \<Gamma>)) a"
      by (rule ciff_mp2[OF ia]) (rule cder.cAx, simp)
    thus "cder (insert a' (insert (cor a' b') \<Gamma>)) (cor a b)" by (rule cor_intro1)
  next
    have ib: "cder (insert b' (insert (cor a' b') \<Gamma>)) (ciff b b')" by (rule cder_weaken[OF assms(2)]) auto
    have "cder (insert b' (insert (cor a' b') \<Gamma>)) b"
      by (rule ciff_mp2[OF ib]) (rule cder.cAx, simp)
    thus "cder (insert b' (insert (cor a' b') \<Gamma>)) (cor a b)" by (rule cor_intro2)
  qed
qed

lemma clit_cong:
  assumes "cder \<Gamma> (ciff a a')"
  shows "cder \<Gamma> (ciff (clit b a) (clit b a'))"
proof (cases b)
  case True
  thus ?thesis using assms by (simp add: clit_def)
next
  case False
  thus ?thesis using cneg_cong[OF assms] by (simp add: clit_def)
qed


lemma cbig_and_cong:
  assumes "length xs = length ys"
    and "\<And>i. i < length xs \<Longrightarrow> cder \<Gamma> (ciff (xs ! i) (ys ! i))"
  shows "cder \<Gamma> (ciff (cbig_and xs) (cbig_and ys))"
  using assms
proof (induction xs arbitrary: ys)
  case Nil
  thus ?case by (simp add: ciff_refl)
next
  case (Cons x xs)
  then obtain y ys' where ys: "ys = y # ys'" by (cases ys) auto
  have h0: "cder \<Gamma> (ciff x y)" using Cons.prems(2)[of 0] ys by simp
  have tail: "cder \<Gamma> (ciff (cbig_and xs) (cbig_and ys'))"
  proof (rule Cons.IH)
    show "length xs = length ys'" using Cons.prems(1) ys by simp
  next
    fix i assume "i < length xs"
    thus "cder \<Gamma> (ciff (xs ! i) (ys' ! i))" using Cons.prems(2)[of "Suc i"] ys by simp
  qed
  show ?case using cand_cong[OF h0 tail] ys by simp
qed

lemma cbig_or_cong:
  assumes "length xs = length ys"
    and "\<And>i. i < length xs \<Longrightarrow> cder \<Gamma> (ciff (xs ! i) (ys ! i))"
  shows "cder \<Gamma> (ciff (cbig_or xs) (cbig_or ys))"
  using assms
proof (induction xs arbitrary: ys)
  case Nil
  thus ?case by (simp add: ciff_refl)
next
  case (Cons x xs)
  then obtain y ys' where ys: "ys = y # ys'" by (cases ys) auto
  have h0: "cder \<Gamma> (ciff x y)" using Cons.prems(2)[of 0] ys by simp
  have tail: "cder \<Gamma> (ciff (cbig_or xs) (cbig_or ys'))"
  proof (rule Cons.IH)
    show "length xs = length ys'" using Cons.prems(1) ys by simp
  next
    fix i assume "i < length xs"
    thus "cder \<Gamma> (ciff (xs ! i) (ys' ! i))" using Cons.prems(2)[of "Suc i"] ys by simp
  qed
  show ?case using cor_cong[OF h0 tail] ys by simp
qed

lemma cmk_conn_cong:
  assumes "length args = length args'"
    and "\<And>i. i < length args \<Longrightarrow> cder \<Gamma> (ciff (args ! i) (args' ! i))"
  shows "cder \<Gamma> (ciff (cmk_conn g args) (cmk_conn g args'))"
proof -
  let ?n = "length args"
  let ?F = "filter g (List.n_lists ?n [True, False])"
  have body: "cder \<Gamma> (ciff (cbig_and (map (\<lambda>i. clit (v ! i) (args ! i)) [0..<?n]))
                           (cbig_and (map (\<lambda>i. clit (v ! i) (args' ! i)) [0..<?n])))" for v
  proof (rule cbig_and_cong)
    show "length (map (\<lambda>i. clit (v ! i) (args ! i)) [0..<?n])
        = length (map (\<lambda>i. clit (v ! i) (args' ! i)) [0..<?n])" by simp
  next
    fix i assume "i < length (map (\<lambda>i. clit (v ! i) (args ! i)) [0..<?n])"
    hence iln: "i < ?n" by simp
    show "cder \<Gamma> (ciff (map (\<lambda>i. clit (v ! i) (args ! i)) [0..<?n] ! i)
                       (map (\<lambda>i. clit (v ! i) (args' ! i)) [0..<?n] ! i))"
      using clit_cong[OF assms(2)[OF iln]] iln by simp
  qed
  have main: "cder \<Gamma> (ciff (cbig_or (map (\<lambda>v. cbig_and (map (\<lambda>i. clit (v ! i) (args ! i)) [0..<?n])) ?F))
                           (cbig_or (map (\<lambda>v. cbig_and (map (\<lambda>i. clit (v ! i) (args' ! i)) [0..<?n])) ?F)))"
  proof (rule cbig_or_cong)
    show "length (map (\<lambda>v. cbig_and (map (\<lambda>i. clit (v ! i) (args ! i)) [0..<?n])) ?F)
        = length (map (\<lambda>v. cbig_and (map (\<lambda>i. clit (v ! i) (args' ! i)) [0..<?n])) ?F)" by simp
  next
    fix j assume "j < length (map (\<lambda>v. cbig_and (map (\<lambda>i. clit (v ! i) (args ! i)) [0..<?n])) ?F)"
    hence jln: "j < length ?F" by simp
    show "cder \<Gamma> (ciff (map (\<lambda>v. cbig_and (map (\<lambda>i. clit (v ! i) (args ! i)) [0..<?n])) ?F ! j)
                       (map (\<lambda>v. cbig_and (map (\<lambda>i. clit (v ! i) (args' ! i)) [0..<?n])) ?F ! j))"
      using body[of "?F ! j"] jln by simp
  qed
  have eql: "cmk_conn g args
           = cbig_or (map (\<lambda>v. cbig_and (map (\<lambda>i. clit (v ! i) (args ! i)) [0..<?n])) ?F)"
    by (simp add: cmk_conn_def)
  have eqr: "cmk_conn g args'
           = cbig_or (map (\<lambda>v. cbig_and (map (\<lambda>i. clit (v ! i) (args' ! i)) [0..<?n])) ?F)"
    by (simp add: cmk_conn_def assms(1)[symmetric])
  show ?thesis using main unfolding eql eqr .
qed

subsection \<open>Simulating the AFP Hilbert calculus in cder\<close>

lemma bt_AX0: "F \<in> AX0 \<Longrightarrow> bt F \<in> cAX"
  by (induction rule: AX0.induct) (auto intro: cAX.intros)

lemma bt_AX10: "F \<in> AX10 \<Longrightarrow> bt F \<in> cAX"
  by (induction rule: AX10.induct) (auto intro: cAX.intros bt_AX0)

lemma HC_sim:
  assumes "S \<turnstile>\<^sub>H G" and cond: "\<forall>F\<in>S. F \<in> AX10 \<or> bt F \<in> \<Gamma>"
  shows "cder \<Gamma> (bt G)"
  using assms(1)
proof (induction rule: HC.induct)
  case (Ax F)
  from Ax cond have "F \<in> AX10 \<or> bt F \<in> \<Gamma>" by blast
  thus "cder \<Gamma> (bt F)"
  proof
    assume "F \<in> AX10"
    thus ?thesis using bt_AX10 by (auto intro: cder.cAxiom)
  next
    assume "bt F \<in> \<Gamma>"
    thus ?thesis by (rule cder.cAx)
  qed
next
  case (MP F G)
  have 1: "cder \<Gamma> (bt F)" using MP.IH(1) .
  have "cder \<Gamma> (bt (Formulas.Imp F G))" using MP.IH(2) .
  hence 2: "cder \<Gamma> (cimp (bt F) (bt G))" by simp
  show "cder \<Gamma> (bt G)" using cder.cMP[OF 1 2] .
qed


subsection \<open>Round-trip: every well-formed formula is cder-equivalent to its bt-image\<close>

lemma roundtrip:
  "formula_well_formed alph f \<Longrightarrow> cder {} (ciff f (bt (tr alph f)))"
proof (induction f)
  case (Atom a)
  have "cder {} (ciff (Atom a) (Atom a))" by (rule ciff_refl)
  thus ?case by simp
next
  case (Conn c args)
  from Conn.prems have len: "length args = arity alph c"
    and wfa: "\<And>x. x \<in> set args \<Longrightarrow> formula_well_formed alph x" by auto
  let ?G = "conn_evals alph c"
  have def: "cder {} (ciff (Conn c args) (cmk_conn ?G args))"
    by (rule cder.cAxiom[OF cAX.cDef[OF len]])
  have ihs: "\<And>i. i < length args \<Longrightarrow> cder {} (ciff (args ! i) (bt (tr alph (args ! i))))"
  proof -
    fix i assume i: "i < length args"
    hence "args ! i \<in> set args" by simp
    thus "cder {} (ciff (args ! i) (bt (tr alph (args ! i))))"
      using Conn.IH wfa by blast
  qed
  have cong: "cder {} (ciff (cmk_conn ?G args) (cmk_conn ?G (map (\<lambda>x. bt (tr alph x)) args)))"
  proof (rule cmk_conn_cong)
    show "length args = length (map (\<lambda>x. bt (tr alph x)) args)" by simp
  next
    fix i assume "i < length args"
    thus "cder {} (ciff (args ! i) (map (\<lambda>x. bt (tr alph x)) args ! i))"
      using ihs[of i] by simp
  qed
  have comp: "cmk_conn ?G (map (\<lambda>x. bt (tr alph x)) args) = bt (tr alph (Conn c args))"
    by (simp add: bt_mk_conn o_def)
  have "cder {} (ciff (Conn c args) (cmk_conn ?G (map (\<lambda>x. bt (tr alph x)) args)))"
    using ciff_trans[OF def cong] .
  thus ?case using comp by simp
qed

lemma roundtrip_fwd:
  "formula_well_formed alph f \<Longrightarrow> cder {f} (bt (tr alph f))"
proof -
  assume "formula_well_formed alph f"
  hence "cder {} (ciff f (bt (tr alph f)))" by (rule roundtrip)
  hence "cder {f} (ciff f (bt (tr alph f)))" by (rule cder_weaken) auto
  moreover have "cder {f} f" by (rule cder.cAx) simp
  ultimately show "cder {f} (bt (tr alph f))" by (rule ciff_mp1)
qed

lemma roundtrip_bwd:
  "formula_well_formed alph f \<Longrightarrow> cder {bt (tr alph f)} f"
proof -
  assume "formula_well_formed alph f"
  hence "cder {} (ciff f (bt (tr alph f)))" by (rule roundtrip)
  hence "cder {bt (tr alph f)} (ciff f (bt (tr alph f)))" by (rule cder_weaken) auto
  moreover have "cder {bt (tr alph f)} (bt (tr alph f))" by (rule cder.cAx) simp
  ultimately show "cder {bt (tr alph f)} f" by (rule ciff_mp2)
qed


subsection \<open>Cut over all hypotheses and translation into a Frege proof list\<close>

lemma cder_mono_cut:
  assumes cut: "\<And>d. d \<in> \<Delta> \<Longrightarrow> cder \<Gamma> d"
  shows "cder \<Delta> \<phi> \<Longrightarrow> cder \<Gamma> \<phi>"
proof (induction rule: cder.induct)
  case (cAx \<phi>)
  thus ?case by (rule cut)
next
  case (cAxiom \<phi>)
  thus ?case by (rule cder.cAxiom)
next
  case (cMP \<phi> \<psi>)
  thus ?case using cder.cMP by blast
qed

lemma cder_proof_list:
  assumes ax: "\<And>\<psi>. \<psi> \<in> cAX \<Longrightarrow> derived R [] \<psi>"
    and mp: "\<And>a b. derived R [a, cimp a b] b"
  shows "cder \<Gamma> \<phi> \<Longrightarrow>
    \<exists>ss. ss \<noteq> [] \<and> last ss = \<phi> \<and>
         (\<forall>i < length ss. ss ! i \<in> \<Gamma> \<or> derived R (take i ss) (ss ! i))"
proof (induction rule: cder.induct)
  case (cAx \<phi>)
  show ?case by (rule exI[of _ "[\<phi>]"]) (use cAx in auto)
next
  case (cAxiom \<phi>)
  show ?case by (rule exI[of _ "[\<phi>]"]) (use ax[OF cAxiom] in auto)
next
  case (cMP \<phi> \<psi>)
  obtain ss1 where ss1: "ss1 \<noteq> []" "last ss1 = \<phi>"
    "\<forall>i < length ss1. ss1 ! i \<in> \<Gamma> \<or> derived R (take i ss1) (ss1 ! i)"
    using cMP.IH(1) by blast
  obtain ss2 where ss2: "ss2 \<noteq> []" "last ss2 = cimp \<phi> \<psi>"
    "\<forall>i < length ss2. ss2 ! i \<in> \<Gamma> \<or> derived R (take i ss2) (ss2 ! i)"
    using cMP.IH(2) by blast
  let ?ss = "ss1 @ ss2 @ [\<psi>]"
  have valid: "?ss ! i \<in> \<Gamma> \<or> derived R (take i ?ss) (?ss ! i)" if i: "i < length ?ss" for i
  proof -
    consider (A) "i < length ss1"
      | (B) "length ss1 \<le> i \<and> i < length ss1 + length ss2"
      | (C) "i = length ss1 + length ss2"
      using i by force
    thus ?thesis
    proof cases
      case A
      have n1: "?ss ! i = ss1 ! i" using A by (simp add: nth_append)
      have t1: "take i ?ss = take i ss1" using A by simp
      show ?thesis using ss1(3) A n1 t1 by auto
    next
      case B
      hence j: "i - length ss1 < length ss2" by auto
      have n2: "?ss ! i = ss2 ! (i - length ss1)" using B j by (simp add: nth_append)
      have t2: "take i ?ss = ss1 @ take (i - length ss1) ss2"
        using B j by simp
      show ?thesis
      proof (cases "ss2 ! (i - length ss1) \<in> \<Gamma>")
        case True
        thus ?thesis using n2 by simp
      next
        case False
        hence d: "derived R (take (i - length ss1) ss2) (ss2 ! (i - length ss1))"
          using ss2(3) j by blast
        have "set (take (i - length ss1) ss2) \<subseteq> set (take i ?ss)" using t2 by auto
        hence "derived R (take i ?ss) (ss2 ! (i - length ss1))" using derived_mono[OF _ d] by blast
        thus ?thesis using n2 by simp
      qed
    next
      case C
      have n3: "?ss ! i = \<psi>" using C by (simp add: nth_append)
      have t3: "take i ?ss = ss1 @ ss2" using C by simp
      have a1: "\<phi> \<in> set ss1" using ss1(2) last_in_set[OF ss1(1)] by simp
      have a2: "cimp \<phi> \<psi> \<in> set ss2" using ss2(2) last_in_set[OF ss2(1)] by simp
      have "set [\<phi>, cimp \<phi> \<psi>] \<subseteq> set (ss1 @ ss2)" using a1 a2 by auto
      hence "derived R (ss1 @ ss2) \<psi>" using derived_mono[OF _ mp] by blast
      thus ?thesis using n3 t3 by simp
    qed
  qed
  have "?ss \<noteq> [] \<and> last ?ss = \<psi> \<and>
        (\<forall>i < length ?ss. ?ss ! i \<in> \<Gamma> \<or> derived R (take i ?ss) (?ss ! i))"
    using valid by simp
  thus ?case by blast
qed


subsection \<open>Completeness of cder and assembly of a Frege system\<close>

lemma cder_complete:
  assumes wfs: "\<forall>f\<in>fs. formula_well_formed alph f"
    and wth: "formula_well_formed alph th"
    and sem: "\<forall>val. (\<forall>f\<in>fs. eval alph val f) \<longrightarrow> eval alph val th"
  shows "cder fs th"
proof -
  have ent: "entailment (tr alph ` fs) (tr alph th)"
    unfolding entailment_def
  proof (intro allI impI)
    fix A assume "\<forall>H\<in>tr alph ` fs. formula_semantics A H"
    hence "\<forall>f\<in>fs. eval alph A f" by (auto simp: tr_sema)
    hence "eval alph A th" using sem by blast
    thus "formula_semantics A (tr alph th)" by (simp add: tr_sema)
  qed
  obtain \<Delta> where \<Delta>: "finite \<Delta>" "\<Delta> \<subseteq> tr alph ` fs" "AX10 \<union> \<Delta> \<turnstile>\<^sub>H tr alph th"
    using entailment_HC[OF ent] by blast
  have c0: "cder (bt ` \<Delta>) (bt (tr alph th))"
  proof (rule HC_sim[OF \<Delta>(3)])
    show "\<forall>F\<in>AX10 \<union> \<Delta>. F \<in> AX10 \<or> bt F \<in> bt ` \<Delta>" by auto
  qed
  have c1: "cder ((\<lambda>f. bt (tr alph f)) ` fs) (bt (tr alph th))"
  proof (rule cder_weaken[OF c0])
    show "bt ` \<Delta> \<subseteq> (\<lambda>f. bt (tr alph f)) ` fs" using \<Delta>(2) by auto
  qed
  have cut: "cder fs d" if "d \<in> (\<lambda>f. bt (tr alph f)) ` fs" for d
  proof -
    from that obtain f where f: "f \<in> fs" "d = bt (tr alph f)" by auto
    have wff: "formula_well_formed alph f" using wfs f(1) by blast
    have "cder {f} (bt (tr alph f))" by (rule roundtrip_fwd[OF wff])
    hence "cder fs (bt (tr alph f))" by (rule cder_weaken) (use f(1) in auto)
    thus "cder fs d" using f(2) by simp
  qed
  have cfs: "cder fs (bt (tr alph th))" by (rule cder_mono_cut[OF cut c1])
  have "cder {bt (tr alph th)} th" by (rule roundtrip_bwd[OF wth])
  hence "cder (insert (bt (tr alph th)) fs) th" by (rule cder_weaken) auto
  thus "cder fs th" using cder_cut[OF _ cfs] by blast
qed

lemma frege_system_from_rules:
  fixes R :: "'c rule set"
  assumes Rfin: "finite R"
    and Rsound: "\<And>r. r \<in> R \<Longrightarrow> sound_rule \<lparr>rules = R, alphabet = alph\<rparr> r"
    and ax: "\<And>\<psi>. \<psi> \<in> cAX \<Longrightarrow> derived R [] \<psi>"
    and mp: "\<And>a b. derived R [a, cimp a b] b"
  shows "frege_system \<lparr>rules = R, alphabet = alph\<rparr>"
proof -
  let ?F = "\<lparr>rules = R, alphabet = alph\<rparr> :: 'c frege"
  show "frege_system ?F"
  proof (rule frege_system.intro)
  show "\<forall>r\<in>rules ?F. sound_rule ?F r" using Rsound by simp
next
  show "finite (rules ?F)" using Rfin by simp
next
  show "finite (UNIV :: 'c set)" using fin .
next
  show "\<forall>f :: dm_conn formula. \<exists>f' :: 'c formula.
          formula_well_formed (alphabet ?F) f' \<and> formulas_equiv f dm_alphabet f' (alphabet ?F)"
    using func_complete by simp
next
  show "\<exists>t. arity (alphabet ?F) t = 0 \<and> (\<forall>val. eval (alphabet ?F) val (Conn t []) = True)"
    using htop by simp
next
  show "\<exists>b. arity (alphabet ?F) b = 0 \<and> (\<forall>val. eval (alphabet ?F) val (Conn b []) = False)"
    using hbot by simp
next
  show "\<forall>fs th.
          (\<forall>f\<in>fs. formula_well_formed (alphabet ?F) f) \<longrightarrow>
          formula_well_formed (alphabet ?F) th \<longrightarrow>
          (\<forall>val. (\<forall>f\<in>fs. eval (alphabet ?F) val f) \<longrightarrow> eval (alphabet ?F) val th) \<longrightarrow>
          (\<exists>pr. valid_proof ?F pr \<and> assumptions pr = fs \<and> thesis pr = th)"
  proof (intro allI impI)
    fix fs th
    assume wfs: "\<forall>f\<in>fs. formula_well_formed (alphabet ?F) f"
      and wth: "formula_well_formed (alphabet ?F) th"
      and sem: "\<forall>val. (\<forall>f\<in>fs. eval (alphabet ?F) val f) \<longrightarrow> eval (alphabet ?F) val th"
    have "cder fs th"
    proof (rule cder_complete)
      show "\<forall>f\<in>fs. formula_well_formed alph f" using wfs by simp
      show "formula_well_formed alph th" using wth by simp
      show "\<forall>val. (\<forall>f\<in>fs. eval alph val f) \<longrightarrow> eval alph val th" using sem by simp
    qed
    then obtain ss where ss: "ss \<noteq> []" "last ss = th"
      "\<forall>i < length ss. ss ! i \<in> fs \<or> derived R (take i ss) (ss ! i)"
      using cder_proof_list[OF ax mp] by blast
    let ?pr = "\<lparr>assumptions = fs, thesis = th, steps = ss\<rparr> :: 'c frege_proof"
    have "valid_proof ?F ?pr" unfolding valid_proof_def using ss by simp
    moreover have "assumptions ?pr = fs" by simp
    moreover have "thesis ?pr = th" by simp
    ultimately show "\<exists>pr. valid_proof ?F pr \<and> assumptions pr = fs \<and> thesis pr = th" by blast
  qed
  qed
qed

end


subsection \<open>Extracting concrete connectives from functional completeness\<close>

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

text \<open>From a functional-completeness witness for a De Morgan formula whose variables lie
  in @{term V}, prune all other atoms to a fixed @{term \<top>} constant.  The result is a
  template whose variables lie in @{term V} and which evaluates exactly like the De Morgan
  formula.\<close>

lemma conn_template:
  fixes alph :: "'c alphabet" and dmf :: "dm_conn formula" and f' :: "'c formula"
  assumes equiv: "formulas_equiv dmf dm_alphabet f' alph"
    and topT: "\<And>val. eval alph val (Conn topc []) = True"
    and Vsub: "var_set_form dmf \<subseteq> V"
  shows "\<exists>tmpl. var_set_form tmpl \<subseteq> V \<and> (\<forall>val. eval alph val tmpl = eval dm_alphabet val dmf)"
proof -
  let ?p = "\<lambda>s. if s \<in> V then Atom s else Conn topc []"
  let ?tmpl = "sub_formula ?p f'"
  have v: "var_set_form ?tmpl \<subseteq> V"
    unfolding var_set_sub by (auto split: if_splits)
  have e: "eval alph val ?tmpl = eval dm_alphabet val dmf" for val
  proof -
    have "eval alph val ?tmpl = eval alph (\<lambda>s. eval alph val (?p s)) f'"
      by (rule sub_formula_eval)
    also have "\<dots> = eval dm_alphabet (\<lambda>s. eval alph val (?p s)) dmf"
      using equiv unfolding formulas_equiv_def by simp
    also have "\<dots> = eval dm_alphabet val dmf"
    proof (rule eval_cong)
      fix v assume "v \<in> var_set_form dmf"
      hence "v \<in> V" using Vsub by blast
      thus "eval alph val (?p v) = val v" by simp
    qed
    finally show ?thesis .
  qed
  from v e show ?thesis by blast
qed



lemma derived_nil:
  assumes "r \<in> R" and "prems r = []" and "sub_formula sub (concl r) = f"
  shows "derived R [] f"
  unfolding derived_def
proof (intro bexI[OF _ assms(1)] exI[where x = sub])
  show "let sub_r = sub_rule sub r
        in concl sub_r = f \<and> (\<forall>f1\<in>set (prems sub_r). \<exists>f2\<in>set []. f1 = f2)"
    using assms(2,3) by (simp add: Let_def)
qed

lemma derived_concl:
  assumes "\<lparr>prems = [], concl = cc\<rparr> \<in> R"
  shows "derived R [] (sub_formula sub cc)"
  by (rule derived_nil[OF assms]) simp_all

lemma frege_system_over_complete_alphabet:
  fixes alph :: "'c alphabet"
  assumes "finite (UNIV :: 'c set)"
    and "\<forall>f :: dm_conn formula. \<exists> f' :: 'c formula.
            formula_well_formed alph f' \<and> formulas_equiv f dm_alphabet f' alph"
    and "\<exists> t. arity alph t = 0 \<and> (\<forall> val. eval alph val (Conn t []) = True)"
    and "\<exists> b. arity alph b = 0 \<and> (\<forall> val. eval alph val (Conn b []) = False)"
  shows "\<exists> F. frege_system F \<and> alphabet F = alph"
proof -
  from assms(3) obtain topc where topc: "\<And>val. eval alph val (Conn topc []) = True" by blast
  from assms(4) obtain botc where botc: "\<And>val. eval alph val (Conn botc []) = False" by blast

  define two :: "'c formula \<Rightarrow> 'c formula \<Rightarrow> string \<Rightarrow> 'c formula"
    where "two = (\<lambda>a b s. if s = ''0'' then a else if s = ''1'' then b else Atom s)"
  define one :: "'c formula \<Rightarrow> string \<Rightarrow> 'c formula"
    where "one = (\<lambda>a s. if s = ''0'' then a else Atom s)"
  define sub3 :: "'c formula \<Rightarrow> 'c formula \<Rightarrow> 'c formula \<Rightarrow> string \<Rightarrow> 'c formula"
    where "sub3 = (\<lambda>F G H s. if s = ''0'' then F else if s = ''1'' then G
                             else if s = ''2'' then H else Atom s)"

  \<comment> \<open>templates from functional completeness, pruned to their marker variables\<close>
  obtain ta where ta_v: "var_set_form ta \<subseteq> {''0'', ''1''}"
    and ta_e: "\<And>val. eval alph val ta = eval dm_alphabet val (Conn And [Atom ''0'', Atom ''1''])"
  proof -
    obtain fa where "formulas_equiv (Conn And [Atom ''0'', Atom ''1''] :: dm_conn formula) dm_alphabet fa alph"
      using assms(2) by blast
    hence "\<exists>t. var_set_form t \<subseteq> {''0'', ''1''} \<and>
               (\<forall>val. eval alph val t = eval dm_alphabet val (Conn And [Atom ''0'', Atom ''1'']))"
      by (rule conn_template[OF _ topc]) simp
    thus thesis using that by blast
  qed
  obtain to where to_v: "var_set_form to \<subseteq> {''0'', ''1''}"
    and to_e: "\<And>val. eval alph val to = eval dm_alphabet val (Conn Or [Atom ''0'', Atom ''1''])"
  proof -
    obtain fo where "formulas_equiv (Conn Or [Atom ''0'', Atom ''1''] :: dm_conn formula) dm_alphabet fo alph"
      using assms(2) by blast
    hence "\<exists>t. var_set_form t \<subseteq> {''0'', ''1''} \<and>
               (\<forall>val. eval alph val t = eval dm_alphabet val (Conn Or [Atom ''0'', Atom ''1'']))"
      by (rule conn_template[OF _ topc]) simp
    thus thesis using that by blast
  qed
  obtain ti where ti_v: "var_set_form ti \<subseteq> {''0'', ''1''}"
    and ti_e: "\<And>val. eval alph val ti = eval dm_alphabet val (Conn Or [Conn Not [Atom ''0''], Atom ''1''])"
  proof -
    obtain fi where "formulas_equiv (Conn Or [Conn Not [Atom ''0''], Atom ''1''] :: dm_conn formula) dm_alphabet fi alph"
      using assms(2) by blast
    hence "\<exists>t. var_set_form t \<subseteq> {''0'', ''1''} \<and>
               (\<forall>val. eval alph val t = eval dm_alphabet val (Conn Or [Conn Not [Atom ''0''], Atom ''1'']))"
      by (rule conn_template[OF _ topc]) simp
    thus thesis using that by blast
  qed
  obtain tn where tn_v: "var_set_form tn \<subseteq> {''0''}"
    and tn_e: "\<And>val. eval alph val tn = eval dm_alphabet val (Conn Not [Atom ''0''])"
  proof -
    obtain fn where "formulas_equiv (Conn Not [Atom ''0''] :: dm_conn formula) dm_alphabet fn alph"
      using assms(2) by blast
    hence "\<exists>t. var_set_form t \<subseteq> {''0''} \<and>
               (\<forall>val. eval alph val t = eval dm_alphabet val (Conn Not [Atom ''0'']))"
      by (rule conn_template[OF _ topc]) simp
    thus thesis using that by blast
  qed

  define cand :: "'c formula \<Rightarrow> 'c formula \<Rightarrow> 'c formula"
    where "cand = (\<lambda>a b. sub_formula (two a b) ta)"
  define cor :: "'c formula \<Rightarrow> 'c formula \<Rightarrow> 'c formula"
    where "cor = (\<lambda>a b. sub_formula (two a b) to)"
  define cimp :: "'c formula \<Rightarrow> 'c formula \<Rightarrow> 'c formula"
    where "cimp = (\<lambda>a b. sub_formula (two a b) ti)"
  define cneg :: "'c formula \<Rightarrow> 'c formula"
    where "cneg = (\<lambda>a. sub_formula (one a) tn)"
  define cfls :: "'c formula"
    where "cfls = Conn botc []"

  \<comment> \<open>evaluation correctness\<close>
  have cand_eval: "eval alph val (cand a b) = (eval alph val a \<and> eval alph val b)" for val a b
  proof -
    have "eval alph val (cand a b) = eval alph (\<lambda>s. eval alph val (two a b s)) ta"
      unfolding cand_def by (simp add: sub_formula_eval)
    also have "\<dots> = eval dm_alphabet (\<lambda>s. eval alph val (two a b s)) (Conn And [Atom ''0'', Atom ''1''])"
      by (rule ta_e)
    also have "\<dots> = (eval alph val a \<and> eval alph val b)" by (simp add: dm_alphabet_def two_def)
    finally show ?thesis .
  qed
  have cor_eval: "eval alph val (cor a b) = (eval alph val a \<or> eval alph val b)" for val a b
  proof -
    have "eval alph val (cor a b) = eval alph (\<lambda>s. eval alph val (two a b s)) to"
      unfolding cor_def by (simp add: sub_formula_eval)
    also have "\<dots> = eval dm_alphabet (\<lambda>s. eval alph val (two a b s)) (Conn Or [Atom ''0'', Atom ''1''])"
      by (rule to_e)
    also have "\<dots> = (eval alph val a \<or> eval alph val b)" by (simp add: dm_alphabet_def two_def)
    finally show ?thesis .
  qed
  have cimp_eval: "eval alph val (cimp a b) = (eval alph val a \<longrightarrow> eval alph val b)" for val a b
  proof -
    have "eval alph val (cimp a b) = eval alph (\<lambda>s. eval alph val (two a b s)) ti"
      unfolding cimp_def by (simp add: sub_formula_eval)
    also have "\<dots> = eval dm_alphabet (\<lambda>s. eval alph val (two a b s)) (Conn Or [Conn Not [Atom ''0''], Atom ''1''])"
      by (rule ti_e)
    also have "\<dots> = (eval alph val a \<longrightarrow> eval alph val b)" by (simp add: dm_alphabet_def two_def)
    finally show ?thesis .
  qed
  have cneg_eval: "eval alph val (cneg a) = (\<not> eval alph val a)" for val a
  proof -
    have "eval alph val (cneg a) = eval alph (\<lambda>s. eval alph val (one a s)) tn"
      unfolding cneg_def by (simp add: sub_formula_eval)
    also have "\<dots> = eval dm_alphabet (\<lambda>s. eval alph val (one a s)) (Conn Not [Atom ''0''])"
      by (rule tn_e)
    also have "\<dots> = (\<not> eval alph val a)" by (simp add: dm_alphabet_def one_def)
    finally show ?thesis .
  qed
  have cfls_eval: "eval alph val cfls = False" for val
    unfolding cfls_def by (rule botc)

  \<comment> \<open>substitution commutes with each connective (markers lie in the template variables)\<close>
  have cand_sub: "sub_formula sub (cand a b) = cand (sub_formula sub a) (sub_formula sub b)" for sub a b
  proof -
    have "sub_formula sub (cand a b) = sub_formula (\<lambda>s. sub_formula sub (two a b s)) ta"
      unfolding cand_def by (simp add: sub_formula_compose)
    also have "\<dots> = sub_formula (two (sub_formula sub a) (sub_formula sub b)) ta"
    proof (rule sub_formula_cong)
      fix v assume "v \<in> var_set_form ta"
      hence "v = ''0'' \<or> v = ''1''" using ta_v by auto
      thus "sub_formula sub (two a b v) = two (sub_formula sub a) (sub_formula sub b) v"
        by (auto simp: two_def)
    qed
    also have "\<dots> = cand (sub_formula sub a) (sub_formula sub b)" unfolding cand_def ..
    finally show ?thesis .
  qed
  have cor_sub: "sub_formula sub (cor a b) = cor (sub_formula sub a) (sub_formula sub b)" for sub a b
  proof -
    have "sub_formula sub (cor a b) = sub_formula (\<lambda>s. sub_formula sub (two a b s)) to"
      unfolding cor_def by (simp add: sub_formula_compose)
    also have "\<dots> = sub_formula (two (sub_formula sub a) (sub_formula sub b)) to"
    proof (rule sub_formula_cong)
      fix v assume "v \<in> var_set_form to"
      hence "v = ''0'' \<or> v = ''1''" using to_v by auto
      thus "sub_formula sub (two a b v) = two (sub_formula sub a) (sub_formula sub b) v"
        by (auto simp: two_def)
    qed
    also have "\<dots> = cor (sub_formula sub a) (sub_formula sub b)" unfolding cor_def ..
    finally show ?thesis .
  qed
  have cimp_sub: "sub_formula sub (cimp a b) = cimp (sub_formula sub a) (sub_formula sub b)" for sub a b
  proof -
    have "sub_formula sub (cimp a b) = sub_formula (\<lambda>s. sub_formula sub (two a b s)) ti"
      unfolding cimp_def by (simp add: sub_formula_compose)
    also have "\<dots> = sub_formula (two (sub_formula sub a) (sub_formula sub b)) ti"
    proof (rule sub_formula_cong)
      fix v assume "v \<in> var_set_form ti"
      hence "v = ''0'' \<or> v = ''1''" using ti_v by auto
      thus "sub_formula sub (two a b v) = two (sub_formula sub a) (sub_formula sub b) v"
        by (auto simp: two_def)
    qed
    also have "\<dots> = cimp (sub_formula sub a) (sub_formula sub b)" unfolding cimp_def ..
    finally show ?thesis .
  qed
  have cneg_sub: "sub_formula sub (cneg a) = cneg (sub_formula sub a)" for sub a
  proof -
    have "sub_formula sub (cneg a) = sub_formula (\<lambda>s. sub_formula sub (one a s)) tn"
      unfolding cneg_def by (simp add: sub_formula_compose)
    also have "\<dots> = sub_formula (one (sub_formula sub a)) tn"
    proof (rule sub_formula_cong)
      fix v assume "v \<in> var_set_form tn"
      hence "v = ''0''" using tn_v by auto
      thus "sub_formula sub (one a v) = one (sub_formula sub a) v" by (auto simp: one_def)
    qed
    also have "\<dots> = cneg (sub_formula sub a)" unfolding cneg_def ..
    finally show ?thesis .
  qed
  have cfls_sub: "sub_formula sub cfls = cfls" for sub
    unfolding cfls_def by simp

  interpret FC: fc_alph alph cimp cand cor cneg cfls
    by unfold_locales
       (rule assms(1) cimp_eval cand_eval cor_eval cneg_eval cfls_eval assms(2) assms(3) assms(4))+

  \<comment> \<open>marker atoms for the connective-definition rules\<close>
  define mrk :: "nat \<Rightarrow> string" where "mrk i = replicate (Suc i) (CHR ''m'')" for i
  have mrk_inj: "inj mrk"
  proof (rule injI)
    fix i j assume "mrk i = mrk j"
    hence "length (mrk i) = length (mrk j)" by simp
    thus "i = j" by (simp add: mrk_def)
  qed
  define subc :: "'c formula list \<Rightarrow> string \<Rightarrow> 'c formula"
    where "subc = (\<lambda>xs s. if s \<in> mrk ` {0..<length xs} then xs ! (the_inv mrk s) else Atom s)"
  have subc_mrk: "subc xs (mrk i) = xs ! i" if "i < length xs" for i xs
    using that by (simp add: subc_def the_inv_f_f[OF mrk_inj] inj_image_mem_iff[OF mrk_inj])
  have mrec: "map (sub_formula (subc xs) \<circ> (\<lambda>i. Atom (mrk i))) [0..<length xs] = xs" for xs
  proof (rule nth_equalityI)
    show "length (map (sub_formula (subc xs) \<circ> (\<lambda>i. Atom (mrk i))) [0..<length xs]) = length xs"
      by simp
  next
    fix i assume "i < length (map (sub_formula (subc xs) \<circ> (\<lambda>i. Atom (mrk i))) [0..<length xs])"
    hence "i < length xs" by simp
    thus "map (sub_formula (subc xs) \<circ> (\<lambda>i. Atom (mrk i))) [0..<length xs] ! i = xs ! i"
      by (simp add: subc_mrk)
  qed
  have conn_recon: "sub_formula (subc xs) (Conn c (map (\<lambda>i. Atom (mrk i)) [0..<length xs])) = Conn c xs"
    for c xs by (simp add: mrec)
  have cmk_recon: "sub_formula (subc xs) (FC.cmk_conn g (map (\<lambda>i. Atom (mrk i)) [0..<length xs])) = FC.cmk_conn g xs"
    for g xs
  proof -
    have "sub_formula (subc xs) (FC.cmk_conn g (map (\<lambda>i. Atom (mrk i)) [0..<length xs]))
        = FC.cmk_conn g (map (sub_formula (subc xs)) (map (\<lambda>i. Atom (mrk i)) [0..<length xs]))"
      by (rule FC.cmk_conn_sub[OF cand_sub cor_sub cneg_sub cfls_sub])
    also have "\<dots> = FC.cmk_conn g xs" by (simp add: mrec)
    finally show ?thesis .
  qed

  \<comment> \<open>the finite, sound, realizing rule set\<close>
  define cdef_rule :: "'c \<Rightarrow> 'c rule"
    where "cdef_rule c = \<lparr>prems = [],
       concl = FC.ciff (Conn c (map (\<lambda>i. Atom (mrk i)) [0..<arity alph c]))
                       (FC.cmk_conn (conn_evals alph c) (map (\<lambda>i. Atom (mrk i)) [0..<arity alph c]))\<rparr>" for c
  define mp_rule :: "'c rule"
    where "mp_rule = \<lparr>prems = [Atom ''0'', cimp (Atom ''0'') (Atom ''1'')], concl = Atom ''1''\<rparr>"
  define proprules :: "'c rule set"
    where "proprules = {
       \<lparr>prems = [], concl = cimp (Atom ''0'') (cimp (Atom ''1'') (Atom ''0''))\<rparr>,
       \<lparr>prems = [], concl = cimp (cimp (Atom ''0'') (cimp (Atom ''1'') (Atom ''2'')))
                                  (cimp (cimp (Atom ''0'') (Atom ''1'')) (cimp (Atom ''0'') (Atom ''2'')))\<rparr>,
       \<lparr>prems = [], concl = cimp (Atom ''0'') (cor (Atom ''0'') (Atom ''1''))\<rparr>,
       \<lparr>prems = [], concl = cimp (Atom ''0'') (cor (Atom ''1'') (Atom ''0''))\<rparr>,
       \<lparr>prems = [], concl = cimp (cimp (Atom ''0'') (Atom ''1''))
                                  (cimp (cimp (Atom ''2'') (Atom ''1'')) (cimp (cor (Atom ''0'') (Atom ''2'')) (Atom ''1'')))\<rparr>,
       \<lparr>prems = [], concl = cimp (cand (Atom ''0'') (Atom ''1'')) (Atom ''0'')\<rparr>,
       \<lparr>prems = [], concl = cimp (cand (Atom ''0'') (Atom ''1'')) (Atom ''1'')\<rparr>,
       \<lparr>prems = [], concl = cimp (Atom ''0'') (cimp (Atom ''1'') (cand (Atom ''0'') (Atom ''1'')))\<rparr>,
       \<lparr>prems = [], concl = cimp (cimp (Atom ''0'') cfls) (cneg (Atom ''0''))\<rparr>,
       \<lparr>prems = [], concl = cimp (cneg (Atom ''0'')) (cimp (Atom ''0'') cfls)\<rparr>,
       \<lparr>prems = [], concl = cimp (cimp (cneg (Atom ''0'')) cfls) (Atom ''0'')\<rparr>
    }"
  define R :: "'c rule set" where "R = insert mp_rule (proprules \<union> cdef_rule ` UNIV)"

  have Rfin: "finite R"
    using assms(1) by (simp add: R_def proprules_def)

  have ax: "derived R [] \<psi>" if "\<psi> \<in> FC.cAX" for \<psi>
    using that
  proof (induction rule: FC.cAX.induct)
    case (cK F G)
    have "derived R [] (sub_formula (two F G) (cimp (Atom ''0'') (cimp (Atom ''1'') (Atom ''0''))))"
      by (rule derived_concl) (simp add: R_def proprules_def)
    thus ?case by (simp add: cimp_sub two_def)
  next
    case (cS F G H)
    have "derived R [] (sub_formula (sub3 F G H)
            (cimp (cimp (Atom ''0'') (cimp (Atom ''1'') (Atom ''2'')))
                  (cimp (cimp (Atom ''0'') (Atom ''1'')) (cimp (Atom ''0'') (Atom ''2'')))))"
      by (rule derived_concl) (simp add: R_def proprules_def)
    thus ?case by (simp add: cimp_sub sub3_def)
  next
    case (cOrI1 F G)
    have "derived R [] (sub_formula (two F G) (cimp (Atom ''0'') (cor (Atom ''0'') (Atom ''1''))))"
      by (rule derived_concl) (simp add: R_def proprules_def)
    thus ?case by (simp add: cimp_sub cor_sub two_def)
  next
    case (cOrI2 F G)
    have "derived R [] (sub_formula (two F G) (cimp (Atom ''0'') (cor (Atom ''1'') (Atom ''0''))))"
      by (rule derived_concl) (simp add: R_def proprules_def)
    thus ?case by (simp add: cimp_sub cor_sub two_def)
  next
    case (cOrE F G H)
    have "derived R [] (sub_formula (sub3 F G H)
            (cimp (cimp (Atom ''0'') (Atom ''1''))
                  (cimp (cimp (Atom ''2'') (Atom ''1'')) (cimp (cor (Atom ''0'') (Atom ''2'')) (Atom ''1'')))))"
      by (rule derived_concl) (simp add: R_def proprules_def)
    thus ?case by (simp add: cimp_sub cor_sub sub3_def)
  next
    case (cAndE1 F G)
    have "derived R [] (sub_formula (two F G) (cimp (cand (Atom ''0'') (Atom ''1'')) (Atom ''0'')))"
      by (rule derived_concl) (simp add: R_def proprules_def)
    thus ?case by (simp add: cimp_sub cand_sub two_def)
  next
    case (cAndE2 F G)
    have "derived R [] (sub_formula (two F G) (cimp (cand (Atom ''0'') (Atom ''1'')) (Atom ''1'')))"
      by (rule derived_concl) (simp add: R_def proprules_def)
    thus ?case by (simp add: cimp_sub cand_sub two_def)
  next
    case (cAndI F G)
    have "derived R [] (sub_formula (two F G) (cimp (Atom ''0'') (cimp (Atom ''1'') (cand (Atom ''0'') (Atom ''1'')))))"
      by (rule derived_concl) (simp add: R_def proprules_def)
    thus ?case by (simp add: cimp_sub cand_sub two_def)
  next
    case (cNotI F)
    have "derived R [] (sub_formula (two F F) (cimp (cimp (Atom ''0'') cfls) (cneg (Atom ''0''))))"
      by (rule derived_concl) (simp add: R_def proprules_def)
    thus ?case by (simp add: cimp_sub cneg_sub cfls_sub two_def)
  next
    case (cNotE F)
    have "derived R [] (sub_formula (two F F) (cimp (cneg (Atom ''0'')) (cimp (Atom ''0'') cfls)))"
      by (rule derived_concl) (simp add: R_def proprules_def)
    thus ?case by (simp add: cimp_sub cneg_sub cfls_sub two_def)
  next
    case (cRAA F)
    have "derived R [] (sub_formula (two F F) (cimp (cimp (cneg (Atom ''0'')) cfls) (Atom ''0'')))"
      by (rule derived_concl) (simp add: R_def proprules_def)
    thus ?case by (simp add: cimp_sub cneg_sub cfls_sub two_def)
  next
    case (cDef xs c)
    show ?case
    proof (rule derived_nil[where sub = "subc xs" and r = "cdef_rule c"])
      show "cdef_rule c \<in> R" by (auto simp: R_def)
      show "prems (cdef_rule c) = []" by (simp add: cdef_rule_def)
      show "sub_formula (subc xs) (concl (cdef_rule c))
          = FC.ciff (Conn c xs) (FC.cmk_conn (conn_evals alph c) xs)"
        unfolding cdef_rule_def cDef[symmetric]
        by (simp add: FC.ciff_sub[OF cimp_sub cand_sub] cmk_recon mrec)
    qed
  qed

  have mp: "derived R [a, cimp a b] b" for a b
    unfolding derived_def
  proof (intro bexI[where x = mp_rule] exI[where x = "two a b"])
    show "let sub_r = sub_rule (two a b) mp_rule
          in concl sub_r = b \<and> (\<forall>f1\<in>set (prems sub_r). \<exists>f2\<in>set [a, cimp a b]. f1 = f2)"
      by (auto simp: mp_rule_def Let_def cimp_sub two_def)
    show "mp_rule \<in> R" by (simp add: R_def)
  qed

  have Rsound: "sound_rule \<lparr>rules = R, alphabet = alph\<rparr> r" if rR: "r \<in> R" for r
  proof -
    consider "r = mp_rule" | "r \<in> proprules" | "r \<in> cdef_rule ` UNIV"
      using rR by (auto simp: R_def)
    thus ?thesis
    proof cases
      case 1
      show ?thesis unfolding 1 sound_rule_def mp_rule_def by (auto simp: cimp_eval)
    next
      case 2
      hence cc: "concl r \<in> FC.cAX" and pp: "prems r = []"
        by (auto simp: proprules_def intro: FC.cAX.intros)
      show ?thesis unfolding sound_rule_def by (simp add: pp FC.cAX_tautology[OF cc])
    next
      case 3
      then obtain c where rc: "r = cdef_rule c" by auto
      have cc: "concl r \<in> FC.cAX"
        unfolding rc cdef_rule_def by (auto intro!: FC.cAX.cDef)
      have pp: "prems r = []" unfolding rc cdef_rule_def by simp
      show ?thesis unfolding sound_rule_def by (simp add: pp FC.cAX_tautology[OF cc])
    qed
  qed

  have fs: "frege_system \<lparr>rules = R, alphabet = alph\<rparr>"
    by (rule FC.frege_system_from_rules[OF Rfin Rsound ax mp])
  have "frege_system \<lparr>rules = R, alphabet = alph\<rparr>
        \<and> alphabet (\<lparr>rules = R, alphabet = alph\<rparr> :: 'c frege) = alph"
    using fs by simp
  thus ?thesis by (rule exI)
qed

end
