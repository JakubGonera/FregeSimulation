theory Translation
  imports Frege "HOL.Transcendental"
begin

(* The numbering of lemmas follows Yuval Filmus' manuscript *)

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

lemma fresh_distinct_atoms_exist:
  "\<exists>vs :: string list.
       length vs = n \<and> distinct vs \<and> ''a'' \<notin> set vs \<and> ''b'' \<notin> set vs"
proof (induction n)
  case 0
  show ?case by (rule exI[where x="[]"]) simp
next
  case (Suc n)
  obtain vs :: "string list" where
    vs_props: "length vs = n" "distinct vs"
              "''a'' \<notin> set vs" "''b'' \<notin> set vs"
    using Suc.IH by blast
  have inf_strings: "infinite (UNIV :: string set)"
    by (simp add: infinite_UNIV_listI)
  have finite_avoid: "finite (set vs \<union> {''a'', ''b''})"
    using vs_props by simp
  obtain x :: string where x_fresh: "x \<notin> set vs \<union> {''a'', ''b''}"
    using inf_strings finite_avoid
    by (meson ex_new_if_finite finite.emptyI finite.insertI finite_UnI finite_set)
  let ?vs' = "x # vs"
  have "length ?vs' = Suc n" using vs_props by simp
  moreover have "distinct ?vs'" using vs_props x_fresh by auto
  moreover have "''a'' \<notin> set ?vs'" using vs_props x_fresh by auto
  moreover have "''b'' \<notin> set ?vs'" using vs_props x_fresh by auto
  ultimately show ?case by blast
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

fun distinguished :: "'c formula \<Rightarrow> string \<Rightarrow> bool" where
  "distinguished (Atom _) _ = True" |
  "distinguished (Conn _ fs) h =
     ((\<exists> f \<in> set fs. contains_atom f h) \<longrightarrow>
        (\<exists>! i. i < length fs \<and> contains_atom (fs ! i) h)
      \<and> (\<forall> f \<in> set fs. distinguished f h))"

(*
  We prove the existence of a fixed proof for congruence of each connective,
  but to be able to say that this contributes only a constant factor we
  designate a "canonical" instantiation of a connective and variables as children
*)
definition canonical_atoms :: "'c \<Rightarrow> string list" where
  "canonical_atoms c = (SOME vs.
       length vs = arity (alphabet F) c
     \<and> distinct vs
     \<and> ''a'' \<notin> set vs
     \<and> ''b'' \<notin> set vs)"

definition canonical_conn :: "'c \<Rightarrow> 'c formula" where
  "canonical_conn c = Conn c (map Atom (canonical_atoms c))"

lemma canonical_atoms_spec:
  shows "length (canonical_atoms c) = arity (alphabet F) c \<and>
         distinct (canonical_atoms c) \<and>
         ''a'' \<notin> set (canonical_atoms c) \<and>
         ''b'' \<notin> set (canonical_atoms c)"
proof -
  have ex: "\<exists>vs :: string list.
              length vs = arity (alphabet F) c \<and> distinct vs
            \<and> ''a'' \<notin> set vs \<and> ''b'' \<notin> set vs"
    using fresh_distinct_atoms_exist by blast
  show ?thesis
    unfolding canonical_atoms_def using someI_ex[OF ex] .
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
           in distinguished \<chi> h \<longrightarrow>
           (\<exists> pr. valid_proof F pr \<and> 
              assumptions pr = {sub_formula sub conn_iff} \<and> 
              thesis pr = (sub_formula sub' conn_iff) \<and>
              length (steps pr) \<le> poly bound s2 \<and>
              (\<forall> step \<in> set (steps pr). len_formula step \<le> poly bound (s1 + s2) \<and>
                                        depth_formula step \<le> d1 + d2 + c))"
  sorry

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
