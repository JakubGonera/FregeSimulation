theory Translation
  imports Frege "HOL.Transcendental"
begin

(* The numbering of lemmas follows Yuval Filmus' manuscript *)

definition plug :: "string \<Rightarrow> 'c formula \<Rightarrow> 'c formula \<Rightarrow> 'c formula" where
  "plug h \<tau> \<chi> = sub_formula (\<lambda>v. if v = h then \<tau> else Atom v) \<chi>"

definition deducible :: "'c frege \<Rightarrow> ('c formula) set \<Rightarrow> 'c formula \<Rightarrow> nat \<Rightarrow> bool" where
  "deducible F asms c n \<longleftrightarrow>
     (\<exists> p. valid_proof F p \<and> assumptions p \<subseteq> asms \<and> thesis p = c \<and> len_proof p \<le> n)"

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

lemma iff_congruent_base:
  fixes c  :: 'c
    and fs :: "'c formula list"
  shows "\<forall> \<phi> \<psi>. \<forall> i < length fs.
          let sub  = \<lambda>v. if v = ''a'' then \<phi> else if v = ''b'' then \<psi> else Atom v;
              sub' = \<lambda>v. if v = ''a'' then Conn c (fs[i := \<phi>])
                         else if v = ''b'' then Conn c (fs[i := \<psi>])
                         else Atom v
          in \<exists> pr. valid_proof F pr \<and>
                   assumptions pr = {sub_formula sub conn_iff} \<and>
                   thesis pr = sub_formula sub' conn_iff"
  sorry

(* lemma 3.2: *)
lemma iff_congruent:
  shows "\<exists> bound :: nat poly. \<forall> \<phi> \<psi> \<chi> h.
           let sub  = \<lambda>v. if v = ''a'' then \<phi> else if v = ''b'' then \<psi> else Atom v;
               sub' = \<lambda>v. if v = ''a'' then plug h \<phi> \<chi>
                         else if v = ''b'' then plug h \<psi> \<chi> else Atom v;
               s1 = max (len_formula \<phi>) (len_formula \<psi>) ;
               s2 = len_formula \<chi>
           in distinguished \<chi> h \<longrightarrow>
           (\<exists> pr. valid_proof F pr \<and> 
              assumptions pr = {sub_formula sub conn_iff} \<and> 
              thesis pr = (sub_formula sub' conn_iff) \<and>
              length (steps pr) \<le> poly bound s2 \<and>
              (\<forall> step \<in> set (steps pr). len_formula step \<le> poly bound (s1 + s2)))"
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
