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

(* iff_dm A B \<equiv> (A \<and> B) \<or> (\<not>A \<and> \<not>B) *)
definition iff_dm :: "dm_conn formula \<Rightarrow> dm_conn formula \<Rightarrow> dm_conn formula" where
  "iff_dm A B = Conn Or [Conn And [A, B], Conn And [Conn Not [A], Conn Not [B]]]"

definition conn_iff :: "'c formula \<Rightarrow> 'c formula \<Rightarrow> 'c formula" where
  "conn_iff = (SOME f. \<forall> A B A' B'.
    formulas_equiv A (alphabet F) A' dm_alphabet \<and>
    formulas_equiv B (alphabet F) B' dm_alphabet \<and>
    formulas_equiv (f A B) (alphabet F) (iff_dm A' B') dm_alphabet)"

lemma conn_iff_spec:
  shows "\<exists> f. \<forall> A B A' B'.
    formulas_equiv A (alphabet F) A' dm_alphabet \<and>
    formulas_equiv B (alphabet F) B' dm_alphabet \<and>
    formulas_equiv (f A B) (alphabet F) (iff_dm A' B') dm_alphabet"
  sorry

(* lemma 3.1 already proven in Frege.thy *)

(* lemma 3.2: *)
lemma chi_preserves_bideducible:
  shows "\<exists> bound :: nat poly.
           \<forall> \<phi> \<psi> \<chi> h n.
             bideducible F \<phi> \<psi> n
             \<longrightarrow> bideducible F (plug h \<phi> \<chi>) (plug h \<psi> \<chi>)
                   (poly bound (n + len_formula \<chi>))"
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
