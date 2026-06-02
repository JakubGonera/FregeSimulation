theory Section6
  imports Section5
begin

(* as in a closure of all connectives *)
definition conn_closed :: "'c alphabet \<Rightarrow> bool" where
  "conn_closed alph \<longleftrightarrow>
    (\<forall>c i b. arity alph c = 0 \<or> (i < arity alph c \<longrightarrow>
       (\<exists>c'. arity alph c' = arity alph c - 1 \<and>
             (\<forall>args. length args = arity alph c - 1 \<longrightarrow>
                conn_evals alph c' args
                  = conn_evals alph c (take i args @ b # drop i args)))))"

locale frege_closure = frege_balancing +
  assumes conn_closed_alphabet: "conn_closed (alphabet F)"
begin

lemma transform_commutes:
  shows "\<exists> (bnd :: nat poly) (c :: real).
           \<forall> conn ps. (\<forall>p \<in> set ps. formula_well_formed (alphabet F) p) \<and> 
                      length ps = arity (alphabet F) conn \<longrightarrow>
             (\<exists> lines sz dep.
                provable_balanced_iff (spira_trans (Conn conn ps)) (Conn conn (map spira_trans ps)) lines sz dep
              \<and> lines \<le> poly bnd (len_formula (Conn conn ps))
              \<and> sz \<le> poly bnd (len_formula (Conn conn ps))
              \<and> real dep \<le> c * log 2 (real (len_formula (Conn conn ps)) + 1))"
  sorry

end
end