theory Section6
  imports Section5
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
  using iff_from_taut[OF reduce_taut[OF assms]]
  unfolding reduce_lines_def reduce_step_len_def reduce_step_depth_def .

definition reduce_sub where
  "reduce_sub c qs =
     (\<lambda>v. case map_of (zip (reduce_atoms c) qs) v of None \<Rightarrow> Atom v | Some f \<Rightarrow> f)"

lemma reduce_subst:
  assumes ar: "arity (alphabet F) c \<ge> 1"
      and len_qs: "length qs = arity (alphabet F) c - 1"
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
  note subst_pbi =
    provable_balanced_iff_subst[OF reduce_proof[where b = b, OF ar] finVS sig_id sig_conn]
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
  using iff_from_taut[OF shc_taut[OF assms]]
  unfolding shc_lines_def shc_step_len_def shc_step_depth_def .

definition shc_sub where
  "shc_sub d gs Z =
     (\<lambda>v. case map_of (zip (shc_atoms d) (gs @ [Z])) v of None \<Rightarrow> Atom v | Some f \<Rightarrow> f)"

lemma shc_subst:
  assumes ar: "i < arity (alphabet F) d"
      and len_gs: "length gs = arity (alphabet F) d"
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
    unfolding shc_slots_def by (simp add: nth_take)
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
  note subst_pbi =
    provable_balanced_iff_subst[OF shc_proof[OF ar] finVS sig_id sig_conn]
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
          have pbi: "provable_balanced_iff (spira_trans ?N1)
                  (Conn (conn_fix c 0 b) (map spira_trans qs))
                  (reduce_lines c b)
                  (reduce_step_len c b * len_sub (set (reduce_atoms c)) (reduce_sub c qs))
                  (reduce_step_depth c b + depth_sub (set (reduce_atoms c)) (reduce_sub c qs))"
            unfolding idN1 idqs using reduce_subst[OF ar lenqs] .
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
          note PB = balance_cong[OF PT PF iff_refl[of "spira_trans (qs ! j)"]]
          note PB' = PB[folded rebeq]
          have gbar_len_c: "length ?gbar = arity (alphabet F) (conn_fix c 0 b)"
            using gbar_len cf_ar by simp
          note shc = shc_subst[OF jc gbar_len_c, where Z = "spira_trans (qs ! j)"]
          have gupd: "?gbar[j := spira_trans (qs ! j)] = ?gbar" using gbar_j[symmetric] by simp
          note shc' = shc[unfolded gupd]
          note comp = iff_trans[OF iff_trans[OF P0 PB'] shc']
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
          have dmax6: "real (max (depth_formula (spira_trans (Conn c (?cb # qs[j := true_const]))))
                  (max (depth_formula (Conn (conn_fix c 0 b) (?gbar[j := true_const])))
                  (max (depth_formula (spira_trans (Conn c (?cb # qs[j := false_const]))))
                  (max (depth_formula (Conn (conn_fix c 0 b) (?gbar[j := false_const])))
                  (max (depth_formula (spira_trans (qs ! j)))
                       (depth_formula (spira_trans (qs ! j))))))))
                \<le> ?LGN + 2"
            using dA3 dB1 dA4 dB2 dZ by (simp add: of_nat_max)
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
                       (depth_formula (spira_trans (qs ! j))))))))" by simp
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
    have redT: "provable_balanced_iff (Conn c (true_const # gbar))
        (Conn (conn_fix c 0 True) gbar) (reduce_lines c True)
        (reduce_step_len c True * len_sub (set (reduce_atoms c)) (reduce_sub c gbar))
        (reduce_step_depth c True + depth_sub (set (reduce_atoms c)) (reduce_sub c gbar))"
      using reduce_subst[where b = True, OF ar len] by simp
    have redF: "provable_balanced_iff (Conn c (false_const # gbar))
        (Conn (conn_fix c 0 False) gbar) (reduce_lines c False)
        (reduce_step_len c False * len_sub (set (reduce_atoms c)) (reduce_sub c gbar))
        (reduce_step_depth c False + depth_sub (set (reduce_atoms c)) (reduce_sub c gbar))"
      using reduce_subst[where b = False, OF ar len] by simp
    note rT = iff_sym[OF redT]
    note rF = iff_sym[OF redF]
    note PB2 = balance_cong[OF rT rF iff_refl[of z]]
    have shc': "provable_balanced_iff
        (balance (Conn c (true_const # gbar)) (Conn c (false_const # gbar)) z)
        (Conn c (z # gbar)) (shc_lines c 0)
        (shc_step_len c 0 * len_sub (set (shc_atoms c)) (shc_sub c (z # gbar) z))
        (shc_step_depth c 0 + depth_sub (set (shc_atoms c)) (shc_sub c (z # gbar) z))"
      using shc_subst[where d = c and i = 0 and gs = "z # gbar" and Z = z] ar0 lenz by simp
    note COL = iff_trans[OF PB2 shc']
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
          using iff_refl[of "Conn conn []"] id0 pnil by simp
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
        have "1 \<le> arity (alphabet F) conn \<and> length (map spira_trans rest) = arity (alphabet F) conn - 1"
          using ar lenrest by simp
        from coll[rule_format, OF this, of "spira_trans Q1"] show thesis
          using that by blast
      qed
      note PB = balance_cong[OF AT AF iff_refl[of "spira_trans Q1"]]
      note PB' = PB[folded rebeq]
      note final = iff_trans[OF iff_trans[OF P0 PB'] COL]
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
          by simp
        also have "\<dots> \<le> (real balance_cong_step_depth + 1) + tcm * log 2 (real ?N + 1)"
          using m6 by simp
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
      qed (use logge1 tcm1 ccL7 in \<open>simp_all add: mult_nonneg_nonneg\<close>)
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

(* Lemma 6.4 *)
lemma transform_commutes_form:
  shows "\<exists> (bnd :: nat poly) (c :: real).
           \<forall> f sub. (\<forall>f' \<in> range sub. formula_well_formed (alphabet F) f') \<longrightarrow>
             (\<exists> lines sz dep.
                provable_balanced_iff (spira_trans (sub_formula sub f)) (sub_formula (\<lambda> v. spira_trans (sub v)) f) lines sz dep
              \<and> lines \<le> poly bnd (len_formula (sub_formula sub f))
              \<and> sz \<le> poly bnd (len_formula (sub_formula sub f))
              \<and> real dep \<le> c * log 2 (real (len_formula (sub_formula sub f)) + 1))"
  sorry
end
end