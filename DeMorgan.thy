theory DeMorgan imports Frege begin

datatype dm_conn = Top | Bot | Not | Or | And

type_synonym dformula = "(string, dm_conn) formula"
type_synonym drule = "(string, dm_conn) rule"
type_synonym dalphabet = "dm_conn alphabet"
type_synonym dfrege = "(string, dm_conn) frege"
type_synonym dproof = "(string, dm_conn) frege_proof"

function rule_to_taut :: "drule \<Rightarrow> dformula" where
  "rule_to_taut \<lparr>prems = [], concl = c\<rparr> = c" |
  "rule_to_taut \<lparr>prems = f # fs, concl = c\<rparr> = 
    Conn Or [Conn Not [f], rule_to_taut \<lparr>prems = fs, concl = c\<rparr>]"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>r. length (prems r))") auto

definition modus_ponens :: drule where
  "modus_ponens = \<lparr> 
    prems = [
      Atom ''P'', 
      Conn Or [Conn Not [Atom ''P''], Atom ''Q'']
    ], 
    concl = Atom ''Q'' 
  \<rparr>"


locale de_morgan_frege =
  fixes F :: dfrege
  assumes alph: "a = alphabet F" 
  and conns_def: "conns a = {Top, Bot, Not, Or, And}"
  and arity_def: "arity a = (\<lambda>c. case c of Top \<Rightarrow> 0 | Bot \<Rightarrow> 0 | Not \<Rightarrow> 1 | Or \<Rightarrow> 2 | And \<Rightarrow> 2)"
  and conn_evals_def: "conn_evals a = (\<lambda> c. case c of
    Top \<Rightarrow> (\<lambda>_. True)                \<comment> \<open>nullary: ignores input list\<close>
  | Bot \<Rightarrow> (\<lambda>_. False)               \<comment> \<open>nullary\<close>
  | Not \<Rightarrow> (\<lambda>args. case args of [x] \<Rightarrow> \<not> x | _ \<Rightarrow> undefined)
  | Or  \<Rightarrow> (\<lambda>args. case args of [x, y] \<Rightarrow> x \<or> y | _ \<Rightarrow> undefined)
  | And \<Rightarrow> (\<lambda>args. case args of [x, y] \<Rightarrow> x \<and> y | _ \<Rightarrow> undefined))"
  and "frege_system F" and "alphabet F = a"
begin

(*
1. Either one of the premises is false, then the formula is true (\<not>f \<or> ...)
2. Or all of the premises are true and by soundness the conclusion is also true (\<not>f \<or> ... \<or> q)
*)

lemma taut_unfold: "prems r = p # ps \<longrightarrow> eval a val (rule_to_taut r) = ((\<not> eval a val p) \<or> 
                         eval a val (rule_to_taut \<lparr>prems = ps, concl = concl r\<rparr>))"
proof
  assume pr: "prems r = p # ps"

  have r_eq: "r = \<lparr>prems = p # ps, concl = concl r\<rparr>"
    using pr by (cases r) auto

  show "eval a val (rule_to_taut r) =
   ((\<not> eval a val p) \<or> eval a val (rule_to_taut \<lparr>prems = ps, concl = concl r\<rparr>))"
  proof -
    have "eval a val (rule_to_taut r) = eval a val (rule_to_taut \<lparr>prems = p # ps, concl = concl r\<rparr>)"
      using r_eq by simp
    also have "... = eval a val (Conn Or [Conn Not [p],
                            rule_to_taut \<lparr>prems = ps, concl = concl r\<rparr>])"
      by auto
    also have "... = (eval a val (Conn Not [p]) \<or> 
                      eval a val (rule_to_taut \<lparr>prems = ps, concl = concl r\<rparr>))"
      using de_morgan_frege_axioms de_morgan_frege_def by auto
    also have "... = ((\<not> eval a val p) \<or> 
                         eval a val (rule_to_taut \<lparr>prems = ps, concl = concl r\<rparr>))"
      using de_morgan_frege_axioms de_morgan_frege_def by auto
    finally show ?thesis .
  qed
qed

lemma premise_false:
  fixes val :: "string \<Rightarrow> bool"
  and r :: drule
assumes "\<exists> f \<in> set (prems r). \<not> eval a val f"
  and "prems r \<noteq> []"
shows "eval a val (rule_to_taut r)"
  using assms
proof (induction "prems r" arbitrary: r)
  case Nil
  thus ?case by auto
next
  case (Cons p ps)
  show ?case
  proof (cases "\<not> eval a val p")
    case True
    show ?thesis using Cons True taut_unfold[of r p ps a val] by auto
  next
    case False
    have "\<exists> g \<in> set (p # ps). \<not> eval a val g" using Cons assms(1) by auto
    hence g: "\<exists> g \<in> set ps. \<not> eval a val g" using False by auto
    hence "ps \<noteq> []" by auto
    hence "eval a val (rule_to_taut \<lparr>prems = ps, concl = concl r\<rparr>)" using g Cons by auto
    thus ?thesis using taut_unfold[of r p ps a val] Cons by auto
  qed
qed

lemma premises_true:
  fixes val :: "string \<Rightarrow> bool"
  and r :: drule
assumes "eval a val (concl r)"
shows "eval a val (rule_to_taut r)"
  using assms
proof (induction "prems r" arbitrary: r)
  case Nil
  have "r = \<lparr> prems = [], concl = concl r\<rparr>" using Nil by simp
  hence "eval a val (rule_to_taut r) = eval a val (rule_to_taut \<lparr>prems = [], concl = concl r\<rparr>)" 
    by simp
  also have  "... = eval a val (concl r)" by simp
  finally have "eval a val (rule_to_taut r) = eval a val (concl r)" by simp
  thus ?case using Nil.prems by simp
next
  case (Cons p ps)
  have eq: "eval a val (rule_to_taut r) = ((\<not> eval a val p) \<or> 
                         eval a val (rule_to_taut \<lparr>prems = ps, concl = concl r\<rparr>))"
    using Cons taut_unfold[of r p ps a val] by simp
  have "eval a val (rule_to_taut \<lparr>prems = ps, concl = concl r\<rparr>)" using Cons by simp
  thus ?case using eq by simp
qed


lemma sound_rule_gives_tautology:
  assumes "r \<in> rules F"
shows "\<forall> val. eval a val (rule_to_taut r)"
proof
  fix val
  show "eval a val (rule_to_taut r)"
  proof (cases "\<exists> f \<in> set (prems r). \<not> eval a val f")
    case True
    have "prems r \<noteq> []" using True by auto
    thus ?thesis using True premise_false by simp
  next
    case False
    have all_prems_true: "\<forall> f \<in> set (prems r). eval a val f" using False by simp
    have "sound_rule F r" 
      using assms de_morgan_frege_def de_morgan_frege_axioms frege_system.sound by auto
    hence "eval a val (concl r)" using all_prems_true sound_rule_def[of F r] alph[of a] by simp 
    thus ?thesis using premises_true by simp
  qed
qed

end

locale de_morgan_sim =
  fixes F :: dfrege and F' :: dfrege
  assumes dm1: "de_morgan_frege F" and dm2: "de_morgan_frege F'"
  and "modus_ponens \<in> rules F"
begin

(*
This theorem says: take a rule from system F' which has the de_morgan alphabet, flatten it
to a chain of implications, and now it has a proof in a system F which only has modus ponens
as a rule, but uses the same de_morgan alphabet
*)

definition proof_of :: "dfrege \<Rightarrow> dproof \<Rightarrow> dformula \<Rightarrow> bool" where
  "proof_of frege pr f \<longleftrightarrow> valid_proof frege pr \<and> assumptions pr = {} \<and> thesis pr = f"

lemma rule_exists_proof:
  assumes "r \<in> rules F'" and "f_rule = rule_to_taut r"
shows "\<exists> pr. valid_proof F pr \<and>  assumptions pr = {} \<and> thesis pr = f_rule"
proof -
  have "alphabet F = alphabet F'" 
    using de_morgan_sim_def de_morgan_sim_axioms de_morgan_frege.alph by simp
  hence all_val: "\<forall> val. eval (alphabet F) val f_rule"
    using de_morgan_frege.sound_rule_gives_tautology[of F' r] assms dm2 by simp
  have fsys: "frege_system F"
    using dm1 unfolding de_morgan_frege_def by simp
  interpret fs: frege_system F
    by (rule fsys)
  have impl0:
    "((\<forall>f\<in>{}. eval (alphabet F) (\<lambda>_. False) f) \<longrightarrow> eval (alphabet F) (\<lambda>_. False) f_rule)
      \<longrightarrow> (\<exists>pr. valid_proof F pr \<and> assumptions pr = {} \<and> thesis pr = f_rule)"
    using fs.impl_complete by blast
  have "eval (alphabet F) (\<lambda>_. False) f_rule"
    using all_val by simp
  with impl0 show ?thesis by simp
qed

lemma first_step_exists: "\<exists> f. \<forall> sub. \<forall> rule \<in> rules F'.
          proof_of F (f rule sub) (rule_to_taut (sub_rule sub rule))"
proof -
  have sub_rule_to_taut:
    "sub_formula sub (rule_to_taut r) = rule_to_taut (sub_rule sub r)"
    for sub r
  proof (induction r rule: rule_to_taut.induct)
    case (1 c)
    then show ?case by simp
  next
    case (2 f fs c)
    then show ?case by simp
  qed

  have step_exists:
    "\<forall>sub. \<forall>rule \<in> rules F'. \<exists>pr. proof_of F pr (rule_to_taut (sub_rule sub rule))"
  proof (intro allI ballI)
    fix sub rule
    assume r_in: "rule \<in> rules F'"
    have ex_pr:
      "\<exists>pr. valid_proof F pr \<and> assumptions pr = {} \<and> thesis pr = rule_to_taut rule"
      using rule_exists_proof[OF r_in refl] .
    let ?pr = "SOME pr. valid_proof F pr \<and> assumptions pr = {} \<and> thesis pr = rule_to_taut rule"
    have pr_props: "valid_proof F ?pr \<and> assumptions ?pr = {} \<and> thesis ?pr = rule_to_taut rule"
      using ex_pr by (rule someI_ex)
    have pr_valid: "valid_proof F ?pr" using pr_props by auto
    have pr_assm: "assumptions ?pr = {}" using pr_props by auto
    have pr_thesis: "thesis ?pr = rule_to_taut rule" using pr_props by auto
    have "frege_system F"
      using dm1 unfolding de_morgan_frege_def by simp
    then have sub_valid: "valid_proof F (sub_proof sub ?pr)"
      using pr_valid frege_system.proof_substitution by auto
    have "proof_of F (sub_proof sub ?pr) (rule_to_taut (sub_rule sub rule))"
      unfolding proof_of_def
      using sub_valid pr_assm pr_thesis sub_rule_to_taut by simp
    then show "\<exists>pr. proof_of F pr (rule_to_taut (sub_rule sub rule))" by auto
  qed

  have per_sub:
    "\<forall>sub. \<exists>h. \<forall>rule \<in> rules F'. proof_of F (h rule) (rule_to_taut (sub_rule sub rule))"
  proof
    fix sub
    have "\<forall>rule \<in> rules F'. \<exists>pr. proof_of F pr (rule_to_taut (sub_rule sub rule))"
      using step_exists by auto
    then show "\<exists>h. \<forall>rule \<in> rules F'. proof_of F (h rule) (rule_to_taut (sub_rule sub rule))"
      by (rule bchoice)
  qed
  from choice[OF per_sub]
  obtain f where
    f_prop: "\<forall>sub. \<forall>rule \<in> rules F'. proof_of F ((f sub) rule) (rule_to_taut (sub_rule sub rule))"
    by auto
  let ?g = "\<lambda>rule sub. (f sub) rule"
  have g_prop: "\<forall>sub. \<forall>rule \<in> rules F'. proof_of F (?g rule sub) (rule_to_taut (sub_rule sub rule))"
    using f_prop by auto
  show ?thesis
  proof (rule exI[of _ ?g])
    show "\<forall>sub. \<forall>rule \<in> rules F'. proof_of F (?g rule sub) (rule_to_taut (sub_rule sub rule))"
      using g_prop .
  qed
qed


definition first_step where
  "first_step = (SOME f. \<forall> rule sub.
          proof_of F (f rule sub) (concl (sub_rule sub rule)))"

lemma "\<exists> g. \<forall> rule sub. len_proof (first_step rule sub) \<le> (g rule) * len_sub sub"
  sorry

definition rule_proof_cost where
  "rule_proof_cost rule = (SOME g. \<forall> rule sub. 
          len_proof (first_step rule sub) \<le> (g rule) * len_sub sub)"

(* peel only returns Some if the input formula is equal to the expected end, or we can peel off
with modus ponens and arrive at the expected formula. *)
fun peel :: "dformula \<Rightarrow> dformula \<Rightarrow> dproof option" where
  "peel x y =
   (if x = y then Some \<lparr>assumptions = {x}, thesis = x, steps = [x]\<rparr>
    else case x of
      Atom _ \<Rightarrow> None
    | Conn c fs \<Rightarrow>
        (if c = Or then
           (case fs of
              [Conn d [a], b] \<Rightarrow>
                (if d = Not then
                   (case peel b y of
                      Some p \<Rightarrow> Some (combine_proofs \<lparr>assumptions = {x, a}, thesis = b, steps = [x, a, b]\<rparr> p)
                    | None \<Rightarrow> None)
                 else None)
            | _ \<Rightarrow> None)
         else None))"

(* We prove from the flattened rule the conclusion, peeling with modus ponens each implication.
Note that we add each premise to assumptions and then include it as a step to immediately
derive from it the peeled formula.*)
fun second_step :: "drule \<Rightarrow> dproof" where
  "second_step rule = (case peel (rule_to_taut rule) (concl rule) of
                      Some p \<Rightarrow> p
                    | None \<Rightarrow> undefined)"

lemma peel_valid: "peel x y = Some p \<longrightarrow> valid_proof F p"
proof (induction x arbitrary: y p)
  case (Atom a)
  show ?case
    by (auto simp: valid_proof_def split: if_splits)
next
  case (Conn c fs)
  show ?case
  proof
    assume peel_some: "peel (Conn c fs) y = Some p"
    show "valid_proof F p"
    proof (cases "Conn c fs = y")
      case True
      with peel_some show ?thesis
        by (auto simp: valid_proof_def)
    next
      case False
      obtain a v q where
        c_def: "c = Or"
        and fs_def: "fs = [Conn Not [a], v]"
        and rec_v: "peel v y = Some q"
        using peel_some False
        by (cases fs) (auto split: option.splits if_splits formula.splits list.splits)
      have p_def: "p = combine_proofs \<lparr>assumptions = {Conn c fs, a}, thesis = v, steps = [Conn c fs, a, v]\<rparr> q"
        using peel_some False c_def fs_def rec_v
        by simp
     

      let ?sub = "\<lambda>s. if s = ''P'' then a else if s = ''Q'' then v else Atom s"

      (* \<not>a \<or> v, a \<longrightarrow> v *)
      have der_v: "derived (rules F) [Conn c fs, a] v"
      proof -
        have "modus_ponens \<in> rules F"
          using de_morgan_sim_axioms unfolding de_morgan_sim_def by auto
        moreover have
          "let sub_r = sub_rule ?sub modus_ponens in
             concl sub_r = v \<and>
             (\<forall>f1\<in>set (prems sub_r). \<exists>f2\<in>set [Conn c fs, a]. f1 = f2)"
          unfolding modus_ponens_def
          using c_def fs_def
          by simp
        ultimately show ?thesis
          unfolding derived_def
          by (intro bexI[of _ modus_ponens] exI[of _ ?sub]) simp
      qed

      have seed_valid:
        "valid_proof F \<lparr>assumptions = {Conn c fs, a}, thesis = v, steps = [Conn c fs, a, v]\<rparr>"
      proof -
        have steps_ok:
          "\<forall>i<length [Conn c fs, a, v].
             [Conn c fs, a, v] ! i \<in> {Conn c fs, a} \<or>
             derived (rules F) (take i [Conn c fs, a, v]) ([Conn c fs, a, v] ! i)"
        proof (intro allI impI)
          fix i
          assume i_lt: "i < length [Conn c fs, a, v]"
          show "[Conn c fs, a, v] ! i \<in> {Conn c fs, a} \<or>
                derived (rules F) (take i [Conn c fs, a, v]) ([Conn c fs, a, v] ! i)"
          proof (cases i)
            case 0
            then show ?thesis by simp
          next
            case (Suc j)
            have i_suc: "i = Suc j"
              using Suc by simp
            then show ?thesis
            proof (cases j)
              case 0
              then show ?thesis using Suc by simp
            next
              case (Suc k)
              have i_eq: "i = Suc (Suc k)"
                using i_suc Suc by simp
              have "k < 1"
                using i_lt i_eq by simp
              then have "k = 0"
                by simp
              have i_two: "i = 2"
                using i_suc Suc \<open>k = 0\<close> by simp
              show ?thesis
                using der_v i_two by simp
            qed
          qed
        qed
        show ?thesis
          unfolding valid_proof_def
          using steps_ok by simp
      qed

      have v_in_fs: "v \<in> set fs"
        using fs_def by simp
      have q_valid: "valid_proof F q"
        using Conn.IH[OF v_in_fs, of y q] rec_v by simp

      have fsys: "frege_system F"
        using dm1 unfolding de_morgan_frege_def by simp
      have comb_valid:
        "valid_proof F (combine_proofs \<lparr>assumptions = {Conn c fs, a}, thesis = v, steps = [Conn c fs, a, v]\<rparr> q)"
        using fsys seed_valid q_valid frege_system.combining_valid_proofs by blast

      show ?thesis
        using p_def comb_valid by simp
    qed
  qed
qed

lemma r_t_t_peelable: "\<exists> p. peel (rule_to_taut rule) (concl rule) = Some p"
proof (induction "prems rule" arbitrary: rule)
  case Nil
  hence "rule = \<lparr>prems = [], concl = concl rule\<rparr>" by simp
  hence "rule_to_taut rule = rule_to_taut \<lparr>prems = [], concl = concl rule\<rparr>" by simp
  hence "rule_to_taut rule = concl rule" by simp
  hence "\<exists> p. peel (rule_to_taut rule) (concl rule) = Some p" by auto
  thus ?case by simp
next
  case (Cons f fs)
  have rule_eq: "rule = \<lparr>prems = f # fs, concl = concl rule\<rparr>"
    using Cons by simp
  let ?tail = "rule_to_taut \<lparr>prems = fs, concl = concl rule\<rparr>"
  have "rule_to_taut rule = rule_to_taut \<lparr>prems = f # fs, concl = concl rule\<rparr>" 
    using rule_eq by simp
  hence rt_def: "rule_to_taut rule = Conn Or [Conn Not [f], ?tail]"
    using rule_to_taut.simps by simp
  have tail_peelable: "\<exists>q. peel ?tail (concl rule) = Some q"
    using Cons by (metis rule.select_convs(1,2))
  then obtain q where q_def: "peel ?tail (concl rule) = Some q"
    by blast

  show ?case
  proof (cases "rule_to_taut rule = concl rule")
    case True
    then show ?thesis by auto
  next
    case False
    have "peel (rule_to_taut rule) (concl rule) =
          Some (combine_proofs
                  \<lparr>assumptions = {rule_to_taut rule, f},
                   thesis = ?tail,
                   steps = [rule_to_taut rule, f, ?tail]\<rparr> q)"
      using rt_def False q_def by simp
    then show ?thesis by blast
  qed
qed

lemma premise_shorter_than_rule_to_taut_aux:
  assumes "x \<in> set ps"
  shows "len_formula x < len_formula (rule_to_taut \<lparr>prems = ps, concl = c\<rparr>)"
  using assms
proof (induction ps)
  case Nil
  then show ?case by simp
next
  case (Cons f fs)
  show ?case
  proof (cases "x = f")
    case True
    then show ?thesis by simp
  next
    case False
    then have x_in_fs: "x \<in> set fs"
      using Cons.prems by simp
    have ih: "len_formula x < len_formula (rule_to_taut \<lparr>prems = fs, concl = c\<rparr>)"
      using Cons.IH[OF x_in_fs] .
    have tail_lt:
      "len_formula (rule_to_taut \<lparr>prems = fs, concl = c\<rparr>) <
       len_formula (rule_to_taut \<lparr>prems = f # fs, concl = c\<rparr>)"
      by simp
    from ih tail_lt show ?thesis by arith
  qed
qed

lemma premise_shorter_than_rule_to_taut:
  assumes "x \<in> set (prems r)"
  shows "len_formula x < len_formula (rule_to_taut r)"
proof (cases r)
  case (fields prems concl)
  then show ?thesis
    using premise_shorter_than_rule_to_taut_aux[of x prems concl] assms by simp
qed

lemma peel_thesis:
  assumes "peel x y = Some p"
  shows "thesis p = y"
  using assms
proof (induction x arbitrary: y p)
  case (Atom a)
  then show ?case
    by (auto split: if_splits)
next
  case (Conn c fs)
  show ?case
  proof (cases "Conn c fs = y")
    case True
    have "p = \<lparr>assumptions = {y}, thesis = y, steps = [y]\<rparr>"
      using Conn.prems True by simp
    then show ?thesis
      by simp
  next
    case False
    obtain d a b q where
      c_def: "c = Or"
      and fs_def: "fs = [Conn d [a], b]"
      and d_def: "d = Not"
      and rec: "peel b y = Some q"
      and p_def: "p = combine_proofs \<lparr>assumptions = {Conn c fs, a}, thesis = b, steps = [Conn c fs, a, b]\<rparr> q"
      using Conn.prems False
      by (cases fs) (auto split: option.splits if_splits formula.splits list.splits)

    show ?thesis
      using p_def Conn.IH[OF _ rec] fs_def by simp
  qed
qed

lemma rule_to_taut_notin_prems:
  shows "rule_to_taut r \<notin> set (prems r)"
proof
  assume "rule_to_taut r \<in> set (prems r)"
  then have "len_formula (rule_to_taut r) < len_formula (rule_to_taut r)"
    using premise_shorter_than_rule_to_taut[of "rule_to_taut r" r] by simp
  then show False by simp
qed

lemma peel_rule_to_taut_assumptions:
  assumes "peel (rule_to_taut rule) (concl rule) = Some p"
  shows "assumptions p = {rule_to_taut rule} \<union> set (prems rule)"
proof -
  obtain ps c where rule_def: "rule = \<lparr>prems = ps, concl = c\<rparr>"
    by (cases rule) auto
  have assm0: "peel (rule_to_taut \<lparr>prems = ps, concl = c\<rparr>) c = Some p"
    using assms rule_def by simp
  have "assumptions p = {rule_to_taut \<lparr>prems = ps, concl = c\<rparr>} \<union> set ps"
    using assm0
  proof (induction ps arbitrary: p)
    case Nil
    then have p_def: "p = \<lparr>assumptions = {c}, thesis = c, steps = [c]\<rparr>"
      by simp
    then show ?case by simp
  next
    case (Cons f fs)
    let ?tail = "\<lparr>prems = fs, concl = c\<rparr>"
    have rt_def: "rule_to_taut \<lparr>prems = f # fs, concl = c\<rparr> = Conn Or [Conn Not [f], rule_to_taut ?tail]"
      by simp
    have tail_ge: "len_formula (rule_to_taut ?tail) \<ge> len_formula c"
    proof (induction fs)
      case Nil
      then show ?case by simp
    next
      case (Cons g gs)
      then show ?case by simp
    qed
    have rt_ne_c: "rule_to_taut \<lparr>prems = f # fs, concl = c\<rparr> \<noteq> c"
    proof
      assume eq: "rule_to_taut \<lparr>prems = f # fs, concl = c\<rparr> = c"
      have "len_formula (rule_to_taut \<lparr>prems = f # fs, concl = c\<rparr>) > len_formula c"
        using tail_ge by simp
      moreover have "len_formula (rule_to_taut \<lparr>prems = f # fs, concl = c\<rparr>) = len_formula c"
        using eq by simp
      ultimately show False by simp
    qed
    from Cons.prems obtain q where
      q_def: "peel (rule_to_taut ?tail) c = Some q"
      and p_def: "p = combine_proofs \<lparr>assumptions = {rule_to_taut \<lparr>prems = f # fs, concl = c\<rparr>, f},
                                      thesis = rule_to_taut ?tail,
                                      steps = [rule_to_taut \<lparr>prems = f # fs, concl = c\<rparr>, f, rule_to_taut ?tail]\<rparr> q"
      using rt_def rt_ne_c by (auto split: option.splits if_splits)
    have q_assm: "assumptions q = {rule_to_taut ?tail} \<union> set fs"
      using Cons.IH[OF q_def] by simp
    have tail_notin_fs: "rule_to_taut ?tail \<notin> set fs"
      using rule_to_taut_notin_prems[of ?tail] by simp
    show ?case
      using p_def q_assm tail_notin_fs by auto
  qed
  then show ?thesis
    using rule_def by simp
qed

lemma second_step_proves:
  fixes rule :: drule
  assumes "pr = second_step rule"
  shows "valid_proof F pr \<and> 
         assumptions pr = {rule_to_taut rule} \<union> set (prems rule) \<and> 
         thesis pr = concl rule"
proof -
  obtain p where peel_res: "peel (rule_to_taut rule) (concl rule) = Some p"
    using r_t_t_peelable by blast
  have pr_eq: "pr = p"
    using assms peel_res by simp
  show ?thesis
    using pr_eq peel_res peel_valid peel_rule_to_taut_assumptions peel_thesis by auto
qed

(* Predicate for a step being derived with a rule, a substitution, and as i-th step of a proof. *)
definition derived_with :: "nat \<Rightarrow> dproof \<Rightarrow> drule \<Rightarrow> (string \<Rightarrow> dformula) \<Rightarrow> bool" where
  "derived_with i pr r s \<longleftrightarrow> (let sub_r = sub_rule s r in 
                       (concl sub_r) = steps pr ! i \<and> 
                       (\<forall> f1 \<in> set (prems sub_r). \<exists> f2 \<in> set (take i (steps pr)). f1 = f2))"

definition choose_rule_sub where
  "choose_rule_sub i pr =
     (SOME (r,s). derived_with i pr r s)"

fun sim_right :: "dproof \<Rightarrow> dformula \<Rightarrow> dproof" where
    "sim_right pr th =
     fold
       (\<lambda>i acc.
          let step = (steps pr) ! i in
          if step \<in> assumptions pr then 
            combine_proofs acc \<lparr>assumptions = {}, thesis = step, steps = [step]\<rparr>
          else
            let (r, s) = choose_rule_sub i pr in
            let pr1 = first_step r s;
                pr2 = second_step (sub_rule s r)
          in combine_proofs (combine_proofs acc pr1) pr2)
       [0..<length (steps pr)]
       \<lparr>assumptions = assumptions pr,
        thesis = th,
        steps = []\<rparr>"

lemma simulation_de_morgan_right:
  assumes modus: "rules F = {modus_ponens}"
  shows "simulates F F'"
  sorry

lemma simulation_de_morgan_left:
  assumes modus: "rules F = {modus_ponens}"
  shows "simulates F' F"
  sorry

end
end
