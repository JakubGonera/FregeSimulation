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
      have c_def: "c = Or"
      proof (rule ccontr)
        assume c_not_or: "c \<noteq> Or"
        have "peel (Conn c fs) y = None"
          using False c_not_or by simp
        with peel_some show False by simp
      qed

      have fs2_ex: "\<exists>u v. fs = [u, v]"
      proof (cases fs)
        case Nil
        with peel_some False c_def show ?thesis
          by simp
      next
        case (Cons f fs')
        have fs_cons: "fs = f # fs'"
          using Cons by simp
        show ?thesis
        proof (cases fs')
          case Nil
          with peel_some False c_def Cons show ?thesis
            by (cases f) (simp_all split: list.splits)
        next
          case (Cons g rest)
          have fs'_cons: "fs' = g # rest"
            using Cons by simp
          show ?thesis
          proof (cases rest)
            case Nil
            have fs_eq: "fs = [f, g]"
              using fs_cons fs'_cons Nil by simp
            then show ?thesis
              by blast
          next
            case (Cons h t)
            have False
              using peel_some False c_def fs_cons fs'_cons Cons
              by (cases f) (simp_all split: list.splits)
            then show ?thesis by blast
          qed
        qed
      qed
      then obtain u v where fs2: "fs = [u, v]" by blast

      have u_ex: "\<exists>d a. u = Conn d [a]"
      proof (cases u)
        case (Atom s)
        with peel_some False c_def fs2 show ?thesis
          by simp
      next
        case (Conn d us)
        then show ?thesis
        proof (cases us)
          case Nil
          with peel_some False c_def fs2 Conn show ?thesis
            by simp
        next
          case (Cons a us')
          have us_cons: "us = a # us'"
            using Cons by simp
          then show ?thesis
          proof (cases us')
            case Nil
            with Conn Cons show ?thesis
              by blast
          next
            case (Cons b rest)
            have False
              using peel_some False c_def fs2 Conn us_cons Cons
              by simp
            then show ?thesis by blast
          qed
        qed
      qed
      then obtain d a where u_def: "u = Conn d [a]" by blast

      have d_def: "d = Not"
      proof (rule ccontr)
        assume d_not: "d \<noteq> Not"
        with peel_some False c_def fs2 u_def show False
          by simp
      qed

      have rec_ex: "\<exists>q. peel v y = Some q"
      proof (cases "peel v y")
        case None
        with peel_some False c_def fs2 u_def d_def show ?thesis
          by simp
      next
        case (Some q')
        then show ?thesis by auto
      qed
      then obtain q where rec_v: "peel v y = Some q" by blast

      have fs_def: "fs = [Conn Not [a], v]"
        using fs2 u_def d_def by simp
      have p_def: "p = combine_proofs \<lparr>assumptions = {Conn c fs, a}, thesis = v, steps = [Conn c fs, a, v]\<rparr> q"
        using peel_some False c_def fs2 u_def d_def rec_v
        by simp
     

      let ?sub = "\<lambda>s. if s = ''P'' then a else if s = ''Q'' then v else Atom s"

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

(* lemma second_step_proves:
  fixes rule :: rule
  assumes "pr = second_step rule"
  shows "valid_proof F pr \<and> 
         assumptions pr = {rule_to_taut rule} \<union> set (prems rule) \<and> 
         thesis pr = concl rule"
proof -
  have "\<exists> p. peel (rule_to_taut rule) (concl rule) = Some p"
  have "valid_proof F pr"
*)



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
