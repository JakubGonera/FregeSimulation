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

lemma rule_proof_fun_exists: "\<exists> f :: drule \<Rightarrow> dproof. \<forall> rule \<in> rules F'.
          proof_of F (f rule) (rule_to_taut rule)"
proof -
  have "\<forall> rule \<in> rules F'. \<exists> pr. proof_of F pr (rule_to_taut rule)"
    using rule_exists_proof proof_of_def by simp
  thus "\<exists> f. \<forall> rule \<in> rules F'. proof_of F (f rule) (rule_to_taut rule)" by meson
qed

definition rule_proof_fun where
  "rule_proof_fun = (SOME f. \<forall> rule \<in> rules F'.
          proof_of F (f rule) (rule_to_taut rule))"


fun first_step :: "drule \<Rightarrow> (string \<Rightarrow> dformula) \<Rightarrow> dproof" where
  "first_step rule sub = sub_proof sub (rule_proof_fun rule)"

lemma first_step_proves:
  assumes "r \<in> rules F'"
  shows "proof_of F (first_step r s) (rule_to_taut (sub_rule s r))"
proof -
  have sub_rule_to_taut:
    "sub_formula sub (rule_to_taut rule) = rule_to_taut (sub_rule sub rule)"
    for sub rule
  proof (induction rule rule: rule_to_taut.induct)
    case (1 c)
    then show ?case by simp
  next
    case (2 f fs c)
    then show ?case by simp
  qed

  have ex_fun:
    "\<exists>f :: drule \<Rightarrow> dproof. \<forall>rule \<in> rules F'. proof_of F (f rule) (rule_to_taut rule)"
    using rule_proof_fun_exists .
  have fun_prop:
    "\<forall>rule \<in> rules F'. proof_of F (rule_proof_fun rule) (rule_to_taut rule)"
    unfolding rule_proof_fun_def
    by (rule someI_ex[OF ex_fun])

  have base_proof: "proof_of F (rule_proof_fun r) (rule_to_taut r)"
    using fun_prop assms by blast
  then have base_valid: "valid_proof F (rule_proof_fun r)"
    and base_assm: "assumptions (rule_proof_fun r) = {}"
    and base_th: "thesis (rule_proof_fun r) = rule_to_taut r"
    unfolding proof_of_def by auto

  have sub_valid: "valid_proof F (sub_proof s (rule_proof_fun r))"
    using frege_system.proof_substitution dm1 base_valid de_morgan_frege_def by auto
  have sub_assm: "assumptions (sub_proof s (rule_proof_fun r)) = {}"
    using base_assm by simp
  have sub_th: "thesis (sub_proof s (rule_proof_fun r)) = rule_to_taut (sub_rule s r)"
    using base_th sub_rule_to_taut[of s r] by simp

  show ?thesis
    unfolding first_step.simps proof_of_def
    using sub_valid sub_assm sub_th by blast
qed


lemma first_step_is_bound: 
  shows "\<exists> g :: (drule \<Rightarrow> int poly). \<forall> rule \<in> rules F'. \<forall>  sub. 
            rule_restricted_sub rule sub \<longrightarrow> 
            len_proof (first_step rule sub) \<le> poly (g rule) (len_sub (var_set_rule rule) sub)"
proof -
  have finite_var_set_form: "finite (var_set_form f)" for f :: dformula
    by (induction f) auto
  have finite_var_set_rule: "finite (var_set_rule r)" for r :: drule
    by (cases r) (auto intro: finite_var_set_form)

  let ?g = "\<lambda>rule. [:0, int (len_proof (rule_proof_fun rule)):]"

  have bound_per_rule:
    "\<forall>rule \<in> rules F'. \<forall>sub.
      rule_restricted_sub rule sub \<longrightarrow>
      len_proof (first_step rule sub) \<le> poly (?g rule) (len_sub (var_set_rule rule) sub)"
  proof (intro ballI allI impI)
    fix rule sub
    assume "rule \<in> rules F'"
    assume rsub: "rule_restricted_sub rule sub"
    have restricted_sub: "\<forall>v. v \<notin> var_set_rule rule \<longrightarrow> sub v = Atom v"
      using rsub unfolding rule_restricted_sub_def by simp

    have nat_bound:
      "len_proof (first_step rule sub)
       \<le> len_proof (rule_proof_fun rule) * len_sub (var_set_rule rule) sub"
      unfolding first_step.simps
      using sub_proof_bound[of "var_set_rule rule" sub "rule_proof_fun rule"]
      using finite_var_set_rule restricted_sub by simp

    have poly_eval:
      "poly (?g rule) (len_sub (var_set_rule rule) sub) =
       int (len_proof (rule_proof_fun rule)) * int (len_sub (var_set_rule rule) sub)"
      by simp

    have int_bound:
      "int (len_proof (first_step rule sub))
       \<le> int (len_proof (rule_proof_fun rule) * len_sub (var_set_rule rule) sub)"
      using nat_bound by (rule of_nat_mono)
    have mult_cast:
      "int (len_proof (rule_proof_fun rule) * len_sub (var_set_rule rule) sub) =
       int (len_proof (rule_proof_fun rule)) * int (len_sub (var_set_rule rule) sub)"
      by simp
    have int_bound':
      "int (len_proof (first_step rule sub))
       \<le> int (len_proof (rule_proof_fun rule)) * int (len_sub (var_set_rule rule) sub)"
      using int_bound mult_cast by simp

    show "len_proof (first_step rule sub) \<le> poly (?g rule) (len_sub (var_set_rule rule) sub)"
      using int_bound' poly_eval by (simp add: algebra_simps)
  qed

  show ?thesis
    by (rule exI[of _ ?g]) (use bound_per_rule in simp)
qed

definition first_step_bound where
  "first_step_bound rule = (SOME g. \<forall> rule \<in> rules F'. \<forall>  sub. 
            rule_restricted_sub rule sub \<longrightarrow> 
            len_proof (first_step rule sub) \<le> poly (g rule) (len_sub (var_set_rule rule) sub))"

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

lemma peel_bound:
  assumes "peel x y = Some p"
  shows "len_proof p \<le> (len_formula x)^2"
  using assms
proof (induction x arbitrary: y p)
  case (Atom x)
  assume "peel (Atom x) y = Some p"
  hence "y = Atom x" using peel.elims by fastforce
  hence "peel (Atom x) y = Some \<lparr>assumptions = {Atom x}, thesis = Atom x, steps = [Atom x]\<rparr>" by simp
  hence "len_proof p = sum_list (map len_formula [Atom x])" using Atom by auto
  thus ?case by simp
next
  case (Conn c fs)
  show ?case
  proof (cases "Conn c fs = y")
    case True
    hence "peel (Conn c fs) y = Some \<lparr>assumptions = {Conn c fs}, thesis = Conn c fs, steps = [Conn c fs]\<rparr>" 
      by simp
    hence "len_proof p = sum_list (map len_formula [Conn c fs])" using Conn.prems by auto
    hence "len_proof p = len_formula (Conn c fs)" by simp
    thus ?thesis
      by (simp add: power2_nat_le_imp_le) 
  next
    case False
    hence "\<exists> a b. Conn c fs = Conn Or [Conn Not [a], b]"
      using Conn.prems
      by (cases fs) (auto split: option.splits if_splits formula.splits list.splits)
    obtain a b q where
      c_def: "c = Or"
      and fs_def: "fs = [Conn Not [a], b]"
      and rec: "peel b y = Some q"
      and p_def: "p = combine_proofs \<lparr>assumptions = {Conn c fs, a}, thesis = b, steps = [Conn c fs, a, b]\<rparr> q"
      using Conn.prems False
      by (cases fs) (auto split: option.splits if_splits formula.splits list.splits)
    have b_in: "b \<in> set fs"
      using fs_def by simp
    have IHb: "len_proof q \<le> (len_formula b)^2"
      using Conn.IH[OF b_in rec] by simp
    have p_len: "len_proof p = len_formula (Conn c fs) + len_formula a + len_formula b + len_proof q"
      using p_def by simp
    have len_x: "len_formula (Conn c fs) = len_formula a + len_formula b + 2"
      using c_def fs_def by simp
    have bound1: "len_proof p \<le> len_formula (Conn c fs) + len_formula a + len_formula b + (len_formula b)^2"
      using p_len IHb by simp
    have bound2:
      "len_formula (Conn c fs) + len_formula a + len_formula b + (len_formula b)^2
       \<le> (len_formula b)^2 + 4 * len_formula a + 4 * len_formula b + 4"
      using len_x by linarith
    have bound3:
      "(len_formula b)^2 + 4 * len_formula a + 4 * len_formula b + 4
       \<le> (len_formula (Conn c fs))^2"
      using len_x by (simp add: power2_eq_square algebra_simps)
    have "len_proof p \<le> (len_formula (Conn c fs))^2"
      using bound1 bound2 bound3 by (meson order_trans)
    thus ?thesis by simp
  qed
qed


(* Predicate for a step being derived with a rule, a substitution, and as i-th step of a proof. *)
definition derived_with :: "nat \<Rightarrow> dproof \<Rightarrow> drule \<Rightarrow> (string \<Rightarrow> dformula) \<Rightarrow> bool" where
  "derived_with i pr r s \<longleftrightarrow> (let sub_r = sub_rule s r in 
                       i < length (steps pr) \<and> (concl sub_r) = steps pr ! i \<and>
                       (\<forall> f1 \<in> set (prems sub_r). \<exists> f2 \<in> set (take i (steps pr)). f1 = f2))"

definition choose_rule_sub where
  "choose_rule_sub i pr =
     (SOME (r,s). r \<in> rules F' \<and> derived_with i pr r s \<and> rule_restricted_sub r s)"

definition sim_right_step :: "dproof \<Rightarrow> nat \<Rightarrow> dproof \<Rightarrow> dproof" where
  "sim_right_step pr i acc =
    (let step = (steps pr) ! i in
      if step \<in> assumptions pr then 
        combine_proofs acc \<lparr>assumptions = {}, thesis = step, steps = [step]\<rparr>
      else
        let (r, s) = choose_rule_sub i pr in
        let pr1 = first_step r s;
            pr2 = second_step (sub_rule s r)
        in combine_proofs acc (combine_proofs pr1 pr2))"

definition sim_right :: "dproof \<Rightarrow> dformula \<Rightarrow> dproof" where
  "sim_right pr th =
     fold (sim_right_step pr)
       [0..<length (steps pr)]
       \<lparr>assumptions = assumptions pr,
        thesis = th,
        steps = []\<rparr>"

lemma sim_right_single_der:
  fixes r :: drule
  and s :: "string \<Rightarrow> dformula"
  assumes r_in: "r \<in> rules F'"
  assumes "pr = combine_proofs (first_step r s) (second_step (sub_rule s r))"
  shows "valid_proof F pr \<and> 
         thesis pr = concl (sub_rule s r) \<and> 
         assumptions pr = set (prems (sub_rule s r)) - set (steps (first_step r s))"
proof -
  let ?rsub = "sub_rule s r"
  let ?pr1 = "first_step r s"
  let ?pr2 = "second_step ?rsub"

  have pr1_proof: "proof_of F ?pr1 (rule_to_taut ?rsub)"
    using first_step_proves[OF r_in] .
  then have pr1_valid: "valid_proof F ?pr1"
    and pr1_assm: "assumptions ?pr1 = {}"
    and pr1_th: "thesis ?pr1 = rule_to_taut ?rsub"
    unfolding proof_of_def by auto

  have pr2_props:
    "valid_proof F ?pr2 \<and>
     assumptions ?pr2 = {rule_to_taut ?rsub} \<union> set (prems ?rsub) \<and>
     thesis ?pr2 = concl ?rsub"
    using second_step_proves[of ?pr2 ?rsub] by simp
  then have pr2_valid: "valid_proof F ?pr2"
    and pr2_assm: "assumptions ?pr2 = {rule_to_taut ?rsub} \<union> set (prems ?rsub)"
    and pr2_th: "thesis ?pr2 = concl ?rsub"
    by auto

  have fsys: "frege_system F"
    using dm1 unfolding de_morgan_frege_def by simp
  have pr_valid: "valid_proof F pr"
    using assms(2) pr1_valid pr2_valid fsys frege_system.combining_valid_proofs by blast
  have pr_thesis: "thesis pr = concl ?rsub"
    using assms(2) pr2_th by simp

  have pr1_nonempty: "steps ?pr1 \<noteq> []"
    using pr1_valid unfolding valid_proof_def by simp
  have taut_in_steps: "rule_to_taut ?rsub \<in> set (steps ?pr1)"
  proof -
    have "thesis ?pr1 = last (steps ?pr1)"
      using pr1_valid unfolding valid_proof_def by simp
    then have eq_last: "rule_to_taut ?rsub = last (steps ?pr1)"
      using pr1_th by simp
    have "last (steps ?pr1) \<in> set (steps ?pr1)"
      using pr1_nonempty by (rule last_in_set)
    then show ?thesis
      by (simp only: eq_last)
  qed

  have taut_notin_prems: "rule_to_taut ?rsub \<notin> set (prems ?rsub)"
    using rule_to_taut_notin_prems[of ?rsub] .
  have pr_assms0:
    "assumptions pr = ({rule_to_taut ?rsub} \<union> set (prems ?rsub)) - set (steps ?pr1)"
    using assms(2) pr1_assm pr2_assm by simp
  have pr_assms: "assumptions pr = set (prems ?rsub) - set (steps ?pr1)"
    using pr_assms0 taut_in_steps taut_notin_prems by auto

  show ?thesis
    using pr_valid pr_thesis pr_assms by simp
qed

lemma sim_right_proves:
  fixes pr :: dproof
  assumes "valid_proof F' pr'"
  and "assumptions pr' = {}"
  and "pr = sim_right pr' (thesis pr')"
shows "valid_proof F pr \<and> thesis pr = thesis pr' \<and> assumptions pr = {}"
proof -
  let ?init = "\<lparr>assumptions = assumptions pr', thesis = thesis pr', steps = []\<rparr>"
  let ?acc = "\<lambda>k. fold (sim_right_step pr') [0..<k] ?init"
  let ?n = "length (steps pr')"

  have sub_formula_agree:
    "sub_formula s1 f = sub_formula s2 f"
    if "\<forall>v \<in> var_set_form f. s1 v = s2 v"
    for s1 s2 :: "string \<Rightarrow> dformula" and f
    using that
  proof (induction f)
    case (Atom x)
    then show ?case by simp
  next
    case (Conn c fs)
    then show ?case by simp
  qed

  have sub_rule_agree:
    "sub_rule s1 r = sub_rule s2 r"
    if "\<forall>v \<in> var_set_rule r. s1 v = s2 v"
    for s1 s2 :: "string \<Rightarrow> dformula" and r
    using that
    by (cases r) (auto intro: sub_formula_agree)

  have choose_rule_sub_props:
    "\<exists>r s. r \<in> rules F' \<and> derived_with i p r s
     \<Longrightarrow> fst (choose_rule_sub i p) \<in> rules F' \<and>
         derived_with i p (fst (choose_rule_sub i p)) (snd (choose_rule_sub i p)) \<and>
         rule_restricted_sub (fst (choose_rule_sub i p)) (snd (choose_rule_sub i p))"
    for i p
  proof -
    assume ex: "\<exists>r s. r \<in> rules F' \<and> derived_with i p r s"
    then obtain r s where r_in: "r \<in> rules F'" and dwith: "derived_with i p r s"
      by blast
    define s' where "s' = (\<lambda>v. if v \<in> var_set_rule r then s v else Atom v)"
    have rs_eq: "sub_rule s' r = sub_rule s r"
      unfolding s'_def
      by (rule sub_rule_agree) auto
    have dwith': "derived_with i p r s'"
      using dwith unfolding derived_with_def rs_eq by simp
    have rsub': "rule_restricted_sub r s'"
      unfolding rule_restricted_sub_def s'_def by simp
    let ?P = "\<lambda>rs :: drule \<times> (string \<Rightarrow> dformula).
      case rs of (r, s) \<Rightarrow> r \<in> rules F' \<and> derived_with i p r s \<and> rule_restricted_sub r s"
    have ex_pair: "\<exists>rs. ?P rs"
      using r_in dwith' rsub' by force
    have "?P (SOME rs. ?P rs)"
      by (rule someI_ex[OF ex_pair])
    then show "fst (choose_rule_sub i p) \<in> rules F' \<and>
               derived_with i p (fst (choose_rule_sub i p)) (snd (choose_rule_sub i p)) \<and>
               rule_restricted_sub (fst (choose_rule_sub i p)) (snd (choose_rule_sub i p))"
      unfolding choose_rule_sub_def
      by (cases "SOME rs. ?P rs") auto
  qed

  have prefix_inv:
    "\<forall>k\<le>?n.
      assumptions (?acc k) = {} \<and>
      set (take k (steps pr')) \<subseteq> set (steps (?acc k)) \<and>
      (k = 0 \<or> (valid_proof F (?acc k) \<and> thesis (?acc k) = steps pr' ! (k - 1)))"
  proof (intro allI impI)
    fix k
    assume k_le: "k \<le> ?n"
    show "assumptions (?acc k) = {} \<and>
          set (take k (steps pr')) \<subseteq> set (steps (?acc k)) \<and>
          (k = 0 \<or> (valid_proof F (?acc k) \<and> thesis (?acc k) = steps pr' ! (k - 1)))"
      using k_le
    proof (induction k)
      case 0
      then show ?case
        using assms(2) by simp
    next
      case (Suc k)
      have k_le: "k \<le> ?n" using Suc.prems by simp
      have k_lt: "k < ?n" using Suc.prems by simp
      have ih:
        "assumptions (?acc k) = {} \<and>
         set (take k (steps pr')) \<subseteq> set (steps (?acc k)) \<and>
         (k = 0 \<or> (valid_proof F (?acc k) \<and> thesis (?acc k) = steps pr' ! (k - 1)))"
        using Suc.IH[OF k_le] .
      then have acc_assm0: "assumptions (?acc k) = {}" by simp
      from ih have take_k_in_steps: "set (take k (steps pr')) \<subseteq> set (steps (?acc k))"
        by simp

      have step_not_assm: "steps pr' ! k \<notin> assumptions pr'"
        using assms(2) k_lt by simp
      have der_k: "derived (rules F') (take k (steps pr')) (steps pr' ! k)"
        using assms(1) k_lt step_not_assm
        unfolding valid_proof_def by blast

      have ex_rs: "\<exists>r s. r \<in> rules F' \<and> derived_with k pr' r s"
        using der_k unfolding derived_def derived_with_def by (meson k_lt)
      have choose_props:
        "fst (choose_rule_sub k pr') \<in> rules F' \<and>
         derived_with k pr' (fst (choose_rule_sub k pr')) (snd (choose_rule_sub k pr')) \<and>
         rule_restricted_sub (fst (choose_rule_sub k pr')) (snd (choose_rule_sub k pr'))"
        using choose_rule_sub_props[OF ex_rs] .
      let ?r = "fst (choose_rule_sub k pr')"
      let ?s = "snd (choose_rule_sub k pr')"
      have r_in: "?r \<in> rules F'" using choose_props by simp
      have dwith: "derived_with k pr' ?r ?s" using choose_props by simp
      have concl_step: "concl (sub_rule ?s ?r) = steps pr' ! k"
        using dwith unfolding derived_with_def by (simp add: Let_def)
      have prems_in_takek:
        "\<forall>f1 \<in> set (prems (sub_rule ?s ?r)). \<exists>f2 \<in> set (take k (steps pr')). f1 = f2"
        using dwith unfolding derived_with_def by (simp add: Let_def)

      let ?inner = "combine_proofs (first_step ?r ?s) (second_step (sub_rule ?s ?r))"
      have inner_props:
        "valid_proof F ?inner \<and>
         thesis ?inner = concl (sub_rule ?s ?r) \<and>
         assumptions ?inner = set (prems (sub_rule ?s ?r)) - set (steps (first_step ?r ?s))"
      proof (rule sim_right_single_der[OF r_in])
        show "?inner = combine_proofs (first_step ?r ?s) (second_step (sub_rule ?s ?r))"
          by simp
      qed
      then have inner_valid: "valid_proof F ?inner"
        and inner_th: "thesis ?inner = concl (sub_rule ?s ?r)"
        and inner_assm:
          "assumptions ?inner = set (prems (sub_rule ?s ?r)) - set (steps (first_step ?r ?s))"
        by auto
      have inner_assm_subset_takek: "assumptions ?inner \<subseteq> set (take k (steps pr'))"
        using inner_assm prems_in_takek by auto

      have acc_suc:
        "?acc (Suc k) = sim_right_step pr' k (?acc k)"
        by (simp add: atLeastLessThanSuc)
      have step_eq:
        "sim_right_step pr' k (?acc k) = combine_proofs (?acc k) ?inner"
      proof -
        have "sim_right_step pr' k (?acc k) =
              (let (r, s) = choose_rule_sub k pr' in
               let pr1 = first_step r s;
                   pr2 = second_step (sub_rule s r)
               in combine_proofs (?acc k) (combine_proofs pr1 pr2))"
          unfolding sim_right_step_def
          using step_not_assm
          by (simp add: Let_def)
        then have eq1:
          "sim_right_step pr' k (?acc k) =
           (let (r, s) = choose_rule_sub k pr' in
            let pr1 = first_step r s;
                pr2 = second_step (sub_rule s r)
            in combine_proofs (?acc k) (combine_proofs pr1 pr2))"
          .
        obtain a b where ch: "choose_rule_sub k pr' = (a, b)"
          by (cases "choose_rule_sub k pr'") auto
        have "sim_right_step pr' k (?acc k) =
              (let (r, s) = (a, b) in
               let pr1 = first_step r s;
                   pr2 = second_step (sub_rule s r)
               in combine_proofs (?acc k) (combine_proofs pr1 pr2))"
          using eq1 ch by simp
        then have "sim_right_step pr' k (?acc k) =
              combine_proofs (?acc k) (combine_proofs (first_step a b) (second_step (sub_rule b a)))"
          by (simp add: Let_def)
        also have "... = combine_proofs (?acc k) ?inner"
          using ch by (simp del: second_step.simps peel.simps)
        finally show ?thesis .
      qed
      have new_eq:
        "?acc (Suc k) = combine_proofs (?acc k) ?inner"
        using acc_suc step_eq by simp

      have assm_suc: "assumptions (?acc (Suc k)) = {}"
      proof -
        have "assumptions (?acc (Suc k)) =
              assumptions (?acc k) \<union> (assumptions ?inner - set (steps (?acc k)))"
          using new_eq by simp
        also have "... = {} \<union> (assumptions ?inner - set (steps (?acc k)))"
          using acc_assm0 by simp
        also have "... = {}"
        proof -
          have "assumptions ?inner \<subseteq> set (steps (?acc k))"
            using inner_assm_subset_takek take_k_in_steps by blast
          then show ?thesis by auto
        qed
        finally show ?thesis by simp
      qed

      have step_in_inner_steps: "steps pr' ! k \<in> set (steps ?inner)"
      proof -
        have inner_nz: "steps ?inner \<noteq> []"
          using inner_valid unfolding valid_proof_def by simp
        have th_last: "thesis ?inner = last (steps ?inner)"
          using inner_valid unfolding valid_proof_def by simp
        have "last (steps ?inner) = thesis ?inner"
          using th_last by simp
        also have "... = concl (sub_rule ?s ?r)"
          using inner_th by simp
        also have "... = steps pr' ! k"
          using concl_step by simp
        finally have "steps pr' ! k = last (steps ?inner)"
          by simp
        then show ?thesis
        proof -
          assume eq_last: "steps pr' ! k = last (steps ?inner)"
          have "last (steps ?inner) \<in> set (steps ?inner)"
            using inner_nz by (rule last_in_set)
          then show ?thesis
            by (simp only: eq_last)
        qed
      qed

      have take_suc_in_steps: "set (take (Suc k) (steps pr')) \<subseteq> set (steps (?acc (Suc k)))"
      proof -
        have "take (Suc k) (steps pr') = take k (steps pr') @ [steps pr' ! k]"
          using k_lt by (simp add: take_Suc_conv_app_nth)
        then have "set (take (Suc k) (steps pr')) = insert (steps pr' ! k) (set (take k (steps pr')))"
          by simp
        moreover have "steps pr' ! k \<in> set (steps (?acc (Suc k)))"
          using new_eq step_in_inner_steps by simp
        moreover have "set (take k (steps pr')) \<subseteq> set (steps (?acc (Suc k)))"
          using take_k_in_steps new_eq by auto
        ultimately show ?thesis by auto
      qed

      have valid_suc: "valid_proof F (?acc (Suc k))"
      proof (cases "k = 0")
        case True
        then show ?thesis
          using new_eq assms(2) inner_valid by simp
      next
        case False
        then have acc_valid: "valid_proof F (?acc k)"
          using ih by auto
        have fsys: "frege_system F"
          using dm1 unfolding de_morgan_frege_def by simp
        show ?thesis
          using new_eq acc_valid inner_valid fsys frege_system.combining_valid_proofs by blast
      qed
      have thesis_suc: "thesis (?acc (Suc k)) = steps pr' ! k"
        using new_eq inner_th concl_step by simp

      show ?case
        using assm_suc take_suc_in_steps valid_suc thesis_suc by auto
    qed
  qed

  have final_inv:
    "assumptions (?acc ?n) = {} \<and>
     set (take ?n (steps pr')) \<subseteq> set (steps (?acc ?n)) \<and>
     (?n = 0 \<or> (valid_proof F (?acc ?n) \<and> thesis (?acc ?n) = steps pr' ! (?n - 1)))"
    using prefix_inv[rule_format, of ?n] by simp
  have n_nz: "?n \<noteq> 0"
    using assms(1) unfolding valid_proof_def by simp
  have final_valid: "valid_proof F (?acc ?n)"
    using final_inv n_nz by auto
  have final_assm: "assumptions (?acc ?n) = {}"
    using final_inv by auto
  have final_th0: "thesis (?acc ?n) = steps pr' ! (?n - 1)"
    using final_inv n_nz by auto
  have final_th: "thesis (?acc ?n) = thesis pr'"
  proof -
    have "thesis pr' = last (steps pr')"
      using assms(1) unfolding valid_proof_def by simp
    moreover have "last (steps pr') = steps pr' ! (?n - 1)"
      using n_nz by (simp add: last_conv_nth)
    ultimately show ?thesis
      using final_th0 by simp
  qed

  have pr_eq: "pr = ?acc ?n"
    using assms(3) unfolding sim_right_def by simp
  show ?thesis
    using pr_eq final_valid final_th final_assm by auto
qed

lemma step_le_proof:
  shows "\<forall> pr. \<forall> f \<in> set (steps pr). len_formula f \<le> len_proof pr"
proof -
  have member_le_sum:
    "len_formula f \<le> sum_list (map len_formula fs)"
    if "f \<in> set fs"
    for f :: "('v, 'c) formula" and fs :: "('v, 'c) formula list"
    using that
  proof (induction fs)
    case Nil
    then show ?case by simp
  next
    case (Cons g gs)
    show ?case
    proof (cases "f = g")
      case True
      then show ?thesis by simp
    next
      case False
      then have "f \<in> set gs"
        using Cons.prems by simp
      then have "len_formula f \<le> sum_list (map len_formula gs)"
        using Cons.IH by simp
      then show ?thesis by simp
    qed
  qed
  have step_bound:
    "len_formula f \<le> len_proof pr"
    if "f \<in> set (steps pr)"
    for pr :: "('v, 'c) frege_proof" and f :: "('v, 'c) formula"
    using member_le_sum[of f "steps pr"] that by simp
  show ?thesis
  proof (rule allI)
    fix pr :: "('v, 'c) frege_proof"
    show "\<forall>f \<in> set (steps pr). len_formula f \<le> len_proof pr"
    proof (rule ballI)
      fix f :: "('v, 'c) formula"
      assume "f \<in> set (steps pr)"
      then show "len_formula f \<le> len_proof pr"
        using step_bound by blast
    qed
  qed
qed

lemma r_t_t_bound:
  shows "len_formula (rule_to_taut r) \<le> 
         len_formula (concl r) + 3 * sum_list (map len_formula (prems r))"
proof (induction "prems r" arbitrary: r)
  case Nil
  hence "r = \<lparr>prems = [], concl = concl r\<rparr>" by simp
  hence "rule_to_taut r = concl r" using rule_to_taut.simps by metis
  thus ?case by auto
next
  case (Cons x xs)
  let ?sub_r = "\<lparr>prems = xs, concl = concl r\<rparr>"
  have "r = \<lparr>prems = x # xs, concl = concl r\<rparr>" using Cons by simp
  hence "rule_to_taut r = Conn Or [Conn Not [x], rule_to_taut ?sub_r]" 
    using rule_to_taut.simps(2)[of x xs] by metis
  hence "len_formula (rule_to_taut r) = 1 + 
                                        len_formula (Conn Not [x]) + 
                                        len_formula (rule_to_taut ?sub_r)"
    by simp
  also have "... \<le> 2 + len_formula x + len_formula (rule_to_taut ?sub_r)"
    by simp
  also have "... \<le> 2 + len_formula x + len_formula (concl r) + 3 * sum_list (map len_formula xs)"
    using Cons.hyps(1)[of ?sub_r] by simp
  also have "... \<le> 3 * len_formula x + len_formula (concl r) + 3 * sum_list (map len_formula xs)"
    using len_formula_positive by auto
  finally have "len_formula (rule_to_taut r) \<le> 
                len_formula (concl r) + 3 * sum_list (map len_formula (x # xs))"
    by simp
  thus ?case using Cons.hyps(2) by simp
qed

lemma subs_rule_bound_by_proof:
  assumes "r \<in> rules F'"
      and "derived_with i pr r s"
      and "rule_restricted_sub r s"
      and "c = Max ((\<lambda> r. length (prems r)) ` rules F') + 1"
  shows "len_formula (rule_to_taut (sub_rule s r)) \<le> 3 * c * len_proof pr"
proof -
  have dwith:
    "i < length (steps pr)"
    "concl (sub_rule s r) = steps pr ! i"
    "\<forall>f1 \<in> set (prems (sub_rule s r)). \<exists>f2 \<in> set (take i (steps pr)). f1 = f2"
    using assms(2) unfolding derived_with_def by (simp_all add: Let_def)
  have concl_bound:
    "len_formula (concl (sub_rule s r)) \<le> len_proof pr"
  proof -
    have "concl (sub_rule s r) \<in> set (steps pr)"
      using dwith(1,2) by (metis in_set_conv_nth)
    then show ?thesis
      using spec[OF step_le_proof, of pr] by blast
  qed
  have prem_bound:
    "sum_list (map len_formula (prems (sub_rule s r))) \<le> length (prems (sub_rule s r)) * len_proof pr"
  proof -
    have aux:
      "sum_list (map len_formula xs) \<le> length xs * len_proof pr"
      if "\<forall>x \<in> set xs. len_formula x \<le> len_proof pr"
      for xs :: "dformula list"
      using that
    proof (induction xs)
      case Nil
      then show ?case by simp
    next
      case (Cons x xs)
      have x_bound: "len_formula x \<le> len_proof pr"
        using Cons.prems by simp
      have tail_bound: "sum_list (map len_formula xs) \<le> length xs * len_proof pr"
        using Cons.IH Cons.prems by simp
      have "sum_list (map len_formula (x # xs)) = len_formula x + sum_list (map len_formula xs)"
        by simp
      also have "... \<le> len_proof pr + length xs * len_proof pr"
        using x_bound tail_bound by simp
      also have "... = length (x # xs) * len_proof pr"
        by simp
      finally show ?case .
    qed
    have "\<forall>x \<in> set (prems (sub_rule s r)). len_formula x \<le> len_proof pr"
    proof
      fix x
      assume x_in: "x \<in> set (prems (sub_rule s r))"
      then obtain f2 where f2_in: "f2 \<in> set (take i (steps pr))" and x_eq: "x = f2"
        using dwith(3) by blast
      have "x \<in> set (steps pr)"
        using f2_in x_eq by (meson in_set_takeD set_take_subset)
      then show "len_formula x \<le> len_proof pr"
        using spec[OF step_le_proof, of pr] by blast
    qed
    then show ?thesis
      using aux[of "prems (sub_rule s r)"] by simp
  qed
  have r_bound:
    "len_formula (rule_to_taut (sub_rule s r))
     \<le> len_formula (concl (sub_rule s r)) + 3 * sum_list (map len_formula (prems (sub_rule s r)))"
    using r_t_t_bound[of "sub_rule s r"] .
  have len_prems_max: "length (prems r) \<le> Max ((\<lambda>r. length (prems r)) ` rules F')"
  proof -
    have fin_rules: "finite (rules F')"
      using dm2 unfolding de_morgan_frege_def by (simp add: frege_system.finite)
    have fin_image: "finite ((\<lambda>r. length (prems r)) ` rules F')"
      using fin_rules by simp
    have ne_image: "((\<lambda>r. length (prems r)) ` rules F') \<noteq> {}"
      using assms(1) by auto
    have len_in: "length (prems r) \<in> ((\<lambda>r. length (prems r)) ` rules F')"
      using assms(1) by blast
    have "length (prems r) \<le> Max ((\<lambda>r. length (prems r)) ` rules F')"
      using Max_ge[OF fin_image len_in] ne_image by simp
    then show ?thesis .
  qed
  have len_prems_bound: "length (prems r) \<le> c"
  proof -
    show ?thesis
      using len_prems_max assms(4) by simp
  qed
  have "len_formula (rule_to_taut (sub_rule s r))
        \<le> len_proof pr + 3 * (length (prems (sub_rule s r)) * len_proof pr)"
    using r_bound concl_bound prem_bound by simp
  also have "... = (1 + 3 * length (prems r)) * len_proof pr"
    by simp
  also have "... \<le> (3 * c) * len_proof pr"
  proof -
    have c_ge_1: "1 \<le> c"
      using assms(4) by simp
    have len_prems_bound': "length (prems r) + 1 \<le> c"
      using len_prems_max assms(4) by simp
    have coeff_bound: "1 + 3 * length (prems r) \<le> 3 * c"
      using len_prems_bound' c_ge_1 by arith
    show ?thesis
    proof -
      have lhs_eq:
        "sum_list (map len_formula (steps pr)) + 3 * length (prems r) * sum_list (map len_formula (steps pr))
         = (1 + 3 * length (prems r)) * sum_list (map len_formula (steps pr))"
        by (simp add: algebra_simps)
      have rhs_bound:
        "(1 + 3 * length (prems r)) * sum_list (map len_formula (steps pr))
         \<le> (3 * c) * sum_list (map len_formula (steps pr))"
        using mult_right_mono[OF coeff_bound, of "sum_list (map len_formula (steps pr))"] by simp
      show ?thesis
        unfolding lhs_eq using rhs_bound by simp
    qed
  qed
  finally show ?thesis by simp
qed
  
lemma var_set_rule_finite:
  shows "finite (var_set_rule r)"
proof (cases r)
  case (fields prems concl)
  have fin_prems: "finite (\<Union> (var_set_form ` set prems))"
  proof (induction prems)
    case Nil
    then show ?case by simp
  next
    case (Cons p ps)
    have fin_p: "finite (var_set_form p)"
      by (induction p) auto
    then show ?case
      using Cons by auto
  qed
  have fin_concl: "finite (var_set_form concl)"
    by (induction concl) auto
  show ?thesis
    using fields fin_prems fin_concl by simp
qed

lemma len_sub_bound_by_proof:
  assumes "r \<in> rules F'"
      and "derived_with i pr r s"
      and "rule_restricted_sub r s"
      and "c = Max ((\<lambda> r. card (var_set_rule r)) ` rules F') + 1"
    shows "len_sub (var_set_rule r) s \<le> c * len_proof pr"
proof -
  let ?var_set = "var_set_rule r"
  have sub_bound: "\<forall>f. \<forall> v \<in> var_set_form f. len_formula (s v) \<le> len_formula (sub_formula s f)"
  proof
    fix f
    show "\<forall> v \<in> var_set_form f. len_formula (s v) \<le> len_formula (sub_formula s f)"
    proof (induction f)
      case (Atom x)
      show ?case by simp
    next
      case (Conn c gs)
      have "sub_formula s (Conn c gs) = Conn c (map (sub_formula s) gs)" by simp
      hence "len_formula (sub_formula s (Conn c gs)) =
                1 + sum_list (map (\<lambda> g. len_formula g) (map (sub_formula s) gs))"
        by simp
      hence unroll: "len_formula (sub_formula s (Conn c gs)) =
                1 + sum_list (map (\<lambda> g. len_formula (sub_formula s g)) gs)"
      proof (induction gs)
        case Nil
        then show ?case by simp
      next
        case (Cons g gs)
        then show ?case by simp
      qed
      have var_in_gs: "v \<in> var_set_form (Conn c gs) \<longrightarrow> (\<exists> f \<in> set gs. v \<in> var_set_form f)"
        by simp
      have g_bounds: "v \<in> var_set_form g \<and> g \<in> set gs \<longrightarrow> len_formula (s v) \<le> len_formula (sub_formula s g)"
        using Conn by simp
      have g_le: "\<forall> g \<in> set gs. len_formula (sub_formula s g) \<le> len_formula (sub_formula s (Conn c gs))"
      proof
        fix g
        assume g_in: "g \<in> set gs"
        have g_sum_bound: "len_formula (sub_formula s g) \<le> sum_list (map (\<lambda>g. len_formula (sub_formula s g)) gs)"
          using g_in
        proof (induction gs)
          case Nil
          then show ?case by simp
        next
          case (Cons h hs)
          then show ?case by (cases "g = h") simp_all
        qed
        show "len_formula (sub_formula s g) \<le> len_formula (sub_formula s (Conn c gs))"
        proof -
          have sum_bound:
            "sum_list (map (\<lambda>g. len_formula (sub_formula s g)) gs)
              \<le> len_formula (sub_formula s (Conn c gs))"
          proof (induction gs)
            case Nil
            then show ?case by simp
          next
            case (Cons h hs)
            then show ?case by simp
          qed
          show ?thesis
            using g_sum_bound sum_bound by arith
        qed
      qed
      show ?case
      proof (intro ballI)
        fix v
        assume v_in: "v \<in> var_set_form (Conn c gs)"
        have ex_g: "\<exists>g \<in> set gs. v \<in> var_set_form g"
          using var_in_gs v_in by simp
        then obtain g where g_in: "g \<in> set gs" and vg_in: "v \<in> var_set_form g"
          by blast
        have IHg: "\<forall>v \<in> var_set_form g. len_formula (s v) \<le> len_formula (sub_formula s g)"
          using Conn.IH g_in by blast
        have v_to_g: "len_formula (s v) \<le> len_formula (sub_formula s g)"
          using IHg vg_in by blast
        have g_to_conn: "len_formula (sub_formula s g) \<le> len_formula (sub_formula s (Conn c gs))"
          using g_le g_in by blast
        show "len_formula (s v) \<le> len_formula (sub_formula s (Conn c gs))"
          using v_to_g g_to_conn by arith
      qed
    qed
  qed

  have "\<forall> v \<in> ?var_set. len_formula (s v) \<le> len_proof pr"
  proof (intro ballI)
    fix v
    assume v_in_vs: "v \<in> ?var_set"
    show "len_formula (s v) \<le> len_proof pr"
    proof (cases "v \<in> var_set_form (concl r)")
      case True
      have "concl (sub_rule s r) \<in> set (steps pr)"
        using assms(2) derived_with_def by simp
      hence a: "len_formula (concl (sub_rule s r)) \<le> len_proof pr"
        using step_le_proof by blast
      have b: "concl (sub_rule s r) = sub_formula s (concl r)" by simp
      have c: "len_formula (s v) \<le> len_formula (sub_formula s (concl r))"
        using sub_bound True by simp
      thus ?thesis using a b by simp
    next
      case False
      hence v_in_prem: "v \<in> \<Union> (var_set_form ` (set (prems r)))"
        using v_in_vs by simp
      obtain f :: dformula
        where v_def: "v \<in> var_set_form f \<and> f \<in> set (prems r)"
        using v_in_prem by auto
      then obtain g :: dformula
        where g_eq: "g \<in> set (prems (sub_rule s r)) \<and> g = sub_formula s f"
        by auto
      hence "g \<in> set (steps pr)" using assms(2) derived_with_def
        by (meson in_set_takeD)
      hence g_le: "len_formula g \<le> len_proof pr"
        using step_le_proof by blast
      have "len_formula (s v) \<le> len_formula g"
        using g_eq v_def sub_bound by simp
      thus ?thesis using g_le by simp
    qed
  qed

  show ?thesis
    sorry


lemma sim_right_step_bound:
  shows "\<exists> bound. \<forall> pr i acc. i \<ge> 0 \<and> i < length (steps pr) \<and> valid_proof F' pr \<longrightarrow>
            len_proof (sim_right_step pr i acc) \<le> poly bound (len_proof pr) + len_proof acc"
  sorry
(*
We create such a polynomial by considering the max of:
- an identity (this solves the case when the steps adds an assumption
- a bound for the first step. such a bound exists as there are only a finite number of rules, thus
  a term-wise max of those polynomial bounds is itself a polynomial that bounds all possibilities.
- a bound for the second step derived from the quadratic bound for peel
The max we consider is maximum of coefficients for each power. We might need a lemma that such
piece-wise max yields a bound for natural inputs. Maybe we don't need this max but some other way
to combine polynomial for a bound, we should use whatever is the tidies.

1. Define the final polynomial
2. Cases: assumption?
  a. len_proof (sim_right_step pr i acc) = len_formula (steps ! i) + len_proof acc
     \<le> len_proof pr + len_proof acc
  b. show that the proof is first_step + second_step + acc.

*)


lemma sim_right_bound:
  assumes "valid_proof F' pr \<and> assumptions pr = {}"
  shows "\<exists> bound. len_proof (sim_right pr (thesis pr)) \<le> poly bound (len_proof pr)"
  sorry

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
