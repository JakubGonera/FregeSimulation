theory Frege
  imports Main
begin

(* A formula can be built over arbitrary connectives, 
  evaluation of which we supply later in a Frege *)

datatype formula = 
  Bot |
  Top |
  Atom string |
  Conn string "formula list"

record rule =
  prems :: "formula list"
  concl :: "formula"

(* If a connective is not in our alphabet we want arity = 0 and eval = \<lambda> l. false*)
record frege =
  rules :: "rule set"
  conn_eval :: "string \<Rightarrow> (bool list \<Rightarrow> bool)"
  conn_arity :: "string \<Rightarrow> nat"

fun eval :: "frege \<Rightarrow> (string \<Rightarrow> bool) \<Rightarrow> formula \<Rightarrow> bool" where
  "eval F v (Bot) = False" |  
  "eval F v (Top) = True" |
  "eval F v (Atom a) = v a" |
  "eval F v (Conn c fs) = (conn_eval F c) (map (eval F v) fs)"

fun valid_formula :: "formula \<Rightarrow> frege \<Rightarrow> bool" where
  "valid_formula Top F = True" |
  "valid_formula Bot F = True" |
  "valid_formula (Atom a) F = True" |
  "valid_formula (Conn c fs) F = 
    (length fs = conn_arity F c
    \<and> list_all (\<lambda>f. valid_formula f F) fs)"

record frege_proof =
  assumptions :: "formula set"
  thesis :: "formula"
  steps :: "formula list"

fun formula_sub :: "(string \<Rightarrow> formula) \<Rightarrow> formula \<Rightarrow> formula" where
  "formula_sub sub (Atom a) = sub a" |
  "formula_sub sub Bot = Bot" |
  "formula_sub sub Top = Top" |
  "formula_sub sub (Conn c fs) = Conn c (map (formula_sub sub) fs)"

fun rule_sub :: "(string \<Rightarrow> formula) \<Rightarrow> rule \<Rightarrow> rule" where
  "rule_sub sub r = \<lparr>
    prems = map (formula_sub sub) (prems r),
    concl = formula_sub sub (concl r)
  \<rparr>"

definition derived :: "formula \<Rightarrow> formula list \<Rightarrow> rule set \<Rightarrow> bool" where
  "derived f fs rs \<longleftrightarrow> (\<exists> r \<in> rs. \<exists> sub. let sub_r = rule_sub sub r in 
                       (concl sub_r) = f \<and> 
                       (\<forall> f1 \<in> set (prems sub_r). \<exists> f2 \<in> set fs. f1 = f2))"

definition valid_proof :: "frege_proof \<Rightarrow> frege \<Rightarrow> bool" where
  "valid_proof pr F \<longleftrightarrow> 
    (\<forall> f \<in> assumptions pr. valid_formula f F)
    \<and> valid_formula (thesis pr) F
    \<and> list_all (\<lambda>f. valid_formula f F) (steps pr)
    \<and> thesis pr = last (steps pr)
    \<and> list_all (\<lambda>f. f \<in> assumptions pr \<or> derived f (steps pr) (rules F)) (steps pr)"

definition sound_rule :: "frege \<Rightarrow> rule \<Rightarrow> bool" where
  "sound_rule F r \<longleftrightarrow> 
    list_all (\<lambda> f. valid_formula f F) (prems r)
    \<and> valid_formula (concl r) F
    \<and> (\<forall> val. list_all (\<lambda> f. eval F val f) (prems r) \<longrightarrow> eval F val (concl r))"

locale frege_system = 
  fixes F :: frege
  assumes sound: "\<forall> r \<in> rules F. sound_rule F r"
  and impl_complete: "\<forall> fs th val. ((\<forall> f \<in> fs. eval F val f) \<longrightarrow> eval F val th) 
                          \<longrightarrow> (\<exists> pr. valid_proof pr F
                                   \<and> assumptions pr = fs 
                                   \<and> thesis pr = th)"
begin

end

end