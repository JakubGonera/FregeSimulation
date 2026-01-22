theory Frege
  imports Main "HOL-Computational_Algebra.Polynomial"
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

fun eval :: "frege \<Rightarrow> (string \<Rightarrow> bool) \<Rightarrow> formula \<Rightarrow> bool" where
  "eval F v (Bot) = False" |  
  "eval F v (Top) = True" |
  "eval F v (Atom a) = v a" |
  "eval F v (Conn c fs) = (conn_eval F c) (map (eval F v) fs)"

record frege_proof =
  assumptions :: "formula set"
  thesis :: "formula"
  steps :: "formula list"

fun sub_formula :: "(string \<Rightarrow> formula) \<Rightarrow> formula \<Rightarrow> formula" where
  "sub_formula sub (Atom a) = sub a" |
  "sub_formula sub Bot = Bot" |
  "sub_formula sub Top = Top" |
  "sub_formula sub (Conn c fs) = Conn c (map (sub_formula sub) fs)"

fun sub_rule :: "(string \<Rightarrow> formula) \<Rightarrow> rule \<Rightarrow> rule" where
  "sub_rule sub r = \<lparr>
    prems = map (sub_formula sub) (prems r),
    concl = sub_formula sub (concl r)
  \<rparr>"

definition derived :: "rule set \<Rightarrow> formula list \<Rightarrow> formula \<Rightarrow> bool" where
  "derived rs fs f \<longleftrightarrow> (\<exists> r \<in> rs. \<exists> sub. let sub_r = sub_rule sub r in 
                       (concl sub_r) = f \<and> 
                       (\<forall> f1 \<in> set (prems sub_r). \<exists> f2 \<in> set fs. f1 = f2))"

definition valid_proof :: "frege \<Rightarrow> frege_proof \<Rightarrow> bool" where
  "valid_proof F pr \<longleftrightarrow> 
    thesis pr = last (steps pr)
    \<and> (\<forall>i < length (steps pr). 
 steps pr ! i \<in> assumptions pr \<or> derived (rules F) (take i (steps pr)) (steps pr ! i))"

definition sound_rule :: "frege \<Rightarrow> rule \<Rightarrow> bool" where
  "sound_rule F r \<longleftrightarrow> 
    (\<forall> val. \<forall> f \<in> set (prems r). eval F val f \<longrightarrow> eval F val (concl r))"

fun len_formula :: "formula \<Rightarrow> nat" where
  "len_formula Bot = 1" |
  "len_formula Top = 1" |
  "len_formula (Atom s) = 1" |
  "len_formula (Conn s fs) = 1 + sum_list (map (\<lambda> f. len_formula f) fs)"

locale frege_system = 
  fixes F :: frege
  assumes sound: "\<forall> r \<in> rules F. sound_rule F r"
  and impl_complete: "\<forall> fs th val. ((\<forall> f \<in> fs. eval F val f) \<longrightarrow> eval F val th) 
                          \<longrightarrow> (\<exists> pr. valid_proof F pr
                                   \<and> assumptions pr = fs 
                                   \<and> thesis pr = th)"
begin

end

theorem Reckhow:
  fixes p q :: "int poly"
  assumes "frege_system F1 \<and> frege_system F2"
  shows "\<exists> f g p q. \<forall> w \<tau>. thesis w = g \<tau> \<and> valid_proof F1 w \<Longrightarrow> 
valid_proof F2 (f w \<tau>) \<and> thesis (f w \<tau>) = \<tau> \<and> 
len_formula (g \<tau>) \<le> poly p (len_formula \<tau>) \<and>
len_proof w \<le> poly q (len_proof f w \<tau>)"
proof
  sorry

  
end