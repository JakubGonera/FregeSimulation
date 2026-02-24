theory Frege
  imports Main "HOL-Computational_Algebra.Polynomial"
begin

(* A formula can be built over arbitrary connectives, 
  evaluation of which we supply later in a Frege *)

datatype formula = 
  Atom string |
  Conn string "formula list"

record rule =
  prems :: "formula list"
  concl :: "formula"

record alphabet = 
  conns :: "string set"
  conn_evals :: "string \<Rightarrow> (bool list \<Rightarrow> bool)"

record frege =
  rules :: "rule set"
  alphabet :: "alphabet"

fun eval :: "alphabet \<Rightarrow> (string \<Rightarrow> bool) \<Rightarrow> formula \<Rightarrow> bool" where
  "eval al v (Atom a) = v a" |
  "eval al v (Conn c fs) = (conn_evals al c) (map (eval al v) fs)"

record frege_proof =
  assumptions :: "formula set"
  thesis :: "formula"
  steps :: "formula list"

fun sub_formula :: "(string \<Rightarrow> formula) \<Rightarrow> formula \<Rightarrow> formula" where
  "sub_formula sub (Atom a) = sub a" |
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
    (\<forall> val. (\<forall> form \<in> set (prems r). eval (alphabet F) val form) \<longrightarrow> eval (alphabet F) val (concl r))"

fun len_formula :: "formula \<Rightarrow> nat" where
  "len_formula (Atom s) = 1" |
  "len_formula (Conn s fs) = 1 + sum_list (map (\<lambda> f. len_formula f) fs)"

fun len_proof :: "frege_proof \<Rightarrow> nat" where
  "len_proof pr = sum_list (map len_formula (steps pr))"

locale frege_system = 
  fixes F :: frege
  assumes sound: "\<forall> r \<in> rules F. sound_rule F r"
  and impl_complete: "\<forall> fs th val. ((\<forall> f \<in> fs. eval (alphabet F) val f) \<longrightarrow> eval (alphabet F) val th) 
                          \<longrightarrow> (\<exists> pr. valid_proof F pr
                                   \<and> assumptions pr = fs 
                                   \<and> thesis pr = th)"
begin

end

definition simulates :: "frege \<Rightarrow> frege \<Rightarrow> bool" where
 "simulates F1 F2 \<longleftrightarrow> (\<exists> f g p q. \<forall> w \<tau>. (thesis w = g \<tau> \<and> valid_proof F1 w) \<longrightarrow> 
    valid_proof F2 (f w \<tau>) \<and> thesis (f w \<tau>) = \<tau> \<and> 
    len_formula (g \<tau>) \<le> poly p (len_formula \<tau>) \<and>
    len_proof w \<le> poly q (len_proof (f w \<tau>)))"


(* A theorem on (only) simulation of Frege systems. For p-simulation we need f and
  g to be polynomial time*)
theorem Reckhow:
  assumes "frege_system F1 \<and> frege_system F2"
  shows "simulates F1 F2"
proof
  sorry

  
end