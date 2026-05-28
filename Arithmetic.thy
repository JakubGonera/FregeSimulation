theory Arithmetic
  imports Complex_Main "HOL-Computational_Algebra.Polynomial"
begin

text \<open>Pure arithmetic / list-arithmetic lemmas, independent of any
      formula-specific types. These are used throughout the project's
      combinatorial bounds.\<close>

lemma poly_nat_mono:
  fixes p :: "nat poly" and a b :: nat
  assumes "a \<le> b"
  shows "poly p a \<le> poly p b"
proof (induction p)
  case 0 thus ?case by simp
next
  case (pCons k p)
  have "a * poly p a \<le> b * poly p b"
    using assms pCons.IH by (rule mult_le_mono)
  thus ?case by simp
qed

lemma poly_le_poly1_pow:
  fixes p :: "nat poly"
  assumes "1 \<le> n"
  shows "poly p n \<le> poly p 1 * n ^ degree p"
proof (induction p)
  case 0 thus ?case by simp
next
  case (pCons k p)
  show ?case
  proof (cases "p = 0")
    case True thus ?thesis by simp
  next
    case False
    have deg_eq: "degree (pCons k p) = Suc (degree p)" using False by simp
    have npow_ge: "1 \<le> n ^ Suc (degree p)" using assms by simp
    have IH: "poly p n \<le> poly p 1 * n ^ degree p" using pCons.IH .
    have "poly (pCons k p) n = k + n * poly p n" by simp
    also have "\<dots> \<le> k + n * (poly p 1 * n ^ degree p)"
      using IH by simp
    also have "\<dots> = k + poly p 1 * n ^ Suc (degree p)"
      by (simp add: mult.left_commute)
    also have "\<dots> \<le> k * n ^ Suc (degree p) + poly p 1 * n ^ Suc (degree p)"
      using npow_ge by (intro add_mono mult_le_mono2) simp_all
    also have "\<dots> = (k + poly p 1) * n ^ Suc (degree p)"
      by (simp add: algebra_simps)
    also have "\<dots> = poly (pCons k p) 1 * n ^ degree (pCons k p)"
      using deg_eq by simp
    finally show ?thesis .
  qed
qed

lemma nat_ceil_le:
  fixes k :: "nat"
    and n :: "nat"
  shows "(n + k) div (k + 1) \<le> n"
proof -
  have "(n + 1) * (k + 1) = n + k + (n * k + 1)"
    by (simp add: algebra_simps)
  hence "n + k < (n + 1) * (k + 1)"
    by simp
  hence "(n + k) div (k + 1) < n + 1"
    by (rule less_mult_imp_div_less)
  thus ?thesis by simp
qed

lemma nat_div_to_mult:
  fixes x :: "nat"
    and n :: "nat"
    and k :: "nat"
  assumes "x \<ge> n div (k+1)"
  shows "(k+1) * x + k \<ge> n"
proof -
  have decomp: "(k + 1) * (n div (k + 1)) + n mod (k + 1) = n"
    using div_mult_mod_eq[of n "k + 1"] by (simp add: algebra_simps)
  have remainder_bound: "n mod (k + 1) \<le> k"
    using mod_less_divisor[of "k + 1" n] by simp
  have step: "(k + 1) * (n div (k + 1)) \<le> (k + 1) * x"
    using assms by (rule mult_le_mono2)
  from decomp remainder_bound step show ?thesis by linarith
qed

lemma sum_list_const_nat:
  fixes K :: nat
  shows "sum_list (map (\<lambda>_. K) xs) = length xs * K"
  by (induction xs) auto

lemma sum_list_pointwise_le:
  fixes f g :: "'a \<Rightarrow> nat"
  assumes "\<forall> x \<in> set xs. f x \<le> g x"
  shows "sum_list (map f xs) \<le> sum_list (map g xs)"
  using assms
proof (induction xs)
  case Nil
  show ?case by simp
next
  case (Cons a xs)
  hence head: "f a \<le> g a" by simp
  have tail: "sum_list (map f xs) \<le> sum_list (map g xs)"
    using Cons.IH Cons.prems by simp
  from head tail show ?case by simp
qed

text \<open>The log-step underlying Spira's depth bound (Filmus lemma 4.3 (c)):
      pure real-arithmetic, independent of any formula type.\<close>

lemma trans_c_log_step:
  fixes A B C T L Larg :: nat and c D_real :: real
  assumes A_gt_B: "A > B"
      and AC_ge_B: "A + C \<ge> B"
      and arg_le: "A * (Larg + 1) \<le> B * L + C + A"
      and L_ge_T: "L \<ge> T"
      and ratio_pos: "B * T + C + A < A * (T + 1)"
      and c_bound: "c * log 2 (real (A * (T + 1))
                              / real (B * T + C + A)) \<ge> D_real"
      and c_nonneg: "c \<ge> 0"
    shows "D_real + c * log 2 (real Larg + 1) \<le> c * log 2 (real L + 1)"
proof -
  let ?A = "real A" and ?B = "real B" and ?C = "real C"
  let ?L = "real L" and ?Larg = "real Larg"
  let ?T = "real T"
  have A_pos: "?A > 0" using A_gt_B by simp
  have BL_nn: "(0::real) \<le> ?B * ?L" by simp
  have BT_nn: "(0::real) \<le> ?B * ?T" by simp
  have C_nn: "(0::real) \<le> ?C" by simp
  have BLCA_pos: "?B * ?L + ?C + ?A > 0" using A_pos BL_nn C_nn by linarith
  have BTCA_pos: "?B * ?T + ?C + ?A > 0" using A_pos BT_nn C_nn by linarith
  have larg_p1_pos: "?Larg + 1 > 0" by simp
  have L_p1_pos: "?L + 1 > 0" by simp
  have L_ge_T_real: "?L \<ge> ?T" using L_ge_T by simp

  have arg_le_real: "?A * (?Larg + 1) \<le> ?B * ?L + ?C + ?A"
  proof -
    have "real (A * (Larg + 1)) \<le> real (B * L + C + A)"
      using arg_le by (simp only: of_nat_le_iff)
    thus ?thesis by (simp add: algebra_simps)
  qed

  have ratio_lower: "?A * (?L + 1) / (?B * ?L + ?C + ?A) \<le> (?L + 1) / (?Larg + 1)"
  proof -
    have "?A * (?Larg + 1) * (?L + 1) \<le> (?B * ?L + ?C + ?A) * (?L + 1)"
      using arg_le_real L_p1_pos by (intro mult_right_mono) auto
    hence step1: "?A * (?L + 1) * (?Larg + 1) \<le> (?B * ?L + ?C + ?A) * (?L + 1)"
      by (simp add: mult.commute)
    have "?A * (?L + 1) / (?B * ?L + ?C + ?A) \<le> (?L + 1) / (?Larg + 1)"
      using step1 BLCA_pos larg_p1_pos
      by (simp add: divide_simps mult.commute)
    thus ?thesis .
  qed

  have ratio_min: "?A * (?T + 1) / (?B * ?T + ?C + ?A)
               \<le> ?A * (?L + 1) / (?B * ?L + ?C + ?A)"
  proof -
    have key: "(?A + ?C - ?B) * (?L - ?T) \<ge> 0"
      using L_ge_T_real AC_ge_B by simp
    hence "(?A + ?C) * ?L + ?B * ?T \<ge> (?A + ?C) * ?T + ?B * ?L"
      by (simp add: algebra_simps)
    hence cross: "(?L + 1) * (?B * ?T + ?C + ?A)
                \<ge> (?T + 1) * (?B * ?L + ?C + ?A)"
      by (simp add: algebra_simps)
    have "?A * ((?T + 1) * (?B * ?L + ?C + ?A))
        \<le> ?A * ((?L + 1) * (?B * ?T + ?C + ?A))"
      using cross A_pos by (simp add: mult_left_mono)
    hence "?A * (?T + 1) * (?B * ?L + ?C + ?A)
        \<le> ?A * (?L + 1) * (?B * ?T + ?C + ?A)"
      by (simp add: algebra_simps)
    thus ?thesis using BLCA_pos BTCA_pos
      by (simp add: divide_simps mult.commute)
  qed

  have combined: "?A * (?T + 1) / (?B * ?T + ?C + ?A) \<le> (?L + 1) / (?Larg + 1)"
    using ratio_lower ratio_min by linarith

  have ratio_at_T_pos: "?A * (?T + 1) / (?B * ?T + ?C + ?A) > 0"
    using A_pos BTCA_pos by simp

  have log_le: "log 2 (?A * (?T + 1) / (?B * ?T + ?C + ?A))
              \<le> log 2 ((?L + 1) / (?Larg + 1))"
    using log_mono[OF _ ratio_at_T_pos combined] by simp

  have log_div_form: "log 2 ((?L + 1) / (?Larg + 1))
                   = log 2 (?L + 1) - log 2 (?Larg + 1)"
    using L_p1_pos larg_p1_pos by (simp add: log_divide)

  have c_bound_form: "c * log 2 (?A * (?T + 1) / (?B * ?T + ?C + ?A)) \<ge> D_real"
  proof -
    have e1: "real (A * (T+1)) = ?A * (?T + 1)" by (simp add: algebra_simps)
    have e2: "real (B * T + C + A) = ?B * ?T + ?C + ?A" by simp
    have e3: "real (A * (T+1)) / real (B * T + C + A)
            = ?A * (?T + 1) / (?B * ?T + ?C + ?A)" using e1 e2 by simp
    show ?thesis using c_bound by (simp only: e3)
  qed

  have "D_real \<le> c * log 2 (?A * (?T + 1) / (?B * ?T + ?C + ?A))"
    using c_bound_form .
  also have "\<dots> \<le> c * log 2 ((?L + 1) / (?Larg + 1))"
    using log_le c_nonneg by (simp add: mult_left_mono)
  also have "\<dots> = c * (log 2 (?L + 1) - log 2 (?Larg + 1))"
    using log_div_form by simp
  also have "\<dots> = c * log 2 (?L + 1) - c * log 2 (?Larg + 1)"
    by (simp add: algebra_simps)
  finally show ?thesis by linarith
qed

end
