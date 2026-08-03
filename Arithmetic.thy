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

text \<open>Bridging powers, ceilings and logarithms.  These convert the balancing
      depth bound  a + c * log 2 (n + 1)  into polynomial size bounds for the
      connective-template translation between Frege systems.\<close>

lemma nat_le_nat_ceiling:
  fixes m :: nat and x :: real
  assumes "real m \<le> x"
  shows "m \<le> nat \<lceil>x\<rceil>"
proof -
  have "\<lceil>real m\<rceil> \<le> \<lceil>x\<rceil>" using assms by (rule ceiling_mono)
  hence "int m \<le> \<lceil>x\<rceil>" by simp
  hence "nat (int m) \<le> nat \<lceil>x\<rceil>" by (rule nat_mono)
  thus ?thesis by simp
qed

lemma ceiling_nat_real_lower:
  fixes x :: real
  assumes "0 \<le> x"
  shows "x \<le> real (nat \<lceil>x\<rceil>)"
proof -
  have nn: "0 \<le> \<lceil>x\<rceil>" using assms by linarith
  have "real (nat \<lceil>x\<rceil>) = of_int \<lceil>x\<rceil>" using nn by simp
  moreover have "x \<le> of_int \<lceil>x\<rceil>" by linarith
  ultimately show ?thesis by linarith
qed

lemma ceiling_nat_real_upper:
  fixes x :: real
  assumes "0 \<le> x"
  shows "real (nat \<lceil>x\<rceil>) \<le> x + 1"
proof -
  have nn: "0 \<le> \<lceil>x\<rceil>" using assms by linarith
  have "real (nat \<lceil>x\<rceil>) = of_int \<lceil>x\<rceil>" using nn by simp
  moreover have "of_int \<lceil>x\<rceil> \<le> x + 1" by linarith
  ultimately show ?thesis by linarith
qed

lemma powr_log_swap:
  fixes base other c :: real
  assumes "0 < base" and "0 < other"
  shows "base powr (c * log 2 other) = other powr (c * log 2 base)"
proof -
  have "c * log 2 other * ln base = c * log 2 base * ln other"
    unfolding log_def by simp
  thus ?thesis
    using assms by (simp add: powr_def)
qed

lemma nat_power_le_powr:
  fixes T :: nat and x :: real
  assumes "1 \<le> T" and "0 \<le> x"
  shows "real (T ^ nat \<lceil>x\<rceil>) \<le> real T * real T powr x"
proof -
  have T1: "(1::real) \<le> real T" using assms(1) by simp
  have Tpos: "(0::real) < real T" using assms(1) by simp
  have "real (T ^ nat \<lceil>x\<rceil>) = real T ^ nat \<lceil>x\<rceil>" by simp
  also have "\<dots> = real T powr real (nat \<lceil>x\<rceil>)"
    using Tpos by (simp add: powr_realpow)
  also have "\<dots> \<le> real T powr (x + 1)"
    using ceiling_nat_real_upper[OF assms(2)] T1 by (simp add: powr_mono)
  also have "\<dots> = real T powr x * real T powr 1"
    by (simp add: powr_add)
  also have "\<dots> = real T * real T powr x"
    using Tpos by (simp add: algebra_simps)
  finally show ?thesis .
qed

lemma powr_le_nat_power:
  fixes y :: nat and r :: real
  assumes "1 \<le> y" and "0 \<le> r"
  shows "real y powr r \<le> real (y ^ nat \<lceil>r\<rceil>)"
proof -
  have y1: "(1::real) \<le> real y" using assms(1) by simp
  have ypos: "(0::real) < real y" using assms(1) by simp
  have "real y powr r \<le> real y powr real (nat \<lceil>r\<rceil>)"
    using ceiling_nat_real_lower[OF assms(2)] y1 by (simp add: powr_mono)
  also have "\<dots> = real y ^ nat \<lceil>r\<rceil>"
    using ypos by (simp add: powr_realpow)
  also have "\<dots> = real (y ^ nat \<lceil>r\<rceil>)" by simp
  finally show ?thesis .
qed

lemma power_nat_exact_poly:
  fixes expo :: nat
  shows "\<exists> p :: nat poly. \<forall> n. poly p n = (n + 1) ^ expo"
proof
  show "\<forall> n. poly ((monom 1 1 + 1) ^ expo) n = (n + 1) ^ expo"
    by (simp add: poly_monom)
qed

lemma power_ceiling_log_poly_bound:
  fixes T :: nat and a c :: real
  assumes "1 \<le> T" and "0 \<le> a" and "0 \<le> c"
  shows "\<exists> p :: nat poly. \<forall> n :: nat.
           T ^ (nat \<lceil>a + c * log 2 (real n + 1)\<rceil>) \<le> T ^ (nat \<lceil>a\<rceil> + 1) * poly p n"
proof -
  have T1: "(1::real) \<le> real T" using assms(1) by simp
  have Tpos: "(0::real) < real T" using assms(1) by simp
  have logT_nn: "0 \<le> log 2 (real T)" using T1 by simp
  have cT_nn: "0 \<le> c * log 2 (real T)"
    using assms(3) logT_nn by (rule mult_nonneg_nonneg)
  obtain p :: "nat poly" where p_val: "\<forall> n. poly p n = (n + 1) ^ nat \<lceil>c * log 2 (real T)\<rceil>"
    using power_nat_exact_poly by blast
  show ?thesis
  proof (rule exI, rule allI)
    fix n :: nat
    have yconv: "real n + 1 = real (n + 1)" by simp
    have y1: "(1::nat) \<le> n + 1" by simp
    have ypos: "(0::real) < real (n + 1)" by simp
    have logy_nn: "0 \<le> log 2 (real (n + 1))"
      using ypos by simp
    have cy_nn: "0 \<le> c * log 2 (real (n + 1))"
      using assms(3) logy_nn by (rule mult_nonneg_nonneg)
    have xnn: "0 \<le> a + c * log 2 (real (n + 1))"
      using assms(2) cy_nn by linarith
    have powr_a_nn: "0 \<le> real T powr a" by simp
    have first: "real (T ^ nat \<lceil>a + c * log 2 (real (n + 1))\<rceil>)
                   \<le> real T * real T powr (a + c * log 2 (real (n + 1)))"
      using nat_power_le_powr[OF assms(1) xnn] .
    have split: "real T powr (a + c * log 2 (real (n + 1)))
               = real T powr a * real T powr (c * log 2 (real (n + 1)))"
      by (simp add: powr_add)
    have swap: "real T powr (c * log 2 (real (n + 1)))
              = real (n + 1) powr (c * log 2 (real T))"
      using powr_log_swap[OF Tpos ypos] .
    have second: "real T powr a \<le> real (T ^ nat \<lceil>a\<rceil>)"
      using powr_le_nat_power[OF assms(1) assms(2)] .
    have third: "real (n + 1) powr (c * log 2 (real T))
                   \<le> real ((n + 1) ^ nat \<lceil>c * log 2 (real T)\<rceil>)"
      using powr_le_nat_power[OF y1 cT_nn] .
    have prod_le: "real T powr a * real (n + 1) powr (c * log 2 (real T))
                 \<le> real (T ^ nat \<lceil>a\<rceil>) * real ((n + 1) ^ nat \<lceil>c * log 2 (real T)\<rceil>)"
      using second third powr_a_nn by (intro mult_mono) simp_all
    have "real (T ^ nat \<lceil>a + c * log 2 (real (n + 1))\<rceil>)
        \<le> real T * (real (T ^ nat \<lceil>a\<rceil>) * real ((n + 1) ^ nat \<lceil>c * log 2 (real T)\<rceil>))"
    proof -
      have "real (T ^ nat \<lceil>a + c * log 2 (real (n + 1))\<rceil>)
          \<le> real T * (real T powr a * real (n + 1) powr (c * log 2 (real T)))"
        using first split swap by simp
      also have "\<dots> \<le> real T * (real (T ^ nat \<lceil>a\<rceil>) * real ((n + 1) ^ nat \<lceil>c * log 2 (real T)\<rceil>))"
        using prod_le Tpos by (intro mult_left_mono) simp_all
      finally show ?thesis .
    qed
    hence real_chain: "real (T ^ nat \<lceil>a + c * log 2 (real (n + 1))\<rceil>)
        \<le> real (T * (T ^ nat \<lceil>a\<rceil> * (n + 1) ^ nat \<lceil>c * log 2 (real T)\<rceil>))"
      by simp
    have nat_chain: "T ^ nat \<lceil>a + c * log 2 (real (n + 1))\<rceil>
        \<le> T * (T ^ nat \<lceil>a\<rceil> * (n + 1) ^ nat \<lceil>c * log 2 (real T)\<rceil>)"
      using real_chain by (simp only: of_nat_le_iff)
    have rhs_eq: "T * (T ^ nat \<lceil>a\<rceil> * (n + 1) ^ nat \<lceil>c * log 2 (real T)\<rceil>)
        = T ^ (nat \<lceil>a\<rceil> + 1) * poly p n"
      using p_val by (simp add: algebra_simps)
    show "T ^ nat \<lceil>a + c * log 2 (real n + 1)\<rceil> \<le> T ^ (nat \<lceil>a\<rceil> + 1) * poly p n"
    proof -
      have "T ^ nat \<lceil>a + c * log 2 (real n + 1)\<rceil>
          = T ^ nat \<lceil>a + c * log 2 (real (n + 1))\<rceil>"
        by (simp only: yconv)
      also have "\<dots> \<le> T * (T ^ nat \<lceil>a\<rceil> * (n + 1) ^ nat \<lceil>c * log 2 (real T)\<rceil>)"
        using nat_chain .
      also have "\<dots> = T ^ (nat \<lceil>a\<rceil> + 1) * poly p n"
        using rhs_eq .
      finally show ?thesis .
    qed
  qed
qed


end
