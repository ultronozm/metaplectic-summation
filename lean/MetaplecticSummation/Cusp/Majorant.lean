import MetaplecticSummation.ThetaMajorant

/-! The uniform growth bound for the contracted scalar majorant in the cusp. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField Filter
open Classical
variable {F : Type} [Field F] [NumberField F]

omit [NumberField F] in
theorem localThetaBound_antitone {κ C s t : ℝ} (v : Place F) (hκ : 0 ≤ κ) (hC : 0 ≤ C)
    (hs : 0 < s) (hst : s ≤ t) : localThetaBound κ v C t ≤ localThetaBound κ v C s := by
  have h (a : ℝ) (ha : a ≤ 0) := Real.rpow_le_rpow_of_nonpos hs hst ha
  cases v with
  | inl w =>
    exact mul_le_mul_of_nonneg_left (min_le_min (h _ (neg_nonpos.mpr hκ)) (h _ (by norm_num))) hC
  | inr p =>
    dsimp only [localThetaBound]
    by_cases ht : t ≤ C
    · rw [ite_eq_left ht,ite_eq_left (hst.trans ht)]
      exact mul_le_mul_of_nonneg_left (h _ (neg_nonpos.mpr hκ)) hC
    · rw [ite_eq_right ht]
      split
      · exact mul_nonneg hC (Real.rpow_nonneg hs.le _)
      · exact le_rfl

/-- Summing the isotropically contracted majorant costs at most the cube of the cusp
height. The constants B account for a fixed compact family of right translations. -/
theorem cusp_majorant_sum {κ : ℝ} (hκ : 0 ≤ κ) (hk : κ ≤ 1) (C B S : Place F → ℝ)
    (hC : ∀ v, 1 ≤ C v) (hB : ∀ v, 1 ≤ B v) (hS : ∀ v, 1 ≤ S v)
    (c₁ : ∀ᶠ v in cofinite, C v = 1) (b₁ : ∀ᶠ v in cofinite, B v = 1)
    (s₁ : ∀ᶠ v in cofinite, S v = 1) {q : ℝ} (hq : 1 ≤ q) (hprod : ∏ᶠ v, S v = q) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k : ℕ, let a := fun v => (B v*S v^k)⁻¹
      Summable (thetaMajorant κ C a) ∧ (∑' z, thetaMajorant κ C a z) ≤ M*q^(3*k) := by
  obtain ⟨T,hT,estimate⟩ := theta_majorant_bound hκ hk C (fun v => zero_le_one.trans (hC v)) (fun _ => hC _) c₁
  let V := ∏ᶠ v, B v
  have hV : 1 ≤ V := one_le_finprod hB
  let e := 2+κ
  refine ⟨T*V^e,mul_nonneg hT (Real.rpow_nonneg (zero_le_one.trans hV) _),fun k => ?_⟩
  let a := fun v => (B v*S v^k)⁻¹
  have pos (v) : 0 < a v := inv_pos.mpr (mul_pos (zero_lt_one.trans_le (hB v)) (pow_pos (zero_lt_one.trans_le (hS v)) _))
  have co : ∀ᶠ v in cofinite, a v = 1 := by filter_upwards [b₁,s₁] with v hb hs; simp [a,hb,hs]
  obtain ⟨hs,h⟩ := estimate a pos co
  have he : (∏ᶠ v, a v) = (V*q^k)⁻¹ := by
    rw [show (∏ᶠ v, a v) = (∏ᶠ v, B v*S v^k)⁻¹ from finprod_inv_distrib _,
      finprod_mul_distrib (g := fun v => S v ^ k) (eventually_cofinite.mp b₁) ((show Function.HasFiniteMulSupport S from eventually_cofinite.mp s₁).pow k),← finprod_pow (eventually_cofinite.mp s₁),hprod]
  have hqk := one_le_pow₀ (n := k) hq
  have scale : (∏ᶠ v, a v)^(-2-κ) = V^e*(q^k)^e := by
    rw [he,show -2-κ = -e by dsimp [e]; ring,Real.rpow_neg (by positivity),
      Real.inv_rpow (mul_nonneg (zero_le_one.trans hV) (zero_le_one.trans hqk)),inv_inv,
      Real.mul_rpow (zero_le_one.trans hV) (zero_le_one.trans hqk)]
  refine ⟨hs,h.trans ?_⟩
  rw [scale,← mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hT (Real.rpow_nonneg (zero_le_one.trans hV) _))
  calc
    (q^k)^e ≤ (q^k)^(3:ℝ) := Real.rpow_le_rpow_of_exponent_le hqk (by dsimp [e]; linarith)
    _ = q^(3*k) := by rw [← Nat.cast_ofNat (n := 3),Real.rpow_natCast,← pow_mul,Nat.mul_comm]

end MetaplecticPoisson.Datum
