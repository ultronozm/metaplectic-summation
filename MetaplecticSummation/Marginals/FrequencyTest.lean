import MetaplecticSummation.Marginals.TestedRadon
import MetaplecticSummation.RadonDecay

/-! Testing the defining integral of the reverse marginal away from frequency zero. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField MeasureTheory Filter Set
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n) (v : Place F)
local notation "K" => LocalField F v
local notation "dx" => selfDual F d.character v
local notation "m" => modulus F v

private theorem radon_frequency_bound (Φ Ψ : d.schwartz v) (hΨ : Ψ.val = d.integralTransform v Φ.val) (c : Kˣ) :
    ∃ D : Kˣ → ℝ, Continuous D ∧ ∀ u y,
      ‖d.hat v (fun t => (d.radonAt v Φ.val t).1 c y) u.val‖ ≤ D u*((1+‖y‖)^3)⁻¹ := by
  let s : ℂ := Real.sqrt (m (n:K))
  obtain ⟨C,hC,H⟩ := d.schwartz_chart_growth v Ψ 3 (by decide)
  let A := 2+2/(m c.val)
  have pos (u : Kˣ) : 0 < m u.val := by cases v <;> simp [modulus,norm_pos_iff,u.ne_zero,pow_pos]
  have hA : 0 ≤ A := by dsimp [A]; positivity [pos c]
  let D (u : Kˣ) := ‖s‖*(m u.val)^(n-1)*C*A^3 / ((m u.val)^n)^3
  have cm : Continuous fun u : Kˣ => m u.val := by
    cases v <;> first | exact Units.continuous_val.norm.pow _ | exact Units.continuous_val.norm
  have cD : Continuous D := (((continuous_const.mul (cm.pow _)).mul continuous_const).mul continuous_const).div
    ((cm.pow _).pow 3) (fun u => pow_ne_zero _ (pow_ne_zero _ (pos u).ne'))
  refine ⟨D,cD,fun u y => ?_⟩
  let r := max (m c.val) (m y)
  let k := (m u.val)^n
  have hr : 0 < r := (pos c).trans_le (le_max_left ..)
  have hk : 0 < k := pow_pos (pos u) _
  have hy : 1+‖y‖ ≤ A*r := by
    have h := mul_le_mul_of_nonneg_left (le_max_left (m c.val) (m y)) (show 0 ≤ 2/(m c.val) by positivity [pos c])
    rw [div_mul_cancel₀ _ (pos c).ne'] at h
    change 2 ≤ (2/m c.val)*r at h
    by_cases hy : ‖y‖ ≤ 1
    · dsimp only [A]; nlinarith
    · have hmy : ‖y‖ ≤ m y := by
        cases v with
        | inr p => exact le_rfl
        | inl w => exact le_self_pow₀ (le_of_not_ge hy) w.mult_ne_zero
      have h' : ‖y‖ ≤ r := hmy.trans (le_max_right ..)
      dsimp only [A]; nlinarith
  let a := u^n*c
  let z := u.val^n*y
  have radius : max (m a.val) (m z) = k*r := by
    rw [show m a.val = k*m c.val by cases v <;> simp [a,k,modulus,mul_pow,pow_right_comm],
      show m z = k*m y by cases v <;> simp [z,k,modulus,mul_pow,pow_right_comm],mul_max_of_nonneg _ _ hk.le]
  have h := (H (a.val,z) (fun h => a.ne_zero (congrArg Prod.fst h))).1
  have hb : ‖Ψ.val.1 a z‖ ≤ C*((k*r)^3)⁻¹ := by
    apply (show ‖Ψ.val.1 a z‖ ≤ _ from by simpa only [xChart,dite_eq_left a.ne_zero,Units.mk0_val,radius] using h).trans
    apply mul_le_mul_of_nonneg_left _ hC
    exact (min_le_right ..).trans_eq (by rw [Real.rpow_neg (mul_nonneg hk.le hr.le),Real.rpow_natCast])
  have h' : ‖Ψ.val.1 a z‖*(1+‖y‖)^3 ≤ C*A^3/k^3 := by
    calc
      _ ≤ C*((k*r)^3)⁻¹ * (A*r)^3 := mul_le_mul hb (pow_le_pow_left₀ (by positivity) hy 3) (by positivity)
          (mul_nonneg hC (by positivity))
      _ = _ := by rw [mul_pow,mul_pow]; field_simp
  rw [d.hat_radon_scaled_charts,← hΨ,norm_mul,norm_mul,norm_pow,show ‖(m u.val : ℂ)‖ = ‖m u.val‖ from Complex.norm_real _,Real.norm_of_nonneg (pos u).le,
    ← div_eq_mul_inv,le_div_iff₀ (by positivity),mul_assoc]
  exact (mul_le_mul_of_nonneg_left h' (mul_nonneg (norm_nonneg s) (pow_nonneg (pos u).le _))).trans_eq
    (by dsimp only [D,k]; ring)

/-- On a compact set of nonzero frequencies, the Fourier transform of the Radon
slice has a joint integrable majorant in the frequency and transverse variables. -/
theorem integrable_radon_frequency_test (Φ Ψ : d.schwartz v) (hΨ : Ψ.val = d.integralTransform v Φ.val) (c : Kˣ) {ρ : K → ℂ}
    (hc : Continuous ρ) (hs : HasCompactSupport ρ) (hz : 0 ∉ tsupport ρ) :
    let R (y t : K) := (d.radonAt v Φ.val t).1 c y
    Integrable (fun z : K × K => d.hat v (R z.1) z.2 * ρ z.2) ((dx).prod dx) := by
  intro R
  let : (dx).IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  have hR : RapidRadonValues R := (d.schwartz_radon_rapid v Φ).1.comp (fun y : K => (c,y))
    (continuous_const.prodMk continuous_id)
  have chat := (hR.fourier dx (d.integrable_local_inv_cube v) (d.character.continuous_localValue v)
    (d.character.norm_localValue v)).1
  obtain ⟨D,cD,hD⟩ := d.radon_frequency_bound v Φ Ψ hΨ c
  let S := (Units.val : Kˣ → K) ⁻¹' tsupport ρ
  have hS : IsCompact S := Units.isEmbedding_val₀.isInducing.isCompact_preimage' hs (fun x hx =>
    ⟨Units.mk0 x (fun h => hz (h ▸ hx)),rfl⟩)
  obtain ⟨B,hB⟩ := hS.bddAbove_image cD.continuousOn
  have meas : Continuous fun z : K × K => d.hat v (R z.1) z.2*ρ z.2 :=
    chat.mul (hc.comp continuous_snd)
  apply (((d.integrable_local_inv_cube v).const_mul B).mul_prod (hc.integrable_of_hasCompactSupport (μ := dx) hs).norm).mono'
    meas.aestronglyMeasurable
  filter_upwards with z
  simp only [norm_mul]
  by_cases h : z.2 ∈ tsupport ρ
  · let u := Units.mk0 z.2 (fun h' => hz (h' ▸ h))
    have hu : u ∈ S := h
    exact mul_le_mul_of_nonneg_right ((hD u z.1).trans (mul_le_mul_of_nonneg_right (hB (mem_image_of_mem D hu))
      (by positivity))) (norm_nonneg _)
  · simp only [image_eq_zero_of_notMem_tsupport h,norm_zero,mul_zero,le_refl]

/-- The weak reverse marginal before the reciprocal change of the transverse
coordinate. The hypotheses apply to test sections and their defining integral
at all number-field places. -/
theorem tested_marginal_of_charts (Φ Ψ : d.schwartz v) (hΨ : Ψ.val = d.integralTransform v Φ.val)
    (c : Kˣ) {ρ : K → ℂ} (hc : Continuous ρ) (hs : HasCompactSupport ρ) (hz : 0 ∉ tsupport ρ) :
    (Real.sqrt (m (n : K)) : ℂ) * d.lineIntegral v (fun u => d.marginal v Ψ (u^n*c) * ρ u.val) =
      ∫ y, ∫ t, d.hat v ρ t * (d.radonAt v Φ.val t).1 c y ∂dx ∂dx := by
  let : (dx).IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  let R (y t : K) := (d.radonAt v Φ.val t).1 c y
  let T (u : K) := (∫ y, d.hat v (R y) u ∂dx) * ρ u
  have hi := d.integrable_radon_frequency_test v Φ Ψ hΨ c hc hs hz
  have rapid : RapidRadonValues R := (d.schwartz_radon_rapid v Φ).1.comp (fun y : K => (c,y))
    (continuous_const.prodMk continuous_id)
  rw [← d.integral_lineMeasure,← integral_const_mul]
  calc
    _ = ∫ u, (m u.val) • T u.val ∂(d.lineMeasure v) := by
      apply integral_congr_ae
      filter_upwards with u
      rw [← mul_assoc,d.marginal_scaled_radon_of_charts v Φ Ψ hΨ]
      simp only [T,Complex.real_smul,mul_assoc,R]
    _ = ∫ u, T u ∂dx := (d.lineMeasure_modulus v T).2
    _ = ∫ y, ∫ u, d.hat v (R y) u * ρ u ∂dx ∂dx := by
      simpa only [T,integral_mul_const] using
        (integral_integral_swap (f := fun y u => d.hat v (R y) u * ρ u) hi).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with y
      rw [d.hat_pair_swap v (f := R y) (g := ρ) (rapid.1.comp (f := fun t => (y,t)) (continuous_const.prodMk continuous_id))
        hc (rapid.integrable dx (d.integrable_local_inv_cube v) y) (hc.integrable_of_hasCompactSupport hs)]
      simp only [R,mul_comm]

/-- A test section at a real, complex or finite place satisfies the tested
Y-chart formula in Appendix A. -/
theorem tested_marginal_slice_on_test (Φ : d.schwartz v) (hΦ : Φ.val ∈ d.testSet v) (s : Kˣ)
    {ρ : K → ℂ} (hc : Continuous ρ) (hs : HasCompactSupport ρ) (hz : 0 ∉ tsupport ρ) :
    (Real.sqrt (m (n : K)) : ℂ) * d.lineIntegral v
      (fun u => d.marginal v (d.transformTest v Φ hΦ) (u^n*s) * ρ u.val) =
      d.lineIntegral v (fun u => ∫ t, d.hat v ρ t *
        (∫ y, d.marginalSlice v Φ.val s u t y ∂dx) ∂dx) :=
  (d.tested_marginal_of_charts v Φ (d.transformTest v Φ hΦ) rfl s hc hs hz).trans
    (d.tested_radon_reciprocal v hΦ.1 s _)

end MetaplecticPoisson.Datum
