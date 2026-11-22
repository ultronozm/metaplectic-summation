import MetaplecticSummation.MultiplicativeMeasure

/-! Integrability of weights with power decay on local units. -/
noncomputable section
namespace MetaplecticPoisson
open MeasureTheory Set Metric
open Classical

private theorem integrable_small_units_rpow {K : Type*} [NormedField K] [ProperSpace K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure Kˣ) [μ.IsHaarMeasure]
    (c : Kˣ) (hc : ‖c.val‖ < 1) {e : ℝ} (he : 0 < e) :
    Integrable ({x : Kˣ | ‖x.val‖ ≤ 1}.indicator fun x => ‖x.val‖^e) μ := by
  let r := ‖c.val‖
  have hr : 0 < r := norm_pos_iff.mpr c.ne_zero
  let D := closedBall (0:K) 1 ∩ {z : K | r ≤ ‖z‖}
  have hD : IsCompact D := (isCompact_closedBall _ _).inter_right (isClosed_le continuous_const continuous_norm)
  let S := (Units.val : Kˣ → K) ⁻¹' D
  have hS : IsCompact S := Units.isEmbedding_val₀.isInducing.isCompact_preimage' hD (by
    intro z hz
    exact ⟨Units.mk0 z (norm_pos_iff.mp (hr.trans_le hz.2)),rfl⟩)
  let T (i : ℕ) := (fun x : Kˣ => (c^i)⁻¹*x) ⁻¹' S
  have hT (i : ℕ) : IsCompact (T i) := (Homeomorph.mulLeft ((c^i)⁻¹)).isCompact_preimage.mpr hS
  have ht (i : ℕ) : μ (T i) = μ S := measure_preimage_mul μ _ _
  have hnorm (x : Kˣ) (i : ℕ) : ‖(((c^i)⁻¹*x).val)‖ = ‖x.val‖ / r^i := by
    simp only [Units.val_mul,Units.val_inv_eq_inv_val,Units.val_pow_eq_pow_val,norm_mul,norm_inv,norm_pow,
      r,div_eq_inv_mul]
  let f (x : Kˣ) := ‖x.val‖^e
  have hcont : Continuous f := (Real.continuous_rpow_const he.le).comp Units.continuous_val.norm
  have hi (i : ℕ) := hcont.continuousOn.integrableOn_compact (μ := μ) (hT i)
  apply (integrable_indicator_iff (isClosed_le Units.continuous_val.norm continuous_const).measurableSet).mpr
  apply (integrableOn_iUnion_of_summable_integral_norm hi ?_).mono_set
  · intro x hx
    obtain ⟨i,hlo,hhi⟩ := exists_nat_pow_near_of_lt_one (norm_pos_iff.mpr x.ne_zero) hx hr hc
    apply mem_iUnion.mpr ⟨i,?_⟩
    change ((c^i)⁻¹*x).val ∈ D
    simp only [D,mem_inter_iff,mem_closedBall_zero_iff,mem_setOf_eq]
    rw [hnorm]
    refine ⟨(div_le_one (pow_pos hr _)).mpr hhi,(le_div_iff₀ (pow_pos hr _)).mpr ?_⟩
    simpa only [pow_succ'] using hlo.le
  · apply Summable.of_nonneg_of_le (fun i => integral_nonneg fun x => norm_nonneg (f x)) _
      ((summable_geometric_of_lt_one (Real.rpow_nonneg hr.le e) (Real.rpow_lt_one hr.le hc he)).mul_left (μ.real S))
    intro i
    have hv : ∫ _ : Kˣ in T i, (r^e)^i ∂μ = μ.real S * (r^e)^i := by
      simp only [integral_const,Measure.real,Measure.restrict_apply_univ,ht,smul_eq_mul]
    apply le_trans _ hv.le
    apply setIntegral_mono_on (hi i).norm (integrableOn_const (hT i).measure_lt_top.ne) (hT i).isClosed.measurableSet
    intro x hx
    have hb := (show ((c^i)⁻¹*x).val ∈ D from hx).1
    rw [mem_closedBall_zero_iff,hnorm,div_le_one (pow_pos hr _)] at hb
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg x.val) e)]
    exact (Real.rpow_le_rpow (norm_nonneg _) hb he.le).trans_eq (by
      rw [← Real.rpow_natCast_mul hr.le,mul_comm,Real.rpow_mul_natCast hr.le])

/-- Positive power decay both at zero and at infinity is integrable for
multiplicative Haar measure. -/
theorem integrable_units_min_rpow {K : Type*} [NormedField K] [ProperSpace K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure Kˣ) [μ.IsHaarMeasure] [μ.IsInvInvariant]
    (c : Kˣ) (hc : ‖c.val‖ < 1) {e : ℝ} (he : 0 < e) :
    Integrable (fun x : Kˣ => min (‖x.val‖^e) (‖x.val‖^(-e))) μ := by
  let S := {x : Kˣ | ‖x.val‖ ≤ 1}
  let f := S.indicator (fun x : Kˣ => ‖x.val‖^e)
  have hf : Integrable f μ := integrable_small_units_rpow μ c hc he
  have hm : Measurable (fun x : Kˣ => min (‖x.val‖^e) (‖x.val‖^(-e))) :=
    (Units.continuous_val.norm.measurable.pow_const _).min (Units.continuous_val.norm.measurable.pow_const _)
  apply (hf.add hf.comp_inv).mono' hm.aestronglyMeasurable
  filter_upwards with x
  have hx := norm_pos_iff.mpr x.ne_zero
  have nonneg (z : Kˣ) : 0 ≤ f z := indicator_nonneg (fun u _ => Real.rpow_nonneg (norm_nonneg u.val) _) _
  rw [Real.norm_of_nonneg (le_min (Real.rpow_nonneg hx.le _) (Real.rpow_nonneg hx.le _))]
  change _ ≤ f x + f x⁻¹
  by_cases h : x ∈ S
  · exact (min_le_left ..).trans ((show ‖x.val‖^e = f x from (indicator_of_mem h (fun z : Kˣ => ‖z.val‖^e)).symm).le.trans
      (le_add_of_nonneg_right (nonneg _)))
  · have hx' : x⁻¹ ∈ S := by
      change ‖(x⁻¹).val‖ ≤ 1
      rw [Units.val_inv_eq_inv_val,norm_inv]
      exact inv_le_one_of_one_le₀ (le_of_not_ge h)
    apply (min_le_right ..).trans
    apply le_trans _ (le_add_of_nonneg_left (nonneg _))
    rw [show f x⁻¹ = ‖(x⁻¹).val‖^e from indicator_of_mem hx' (fun z : Kˣ => ‖z.val‖^e), Units.val_inv_eq_inv_val,norm_inv,
      Real.inv_rpow hx.le,Real.rpow_neg hx.le]

end MetaplecticPoisson
