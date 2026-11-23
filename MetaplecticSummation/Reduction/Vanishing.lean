import MetaplecticSummation.Reduction.FiberIntegral

/-! The integral-to-pointwise vanishing argument at the end of Proposition B.6. -/

noncomputable section
namespace MetaplecticPoisson

open MeasureTheory Set Topology NumberField
open scoped MatrixGroups Pointwise ENNReal

variable (F : Type) [Field F] [NumberField F]
local notation "G" => AdelicSL F
local notation "X" => SLArithmeticQuotient F
local notation "Y" => UnipotentArithmeticQuotient F
local notation "π" => (Quotient.mk _ : G → X)
local notation "η" => Exists.choose (ExistsUnique.exists (Datum.exists_quotient_measure (F := F)))
local instance : MeasurableSpace (Datum.AdeleQuotient F) := borel _
local instance : BorelSpace (Datum.AdeleQuotient F) := ⟨rfl⟩

instance (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsOpenPosMeasure] :
    (slQuotientMeasure F μ).IsOpenPosMeasure := by
  constructor
  intro U ho hn hzero
  have hop : IsOpen (π ⁻¹' U) := ho.preimage continuous_quotient_mk'
  have hU : MeasurableSet U := measurableSet_quotient.mpr hop.measurableSet
  rw [slQuotientMeasure, Measure.map_apply measurable_quotient_mk'' hU, Measure.restrict_apply hop.measurableSet] at hzero
  have hinv (γ : rationalSL F) : γ • (π ⁻¹' U) = π ⁻¹' U := by
    ext x
    rw [mem_smul_set_iff_inv_smul_mem]
    change π (γ.val⁻¹ * x) ∈ U ↔ π x ∈ U
    have he : π (γ.val⁻¹ * x) = π x := Quotient.sound (QuotientGroup.rightRel_apply.mpr (by simp))
    rw [he]
  obtain ⟨q, hq⟩ := hn
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  exact (hop.measure_ne_zero μ ⟨x,hq⟩) ((isFundamentalDomain_rationalSL F μ).measure_zero_of_invariant _ hinv hzero)

/-- If a continuous function's square is an absolutely integrable rational orbit sum
and all the compact-fiber integrals vanish, the function vanishes at every point. -/
theorem eq_zero_of_unipotentFiber_cancellation (μ : Measure G)
    [μ.IsMulLeftInvariant] [μ.IsOpenPosMeasure] [SFinite μ]
    {f : Y → ℂ} (hf : Measurable f)
    (habs : (∫⁻ x, arithmeticOrbitSum F (fun y => ‖f y‖ₑ) x ∂slQuotientMeasure F μ) < ⊤)
    {δ : X → ℝ} (hδ : Continuous δ)
    (hsq : ∀ x, arithmeticOrbitSum F f x = ((δ x ^ 2 : ℝ) : ℂ))
    (hcancel : ∀ x : G, (∫ q, f (unipotentFiber F x q) ∂η) = 0) :
    δ = 0 := by
  have zero (z : AdelicUnipotentQuotient F) : unipotentFiberIntegral F f z = 0 := by
    induction z using Quotient.inductionOn with | _ x => exact hcancel x
  have he := integral_arithmeticOrbitSum_eq_fiberIntegral F μ hf habs
  simp only [hsq, zero, integral_zero, integral_complex_ofReal, Complex.ofReal_eq_zero] at he
  have hi := (integral_arithmeticOrbitSum F μ hf ((integrable_iff_arithmeticOrbitSum_norm F μ hf).mpr habs)).1.re
  have hi₂ : Integrable (fun x => δ x ^ 2) (slQuotientMeasure F μ) := by
    simpa only [hsq, RCLike.re_to_complex, Complex.ofReal_re] using hi
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (δ x)) hi₂).mp he
  apply Measure.eq_of_ae_eq (μ := slQuotientMeasure F μ) _ hδ continuous_zero
  filter_upwards [hae] with x hx
  change δ x = 0
  simpa only [sq, mul_self_eq_zero] using (show δ x ^ 2 = 0 from hx)

end MetaplecticPoisson
