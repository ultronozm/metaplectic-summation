import MetaplecticSummation.Reduction.UnipotentFiber
import MetaplecticSummation.Reduction.SecondCountable

/-! Integration along the compact unipotent fiber in Proposition B.6. -/
noncomputable section
namespace MetaplecticPoisson
open MeasureTheory Set Topology NumberField
open scoped MatrixGroups Pointwise ENNReal
variable (F : Type) [Field F] [NumberField F]
local notation "A" => Adeles F
local notation "G" => AdelicSL F
local notation "Y" => UnipotentArithmeticQuotient F
local notation "Z" => AdelicUnipotentQuotient F
local notation "ρ" => (Quotient.mk _ : G → Y)
local notation "π" => (Quotient.mk _ : G → Z)
local notation "η" => Exists.choose (ExistsUnique.exists (Datum.exists_quotient_measure (F := F)))
local instance : MeasurableSpace (Datum.AdeleQuotient F) := borel _
local instance : BorelSpace (Datum.AdeleQuotient F) := ⟨rfl⟩
local notation "du" => Measure.restrict (GroundTheory.Global.adeleMeasure F) (GroundTheory.Global.fundamentalSet F)
local instance : IsProbabilityMeasure du := ⟨by
  rw [Measure.restrict_apply_univ, GroundTheory.Global.adeleMeasure_fundamentalSet]⟩

private theorem measurable_shear_pair {E : Type*} [MeasurableSpace E] {f : Y → E} (hf : Measurable f) :
    Measurable (fun w : G × A => f (ρ (adelicUpper F w.2 * w.1))) :=
  hf.comp (measurable_quotient_mk''.comp (((continuous_adelicUpper F).comp continuous_snd).mul continuous_fst).measurable)

theorem unipotentFiberLIntegral_mk {f : Y → ℝ≥0∞} (hf : Measurable f) (x : G) :
    unipotentFiberLIntegral F f (π x) = ∫⁻ u, f (ρ (adelicUpper F u*x)) ∂du := by
  change (∫⁻ q, f (unipotentFiber F x q) ∂η) = _
  rw [Datum.quotient_measure_fundamental F]
  exact lintegral_map (hf.comp (measurable_unipotentFiber F x)) QuotientAddGroup.continuous_mk.measurable

theorem unipotentFiberIntegral_mk {f : Y → ℂ} (hf : Measurable f) (x : G) :
    unipotentFiberIntegral F f (π x) = ∫ u, f (ρ (adelicUpper F u*x)) ∂du := by
  change (∫ q, f (unipotentFiber F x q) ∂η) = _
  rw [Datum.quotient_measure_fundamental F]
  exact integral_map QuotientAddGroup.continuous_mk.measurable.aemeasurable
    (hf.comp (measurable_unipotentFiber F x)).aestronglyMeasurable

private theorem lintegral_translated {f : Y → ℝ≥0∞} (hf : Measurable f) (μ : Measure G)
    [μ.IsMulLeftInvariant] (u : A) :
    (∫⁻ x in rationalUnipotentDomain F, f (ρ (adelicUpper F u*x)) ∂μ) =
      ∫⁻ y, f y ∂unipotentQuotientMeasure F μ := by
  have h := (measurePreserving_unipotentTranslate F μ u).lintegral_comp hf
  exact (lintegral_map (hf.comp (measurable_unipotentTranslate F u)) measurable_quotient_mk'').symm.trans h

private theorem lintegral_shear_pair {f : Y → ℝ≥0∞} (hf : Measurable f) (μ : Measure G)
    [μ.IsMulLeftInvariant] [SFinite μ] :
    (∫⁻ w : G × A, f (ρ (adelicUpper F w.2 * w.1)) ∂(μ.restrict (rationalUnipotentDomain F)).prod du) =
      ∫⁻ y, f y ∂unipotentQuotientMeasure F μ := by
  rw [lintegral_prod_symm' _ (measurable_shear_pair F hf)]
  simp only [lintegral_translated F hf μ, lintegral_const, measure_univ, mul_one]

theorem lintegral_unipotentFiber (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    {f : Y → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ z, unipotentFiberLIntegral F f z ∂adelicUnipotentQuotientMeasure F μ) =
      ∫⁻ y, f y ∂unipotentQuotientMeasure F μ := by
  have hm : Measurable (unipotentFiberLIntegral F f) := by
    apply measurable_from_quotient.mpr
    change Measurable (fun x : G => unipotentFiberLIntegral F f (π x))
    simp only [unipotentFiberLIntegral_mk F hf]
    exact (measurable_shear_pair F hf).lintegral_prod_right'
  refine (lintegral_map hm (measurable_adelicUnipotentProjection F)).trans ?_
  refine (lintegral_map (hm.comp (measurable_adelicUnipotentProjection F)) measurable_quotient_mk'').trans ?_
  change (∫⁻ x in rationalUnipotentDomain F, unipotentFiberLIntegral F f (π x) ∂μ) = _
  simp only [unipotentFiberLIntegral_mk F hf]
  exact (lintegral_prod _ (measurable_shear_pair F hf).aemeasurable).symm.trans (lintegral_shear_pair F hf μ)

theorem measurable_unipotentFiberIntegral {f : Y → ℂ} (hf : Measurable f) :
    Measurable (unipotentFiberIntegral F f) := by
  apply measurable_from_quotient.mpr
  change Measurable (fun x : G => unipotentFiberIntegral F f (π x))
  simp only [unipotentFiberIntegral_mk F hf]
  exact (measurable_shear_pair F hf).stronglyMeasurable.integral_prod_right'.measurable

theorem integrable_unipotentFiberIntegral (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    {f : Y → ℂ} (hf : Measurable f) (hi : Integrable f (unipotentQuotientMeasure F μ)) :
    Integrable (unipotentFiberIntegral F f) (adelicUnipotentQuotientMeasure F μ) := by
  have bound (z : Z) : ‖unipotentFiberIntegral F f z‖ₑ ≤ unipotentFiberLIntegral F (fun y => ‖f y‖ₑ) z := by
    induction z using Quotient.inductionOn with | _ x => _
    exact enorm_integral_le_lintegral_enorm (fun q => f (unipotentFiber F x q))
  exact ⟨(measurable_unipotentFiberIntegral F hf).aestronglyMeasurable,
    (lintegral_mono bound).trans_lt ((lintegral_unipotentFiber F μ hf.enorm).trans_lt hi.hasFiniteIntegral)⟩

/-- Disintegration over N(𝔸) ∖ SL₂(𝔸) using probability Haar on the additive compact fiber. -/
theorem integral_unipotentFiber (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    {f : Y → ℂ} (hf : Measurable f) (hi : Integrable f (unipotentQuotientMeasure F μ)) :
    (∫ z, unipotentFiberIntegral F f z ∂adelicUnipotentQuotientMeasure F μ) =
      ∫ y, f y ∂unipotentQuotientMeasure F μ := by
  have hm := measurable_unipotentFiberIntegral F hf
  have hi' : Integrable (fun w : G × A => f (ρ (adelicUpper F w.2 * w.1)))
      ((μ.restrict (rationalUnipotentDomain F)).prod du) :=
    ⟨(measurable_shear_pair F hf).aestronglyMeasurable,
      (lintegral_shear_pair F hf.enorm μ).trans_lt hi.hasFiniteIntegral⟩
  have fixed (u : A) : (∫ x in rationalUnipotentDomain F, f (ρ (adelicUpper F u * x)) ∂μ) =
      ∫ y, f y ∂unipotentQuotientMeasure F μ := by
    have tr := measurePreserving_unipotentTranslate F μ u
    calc
      _ = ∫ y, f (unipotentTranslate F u y) ∂unipotentQuotientMeasure F μ :=
        (integral_map measurable_quotient_mk''.aemeasurable (hf.comp tr.measurable).aestronglyMeasurable).symm
      _ = ∫ y, f y ∂(unipotentQuotientMeasure F μ).map (unipotentTranslate F u) :=
        (integral_map tr.measurable.aemeasurable hf.aestronglyMeasurable).symm
      _ = _ := by rw [tr.map_eq]
  refine (integral_map (measurable_adelicUnipotentProjection F).aemeasurable hm.aestronglyMeasurable).trans ?_
  refine (integral_map measurable_quotient_mk''.aemeasurable
    (hm.comp (measurable_adelicUnipotentProjection F)).aestronglyMeasurable).trans ?_
  change (∫ x in rationalUnipotentDomain F, unipotentFiberIntegral F f (π x) ∂μ) = _
  simp only [unipotentFiberIntegral_mk F hf]
  rw [integral_integral_swap hi']
  simp only [fixed,integral_const,probReal_univ,one_smul]

/-- Unfold the rational orbit and then integrate over the compact unipotent fiber.
The hypothesis is the integral of the absolute orbit sum on the SL₂ quotient. -/
theorem integral_arithmeticOrbitSum_eq_fiberIntegral (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    {f : Y → ℂ} (hf : Measurable f)
    (habs : (∫⁻ x, arithmeticOrbitSum F (fun y => ‖f y‖ₑ) x ∂slQuotientMeasure F μ) < ⊤) :
    (∫ x, arithmeticOrbitSum F f x ∂slQuotientMeasure F μ) =
      ∫ z, unipotentFiberIntegral F f z ∂adelicUnipotentQuotientMeasure F μ := by
  have hi := (integrable_iff_arithmeticOrbitSum_norm F μ hf).mpr habs
  exact (integral_arithmeticOrbitSum F μ hf hi).2.trans (integral_unipotentFiber F μ hf hi).symm

end MetaplecticPoisson
