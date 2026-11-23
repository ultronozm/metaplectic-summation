import MetaplecticSummation.Reduction.OrbitDomain

/-! Unfolding from SL₂(F) to N(F) with measures induced by a common adelic Haar measure. -/
noncomputable section
namespace MetaplecticPoisson
open MeasureTheory Set Topology NumberField
open scoped MatrixGroups Pointwise ENNReal
open Classical
variable (F : Type) [Field F] [NumberField F]
local notation "G" => AdelicSL F
local notation "Γ" => SL(2,F)
local notation "ι" => rationalSLMap F
abbrev SLArithmeticQuotient := Quotient (QuotientGroup.rightRel (rationalSL F))
abbrev UnipotentArithmeticQuotient := Quotient (QuotientGroup.rightRel (rationalUnipotents F))
local notation "X" => SLArithmeticQuotient F
local notation "Y" => UnipotentArithmeticQuotient F
local notation "Q" => RationalCosets F
local notation "π" => (Quotient.mk _ : G → X)
local notation "ρ" => (Quotient.mk _ : G → Y)

/-- Quotient measures for a common normalization upstairs. -/
def slQuotientMeasure (μ : Measure G) : Measure X := Measure.map π (μ.restrict (rationalSLDomain F))
def unipotentQuotientMeasure (μ : Measure G) : Measure Y := Measure.map ρ (μ.restrict (rationalUnipotentDomain F))

private def cosetRightMul (γ : Γ) : Q ≃ Q :=
  Quotient.congr (Equiv.mulRight γ) fun a b => by
    simp only [QuotientGroup.rightRel_apply]
    change _ ↔ b*γ*(a*γ)⁻¹ ∈ upperUnipotent F
    rw [mul_inv_rev,← mul_assoc,mul_inv_cancel_right]

private def orbitTranslate (x : G) : Q → Y :=
  Quotient.lift (fun a : Γ => ρ (ι a*x)) fun a b h => by
    apply Quotient.sound
    apply QuotientGroup.rightRel_apply.mpr
    refine ⟨b*a⁻¹,QuotientGroup.rightRel_apply.mp h,?_⟩
    simp [mul_assoc]

private theorem orbitTranslate_out (x : G) (q : Q) : orbitTranslate F x q = ρ (ι q.out*x) :=
  (congrArg (orbitTranslate F x) (Quotient.out_eq q)).symm

private theorem orbitTranslate_mul (x : G) (γ : Γ) (q : Q) :
    orbitTranslate F (ι γ*x) q = orbitTranslate F x (cosetRightMul F γ q) := by
  induction q using Quotient.inductionOn with | _ a => _
  change ρ (ι a*(ι γ*x)) = ρ (ι (a*γ)*x)
  rw [map_mul,mul_assoc]

/-- Sum over the fibers of N(F) ∖ SL₂(𝔸) → SL₂(F) ∖ SL₂(𝔸). -/
def arithmeticOrbitSum {E : Type*} [AddCommMonoid E] [TopologicalSpace E] (f : Y → E) : X → E :=
  Quotient.lift (fun x : G => ∑' q : Q, f (orbitTranslate F x q)) fun x y h => by
    obtain ⟨γ,hγ⟩ := QuotientGroup.rightRel_apply.mp h
    have ey : y = ι γ*x := (eq_mul_inv_iff_mul_eq.mp hγ).symm
    rw [ey]
    simp_rw [orbitTranslate_mul]
    exact ((cosetRightMul F γ).tsum_eq _).symm

theorem arithmeticOrbitSum_mk {E : Type*} [AddCommMonoid E] [TopologicalSpace E] (f : Y → E) (x : G) :
    arithmeticOrbitSum F f (π x) = ∑' q : Q, f (ρ (ι q.out*x)) := by
  change (∑' q, f (orbitTranslate F x q)) = _
  simp only [orbitTranslate_out]

private theorem measurable_orbit_term {E : Type*} [MeasurableSpace E] {f : Y → E} (hf : Measurable f) (q : Q) :
    Measurable (fun x : G => f (ρ (ι q.out*x))) :=
  hf.comp (measurable_quotient_mk''.comp (continuous_const_mul _).measurable)

theorem measurable_arithmeticOrbitSum {f : Y → ℂ} (hf : Measurable f) : Measurable (arithmeticOrbitSum F f) := by
  apply measurable_from_quotient.mpr
  change Measurable (fun x : G => arithmeticOrbitSum F f (π x))
  simp only [arithmeticOrbitSum_mk]
  exact Measurable.tsum (measurable_orbit_term F hf)

theorem measurable_arithmeticOrbitSum_nonneg {f : Y → ℝ≥0∞} (hf : Measurable f) : Measurable (arithmeticOrbitSum F f) := by
  apply measurable_from_quotient.mpr
  change Measurable (fun x : G => arithmeticOrbitSum F f (π x))
  simp only [arithmeticOrbitSum_mk]
  exact Measurable.tsum (measurable_orbit_term F hf)

theorem lintegral_arithmeticOrbitSum (μ : Measure G) [μ.IsMulLeftInvariant] {f : Y → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ q, arithmeticOrbitSum F f q ∂slQuotientMeasure F μ) = ∫⁻ y, f y ∂unipotentQuotientMeasure F μ := by
  rw [slQuotientMeasure,unipotentQuotientMeasure,lintegral_map (measurable_arithmeticOrbitSum_nonneg F hf) measurable_quotient_mk'',
    lintegral_map hf measurable_quotient_mk'']
  simp only [arithmeticOrbitSum_mk]
  rw [lintegral_tsum (fun q => (measurable_orbit_term F hf q).aemeasurable),rationalUnipotentDomain,
    lintegral_iUnion (measurableSet_unipotentDomainPiece F) (disjoint_unipotentDomainPiece F)]
  exact tsum_congr fun q => (measurePreserving_mul_left μ (ι q.out)).setLIntegral_comp_emb
    (Homeomorph.mulLeft (ι q.out)).measurableEmbedding (fun x => f (ρ x)) (rationalSLDomain F)

/-- Absolute convergence and the complex orbit integral, with both quotient measures
obtained from the same left Haar measure. -/
theorem integral_arithmeticOrbitSum (μ : Measure G) [μ.IsMulLeftInvariant] {f : Y → ℂ}
    (hf : Measurable f) (hi : Integrable f (unipotentQuotientMeasure F μ)) :
    Integrable (arithmeticOrbitSum F f) (slQuotientMeasure F μ) ∧
      (∫ q, arithmeticOrbitSum F f q ∂slQuotientMeasure F μ) = ∫ y, f y ∂unipotentQuotientMeasure F μ := by
  let L := fun y : Y => ‖f y‖ₑ
  have hL : Measurable L := hf.enorm
  have finite : (∫⁻ q, arithmeticOrbitSum F L q ∂slQuotientMeasure F μ) < ⊤ :=
    (lintegral_arithmeticOrbitSum F μ hL).trans_lt hi.hasFiniteIntegral
  have bound (q : X) : ‖arithmeticOrbitSum F f q‖ₑ ≤ arithmeticOrbitSum F L q := by
    induction q using Quotient.inductionOn with | _ x => _
    simp only [arithmeticOrbitSum_mk]
    exact enorm_tsum_le_tsum_enorm
  refine ⟨⟨(measurable_arithmeticOrbitSum F hf).aestronglyMeasurable,(lintegral_mono bound).trans_lt finite⟩,?_⟩
  have pulled : IntegrableOn (f ∘ ρ) (rationalUnipotentDomain F) μ :=
    hi.comp_measurable (μ := μ.restrict (rationalUnipotentDomain F)) measurable_quotient_mk''
  have absSum : (∑' q : Q, ∫⁻ x in rationalSLDomain F, ‖f (ρ (ι q.out*x))‖ₑ ∂μ) ≠ ⊤ := by
    rw [slQuotientMeasure,lintegral_map (measurable_arithmeticOrbitSum_nonneg F hL) measurable_quotient_mk''] at finite
    simp only [arithmeticOrbitSum_mk,L] at finite
    rwa [lintegral_tsum (fun q => (measurable_orbit_term F hf q).enorm.aemeasurable),lt_top_iff_ne_top] at finite
  rw [slQuotientMeasure,unipotentQuotientMeasure,integral_map measurable_quotient_mk''.aemeasurable
    (measurable_arithmeticOrbitSum F hf).aestronglyMeasurable,integral_map measurable_quotient_mk''.aemeasurable hf.aestronglyMeasurable]
  simp only [arithmeticOrbitSum_mk]
  rw [integral_tsum (fun q => (measurable_orbit_term F hf q).aestronglyMeasurable) absSum]
  change _ = ∫ x in ⋃ q, unipotentDomainPiece F q, (f ∘ ρ) x ∂μ
  rw [integral_iUnion (measurableSet_unipotentDomainPiece F) (disjoint_unipotentDomainPiece F) pulled]
  exact tsum_congr fun q => ((measurePreserving_mul_left μ (ι q.out)).setIntegral_image_emb
    (Homeomorph.mulLeft (ι q.out)).measurableEmbedding (f ∘ ρ) (rationalSLDomain F)).symm

/-- A bound for the sum of absolute values on the SL₂ quotient suffices for unfolding. -/
theorem integrable_iff_arithmeticOrbitSum_norm (μ : Measure G) [μ.IsMulLeftInvariant]
    {f : Y → ℂ} (hf : Measurable f) :
    Integrable f (unipotentQuotientMeasure F μ) ↔
      (∫⁻ x, arithmeticOrbitSum F (fun y => ‖f y‖ₑ) x ∂slQuotientMeasure F μ) < ⊤ := by
  rw [lintegral_arithmeticOrbitSum F μ hf.enorm]
  exact ⟨Integrable.hasFiniteIntegral, fun h => ⟨hf.aestronglyMeasurable, h⟩⟩

end MetaplecticPoisson
