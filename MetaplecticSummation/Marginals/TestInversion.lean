import MetaplecticSummation.DiagonalTransform
import MetaplecticSummation.Marginals.Density

noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField IsDedekindDomain MeasureTheory
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)
variable (v : Place F)

/-- The converse marginal Fourier identity on test sections (Appendix A). -/
theorem reverse_marginal_on_test (v : Place F) (Φ : d.schwartz v) (hΦ : Φ.val ∈ d.testSet v) (x : (LocalField F v)ˣ) :
    ∀ u : (LocalField F v)ˣ, d.marginal v (d.transformTest v Φ hΦ) (u^n*x) =
      (Real.sqrt (modulus F v (n : LocalField F v)) : ℂ)⁻¹ * d.hat v (d.axisDensity v Φ x) u := by sorry

/-- The double integral on a test section is the indicated diagonal translate.
This deduction from the reverse test identity does not use a Fourier endomorphism. -/
theorem integralTransform_square_on_test
    (hFourier : ∀ f : LocalField F v → ℂ, Bruhat v f → d.hat v (d.hat v f) 1 = f (-1))
    {f : Charts (LocalField F v)} (hf : f ∈ d.testSet v) :
    d.integralTransform v (d.integralTransform v f) = d.torusCharts v ((-1)^(n+1)) f := by
  apply d.integralTransform_square_of_test_axis v _ hf
  intro Φ hΦ y
  exact d.integralTransform_axis_of_marginal v Φ (d.transformTest v Φ hΦ) y _
    (d.axisDensity_unit v Φ y⁻¹ (-1)) (d.reverse_marginal_on_test v Φ hΦ y⁻¹)
    (hFourier _ (d.axisDensity_bruhat v Φ y⁻¹))

end MetaplecticPoisson.Datum
