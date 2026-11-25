import MetaplecticSummation.DiagonalTransform
import MetaplecticSummation.Marginals.FiniteTestInversion
import MetaplecticSummation.Marginals.Density
import MetaplecticSummation.Marginals.ArchimedeanTestInversion

noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField IsDedekindDomain MeasureTheory
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)
variable (v : Place F)

/-- The Archimedean case of Appendix A on test sections. -/
theorem arch_reverse_marginal_on_test (w : InfinitePlace F) (Φ : d.schwartz (.inl w)) (hΦ : Φ.val ∈ d.testSet (.inl w)) (x : (LocalField F (.inl w))ˣ) :
    ∀ u : (LocalField F (.inl w))ˣ, d.marginal (.inl w) (d.transformTest (.inl w) Φ hΦ) (u^n*x) =
      (Real.sqrt (modulus F (.inl w) (n : LocalField F (.inl w))) : ℂ)⁻¹ * d.hat (.inl w) (d.axisDensity (.inl w) Φ x) u :=
  d.arch_reverse_marginal w Φ hΦ x

/-- The converse marginal Fourier identity on test sections (Appendix A). -/
theorem reverse_marginal_on_test (v : Place F) (Φ : d.schwartz v) (hΦ : Φ.val ∈ d.testSet v) (x : (LocalField F v)ˣ) :
    ∀ u : (LocalField F v)ˣ, d.marginal v (d.transformTest v Φ hΦ) (u^n*x) =
      (Real.sqrt (modulus F v (n : LocalField F v)) : ℂ)⁻¹ * d.hat v (d.axisDensity v Φ x) u := by
  cases v with
  | inl w => exact d.arch_reverse_marginal_on_test w Φ hΦ x
  | inr p => exact d.reverse_marginal_finite p Φ hΦ x

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
