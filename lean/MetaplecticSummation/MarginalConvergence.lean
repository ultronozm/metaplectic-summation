import MetaplecticSummation.Marginals.DifferenceConvergence
import MetaplecticSummation.TestedMarginal

noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField IsDedekindDomain MeasureTheory Set Filter Polynomial
open scoped Topology
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

theorem finite_tested_marginal_difference (p : HeightOneSpectrum (𝓞 F)) (Φ : d.schwartz (.inr p))
    (hΦ : Φ.val ∈ d.testSet (.inr p)) (s : (LocalField F (.inr p))ˣ)
    {ρ : LocalField F (.inr p) → ℂ} (hρ : Bruhat (.inr p) ρ) (h₀ : ρ 0 = 0) :
    let v : Place F := .inr p
    let dx := selfDual F d.character v
    let h := d.hat v ρ
    (Real.sqrt (modulus F v (n : LocalField F v)) : ℂ) *
      d.lineIntegral v (fun μ => d.marginal v (d.fourier v Φ) (μ^n*s) * ρ μ.val) =
      ∫ y, if hy : y ≠ 0 then
        ∫ t, h t * d.differenceIntegral v (fun x => Φ.val.2 x (Units.mk0 y hy))
          (-(s * Units.mk0 y hy)) (t^n+s.val*y) ∂dx else 0 ∂dx := by
  simpa only [d.transformTest_eq_fourier] using d.finite_tested_marginal_difference_on_test p Φ hΦ s hρ h₀

end MetaplecticPoisson.Datum
