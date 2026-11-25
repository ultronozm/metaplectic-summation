import MetaplecticSummation.Marginals.TestedRadon
import MetaplecticSummation.Marginals.Fourier

noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField IsDedekindDomain MeasureTheory Set Filter Polynomial
open scoped Topology
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

theorem hat_radon_scaled (v : Place F) (Φ : d.schwartz v) (s u : (LocalField F v)ˣ) (y : LocalField F v) :
    let dx := selfDual F d.character v
    d.hat v (fun t => (radon n (d.symbol v) (modulus F v) dx Φ.val t).1 s y) u.val =
      (Real.sqrt (modulus F v (n : LocalField F v)) : ℂ) * (modulus F v u.val : ℂ)^(n-1) *
        (d.fourier v Φ).val.1 (u^n*s) (u.val^n*y) := by
  rw [d.fourier_apply]
  exact d.hat_radon_scaled_charts v Φ.val s u y


theorem marginal_scaled_radon (v : Place F) (Φ : d.schwartz v) (s u : (LocalField F v)ˣ) :
    let dx := selfDual F d.character v
    (Real.sqrt (modulus F v (n : LocalField F v)) : ℂ) * d.marginal v (d.fourier v Φ) (u^n*s) =
      (modulus F v u.val : ℂ) * ∫ y,
        d.hat v (fun t => (radon n (d.symbol v) (modulus F v) dx Φ.val t).1 s y) u.val ∂dx :=
  d.marginal_scaled_radon_of_charts v Φ _ (d.fourier_apply v Φ) s u


theorem finite_tested_marginal (p : HeightOneSpectrum (𝓞 F)) (Φ : d.schwartz (.inr p))
    (hΦ : Φ.val ∈ d.testSet (.inr p)) (s : (LocalField F (.inr p))ˣ)
    {ρ : LocalField F (.inr p) → ℂ} (hρ : Bruhat (.inr p) ρ) (h₀ : ρ 0 = 0) :
    let v : Place F := .inr p
    let dx := selfDual F d.character v
    let R := radon n (d.symbol v) (modulus F v) dx Φ.val
    (Real.sqrt (modulus F v (n : LocalField F v)) : ℂ) *
      d.lineIntegral v (fun u => d.marginal v (d.fourier v Φ) (u^n*s) * ρ u.val) =
      ∫ y, ∫ t, d.hat v ρ t * (R t).1 s y ∂dx ∂dx := by
  simpa only [d.transformTest_eq_fourier] using d.finite_tested_marginal_on_test p Φ hΦ s hρ h₀


theorem finite_tested_marginal_slice (p : HeightOneSpectrum (𝓞 F)) (Φ : d.schwartz (.inr p))
    (hΦ : Φ.val ∈ d.testSet (.inr p)) (s : (LocalField F (.inr p))ˣ)
    {ρ : LocalField F (.inr p) → ℂ} (hρ : Bruhat (.inr p) ρ) (h₀ : ρ 0 = 0) :
    let v : Place F := .inr p
    let dx := selfDual F d.character v
    (Real.sqrt (modulus F v (n : LocalField F v)) : ℂ) *
      d.lineIntegral v (fun u => d.marginal v (d.fourier v Φ) (u^n*s) * ρ u.val) =
      d.lineIntegral v (fun u => ∫ t, d.hat v ρ t * (∫ y, d.marginalSlice v Φ.val s u t y ∂dx) ∂dx) := by
  simpa only [d.transformTest_eq_fourier] using d.finite_tested_marginal_slice_on_test p Φ hΦ s hρ h₀

end MetaplecticPoisson.Datum
