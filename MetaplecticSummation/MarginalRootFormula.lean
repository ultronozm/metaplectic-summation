import MetaplecticSummation.Marginals.RootSum
import MetaplecticSummation.MarginalConvergence

noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField IsDedekindDomain MeasureTheory Set Filter Polynomial
open scoped Topology
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

theorem finite_tested_root_sum (p : HeightOneSpectrum (𝓞 F)) (Φ : d.schwartz (.inr p))
    (hΦ : Φ.val ∈ d.testSet (.inr p)) (s : (LocalField F (.inr p))ˣ)
    (hpow : ∀ a : (LocalField F (.inr p))ˣ, (∀ u, d.symbol (.inr p) u a = 1) → ∃ b, b^n = a)
    {ρ : LocalField F (.inr p) → ℂ} (hρ : Bruhat (.inr p) ρ) (h₀ : ρ 0 = 0) :
    let v : Place F := .inr p
    (Real.sqrt (modulus F v (n : LocalField F v)) : ℂ) *
      d.lineIntegral v (fun μ => d.marginal v (d.fourier v Φ) (μ^n*s) * ρ μ.val) =
      ∫ y, (if hy : y ≠ 0 then d.axis v Φ (Units.mk0 y hy) else 0) *
        ∑ r ∈ nthRootsFinset n (-(s.val*y)), d.lineIntegral v (fun μ => ρ μ.val * d.character.localValue F v (μ.val*r))
        ∂(selfDual F d.character v) := by
  simpa only [d.transformTest_eq_fourier] using d.finite_tested_root_sum_on_test p Φ hΦ s hpow hρ h₀

theorem finite_marginal_root_formula (p : HeightOneSpectrum (𝓞 F)) (Φ : d.schwartz (.inr p))
    (hΦ : Φ.val ∈ d.testSet (.inr p)) (s μ : (LocalField F (.inr p))ˣ)
    (hpow : ∀ a : (LocalField F (.inr p))ˣ, (∀ u, d.symbol (.inr p) u a = 1) → ∃ b, b^n = a) :
    let v : Place F := .inr p
    (Real.sqrt (modulus F v (n : LocalField F v)) : ℂ) * d.marginal v (d.fourier v Φ) (μ^n*s) =
      ∫ y, (if hy : y ≠ 0 then d.axis v Φ (Units.mk0 y hy) else 0) *
        ∑ a ∈ nthRootsFinset n (-(s.val*y)), d.character.localValue F v (μ.val*a)
        ∂(selfDual F d.character v) := by
  simpa only [d.transformTest_eq_fourier] using d.finite_marginal_root_formula_on_test p Φ hΦ s μ hpow

/-- The reverse marginal expressed as a sum over roots at every finite place. -/
theorem marginal_root_formula_finite (p : HeightOneSpectrum (𝓞 F))
    (Φ : d.schwartz (.inr p)) (hΦ : Φ.val ∈ d.testSet (.inr p)) (s μ : (LocalField F (.inr p))ˣ) :
    let v : Place F := .inr p
    (Real.sqrt (modulus F v (n : LocalField F v)) : ℂ) * d.marginal v (d.fourier v Φ) (μ^n*s) =
      ∫ y, (if hy : y ≠ 0 then d.axis v Φ (Units.mk0 y hy) else 0) *
        ∑ a ∈ nthRootsFinset n (-(s.val*y)), d.character.localValue F v (μ.val*a)
        ∂(selfDual F d.character v) :=
  d.finite_marginal_root_formula p Φ hΦ s μ (d.finite_symbol_power p)

/-- The reverse marginal's pointwise root-sum formula at every finite place
of residue characteristic prime to the degree. -/
theorem tame_marginal_root_formula (p : HeightOneSpectrum (𝓞 F)) (hp : p.asIdeal.absNorm.Coprime n)
    (Φ : d.schwartz (.inr p)) (hΦ : Φ.val ∈ d.testSet (.inr p)) (s μ : (LocalField F (.inr p))ˣ) :
    let v : Place F := .inr p
    (Real.sqrt (modulus F v (n : LocalField F v)) : ℂ) * d.marginal v (d.fourier v Φ) (μ^n*s) =
      ∫ y, (if hy : y ≠ 0 then d.axis v Φ (Units.mk0 y hy) else 0) *
        ∑ a ∈ nthRootsFinset n (-(s.val*y)), d.character.localValue F v (μ.val*a)
        ∂(selfDual F d.character v) :=
  d.finite_marginal_root_formula p Φ hΦ s μ (fun a => (d.tame_symbol_radical p hp a).mp)

end MetaplecticPoisson.Datum
