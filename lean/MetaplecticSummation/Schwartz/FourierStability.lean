import MetaplecticSummation.ArchimedeanDiagonal
import MetaplecticSummation.Marginals.TestInversion
import MetaplecticSummation.RadonDecay

/-! Construction of the local Fourier endomorphism from inversion on test sections. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

/-- The double integral on each test generator is a diagonal translate of that
test. This places its second transform in the defining Schwartz span at every
number-field place and yields the endomorphism of §7. -/
theorem exists_fourier_of_test_inversion (v : Place F) :
    ∃ L : d.schwartz v →ₗ[ℂ] d.schwartz v, ∀ Φ, (L Φ).val = d.integralTransform v Φ.val := by
  apply (d.fourier_stability_iff_square_on_tests v).2
  intro f hf
  have hinv (g : LocalField F v → ℂ) (hg : Bruhat v g) : d.hat v (d.hat v g) 1 = g (-1) := by
    cases v with
    | inl w => exact congrFun (d.arch_hat_hat w g hg) 1
    | inr p => exact d.hat_hat_finite p hg 1
  rw [d.integralTransform_square_on_test v hinv hf]
  have ht : d.torusCharts v ((-1)^(n+1)) f ∈ d.testSet v := by
    cases v with
    | inl w => exact d.torusCharts_archTest w _ hf
    | inr p => exact d.torusCharts_finiteTest p _ hf
  exact Submodule.subset_span (Or.inl ht)

end MetaplecticPoisson.Datum
