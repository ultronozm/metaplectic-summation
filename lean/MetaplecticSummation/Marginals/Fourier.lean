import MetaplecticSummation.Schwartz.Local

noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField IsDedekindDomain MeasureTheory Filter
open scoped Topology
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

theorem axis_fourier (v : Place F) (Φ : d.schwartz v) (y u : (LocalField F v)ˣ) :
    d.axis v (d.fourier v Φ) (u^n*y) =
      (Real.sqrt (modulus F v (n : LocalField F v)) : ℂ)⁻¹ *
      (modulus F v u : ℂ)^(1-(n : ℤ)) * d.hat v (d.axisLine v Φ y) u := by
  unfold axis
  rw [d.fourier_apply]
  exact d.axis_integralTransform v Φ y u

theorem axisLine_hat_zero (v : Place F) (Φ : d.schwartz v) (y : (LocalField F v)ˣ)
    (hi : Integrable (d.axisLine v Φ y) (selfDual F d.character v)) :
    (Real.sqrt (modulus F v (n : LocalField F v)) : ℂ)⁻¹ * d.hat v (d.axisLine v Φ y) 0 =
      (d.leading v (d.fourier v Φ)).2 0 y :=
  d.axisLine_hat_zero_of_charts v Φ _ (d.fourier_apply v Φ) y hi

theorem transformTest_eq_fourier (v : Place F) (Φ : d.schwartz v) (hΦ : Φ.val ∈ d.testSet v) :
    d.transformTest v Φ hΦ = d.fourier v Φ :=
  Subtype.ext (d.fourier_apply v Φ).symm

end MetaplecticPoisson.Datum
