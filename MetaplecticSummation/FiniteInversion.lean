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

/-- Fourier inversion on ordinary Schwartz functions and the reverse identity
on test sections imply the square formula on the entire local Schwartz space. -/
theorem fourier_square_of_ordinary_inversion
    (hFourier : ∀ f : LocalField F v → ℂ, Bruhat v f → d.hat v (d.hat v f) 1 = f (-1))
    (Φ : d.schwartz v) : (d.fourier v (d.fourier v Φ)).val = d.torusCharts v ((-1)^(n+1)) Φ.val := by
  let e : (LocalField F v)ˣ := (-1)^(n+1)
  let L := d.fourier v
  let A := (d.schwartz v).subtype.comp (L.comp L)
  let B := (d.torusLinear v e).comp (d.schwartz v).subtype
  suffices he : A = B from DFunLike.congr_fun he Φ
  apply LinearMap.ext_on (Submodule.span_span_coe_preimage (R := ℂ)
    (s := d.testSet v ∪ d.integralTransform v '' d.testSet v))
  rintro ⟨f,hf⟩ (ht | ⟨g,hg,rfl⟩)
  · change (L (L ⟨f,hf⟩)).val = _
    rw [d.fourier_apply v (L ⟨f,hf⟩),d.fourier_apply]
    exact d.integralTransform_square_on_test v hFourier ht
  · let Ψ : d.schwartz v := ⟨d.integralTransform v g,hf⟩
    change (L (L Ψ)).val = d.torusCharts v e (d.integralTransform v g)
    rw [d.fourier_apply v (L Ψ),d.fourier_apply]
    change d.integralTransform v (d.integralTransform v (d.integralTransform v g)) = _
    rw [d.integralTransform_square_on_test v hFourier hg]
    exact d.integralTransform_torusCharts v e g

/-- The square formula at every finite completion. -/
theorem finite_fourier_square (p : HeightOneSpectrum (𝓞 F)) (Φ : d.schwartz (.inr p)) :
    let v : Place F := .inr p
    (d.fourier v (d.fourier v Φ)).val = d.torusCharts v ((-1)^(n+1)) Φ.val :=
  d.fourier_square_of_ordinary_inversion (.inr p) (fun _ hf => d.hat_hat_finite p hf 1) Φ

end MetaplecticPoisson.Datum
