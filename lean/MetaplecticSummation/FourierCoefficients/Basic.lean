import MetaplecticSummation.FourierCoefficients.Integrands
import MetaplecticSummation.Poisson

/-! Equality of the Fourier coefficients as a consequence of the Poisson formula. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField MeasureTheory Filter
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

/-- Two vanishing local leading terms make the theta series agree under
every adelic upper unipotent translation, hence also after taking a Fourier coefficient. -/
theorem coefficient_eq_fourier_of_local_vanishing (Φ : (v : Place F) → d.schwartz v)
    (hf : ∀ᶠ v in cofinite, Φ v = d.basic v) (v w : Place F)
    (hv : d.leading v (Φ v) = 0) (hw : d.leading w (d.fourier w (Φ w)) = 0) (a : F) :
    d.coefficient Φ a = d.coefficient (fun q => d.fourier q (Φ q)) a := by
  unfold coefficient
  apply integral_congr_ae
  filter_upwards with q
  induction q using Quotient.inductionOn with | _ u => _
  change d.translatedTheta Φ u * _ = d.translatedTheta _ u * _
  congr 1
  choose g hg _ using fun v => d.exists_upper v (component u v)
  have hΦ : ∀ᶠ v in cofinite, g v (Φ v) = d.basic v :=
    hf.and (d.eventually_upper_basic u g hg) |>.mono fun v h => by rw [h.1,h.2]
  have hΨ : ∀ᶠ v in cofinite, g v (d.fourier v (Φ v)) = d.basic v := by
    filter_upwards [hf,d.eventually_fourier_basic,d.eventually_upper_basic u g hg] with v h₁ h₂ h₃
    rwa [h₁,h₂]
  have he := d.poisson_pure_of_local_vanishing (fun v => g v (Φ v)) hΦ v w
    (by rw [d.leading_upper v _ (hg v),hv]; exact (upperShearLinear _ _).map_zero)
    (by rw [d.fourier_upper w _ (hg w),d.leading_upper w _ (hg w),hw]; exact (upperShearLinear _ _).map_zero)
  rw [d.translatedTheta_eq_upper u g hg Φ hΦ,d.translatedTheta_eq_upper u g hg _ hΨ]
  rw [d.adelicFourier_pure] at he
  change (∑' p, d.evaluation _ p) = ∑' p, d.evaluation _ p
  simpa only [d.fourier_upper _ _ (hg _)] using he

end MetaplecticPoisson.Datum
