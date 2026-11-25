import MetaplecticSummation.Schwartz.FourierStability

noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

theorem exists_fourier (v : Place F) :
    ∃ L : d.schwartz v →ₗ[ℂ] d.schwartz v, ∀ f, (L f).val = d.integralTransform v f :=
  d.exists_fourier_of_test_inversion v

def fourier (v : Place F) := (d.exists_fourier v).choose

theorem fourier_apply (v : Place F) (f : d.schwartz v) :
    (d.fourier v f).val = d.integralTransform v f :=
  (d.exists_fourier v).choose_spec f

end MetaplecticPoisson.Datum
