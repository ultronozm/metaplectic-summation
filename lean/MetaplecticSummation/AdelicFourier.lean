import MetaplecticSummation.RationalEvaluation

noncomputable section
namespace MetaplecticPoisson
namespace Datum
open Filter
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

def adelicFourier : d.Schwartz →ₗ[ℂ] d.Schwartz :=
  tensorMap d.basic d.basic d.fourier d.eventually_fourier_basic

abbrev Boundary := restrictedTensor (fun v => (d.leading v).rangeRestrict (d.basic v))

def adelicLeading : d.Schwartz →ₗ[ℂ] d.Boundary :=
  tensorMap d.basic (fun v => (d.leading v).rangeRestrict (d.basic v))
    (fun v => (d.leading v).rangeRestrict) (Eventually.of_forall fun _ => rfl)

theorem adelicLeading_surjective : Function.Surjective d.adelicLeading :=
  tensorMap_surjective _ _ _ _ (fun v => (d.leading v).surjective_rangeRestrict)

theorem adelicFourier_pure (f : ∀ v, d.schwartz v) (hf) :
    d.adelicFourier (d.pure f hf) = d.pure (fun v => d.fourier v (f v)) (by
      filter_upwards [hf,d.eventually_fourier_basic] with v hv hb
      exact hv ▸ hb) := by
  apply Subtype.ext
  change PiTensorProduct.map d.fourier (PiTensorProduct.tprod ℂ f) = _
  rw [PiTensorProduct.map_tprod]
  rfl

theorem adelicLeading_pure_eq_zero (f : ∀ v, d.schwartz v) (hf) (v : Place F)
    (hv : d.leading v (f v) = 0) : d.adelicLeading (d.pure f hf) = 0 := by
  apply Subtype.ext
  change PiTensorProduct.map _ (PiTensorProduct.tprod ℂ f) = 0
  rw [PiTensorProduct.map_tprod]
  exact (PiTensorProduct.tprod ℂ).map_coord_zero v (Subtype.ext hv)

end Datum
end MetaplecticPoisson
