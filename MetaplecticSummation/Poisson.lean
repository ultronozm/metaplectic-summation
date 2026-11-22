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

/-- Theorem 9.1. Both sums range over the nonzero rational vectors. -/
theorem poisson :
    ∃! B : d.Boundary →ₗ[ℂ] ℂ, ∀ Φ : d.Schwartz,
      Summable (fun v => ‖d.evaluation Φ v‖) ∧
      Summable (fun v => ‖d.evaluation (d.adelicFourier Φ) v‖) ∧
      (∑' v, d.evaluation Φ v) + B (d.adelicLeading Φ) =
        (∑' v, d.evaluation (d.adelicFourier Φ) v) +
          B (d.adelicLeading (d.adelicFourier Φ)) := by sorry

/-- Corollary 9.2. The two boundary contributions vanish. -/
theorem poisson_of_leading_eq_zero (Φ : d.Schwartz)
    (h : d.adelicLeading Φ = 0) (hF : d.adelicLeading (d.adelicFourier Φ) = 0) :
    (∑' v, d.evaluation Φ v) = ∑' v, d.evaluation (d.adelicFourier Φ) v := by
  obtain ⟨B, hB, _⟩ := d.poisson
  simpa only [h, hF, map_zero, add_zero] using (hB Φ).2.2

/-- The pure-tensor case of Corollary 9.2 allows the two vanishing factors
to occur at different places. -/
theorem poisson_pure_of_local_vanishing (f : ∀ v, d.schwartz v) (hf) (v w : Place F)
    (hv : d.leading v (f v) = 0) (hw : d.leading w (d.fourier w (f w)) = 0) :
    (∑' p, d.evaluation (d.pure f hf) p) = ∑' p, d.evaluation (d.adelicFourier (d.pure f hf)) p := by
  apply d.poisson_of_leading_eq_zero _ (d.adelicLeading_pure_eq_zero f hf v hv)
  rw [d.adelicFourier_pure]
  exact d.adelicLeading_pure_eq_zero _ _ w hw

/-- The paragraph following Theorem 9.1. In degree one the leading term
in the direction (1,0) gives the local Schwartz function's value at zero. -/
theorem boundary_degree_one (a : Datum F 1) (f : ∀ v, a.schwartz v)
    (hf : ∀ᶠ v in cofinite, f v = a.basic v) :
    a.poisson.exists.choose (a.adelicLeading (a.pure f hf)) =
      ∏ᶠ v, ((a.leading v) (f v)).1 1 0 := by sorry

end Datum
end MetaplecticPoisson
