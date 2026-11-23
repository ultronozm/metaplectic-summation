import MetaplecticSummation.BoundaryConstruction
import MetaplecticSummation.Cusp.LocalContinuity

noncomputable section
namespace MetaplecticPoisson
namespace Datum
open Filter
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

/-- Absolute convergence and the boundary identity for a proposed functional. -/
def IsPoissonBoundary (B : d.Boundary →ₗ[ℂ] ℂ) : Prop :=
  ∀ Φ : d.Schwartz, Summable (fun v => ‖d.evaluation Φ v‖) ∧
    Summable (fun v => ‖d.evaluation (d.adelicFourier Φ) v‖) ∧
    (∑' v, d.evaluation Φ v) + B (d.adelicLeading Φ) =
      (∑' v, d.evaluation (d.adelicFourier Φ) v) + B (d.adelicLeading (d.adelicFourier Φ))

private theorem boundary_agree_of_zero {B C : d.Boundary →ₗ[ℂ] ℂ}
    (hB : d.IsPoissonBoundary B) (hC : d.IsPoissonBoundary C) (Φ : d.Schwartz)
    (h : d.adelicLeading (d.adelicFourier Φ) = 0) : B (d.adelicLeading Φ) = C (d.adelicLeading Φ) := by
  have hb := (hB Φ).2.2
  have hc := (hC Φ).2.2
  have eb := (congrArg B h).trans B.map_zero
  have ec := (congrArg C h).trans C.map_zero
  exact add_left_cancel (hb.trans ((congrArg (_ + ·) (eb.trans ec.symm)).trans hc.symm))

/-- The local modification in one finite factor determines the boundary
functional uniquely on every restricted pure tensor. -/
theorem poisson_boundary_unique {B C : d.Boundary →ₗ[ℂ] ℂ}
    (hB : d.IsPoissonBoundary B) (hC : d.IsPoissonBoundary C) : B = C := by
  classical
  obtain ⟨I,hI,hprime⟩ := Ring.not_isField_iff_exists_prime.mp (NumberField.RingOfIntegers.not_isField F)
  let p : Prime F := ⟨I,hprime,hI⟩
  let w : Place F := .inr p
  obtain ⟨π,hπ⟩ := FinitePlace.exists_norm_uniformizer p
  have eqn : B.comp d.adelicLeading = C.comp d.adelicLeading := by
    apply d.ext_pure
    intro f hf
    let g := Function.update f w (d.boundaryModification p π (f w))
    have hg : ∀ᶠ v in cofinite, g v = d.basic v := by
      filter_upwards [hf,eventually_cofinite_ne w] with v hv hw
      exact (Function.update_of_ne hw _ _).trans hv
    have hw : g w = d.boundaryModification p π (f w) := Function.update_self ..
    have hs := d.boundaryModification_spec p π hπ (f w)
    have he : d.adelicLeading (d.pure g hg) = d.adelicLeading (d.pure f hf) := by
      apply Subtype.ext
      change PiTensorProduct.map _ (PiTensorProduct.tprod ℂ g) = PiTensorProduct.map _ (PiTensorProduct.tprod ℂ f)
      rw [PiTensorProduct.map_tprod,PiTensorProduct.map_tprod]
      apply congrArg (PiTensorProduct.tprod ℂ)
      funext v
      by_cases h : v = w
      · subst v
        exact Subtype.ext (hw ▸ hs.1)
      · simp only [g,Function.update_of_ne h]
    have hz : d.adelicLeading (d.adelicFourier (d.pure g hg)) = 0 := by
      rw [d.adelicFourier_pure]
      apply d.adelicLeading_pure_eq_zero _ _ w
      rw [hw]
      exact hs.2
    change B (d.adelicLeading (d.pure f hf)) = C (d.adelicLeading (d.pure f hf))
    rw [← he]
    exact d.boundary_agree_of_zero hB hC _ hz
  exact LinearMap.ext fun y => by
    obtain ⟨x,rfl⟩ := d.adelicLeading_surjective y
    exact LinearMap.congr_fun eqn x

/-- Proposition B.6. The theta difference vanishes when a local leading term
and a (possibly different) transformed local leading term vanish. -/
theorem thetaDifference_vanishing : d.VanishesOnLocalKernels d.thetaDifference :=
  d.thetaDifference_eq_zero_of_local_evaluation_lifts d.hasLocalEvaluationLifts

/-- Existence and absolute convergence in Theorem 9.1. -/
theorem exists_poisson_boundary : ∃ B, d.IsPoissonBoundary B := by
  obtain ⟨I,hI,hprime⟩ := Ring.not_isField_iff_exists_prime.mp (NumberField.RingOfIntegers.not_isField F)
  let p : Prime F := ⟨I,hprime,hI⟩
  obtain ⟨π,hπ⟩ := FinitePlace.exists_norm_uniformizer p
  obtain ⟨B,hB⟩ := d.exists_boundary_of_vanishing d.thetaDifference d.thetaDifference_vanishing
    d.thetaDifference_fourier p π hπ
  refine ⟨B,fun Φ => ⟨d.summable_theta Φ,d.summable_theta _,?_⟩⟩
  have he : d.theta Φ - d.theta (d.adelicFourier Φ) =
      B (d.adelicLeading (d.adelicFourier Φ)) - B (d.adelicLeading Φ) := hB Φ
  change d.theta Φ + B (d.adelicLeading Φ) = d.theta (d.adelicFourier Φ) + _
  linear_combination he

/-- Theorem 9.1. Both sums range over the nonzero rational vectors. -/
theorem poisson :
    ∃! B : d.Boundary →ₗ[ℂ] ℂ, ∀ Φ : d.Schwartz,
      Summable (fun v => ‖d.evaluation Φ v‖) ∧
      Summable (fun v => ‖d.evaluation (d.adelicFourier Φ) v‖) ∧
      (∑' v, d.evaluation Φ v) + B (d.adelicLeading Φ) =
        (∑' v, d.evaluation (d.adelicFourier Φ) v) +
          B (d.adelicLeading (d.adelicFourier Φ)) := by
  obtain ⟨B,hB⟩ := d.exists_poisson_boundary
  exact ⟨B,hB,fun C hC => d.poisson_boundary_unique hC hB⟩

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
  exact sub_eq_zero.mp (d.thetaDifference_vanishing f hf v w hv hw)

/-- The paragraph following Theorem 9.1. In degree one the leading term
in the direction (1,0) gives the local Schwartz function's value at zero. -/
theorem boundary_degree_one (a : Datum F 1) (f : ∀ v, a.schwartz v)
    (hf : ∀ᶠ v in cofinite, f v = a.basic v) :
    a.poisson.exists.choose (a.adelicLeading (a.pure f hf)) =
      ∏ᶠ v, ((a.leading v) (f v)).1 1 0 := by sorry

end Datum
end MetaplecticPoisson
