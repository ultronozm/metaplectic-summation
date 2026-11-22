import MetaplecticSummation.AdelicFourier
import MetaplecticSummation.BoundaryDilation
import MetaplecticSummation.FiniteInversion
import MetaplecticSummation.TensorDescent

/-! The descent and reconstruction of the Poisson boundary functional in Appendix B. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField Filter
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

local instance : AddCommGroup d.Schwartz := Module.addCommMonoidToAddCommGroup ℂ

local instance : AddCommGroup d.Boundary := Module.addCommMonoidToAddCommGroup ℂ

private theorem good_update (f : ∀ v, d.schwartz v) (hf : ∀ᶠ v in cofinite, f v = d.basic v)
    (w : Place F) (x : d.schwartz w) : ∀ᶠ v in cofinite, Function.update f w x v = d.basic v := by
  filter_upwards [hf,eventually_cofinite_ne w] with v h hv
  simpa only [Function.update_of_ne hv] using h

/-- Apply a local linear operator in one factor of the adelic Schwartz space. -/
def modifyAt (w : Place F) (Q : d.schwartz w →ₗ[ℂ] d.schwartz w) : d.Schwartz →ₗ[ℂ] d.Schwartz :=
  tensorMap d.basic d.basic (Function.update (fun _ => LinearMap.id) w Q) (by
    filter_upwards [eventually_cofinite_ne w] with v hv
    simp only [Function.update_of_ne hv,LinearMap.id_apply])

private theorem modifyAt_pure (w : Place F) (Q : d.schwartz w →ₗ[ℂ] d.schwartz w)
    (f : ∀ v, d.schwartz v) (hf) :
    d.modifyAt w Q (d.pure f hf) =
      d.pure (Function.update f w (Q (f w))) (d.good_update f hf w _) := by
  apply Subtype.ext
  change PiTensorProduct.map _ (PiTensorProduct.tprod ℂ f) = PiTensorProduct.tprod ℂ _
  rw [PiTensorProduct.map_tprod]
  apply congrArg (PiTensorProduct.tprod ℂ)
  funext v
  by_cases h : v = w
  · subst v; simp
  · simp [Function.update_of_ne h]

private theorem pure_sub_modifyAt (w : Place F) (Q : d.schwartz w →ₗ[ℂ] d.schwartz w)
    (f : ∀ v, d.schwartz v) (hf) :
    d.pure f hf - d.modifyAt w Q (d.pure f hf) =
      d.pure (Function.update f w (f w - Q (f w))) (d.good_update f hf w _) := by
  rw [d.modifyAt_pure]
  apply Subtype.ext
  change PiTensorProduct.tprod ℂ f - PiTensorProduct.tprod ℂ _ = PiTensorProduct.tprod ℂ _
  rw [(PiTensorProduct.tprod ℂ).map_update_sub,Function.update_eq_self]

/-- The vanishing on pure tensors in Proposition B.6. -/
def VanishesOnLocalKernels (D : d.Schwartz →ₗ[ℂ] ℂ) : Prop :=
  ∀ (f : ∀ v, d.schwartz v) (hf) (v w : Place F), d.leading v (f v) = 0 →
    d.leading w (d.fourier w (f w)) = 0 → D (d.pure f hf) = 0

/-- Descent of the modified difference through the adelic leading-term map
(Lemma B.10 and the construction following it). -/
private theorem boundary_descend (D : d.Schwartz →ₗ[ℂ] ℂ) (hD : d.VanishesOnLocalKernels D)
    (p : Prime F) (π : (LocalField F (.inr p))ˣ) (hπ : ‖π.val‖ = (p.asIdeal.absNorm : ℝ)⁻¹) :
    ∃ B : d.Boundary →ₗ[ℂ] ℂ, B.comp d.adelicLeading = -(D.comp (d.modifyAt (.inr p) (d.boundaryModification p π))) := by
  let w : Place F := .inr p
  let Q := d.boundaryModification p π
  apply restrictedTensor_descend d.basic (fun v => (d.leading v).rangeRestrict)
    (fun v => (d.leading v).surjective_rangeRestrict)
  intro f hf v hv
  change -D (d.modifyAt w Q (d.pure f hf)) = 0
  rw [neg_eq_zero,d.modifyAt_pure]
  apply hD _ _ v w
  · by_cases h : v = w
    · subst v
      rw [Function.update_self,(d.boundaryModification_spec p π hπ _).1]
      exact congrArg Subtype.val hv
    · rw [Function.update_of_ne h]
      exact congrArg Subtype.val hv
  · rw [Function.update_self]
    exact (d.boundaryModification_spec p π hπ _).2

/-- Lemma B.10. A zero adelic leading term forces the modified difference to vanish. -/
theorem boundary_well_defined (D : d.Schwartz →ₗ[ℂ] ℂ) (hD : d.VanishesOnLocalKernels D)
    (p : Prime F) (π : (LocalField F (.inr p))ˣ) (hπ : ‖π.val‖ = (p.asIdeal.absNorm : ℝ)⁻¹)
    (Φ : d.Schwartz) (hΦ : d.adelicLeading Φ = 0) :
    D (d.modifyAt (.inr p) (d.boundaryModification p π) Φ) = 0 := by
  obtain ⟨B,hB⟩ := d.boundary_descend D hD p π hπ
  have h : B (d.adelicLeading Φ) = -D (d.modifyAt (.inr p) (d.boundaryModification p π) Φ) :=
    LinearMap.congr_fun hB Φ
  rw [hΦ,B.map_zero] at h
  exact neg_eq_zero.mp h.symm

private theorem boundary_observation (D : d.Schwartz →ₗ[ℂ] ℂ) (hD : d.VanishesOnLocalKernels D)
    (p : Prime F) (π : (LocalField F (.inr p))ˣ) (hπ : ‖π.val‖ = (p.asIdeal.absNorm : ℝ)⁻¹)
    (B : d.Boundary →ₗ[ℂ] ℂ)
    (hb : ∀ Φ, B (d.adelicLeading Φ) = -D (d.modifyAt (.inr p) (d.boundaryModification p π) Φ))
    (f : ∀ v, d.schwartz v) (hf) (hz : d.leading (.inr p) (d.fourier (.inr p) (f (.inr p))) = 0) :
    D (d.pure f hf) = -B (d.adelicLeading (d.pure f hf)) := by
  let w : Place F := .inr p
  let Q := d.boundaryModification p π
  let A := d.modifyAt w Q
  let g := Function.update f w (f w-Q (f w))
  have hg := d.good_update f hf w (f w-Q (f w))
  have hw : g w = f w-Q (f w) := Function.update_self ..
  have e : d.pure f hf - A (d.pure f hf) = d.pure g hg := d.pure_sub_modifyAt w Q f hf
  have h₁ : d.leading w (g w) = 0 := by
    rw [hw,(d.leading w).map_sub]
    exact sub_eq_zero.mpr (d.boundaryModification_spec p π hπ _).1.symm
  have h₂ : d.leading w (d.fourier w (g w)) = 0 := by
    rw [hw,(d.fourier w).map_sub,(d.leading w).map_sub,hz,(d.boundaryModification_spec p π hπ _).2,sub_self]
  rw [hb,neg_neg]
  exact sub_eq_zero.mp (((D.map_sub _ _).symm.trans (congrArg D e)).trans (hD g hg w w h₁ h₂))

set_option maxHeartbeats 1000000 in
/-- The algebraic conclusion of Appendix B from vanishing on local kernels
and antisymmetry of the theta difference under Fourier transformation. -/
theorem exists_boundary_of_vanishing (D : d.Schwartz →ₗ[ℂ] ℂ) (hD : d.VanishesOnLocalKernels D)
    (hanti : ∀ Φ, D (d.adelicFourier Φ) = - D Φ)
    (p : Prime F) (π : (LocalField F (.inr p))ˣ) (hπ : ‖π.val‖ = (p.asIdeal.absNorm : ℝ)⁻¹) :
    ∃ B : d.Boundary →ₗ[ℂ] ℂ, ∀ Φ, D Φ = B (d.adelicLeading (d.adelicFourier Φ)) - B (d.adelicLeading Φ) := by
  let w : Place F := .inr p
  let Q := d.boundaryModification p π
  let A := d.modifyAt w Q
  obtain ⟨B,hB⟩ := d.boundary_descend D hD p π hπ
  have hb (Φ) : B (d.adelicLeading Φ) = -D (A Φ) := LinearMap.congr_fun hB Φ
  suffices he : D = ((B.comp d.adelicLeading).comp d.adelicFourier) - B.comp d.adelicLeading from
    ⟨B,fun Φ => LinearMap.congr_fun he Φ⟩
  apply d.ext_pure
  intro f hf
  let Φ := d.pure f hf
  let g := Function.update f w (f w-Q (f w))
  have hg := d.good_update f hf w (f w-Q (f w))
  have eg : Φ - A Φ = d.pure g hg := d.pure_sub_modifyAt w Q f hf
  have hw : d.leading w (g w) = 0 := by
    rw [show g w = f w - Q (f w) from Function.update_self ..,(d.leading w).map_sub,(d.boundaryModification_spec p π hπ _).1,sub_self]
  have hw₂ : d.leading w (d.fourier w (d.fourier w (g w))) = 0 := by
    apply (d.finite_germs p _).1.mpr
    rw [d.finite_fourier_square]
    exact d.torusCharts_finiteTest p _ ((d.finite_germs p _).1.mp hw)
  have hobs : D (d.adelicFourier (Φ - A Φ)) = -B (d.adelicLeading (d.adelicFourier (Φ - A Φ))) := by
    rw [eg,d.adelicFourier_pure]
    exact d.boundary_observation D hD p π hπ B hb _ _ hw₂
  have hz : d.adelicLeading (d.adelicFourier (A Φ)) = 0 := by
    change d.adelicLeading (d.adelicFourier (d.modifyAt w Q (d.pure f hf))) = 0
    rw [d.modifyAt_pure,d.adelicFourier_pure]
    apply d.adelicLeading_pure_eq_zero _ _ w
    rw [Function.update_self]
    exact (d.boundaryModification_spec p π hπ _).2
  rw [hanti,D.map_sub,d.adelicFourier.map_sub,d.adelicLeading.map_sub (d.adelicFourier Φ) (d.adelicFourier (A Φ)),hz,sub_zero] at hobs
  change D Φ = B (d.adelicLeading (d.adelicFourier Φ)) - B (d.adelicLeading Φ)
  rw [hb Φ]
  linear_combination -hobs

end MetaplecticPoisson.Datum
