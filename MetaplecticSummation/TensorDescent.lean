import MetaplecticSummation.Core
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! Descent of a functional on the algebraic restricted tensor product through
a family of local quotient maps, as used in Appendix B. -/

noncomputable section
namespace MetaplecticPoisson
open Filter
open scoped TensorProduct
variable {ι : Type*} {V W : ι → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

/-- Induction on a restricted tensor using pure tensors equal to the reference
family away from finitely many places. -/
theorem restrictedTensor_induction (ξ : ∀ i, V i) {P : restrictedTensor ξ → Prop}
    (pure : ∀ (f : ∀ i, V i) (hf : ∀ᶠ i in cofinite, f i = ξ i),
      P ⟨PiTensorProduct.tprod ℂ f,Submodule.subset_span ⟨f,hf,rfl⟩⟩)
    (zero : P 0) (add : ∀ x y, P x → P y → P (x+y))
    (smul : ∀ (c : ℂ) x, P x → P (c • x)) (x : restrictedTensor ξ) : P x := by
  obtain ⟨x,hx⟩ := x
  refine Submodule.span_induction (p := fun x hx => P ⟨x,hx⟩) ?_ zero ?_ ?_ hx
  · rintro _ ⟨f,hf,rfl⟩
    exact pure f hf
  · exact fun _ _ hx hy => add ⟨_,hx⟩ ⟨_,hy⟩
  · exact fun c _ hx => smul c ⟨_,hx⟩

private theorem section_at_reference {X Y : Type*} [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] (L : X →ₗ[ℂ] Y) (hs : Function.Surjective L) (x : X) :
    ∃ S : Y →ₗ[ℂ] X, (∀ y, L (S y) = y) ∧ (L x ≠ 0 → S (L x) = x) := by
  obtain ⟨S,hS⟩ := L.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hs)
  have hs' (y : Y) : L (S y) = y := LinearMap.congr_fun hS y
  by_cases hx : L x = 0
  · exact ⟨S,hs',fun h => (h hx).elim⟩
  obtain ⟨e,_,he⟩ := LinearMap.exists_extend_of_notMem (0 : (⊥ : Submodule ℂ Y) →ₗ[ℂ] ℂ)
    (show L x ∉ (⊥ : Submodule ℂ Y) from hx) 1
  refine ⟨S + e.smulRight (x-S (L x)),?_,?_⟩
  · intro y
    simp [LinearMap.smulRight_apply,map_sub,hs']
  · intro _
    simp [LinearMap.smulRight_apply,he]

private theorem multilinear_eq_of_local_images (ξ : ∀ i, V i) (L : ∀ i, V i →ₗ[ℂ] W i)
    (M : MultilinearMap ℂ V ℂ)
    (hM : ∀ f, (∀ᶠ i in cofinite, f i = ξ i) → ∀ i, L i (f i) = 0 → M f = 0)
    (f g : ∀ i, V i) (hf : ∀ᶠ i in cofinite, f i = ξ i) (he : ∀ i, L i (f i) = L i (g i))
    (hfg : ∀ᶠ i in cofinite, f i = g i) : M f = M g := by
  classical
  have hfinite := eventually_cofinite.mp hfg
  suffices aux : ∀ (s : Finset ι) (x : ∀ i, V i), (∀ᶠ i in cofinite, x i = ξ i) →
      (∀ i, L i (x i) = L i (g i)) → (∀ i ∉ s, x i = g i) → M x = M g by
    exact aux hfinite.toFinset f hf he (fun i hi => by simpa using hi)
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro x _ _ hout
    exact congrArg M (funext (fun i => hout i (Finset.notMem_empty i)))
  | @insert i s _ ih =>
    intro x hx him hout
    have hu (a : V i) : ∀ᶠ j in cofinite, Function.update x i a j = ξ j := by
      filter_upwards [hx,eventually_cofinite_ne i] with j hj hji
      simpa only [Function.update_of_ne hji] using hj
    have hz := hM (Function.update x i (x i - g i)) (hu _) i (by simp [him])
    rw [M.map_update_sub,Function.update_eq_self,sub_eq_zero] at hz
    apply hz.trans (ih _ (hu _) ?_ ?_)
    · intro j
      by_cases h : j = i
      · subst j; simp
      · simpa only [Function.update_of_ne h] using him j
    · intro j hj
      by_cases h : j = i
      · subst j; simp
      · exact (Function.update_of_ne h _ _).trans (hout j (by simp [h,hj]))

/-- A functional vanishing on each restricted pure tensor with a local factor
in a kernel descends through the tensor product of the quotient maps. -/
theorem restrictedTensor_descend (ξ : ∀ i, V i) (L : ∀ i, V i →ₗ[ℂ] W i)
    (hs : ∀ i, Function.Surjective (L i)) (D : restrictedTensor ξ →ₗ[ℂ] ℂ)
    (hD : ∀ (f : ∀ i, V i) (hf : ∀ᶠ i in cofinite, f i = ξ i), ∀ i, L i (f i) = 0 →
      D ⟨PiTensorProduct.tprod ℂ f,Submodule.subset_span ⟨f,hf,rfl⟩⟩ = 0) :
    ∃ B : restrictedTensor (fun i => L i (ξ i)) →ₗ[ℂ] ℂ,
      B.comp (tensorMap ξ _ L (.of_forall fun _ => rfl)) = D := by
  classical
  choose S hS hξ using fun i => section_at_reference (L i) (hs i) (ξ i)
  obtain ⟨E,hE⟩ := D.exists_extend
  let M := E.compMultilinearMap (PiTensorProduct.tprod ℂ)
  have hz (f : ∀ i, V i) (hf : ∀ᶠ i in cofinite, f i = ξ i) (i : ι) (h : L i (f i) = 0) :
      M f = 0 := (LinearMap.congr_fun hE ⟨_,Submodule.subset_span ⟨f,hf,rfl⟩⟩).trans (hD f hf i h)
  let B := (E.comp (PiTensorProduct.map S)).comp (restrictedTensor (fun i => L i (ξ i))).subtype
  refine ⟨B,?_⟩
  apply LinearMap.ext
  rintro ⟨x,hx⟩
  refine Submodule.span_induction (p := fun x hx => (B.comp (tensorMap ξ _ L _)) ⟨x,hx⟩ = D ⟨x,hx⟩) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨f,hf,rfl⟩
    change E (PiTensorProduct.map S (PiTensorProduct.map L (PiTensorProduct.tprod ℂ f))) = _
    rw [PiTensorProduct.map_tprod,PiTensorProduct.map_tprod]
    apply Eq.trans _ (LinearMap.congr_fun hE ⟨_,Submodule.subset_span ⟨f,hf,rfl⟩⟩)
    change M (fun i => S i (L i (f i))) = M f
    by_cases h : ∃ i, L i (f i) = 0
    · obtain ⟨i,hi⟩ := h
      rw [hz f hf i hi]
      exact M.map_coord_zero i (by simp [hi])
    · symm
      apply multilinear_eq_of_local_images ξ L M hz f _ hf (fun i => (hS i _).symm)
      filter_upwards [hf] with i hi
      exact hi ▸ (hξ i (fun e => h ⟨i,hi ▸ e⟩)).symm
  · exact ((B.comp (tensorMap ξ _ L _)).map_zero).trans D.map_zero.symm
  · intro x y hx hy ex ey
    exact (map_add _ (⟨x,hx⟩ : restrictedTensor ξ) ⟨y,hy⟩).trans
      ((congrArg₂ (·+·) ex ey).trans (D.map_add _ _).symm)
  · intro c x hx ex
    exact (map_smul _ c (⟨x,hx⟩ : restrictedTensor ξ)).trans ((congrArg (c • ·) ex).trans (D.map_smul _ _).symm)

end MetaplecticPoisson
