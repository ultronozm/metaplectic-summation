import MetaplecticSummation.Hilbert.InfiniteLaws
import MetaplecticSummation.Hilbert.FiniteLaws

noncomputable section
namespace MetaplecticPoisson.Hilbert
open NumberField IsDedekindDomain Filter Set MetaplecticPoisson
variable {F : Type} [Field F] [NumberField F] (n : ℕ+) {ζ : F} (hζ : IsPrimitiveRoot ζ (n : ℕ))

def family : SymbolFamily F n
  | .inl w => infiniteValue n w
  | .inr p => finiteValue n hζ p

private theorem product_on_places {I J G : Type*} [Fintype I] [CommGroup G] (f : I ⊕ J → G)
    (h : Function.HasFiniteMulSupport (fun j => f (.inr j))) :
    Function.HasFiniteMulSupport f ∧
      (∏ᶠ v, f v) = (∏ i, f (.inl i)) * ∏ᶠ j, f (.inr j) := by
  classical
  let t := h.toFinset
  have ht : Function.mulSupport (fun j => f (.inr j)) ⊆ (t : Set J) :=
    fun _ hx => h.mem_toFinset.mpr hx
  have hu : Function.mulSupport f ⊆ ((Finset.univ.disjSum t : Finset (I ⊕ J)) : Set _) := by
    intro x hx
    cases x with
    | inl i => exact Finset.inl_mem_disjSum.mpr (Finset.mem_univ _)
    | inr j => exact Finset.inr_mem_disjSum.mpr (ht hx)
  refine ⟨(Finset.finite_toSet _).subset hu, ?_⟩
  rw [finprod_eq_prod_of_mulSupport_subset _ hu,Finset.prod_disjSum,
    finprod_eq_prod_of_mulSupport_subset _ ht]

theorem family_spec : IsHilbertFamily F n (family n hζ) where
  continuous_pair
    | .inl w => infiniteValue_continuous n w
    | .inr p => finiteValue_continuous n hζ p
  mul_left
    | .inl w => infiniteValue_mul_left n w
    | .inr p => finiteValue_mul_left n hζ p
  mul_right
    | .inl w, a,b,c => by
      change infiniteValue n w a (b*c) = _
      rw [infiniteValue_symm n w a (b*c), infiniteValue_mul_left,
        infiniteValue_symm n w b a, infiniteValue_symm n w c a]
      rfl
    | .inr p, a,b,c => finiteValue_mul_right n hζ p a b c
  skew
    | .inl w => infiniteValue_skew n w
    | .inr p => finiteValue_skew n hζ p
  neg_self
    | .inl w => infiniteValue_neg_self n w
    | .inr p => finiteValue_neg_self p n hζ
  tame_units := fun p => finiteValue_tame_units p n hζ
  tame_uniformizer := fun p => finiteValue_tame_uniformizer p n hζ
  unramified a b := by
    let f (v : Place F) := family n hζ v (Units.map (diagonal F v) a) (Units.map (diagonal F v) b)
    exact eventually_cofinite.mpr (product_on_places f (finiteValue_support n hζ a b)).1
  reciprocity a b := by
    let f (v : Place F) := family n hζ v (Units.map (diagonal F v) a) (Units.map (diagonal F v) b)
    exact (product_on_places f (finiteValue_support n hζ a b)).2.trans (normalized_product n hζ a b)

end MetaplecticPoisson.Hilbert
