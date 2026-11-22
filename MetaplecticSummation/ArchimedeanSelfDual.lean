import MetaplecticSummation.AdelicAnnihilator
import MetaplecticSummation.ArchimedeanPlancherel

/-! Construction of the self-dual measure on a number-field completion at infinity. -/
noncomputable section
namespace MetaplecticPoisson
open NumberField MeasureTheory
variable {F : Type} [Field F] [NumberField F] (ψ : Character F) (w : InfinitePlace F)
local notation "v" => (Sum.inl w : Place F)
local notation "K" => LocalField F v

private theorem arch_selfDual_coordinates {L : Type} [RCLike L] (e : w.Completion ≃+* L)
    (he : Isometry e) : ∃ μ, IsSelfDual F ψ v μ := by
  letI : MeasurableSpace w.Completion := borel _
  letI : BorelSpace w.Completion := ⟨rfl⟩
  let i : K ≃ᵢ L := ⟨e.toEquiv,he⟩
  let χ : AddChar L ℂ := ⟨fun x => ψ.localValue F v (e.symm x),
    by rw [map_zero]; exact ψ.localValue_zero v,
    fun x y => by rw [map_add]; exact ψ.localValue_add v _ _⟩
  have hc : Continuous χ := (ψ.continuous_localValue v).comp i.symm.continuous
  obtain ⟨x,hx⟩ := ψ.nontrivial_localValue v
  have hn : ∃ z, χ z ≠ 1 := ⟨e x,by simpa only [χ,AddChar.coe_mk,e.symm_apply_apply] using hx⟩
  obtain ⟨ν,hν,hP⟩ := exists_rclike_plancherel χ hc (fun _ => ψ.norm_localValue v _) hn
  letI : ν.IsAddHaarMeasure := hν
  let j := i.symm.toHomeomorph.toMeasurableEquiv
  let μ := ν.map j
  refine ⟨μ,e.symm.toAddEquiv.isAddHaarMeasure_map ν i.symm.continuous i.continuous,?_⟩
  intro f hf hK
  let g := f ∘ i.symm
  have H := hP g (hf.comp i.symm.continuous) (hK.comp_homeomorph i.symm.toHomeomorph)
  change (∫⁻ y, ‖∫ x, f x * ψ.localValue F v (x*y) ∂ν.map j‖ₑ^2 ∂ν.map j) = ∫⁻ x, ‖f x‖ₑ^2 ∂ν.map j
  rw [lintegral_map_equiv,lintegral_map_equiv]
  simp_rw [integral_map_equiv]
  have pair (x y : L) : ψ.localValue F v (j x * j y) = χ (x*y) := congrArg (ψ.localValue F v) (e.symm.map_mul x y).symm
  simp_rw [pair]
  exact H

/-- Existence of the self-dual Haar measure at every infinite place. -/
theorem exists_arch_selfDual : ∃ μ, IsSelfDual F ψ v μ := by
  by_cases h : w.IsReal
  · exact arch_selfDual_coordinates ψ w (InfinitePlace.Completion.ringEquivRealOfIsReal h)
      (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal h)
  · exact arch_selfDual_coordinates ψ w
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex (InfinitePlace.not_isReal_iff_isComplex.mp h))
      (InfinitePlace.Completion.isometry_extensionEmbedding w)

end MetaplecticPoisson
