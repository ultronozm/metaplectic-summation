import MetaplecticSummation.ArchimedeanCharacters
import MetaplecticSummation.ArchimedeanInversion
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.InnerProductSpace.Dual

/-! Ordinary Fourier transformation on Schwartz space for the chosen local
character and Haar measure at a real or complex place. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField MeasureTheory InnerProductSpace
open scoped Topology FourierTransform RealInnerProductSpace NNReal
open Classical

/-- In inner-product coordinates the nontrivial character of the field
pairing differs from the standard Fourier character by a linear isomorphism. -/
private theorem frequency_equiv {L : Type} [RCLike L] (χ : AddChar L ℂ) (hc : Continuous χ)
    (hu : ∀ t, ‖χ t‖ = 1) (hn : ∃ t, χ t ≠ 1) :
    ∃ T : L ≃L[ℝ] L, ∀ x y, χ (x*y) = (Real.fourierChar (-inner ℝ y (T x)) : ℂ) := by
  obtain ⟨l,hl⟩ := continuous_unitary_character_linear χ hc hu
  let B := ((ContinuousLinearMap.compL ℝ L L ℝ) (-l)).comp (ContinuousLinearMap.mul ℝ L)
  let A := continuousLinearMapOfBilin B
  have pair (x y : L) : inner ℝ (A x) y = -l (x*y) := continuousLinearMapOfBilin_apply B x y
  have hi : Function.Injective A := by
    apply (injective_iff_map_eq_zero A).2
    intro x hx
    by_contra he
    obtain ⟨t,ht⟩ := hn
    have h := pair x (t/x)
    rw [hx,inner_zero_left,mul_div_cancel₀ _ he] at h
    rw [hl,show l t = 0 by simpa using h] at ht
    simp at ht
  let T := (LinearEquiv.ofInjectiveEndo A.toLinearMap hi).toContinuousLinearEquiv
  refine ⟨T,fun x y => ?_⟩
  change χ (x*y) = (Real.fourierChar (-inner ℝ y (A x)) : ℂ)
  rw [real_inner_comm,pair,neg_neg,hl]

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (d : Datum F n) (w : InfinitePlace F)
local notation "vi" => (Sum.inl w : Place F)
local notation "K" => LocalField F vi
local notation "dx" => selfDual F d.character vi

private theorem arch_hat_coordinates {L : Type} [RCLike L] (e : w.Completion ≃+* L) (he : Isometry e)
    {f : K → ℂ} (g : SchwartzMap L ℂ) (hg : ∀ x, f x = g (e x)) :
    ∃ G : SchwartzMap L ℂ, ∀ x, d.hat vi f x = G (e x) := by
  let i : K ≃ᵢ L := ⟨e.toEquiv,he⟩
  let χ : AddChar L ℂ := ⟨fun x => d.character.localValue F vi (e.symm x),
    by rw [map_zero]; exact d.character.localValue_zero vi,
    fun x y => by rw [map_add]; exact d.character.localValue_add vi _ _⟩
  have hc : Continuous χ := (d.character.continuous_localValue vi).comp i.symm.continuous
  have hn : ∃ x, χ x ≠ 1 := by
    obtain ⟨x,hx⟩ := d.character.nontrivial_localValue vi
    exact ⟨e x,by simpa only [χ,AddChar.coe_mk,e.symm_apply_apply] using hx⟩
  obtain ⟨T,hT⟩ := frequency_equiv χ hc (fun x => d.character.norm_localValue vi _) hn
  let ν := (dx).map i
  letI : (dx).IsAddHaarMeasure := (existsUnique_selfDual F d.character vi).exists.choose_spec.1
  letI : ν.IsAddHaarMeasure := e.toAddEquiv.isAddHaarMeasure_map dx he.continuous i.symm.continuous
  let r := Measure.addHaarScalarFactor ν volume
  have hν : ν = r • volume := Measure.isAddLeftInvariant_eq_smul _ _
  refine ⟨(r : ℝ) • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ T (𝓕 g),fun x => ?_⟩
  let H (y : L) := (Real.fourierChar (-inner ℝ y (T (e x))) : ℂ) * g y
  have heq (t : K) : f t * d.character.localValue F vi (x*t) = H (i t) := by
    rw [hg,mul_comm]
    unfold H
    rw [← hT]
    change _ = d.character.localValue F vi (e.symm (e x * e t)) * _
    rw [← map_mul,e.symm_apply_apply]
    rfl
  unfold hat
  simp_rw [heq]
  have pull : (∫ t : K, H (i t) ∂dx) = ∫ y, H y ∂ν :=
    (integral_map_equiv i.toHomeomorph.toMeasurableEquiv H).symm
  rw [pull,hν,integral_smul_nnreal_measure]
  change (r : ℝ) • (∫ y, H y) = (r : ℝ) • (𝓕 g) (T (e x))
  rfl

theorem arch_hat_bruhat {f : K → ℂ} (hf : Bruhat vi f) : Bruhat vi (d.hat vi f) := by
  dsimp only [Bruhat] at hf ⊢
  split at hf <;> rename_i h
  · rw [dif_pos h]
    obtain ⟨g,hg⟩ := hf
    exact d.arch_hat_coordinates w _ (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal h) g hg
  · rw [dif_neg h]
    obtain ⟨g,hg⟩ := hf
    exact d.arch_hat_coordinates w _ (InfinitePlace.Completion.isometry_extensionEmbedding w) g hg

end MetaplecticPoisson.Datum
