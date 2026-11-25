import MetaplecticSummation.ArchimedeanPlancherel
import MetaplecticSummation.ArchimedeanInversion
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-! Ordinary Fourier transformation on Schwartz space for the chosen local
character and Haar measure at a real or complex place. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField MeasureTheory InnerProductSpace
open scoped Topology FourierTransform RealInnerProductSpace NNReal
open Classical

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
    refine ⟨e x, fun h => hx ?_⟩
    exact (congrArg (d.character.localValue F vi) (e.symm_apply_apply x)).symm.trans h
  obtain ⟨T,hT⟩ := character_frequency_equiv χ hc (fun x => d.character.norm_localValue vi _) hn
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
    have h : e.symm (e x * e t) = x*t :=
      (congrArg e.symm (e.map_mul x t).symm).trans (e.symm_apply_apply _)
    exact congrArg (fun z : K => d.character.localValue F vi z * g (e t)) h.symm
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
