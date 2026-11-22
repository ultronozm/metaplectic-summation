import MetaplecticSummation.Schwartz.Local
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! Rapid decay at the origin and at infinity under linear changes of variables. -/

noncomputable section
namespace MetaplecticPoisson
open Set Filter
open scoped Topology ContDiff
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem radial_weight_comp (L : E ≃L[ℝ] E) (N : ℕ) (x : E) :
    let B := max 1 (max ‖L.toContinuousLinearMap‖ ‖L.symm.toContinuousLinearMap‖)
    min (‖L x‖^N) (‖L x‖^N)⁻¹ ≤ B^N * min (‖x‖^N) (‖x‖^N)⁻¹ := by
  let B := max 1 (max ‖L.toContinuousLinearMap‖ ‖L.symm.toContinuousLinearMap‖)
  have hB : 1 ≤ B := le_max_left _ _
  have bound (x : E) : ‖L x‖ ≤ B*‖x‖ := (L.toContinuousLinearMap.le_opNorm x).trans
    (mul_le_mul_of_nonneg_right ((le_max_left ..).trans (le_max_right ..)) (norm_nonneg x))
  have invbound : ‖x‖ ≤ B*‖L x‖ := by
    have h := L.symm.toContinuousLinearMap.le_opNorm (L x)
    rw [ContinuousLinearEquiv.coe_coe,L.symm_apply_apply] at h
    exact h.trans (mul_le_mul_of_nonneg_right ((le_max_right ..).trans (le_max_right ..)) (norm_nonneg _))
  change _ ≤ B^N * _
  rw [mul_min_of_nonneg _ _ (pow_nonneg (zero_le_one.trans hB) N)]
  apply le_min
  · apply (min_le_left ..).trans
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (bound x) N
  · apply (min_le_right ..).trans
    by_cases hx : x = 0
    · subst x
      simp only [map_zero,norm_zero]
      exact le_mul_of_one_le_left (by positivity) (one_le_pow₀ hB)
    have h₁ : 0 < ‖x‖^N := pow_pos (norm_pos_iff.mpr hx) _
    have h₂ : 0 < ‖L x‖^N := pow_pos (norm_pos_iff.mpr (L.map_ne_zero_iff.mpr hx)) _
    rw [← div_eq_mul_inv,le_div_iff₀ h₁,inv_mul_eq_div,div_le_iff₀ h₂]
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) invbound N

theorem rapidChart_comp_equiv {U : Set E} {f : E → ℂ} (hf : rapidChart U f) (L : E ≃L[ℝ] E) :
    rapidChart ((fun x => L x) ⁻¹' U) (fun x => f (L x)) := by
  refine ⟨hf.1.comp L.contDiff.contDiffOn (fun _ h => h),?_⟩
  intro k N
  obtain ⟨C,hC⟩ := hf.2 k N
  let D := max 0 C
  let B := max 1 (max ‖L.toContinuousLinearMap‖ ‖L.symm.toContinuousLinearMap‖)
  refine ⟨‖L.toContinuousLinearMap‖^k * D * B^N,fun x hx => ?_⟩
  have he := L.iteratedFDerivWithin_comp_right f (uniqueDiffOn_univ (𝕜 := ℝ)) (mem_univ (L x)) k
  simp only [preimage_univ,iteratedFDerivWithin_univ,Function.comp_def] at he
  rw [he]
  have h := (iteratedFDeriv ℝ k f (L x)).norm_compContinuousLinearMap_le (fun _ : Fin k => L.toContinuousLinearMap)
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at h
  have hD : 0 ≤ D := le_max_left _ _
  have hW : 0 ≤ min (‖L x‖^N) (‖L x‖^N)⁻¹ := by positivity
  calc
    _ ≤ ‖iteratedFDeriv ℝ k f (L x)‖ * ‖L.toContinuousLinearMap‖^k := h
    _ ≤ (D * min (‖L x‖^N) (‖L x‖^N)⁻¹) * ‖L.toContinuousLinearMap‖^k :=
      mul_le_mul_of_nonneg_right ((hC _ hx).trans (mul_le_mul_of_nonneg_right (le_max_right 0 C) hW)) (by positivity)
    _ ≤ (D * (B^N * min (‖x‖^N) (‖x‖^N)⁻¹)) * ‖L.toContinuousLinearMap‖^k :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (radial_weight_comp L N x) hD) (by positivity)
    _ = _ := by ring

/-- Locally, a change of chart may select either of two rapid functions and
multiply it by a constant of norm one. The two derivative bounds are uniform. -/
theorem rapidChart_of_local_branches {U V W : Set E} {f g h : E → ℂ}
    (hU : IsOpen U) (hV : IsOpen V) (hf : rapidChart U f) (hg : rapidChart V g)
    (hh : ∀ x ∈ W, (x ∈ U ∧ ∃ c : ℂ, ‖c‖ = 1 ∧ h =ᶠ[𝓝 x] c • f) ∨
      (x ∈ V ∧ ∃ c : ℂ, ‖c‖ = 1 ∧ h =ᶠ[𝓝 x] c • g)) : rapidChart W h := by
  have localBound {A : Set E} {b : E → ℂ} (hA : IsOpen A) (hb : rapidChart A b) {x} (hx : x ∈ A)
      {c : ℂ} (hc : ‖c‖ = 1) (he : h =ᶠ[𝓝 x] c • b) :
      ContDiffAt ℝ ∞ h x ∧ ∀ k, ‖iteratedFDeriv ℝ k h x‖ = ‖iteratedFDeriv ℝ k b x‖ := by
    have hd := hb.1.contDiffAt (hA.mem_nhds hx)
    refine ⟨(hd.const_smul c).congr_of_eventuallyEq he,fun k => ?_⟩
    rw [(he.iteratedFDeriv ℝ k).self_of_nhds,iteratedFDeriv_const_smul_apply
      (hd.of_le (by exact_mod_cast le_top : (k : WithTop ℕ∞) ≤ ∞)),norm_smul,hc,one_mul]
  constructor
  · intro x hx
    rcases hh x hx with ⟨h,_,hc,he⟩ | ⟨h,_,hc,he⟩
    · exact (localBound hU hf h hc he).1.contDiffWithinAt
    · exact (localBound hV hg h hc he).1.contDiffWithinAt
  · intro k N
    obtain ⟨C,hC⟩ := hf.2 k N
    obtain ⟨D,hD⟩ := hg.2 k N
    refine ⟨max C D,fun x hx => ?_⟩
    have hw : 0 ≤ min (‖x‖^N) (‖x‖^N)⁻¹ := by positivity
    rcases hh x hx with ⟨h,_,hc,he⟩ | ⟨h,_,hc,he⟩
    · rw [(localBound hU hf h hc he).2]
      exact (hC x h).trans (mul_le_mul_of_nonneg_right (le_max_left ..) hw)
    · rw [(localBound hV hg h hc he).2]
      exact (hD x h).trans (mul_le_mul_of_nonneg_right (le_max_right ..) hw)

end MetaplecticPoisson
