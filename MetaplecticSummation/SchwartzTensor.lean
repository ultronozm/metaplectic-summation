/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in licenses/TauCeti-Apache-2.0.txt.
Authors: The Tau Ceti contributors
-/
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Normed.Operator.Prod

/-! Complex-valued products of independent Schwartz functions. The derivative bound and
binary product proof are adapted from Tau Ceti's CompLinear and SchwartzSpace.Prod. -/

noncomputable section
open scoped ContDiff SchwartzMap
namespace MetaplecticPoisson

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {n : WithTop ℕ∞}

/-- Precomposition with a continuous linear map `g` multiplies the norm of the `i`-th iterated
derivative by at most `‖g‖ ^ i`. -/
private theorem derivative_comp_bound (g : G →L[𝕜] E) {f : E → F} (hf : ContDiff 𝕜 n f)
    (x : G) {i : ℕ} (hi : i ≤ n) :
    ‖iteratedFDeriv 𝕜 i (f ∘ g) x‖ ≤ ‖iteratedFDeriv 𝕜 i f (g x)‖ * ‖g‖ ^ i := by
  rw [g.iteratedFDeriv_comp_right hf x hi]
  exact ((iteratedFDeriv 𝕜 i f (g x)).norm_compContinuousLinearMap_le _).trans_eq
    (by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin])


section
variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- External product of two complex-valued Schwartz functions. -/
def schwartzProduct (ψ : 𝓢(D, ℂ)) (u : 𝓢(E, ℂ)) : 𝓢(D × E, ℂ) where
  toFun z := ψ z.1 * u z.2
  smooth' := ((ψ.smooth ⊤).comp contDiff_fst).mul ((u.smooth ⊤).comp contDiff_snd)
  decay' k m := by
    refine ⟨∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
      (SchwartzMap.seminorm ℝ k i ψ * SchwartzMap.seminorm ℝ 0 (m - i) u +
        SchwartzMap.seminorm ℝ 0 i ψ * SchwartzMap.seminorm ℝ k (m - i) u), fun z => ?_⟩
    have hψ := (ψ.smooth ⊤).comp (ContinuousLinearMap.fst ℝ D E).contDiff
    have hu := (u.smooth ⊤).comp (ContinuousLinearMap.snd ℝ D E).contDiff
    -- The Leibniz rule, and `‖(t, x)‖ ^ k ≤ ‖t‖ ^ k + ‖x‖ ^ k` for the sup norm.
    have hz : ‖z‖ ^ k ≤ ‖z.1‖ ^ k + ‖z.2‖ ^ k := by
      rw [Prod.norm_def]
      rcases le_total ‖z.1‖ ‖z.2‖ with h | h
      · rw [max_eq_right h]
        exact le_add_of_nonneg_left (by positivity)
      · rw [max_eq_left h]
        exact le_add_of_nonneg_right (by positivity)
    calc ‖z‖ ^ k * ‖iteratedFDeriv ℝ m (fun z : D × E => ψ z.1 * u z.2) z‖
        ≤ ‖z‖ ^ k * ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i (ψ ∘ ContinuousLinearMap.fst ℝ D E) z‖ *
            ‖iteratedFDeriv ℝ (m - i) (u ∘ ContinuousLinearMap.snd ℝ D E) z‖ :=
          mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_mul_le hψ hu z
            (by exact_mod_cast le_top)) (by positivity)
      _ ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
            (SchwartzMap.seminorm ℝ k i ψ * SchwartzMap.seminorm ℝ 0 (m - i) u +
              SchwartzMap.seminorm ℝ 0 i ψ * SchwartzMap.seminorm ℝ k (m - i) u) := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun i _ => ?_
        -- The projections have norm at most one.
        have h₁ := (derivative_comp_bound (ContinuousLinearMap.fst ℝ D E) (ψ.smooth ⊤) z
          (i := i) (WithTop.coe_le_coe.2 le_top)).trans (mul_le_of_le_one_right (norm_nonneg _)
            (pow_le_one₀ (norm_nonneg _) (ContinuousLinearMap.norm_fst_le ℝ D E)))
        have h₂ := (derivative_comp_bound (ContinuousLinearMap.snd ℝ D E) (u.smooth ⊤) z
          (i := m - i) (WithTop.coe_le_coe.2 le_top)).trans (mul_le_of_le_one_right (norm_nonneg _)
            (pow_le_one₀ (norm_nonneg _) (ContinuousLinearMap.norm_snd_le ℝ D E)))
        have a₁ := ψ.le_seminorm ℝ k i z.1
        have a₂ := ψ.le_seminorm ℝ 0 i z.1
        have b₁ := u.le_seminorm ℝ 0 (m - i) z.2
        have b₂ := u.le_seminorm ℝ k (m - i) z.2
        simp only [pow_zero, one_mul] at a₂ b₁
        calc ‖z‖ ^ k * ((m.choose i : ℝ) *
              ‖iteratedFDeriv ℝ i (ψ ∘ ContinuousLinearMap.fst ℝ D E) z‖ *
              ‖iteratedFDeriv ℝ (m - i) (u ∘ ContinuousLinearMap.snd ℝ D E) z‖)
            ≤ (‖z.1‖ ^ k + ‖z.2‖ ^ k) * ((m.choose i : ℝ) *
                ‖iteratedFDeriv ℝ i ψ z.1‖ * ‖iteratedFDeriv ℝ (m - i) u z.2‖) := by
              gcongr ?_ * (_ * ?_ * ?_)
              exacts [h₁, h₂]
          _ = (m.choose i : ℝ) *
                ((‖z.1‖ ^ k * ‖iteratedFDeriv ℝ i ψ z.1‖) * ‖iteratedFDeriv ℝ (m - i) u z.2‖ +
                  ‖iteratedFDeriv ℝ i ψ z.1‖ * (‖z.2‖ ^ k * ‖iteratedFDeriv ℝ (m - i) u z.2‖)) := by
              ring
          _ ≤ _ := by gcongr


private theorem fin_schwartz_tensor (N : ℕ) (f : Fin N → SchwartzMap E ℂ) :
    ∃ φ : SchwartzMap (Fin N → E) ℂ, ∀ x, φ x = ∏ i, f i (x i) := by
  induction N with
  | zero =>
    let c : (Fin 0 → E) → ℂ := fun _ => 1
    have hc : HasCompactSupport c := HasCompactSupport.intro (isCompact_singleton (x := (0 : Fin 0 → E)))
      (fun x hx => False.elim (hx (Subsingleton.elim x 0)))
    exact ⟨hc.toSchwartzMap (contDiff_const : ContDiff ℝ ∞ c),fun _ => (Finset.prod_empty).symm⟩
  | succ N ih =>
    obtain ⟨φ,hφ⟩ := ih (fun i => f i.succ)
    let e := (Fin.consEquivL ℝ (fun _ : Fin (N+1) => E)).symm
    refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e (schwartzProduct (f 0) φ),fun x => ?_⟩
    change f 0 (x 0) * φ (fun i => x i.succ) = _
    rw [hφ,Fin.prod_univ_succ]

/-- A finite product of one-variable Schwartz functions is Schwartz for the product norm. -/
theorem exists_schwartz_tensor {ι : Type*} [Fintype ι] (f : ι → SchwartzMap E ℂ) :
    ∃ φ : SchwartzMap (ι → E) ℂ, ∀ x, φ x = ∏ i, f i (x i) := by
  classical
  let e := Fintype.equivFin ι
  obtain ⟨φ,hφ⟩ := fin_schwartz_tensor (Fintype.card ι) (fun i => f (e.symm i))
  let L := (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : ι => E) e.symm).symm
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L φ,fun x => ?_⟩
  change φ (L x) = _
  rw [hφ]
  exact e.symm.prod_comp (fun i => f i (x i))

end
end MetaplecticPoisson
