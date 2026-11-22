import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-! Compact families of Schwartz functions in the determinant parameter. -/
noncomputable section
namespace MetaplecticPoisson
open Set

/-- A chart family consists of Schwartz functions in the line variable,
with each derivative bounded in every polynomial weight on compact parameter sets. -/
def SchwartzSliceFamily {P K L : Type} [TopologicalSpace P] [NormedField K]
    [NormedField L] [NormedAlgebra ℝ L] (e : K ≃+* L) (R : P → K → ℂ) : Prop :=
  ∃ G : P → SchwartzMap L ℂ, (∀ q t, R q t = G q (e t)) ∧
    ∀ T : Set P, IsCompact T → ∀ k N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ T, ∀ y : L,
      ‖iteratedFDeriv ℝ k (G q) y‖ * (1+‖y‖)^N ≤ C

private theorem bounded_schwartz_family_iff {P E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : P → SchwartzMap E ℂ) (T : Set P) :
    Bornology.IsVonNBounded ℝ (G '' T) ↔
      ∀ k N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ T, ∀ y : E,
        ‖iteratedFDeriv ℝ k (G q) y‖ * (1 + ‖y‖)^N ≤ C := by
  constructor
  · intro h k N
    obtain ⟨C, hC, hb⟩ :=
      ((schwartz_withSeminorms ℝ E ℂ).image_isVonNBounded_iff_finset_seminorm_bounded G).mp h
        (Finset.Iic (N, k))
    refine ⟨2^N * C, by positivity, fun q hq y => ?_⟩
    rw [mul_comm]
    exact (SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (N,k)) le_rfl le_rfl (G q) y).trans
      (mul_le_mul_of_nonneg_left (hb q hq).le (by positivity))
  · intro h
    apply ((schwartz_withSeminorms ℝ E ℂ).image_isVonNBounded_iff_seminorm_bounded G).mpr
    intro ⟨N,k⟩
    obtain ⟨C,hC,H⟩ := h k N
    refine ⟨C + 1, by linarith, fun q hq => lt_of_le_of_lt ?_ (by linarith : C < C+1)⟩
    apply SchwartzMap.seminorm_le_bound ℝ N k _ hC
    intro y
    rw [mul_comm]
    exact (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg y) (by linarith : ‖y‖ ≤ 1 + ‖y‖) N) (norm_nonneg _)).trans
      (H q hq y)

/-- Pulling a bounded family back along a positive power preserves uniform Schwartz estimates. -/
theorem SchwartzSliceFamily.comp_pow {P K L : Type} [TopologicalSpace P] [NormedField K]
    [NormedField L] [NormedAlgebra ℝ L] {e : K ≃+* L} {R : P → K → ℂ}
    (hR : SchwartzSliceFamily e R) (n : ℕ) [NeZero n] :
    SchwartzSliceFamily e (fun q t => R q (t^n)) := by
  obtain ⟨G,hG,H⟩ := hR
  have hg : (fun y : L => y^n).HasTemperateGrowth := Function.HasTemperateGrowth.id'.pow n
  have growth (y : L) : ‖y‖ ≤ 1 * (1 + ‖y^n‖)^1 := by
    rw [one_mul,pow_one,norm_pow]
    rcases le_total ‖y‖ 1 with hy | hy
    · linarith [pow_nonneg (norm_nonneg y) n]
    · linarith [le_self_pow₀ hy (NeZero.ne n)]
  let A : SchwartzMap L ℂ →L[ℝ] SchwartzMap L ℂ := SchwartzMap.compCLM ℝ hg ⟨1,1,growth⟩
  refine ⟨A ∘ G, fun q t => ?_, fun T hT => ?_⟩
  · change R q (t^n) = G q ((e t)^n)
    simpa only [map_pow] using hG q (t^n)
  · apply (bounded_schwartz_family_iff _ _).mp
    rw [Set.image_comp]
    exact ((bounded_schwartz_family_iff _ _).mpr (H T hT)).image A

/-- An isometric field coordinate change preserves the compact-uniform Schwartz bounds. -/
theorem SchwartzSliceFamily.change_coordinates {P K L L' : Type} [TopologicalSpace P]
    [NormedField K] [NormedField L] [NormedField L'] [NormedAlgebra ℝ L] [NormedAlgebra ℝ L']
    {e : K ≃+* L} (he : Isometry e) (e' : K ≃+* L') (he' : Isometry e')
    {R : P → K → ℂ} (hR : SchwartzSliceFamily e R) : SchwartzSliceFamily e' R := by
  obtain ⟨G, hG, H⟩ := hR
  let r := e'.symm.trans e
  have hr : Isometry r := he.comp (show K ≃ᵢ L' from ⟨e'.toEquiv, he'⟩).symm.isometry
  let Lmap : L' ≃L[ℝ] L :=
    { toFun := r, invFun := r.symm, left_inv := r.left_inv, right_inv := r.right_inv
      map_add' := r.map_add, map_smul' := map_real_smul r hr.continuous
      continuous_toFun := hr.continuous
      continuous_invFun := (show L' ≃ᵢ L from ⟨r.toEquiv, hr⟩).symm.continuous }
  let A : SchwartzMap L ℂ →L[ℝ] SchwartzMap L' ℂ := SchwartzMap.compCLMOfContinuousLinearEquiv ℝ Lmap
  refine ⟨A ∘ G, fun q t => ?_, fun T hT => ?_⟩
  · change R q t = G q (e (e'.symm (e' t)))
    simpa using hG q t
  · apply (bounded_schwartz_family_iff _ _).mp
    rw [Set.image_comp]
    exact ((bounded_schwartz_family_iff _ _).mpr (H T hT)).image A

end MetaplecticPoisson
