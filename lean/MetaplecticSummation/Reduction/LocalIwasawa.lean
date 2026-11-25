import MetaplecticSummation.Reduction.Diagonal

/-! Bounded local factors of adelic SL₂ matrices for the reduction in Proposition B.6. -/
noncomputable section
namespace MetaplecticPoisson
open scoped Matrix MatrixGroups
open Classical

/-- The two compact charts for the nonzero bottom row. -/
def iwasawaChart {R : Type} [CommRing R] (swap : Bool) (r : R) : SL(2,R) :=
  if swap then ⟨!![0,-1;1,r], by simp [Matrix.det_fin_two]⟩
  else ⟨!![1,0;r,1], by simp [Matrix.det_fin_two]⟩

/-- The larger bottom-row entry fixes the absolute value of the torus factor.
The final factor has entries bounded by one, at real, complex and finite places. -/
theorem exists_local_iwasawa {K : Type} [NormedField K] (g : SL(2,K)) :
    ∃ (u : K) (a : Kˣ) (swap : Bool) (r : K), ‖r‖ ≤ 1 ∧
      ‖(a⁻¹).val‖ = max ‖g.val 1 0‖ ‖g.val 1 1‖ ∧
      ‖u‖ ≤ max ‖g.val 0 0‖ ‖g.val 0 1‖ * ‖a.val‖ ∧
      g = upperUnipotentParam (Multiplicative.ofAdd u) * diagonalSL a * iwasawaChart swap r := by
  let c := g.val 1 0
  let d := g.val 1 1
  let b := g.val 0 1
  let p := g.val 0 0
  have det : p*d-b*c = 1 := by simpa only [p,b,c,d,Matrix.det_fin_two] using g.property
  have entries : g.val = !![p,b;c,d] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have matrix (u : K) : (upperUnipotentParam (Multiplicative.ofAdd u)).val = !![1,u;0,1] := upperTransvection_matrix u
  by_cases h : ‖c‖ ≤ ‖d‖
  · have hd : d ≠ 0 := by
      intro hd
      have hc : c = 0 := norm_le_zero_iff.mp (by simpa [hd] using h)
      simp [hd,hc] at det
    let a := (Units.mk0 d hd)⁻¹
    refine ⟨b/d,a,false,c/d,?_,?_,?_,?_⟩
    · rw [norm_div]
      exact (div_le_one (norm_pos_iff.mpr hd)).mpr h
    · change ‖d‖ = max ‖c‖ ‖d‖
      exact (max_eq_right h).symm
    · change ‖b/d‖ ≤ max ‖p‖ ‖b‖ * ‖d⁻¹‖
      rw [norm_div, norm_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (le_max_right ..) (by positivity)
    · apply Subtype.ext
      change g.val = (upperUnipotentParam _).val * (diagonalSL a).val * !![1,0;c/d,1]
      rw [entries,matrix,diagonalSL_matrix]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply,Fin.sum_univ_two,a,hd]
      all_goals field_simp [hd]
      linear_combination det
  · have h' := le_of_not_ge h
    have hc : c ≠ 0 := by
      intro hc
      exact h (by simp [hc])
    let a := (Units.mk0 c hc)⁻¹
    refine ⟨p/c,a,true,d/c,?_,?_,?_,?_⟩
    · rw [norm_div]
      exact (div_le_one (norm_pos_iff.mpr hc)).mpr h'
    · change ‖c‖ = max ‖c‖ ‖d‖
      exact (max_eq_left h').symm
    · change ‖p/c‖ ≤ max ‖p‖ ‖b‖ * ‖c⁻¹‖
      rw [norm_div, norm_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (le_max_left ..) (by positivity)
    · apply Subtype.ext
      change g.val = (upperUnipotentParam _).val * (diagonalSL a).val * !![0,-1;1,d/c]
      rw [entries,matrix,diagonalSL_matrix]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply,Fin.sum_univ_two,a,hc]
      all_goals field_simp [hc]
      linear_combination -det

/-- At an integral finite-place matrix the bottom row is primitive. -/
theorem max_norm_bottomRow_of_integral {K : Type} [NormedField K] [IsUltrametricDist K]
    (g : SL(2,K)) (hg : ∀ i j, ‖g.val i j‖ ≤ 1) :
    max ‖g.val 1 0‖ ‖g.val 1 1‖ = 1 := by
  apply le_antisymm (max_le (hg _ _) (hg _ _))
  have hd := g.property
  rw [Matrix.det_fin_two, sub_eq_add_neg] at hd
  have h := IsUltrametricDist.norm_add_le_max (g.val 0 0 * g.val 1 1) (-(g.val 0 1 * g.val 1 0))
  rw [hd,norm_one,norm_neg,norm_mul,norm_mul] at h
  refine h.trans (max_le ?_ ?_)
  · exact (mul_le_of_le_one_left (norm_nonneg _) (hg _ _)).trans (le_max_right ..)
  · exact (mul_le_of_le_one_left (norm_nonneg _) (hg _ _)).trans (le_max_left ..)

/-- The torus factor is a unit of norm one and the shear is integral
at each finite place where the input matrix has integral entries. -/
theorem exists_integral_local_iwasawa {K : Type} [NormedField K] [IsUltrametricDist K]
    (g : SL(2,K)) (hg : ∀ i j, ‖g.val i j‖ ≤ 1) :
    ∃ (u : K) (a : Kˣ) (swap : Bool) (r : K), ‖u‖ ≤ 1 ∧ ‖a.val‖ = 1 ∧ ‖r‖ ≤ 1 ∧
      g = upperUnipotentParam (Multiplicative.ofAdd u) * diagonalSL a * iwasawaChart swap r := by
  obtain ⟨u,a,swap,r,hr,ha,hu,he⟩ := exists_local_iwasawa g
  rw [max_norm_bottomRow_of_integral g hg, Units.val_inv_eq_inv_val, norm_inv, inv_eq_one] at ha
  refine ⟨u,a,swap,r,?_,ha,hr,he⟩
  rw [ha,mul_one] at hu
  exact hu.trans (max_le (hg _ _) (hg _ _))

end MetaplecticPoisson
