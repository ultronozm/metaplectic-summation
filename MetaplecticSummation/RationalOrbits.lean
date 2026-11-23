import MetaplecticSummation.Theta

/-! Rational row vectors and the upper unipotent stabilizer in Appendix B. -/

noncomputable section
namespace MetaplecticPoisson
open scoped Matrix MatrixGroups
open Classical
variable {F : Type} [Field F]

private def rowMul (z : F × F) (γ : SL(2,F)) : F × F :=
  (z.1*γ.1 0 0 + z.2*γ.1 1 0, z.1*γ.1 0 1 + z.2*γ.1 1 1)

private theorem rowMul_mul (z : F × F) (A B : SL(2,F)) :
    rowMul z (A*B) = rowMul (rowMul z A) B := by
  apply Prod.ext <;> simp [rowMul,Matrix.mul_apply,Fin.sum_univ_two] <;> ring

private theorem rowMul_one (z : F × F) : rowMul z 1 = z := by
  ext <;> simp [rowMul]

/-- Right multiplication on the nonzero rational row vectors. -/
def rationalRowPerm (γ : SL(2,F)) : RationalPoint F ≃ RationalPoint F := by
  let act (g : SL(2,F)) (z : RationalPoint F) : RationalPoint F :=
    ⟨rowMul z.val g,fun h => z.property (by
      rw [← rowMul_one z.val,← mul_inv_cancel g,rowMul_mul,h]
      simp [rowMul])⟩
  exact ⟨act γ,act γ⁻¹,
    fun z => Subtype.ext (by change rowMul (rowMul z.val γ) γ⁻¹ = z.val; rw [← rowMul_mul,mul_inv_cancel,rowMul_one]),
    fun z => Subtype.ext (by change rowMul (rowMul z.val γ⁻¹) γ = z.val; rw [← rowMul_mul,inv_mul_cancel,rowMul_one])⟩

theorem rationalRowPerm_mul (A B : SL(2,F)) (z : RationalPoint F) :
    rationalRowPerm (A*B) z = rationalRowPerm B (rationalRowPerm A z) :=
  Subtype.ext (rowMul_mul z.val A B)


theorem rationalRowPerm_val (A : SL(2,F)) (z : RationalPoint F) :
    (rationalRowPerm A z).val =
      (z.val.1*A.val 0 0 + z.val.2*A.val 1 0,z.val.1*A.val 0 1 + z.val.2*A.val 1 1) := rfl

theorem upperTransvection_matrix {F : Type} [CommRing F] (t : F) :
    (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 from zero_ne_one) t).val = !![1,t;0,1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.transvection_coe]
theorem lowerTransvection_matrix (t : F) :
    (Matrix.SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 from one_ne_zero) t).val = !![1,0;t,1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.transvection_coe]

def upperUnipotentParam {F : Type} [CommRing F] : Multiplicative F →* SL(2,F) where
  toFun t := Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 from zero_ne_one) t.toAdd
  map_one' := Matrix.SpecialLinearGroup.transvection_coeff_zero _
  map_mul' _ _ := Matrix.SpecialLinearGroup.transvection_add _ _ _

def upperUnipotent (F : Type) [CommRing F] : Subgroup SL(2,F) := (upperUnipotentParam (F := F)).range

private theorem upperParam_matrix (t : Multiplicative F) :
    (upperUnipotentParam t).val = !![1,t.toAdd;0,1] := upperTransvection_matrix t.toAdd

/-- The rational row vector (0,1). -/
def verticalPoint (F : Type) [Field F] : RationalPoint F := ⟨(0,1),fun h => one_ne_zero (congrArg Prod.snd h)⟩

def rationalBottomRow (A : SL(2,F)) : RationalPoint F := rationalRowPerm A (verticalPoint F)

theorem rationalBottomRow_val (A : SL(2,F)) : (rationalBottomRow A).val = (A.val 1 0,A.val 1 1) := by
  change ((0:F)*_ + 1*_,0*_+1*_) = _
  simp

private theorem row_fixed_iff (A : SL(2,F)) : rationalBottomRow A = verticalPoint F ↔ A ∈ upperUnipotent F := by
  constructor
  · intro h
    have he := congrArg Subtype.val h
    rw [rationalBottomRow_val] at he
    have hc : A.val 1 0 = 0 := congrArg Prod.fst he
    have hd : A.val 1 1 = 1 := congrArg Prod.snd he
    have ha := A.property
    rw [Matrix.det_fin_two,hc,hd,mul_one,mul_zero,sub_zero] at ha
    refine ⟨Multiplicative.ofAdd (A.val 0 1),Subtype.ext ?_⟩
    rw [upperParam_matrix]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ha,hc,hd]
  · rintro ⟨t,rfl⟩
    apply Subtype.ext
    rw [rationalBottomRow_val,upperParam_matrix]
    rfl

theorem rationalBottomRow_surjective : Function.Surjective (rationalBottomRow (F := F)) := by
  rintro ⟨⟨x,y⟩,h⟩
  by_cases hx : x = 0
  · subst x
    have hy : y ≠ 0 := fun h' => h (Prod.ext rfl h')
    let A : SL(2,F) := ⟨!![y⁻¹,0;0,y],by simp [Matrix.det_fin_two,hy]⟩
    exact ⟨A,Subtype.ext (rationalBottomRow_val A)⟩
  · let A : SL(2,F) := ⟨!![0,-x⁻¹;x,y],by simp [Matrix.det_fin_two,hx]⟩
    exact ⟨A,Subtype.ext (rationalBottomRow_val A)⟩

theorem rationalBottomRow_rel (A B : SL(2,F)) :
    QuotientGroup.rightRel (upperUnipotent F) A B ↔ rationalBottomRow A = rationalBottomRow B := by
  rw [QuotientGroup.rightRel_apply,← row_fixed_iff]
  have e : rationalRowPerm A (rationalBottomRow (B*A⁻¹)) = rationalBottomRow B := by
    change rationalRowPerm A (rationalRowPerm (B*A⁻¹) _) = _
    rw [← rationalRowPerm_mul,inv_mul_cancel_right]
    rfl
  constructor
  · intro h
    exact (congrArg (rationalRowPerm A) h).symm.trans e
  · intro h
    exact (rationalRowPerm A).injective (e.trans h.symm)

/-- The bottom row identifies the right cosets N(F) ∖ SL₂(F) with the nonzero rational vectors. -/
def rationalBottomRowEquiv :
    Quotient (QuotientGroup.rightRel (upperUnipotent F)) ≃ RationalPoint F := by
  let f := Quotient.lift (rationalBottomRow (F := F)) (fun A B h => (rationalBottomRow_rel A B).mp h)
  refine Equiv.ofBijective f ⟨?_,?_⟩
  · intro a b
    induction a using Quotient.inductionOn with | _ A => _
    induction b using Quotient.inductionOn with | _ B => _
    exact fun h => Quotient.sound ((rationalBottomRow_rel A B).mpr h)
  · intro z
    obtain ⟨A,h⟩ := rationalBottomRow_surjective z
    exact ⟨Quotient.mk _ A,h⟩

@[simp] theorem rationalBottomRowEquiv_mk (A : SL(2,F)) :
    rationalBottomRowEquiv (Quotient.mk _ A) = rationalBottomRow A := rfl

namespace Datum
variable [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

/-- The absolutely convergent orbit expansion used to unfold the integral in B.6. -/
theorem theta_coset_expansion (Φ : d.Schwartz) :
    Summable (fun q => ‖d.evaluation Φ (rationalBottomRowEquiv q)‖) ∧
      d.theta Φ = ∑' q, d.evaluation Φ (rationalBottomRowEquiv q) := by
  exact ⟨(d.summable_theta Φ).comp_injective rationalBottomRowEquiv.injective,
    (rationalBottomRowEquiv.tsum_eq (d.evaluation Φ)).symm⟩
end Datum
end MetaplecticPoisson
