import MetaplecticSummation.SmoothFiniteLines
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-! Comparison of the two chart trivializations on pairs of rows of determinant one. -/
noncomputable section
namespace MetaplecticPoisson
open scoped Matrix MatrixGroups
open Classical

namespace RowPairing
variable {K : Type} [Field K]

def det (p q : Fin 2 → K) := p 0 * q 1 - p 1 * q 0

theorem det_vecMul (p q : Fin 2 → K) (m : SL(2,K)) :
    det (p ᵥ* m.val) (q ᵥ* m.val) = det p q := by
  have h := congrArg Matrix.det (show Matrix.of ![p ᵥ* m.val,q ᵥ* m.val] =
      Matrix.of ![p,q] * m.val by
    ext i j
    fin_cases i <;> rfl)
  rw [Matrix.det_mul,m.property,mul_one] at h
  simp only [Matrix.det_fin_two] at h
  exact h

/-- A function constant along determinant-one pairs is constant on the punctured plane. -/
theorem eq_of_det_one {B : Type*} {f : (Fin 2 → K) → B}
    (hf : ∀ p q, det p q = 1 → f p = f q) {p : Fin 2 → K} (hp : p ≠ 0) :
    f p = f ![1,0] := by
  have above (q : Fin 2 → K) (hy : q 1 ≠ 0) : f q = f ![1,0] := by
    let r : Fin 2 → K := ![(q 0-1)/q 1,1]
    apply (hf q r ?_).trans (hf ![1,0] r ?_).symm
    · simp [det,r,mul_div_cancel₀ _ hy]
    · simp [det,r]
  by_cases hy : p 1 ≠ 0
  · exact above p hy
  · have hx : p 0 ≠ 0 := fun h => hp (by ext i; fin_cases i <;> simp [h,not_ne_iff.mp hy])
    let r : Fin 2 → K := ![0,(p 0)⁻¹]
    exact (hf p r (by simp [det,r,hx])).trans (above r (by simp [r,hx]))

end RowPairing

namespace LineSymbol
variable {K : Type} [NontriviallyNormedField K] {n : ℕ} (H : LineSymbol K n)

/-- The transition between evaluation using X whenever available and using Y whenever
available. On an axis the two choices use the same chart. -/
def rowTransition (p : Fin 2 → K) : ℂˣ := H.pairing (liftUnit (p 0)) (liftUnit (p 1))

def rowPairX (p q : Fin 2 → K) : ℂˣ := H.pairing (liftUnit (p 0)) (-(liftUnit (q 0)))

def rowPairY (p q : Fin 2 → K) : ℂˣ := H.pairing (-(liftUnit (p 1))) (liftUnit (q 1))

/-- The determinant-one multiplier identity includes pairs on either coordinate axis. -/
theorem row_pairing (p q : Fin 2 → K) (h : RowPairing.det p q = 1) :
    H.rowTransition p * H.rowPairX p q = H.rowTransition q * H.rowPairY p q := by
  let X := liftUnit (p 0)
  let Y := liftUnit (p 1)
  let A := liftUnit (q 0)
  let B := liftUnit (q 1)
  have hs : H.pairing (B*X) ((-A)*Y) = 1 := by
    by_cases hz : p 0 * q 1 = 0
    · have e : -q 0*p 1 = 1 := by unfold RowPairing.det at h; linear_combination h - hz
      have hn := mul_ne_zero_iff.mp (e.trans_ne one_ne_zero)
      have he : (-A)*Y = 1 := Units.ext (by simpa [A,Y,liftUnit,neg_ne_zero.mp hn.1,hn.2] using e)
      rw [he,map_one]
    · have hn := mul_ne_zero_iff.mp hz
      have bx : ((B*X : Kˣ) : K) = q 1*p 0 := by simp [B,X,liftUnit,hn.1,hn.2]
      by_cases hw : p 1 * q 0 = 0
      · have e : B*X = 1 := Units.ext (by rw [bx,mul_comm]; simpa [RowPairing.det,hw] using h)
        simp [e]
      · have hy := mul_ne_zero_iff.mp hw
        apply H.steinberg
        rw [bx]
        simp only [A,Y,Units.val_mul,Units.val_neg,liftUnit_val hy.1,liftUnit_val hy.2]
        unfold RowPairing.det at h
        linear_combination h
  simp only [map_mul,MonoidHom.mul_apply] at hs
  have hr : H.pairing X Y * H.pairing X (-A) = (H.pairing B (-A) * H.pairing B Y)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    convert hs using 1
    ac_rfl
  change H.pairing X Y * H.pairing X (-A) = H.pairing A B * H.pairing (-Y) B
  rw [hr,mul_inv,← H.skew (-A) B,← H.skew Y B,← neg_one_mul A,← neg_one_mul Y]
  simp only [map_mul,MonoidHom.mul_apply]
  simp [mul_left_comm,mul_comm]

end LineSymbol
end MetaplecticPoisson
