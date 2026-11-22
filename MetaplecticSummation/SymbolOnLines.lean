import MetaplecticSummation.Core
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-! The Hilbert-symbol calculation on a line in §4.1. -/

namespace MetaplecticPoisson

variable {K : Type*} [Field K] {n : ℕ}

/-- Bimultiplicativity is recorded by the two monoid homomorphisms. -/
structure LineSymbol (K : Type*) [Field K] (n : ℕ) where
  pairing : Kˣ →* Kˣ →* ℂˣ
  torsion : ∀ a b, pairing a b ^ n = 1
  skew : ∀ a b, pairing a b = (pairing b a)⁻¹
  neg_self : ∀ a, pairing a (-a) = 1
  steinberg : ∀ a b : Kˣ, (a : K) + b = 1 → pairing a b = 1

namespace LineSymbol
variable (H : LineSymbol K n)

@[simp] theorem pow_left (a b : Kˣ) : H.pairing (a ^ n) b = 1 := by
  rw [map_pow, MonoidHom.pow_apply, H.torsion]

@[simp] theorem pow_right (a b : Kˣ) : H.pairing a (b ^ n) = 1 := by
  rw [map_pow, H.torsion]

theorem of_sum_eq_pow (hn : n ≠ 0) (a b : Kˣ) (t : K) (hab : (a : K) + b = t ^ n) :
    H.pairing a b = 1 := by
  by_cases ht : t = 0
  · have h : b = -a := by
      apply Units.ext
      simpa [ht, zero_pow hn] using (show (b : K) = -(a : K) + t ^ n by linear_combination hab)
    simpa [h] using H.neg_self a
  let u := Units.mk0 t ht
  have h : ((a / u ^ n : Kˣ) : K) + ((b / u ^ n : Kˣ) : K) = 1 := by
    simp only [Units.val_div_eq_div_val, Units.val_pow_eq_pow_val, Units.val_mk0, u]
    rw [← add_div, hab, div_self (pow_ne_zero _ ht)]
  have hs := H.steinberg _ _ h
  simpa only [map_div, MonoidHom.div_apply, H.pow_left, div_one, H.pow_right] using hs

/-- Identity of multipliers in the overlap of the X and Y charts. -/
theorem line_multiplier (hn : n ≠ 0) (x y a b : Kˣ) (t : K)
    (hline : (x : K) * b - (y : K) * a = t ^ n) :
    H.pairing x y * H.pairing x (-a) =
      H.pairing a b * (H.pairing y b * H.pairing (-1) b) := by
  have hs := H.of_sum_eq_pow hn (b*x) ((-a)*y) t (by
    change (b : K)*x + -(a : K)*y = t^n
    linear_combination hline)
  simp only [map_mul, MonoidHom.mul_apply] at hs
  have hprod : H.pairing x y * H.pairing x (-a) =
      (H.pairing b (-a) * H.pairing b y)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    convert hs using 1
    ac_rfl
  rw [hprod, mul_inv, ← H.skew (-a) b, ← H.skew y b, ← neg_one_mul a, map_mul,
    MonoidHom.mul_apply]
  ac_rfl

theorem integrands_agree (hn : n ≠ 0) {f : Charts K}
    (hf : Glues (fun a b => H.pairing a b) f) (x y a b : Kˣ) (t : K)
    (hline : (x : K) * b - (y : K) * a = t ^ n) :
    f.1 x y * (H.pairing x (-a) : ℂ) =
      (H.pairing a b : ℂ) * (f.2 x y * (H.pairing y b : ℂ) * (H.pairing (-1) b : ℂ)) := by
  have h := congrArg Units.val (H.line_multiplier hn x y a b t hline)
  simp only [Units.val_mul] at h
  rw [hf]
  linear_combination (f.2 x y) * h

end LineSymbol
end MetaplecticPoisson
