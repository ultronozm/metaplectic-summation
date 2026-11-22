import MetaplecticSummation.Core
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! The chart formulas of §5 on raw functions. The covariance identities hold
before one proves convergence, smoothness or preservation of the Schwartz space. -/

noncomputable section
namespace MetaplecticPoisson
open MeasureTheory

variable {K : Type*} [Field K] (h : Kˣ → Kˣ → ℂ)

/-- On the X chart the upper unipotent is translation in the second coordinate.
The transition function recovers its Y component off the fixed axis. -/
def upperShear (u : K) (f : Charts K) : Charts K := by
  classical
  exact (fun x y => f.1 x (y + u*x), fun x y =>
    if hx : x ≠ 0 then f.1 (Units.mk0 x hx) ((y : K) + u*x) / h (Units.mk0 x hx) y
    else f.2 0 y)

/-- The lower unipotent fixes the X-axis and has a shear formula on the Y chart. -/
def lowerShear (u : K) (f : Charts K) : Charts K := by
  classical
  exact (fun x y => if hy : y ≠ 0 then
    h x (Units.mk0 y hy) * f.2 ((x : K) + u*y) (Units.mk0 y hy) else f.1 x 0,
    fun x y => f.2 (x + u*y) y)

theorem upperShear_glues (hn : ∀ x y, h x y ≠ 0) (u : K) (f : Charts K) :
    Glues h (upperShear h u f) := by
  intro x y
  simp [upperShear, x.ne_zero, hn, mul_div_cancel₀]

theorem lowerShear_glues (u : K) (f : Charts K) : Glues h (lowerShear h u f) := by
  intro x y
  simp [lowerShear, y.ne_zero]

theorem upperShear_zero (hn : ∀ x y, h x y ≠ 0) {f : Charts K} (hf : Glues h f) :
    upperShear h 0 f = f := by
  ext x y
  · simp [upperShear]
  · by_cases hx : x = 0
    · simp [upperShear, hx]
    · simp [upperShear, hx, hf (Units.mk0 x hx) y, hn]

theorem lowerShear_zero {f : Charts K} (hf : Glues h f) : lowerShear h 0 f = f := by
  ext x y
  · by_cases hy : y = 0
    · simp [lowerShear, hy]
    · simpa [lowerShear, hy] using (hf x (Units.mk0 y hy)).symm
  · simp [lowerShear]

theorem upperShear_add (u w : K) (f : Charts K) :
    upperShear h u (upperShear h w f) = upperShear h (u+w) f := by
  ext x y
  · simp [upperShear, add_mul, add_assoc]
  · by_cases hx : x = 0 <;> simp [upperShear, hx, add_mul, add_assoc]

theorem lowerShear_add (u w : K) (f : Charts K) :
    lowerShear h u (lowerShear h w f) = lowerShear h (u+w) f := by
  ext x y
  · by_cases hy : y = 0 <;> simp [lowerShear, hy, add_mul, add_assoc]
  · simp [lowerShear, add_mul, add_assoc]

variable [MeasurableSpace K] (n : ℕ) (modulus : K → ℝ) (dx : Measure K)

/-- The X-chart equality of (5.4), for every line parameter including zero. -/
theorem radon_upper (u t : K) (f : Charts K) (a : Kˣ) (b : K) :
    (radon n h modulus dx (upperShear h u f) t).1 a b =
      (radon n h modulus dx f t).1 a (b + u*a) := by
  unfold radon upperShear
  dsimp only
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  split_ifs with hx
  · have coord : (x*b - t^n) / (a : K) + u*x = (x*(b + u*a) - t^n) / (a : K) := by
      field_simp
      ring
    simp only [Units.val_mk0, coord]
  · rfl

/-- The Y-chart equality of (5.4). -/
theorem radon_lower (u t : K) (f : Charts K) (a : K) (b : Kˣ) :
    (radon n h modulus dx (lowerShear h u f) t).2 a b =
      (radon n h modulus dx f t).2 (a + u*b) b := by
  unfold radon lowerShear
  dsimp only
  congr 1
  apply integral_congr_ae
  filter_upwards with y
  split_ifs with hy
  · have coord : (a*y + t^n) / (b : K) + u*y = ((a + u*b)*y + t^n) / (b : K) := by
      field_simp
      ring
    simp only [Units.val_mk0, coord]
  · rfl

theorem transform_upper (ψ : K → ℂ) (u : K) (f : Charts K) (a : Kˣ) (b : K) :
    (transform n ψ h modulus dx (upperShear h u f)).1 a b =
      (transform n ψ h modulus dx f).1 a (b + u*a) := by
  simp only [transform, radon_upper]

theorem transform_lower (ψ : K → ℂ) (u : K) (f : Charts K) (a : K) (b : Kˣ) :
    (transform n ψ h modulus dx (lowerShear h u f)).2 a b =
      (transform n ψ h modulus dx f).2 (a + u*b) b := by
  simp only [transform, radon_lower]

/-- Covariance of the twice-iterated integral on each shear's translation chart. -/
theorem transform_square_upper (ψ : K → ℂ) (u : K) (f : Charts K) (a : Kˣ) (b : K) :
    let T := transform n ψ h modulus dx
    (T (T (upperShear h u f))).1 a b = (T (T f)).1 a (b+u*a) := by
  let T := transform n ψ h modulus dx
  have he : (T (upperShear h u f)).1 = (upperShear h u (T f)).1 :=
    funext fun x => funext (transform_upper h n modulus dx ψ u f x)
  exact (congrArg (fun X => (T (X,(T f).2)).1 a b) he).trans
    (transform_upper h n modulus dx ψ u (T f) a b)

theorem transform_square_lower (ψ : K → ℂ) (u : K) (f : Charts K) (a : K) (b : Kˣ) :
    let T := transform n ψ h modulus dx
    (T (T (lowerShear h u f))).2 a b = (T (T f)).2 (a+u*b) b := by
  let T := transform n ψ h modulus dx
  have he : (T (lowerShear h u f)).2 = (lowerShear h u (T f)).2 :=
    funext fun x => funext (transform_lower h n modulus dx ψ u f x)
  exact (congrArg (fun Y => (T ((T f).1,Y)).2 a b) he).trans
    (transform_lower h n modulus dx ψ u (T f) a b)

end MetaplecticPoisson
