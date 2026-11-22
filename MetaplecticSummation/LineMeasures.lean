import MetaplecticSummation.SymbolOnLines
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.MeasureTheory.Group.Integral

/-! Change of coordinates on the lines in §4.1 and gluing of the Fourier transform. -/

noncomputable section
namespace MetaplecticPoisson
open MeasureTheory MeasureTheory.Measure
open scoped NNReal
open Classical

variable {K : Type*} [NormedField K] [LocallyCompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (dx : Measure K) [dx.IsAddHaarMeasure] [dx.Regular]

/-- Change of variables under an affine map of a local field. The scalar is the
inverse of the modulus of the linear part. -/
theorem integral_unit_mul_add (u : Kˣ) (c : K) (g : K → ℂ) :
    (∫ x, g ((u : K) * x + c) ∂dx) =
      (distribHaarChar K u⁻¹ : ℝ≥0) • ∫ y, g y ∂dx := by
  have he := integral_domSMul (μ := dx) (DomMulAct.mk u⁻¹) (fun y => g (y+c))
  have hm := isAddLeftInvariant_eq_smul_of_regular (DomMulAct.mk u⁻¹ • dx) dx
  rw [addHaarScalarFactor_smul_eq_distribHaarChar] at hm
  rw [hm, integral_smul_nnreal_measure] at he
  simpa [Units.smul_def, integral_add_right_eq_self] using he.symm

/-- The two normalized line integrals glue for every parameter, including zero.
The modulus is specified on units by its Haar scaling property. -/
theorem LineSymbol.radon_glues {n : ℕ} (H : LineSymbol K n) (hn : n ≠ 0)
    [NullSingletonClass dx] (m : K → ℝ) (hm : ∀ u : Kˣ, m u = distribHaarChar K u)
    {f : Charts K} (hf : Glues (fun u v => H.pairing u v) f) (t : K) :
    Glues (fun u v => H.pairing u v) (radon n (fun u v => H.pairing u v) m dx f t) := by
  intro a b
  let y (x : K) := (x*b-t^n)/(a : K)
  let X (x : K) : ℂ := if hx : x ≠ 0 then
    f.1 (Units.mk0 x hx) (y x) * (H.pairing (Units.mk0 x hx) (-a) : ℂ) else 0
  let Y (z : K) : ℂ := if hz : z ≠ 0 then
    f.2 (((a : K)*z+t^n)/b) (Units.mk0 z hz) * (H.pairing (Units.mk0 z hz) b : ℂ) *
      (H.pairing (-1) b : ℂ) else 0
  change (∫ x, X x ∂dx) / (m a : ℂ) = (H.pairing a b : ℂ) * ((∫ z, Y z ∂dx) / (m b : ℂ))
  have he : (∫ x, X x ∂dx) = (H.pairing a b : ℂ) * ∫ x, Y (y x) ∂dx := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [dx.ae_ne 0, dx.ae_ne (t^n / (b : K))] with x hx hxb
    have hy : y x ≠ 0 := div_ne_zero (sub_ne_zero.mpr (mt (eq_div_iff b.ne_zero).mpr hxb)) a.ne_zero
    have hline : x * (b : K) - y x * (a : K) = t^n := by dsimp [y]; field_simp; ring
    have hx' : ((a : K) * y x + t^n) / b = x := by
      apply (div_eq_iff b.ne_zero).mpr
      linear_combination -hline
    simpa [X, Y, hx, hy, hx'] using H.integrands_agree hn hf (Units.mk0 x hx)
      (Units.mk0 (y x) hy) a b t hline
  have hc : (∫ x, Y (y x) ∂dx) = (distribHaarChar K (b/a)⁻¹ : ℝ≥0) • ∫ z, Y z ∂dx := by
    rw [← integral_unit_mul_add dx (b/a) (-(t^n)/(a : K)) Y]
    apply integral_congr_ae
    filter_upwards with x
    congr 1
    dsimp [y]
    rw [Units.val_div_eq_div_val]
    ring
  have hd : distribHaarChar K (a/b) = distribHaarChar K a / distribHaarChar K b := by
    apply (eq_div_iff (distribHaarChar_pos (A := K) (g := b)).ne').mpr
    rw [← map_mul, div_mul_cancel]
  rw [he, hc, hm, hm, inv_div, hd, NNReal.smul_def, Complex.real_smul, NNReal.coe_div,
    Complex.ofReal_div]
  have ha : ((distribHaarChar K a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (distribHaarChar_pos (A := K) (g := a)).ne'
  have hb : ((distribHaarChar K b : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (distribHaarChar_pos (A := K) (g := b)).ne'
  field_simp

/-- Integrating the glued line integrals in the outer variable gives a genuine
Fourier transform as soon as the Radon transforms glue. -/
theorem transform_glues_of_radon_glues {k : Type*} [Field k] [MeasurableSpace k]
    (n : ℕ) (ψ : k → ℂ) (h : kˣ → kˣ → ℂ) (m : k → ℝ) (μ : Measure k) (f : Charts k)
    (hr : ∀ t, Glues h (radon n h m μ f t)) : Glues h (transform n ψ h m μ f) := by
  intro a b
  dsimp [transform]
  simp_rw [hr _ a b, ← mul_assoc, mul_comm (ψ _) (h a b), mul_assoc]
  rw [integral_const_mul]
  ring

end MetaplecticPoisson
