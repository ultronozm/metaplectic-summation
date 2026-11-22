import MetaplecticSummation.Poisson
import MetaplecticSummation.RayFourier

noncomputable section
namespace MetaplecticPoisson
namespace Datum

open MeasureTheory Filter NumberField IsDedekindDomain
open scoped ContDiff Topology
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [hn : NeZero n] (d : Datum F n)

abbrev Weight (v : Place F) := (LocalField F v)ˣ → ℂ

def jacquet (v : Place F) (Φ : d.schwartz v) (c : (LocalField F v)ˣ) : ℂ :=
  ∫ y, Φ.val.1 c y * d.character.localValue F v (-y / (c : LocalField F v))
    ∂(selfDual F d.character v)

open Set in
theorem basic_x_outside (p : Prime F) (ht : p.asIdeal.absNorm.Coprime n)
    (x : (LocalField F (.inr p))ˣ) (y : LocalField F (.inr p)) (h : 1 < max ‖x.val‖ ‖y‖) :
    (d.basic (.inr p)).val.1 x y = 0 := by
  have hq : 1 ≤ (p.asIdeal.absNorm : ℝ) := by
    exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm p).le
  have he (k : ℕ) : max ‖x.val‖ ‖y‖ ≠ ((p.asIdeal.absNorm : ℝ)^(n*k))⁻¹ :=
    ne_of_gt ((inv_le_one_of_one_le₀ (one_le_pow₀ hq)).trans_lt h)
  simp [basic, dif_pos ht, basicCharts, he]

theorem jacquet_basic_nonintegral (p : Prime F) (ht : p.asIdeal.absNorm.Coprime n)
    (c : (LocalField F (.inr p))ˣ) (hc : 1 < ‖c.val‖) :
    d.jacquet (.inr p) (d.basic (.inr p)) c = 0 := by
  unfold jacquet
  simp only [d.basic_x_outside p ht c _ (hc.trans_le (le_max_left _ _)), zero_mul, integral_zero]

open Set in
theorem jacquet_basic_unit (p : Prime F) (ht : p.asIdeal.absNorm.Coprime n)
    (hψ : ∀ x : LocalField F (.inr p), ‖x‖ ≤ 1 → d.character.localValue F (.inr p) x = 1)
    (c : (LocalField F (.inr p))ˣ) (hc : ‖c.val‖ = 1) :
    d.jacquet (.inr p) (d.basic (.inr p)) c =
      ((selfDual F d.character (.inr p)).real {x | ‖x‖ ≤ 1} : ℂ) := by
  let O := {x : LocalField F (.inr p) | ‖x‖ ≤ 1}
  have hO : MeasurableSet O := (isClosed_le continuous_norm continuous_const).measurableSet
  unfold jacquet
  calc
    _ = ∫ x, O.indicator (fun _ => (1:ℂ)) x ∂(selfDual F d.character (.inr p)) := by
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : ‖x‖ ≤ 1
      · have he := d.basic_xChart_unit p ht c.val x hc hx
        simp only [xChart, c.ne_zero, ne_eq, not_false_eq_true, dif_pos] at he
        have hval : (d.basic (.inr p)).val.1 c x = 1 := by
          rwa [show Units.mk0 c.val c.ne_zero = c from Units.ext rfl] at he
        rw [hval, hψ _ (by simpa only [norm_div, norm_neg, hc, div_one] using hx),
          one_mul, indicator_of_mem (show x ∈ O from hx)]
      · rw [d.basic_x_outside p ht c x ((lt_of_not_ge hx).trans_le (le_max_right _ _)),
          zero_mul, indicator_of_notMem (show x ∉ O from hx)]
    _ = _ := by simp [integral_indicator hO, Measure.real, O]

def lineIntegral (v : Place F) (f : Weight v) : ℂ := by
  classical
  exact ∫ x, if h : x ≠ 0 then f (Units.mk0 x h) / (modulus F v x : ℂ) else 0
    ∂(selfDual F d.character v)

omit hn in
theorem lineIntegral_const_mul (v : Place F) (z : ℂ) (f : Weight v) :
    d.lineIntegral v (fun x => z * f x) = z * d.lineIntegral v f := by
  classical
  unfold lineIntegral
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  split_ifs <;> ring

omit hn in
/-- Multiplicative Haar integration is invariant under translation by a unit. -/
theorem lineIntegral_mul (v : Place F) (u : (LocalField F v)ˣ) (f : Weight v) :
    d.lineIntegral v (fun x => f (u*x)) = d.lineIntegral v f := by
  classical
  let g (w : Weight v) (x : LocalField F v) : ℂ :=
    if h : x ≠ 0 then w (Units.mk0 x h) / (modulus F v x : ℂ) else 0
  let m : ℂ := modulus F v u.val
  have hm : m ≠ 0 := Complex.ofReal_ne_zero.mpr (modulus_ne_zero v u)
  have hmod (x : LocalField F v) : modulus F v (u.val*x) = modulus F v u.val * modulus F v x := by
    cases v <;> simp [modulus,norm_mul,mul_pow]
  have he (x : LocalField F v) : g f (u.val*x) = g (fun a => f (u*a)) x / m := by
    by_cases hx : x = 0
    · simp [g,hx]
    · have hux := mul_ne_zero u.ne_zero hx
      simp only [g,dif_pos hux,dif_pos hx,hmod,Complex.ofReal_mul]
      rw [show Units.mk0 (u.val*x) hux = u * Units.mk0 x hx from Units.ext rfl]
      ring
  have h := d.integral_local_mul v u (g f)
  dsimp only at h
  simp_rw [he] at h
  rw [integral_div] at h
  exact (div_left_inj' hm).mp h

def archSmooth {K L : Type} [Field K] [NormedField L] [NormedAlgebra ℝ L]
    (e : K ≃+* L) (W : Kˣ → ℂ) : Prop := by
  classical
  exact ContDiffOn ℝ ∞ (fun x => if h : e.symm x ≠ 0 then W (Units.mk0 _ h) else 0) {0}ᶜ

def TestWeight (v : Place F) (W : Weight v) : Prop :=
  HasCompactSupport W ∧ (by
    classical
    cases v with
    | inr p => exact IsLocallyConstant W
    | inl w =>
      by_cases h : w.IsReal
      · exact archSmooth (InfinitePlace.Completion.ringEquivRealOfIsReal h) W
      · exact archSmooth (InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (InfinitePlace.not_isReal_iff_isComplex.mp h)) W)

end Datum
end MetaplecticPoisson
