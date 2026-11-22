import MetaplecticSummation.Dilations
import MetaplecticSummation.Jacquet.Local
import MetaplecticSummation.LineMoments

/-! The power average of a test lift and the leading term of its transform. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open MeasureTheory
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

def powerAverage (v : Place F) (f : Charts (LocalField F v)) : Charts (LocalField F v) :=
  let avg := fun g : Weight v => d.lineIntegral v fun x =>
    if ∃ u : (LocalField F v)ˣ, x = u^n then (modulus F v x ^ (1+1/(n : ℝ)) : ℝ) * g x else 0
  (fun x y => avg fun a => (dilateCharts a f).1 x y,
   fun x y => avg fun a => (dilateCharts a f).2 x y)

/-- The X-chart of the power average of a Jacquet lift, in terms of the weighted
moment on the power class of its first coordinate (equation `eq:lift-average`). -/
theorem powerAverage_jacquetLift (v : Place F) (W : Weight v) (β : LocalField F v → ℂ)
    (x : (LocalField F v)ˣ) (y : LocalField F v) :
    (d.powerAverage v (d.jacquetLift v W β)).1 x y =
      β (y / x.val) / ((modulus F v x.val ^ (1 + 1 / (n : ℝ)) : ℝ) : ℂ) *
        d.lineIntegral v (fun t =>
          if (QuotientGroup.mk t : PowerClass n v) = QuotientGroup.mk x then
            W t * ((modulus F v t.val ^ (1 / (n : ℝ)) : ℝ) : ℂ) else 0) := by
  let m (u : (LocalField F v)ˣ) := modulus F v u.val
  have pos (u : (LocalField F v)ˣ) : 0 < m u := by
    cases v <;> simp [m,modulus,norm_pos_iff,u.ne_zero,pow_pos (norm_pos_iff.mpr u.ne_zero)]
  let s := 1 / (n : ℝ)
  let g (t : (LocalField F v)ˣ) : ℂ :=
    if (QuotientGroup.mk t : PowerClass n v) = QuotientGroup.mk x then W t * (m t ^ s : ℝ) else 0
  let b := β (y / x.val) / ((m x ^ (1 + s) : ℝ) : ℂ)
  unfold powerAverage
  dsimp only
  change _ = b * d.lineIntegral v g
  rw [← d.lineIntegral_mul v x g,← d.lineIntegral_const_mul]
  congr 1
  funext a
  have coset : (QuotientGroup.mk (x*a) : PowerClass n v) = QuotientGroup.mk x ↔
      ∃ u : (LocalField F v)ˣ, a = u^n := by
    rw [QuotientGroup.eq_iff_div_mem,mul_comm x a,mul_div_cancel_right]
    exact ⟨fun ⟨u,hu⟩ => ⟨u,hu.symm⟩,fun ⟨u,hu⟩ => ⟨u,hu.symm⟩⟩
  change (if ∃ u : (LocalField F v)ˣ, a = u^n then
    ((m a ^ (1+s) : ℝ) : ℂ) * jacquetLiftX v W β (a*x) (a.val*y) else 0) = b * g (x*a)
  simp only [g,coset]
  split_ifs
  · have hm : m (a*x) = m a * m x := by cases v <;> simp [m,modulus,norm_mul,mul_pow]
    have ratio : a.val*y / (a*x).val = y / x.val := by rw [Units.val_mul]; field_simp
    rw [jacquetLiftX,ratio,mul_comm x a]
    change ((m a ^ (1+s) : ℝ) : ℂ) * ((m (a*x) : ℂ)⁻¹ * W (a*x) * β (y/x.val)) =
      β (y/x.val) / ((m x ^ (1+s) : ℝ) : ℂ) * (W (a*x) * ((m (a*x)^s : ℝ) : ℂ))
    rw [hm,Real.mul_rpow (pos a).le (pos x).le,Real.rpow_add (pos a),Real.rpow_add (pos x)]
    simp only [Real.rpow_one,Complex.ofReal_mul]
    field_simp [Complex.ofReal_ne_zero.mpr (pos a).ne', Complex.ofReal_ne_zero.mpr (pos x).ne',
      Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (pos x) s).ne']
  · exact (mul_zero _).symm

theorem powerAverage_glues (v : Place F) {f : Charts (LocalField F v)} (hf : Glues (d.symbol v) f) :
    Glues (d.symbol v) (d.powerAverage v f) := by
  intro x y
  unfold powerAverage
  dsimp only
  rw [← d.lineIntegral_const_mul]
  congr 1
  funext a
  split_ifs with ha
  · obtain ⟨u,rfl⟩ := ha
    rw [d.dilateCharts_glues v u hf x y]
    ring
  · rw [mul_zero]

/-- Vanishing of all the power-class moments kills the average in both charts. -/
theorem powerAverage_jacquetLift_eq_zero (v : Place F) (W : Weight v) (β : LocalField F v → ℂ)
    (h : ∀ c : PowerClass n v, d.lineIntegral v (fun t =>
      if (QuotientGroup.mk t : PowerClass n v) = c then
        W t * ((modulus F v t.val ^ (1 / (n : ℝ)) : ℝ) : ℂ) else 0) = 0) :
    d.powerAverage v (d.jacquetLift v W β) = 0 := by
  let f := d.jacquetLift v W β
  have hx (x : (LocalField F v)ˣ) (y : LocalField F v) : (d.powerAverage v f).1 x y = 0 := by
    dsimp only [f]
    rw [d.powerAverage_jacquetLift,h,mul_zero]
  refine Prod.ext (funext fun x => funext fun y => hx x y) (funext fun x => funext fun y => ?_)
  by_cases hn : x = 0
  · subst x
    simp [powerAverage,dilateCharts,jacquetLift,lineIntegral]
  · let x' := Units.mk0 x hn
    have eqn := d.powerAverage_glues v (d.jacquetLift_glues v W β) x' y
    rw [hx] at eqn
    exact (mul_eq_zero.mp eqn.symm).resolve_left (d.unitPairing v x' y).ne_zero

def intertwiner (v : Place F) (f : Charts (LocalField F v)) :=
  radon n (d.symbol v) (modulus F v) (selfDual F d.character v) f 1

theorem leading_fourier_test (v : Place F) (Φ : d.schwartz v) (h : Φ.val ∈ d.testSet v) :
    d.leading v (d.fourier v Φ) =
      ((n : ℂ) / ((modulus F v (n : LocalField F v) ^ (3/2 : ℝ) : ℝ) : ℂ)) •
        d.intertwiner v (d.powerAverage v Φ.val) := by sorry

end MetaplecticPoisson.Datum
