import MetaplecticSummation.Arithmetic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Tactic.LinearCombination

noncomputable section
namespace MetaplecticPoisson.Datum
open MeasureTheory Set
open Classical

/-- The ordinary Fourier integral of a subgroup indicator is its volume times
the indicator of its annihilator. -/
theorem hat_addSubgroup_indicator {K : Type*} [NormedField K] [MeasurableSpace K] [BorelSpace K]
    (O : AddSubgroup K) (D : Set K) (hO : MeasurableSet (O : Set K))
    (μ : Measure K) [μ.IsAddHaarMeasure] (ψ : K → ℂ) (ha : ∀ x y, ψ (x+y) = ψ x * ψ y)
    (hperp : ∀ x : K, (∀ y ∈ O, ψ (x*y) = 1) ↔ x ∈ D) (y : K) :
    (∫ x, (O : Set K).indicator (fun _ => (1 : ℂ)) x * ψ (x*y) ∂μ) =
      D.indicator (fun _ => (μ.real (O : Set K) : ℂ)) y := by
  let g := (O : Set K).indicator (fun _ => (1 : ℂ))
  change (∫ x, g x * ψ (x*y) ∂μ) = _
  by_cases hy : y ∈ D
  · rw [indicator_of_mem hy]
    have he (x : K) : g x * ψ (x*y) = g x := by
      by_cases hx : x ∈ O
      · rw [mul_comm x y, (hperp y).mpr hy x hx, mul_one]
      · simp [g,hx]
    simp only [he, g, integral_indicator hO, integral_const, Measure.restrict_apply_univ,
      Complex.real_smul, mul_one, Measure.real]
  · obtain ⟨t, ht, hχ⟩ : ∃ t ∈ O, ψ (y*t) ≠ 1 := by
      by_contra! he
      exact hy ((hperp y).mp he)
    let f (x : K) := g x * ψ (x*y)
    have htrans (x : K) : f (x+t) = f x * ψ (y*t) := by
      have hmem : x + t ∈ O ↔ x ∈ O := O.add_mem_cancel_right ht
      simp only [f, g, indicator, SetLike.mem_coe, hmem, add_mul, ha, mul_assoc, mul_comm t y]
    have hi := integral_add_right_eq_self (μ := μ) f t
    simp_rw [htrans] at hi
    rw [integral_mul_const] at hi
    rw [indicator_of_notMem hy]
    exact by_contra fun h => hχ ((mul_eq_left₀ h).mp hi)

/-- Plancherel on the characteristic function of an additive compact open
subgroup makes the product of its volume and its annihilator’s volume one. -/
theorem volume_mul_annihilator {K : Type*} [NormedField K] [MeasurableSpace K]
    [BorelSpace K] (O : AddSubgroup K) (D : Set K) (hD : MeasurableSet D) (hO : IsClopen (O : Set K)) (hK : IsCompact (O : Set K))
    (μ : Measure K) [μ.IsAddHaarMeasure] (ψ : K → ℂ)
    (ha : ∀ x y, ψ (x+y) = ψ x * ψ y)
    (hperp : ∀ x : K, (∀ y ∈ O, ψ (x*y) = 1) ↔ x ∈ D)
    (hP : ∀ f : K → ℂ, Continuous f → HasCompactSupport f →
      (∫⁻ y, ‖∫ x, f x * ψ (x*y) ∂μ‖ₑ^2 ∂μ) = ∫⁻ x, ‖f x‖ₑ^2 ∂μ) :
    μ.real O * μ.real D = 1 := by
  let g := (O : Set K).indicator (fun _ => (1 : ℂ))
  let V := μ.real (O : Set K)
  have hV : 0 < V := ENNReal.toReal_pos
    (hO.isOpen.measure_pos μ ⟨0,O.zero_mem⟩).ne' hK.measure_ne_top
  have hhat (y : K) : (∫ x, g x * ψ (x*y) ∂μ) = D.indicator (fun _ => (V : ℂ)) y :=
    hat_addSubgroup_indicator O D hO.isOpen.measurableSet μ ψ ha hperp y
  have hp := hP g (hO.continuous_indicator continuous_const)
    (HasCompactSupport.intro hK fun _ h => indicator_of_notMem h _)
  have hind (A : Set K) (r : ℂ) (x : K) : ‖A.indicator (fun _ => r) x‖ₑ ^ 2 =
      A.indicator (fun _ => ‖r‖ₑ^2) x := by
    by_cases hx : x ∈ A <;> simp [hx]
  simp only [hhat, g, hind, lintegral_indicator hD, lintegral_indicator hO.isOpen.measurableSet, lintegral_const,
    Measure.restrict_apply_univ, enorm_one, one_pow, one_mul] at hp
  have he := congrArg ENNReal.toReal hp
  have hnorm : ‖(V : ℂ)‖ = V := by simp [abs_of_pos hV]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, toReal_enorm, hnorm] at he
  change V^2 * μ.real D = V at he
  apply mul_left_cancel₀ hV.ne' (b := V * μ.real D)
  linear_combination he

end MetaplecticPoisson.Datum
