import MetaplecticSummation.ArchimedeanLines
import MetaplecticSummation.FiniteHaar
import MetaplecticSummation.AdelicAnnihilator

/-! A local character satisfying Plancherel is nontrivial. -/
noncomputable section
open MeasureTheory Set
namespace MetaplecticPoisson
/-- A trivial character would give a nonzero constant transform for a nonnegative
compactly supported bump. This contradicts Plancherel on a field of infinite Haar measure. -/
theorem character_nontrivial_of_plancherel {K : Type*} [NontriviallyNormedField K]
    [ProperSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsAddHaarMeasure]
    (ψ : K → ℂ) (hP : ∀ f : K → ℂ, Continuous f → HasCompactSupport f →
      (∫⁻ y, ‖∫ x, f x * ψ (x*y) ∂μ‖ₑ ^ 2 ∂μ) = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ) :
    ∃ x, ψ x ≠ 1 := by
  by_contra! hψ
  obtain ⟨φ,hφ,hpos,hne⟩ : ∃ f : C(K,ℝ), HasCompactSupport f ∧ 0 ≤ f ∧ f 0 ≠ 0 :=
    exists_continuous_nonneg_pos 0
  let g (x : K) : ℂ := φ x
  have hc : Continuous g := Complex.continuous_ofReal.comp φ.continuous
  have hk : HasCompactSupport g := hφ.comp_left (show (0:ℝ) = (0:ℂ) by simp)
  have hi : (∫ x, g x ∂μ) ≠ 0 := by
    rw [show (∫ x, g x ∂μ) = ((∫ x, φ x ∂μ) : ℝ) from integral_ofReal]
    exact Complex.ofReal_ne_zero.mpr (φ.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hφ hpos hne).ne'
  have hr : (∫⁻ x, ‖g x‖ₑ^2 ∂μ) < ⊤ := by
    have hi' := (hc.pow 2).integrable_of_hasCompactSupport (μ := μ) (by simpa only [pow_two] using hk.mul_right (f' := g))
    simpa only [hasFiniteIntegral_iff_enorm,Pi.pow_apply,enorm_pow] using hi'.hasFiniteIntegral
  have H := hP g hc hk
  simp only [hψ,mul_one,lintegral_const,measure_univ_of_isAddLeftInvariant,
    ENNReal.mul_top (pow_ne_zero 2 (enorm_ne_zero.mpr hi))] at H
  exact hr.ne H.symm

end MetaplecticPoisson
