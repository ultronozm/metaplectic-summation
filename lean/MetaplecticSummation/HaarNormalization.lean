import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Complex.Basic

/-! Uniqueness of the Haar scalar in the self-dual Plancherel normalization. -/
noncomputable section
namespace MetaplecticPoisson
open MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal

/-- The Plancherel identity on continuous compactly supported tests for an integral kernel. -/
def KernelPlancherel {K : Type*} [TopologicalSpace K] [MeasurableSpace K]
    (kernel : K → K → ℂ) (μ : Measure K) : Prop :=
  ∀ f : K → ℂ, Continuous f → HasCompactSupport f →
    (∫⁻ y, ‖∫ x, f x * kernel x y ∂μ‖ₑ^2 ∂μ) = ∫⁻ x, ‖f x‖ₑ^2 ∂μ

/-- For a fixed integral kernel, at most one additive Haar measure satisfies the
Plancherel identity on continuous compactly supported tests. -/
theorem haar_eq_of_plancherel {K : Type*} [NormedField K] [LocallyCompactSpace K]
    [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] (kernel : K → K → ℂ)
    (μ ν : Measure K) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    (hμ : KernelPlancherel kernel μ) (hν : KernelPlancherel kernel ν) : ν = μ := by
  let c := addHaarScalarFactor ν μ
  have hc : 0 < c := addHaarScalarFactor_pos_of_isAddHaarMeasure ν μ
  have eqn : ν = c • μ := isAddLeftInvariant_eq_smul_of_regular ν μ
  obtain ⟨φ,hφ,_,hφ₀⟩ : ∃ φ : C(K,ℝ), HasCompactSupport φ ∧ 0 ≤ φ ∧ φ 0 ≠ 0 :=
    exists_continuous_nonneg_pos 0
  let f (x : K) : ℂ := φ x
  have hf : Continuous f := Complex.continuous_ofReal.comp φ.continuous
  have hk : HasCompactSupport f := hφ.comp_left Complex.ofReal_zero
  let J := ∫⁻ x, ‖f x‖ₑ^2 ∂μ
  have hJ : J ≠ 0 := by
    intro he
    have ha := (lintegral_eq_zero_iff (hf.enorm.measurable.pow_const 2)).mp he
    have hz : f =ᵐ[μ] 0 := by
      filter_upwards [ha] with x hx
      simpa using hx
    have hzero := (hf.ae_eq_iff_eq (μ := μ) continuous_zero).mp hz
    exact hφ₀ (Complex.ofReal_eq_zero.mp (congrFun hzero 0))
  have hJ' : J ≠ ⊤ := by
    have hi := (hf.pow 2).integrable_of_hasCompactSupport (μ := μ)
      (by simpa only [pow_two] using hk.mul_right (f' := f))
    exact (by simpa only [J,hasFiniteIntegral_iff_enorm,Pi.pow_apply,enorm_pow] using hi.hasFiniteIntegral : J < ⊤).ne
  have hp := hμ f hf hk
  have hp' := hν f hf hk
  have hen : ‖(c : ℂ)‖ₑ = (c : ℝ≥0∞) := by
    change ((‖(c : ℂ)‖₊ : ℝ≥0) : ℝ≥0∞) = _
    rw [Complex.nnnorm_real]
    exact congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) (Real.nnnorm_of_nonneg c.property)
  rw [eqn] at hp'
  simp_rw [integral_smul_nnreal_measure,NNReal.smul_def,Complex.real_smul,enorm_mul,mul_pow,hen] at hp'
  rw [lintegral_smul_measure,lintegral_smul_measure,lintegral_const_mul' _ _ (by finiteness),hp] at hp'
  change (c : ℝ≥0∞) * ((c : ℝ≥0∞)^2 * J) = c * J at hp'
  have H := congrArg ENNReal.toReal hp'
  simp only [ENNReal.toReal_mul,ENNReal.toReal_pow, ENNReal.coe_toReal] at H
  have hj : 0 < J.toReal := ENNReal.toReal_pos hJ hJ'
  have hc' : 0 < (c : ℝ) := hc
  have hsq : (c : ℝ)^2 = 1 := by
    have := (mul_left_cancel₀ hc'.ne' H)
    exact mul_right_cancel₀ hj.ne' (show (c : ℝ)^2*J.toReal = 1*J.toReal by simpa using this)
  have hc1 : c = 1 := NNReal.eq ((sq_eq_one_iff.mp hsq).resolve_right (by linarith))
  simpa [hc1] using eqn

end MetaplecticPoisson
