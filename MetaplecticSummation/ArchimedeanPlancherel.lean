import MetaplecticSummation.ArchimedeanCharacters
import MetaplecticSummation.HaarNormalization
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Fourier.LpSpace
/-! Plancherel for an arbitrary nontrivial continuous unitary character of ℝ or ℂ.
The identification of the integral and L² Fourier transforms uses test pairings
as in OAI.MathematicalPhysics.Boltzmann.Collision.FourierL2Identification.
See licenses/OpenAI-Lean-Apache-2.0.txt. -/
noncomputable section
namespace MetaplecticPoisson
open MeasureTheory InnerProductSpace
open scoped FourierTransform RealInnerProductSpace ContDiff ENNReal NNReal SchwartzMap
variable {L : Type} [RCLike L]

/-- Plancherel for the ordinary Bochner Fourier integral on the real or
complex line, with Euclidean volume. -/
theorem euclidean_integral_plancherel {f : L → ℂ} (hi : Integrable f) (h₂ : MemLp f 2) :
    (∫⁻ y, ‖𝓕 f y‖ₑ^2) = ∫⁻ x, ‖f x‖ₑ^2 := by
  let g := h₂.toLp f
  have hc : Continuous (𝓕 f) := VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ hi
  let G : Lp ℂ 2 (volume : Measure L) := 𝓕 g
  have ae : (𝓕 f) =ᵐ[volume] ⇑G := by
    apply ae_eq_of_integral_contDiff_smul_eq hc.locallyIntegrable ((Lp.memLp G).locallyIntegrable (by norm_num))
    intro φ hφ hK
    let φc := Complex.ofRealCLM ∘ φ
    have hdc : ContDiff ℝ ∞ φc := Complex.ofRealCLM.contDiff.comp hφ
    have hkc : HasCompactSupport φc := hK.comp_left rfl
    let s := hkc.toSchwartzMap hdc
    have swap : (∫ x, (𝓕 s) x * f x) = ∫ x, s x * 𝓕 f x := by
      have flip : (innerₗ L).flip = innerₗ L := by
        apply LinearMap.ext
        intro a
        apply LinearMap.ext
        intro b
        exact real_inner_comm a b
      have h := VectorFourier.integral_fourierIntegral_smul_eq_flip (μ := volume) (ν := volume) (L := innerₗ L)
        Real.continuous_fourierChar continuous_inner s.integrable hi
      rw [flip] at h
      exact h
    have hd := congrArg (fun T : 𝓢'(L,ℂ) => T s) (Lp.fourier_toTemperedDistribution_eq g)
    change (∫ x, (φ x:ℂ) * 𝓕 f x) = ∫ x, (φ x:ℂ) * G x
    calc
      _ = ∫ x, (𝓕 s) x * f x := swap.symm
      _ = ∫ x, (𝓕 s) x • g x := by
        apply integral_congr_ae
        filter_upwards [h₂.coeFn_toLp] with x hx
        rw [show g x = f x from hx,smul_eq_mul]
      _ = ∫ x, s x • G x := by simpa only [G,TemperedDistribution.fourier_apply,Lp.toTemperedDistribution_apply] using hd
      _ = _ := rfl
  have hn : eLpNorm (𝓕 f) 2 volume = eLpNorm f 2 volume := by
    rw [eLpNorm_congr_ae ae,← Lp.enorm_def,← Lp.enorm_toLp h₂]
    simpa only [ofReal_norm] using congrArg ENNReal.ofReal (Lp.norm_fourier_eq g)
  have sq (h : L → ℂ) : (∫⁻ x, ‖h x‖ₑ^2) = eLpNorm h 2 volume ^ 2 := by
    simpa using (eLpNorm_nnreal_pow_eq_lintegral (μ := volume) (f := h) (p := 2) (by norm_num)).symm
  rw [sq,sq,hn]

/-- In inner-product coordinates the nontrivial character of the field
pairing differs from the standard Fourier character by a linear isomorphism. -/
theorem character_frequency_equiv {L : Type} [RCLike L] (χ : AddChar L ℂ) (hc : Continuous χ)
    (hu : ∀ t, ‖χ t‖ = 1) (hn : ∃ t, χ t ≠ 1) :
    ∃ T : L ≃L[ℝ] L, ∀ x y, χ (x*y) = (Real.fourierChar (-inner ℝ y (T x)) : ℂ) := by
  obtain ⟨l,hl⟩ := continuous_unitary_character_linear χ hc hu
  let B := ((ContinuousLinearMap.compL ℝ L L ℝ) (-l)).comp (ContinuousLinearMap.mul ℝ L)
  let A := continuousLinearMapOfBilin B
  have pair (x y : L) : inner ℝ (A x) y = -l (x*y) := continuousLinearMapOfBilin_apply B x y
  have hi : Function.Injective A := by
    apply (injective_iff_map_eq_zero A).2
    intro x hx
    by_contra he
    obtain ⟨t,ht⟩ := hn
    have h := pair x (t/x)
    rw [hx,inner_zero_left,mul_div_cancel₀ _ he] at h
    rw [hl,show l t = 0 by simpa using h] at ht
    simp at ht
  let T := (LinearEquiv.ofInjectiveEndo A.toLinearMap hi).toContinuousLinearEquiv
  refine ⟨T,fun x y => ?_⟩
  change χ (x*y) = (Real.fourierChar (-inner ℝ y (A x)) : ℂ)
  rw [real_inner_comm,pair,neg_neg,hl]

/-- The self-dual positive Haar normalization for an arbitrary nontrivial
continuous unitary additive character of the real or complex field. -/
theorem exists_rclike_plancherel (χ : AddChar L ℂ) (hc : Continuous χ)
    (hu : ∀ x, ‖χ x‖ = 1) (hn : ∃ x, χ x ≠ 1) :
    ∃ μ : Measure L, μ.IsAddHaarMeasure ∧ KernelPlancherel (fun x y => χ (x*y)) μ := by
  obtain ⟨T,hT⟩ := character_frequency_equiv χ hc hu hn
  let ν := (volume : Measure L).map T
  letI : ν.IsAddHaarMeasure := T.isAddHaarMeasure_map volume
  let c := Measure.addHaarScalarFactor ν volume
  have hc₀ : 0 < c := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure ν volume
  have eqν : ν = c • volume := Measure.isAddLeftInvariant_eq_smul _ _
  let r := (NNReal.sqrt c)⁻¹
  have hr : r ≠ 0 := inv_ne_zero (by simpa using hc₀.ne')
  have cancel : r^2*c = 1 := by
    dsimp only [r]
    rw [inv_pow,NNReal.sq_sqrt,inv_mul_cancel₀ hc₀.ne']
  refine ⟨r • volume,Measure.IsAddHaarMeasure.nnreal_smul _ hr,?_⟩
  intro f hf hK
  have euclid := euclidean_integral_plancherel (hf.integrable_of_hasCompactSupport hK)
    (hf.memLp_of_hasCompactSupport hK)
  have transform (y : L) : (∫ x, f x * χ (x*y)) = 𝓕 f (T y) := by
    rw [Real.fourier_eq]
    apply integral_congr_ae (.of_forall fun x => ?_)
    rw [mul_comm x y,hT]
    exact mul_comm _ _
  have mapped : (∫⁻ y, ‖𝓕 f (T y)‖ₑ^2) = (c : ℝ≥0∞) * ∫⁻ x, ‖f x‖ₑ^2 := by
    apply Eq.trans (b := ∫⁻ z, ‖𝓕 f z‖ₑ^2 ∂ν) (lintegral_map_equiv (μ := volume) _ T.toHomeomorph.toMeasurableEquiv).symm
    rw [eqν,lintegral_smul_measure,euclid]
    rfl
  have hen : ‖(r : ℂ)‖ₑ = (r : ℝ≥0∞) := by
    change ((‖(r : ℂ)‖₊ : ℝ≥0) : ℝ≥0∞) = _
    rw [Complex.nnnorm_real]
    exact congrArg (fun a : ℝ≥0 => (a : ℝ≥0∞)) (Real.nnnorm_of_nonneg r.property)
  simp_rw [integral_smul_nnreal_measure,NNReal.smul_def,Complex.real_smul,enorm_mul,mul_pow,hen,transform]
  rw [lintegral_smul_measure,lintegral_smul_measure,lintegral_const_mul' _ _ (by finiteness),mapped]
  have h : (r:ℝ≥0∞)^2*(c:ℝ≥0∞) = 1 := by exact_mod_cast cancel
  change (r:ℝ≥0∞)*(_*(_*_)) = (r:ℝ≥0∞)*_
  rw [← mul_assoc ((r:ℝ≥0∞)^2),h,one_mul]

end MetaplecticPoisson
