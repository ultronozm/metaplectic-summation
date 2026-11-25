import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.MeanValue

/-! Real linear coordinates for continuous unitary additive characters.
The real-line derivative and exponential proofs are adapted from
OAI.RepresentationTheory.Weil.UnitarySplitting.RealCharacter in openai/math.
The basis argument follows OAI.RepresentationTheory.Weil.AdelicSplitting.RealCharacters.
See licenses/OpenAI-Lean-Apache-2.0.txt. -/

noncomputable section
namespace MetaplecticPoisson
open MeasureTheory
open scoped Topology FourierTransform
open Classical

private theorem continuous_real_character_hasDerivAt
    (ψ : AddChar ℝ ℂ) (hψ : Continuous (fun t : ℝ => ψ t)) :
    ∃ c : ℂ, ∀ t : ℝ, HasDerivAt (fun t : ℝ => ψ t) (c * ψ t) t := by
  let J : ℝ → ℂ := fun a => ∫ t in 0..a, ψ t
  have hJ (a : ℝ) : HasDerivAt J (ψ a) a :=
    intervalIntegral.integral_hasDerivAt_right (hψ.intervalIntegrable 0 a)
      hψ.aestronglyMeasurable.stronglyMeasurableAtFilter hψ.continuousAt
  obtain ⟨a, ha⟩ : ∃ a : ℝ, J a ≠ 0 := by
    by_contra! h
    have heq : J = fun _ => 0 := funext h
    have hh := hJ 0
    rw [heq] at hh
    have hbad := hh.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))
    simp only [ψ.map_zero_eq_one, one_ne_zero] at hbad
  have hformula (t : ℝ) : ψ t = (J (t + a) - J t) / J a := by
    have hint : J (t + a) - J t = ∫ s in t..t + a, ψ s := by
      have hh : J t + (∫ s in t..t + a, ψ s) = J (t + a) :=
        intervalIntegral.integral_add_adjacent_intervals
          (hψ.intervalIntegrable 0 t) (hψ.intervalIntegrable t (t + a))
      linear_combination -hh
    have hshift : (∫ s in t..t + a, ψ s) = ψ t * J a := by
      calc
        _ = ∫ s in 0..a, ψ (t + s) := by
          simpa only [add_zero] using
            (intervalIntegral.integral_comp_add_left (a := 0) (b := a) (fun s : ℝ => ψ s) t).symm
        _ = ψ t * J a := by
          simp_rw [ψ.map_add_eq_mul]
          rw [intervalIntegral.integral_const_mul]
    rw [hint, hshift, mul_div_cancel_right₀ _ ha]
  refine ⟨(ψ a - 1) / J a, fun t => ?_⟩
  have hd : HasDerivAt (fun t => (J (t + a) - J t) / J a)
      ((ψ (t + a) - ψ t) / J a) t := by
    simpa only [one_smul, Function.comp_apply, Pi.sub_apply, id_eq] using
      (((hJ (t + a)).scomp t ((hasDerivAt_id t).add_const a)).sub
        (hJ t)).div_const (J a)
  have hcoef : (ψ (t + a) - ψ t) / J a =
      (ψ a - 1) / J a * ψ t := by
    rw [ψ.map_add_eq_mul]
    ring
  convert hd using 1
  · exact funext hformula
  · exact hcoef.symm

private theorem continuous_real_character_exponential
    (ψ : AddChar ℝ ℂ) (hψ : Continuous (fun t : ℝ => ψ t)) :
    ∃ c : ℂ, ∀ t : ℝ, ψ t = Complex.exp ((t : ℂ) * c) := by
  obtain ⟨c, hc⟩ := continuous_real_character_hasDerivAt ψ hψ
  let f : ℝ → ℂ := fun t => ψ t * Complex.exp (-(t : ℂ) * c)
  have hf (t : ℝ) : HasDerivAt f 0 t := by
    have he : HasDerivAt (fun t : ℝ => Complex.exp (-(t : ℂ) * c))
        (Complex.exp (-(t : ℂ) * c) * (-c)) t := by
      convert (((hasDerivAt_id t).ofReal_comp.neg).mul_const c).cexp using 1 <;> simp
    have hz : c * ψ t * Complex.exp (-(t : ℂ) * c) +
        ψ t * (Complex.exp (-(t : ℂ) * c) * (-c)) = 0 := by ring
    simpa only [hz, Pi.mul_def] using (hc t).mul he
  have hconst (t : ℝ) : f t = 1 := by
    have hh := is_const_of_deriv_eq_zero (fun t => (hf t).differentiableAt)
      (fun t => (hf t).deriv) t 0
    simpa [f] using hh
  refine ⟨c, fun t => ?_⟩
  have hh := congrArg (fun z => z * Complex.exp ((t : ℂ) * c)) (hconst t)
  dsimp only [f] at hh
  rw [mul_assoc, ← Complex.exp_add] at hh
  have he : -(t : ℂ) * c + (t : ℂ) * c = 0 := by ring
  simpa only [he, Complex.exp_zero, mul_one, one_mul] using hh

private theorem real_character_frequency (ψ : AddChar ℝ ℂ) (hc : Continuous ψ)
    (hu : ∀ x, ‖ψ x‖ = 1) : ∃ r : ℝ, ∀ x, ψ x = (Real.fourierChar (r*x) : ℂ) := by
  obtain ⟨z,hz⟩ := continuous_real_character_exponential ψ hc
  have hre : z.re = 0 := by
    have h := hu 1
    rw [hz] at h
    simpa only [Complex.ofReal_one,one_mul,Complex.norm_exp,Real.exp_eq_one_iff] using h
  have he : z = (z.im : ℂ) * Complex.I := by apply Complex.ext <;> simp [hre]
  refine ⟨z.im / (2*Real.pi),fun x => ?_⟩
  rw [hz,Real.fourierChar_apply,show 2*Real.pi*(z.im/(2*Real.pi)*x) = z.im*x by field_simp]
  rw [Complex.ofReal_mul]
  conv_lhs => rw [he]
  ring_nf

theorem continuous_unitary_character_linear {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (ψ : AddChar E ℂ) (hc : Continuous ψ) (hu : ∀ x, ‖ψ x‖ = 1) :
    ∃ l : E →L[ℝ] ℝ, ∀ x, ψ x = (Real.fourierChar (l x) : ℂ) := by
  let b := Module.finBasis ℝ E
  let χ (i : Fin (Module.finrank ℝ E)) := ψ.compAddMonoidHom (LinearMap.toSpanSingleton ℝ E (b i)).toAddMonoidHom
  have hχ i : Continuous (χ i) := hc.comp (continuous_id.smul continuous_const)
  choose r hr using fun i => real_character_frequency (χ i) (hχ i) (fun t => hu (t • b i))
  let l : E →ₗ[ℝ] ℝ := ∑ i, r i • b.coord i
  refine ⟨LinearMap.toContinuousLinearMap l, fun x => ?_⟩
  have sum_repr : ψ x = ∏ i, ψ (b.repr x i • b i) := by
    conv_lhs => rw [← b.sum_repr x]
    exact map_prod ψ.toMonoidHom (fun i => Multiplicative.ofAdd (b.repr x i • b i)) Finset.univ
  rw [sum_repr]
  change _ = (Real.fourierChar (l x) : ℂ)
  have hm (i) : ψ (b.repr x i • b i) = (Real.fourierChar (r i*b.repr x i) : ℂ) := hr i _
  simp_rw [hm]
  let e := Circle.coeHom.compAddChar Real.fourierChar
  change (∏ i, e (r i*b.repr x i)) = e (l x)
  rw [show l x = ∑ i, r i*b.repr x i by simp [l,LinearMap.sum_apply,Module.Basis.coord_apply]]
  exact (map_prod e.toMonoidHom (fun i => Multiplicative.ofAdd (r i*b.repr x i)) Finset.univ).symm

end MetaplecticPoisson
