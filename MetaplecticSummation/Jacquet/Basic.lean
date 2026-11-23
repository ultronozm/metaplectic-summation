import MetaplecticSummation.Poisson
import MetaplecticSummation.LineIntegral

noncomputable section
namespace MetaplecticPoisson
namespace Datum

open MeasureTheory Filter NumberField IsDedekindDomain
open scoped ContDiff Topology
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [hn : NeZero n] (d : Datum F n)

def jacquet (v : Place F) (Φ : d.schwartz v) (c : (LocalField F v)ˣ) : ℂ :=
  ∫ y, Φ.val.1 c y * d.character.localValue F v (-y / (c : LocalField F v))
    ∂(selfDual F d.character v)

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
