import MetaplecticSummation.AdditivePoisson
import MetaplecticSummation.ConductorMeasure
import MetaplecticSummation.RationalEvaluation

/-! The conductor and finite self-dual volumes for a rational multiple of the trace character. -/
noncomputable section
namespace MetaplecticPoisson.Character
open GroundTheory.Global NumberField IsDedekindDomain
variable {F : Type} [Field F] [NumberField F]
variable (ψ : Character F) (b : Fˣ) (hb : ∀ x : Adeles F, ψ.toChar x =
  adelicChar F (algebraMap F (Adeles F) b.val * x))

include hb in
/-- Restriction of the rationally scaled trace character to one finite completion. -/
theorem localValue_trace_finite (p : HeightOneSpectrum (𝓞 F)) (x : p.adicCompletion F) :
    ψ.localValue F (.inr p) x = (localAdelicChar F p ((algebraMap F (p.adicCompletion F) b.val) * x) : ℂ) := by
  classical
  unfold Character.localValue
  rw [hb,localAdelicChar_apply]
  congr 2
  apply Prod.ext (mul_zero _)
  exact (RestrictedProduct.mul_single _ p x (algebraMap F (Adeles F) b.val).2).symm

include hb in
/-- Restriction at infinity, with the sign and multiplicity of the trace character. -/
theorem localValue_trace_infinite (w : InfinitePlace F) (x : w.Completion) :
    ψ.localValue F (.inl w) x = (infiniteAdelicChar F w ((algebraMap F w.Completion b.val) * x) : ℂ) := by
  classical
  unfold Character.localValue
  rw [hb,infiniteAdelicChar_apply']
  congr 2
  exact Prod.ext (Pi.single_mul_right (f := (algebraMap F (Adeles F) b.val).1) x).symm (mul_zero _)

include hb in
/-- The annihilator of the local integers is the inverse different scaled by the inverse trace parameter. -/
theorem finite_trace_annihilator (p : HeightOneSpectrum (𝓞 F)) (x : p.adicCompletion F) :
    (∀ y : p.adicCompletion F, ‖y‖ ≤ 1 → ψ.localValue F (.inr p) (x*y) = 1) ↔
      (algebraMap F (p.adicCompletion F) b.val) * x ∈ localInvDifferent p := by
  rw [← forall_localAdelicChar_mul_eq_one_iff]
  constructor
  · intro h y hy
    have H := h y ((Datum.mem_localIntegers_iff p _).mp hy)
    rw [ψ.localValue_trace_finite b hb] at H
    apply Subtype.ext
    simpa only [Circle.coe_one,mul_left_comm,mul_comm,mul_assoc] using H
  · intro h y hy
    rw [ψ.localValue_trace_finite b hb]
    have H := congrArg (fun z : Circle => (z : ℂ)) (h y ((Datum.mem_localIntegers_iff p _).mpr hy))
    simpa only [Circle.coe_one,mul_left_comm,mul_comm,mul_assoc] using H
end MetaplecticPoisson.Character

namespace MetaplecticPoisson.Datum
open GroundTheory.Global NumberField IsDedekindDomain WithZero
open scoped nonZeroDivisors
variable {F : Type} [Field F] [NumberField F] {n : ℕ} (d : Datum F n)
variable (b : Fˣ) (hb : ∀ x : Adeles F, d.character.toChar x =
  adelicChar F (algebraMap F (Adeles F) b.val * x))

include hb in
/-- Self-dual mass of the local integers at a possibly ramified finite place. -/
theorem selfDual_volume_trace (p : HeightOneSpectrum (𝓞 F)) :
    (selfDual F d.character (.inr p)).real {x | ‖x‖ ≤ 1} =
      Real.sqrt ‖algebraMap F (p.adicCompletion F) b.val‖ *
        Real.sqrt ((p.asIdeal.absNorm : ℝ) ^ (-FractionalIdeal.count F p
          ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F))) := by
  let δ := FractionalIdeal.count F p
    ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F)
  let a := Units.map (algebraMap F (p.adicCompletion F)).toMonoidHom b
  let π := uniformizerUnit p
  have h := d.selfDual_volume_of_conductor p (a * π ^ δ) (fun x => by
    rw [d.character.finite_trace_annihilator b hb,mem_localInvDifferent_iff_valued]
    have hh := inv_uniformizerUnit_zpow_mul_mem_iff p (-δ) (a.val * x)
    rw [mem_localIntegers_iff,neg_neg,zpow_neg,Units.val_inv_eq_inv_val,inv_inv] at hh
    change Valued.v (a.val*x) ≤ exp δ ↔ ‖x * (a * π^δ).val‖ ≤ 1
    simpa only [π,Units.val_mul,mul_left_comm,mul_comm,mul_assoc] using hh.symm)
  rw [h,Units.val_mul,norm_mul,Real.sqrt_mul (norm_nonneg _),norm_uniformizerUnit_zpow]
  rfl


open Filter Function
open scoped BigOperators

include hb in
/-- Product of the local masses with the discriminant normalization of adelic Poisson. -/
theorem finite_selfDual_volume_product :
    (∏ᶠ p : HeightOneSpectrum (𝓞 F), (selfDual F d.character (.inr p)).real {x | ‖x‖ ≤ 1}) =
      (∏ᶠ p : HeightOneSpectrum (𝓞 F), Real.sqrt ‖algebraMap F (p.adicCompletion F) b.val‖) *
        (finiteAdeleMeasure F).real (integralFiniteAdeles (𝓞 F) F) := by
  classical
  let D : FractionalIdeal (𝓞 F)⁰ F := differentIdeal ℤ (𝓞 F)
  let I := Units.mk0 D (FractionalIdeal.coeIdeal_ne_zero.mpr (differentIdeal_ne_bot (A := ℤ)))
  let q (p : HeightOneSpectrum (𝓞 F)) := (p.asIdeal.absNorm : ℝ) ^ FractionalIdeal.count F p D
  have hq : ∀ᶠ p in cofinite, q p = 1 := (FractionalIdeal.finite_factors D).mono fun p hp => by simp [q,hp]
  have hb' : ∀ᶠ p : HeightOneSpectrum (𝓞 F) in cofinite, Real.sqrt ‖algebraMap F (p.adicCompletion F) b.val‖ = 1 :=
    (eventually_diagonal_norm_one b.ne_zero).mono fun p hp => by
      change ‖algebraMap F (p.adicCompletion F) b.val‖ = 1 at hp
      rw [hp,Real.sqrt_one]
  have hv (p : HeightOneSpectrum (𝓞 F)) := d.selfDual_volume_trace b hb p
  simp only [zpow_neg,Real.sqrt_inv] at hv
  change ∀ p, _ = _ * (Real.sqrt (q p))⁻¹ at hv
  simp_rw [hv]
  rw [finprod_mul_distrib (eventually_cofinite.mp hb') (eventually_cofinite.mp (hq.mono (fun p h => by simp [h]))),
    finprod_inv_distrib]
  congr 1
  have hs := eventually_cofinite.mp hq
  have he : (∏ᶠ p, Real.sqrt (q p)) = Real.sqrt (∏ᶠ p, q p) := by
    rw [finprod_eq_prod_of_mulSupport_subset (s := hs.toFinset) _ (by
      intro p hp
      by_contra hn
      exact hp (by simp [show q p = 1 from not_not.mp (fun h => hn (hs.mem_toFinset.mpr h))])),
      finprod_eq_prod _ hs,Real.sqrt_prod _ (fun p _ => zpow_nonneg (Nat.cast_nonneg _) _)]
    rfl
  rw [he,← show ((FractionalIdeal.absNorm D : ℚ) : ℝ) = ∏ᶠ p, q p from absNorm_eq_finprod I]
  rw [MeasureTheory.Measure.real,finiteAdeleMeasure_integralFiniteAdeles,ENNReal.coe_toReal,NNReal.coe_inv]
  simp [D,FractionalIdeal.coeIdeal_absNorm,absNorm_differentIdeal F (𝓞 F),Real.coe_sqrt,
    coe_nnnorm,Int.norm_eq_abs,Nat.cast_natAbs]

end MetaplecticPoisson.Datum
