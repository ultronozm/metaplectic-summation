import MetaplecticSummation.FourierCoefficients.SliceBounds

/-! Integration over the rational upper-unipotent orbits in Appendix B. -/

noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField MeasureTheory Filter
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} (d : Datum F n)
local notation "A" => Adeles F
local notation "X" => AdeleQuotient F
local notation "ι" => algebraMap F A
local notation "haar" => Exists.choose (ExistsUnique.exists (exists_quotient_measure (F := F)))
local instance frequencyMeasurableSpace : MeasurableSpace X := borel _
local instance frequencyBorelSpace : BorelSpace X := ⟨rfl⟩

/-- The factor ψ(−au) in the Fourier coefficient descends to the adelic quotient. -/
def quotientFrequency (a : F) : X → ℂ :=
  Quotient.lift (fun u : A => (d.character.toChar (-(ι a * u)) : ℂ)) (by
    intro u w h
    obtain ⟨t,ht⟩ := QuotientAddGroup.leftRel_apply.mp h
    have he : w = u + ι t := by rw [ht]; abel
    rw [he,mul_add,neg_add,← map_mul,← map_neg,AddChar.map_add_eq_mul,d.character.trivial_diagonal,mul_one])

@[simp] theorem quotientFrequency_mk (a : F) (u : A) :
    d.quotientFrequency a (QuotientAddGroup.mk u) = (d.character.toChar (-(ι a * u)) : ℂ) := rfl

theorem continuous_quotientFrequency (a : F) : Continuous (d.quotientFrequency a) := by
  unfold quotientFrequency
  apply Continuous.quotient_lift
  exact continuous_subtype_val.comp (d.character.continuous_toChar.comp (continuous_const.mul continuous_id).neg)

private theorem quotientFrequency_add (a : F) (q r : X) :
    d.quotientFrequency a (q+r) = d.quotientFrequency a q * d.quotientFrequency a r := by
  induction q using Quotient.inductionOn with | _ u => _
  induction r using Quotient.inductionOn with | _ v => _
  change (d.character.toChar (-(ι a * (u+v))) : ℂ) = _
  rw [mul_add,neg_add,AddChar.map_add_eq_mul]
  rfl

theorem integral_quotientFrequency (a : F) :
    (∫ q : X, d.quotientFrequency a q ∂haar) = if a = 0 then 1 else 0 := by
  let : (haar).IsAddHaarMeasure := (exists_quotient_measure (F := F)).exists.choose_spec.1
  let : IsProbabilityMeasure haar := (exists_quotient_measure (F := F)).exists.choose_spec.2
  by_cases h : a = 0
  · subst a
    have one (q : X) : d.quotientFrequency 0 q = 1 := by
      induction q using Quotient.inductionOn with | _ x => simp
    simp [one]
  rw [ite_eq_right h]
  obtain ⟨u,hu⟩ := d.character.nontrivial
  let t : A := -(ι a⁻¹ * u)
  have e : -(ι a * t) = u := by simp [t,← mul_assoc,← map_mul,h]
  have ht : d.quotientFrequency a (QuotientAddGroup.mk t) ≠ 1 := by
    rw [d.quotientFrequency_mk,e]
    exact fun he => hu (Subtype.ext he)
  have eqn := integral_add_right_eq_self (μ := haar) (d.quotientFrequency a) (QuotientAddGroup.mk t)
  simp_rw [d.quotientFrequency_add] at eqn
  rw [integral_mul_const] at eqn
  exact by_contra fun h => ht ((mul_eq_left₀ h).mp eqn)

theorem periodization_frequency (a : F) (f : A → ℂ) (q : X) :
    rationalPeriodization F (fun u => f u * d.quotientFrequency a (QuotientAddGroup.mk u)) q =
      rationalPeriodization F f q * d.quotientFrequency a q := by
  induction q using Quotient.inductionOn with | _ u => _
  simp only [rationalPeriodization_mk,← tsum_mul_right]
  apply tsum_congr
  intro t
  have e : (QuotientAddGroup.mk (u + ι t) : X) = QuotientAddGroup.mk u :=
    QuotientAddGroup.mk_add_of_mem u ⟨t,rfl⟩
  rw [e]

/-- Absolute convergence and unfolding at every rational frequency. -/
theorem coefficient_eq_slope_integrals [NeZero n] (Φ : ∀ v, d.schwartz v)
    (hΦ : ∀ᶠ v in cofinite, Φ v = d.basic v) (a : F) :
    Integrable (d.quotientIntegrand Φ a) haar ∧
      d.coefficient Φ a = (if a = 0 then ∑' y : Fˣ, ∏ᶠ v, d.axis v (Φ v) (atPlace v y) else 0) +
        ∑' x : Fˣ, ∫ u : A, d.adelicSlopeSlice Φ x u * (d.character.toChar (-(ι a * u)) : ℂ)
          ∂GroundTheory.Global.adeleMeasure F := by
  let := GroundTheory.Global.countable_numberField F
  let : Countable Fˣ := (Units.val_injective (α := F)).countable
  let : IsProbabilityMeasure haar := (exists_quotient_measure (F := F)).exists.choose_spec.2
  have hL := d.summable_slope_integrals Φ hΦ
  let ψ := d.quotientFrequency a
  let π : A → X := QuotientAddGroup.mk
  let W (x : Fˣ) (u : A) := d.adelicSlopeSlice Φ x u * ψ (π u)
  let P (x : Fˣ) := rationalPeriodization F (W x)
  let b := ∑' y : Fˣ, ∏ᶠ v, d.axis v (Φ v) (atPlace v y)
  have meas (x) : Measurable (W x) := (d.measurable_adelicSlopeSlice Φ hΦ x).mul
    ((d.continuous_quotientFrequency a).comp QuotientAddGroup.continuous_mk).measurable
  have enorm (x : Fˣ) (u : A) : ‖W x u‖ₑ = ‖d.adelicSlopeSlice Φ x u‖ₑ := by
    change ‖d.adelicSlopeSlice Φ x u * (d.character.toChar (-(ι a * u)) : ℂ)‖ₑ = _
    rw [enorm_mul,Circle.enorm_coe,mul_one]
  have hW (x) : Integrable (W x) (GroundTheory.Global.adeleMeasure F) := by
    refine ⟨(meas x).aestronglyMeasurable,?_⟩
    change (∫⁻ u, ‖W x u‖ₑ ∂GroundTheory.Global.adeleMeasure F) < ⊤
    simp only [enorm]
    exact (ENNReal.le_tsum x).trans_lt (lt_top_iff_ne_top.mpr hL)
  have measP (x) : AEStronglyMeasurable (P x) haar :=
    (measurable_rationalPeriodization F (meas x)).aestronglyMeasurable
  have sumP : (∑' x, ∫⁻ q, ‖P x q‖ₑ ∂haar) ≠ ⊤ := by
    apply ne_top_of_le_ne_top hL
    apply ENNReal.tsum_le_tsum
    intro x
    simpa only [enorm] using lintegral_enorm_periodization_le F (meas x)
  have intP : Integrable (fun q => ∑' x, P x q) haar := by
    refine ⟨AEStronglyMeasurable.tsum measP,?_⟩
    change (∫⁻ q, ‖∑' x, P x q‖ₑ ∂haar) < ⊤
    apply lt_of_le_of_lt (lintegral_mono (fun _ => enorm_tsum_le_tsum_enorm))
    rw [lintegral_tsum (fun x => (measP x).enorm)]
    exact lt_top_iff_ne_top.mpr sumP
  have intψ : Integrable (fun q => b * ψ q) haar :=
    ((d.continuous_quotientFrequency a).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).const_mul b
  have orbit (q : X) : d.quotientIntegrand Φ a q = b * ψ q + ∑' x, P x q := by
    induction q using Quotient.inductionOn with | _ u => _
    rw [d.quotientIntegrand_mk,d.translatedTheta_orbit_sum Φ hΦ,add_mul]
    apply congrArg (b * ψ (π u) + ·)
    rw [← tsum_mul_right]
    apply tsum_congr
    intro x
    exact ((d.periodization_frequency a (d.adelicSlopeSlice Φ x) (π u)).trans
      (congrArg (· * ψ (π u)) (rationalPeriodization_mk F _ u))).symm
  constructor
  · exact (intψ.add intP).congr (ae_of_all _ fun q => (orbit q).symm)
  · unfold coefficient
    simp_rw [orbit]
    rw [integral_add intψ intP,integral_const_mul,integral_tsum measP sumP]
    change b * (∫ q, d.quotientFrequency a q ∂haar) + _ = (if a = 0 then b else 0) + _
    rw [d.integral_quotientFrequency]
    congr 1
    · split <;> simp_all only [mul_one,mul_zero]
    · exact tsum_congr fun x => integral_periodization F (hW x) (meas x)

end MetaplecticPoisson.Datum
