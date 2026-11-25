import MetaplecticSummation.FourierCoefficients.Integrands
import GroundTheory.GlobalFields.TateThesis.AdeleMeasure
import Mathlib.Topology.Covering.Quotient

/-! Unfolding an additive periodization with the probability measure on the adelic quotient. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField IsDedekindDomain MeasureTheory Set GroundTheory.Global
open Classical
open scoped Pointwise ENNReal
variable (F : Type) [Field F] [NumberField F]
local notation "A" => Adeles F
local notation "Γ" => AdeleRing.principalSubgroup (𝓞 F) F
local notation "X" => AdeleQuotient F
local notation "D" => fundamentalSet F
local notation "μ" => adeleMeasure F
local notation "ν" => Exists.choose (ExistsUnique.exists (exists_quotient_measure (F := F)))
local instance periodizationQuotientBorelMeasurable : MeasurableSpace X := borel _
local instance periodizationQuotientBorel : BorelSpace X := ⟨rfl⟩
private def principalEquiv : F ≃ Γ :=
  Equiv.ofBijective (fun a => ⟨algebraMap F A a,a,rfl⟩) ⟨
    fun _ _ h => (algebraMap F A).injective (congrArg Subtype.val h),
    fun ⟨_,a,ha⟩ => ⟨a,Subtype.ext ha⟩⟩
local instance principalCountable : Countable Γ :=
  let := countable_numberField F
  Countable.of_equiv F (principalEquiv F)

private theorem opposite_fundamental : IsAddFundamentalDomain (Γ).op D μ := by
  refine IsAddFundamentalDomain.mk' (measurableSet_fundamentalSet F).nullMeasurableSet fun x => ?_
  obtain ⟨k,hk,hu⟩ := GroundTheory.Global.existsUnique_sub_mem_fundamentalSet F x
  refine ⟨⟨AddOpposite.op (algebraMap F A (-k)), -k, rfl⟩,?_,?_⟩
  · change x + algebraMap F A (-k) ∈ D
    rwa [map_neg,← sub_eq_add_neg]
  · rintro ⟨y,a,ha⟩ h
    change algebraMap F A a = AddOpposite.unop y at ha
    change x + AddOpposite.unop y ∈ D at h
    rw [← ha] at h
    have e : -a = k := hu (-a) (by change x - algebraMap F A (-a) ∈ D; rwa [map_neg,sub_neg_eq_add])
    exact Subtype.ext (AddOpposite.unop_injective (ha.symm.trans (by change algebraMap F A a = algebraMap F A (-k); rw [← e,neg_neg])))

/-- Probability Haar measure on the quotient is the pushforward of the adelic
measure restricted to the fundamental domain of mass one. -/
theorem quotient_measure_fundamental :
    ν = Measure.map (QuotientAddGroup.mk : A → X) ((μ).restrict D) := by
  let : (ν).IsAddHaarMeasure := (exists_quotient_measure (F := F)).exists.choose_spec.1
  let : IsProbabilityMeasure ν := (exists_quotient_measure (F := F)).exists.choose_spec.2
  let π : A → X := QuotientAddGroup.mk
  let η : Measure X := Measure.map π ((μ).restrict D)
  have hπ : Measurable π := QuotientAddGroup.continuous_mk.measurable
  have : IsProbabilityMeasure η := ⟨by
    change Measure.map π _ univ = 1
    rw [Measure.map_apply hπ MeasurableSet.univ,preimage_univ,Measure.restrict_apply_univ,adeleMeasure_fundamentalSet]⟩
  have eval (s : Set X) (hs : MeasurableSet s) : η s = μ (π ⁻¹' s ∩ D) := by
    rw [show η = _ from rfl,Measure.map_apply hπ hs,Measure.restrict_apply (hπ hs)]
  have : η.IsAddLeftInvariant := ⟨by
    intro z
    induction z using Quotient.inductionOn with | _ z => _
    ext s hs
    have hz : Measurable ((π z) + ·) := (continuous_const_add _).measurable
    rw [Measure.map_apply hz hs,eval _ (hz hs),eval _ hs]
    let B := π ⁻¹' s
    have transD := (opposite_fundamental F).vadd_of_comm z
    have he : μ (B ∩ (z +ᵥ D)) = μ (B ∩ D) := transD.measure_set_eq (opposite_fundamental F) (hπ hs) (by
      intro g
      ext x
      change π (x+g.val.unop) ∈ s ↔ π x ∈ s
      rw [show π (x+g.val.unop) = π x from QuotientAddGroup.mk_add_of_mem x g.property])
    apply Eq.trans _ he
    have lift : π ⁻¹' ((π z + ·) ⁻¹' s) = (z + ·) ⁻¹' B := rfl
    rw [lift]
    rw [← measure_preimage_add μ z (B ∩ (z +ᵥ D)),preimage_inter]
    congr 2
    ext x
    change x ∈ D ↔ z + x ∈ z +ᵥ D
    exact ⟨fun hx => ⟨x,hx,rfl⟩,fun ⟨y,hy,he⟩ => (add_left_cancel he : y = x) ▸ hy⟩⟩
  have hη := Measure.isAddInvariant_eq_smul_of_compactSpace η ν
  have mass := congrArg (fun m : Measure X => m univ) hη
  have one : Measure.addHaarScalarFactor η ν = 1 := by
    simpa using mass.symm
  simpa [one] using hη.symm

/-- Periodize an adelic function under the diagonal number field. -/
def rationalPeriodization (f : A → ℂ) : X → ℂ := QuotientAddGroup.automorphize f

theorem rationalPeriodization_mk (f : A → ℂ) (u : A) :
    rationalPeriodization F f (QuotientAddGroup.mk u) = ∑' t : F, f (u + algebraMap F A t) := by
  let e := (principalEquiv F).trans (AddSubgroup.equivOp (Γ))
  exact (e.tsum_eq (fun γ => f (u + γ.val.unop))).symm

/-- Measurability on the compact adelic quotient can be checked upstairs. -/
theorem measurable_of_quotientLift {E : Type*} [MeasurableSpace E] {g : X → E} (hg : Measurable (g ∘ (QuotientAddGroup.mk : A → X))) :
    Measurable g := by
  let π : A → X := QuotientAddGroup.mk
  let L := AdeleRing.principalSubgroup (𝓞 F) F
  let : DiscreteTopology L := AdeleLattice.discreteTopology_principalSubgroup F
  have cover : IsLocalHomeomorph π := (L.isAddQuotientCoveringMap (show IsDiscrete (L : Set A) from SetLike.isDiscrete_iff_discreteTopology.mpr inferInstance)).isLocalHomeomorph
  choose e hx he using cover
  have hc : univ ⊆ ⋃ x, (e x).target := by
    rintro q _
    obtain ⟨x,rfl⟩ := Quotient.exists_rep q
    refine mem_iUnion.mpr ⟨x,?_⟩
    change π x ∈ (e x).target
    rw [he x]
    exact (e x).map_source (hx x)
  obtain ⟨T,hT⟩ := isCompact_univ.elim_finite_subcover _ (fun x => (e x).open_target) hc
  intro S hS
  have small (x : A) : MeasurableSet ((e x).target ∩ g ⁻¹' S) := by
    let U := (e x).target
    have hinv : Continuous (fun q : U => (e x).symm q.val) := (e x).continuousOn_invFun.domRestrict
    have hm : Measurable (fun q : U => g q.val) := by
      convert hg.comp hinv.measurable using 1
      funext q
      change g q.val = g (π ((e x).symm q.val))
      rw [he x,(e x).right_inv q.property]
    have ms := (MeasurableEmbedding.subtype_coe (e x).open_target.measurableSet).measurableSet_image.mpr (hm hS)
    convert ms using 1
    ext q
    exact ⟨fun h => ⟨⟨q,h.1⟩,h.2,rfl⟩,fun ⟨w,hw,heq⟩ => heq ▸ ⟨w.property,hw⟩⟩
  have eqn : g ⁻¹' S = ⋃ x ∈ T, ((e x).target ∩ g ⁻¹' S) := by
    ext q
    simp only [mem_iUnion,mem_inter_iff,mem_preimage]
    constructor
    · intro h
      obtain ⟨x,hx⟩ := mem_iUnion.mp (hT (mem_univ q))
      obtain ⟨hxt,hq⟩ := mem_iUnion.mp hx
      exact ⟨x,hxt,hq,h⟩
    · exact fun ⟨_,_,_,h⟩ => h
  rw [eqn]
  exact T.measurableSet_biUnion (fun x _ => small x)

theorem measurable_rationalPeriodization {f : A → ℂ} (hf : Measurable f) :
    Measurable (rationalPeriodization F f) := by
  let := GroundTheory.Global.countable_numberField F
  apply measurable_of_quotientLift
  change Measurable (fun u : A => rationalPeriodization F f (QuotientAddGroup.mk u))
  simp only [rationalPeriodization_mk]
  exact Measurable.tsum (fun t : F => hf.comp (continuous_add_const _).measurable)

/-- Integration of the rational periodization against probability Haar
measure recovers the integral for the adelic measure of covolume one. -/
theorem integral_periodization {f : A → ℂ} (hf : Integrable f μ)
    (hm : Measurable f) :
    (∫ q : X, rationalPeriodization F f q ∂ν) = ∫ u : A, f u ∂μ := by
  have hp : AEStronglyMeasurable (rationalPeriodization F f) ν :=
    (measurable_rationalPeriodization F hm).aestronglyMeasurable
  rw [quotient_measure_fundamental F] at hp ⊢
  exact (QuotientAddGroup.integral_eq_integral_automorphize (opposite_fundamental F) hf hp).symm

/-- Integrate a nonnegative function by summing its rational translates on a fundamental domain. -/
theorem lintegral_rational_translates {f : A → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ u in D, ∑' t : F, f (u + algebraMap F A t) ∂μ) = ∫⁻ u, f u ∂μ := by
  let := countable_numberField F
  calc
    _ = ∑' t : F, ∫⁻ u in D, f (u + algebraMap F A t) ∂μ :=
      lintegral_tsum fun t => (hf.comp (continuous_add_const _).measurable).aemeasurable
    _ = _ := by
      rw [(isAddFundamentalDomain_fundamentalSet F).lintegral_eq_tsum'' f]
      exact ((principalEquiv F).tsum_eq (fun t => ∫⁻ u in D, f (t.val+u) ∂μ)) ▸
        tsum_congr fun t => by
          change (∫⁻ u in D, f (u + algebraMap F A t) ∂μ) = ∫⁻ u in D, f (algebraMap F A t + u) ∂μ
          simp only [add_comm (algebraMap F A t)]

/-- Periodization contracts the integral of the absolute value. -/
theorem lintegral_enorm_periodization_le {f : A → ℂ} (hf : Measurable f) :
    (∫⁻ q : X, ‖rationalPeriodization F f q‖ₑ ∂ν) ≤ ∫⁻ u : A, ‖f u‖ₑ ∂μ := by
  let := countable_numberField F
  have hπ : Measurable (QuotientAddGroup.mk : A → X) := QuotientAddGroup.continuous_mk.measurable
  rw [quotient_measure_fundamental F, lintegral_map (measurable_rationalPeriodization F hf).enorm hπ]
  calc
    _ ≤ ∫⁻ u in D, ∑' t : F, ‖f (u + algebraMap F A t)‖ₑ ∂μ := by
      apply lintegral_mono
      intro u
      dsimp only
      rw [rationalPeriodization_mk]
      exact enorm_tsum_le_tsum_enorm
    _ = _ := lintegral_rational_translates F hf.enorm

theorem integrable_rationalPeriodization {f : A → ℂ} (hf : Measurable f) (hi : Integrable f μ) :
    Integrable (rationalPeriodization F f) ν :=
  ⟨(measurable_rationalPeriodization F hf).aestronglyMeasurable,
    (lintegral_enorm_periodization_le F hf).trans_lt hi.hasFiniteIntegral⟩

end MetaplecticPoisson.Datum
