import MetaplecticSummation.Reduction.SiegelCover
import MetaplecticSummation.FourierCoefficients.Periodization

/-! The weighted Siegel integral inequality for the rational quotient of adelic SL₂. -/

noncomputable section
namespace MetaplecticPoisson
open Set NumberField IsDedekindDomain MeasureTheory
open GroundTheory.Global (adeleMeasure fundamentalSet adeleMeasure_smul adeleMeasure_fundamentalSet
  isCompact_closure_fundamentalSetInfinite isCompact_integralFiniteAdeles integralFiniteAdeles fundamentalSetInfinite)
open scoped MatrixGroups Pointwise ENNReal
open Classical
variable (F : Type) [Field F] [NumberField F]
local notation "G" => AdelicSL F
local notation "A" => Adeles F
local notation "Γ" => rationalSL F
local notation "P" => HeightOneSpectrum (𝓞 F)
local notation "X" => SLArithmeticQuotient F
local notation "π" => (Quotient.mk _ : G → X)
local notation "D" => fundamentalSet F
local notation "du" => adeleMeasure F
local notation "I" => integralFiniteAdeles (𝓞 F) F
local notation "n" => adelicUpper F

local instance siegelFundamentalProbability : IsProbabilityMeasure ((du).restrict D) := ⟨by
  rw [Measure.restrict_apply_univ, adeleMeasure_fundamentalSet]⟩

/-- Integrate over the unipotent parameter and count the rational translates in Ω. -/
private def multiplicity (Ω : Set G) (h x : G) : ℝ≥0∞ :=
  ∑' γ : Γ, ∫⁻ u in D, Ω.indicator (fun _ => (1 : ℝ≥0∞)) ((n u * h)⁻¹ * (γ.val * x)) ∂du

private theorem measurable_window {Ω : Set G} (hΩ : MeasurableSet Ω) (h : G) :
    Measurable (fun p : G × A => Ω.indicator (fun _ => (1 : ℝ≥0∞)) ((n p.2 * h)⁻¹ * p.1)) :=
  (measurable_const.indicator hΩ).comp
    ((((continuous_adelicUpper F).comp continuous_snd).mul continuous_const).inv.mul continuous_fst).measurable

private theorem measurable_multiplicity {Ω : Set G} (hΩ : MeasurableSet Ω) (h : G) :
    Measurable (multiplicity F Ω h) := by
  apply Measurable.tsum
  intro γ
  exact ((measurable_window F hΩ h).lintegral_prod_right' (ν := (du).restrict D)).comp (continuous_const_mul γ.val).measurable

private theorem quotient_translate (γ : Γ) (x : G) : π (γ.val * x) = π x := by
  apply Quotient.sound
  apply QuotientGroup.rightRel_apply.mpr
  simp [mul_inv_rev,← mul_assoc,γ.property]

private theorem lintegral_multiplicity (μ : Measure G) [SFinite μ] [μ.IsMulLeftInvariant]
    {Ω : Set G} (hΩ : MeasurableSet Ω) (h : G) {f : X → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x in rationalSLDomain F, f (π x) * multiplicity F Ω h x ∂μ) =
      ∫⁻ u in D, ∫⁻ ω in Ω, f (π (n u*h*ω)) ∂μ ∂du := by
  let W := fun x : G => ∫⁻ u in D, Ω.indicator (fun _ => (1 : ℝ≥0∞)) ((n u*h)⁻¹*x) ∂du
  have hW : Measurable W := (measurable_window F hΩ h).lintegral_prod_right'
  have hj : Measurable (fun p : G × A => f (π p.1) *
      Ω.indicator (fun _ => (1 : ℝ≥0∞)) ((n p.2*h)⁻¹*p.1)) :=
    (hf.comp (measurable_quotient_mk''.comp measurable_fst)).mul (measurable_window F hΩ h)
  calc
    _ = ∫⁻ x in rationalSLDomain F, ∑' γ : Γ, f (π (γ.val*x)) * W (γ.val*x) ∂μ := by
      apply lintegral_congr
      intro x
      simp only [quotient_translate,ENNReal.tsum_mul_left,multiplicity,W]
    _ = ∫⁻ x, f (π x) * W x ∂μ := by
      rw [lintegral_tsum (f := fun (γ : Γ) (x : G) => f (π (γ.val*x)) * W (γ.val*x)) fun γ => (((hf.comp (measurable_quotient_mk'' : Measurable π)).mul hW).comp
        (continuous_const_mul γ.val).measurable).aemeasurable]
      exact ((isFundamentalDomain_rationalSL F μ).lintegral_eq_tsum'' (fun x => f (π x) * W x)).symm
    _ = ∫⁻ x, ∫⁻ u in D, f (π x) * Ω.indicator (fun _ => (1 : ℝ≥0∞)) ((n u*h)⁻¹*x) ∂du ∂μ := by
      apply lintegral_congr
      intro x
      exact (lintegral_const_mul _ ((measurable_window F hΩ h).comp (measurable_const.prodMk measurable_id))).symm
    _ = _ := by
      rw [lintegral_lintegral_swap hj.aemeasurable]
      apply lintegral_congr
      intro u
      let a := n u*h
      let L := fun x : G => f (π x) * Ω.indicator (fun _ => (1 : ℝ≥0∞)) (a⁻¹*x)
      have translate := (measurePreserving_mul_left μ a).lintegral_comp_emb
        (Homeomorph.mulLeft a).measurableEmbedding L
      change (∫⁻ x, L x ∂μ) = _
      rw [← translate,← lintegral_indicator hΩ]
      apply lintegral_congr
      intro x
      change f (π (a*x)) * Ω.indicator _ (a⁻¹*(a*x)) = Ω.indicator (fun y => f (π (a*y))) x
      rw [inv_mul_cancel_left]
      by_cases hx : x ∈ Ω <;> simp [hx]

private def rationalUpper (t : F) : Γ :=
  (rationalSLMap F).rangeRestrict (upperUnipotentParam (Multiplicative.ofAdd t))

private theorem rationalUpper_injective : Function.Injective (rationalUpper F) := by
  intro t s h
  have e := rationalSLMap_injective F (congrArg Subtype.val h)
  have entry (v : F) : (upperUnipotentParam (Multiplicative.ofAdd v)).val 0 1 = v := by
    rw [show (upperUnipotentParam (Multiplicative.ofAdd v)).val = _ from upperTransvection_matrix v]; rfl
  exact (entry t).symm.trans ((congrArg (fun x : SL(2,F) => x.val 0 1) e).trans (entry s))

private theorem rationalUpper_val (t : F) :
    (rationalUpper F t).val = n (algebraMap F A t) := (adelicUpper_diagonal F t).symm

private theorem window_translate (u : A) (h x : G) (γ : Γ) (t : F) :
    (n (u + algebraMap F A t) * h)⁻¹ * (γ.val*x) =
      (n u*h)⁻¹ * ((rationalUpper F (-t) * γ).val*x) := by
  rw [add_comm,adelicUpper_add,Subgroup.coe_mul,rationalUpper_val,map_neg]
  have hn (v : A) : n (-v) = (n v)⁻¹ := map_inv (upperUnipotentParam (F := A)) (Multiplicative.ofAdd v)
  rw [hn]
  group

private theorem lintegral_le_of_rational_translates {E : Type*} (j : F → E) (hj : Function.Injective j)
    (W : A → ℝ≥0∞) (hW : Measurable W) (V : E → A → ℝ≥0∞)
    (he : ∀ t u, W (u + algebraMap F A t) = V (j t) u) :
    (∫⁻ u, W u ∂du) ≤ ∑' e, ∫⁻ u in D, V e u ∂du := by
  let := GroundTheory.Global.countable_numberField F
  calc
    _ = ∫⁻ u in D, ∑' t : F, W (u + algebraMap F A t) ∂du := (Datum.lintegral_rational_translates F hW).symm
    _ = ∑' t : F, ∫⁻ u in D, W (u + algebraMap F A t) ∂du :=
      lintegral_tsum fun t => (hW.comp (continuous_add_const (algebraMap F A t)).measurable).aemeasurable
    _ = ∑' t : F, ∫⁻ u in D, V (j t) u ∂du := tsum_congr fun t => lintegral_congr (he t)
    _ ≤ _ := ENNReal.tsum_comp_le_tsum_of_injective hj (fun e => ∫⁻ u in D, V e u ∂du)

private theorem unipotent_integral_le {Ω : Set G} (hΩ : MeasurableSet Ω) (h x : G) (γ : Γ) :
    (∫⁻ u, Ω.indicator (fun _ => (1 : ℝ≥0∞)) ((n u*h)⁻¹*(γ.val*x)) ∂du) ≤ multiplicity F Ω h x := by
  let j : F → Γ := fun t => rationalUpper F (-t) * γ
  have inj : Function.Injective j := by
    intro a b hab
    apply neg_injective
    apply rationalUpper_injective F
    exact mul_right_cancel (show rationalUpper F (-a)*γ = rationalUpper F (-b)*γ from hab)
  let V := fun (δ : Γ) (u : A) => Ω.indicator (fun _ => (1 : ℝ≥0∞)) ((n u*h)⁻¹*(δ.val*x))
  have hc : Continuous (fun u : A => (n u*h)⁻¹*(γ.val*x)) :=
    (((continuous_adelicUpper F).mul (continuous_const (y := h))).inv).mul (continuous_const (y := γ.val*x))
  have hm : Measurable (V γ) := (measurable_const.indicator hΩ).comp hc.measurable
  exact lintegral_le_of_rational_translates F j inj (V γ) hm V fun t u =>
    congrArg (Ω.indicator (fun _ => (1 : ℝ≥0∞))) (window_translate F u h x γ t)

/-- Along a covered orbit the thickened compact set contains a translate of the
scaled additive fundamental set, of measure q to the power 2k. -/
private theorem layer_mass (w : P) (k : ℕ) (u₀ : A) (ω : G) (Ω : Set G)
    (hthick : ∀ t ∈ D, n t * ω ∈ Ω) :
    let h := ideleDiagonal F (cuspIdele F w)^k
    ENNReal.ofReal ((w.asIdeal.absNorm : ℝ)^(2*k)) ≤
      ∫⁻ u, Ω.indicator (fun _ => (1 : ℝ≥0∞)) ((n u*h)⁻¹*(n u₀*h*ω)) ∂du := by
  let z := IdeleGroup.equivAdeleRingUnits (cuspIdele F w)
  let c := z^k
  let h := diagonalSL c
  change _ ≤ ∫⁻ u, Ω.indicator (fun _ => (1 : ℝ≥0∞)) ((n u*(diagonalSL z)^k)⁻¹ * (n u₀*(diagonalSL z)^k*ω)) ∂du
  rw [← map_pow]
  let S := (fun u : A => u₀-u) ⁻¹' ((c^2) • D)
  have hD := GroundTheory.Global.measurableSet_fundamentalSet F
  have hs := hD.const_smul (c^2)
  have hs' : MeasurableSet S := hs.preimage (continuous_const.sub continuous_id).measurable
  have mass : du S = ENNReal.ofReal ((w.asIdeal.absNorm : ℝ)^(2*k)) := by
    rw [show du S = du ((c^2) • D) from ((du).measurePreserving_sub_left u₀).measure_preimage hs.nullMeasurableSet,
      adeleMeasure_smul,adeleMeasure_fundamentalSet,mul_one,map_pow,map_pow]
    change ENNReal.ofReal (((GroundTheory.Global.IdeleGroup.ideleModule F z : ℝ)^k)^2) = _
    rw [← pow_mul,Nat.mul_comm k 2,cuspIdele_haarModule]
  rw [← mass,← lintegral_indicator_one hs']
  apply lintegral_mono
  intro u
  by_cases hu : u ∈ S
  · rw [Set.indicator_of_mem hu]
    obtain ⟨t,ht,he⟩ := hu
    change c.val^2*t = u₀-u at he
    have he' : n u₀*h*ω = (n u*h)*(n t*ω) := by
      change _ = (n u*diagonalSL c)*(n t*ω)
      rw [← mul_assoc (n u*diagonalSL c),mul_assoc (n u),diagonalSL_mul_adelicUpper,
        ← mul_assoc (n u),← adelicUpper_add,he,add_sub_cancel]
    change 1 ≤ Ω.indicator _ ((n u*h)⁻¹*(n u₀*h*ω))
    rw [he',inv_mul_cancel_left,Set.indicator_of_mem (hthick t ht)]
  · simp [Set.indicator_of_notMem hu]

/-- For a fixed finite place, a compact enlargement of the Siegel set bounds the
quotient integral. The additive integral is written on the covolume-one fundamental set. -/
private theorem siegel_bound_fundamentalSet (w : P) :
    ∃ Ω : Set G, IsCompact Ω ∧
      (∀ g : G, ∃ γ : SL(2,F), ∃ u : A, ∃ k : ℕ, ∃ ω ∈ Ω,
        g = rationalSLMap F γ * n u * ideleDiagonal F (cuspIdele F w)^k * ω) ∧
      ∀ (μ : Measure G) [SFinite μ] [μ.IsMulLeftInvariant],
      ∀ f : X → ℝ≥0∞, Measurable f →
      (∫⁻ x, f x ∂slQuotientMeasure F μ) ≤
        ∑' k : ℕ, ENNReal.ofReal ((w.asIdeal.absNorm : ℝ)^(2*k))⁻¹ *
          ∫⁻ u in D, ∫⁻ ω in Ω, f (π (n u * ideleDiagonal F (cuspIdele F w)^k * ω)) ∂μ ∂du := by
  obtain ⟨K,hK,rep⟩ := exists_natural_cusp_cover F w
  let B : Set A := closure (fundamentalSetInfinite F) ×ˢ (I : Set _)
  have hB : IsCompact B := (isCompact_closure_fundamentalSetInfinite F).prod (isCompact_integralFiniteAdeles F)
  let Ω := K ∪ (n '' B) * K
  have hΩ : IsCompact Ω := hK.union ((hB.image (continuous_adelicUpper F)).mul hK)
  refine ⟨Ω,hΩ,fun g => ?_,?_⟩
  · obtain ⟨γ,u,k,ω,hω,he⟩ := rep g
    exact ⟨γ,u,k,ω,Or.inl hω,he⟩
  intro μ _ _ f hf
  let h (k : ℕ) := ideleDiagonal F (cuspIdele F w)^k
  let Q (k : ℕ) := (w.asIdeal.absNorm : ℝ)^(2*k)
  have pos (k) : 0 < Q k := pow_pos (by exact_mod_cast (lt_trans Nat.zero_lt_one (NumberField.HeightOneSpectrum.one_lt_absNorm w))) _
  have point (x : G) : f (π x) ≤ ∑' k : ℕ, ENNReal.ofReal (Q k)⁻¹ * (f (π x) * multiplicity F Ω (h k) x) := by
    obtain ⟨γ,u,k,ω,hω,he⟩ := rep x
    let δ := (rationalSLMap F).rangeRestrict γ⁻¹
    have he' : δ.val*x = n u*h k*ω := by
      rw [he]
      change rationalSLMap F γ⁻¹ * _ = _
      rw [map_inv]
      simp [mul_assoc,h]
    have hmass := layer_mass F w k u ω Ω fun t ht =>
      Or.inr (Set.mul_mem_mul (show n t ∈ n '' B from ⟨t,⟨subset_closure ht.1,ht.2⟩,rfl⟩) hω)
    have hcount := unipotent_integral_le F hΩ.measurableSet (h k) x δ
    rw [he'] at hcount
    have bound : ENNReal.ofReal (Q k) ≤ multiplicity F Ω (h k) x := hmass.trans hcount
    apply le_trans _ (ENNReal.le_tsum k)
    calc
      _ = ENNReal.ofReal (Q k)⁻¹ * (f (π x) * ENNReal.ofReal (Q k)) := by
        rw [mul_left_comm,← ENNReal.ofReal_mul (inv_pos.mpr (pos k)).le,inv_mul_cancel₀ (pos k).ne',ENNReal.ofReal_one,mul_one]
      _ ≤ _ := by gcongr
  rw [slQuotientMeasure,lintegral_map hf measurable_quotient_mk'']
  apply (lintegral_mono point).trans_eq
  have hm (k) := (hf.comp measurable_quotient_mk'').mul (measurable_multiplicity F hΩ.measurableSet (h k))
  rw [lintegral_tsum (f := fun k (x : G) => ENNReal.ofReal (Q k)⁻¹ * (f (π x) * multiplicity F Ω (h k) x)) fun k => (measurable_const.mul (hm k)).aemeasurable]
  apply tsum_congr
  intro k
  rw [lintegral_const_mul (f := fun x : G => f (π x) * multiplicity F Ω (h k) x) _ (hm k),lintegral_multiplicity F μ hΩ.measurableSet (h k) hf]

local notation "T" => Datum.AdeleQuotient F
local notation "η" => Exists.choose (ExistsUnique.exists (Datum.exists_quotient_measure (F := F)))
local instance siegelQuotientMeasurableSpace : MeasurableSpace T := borel _
local instance siegelQuotientBorelSpace : BorelSpace T := ⟨rfl⟩

/-- The image of an upper unipotent translate on the rational SL₂ quotient. -/
def unipotentOrbitPoint (g : G) : T → X :=
  Quotient.lift (fun u : A => π (n u*g)) fun u v huv => by
    obtain ⟨t,ht⟩ := QuotientAddGroup.leftRel_apply.mp huv
    have hv : v = algebraMap F A t + u := by rw [ht]; abel
    rw [hv,adelicUpper_add,mul_assoc,← rationalUpper_val]
    exact (quotient_translate F _ _).symm

/-- The adelic Siegel covering and quotient Haar integral bound of Proposition B.6.
The measure on the compact set is the restriction of the same Haar measure used
to define the rational quotient measure. The integral on 𝔸/F uses probability Haar. -/
theorem exists_siegel_integral_bound (w : P) :
    ∃ Ω : Set G, IsCompact Ω ∧
      (∀ g : G, ∃ γ : SL(2,F), ∃ u : A, ∃ k : ℕ, ∃ ω ∈ Ω,
        g = rationalSLMap F γ * n u * ideleDiagonal F (cuspIdele F w)^k * ω) ∧
      ∀ (μ : Measure G) [μ.IsHaarMeasure], μ Ω < ⊤ ∧ ∀ f : X → ℝ≥0∞, Measurable f →
        (∫⁻ x, f x ∂slQuotientMeasure F μ) ≤
          ∑' k : ℕ, ENNReal.ofReal ((w.asIdeal.absNorm : ℝ)^(2*k))⁻¹ *
            ∫⁻ t : T, ∫⁻ ω in Ω, f (unipotentOrbitPoint F (ideleDiagonal F (cuspIdele F w)^k * ω) t) ∂μ ∂η := by
  obtain ⟨Ω,hΩ,cover,bound⟩ := siegel_bound_fundamentalSet F w
  refine ⟨Ω,hΩ,cover,?_⟩
  intro μ _
  refine ⟨hΩ.measure_lt_top,fun f hf => (bound μ f hf).trans_eq ?_⟩
  apply tsum_congr
  intro k
  apply congrArg (_ * ·)
  let h := ideleDiagonal F (cuspIdele F w)^k
  let L := fun t : T => ∫⁻ ω in Ω, f (unipotentOrbitPoint F (h*ω) t) ∂μ
  have hL : Measurable L := by
    apply Datum.measurable_of_quotientLift F
    change Measurable (fun u : A => ∫⁻ ω in Ω, f (π (n u*(h*ω))) ∂μ)
    have hm : Measurable (fun p : A × G => n p.1*(h*p.2)) :=
      (((continuous_adelicUpper F).comp continuous_fst).mul (continuous_const.mul continuous_snd)).measurable
    exact (hf.comp (measurable_quotient_mk''.comp hm)).lintegral_prod_right'
  change _ = ∫⁻ t, L t ∂η
  rw [Datum.quotient_measure_fundamental F,lintegral_map hL QuotientAddGroup.continuous_mk.measurable]
  simp only [L,unipotentOrbitPoint,Quotient.lift_mk,← mul_assoc,h]

/-- The arithmetic quotient has finite volume for every Haar normalization. -/
theorem finiteVolume_slQuotient (w : P) (μ : Measure G) [μ.IsHaarMeasure] :
    IsFiniteMeasure (slQuotientMeasure F μ) := by
  obtain ⟨Ω,_,_,bound⟩ := exists_siegel_integral_bound F w
  obtain ⟨hΩ,estimate⟩ := bound μ
  let : IsProbabilityMeasure η := (Datum.exists_quotient_measure (F := F)).exists.choose_spec.2
  have h := estimate (fun _ => 1) measurable_const
  simp only [lintegral_const,Measure.restrict_apply_univ,one_mul,measure_univ,mul_one] at h
  let q : ℝ := w.asIdeal.absNorm
  let r := ENNReal.ofReal ((q^2)⁻¹)
  have hq : 1 < q := by dsimp [q]; exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm w
  have hlt : r < 1 := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
    exact (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).mpr (inv_lt_one_of_one_lt₀ (one_lt_pow₀ hq (by decide : 2 ≠ 0)))
  have weight (k : ℕ) : ENNReal.ofReal ((w.asIdeal.absNorm : ℝ)^(2*k))⁻¹ = r^k := by
    dsimp only [r,q]
    rw [pow_mul,← inv_pow,ENNReal.ofReal_pow (by positivity)]
  refine ⟨h.trans_lt ?_⟩
  simp only [weight,ENNReal.tsum_mul_right]
  exact ENNReal.mul_lt_top (tsum_geometric_lt_top.mpr hlt) hΩ

end MetaplecticPoisson
