import MetaplecticSummation.MarginalDifference
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-! The measure dx/|x| on the units of a completion. -/

noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField MeasureTheory Set
open scoped ENNReal
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

instance (priority := 100) unitsBorel (K : Type*) [NormedField K] [MeasurableSpace K] [BorelSpace K] :
    BorelSpace Kˣ := by
  constructor
  change MeasurableSpace.comap Units.val _ = _
  rw [BorelSpace.measurable_eq (α := K)]
  exact (borel_comap (f := (Units.val : Kˣ → K))).symm.trans
    (congrArg (@borel Kˣ) Units.isEmbedding_val₀.isInducing.eq_induced.symm)

private theorem unitsOpenEmbedding (K : Type*) [NormedField K] :
    Topology.IsOpenEmbedding (Units.val : Kˣ → K) := by
  refine ⟨Units.isEmbedding_val₀, ?_⟩
  have h : range (Units.val : Kˣ → K) = {0}ᶜ := by
    ext x
    exact ⟨fun ⟨u,hu⟩ => hu ▸ u.ne_zero, fun hx => ⟨Units.mk0 x hx,rfl⟩⟩
  rw [h]
  exact isClosed_singleton.isOpen_compl

private theorem continuous_invModulus (v : Place F) :
    Continuous (fun u : (LocalField F v)ˣ => (modulus F v u.val)⁻¹) := by
  apply Continuous.inv₀ _ (modulus_ne_zero v)
  cases v <;> simp only [modulus] <;> fun_prop

/-- Multiplicative Haar measure normalized by the additive self-dual measure. -/
def lineMeasure (v : Place F) : Measure (LocalField F v)ˣ :=
  ((selfDual F d.character v).comap Units.val).withDensity
    (fun u => ENNReal.ofReal (modulus F v u.val)⁻¹)

omit [NeZero n] in
private theorem map_units_comap (v : Place F) :
    ((selfDual F d.character v).comap (Units.val : (LocalField F v)ˣ → _)).map Units.val =
      selfDual F d.character v := by
  let dx := selfDual F d.character v
  rw [(unitsOpenEmbedding _).measurableEmbedding.map_comap,Measure.restrict_eq_self_of_ae_mem]
  letI : NullSingletonClass dx := d.selfDual_nullSingleton v
  filter_upwards [dx.ae_ne 0] with x hx
  exact ⟨Units.mk0 x hx,rfl⟩

omit [NeZero n] in
theorem integral_lineMeasure (v : Place F) (f : Weight v) :
    ∫ u, f u ∂(d.lineMeasure v) = d.lineIntegral v f := by
  let K := LocalField F v
  let μ := selfDual F d.character v
  let g (x : K) := if hx : x ≠ 0 then f (Units.mk0 x hx) / (modulus F v x : ℂ) else 0
  have emb := (unitsOpenEmbedding K).measurableEmbedding
  have he := d.map_units_comap v
  have hn (u : Kˣ) : 0 ≤ modulus F v u.val := by cases v <;> simp [modulus,pow_nonneg]
  rw [lineMeasure,integral_withDensity_eq_integral_toReal_smul
    (f := fun u : Kˣ => ENNReal.ofReal (modulus F v u.val)⁻¹)
    (ENNReal.measurable_ofReal.comp (continuous_invModulus v).measurable) (by simp)]
  change _ = ∫ x, g x ∂μ
  change (μ.comap (Units.val : Kˣ → K)).map Units.val = μ at he
  conv_rhs => rw [← he,emb.integral_map]
  apply integral_congr_ae
  filter_upwards with u
  simp [g,u.ne_zero,ENNReal.toReal_ofReal (inv_nonneg.mpr (hn u)),Complex.real_smul,div_eq_inv_mul]


private instance completionLocallyCompact (v : Place F) : LocallyCompactSpace (LocalField F v) := by
  cases v with
  | inl w => exact inferInstanceAs (LocallyCompactSpace w.Completion)
  | inr p => exact inferInstanceAs (LocallyCompactSpace (p.adicCompletion F))

private instance completionSecondCountable (v : Place F) : SecondCountableTopology (LocalField F v) := by
  cases v with
  | inl w => exact (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  | inr p =>
    letI : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
    letI : TopologicalSpace.SeparableSpace (p.adicCompletion F) :=
      TopologicalSpace.SeparableSpace.of_denseRange _ (IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap (K := F) p)
    exact inferInstanceAs (SecondCountableTopology (p.adicCompletion F))

omit [NeZero n] in
instance lineMeasure_locallyFinite (v : Place F) : IsLocallyFiniteMeasure (d.lineMeasure v) := by
  let dx := selfDual F d.character v
  letI : dx.IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  letI : IsFiniteMeasureOnCompacts (dx.comap (Units.val : (LocalField F v)ˣ → _)) :=
    .comap' _ Units.continuous_val (unitsOpenEmbedding _).measurableEmbedding
  exact IsLocallyFiniteMeasure.withDensity_ofReal (μ := dx.comap Units.val) (continuous_invModulus v)

omit [NeZero n] in
instance lineMeasure_haar (v : Place F) : (d.lineMeasure v).IsHaarMeasure := by
  let K := LocalField F v
  let dx := selfDual F d.character v
  let μ := d.lineMeasure v
  let emb := unitsOpenEmbedding K
  letI : dx.IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  letI : SecondCountableTopology Kˣ := emb.isEmbedding.secondCountableTopology
  refine { map_mul_left_eq_self := ?_, open_pos := ?_ }
  · intro u
    let e := Homeomorph.mulLeft u
    have eemb : MeasurableEmbedding e := e.toMeasurableEquiv.measurableEmbedding
    change μ.map e = μ
    letI : IsFiniteMeasureOnCompacts (μ.map e) := ⟨fun C hC => by
      rw [eemb.map_apply]
      exact (e.isProperMap.isCompact_preimage hC).measure_lt_top⟩
    apply Measure.ext_of_integral_eq_on_compactlySupported
    intro f
    rw [eemb.integral_map]
    have h := d.lineIntegral_mul v u (fun x => (f x : ℂ))
    rw [← d.integral_lineMeasure,← d.integral_lineMeasure] at h
    change (∫ x, f (u*x) ∂d.lineMeasure v) = ∫ x, f x ∂d.lineMeasure v
    exact Complex.ofReal_injective (by simpa only [integral_complex_ofReal] using h)
  · intro U hU hne hz
    have hm : Measurable (fun u : Kˣ => ENNReal.ofReal (modulus F v u.val)⁻¹) :=
      ENNReal.measurable_ofReal.comp (continuous_invModulus v).measurable
    have hpos (u : Kˣ) : 0 < modulus F v u.val := by
      cases v <;> simp [modulus,norm_pos_iff,u.ne_zero,pow_pos]
    have h := (withDensity_apply_eq_zero' hm.aemeasurable).mp hz
    have he : {u : Kˣ | ENNReal.ofReal (modulus F v u.val)⁻¹ ≠ 0} = univ :=
      eq_univ_of_forall fun u => (ENNReal.ofReal_pos.mpr (inv_pos.mpr (hpos u))).ne'
    rw [he,univ_inter,emb.measurableEmbedding.comap_apply] at h
    exact (emb.isOpenMap U hU).measure_ne_zero dx (hne.image _) h

omit [NeZero n] in
theorem lineIntegral_inv (v : Place F) (f : Weight v) :
    d.lineIntegral v (fun u => f u⁻¹) = d.lineIntegral v f := by
  letI : SecondCountableTopology (LocalField F v)ˣ := (unitsOpenEmbedding _).isEmbedding.secondCountableTopology
  rw [← d.integral_lineMeasure,← d.integral_lineMeasure,integral_inv_eq_self]

omit [NeZero n] in
instance lineMeasure_sigmaFinite (v : Place F) : SigmaFinite (d.lineMeasure v) := by
  letI : SecondCountableTopology (LocalField F v)ˣ := (unitsOpenEmbedding _).isEmbedding.secondCountableTopology
  infer_instance

omit [NeZero n] in
/-- Multiplication by the local modulus converts d×u back to du, both in
the integrability criterion and in the integral itself. -/
theorem lineMeasure_modulus (v : Place F) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : LocalField F v → E) :
    let dx := selfDual F d.character v
    let g := fun u : (LocalField F v)ˣ => modulus F v u.val • f u.val
    (Integrable g (d.lineMeasure v) ↔ Integrable f dx) ∧
      (∫ u, g u ∂(d.lineMeasure v)) = ∫ x, f x ∂dx := by
  dsimp only
  let K := LocalField F v
  let dx := selfDual F d.character v
  let ν := dx.comap (Units.val : Kˣ → K)
  let w (u : Kˣ) := ((modulus F v u.val)⁻¹).toNNReal
  have hm : Measurable w := (continuous_real_toNNReal.comp (continuous_invModulus v)).measurable
  have hw (u : Kˣ) : (w u : ℝ) = (modulus F v u.val)⁻¹ := by
    apply Real.coe_toNNReal
    apply inv_nonneg.mpr
    cases v <;> simp [modulus,pow_nonneg]
  have he (u : Kˣ) : w u • (modulus F v u.val • f u.val) = f u.val := by
    rw [NNReal.smul_def,hw,smul_smul,inv_mul_cancel₀ (modulus_ne_zero v u),one_smul]
  have emb := (unitsOpenEmbedding K).measurableEmbedding
  have hmap : ν.map Units.val = dx := d.map_units_comap v
  change (Integrable _ (ν.withDensity fun u => (w u : ℝ≥0∞)) ↔ Integrable f dx) ∧
    (∫ u, _ ∂(ν.withDensity fun u => (w u : ℝ≥0∞))) = ∫ x, f x ∂dx
  rw [integrable_withDensity_iff_integrable_smul hm,integral_withDensity_eq_integral_smul hm]
  simp_rw [he]
  constructor
  · conv_rhs => rw [← hmap,emb.integrable_map_iff]
    rfl
  · conv_rhs => rw [← hmap,emb.integral_map]

omit [NeZero n] in
/-- Substitution t = a/u in the inner multiplicative integral of Appendix A. -/
theorem reciprocal_integral (v : Place F) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : (LocalField F v)ˣ) (f : LocalField F v → E) (hf : Integrable f (selfDual F d.character v)) :
    let g := fun u : (LocalField F v)ˣ => (modulus F v u.val)⁻¹ • f (a.val/u.val)
    Integrable g (d.lineMeasure v) ∧
      (∫ u, g u ∂d.lineMeasure v) = (modulus F v a.val)⁻¹ • ∫ x, f x ∂(selfDual F d.character v) := by
  dsimp only
  letI : SecondCountableTopology (LocalField F v)ˣ := (unitsOpenEmbedding _).isEmbedding.secondCountableTopology
  let μ := d.lineMeasure v
  let h (u : (LocalField F v)ˣ) := modulus F v u.val • f u.val
  let c := (modulus F v a.val)⁻¹
  have ⟨hi,he⟩ := d.lineMeasure_modulus v f
  have eqn (u : (LocalField F v)ˣ) : (modulus F v u.val)⁻¹ • f (a.val/u.val) = c • h (a/u) := by
    have hd : modulus F v (a/u).val = modulus F v a.val / modulus F v u.val := by
      cases v <;> simp [modulus,div_pow]
    dsimp only [h]
    rw [smul_smul,hd,Units.val_div_eq_div_val]
    congr 1
    dsimp [c]
    field_simp [modulus_ne_zero v a,modulus_ne_zero v u]
  simp_rw [eqn]
  refine ⟨((hi.mpr hf).comp_div_left a).smul c, ?_⟩
  rw [integral_smul,integral_div_left_eq_self h μ,he]

end MetaplecticPoisson.Datum
