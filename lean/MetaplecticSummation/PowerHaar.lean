import MetaplecticSummation.PowerArea
import Mathlib.Topology.LocallyConstant.Algebra
import MetaplecticSummation.MultiplicativeMeasure
import MetaplecticSummation.PowerSubgroup
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-! Multiplicative Haar measure under the power map (§2). -/
noncomputable section
open MeasureTheory Filter Metric Set Function
open scoped Topology ENNReal NNReal
open Classical
namespace MetaplecticPoisson

theorem unitPower_proper {K : Type*} [NormedField K] [ProperSpace K]
    (n : ℕ) (hn : n ≠ 0) :
    Tendsto (powMonoidHom n : Kˣ →* Kˣ).rangeRestrict (cocompact _) (cocompact _) := by
  let H := (powMonoidHom n : Kˣ →* Kˣ).range
  let f := (powMonoidHom n : Kˣ →* Kˣ).rangeRestrict
  have hf : Continuous f := (continuous_id.pow n : Continuous (fun x : Kˣ => x^n)).subtype_mk _
  rw [hasBasis_cocompact.tendsto_right_iff]
  intro C hC
  change f ⁻¹' Cᶜ ∈ cocompact _
  rw [preimage_compl]
  apply IsCompact.compl_mem_cocompact
  let S : Set K := (fun x : H => x.val.val) '' C
  have hS : IsCompact S := hC.image (Units.continuous_val.comp continuous_subtype_val)
  have hnz : (0:K) ∉ S := by
    rintro ⟨u,_,hu⟩
    exact u.val.ne_zero hu
  obtain ⟨R,hR⟩ := hS.isBounded.subset_closedBall (0 : K)
  let T := (fun x : K => x^n) ⁻¹' S
  have hT : IsCompact T := (isCompact_closedBall (0 : K) (max 1 R)).of_isClosed_subset
    (hS.isClosed.preimage (continuous_id.pow n)) (by
      intro x hx
      have hxR := mem_closedBall_zero_iff.mp (hR hx)
      rw [norm_pow] at hxR
      apply mem_closedBall_zero_iff.mpr
      by_cases h : ‖x‖ ≤ 1
      · exact h.trans (le_max_left ..)
      · exact ((le_self_pow₀ (le_of_not_ge h) hn).trans hxR).trans (le_max_right ..))
  have hU : IsCompact ((Units.val : Kˣ → K) ⁻¹' T) :=
    Units.isEmbedding_val₀.isInducing.isCompact_preimage' hT (by
      intro x hx
      refine ⟨Units.mk0 x ?_,rfl⟩
      rintro rfl
      exact hnz (by simpa only [T,mem_preimage,zero_pow hn] using hx))
  apply hU.of_isClosed_subset (hC.isClosed.preimage hf)
  intro x hx
  exact ⟨f x,hx,Units.val_pow_eq_pow_val _ _⟩

/-- The multiplicative Haar measure pushed forward by the power map is
proportional to its restriction to the open subgroup of powers. -/
private theorem map_unitPower_proportional {K : Type*} [NontriviallyNormedField K]
    [ProperSpace K] [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure Kˣ) [μ.IsHaarMeasure] (n : ℕ) (hn : (n : K) ≠ 0) :
    ∃ c : ℝ≥0, μ.map (fun x : Kˣ => x^n) =
      c • μ.restrict ((powMonoidHom n : Kˣ →* Kˣ).range : Set Kˣ) := by
  let H := (powMonoidHom n : Kˣ →* Kˣ).range
  let f := (powMonoidHom n : Kˣ →* Kˣ).rangeRestrict
  have hp := unitPower_proper (K := K) n (by rintro rfl; simp at hn)
  have ho : IsOpen (H : Set Kˣ) := isOpen_unit_powers n hn
  have emb : Topology.IsOpenEmbedding H.subtype := ho.isOpenEmbedding_subtypeVal
  letI : LocallyCompactSpace H := ho.locallyCompactSpace
  letI : SecondCountableTopology Kˣ := Units.isEmbedding_val₀.secondCountableTopology
  have hf : Continuous f := (continuous_id.pow n : Continuous (fun x : Kˣ => x^n)).subtype_mk _
  letI : SecondCountableTopology H := emb.isEmbedding.secondCountableTopology
  letI : (μ.map f).IsHaarMeasure := Measure.isHaarMeasure_map μ f hf
    (MonoidHom.rangeRestrict_surjective _) hp
  letI : (μ.comap H.subtype).IsHaarMeasure := Measure.IsHaarMeasure.comap (mH := inferInstance) μ emb
  obtain ⟨c,he⟩ : ∃ c : ℝ≥0, μ.map f = c • μ.comap H.subtype :=
    ⟨_,Measure.isMulLeftInvariant_eq_smul _ _⟩
  refine ⟨c,?_⟩
  have h := congrArg (Measure.map H.subtype) he
  rw [Measure.map_map emb.continuous.measurable hf.measurable,Measure.map_smul (hf := emb.continuous.aemeasurable),
    emb.measurableEmbedding.map_comap] at h
  exact h.trans (by rw [show range H.subtype = (H : Set Kˣ) from Subtype.range_coe])

namespace Datum
open NumberField IsDedekindDomain Polynomial
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)
variable (p : HeightOneSpectrum (𝓞 F))
local notation "K" => LocalField F (Sum.inr p)
local notation "v" => (Sum.inr p : Place F)
local notation "dx" => selfDual F d.character v
local notation "μ" => d.lineMeasure v

/-- On a finite completion, the number of sheets of the power map and the
absolute value of its derivative give the exact pushforward of multiplicative Haar measure. -/
theorem finite_map_lineMeasure_pow :
    (μ).map (fun u : Kˣ => u^n) = ((n : ℝ) / ‖(n : K)‖).toNNReal •
      (μ).restrict ((powMonoidHom n : Kˣ →* Kˣ).range : Set Kˣ) := by
  letI : NontriviallyNormedField (p.adicCompletion F) := FinitePlace.nontriviallyNormedCompletion p
  letI : ProperSpace (p.adicCompletion F) := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace _
  letI : ProperSpace K := inferInstanceAs (ProperSpace (p.adicCompletion F))
  letI : MeasurableSpace (p.adicCompletion F) := borel _
  letI : BorelSpace (p.adicCompletion F) := ⟨rfl⟩
  letI : IsUltrametricDist K := inferInstanceAs (IsUltrametricDist (p.adicCompletion F))
  letI : CharZero K := charZero_of_injective_ringHom (diagonal F v).injective
  have hn : (n : K) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  let H := ((powMonoidHom n : Kˣ →* Kˣ).range : Set Kˣ)
  have hH : IsOpen H := isOpen_unit_powers («K» := p.adicCompletion F) n hn
  have hζ : IsPrimitiveRoot (diagonal F v d.root) n := d.primitive.map_of_injective (diagonal F v).injective
  let B : Set K := sphere 0 1
  have hB : IsClopen B := IsUltrametricDist.isClopen_sphere _ one_ne_zero
  let g : K → ℂ := B.indicator (fun _ => 1)
  let k : Kˣ → ℂ := fun u => g u.val
  have memB (x : K) : x ∈ B ↔ ‖x‖ = 1 := mem_sphere_zero_iff_norm
  have gl : IsLocallyConstant g := (LocallyConstant.charFn ℂ hB).isLocallyConstant
  have g0 : g 0 = 0 := indicator_of_notMem (by simp [memB]) _
  have gc : HasCompactSupport g := HasCompactSupport.intro (isCompact_sphere _ _) (fun _ hx => indicator_of_notMem hx _)
  let I := ∫ x, g x ∂dx
  let P (y : K) := ∃ x : K, x^n=y
  let J := ∫ y, (if P y then g y else 0) ∂dx
  have hI : I ≠ 0 := by
    letI : (dx).IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
    have pos := hB.isOpen.measure_pos dx (show B.Nonempty from ⟨1,(memB _).mpr norm_one⟩)
    have hc : IsCompact B := isCompact_sphere _ _
    simp [I,g,integral_indicator hB.isClosed.measurableSet,
      Measure.real,ENNReal.toReal_ne_zero.mpr ⟨pos.ne',hc.measure_ne_top⟩]
  have rootSum (y : K) : (∑ x ∈ nthRootsFinset n y, g x) = (n : ℂ) * (if P y then g y else 0) := by
    by_cases h : P y
    · rw [if_pos h]
      by_cases hy : y = 0
      · subst y
        apply Eq.trans (Finset.sum_eq_zero fun x hx => ?_) (by simp [g0])
        have he := (mem_nthRootsFinset (NeZero.pos n) _).mp hx
        exact (eq_zero_of_pow_eq_zero he) ▸ g0
      have card : (nthRootsFinset n y).card = n := by
        rw [nthRootsFinset,Multiset.toFinset_card_of_nodup (hζ.nthRoots_nodup hy),hζ.card_nthRoots,if_pos h]
      have same (x) (hx : x ∈ nthRootsFinset n y) : g x = g y := by
        have he := (mem_nthRootsFinset (NeZero.pos n) _).mp hx
        have iff : y ∈ B ↔ x ∈ B := by
          rw [memB,memB,← he,norm_pow,pow_eq_one_iff_of_nonneg (norm_nonneg _) (NeZero.ne n)]
        by_cases hx' : x ∈ B <;> simp [g,hx',iff]
      rw [Finset.sum_congr rfl same,Finset.sum_const,card,nsmul_eq_mul]
    · rw [if_neg h,mul_zero]
      exact Finset.sum_eq_zero fun x hx => (h ⟨x,(mem_nthRootsFinset (NeZero.pos n) _).mp hx⟩).elim
  have area : (n : ℂ)*J = (‖(n : K)‖ : ℂ)*I := by
    have h := d.finite_power_area p gl gc g0
    dsimp only at h
    change (∫ y : K, ∑ x ∈ nthRootsFinset n y, g x ∂dx) = _ at h
    simp_rw [rootSum] at h
    rw [integral_const_mul] at h
    refine h.trans ?_
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ B
    · rw [norm_mul,norm_pow,(memB _).mp hx,one_pow,mul_one]
    · simp [g,indicator_of_notMem hx]
  letI : SecondCountableTopology (p.adicCompletion F) := completionSecondCountable v
  obtain ⟨c,hc⟩ := @map_unitPower_proportional (p.adicCompletion F) (FinitePlace.nontriviallyNormedCompletion p)
    (inferInstanceAs (ProperSpace (p.adicCompletion F))) (completionSecondCountable v) (borel _) ⟨rfl⟩
    (d.lineMeasure v) (d.lineMeasure_haar v) n hn
  have hpush : (μ).map (fun x : Kˣ => x^n) = c • (μ).restrict H := hc
  have kpow (u : Kˣ) : k (u^n) = k u := by
    have he : (u^n).val ∈ B ↔ u.val ∈ B := by
      rw [memB,memB,Units.val_pow_eq_pow_val,norm_pow,pow_eq_one_iff_of_nonneg (norm_nonneg _) (NeZero.ne n)]
    change B.indicator _ (u^n).val = B.indicator _ u.val
    by_cases hu : u.val ∈ B
    · rw [indicator_of_mem (he.mpr hu),indicator_of_mem hu]
    · rw [indicator_of_notMem (he.not.mpr hu),indicator_of_notMem hu]
  have normed (x : K) : g x / (‖x‖ : ℂ) = g x := by
    by_cases hx : x ∈ B
    · rw [(memB _).mp hx,Complex.ofReal_one,div_one]
    · simp [g,indicator_of_notMem hx]
  have Ik : (∫ u, k u ∂μ) = I := by
    rw [d.integral_lineMeasure]
    unfold lineIntegral
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ≠ 0
    · exact (dif_pos hx).trans (normed x)
    · simp [not_ne_iff.mp hx,g0]
  have Jk : (∫ u in H, k u ∂μ) = J := by
    rw [← integral_indicator hH.measurableSet,d.integral_lineMeasure]
    unfold lineIntegral
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ≠ 0
    · rw [dif_pos hx]
      have he : Units.mk0 x hx ∈ H ↔ P x := by
        constructor
        · rintro ⟨u,hu⟩
          exact ⟨u.val,(Units.val_pow_eq_pow_val u n).symm.trans (congrArg Units.val hu)⟩
        · rintro ⟨t,rfl⟩
          exact ⟨Units.mk0 t (fun h => hx (by rw [h,zero_pow (NeZero.ne n)])),Units.ext (Units.val_pow_eq_pow_val _ _)⟩
      by_cases h : P x
      · rw [indicator_of_mem (he.mpr h),if_pos h]; exact normed x
      · simp only [indicator_of_notMem (he.not.mpr h),zero_div,if_neg h]
    · simp [not_ne_iff.mp hx,g0]
  have eqn : I = (c : ℂ)*J := by
    have h := integral_map («μ» := μ) ((continuous_id.pow n : Continuous (fun x : Kˣ => x^n)).aemeasurable)
      ((gl.continuous.comp Units.continuous_val).aestronglyMeasurable («μ» := (μ).map (fun x : Kˣ => x^n)))
    change (∫ x, k x ∂(μ).map (fun x : Kˣ => x^n)) = ∫ u, k (u^n) ∂μ at h
    simp_rw [kpow] at h
    rw [hpush,integral_smul_nnreal_measure,Ik,Jk] at h
    exact h.symm
  have hJ : J ≠ 0 := fun hz => hI (by rw [eqn,hz,mul_zero])
  have scale : ((n : ℂ) - (‖(n : K)‖ : ℂ)*c)*J = 0 := by rw [sub_mul,mul_assoc,← eqn]; exact sub_eq_zero.mpr area
  have ce : (c : ℝ) = (n:ℝ) / ‖(n : K)‖ := by
    have h := sub_eq_zero.mp ((mul_eq_zero.mp scale).resolve_right hJ)
    apply (eq_div_iff (norm_pos_iff.mpr hn).ne').mpr
    exact_mod_cast (mul_comm (c : ℂ) _).trans h.symm
  rw [hpush,← ce,Real.toNNReal_coe]
end Datum

private def annulus {K : Type*} [NormedField K] (R : ℝ) : Set Kˣ := {x | 1 ≤ ‖x.val‖ ∧ ‖x.val‖ < R}

private theorem measurable_annulus {K : Type*} [NormedField K] [MeasurableSpace K] [BorelSpace K]
    (R : ℝ) : MeasurableSet (annulus (K := K) R) :=
  (measurableSet_Ico : MeasurableSet (Ico 1 R)).preimage Units.continuous_val.norm.measurable

private theorem annulus_finite {K : Type*} [NormedField K] [ProperSpace K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure Kˣ) [IsFiniteMeasureOnCompacts μ] (R : ℝ) :
    μ (annulus (K := K) R) ≠ ⊤ := by
  let C := closedBall (0:K) R ∩ {x : K | 1 ≤ ‖x‖}
  have hC : IsCompact C := (isCompact_closedBall _ _).inter_right (isClosed_le continuous_const continuous_norm)
  have hU := Units.isEmbedding_val₀.isInducing.isCompact_preimage' hC (by
    rintro x hx
    exact ⟨Units.mk0 x (norm_pos_iff.mp (zero_lt_one.trans_le hx.2)),rfl⟩)
  exact measure_ne_top_of_subset (fun x (hx : x ∈ annulus R) =>
    (show x.val ∈ C from ⟨mem_closedBall_zero_iff.mpr hx.2.le,hx.1⟩)) hU.measure_ne_top

/-- Count adjacent radial annuli by Haar invariance under multiplication by a power. -/
private theorem annulus_powers {K : Type*} [NormedField K] [ProperSpace K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure Kˣ) [μ.IsHaarMeasure] (H : Subgroup Kˣ)
    (ho : IsOpen (H : Set Kˣ)) (a : Kˣ) (ha : a ∈ H) (hr : 1 < ‖a.val‖) (k : ℕ) :
    μ.real (annulus (‖a.val‖^k) ∩ H) = k * μ.real (annulus ‖a.val‖ ∩ H) := by
  let r := ‖a.val‖
  let S (j : ℕ) := annulus (K := K) (r^j) ∩ (H : Set Kˣ)
  let T := annulus (K := K) r ∩ (H : Set Kˣ)
  have pos : 0 < r := zero_lt_one.trans hr
  have fin (j) : μ (S j) ≠ ⊤ := measure_ne_top_of_subset inter_subset_left (annulus_finite μ _)
  change μ.real (S k) = k * μ.real T
  induction k with
  | zero =>
    have empty : S 0 = ∅ := eq_empty_iff_forall_notMem.mpr (fun x hx => (not_lt_of_ge hx.1.1) (by simpa using hx.1.2))
    simp [empty]
  | succ k ih =>
    let V := (fun x : Kˣ => (a^k)⁻¹*x) ⁻¹' T
    have memV (x : Kˣ) : x ∈ V ↔ (r^k ≤ ‖x.val‖ ∧ ‖x.val‖ < r^(k+1)) ∧ x ∈ H := by
      have hn : ‖((a^k)⁻¹*x).val‖ = ‖x.val‖ / r^k := by simp [r,Units.val_mul,Units.val_inv_eq_inv_val,Units.val_pow_eq_pow_val,norm_mul,norm_pow,div_eq_inv_mul]
      change (1 ≤ ‖((a^k)⁻¹*x).val‖ ∧ ‖((a^k)⁻¹*x).val‖ < r) ∧ _ ↔ _
      rw [hn,one_le_div (pow_pos pos _),div_lt_iff₀ (pow_pos pos _),pow_succ']
      exact and_congr_right (fun _ => H.mul_mem_cancel_left (H.inv_mem (H.pow_mem ha k)))
    have union : S (k+1) = S k ∪ V := by
      ext x
      rw [mem_union,memV]
      change (1 ≤ ‖x.val‖ ∧ ‖x.val‖ < r^(k+1)) ∧ x ∈ H ↔
        ((1 ≤ ‖x.val‖ ∧ ‖x.val‖ < r^k) ∧ x ∈ H) ∨ _
      have hlo := one_le_pow₀ hr.le (n := k)
      have hhi : r^k < r^(k+1) := pow_lt_pow_right₀ hr (Nat.lt_succ_self _)
      grind
    have dis : Disjoint (S k) V := disjoint_left.mpr fun x hx hv => (not_lt_of_ge (memV x |>.mp hv).1.1) hx.1.2
    have measV : MeasurableSet V := ((measurable_annulus _).inter ho.measurableSet).preimage
      (continuous_const.mul continuous_id).measurable
    have meas : μ V = μ T := measure_preimage_mul μ _ T
    rw [union,measureReal_union dis measV (fin k) (meas ▸ measure_ne_top_of_subset inter_subset_left (annulus_finite μ _)),
      show μ.real V = μ.real T from congrArg ENNReal.toReal meas,ih,Nat.cast_succ,add_mul,one_mul]

private theorem arch_power_scalar {K : Type*} [NontriviallyNormedField K] [ProperSpace K]
    [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure Kˣ) [μ.IsHaarMeasure] (n : ℕ) (hn : (n : K) ≠ 0)
    (a b : Kˣ) (ha : a ∈ (powMonoidHom n : Kˣ →* Kˣ).range) (hb : 1 < ‖b.val‖) (hab : ‖b.val‖ < ‖a.val‖)
    (l : ℝ) (index : μ.real (annulus ‖a.val‖) = l * μ.real (annulus ‖a.val‖ ∩ (powMonoidHom n : Kˣ →* Kˣ).range)) :
    μ.map (fun x : Kˣ => x^n) = (l / n).toNNReal • μ.restrict ((powMonoidHom n : Kˣ →* Kˣ).range : Set Kˣ) := by
  let H := (powMonoidHom n : Kˣ →* Kˣ).range
  have ho : IsOpen (H : Set Kˣ) := isOpen_unit_powers n hn
  obtain ⟨c,hc⟩ := map_unitPower_proportional μ n hn
  have nz : n ≠ 0 := by rintro rfl; exact hn (by simp)
  have he := congrArg (fun m : Measure Kˣ => m.real (annulus (‖a.val‖^n))) hc
  simp only [measureReal_nnreal_smul_apply,measureReal_restrict_apply (measurable_annulus _)] at he
  have pre : (fun x : Kˣ => x^n) ⁻¹' annulus (‖a.val‖^n) = annulus ‖a.val‖ := by
    ext x
    change (1 ≤ ‖(x^n).val‖ ∧ ‖(x^n).val‖ < _) ↔ _
    rw [Units.val_pow_eq_pow_val,norm_pow,one_le_pow_iff_of_nonneg (norm_nonneg _) nz,
      pow_lt_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) nz]
    rfl
  change (μ.map (fun x : Kˣ => x^n)).real _ = _ at he
  have hm : Measurable (fun x : Kˣ => x^n) := (continuous_id.pow n).measurable
  rw [map_measureReal_apply hm (measurable_annulus _),pre,
    annulus_powers μ H ho a ha (hb.trans hab),index] at he
  have hp : μ.real (annulus ‖a.val‖) ≠ 0 := by
    apply (measureReal_eq_zero_iff (annulus_finite μ _)).not.mpr
    let U := {x : Kˣ | 1 < ‖x.val‖ ∧ ‖x.val‖ < ‖a.val‖}
    have o : IsOpen U := (isOpen_lt continuous_const Units.continuous_val.norm).inter (isOpen_lt Units.continuous_val.norm continuous_const)
    exact ne_of_gt ((o.measure_pos μ ⟨b,hb,hab⟩).trans_le (measure_mono (fun x (hx : x ∈ U) => ⟨hx.1.le,hx.2⟩)))
  have hd : μ.real (annulus ‖a.val‖ ∩ H) ≠ 0 := fun hz => hp (by rw [index,hz,mul_zero])
  have ce : (c : ℝ) = l/n := by
    apply (eq_div_iff (Nat.cast_ne_zero.mpr nz)).mpr
    rw [← mul_assoc] at he
    exact (mul_right_cancel₀ hd he).symm
  rw [hc,← ce,Real.toNNReal_coe]

private theorem real_square_index {K : Type*} [NormedField K] [ProperSpace K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure Kˣ) [μ.IsHaarMeasure]
    (e : K ≃+* ℝ) (he : Continuous e) (R : ℝ) :
    μ.real (annulus R) = 2 * μ.real (annulus R ∩ (powMonoidHom 2 : Kˣ →* Kˣ).range) := by
  let H := (powMonoidHom 2 : Kˣ →* Kˣ).range
  have memH (x : Kˣ) : x ∈ H ↔ 0 < e x.val := by
    constructor
    · rintro ⟨y,rfl⟩
      change 0 < e ((y^2).val)
      rw [Units.val_pow_eq_pow_val,map_pow]
      exact sq_pos_of_ne_zero ((map_ne_zero e).mpr y.ne_zero)
    · intro h
      let t := e.symm (Real.sqrt (e x.val))
      have ht : t ≠ 0 := (map_ne_zero _).mpr (Real.sqrt_pos_of_pos h).ne'
      refine ⟨Units.mk0 t ht,Units.ext (e.injective ?_)⟩
      change e (t^2) = e x.val
      rw [map_pow,e.apply_symm_apply,Real.sq_sqrt h.le]
  let T := annulus (K := K) R ∩ (H : Set Kˣ)
  let V := (fun x : Kˣ => (-1)*x) ⁻¹' T
  have hV (x : Kˣ) : x ∈ V ↔ x ∈ annulus R ∧ e x.val < 0 := by
    change (1 ≤ ‖((-1:Kˣ)*x).val‖ ∧ ‖((-1:Kˣ)*x).val‖ < R) ∧ (-1:Kˣ)*x ∈ H ↔ _
    simp only [memH,neg_one_mul,Units.val_neg,norm_neg,map_neg,neg_pos]
    rfl
  have mt : MeasurableSet T := (measurable_annulus _).inter (by
    rw [show (H : Set Kˣ) = {x : Kˣ | 0 < e x.val} from Set.ext memH]
    exact (isOpen_lt continuous_const (he.comp Units.continuous_val)).measurableSet)
  have hTV : annulus R = T ∪ V := by
    ext x
    change x ∈ annulus R ↔ (x ∈ annulus R ∧ x ∈ H) ∨ x ∈ V
    rw [hV,memH]
    have hn := (map_ne_zero e).mpr x.ne_zero
    grind
  have dis : Disjoint T V := disjoint_left.mpr fun x hx hv => (not_lt_of_gt ((memH x).mp hx.2)) ((hV x).mp hv).2
  have mV : μ V = μ T := measure_preimage_mul μ (-1) T
  have fin : μ T ≠ ⊤ := measure_ne_top_of_subset inter_subset_left (annulus_finite μ R)
  change μ.real (annulus R) = 2 * μ.real T
  rw [hTV,measureReal_union' dis mt fin (mV ▸ fin),show μ.real V = μ.real T from congrArg ENNReal.toReal mV,two_mul]

private theorem arch_coordinate_pow {K : Type*} [NontriviallyNormedField K] [ProperSpace K]
    [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] [CharZero K]
    (μ : Measure Kˣ) [μ.IsHaarMeasure] (n : ℕ) (hn₀ : n ≠ 0) (m : ℕ)
    (normNat : ∀ i : ℕ, ‖(i : K)‖ = (i : ℝ))
    (place : (∃ e : K ≃+* ℝ, Continuous e ∧ m = 1 ∧ n ≤ 2) ∨ (Nonempty (K ≃+* ℂ) ∧ m = 2)) :
    μ.map (fun x : Kˣ => x^n) = ((n : ℝ) / (n : ℝ)^m).toNNReal •
      μ.restrict ((powMonoidHom n : Kˣ →* Kˣ).range : Set _) := by
  have hn : (n : K) ≠ 0 := Nat.cast_ne_zero.mpr hn₀
  let b := Units.mk0 (2 : K) (by norm_num)
  let a := b^2
  have hb : ‖b.val‖=2 := normNat 2
  have hab : ‖a.val‖=4 := by simp only [a,Units.val_pow_eq_pow_val,norm_pow,hb]; norm_num
  have calib (l : ℝ) (ha : a ∈ (powMonoidHom n : Kˣ →* Kˣ).range)
      (hi : μ.real (annulus ‖a.val‖) = l * μ.real (annulus ‖a.val‖ ∩ (powMonoidHom n : Kˣ →* Kˣ).range)) :
      μ.map (fun x : Kˣ => x^n) = (l/n).toNNReal •
        μ.restrict ((powMonoidHom n : Kˣ →* Kˣ).range : Set _) :=
    arch_power_scalar μ n hn a b ha
      (by rw [hb]; norm_num) (by rw [hab,hb]; norm_num) l hi
  rcases place with hr|hc
  · obtain ⟨e,hcont,hm,hle⟩ := hr
    have cases_n : n = 1 ∨ n = 2 := by have := Nat.pos_of_ne_zero hn₀; omega
    rcases cases_n with h | h
    · have top : ((powMonoidHom n : Kˣ →* Kˣ).range : Set Kˣ) = univ := by
        apply eq_univ_of_forall
        intro x
        exact ⟨x,by simp [h]⟩
      rw [top,Measure.restrict_univ,h]; simp [Measure.map_id']
    · have hI := real_square_index (K := K) μ e hcont ‖a.val‖
      have he := calib 2 ⟨b,by change b^n=b^2; rw [h]⟩ (by simpa only [h] using hI)
      rw [he,hm,pow_one,h,Nat.cast_ofNat]
  · obtain ⟨⟨e⟩,hm⟩ := hc
    have surj (x : Kˣ) : x ∈ (powMonoidHom n : Kˣ →* Kˣ).range := by
      obtain ⟨z,hz⟩ := IsAlgClosed.exists_pow_nat_eq (e x.val) (Nat.pos_of_ne_zero hn₀)
      have hzero : z ≠ 0 := by
        rintro rfl
        exact ((map_ne_zero e).mpr x.ne_zero) (hz.symm.trans (zero_pow (hn₀)))
      refine ⟨Units.mk0 (e.symm z) ((map_ne_zero _).mpr hzero),Units.ext (e.injective ?_)⟩
      change e ((e.symm z)^n) = _
      rw [map_pow,e.apply_symm_apply,hz]
    have top := eq_univ_of_forall surj
    have he := calib 1 (surj a) (by rw [top,inter_univ,one_mul])
    rw [he,hm]
    congr 2
    field_simp
namespace Datum
open NumberField
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

theorem arch_map_lineMeasure_pow (w : InfinitePlace F) :
    let v : Place F := .inl w
    (d.lineMeasure v).map (fun x : (LocalField F v)ˣ => x^n) =
      ((n : ℝ) / modulus F v (n : LocalField F v)).toNNReal •
        (d.lineMeasure v).restrict ((powMonoidHom n : (LocalField F v)ˣ →* (LocalField F v)ˣ).range : Set _) := by
  let v : Place F := .inl w
  letI iw : NontriviallyNormedField w.Completion := { (inferInstance : NormedField w.Completion) with
    non_trivial := (archNontriviallyNormedCompletion w).non_trivial }
  letI : ProperSpace w.Completion := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace _
  letI : SecondCountableTopology w.Completion := (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  letI : MeasurableSpace w.Completion := borel _
  letI : BorelSpace w.Completion := ⟨rfl⟩
  let μ : Measure w.Completionˣ := d.lineMeasure v
  letI : CharZero w.Completion := charZero_of_injective_ringHom (algebraMap F w.Completion).injective
  have normNat (i : ℕ) : ‖(i : w.Completion)‖ = (i:ℝ) := by
    have h := (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
      (map_zero (InfinitePlace.Completion.extensionEmbedding w)) (i : w.Completion)
    simpa only [map_natCast,Complex.norm_natCast] using h.symm
  change μ.map (fun x : w.Completionˣ => x^n) = ((n:ℝ)/‖(n:w.Completion)‖^w.mult).toNNReal • μ.restrict _
  rw [normNat]
  apply @arch_coordinate_pow w.Completion iw _ _ (borel _) ⟨rfl⟩ _
    μ (d.lineMeasure_haar v) n (NeZero.ne n) w.mult normNat
  by_cases hw : w.IsReal
  · refine Or.inl ⟨InfinitePlace.Completion.ringEquivRealOfIsReal hw,
      (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).continuous,InfinitePlace.mult_isReal ⟨w,hw⟩,?_⟩
    by_contra! h
    have hz := InfinitePlace.IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt h d.primitive
    have pos : 0 < InfinitePlace.nrRealPlaces F := Fintype.card_pos_iff.mpr ⟨⟨w,hw⟩⟩
    omega
  · let h := InfinitePlace.not_isReal_iff_isComplex.mp hw
    exact Or.inr ⟨⟨InfinitePlace.Completion.ringEquivComplexOfIsComplex h⟩,InfinitePlace.mult_isComplex ⟨w,h⟩⟩
/-- The power map has exactly the Haar normalization of the paper at every number-field place. -/
theorem map_lineMeasure_pow (v : Place F) :
    (d.lineMeasure v).map (fun x : (LocalField F v)ˣ => x^n) =
      ((n : ℝ) / modulus F v (n : LocalField F v)).toNNReal •
        (d.lineMeasure v).restrict ((powMonoidHom n : (LocalField F v)ˣ →* (LocalField F v)ˣ).range : Set _) := by
  cases v with
  | inl w => exact d.arch_map_lineMeasure_pow w
  | inr p => exact d.finite_map_lineMeasure_pow p

/-- Integration over the subgroup of powers with the ambient multiplicative Haar measure. -/
theorem lineIntegral_on_powers (v : Place F) (g : (LocalField F v)ˣ → ℂ) (hg : Measurable g) :
    d.lineIntegral v (fun a => if ∃ u : (LocalField F v)ˣ, a=u^n then g a else 0) =
      ((modulus F v (n : LocalField F v) : ℂ) / (n : ℂ)) *
        ∫ u, g (u^n) ∂(d.lineMeasure v) := by
  let H := (powMonoidHom n : (LocalField F v)ˣ →* (LocalField F v)ˣ).range
  have ho : IsOpen (H : Set (LocalField F v)ˣ) := by
    cases v with
    | inl w =>
      letI : NontriviallyNormedField w.Completion := { (inferInstance : NormedField w.Completion) with
        non_trivial := (archNontriviallyNormedCompletion w).non_trivial }
      letI : CharZero w.Completion := charZero_of_injective_ringHom (algebraMap F w.Completion).injective
      exact isOpen_unit_powers (K := w.Completion) n (Nat.cast_ne_zero.mpr (NeZero.ne n))
    | inr p =>
      letI := FinitePlace.nontriviallyNormedCompletion p
      letI : CharZero (p.adicCompletion F) := charZero_of_injective_ringHom (diagonal F (.inr p)).injective
      exact isOpen_unit_powers (K := p.adicCompletion F) n (Nat.cast_ne_zero.mpr (NeZero.ne n))
  have hp : 0 < modulus F v (n : LocalField F v) := by
    have hnz := (diagonal F v).injective.ne (Nat.cast_ne_zero.mpr (NeZero.ne n) : (n:F) ≠ 0)
    have hn : (n : LocalField F v) ≠ 0 := by simpa only [map_natCast,map_zero] using hnz
    cases v <;> simp [modulus,norm_pos_iff,hn,pow_pos (norm_pos_iff.mpr hn)]
  have hi : (fun a => if ∃ u : (LocalField F v)ˣ, a=u^n then g a else 0) = (H : Set _).indicator g := by
    funext a
    have he : a ∈ H ↔ ∃ u : (LocalField F v)ˣ, a=u^n := ⟨fun ⟨u,hu⟩ => ⟨u,hu.symm⟩, fun ⟨u,hu⟩ => ⟨u,hu.symm⟩⟩
    change (if ∃ u : (LocalField F v)ˣ, a=u^n then g a else 0) = if a ∈ H then g a else 0
    rw [he]
  have hm : Measurable (fun u : (LocalField F v)ˣ => u^n) := (continuous_id.pow n).measurable
  rw [hi,← d.integral_lineMeasure,integral_indicator ho.measurableSet,← integral_map hm.aemeasurable hg.aestronglyMeasurable,
    d.map_lineMeasure_pow,integral_smul_nnreal_measure,NNReal.smul_def,Complex.real_smul,
    Real.coe_toNNReal _ (div_nonneg (Nat.cast_nonneg _) hp.le),Complex.ofReal_div,Complex.ofReal_natCast]
  field_simp [Complex.ofReal_ne_zero.mpr hp.ne',(Nat.cast_ne_zero.mpr (NeZero.ne n) : (n:ℂ) ≠ 0)]
  rfl

end Datum
end MetaplecticPoisson
