import MetaplecticSummation.Jacquet.Kernel
import MetaplecticSummation.PowerSubgroup
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Topology.LocallyConstant.Algebra

/-! Local power-class moments for the global line summation formula. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open MeasureTheory NumberField Filter Set Metric
open scoped Topology ContDiff
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n]

private abbrev nontrivialArchNorm (w : InfinitePlace F) : NontriviallyNormedField w.Completion where
  non_trivial := by
    refine ⟨algebraMap F w.Completion (2 : F), ?_⟩
    have h := InfinitePlace.Completion.norm_coe w ((WithAbs.equiv w.1).symm (2 : F))
    change 1 < ‖algebraMap F w.Completion (2 : F)‖
    rw [show ‖algebraMap F w.Completion (2 : F)‖ = w (2 : F) from h]
    simpa only [← Nat.cast_ofNat (R := F) (n := 2), w.map_natCast] using (by norm_num : (1:ℝ) < (2:ℕ))

abbrev Weights (S : Finset (Place F)) := (v : S) → Weight v.val
abbrev Admissible {S : Finset (Place F)} (W : Weights S) := ∀ v, TestWeight v.val (W v)
abbrev PowerClass (n : ℕ) (v : Place F) := (LocalField F v)ˣ ⧸ (powMonoidHom n :
  (LocalField F v)ˣ →* (LocalField F v)ˣ).range
abbrev Classes (n : ℕ) (S : Finset (Place F)) := (v : S) → PowerClass n v.val

theorem finite_power_classes (v : Place F) : Finite (PowerClass n v) := by
  cases v with
  | inl w =>
    letI := nontrivialArchNorm w
    letI : ProperSpace w.Completion := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace _
    letI : CharZero w.Completion := charZero_of_injective_ringHom (algebraMap F w.Completion).injective
    exact finite_unit_power_quotient (K := w.Completion) n (Nat.cast_ne_zero.mpr (NeZero.ne n))
  | inr p =>
    letI : NontriviallyNormedField (p.adicCompletion F) := FinitePlace.nontriviallyNormedCompletion p
    letI : ProperSpace (p.adicCompletion F) := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace _
    letI : CharZero (p.adicCompletion F) := charZero_of_injective_ringHom (algebraMap F (p.adicCompletion F)).injective
    exact finite_unit_power_quotient (K := p.adicCompletion F) n (Nat.cast_ne_zero.mpr (NeZero.ne n))

private theorem open_powerClass (v : Place F) (β : PowerClass n v) :
    IsOpen {x : (LocalField F v)ˣ | QuotientGroup.mk x = β} := by
  let H := (powMonoidHom n : (LocalField F v)ˣ →* (LocalField F v)ˣ).range
  have hH : IsOpen (H : Set (LocalField F v)ˣ) := by
    cases v with
    | inl w =>
      letI := nontrivialArchNorm w
      letI : ProperSpace w.Completion := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace _
      letI : CharZero w.Completion := charZero_of_injective_ringHom (algebraMap F w.Completion).injective
      exact isOpen_unit_powers (K := w.Completion) n (Nat.cast_ne_zero.mpr (NeZero.ne n))
    | inr p =>
      letI := FinitePlace.nontriviallyNormedCompletion p
      letI : CharZero (p.adicCompletion F) := charZero_of_injective_ringHom (algebraMap F (p.adicCompletion F)).injective
      exact isOpen_unit_powers (K := p.adicCompletion F) n (Nat.cast_ne_zero.mpr (NeZero.ne n))
  letI : DiscreteTopology (PowerClass n v) := QuotientGroup.discreteTopology hH
  exact (isOpen_discrete ({β} : Set (PowerClass n v))).preimage (QuotientGroup.continuous_mk (N := H))

private theorem arch_bump {K E : Type} [NormedField K] [NormedField E] [NormedAlgebra ℝ E]
    [FiniteDimensional ℝ E] (e : K ≃+* E) (he : Isometry e)
    {U : Set Kˣ} (hU : IsOpen U) (a : Kˣ) (ha : a ∈ U) :
    ∃ g : Kˣ → ℝ, Continuous g ∧ HasCompactSupport g ∧ (∀ x, 0 ≤ g x) ∧ g a = 1 ∧
      (∀ x ∉ U, g x = 0) ∧ ∀ z : ℂ, archSmooth e (fun x => z * (g x : ℂ)) := by
  let i : K ≃ᵢ E := ⟨e.toEquiv,he⟩
  let j : Kˣ → E := fun x => i x.val
  have hj : Topology.IsOpenEmbedding j := i.toHomeomorph.isOpenEmbedding.comp
    (show Topology.IsOpenEmbedding (Units.val : Kˣ → K) from
      (IsOpen.isOpenEmbedding_subtypeVal isOpen_compl_singleton).comp unitsHomeomorphNeZero.isOpenEmbedding)
  obtain ⟨b,hsub,hk,hd,hb,h1⟩ := exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞))
    ((hj.isOpenMap U hU).mem_nhds (mem_image_of_mem j ha))
  refine ⟨b ∘ j,hd.continuous.comp hj.continuous,?_,fun x => (hb ⟨_,rfl⟩).1,h1,?_,?_⟩
  · exact HasCompactSupport.intro (hj.isInducing.isCompact_preimage' hk
      (hsub.trans (image_subset_range ..))) (fun x hx => (image_eq_zero_of_notMem_tsupport (f := b) (x := j x) hx))
  · intro x hx
    change b (j x) = 0
    apply image_eq_zero_of_notMem_tsupport
    exact fun h => hx (by obtain ⟨y,hy,heq⟩ := hsub h; exact hj.injective heq ▸ hy)
  · intro z
    apply ((contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hd)).contDiffOn :
      ContDiffOn ℝ ∞ (fun t => z * (b t : ℂ)) {0}ᶜ).congr
    intro t ht
    have ht' : e.symm t ≠ 0 := (map_ne_zero e.symm).mpr ht
    simp only [dif_pos ht',Function.comp_apply,j,Units.val_mk0]
    exact congrArg (fun s => z * (b s : ℂ)) (e.apply_symm_apply t)

private theorem finite_bump {K : Type} [NormedField K] [ProperSpace K] [IsUltrametricDist K]
    {U : Set Kˣ} (hU : IsOpen U) (a : Kˣ) (ha : a ∈ U) :
    ∃ g : Kˣ → ℝ, Continuous g ∧ HasCompactSupport g ∧ (∀ x, 0 ≤ g x) ∧ g a = 1 ∧
      (∀ x ∉ U, g x = 0) ∧ ∀ z : ℂ, IsLocallyConstant (fun x => z * (g x : ℂ)) := by
  have hj : Topology.IsOpenEmbedding (Units.val : Kˣ → K) :=
    (IsOpen.isOpenEmbedding_subtypeVal isOpen_compl_singleton).comp unitsHomeomorphNeZero.isOpenEmbedding
  obtain ⟨r,hr,hs⟩ := Metric.mem_nhds_iff.mp ((hj.isOpenMap U hU).mem_nhds (mem_image_of_mem Units.val ha))
  let B : Set K := closedBall (a.val : K) (r/2)
  have hcl : IsClopen B := IsUltrametricDist.isClopen_closedBall _ (half_pos hr).ne'
  have sub : B ⊆ Units.val '' U := (closedBall_subset_ball (half_lt_self hr)).trans hs
  let C := (Units.val : Kˣ → K) ⁻¹' B
  have hc : IsClopen C := hcl.preimage hj.continuous
  have hk : IsCompact C := hj.isInducing.isCompact_preimage' (isCompact_closedBall _ _) (sub.trans (image_subset_range ..))
  let g := C.indicator (fun _ => (1 : ℝ))
  have lg : IsLocallyConstant g := (LocallyConstant.charFn ℝ hc).isLocallyConstant
  have kg : HasCompactSupport g := HasCompactSupport.intro hk (fun _ h => indicator_of_notMem h _)
  refine ⟨g,lg.continuous,kg,fun x => indicator_nonneg (fun _ _ => zero_le_one) x,?_,?_,?_⟩
  · exact indicator_of_mem (show a ∈ C from mem_closedBall_self (half_pos hr).le) _
  · intro x hx
    apply indicator_of_notMem
    intro h
    obtain ⟨y,hy,e⟩ := sub h
    exact hx (Units.ext e ▸ hy)
  · intro z
    exact lg.comp (fun t => z * (t : ℂ))

private theorem exists_test_bump (v : Place F) {U : Set (LocalField F v)ˣ} (hU : IsOpen U)
    (a : (LocalField F v)ˣ) (ha : a ∈ U) :
    ∃ g : (LocalField F v)ˣ → ℝ, Continuous g ∧ HasCompactSupport g ∧ (∀ x, 0 ≤ g x) ∧ g a = 1 ∧
      (∀ x ∉ U, g x = 0) ∧ ∀ z : ℂ, TestWeight v (fun x => z * (g x : ℂ)) := by
  cases v with
  | inl w =>
    by_cases hw : w.IsReal
    · obtain ⟨g,hc,hk,hp,hg,hs,hd⟩ := arch_bump (InfinitePlace.Completion.ringEquivRealOfIsReal hw)
        (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw) hU a ha
      exact ⟨g,hc,hk,hp,hg,hs,fun z => ⟨(hk.comp_left Complex.ofReal_zero).mul_left,
        by dsimp only; rw [dif_pos hw]; exact hd z⟩⟩
    · let h := InfinitePlace.not_isReal_iff_isComplex.mp hw
      obtain ⟨g,hc,hk,hp,hg,hs,hd⟩ := arch_bump (InfinitePlace.Completion.ringEquivComplexOfIsComplex h)
        (InfinitePlace.Completion.isometry_extensionEmbedding w) hU a ha
      exact ⟨g,hc,hk,hp,hg,hs,fun z => ⟨(hk.comp_left Complex.ofReal_zero).mul_left,
        by dsimp only; rw [dif_neg hw]; exact hd z⟩⟩
  | inr p =>
    let K := p.adicCompletion F
    letI : NontriviallyNormedField K := FinitePlace.nontriviallyNormedCompletion p
    letI : ProperSpace K := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace _
    obtain ⟨g,hc,hk,hp,hg,hs,hd⟩ := finite_bump (K := p.adicCompletion F) hU a ha
    exact ⟨g,hc,hk,hp,hg,hs,fun z => ⟨(hk.comp_left Complex.ofReal_zero).mul_left,hd z⟩⟩

variable (d : Datum F n)

/-- The weighted integral of a test on a single local power class. -/
def classMoment (v : Place F) (W : Weight v) (β : PowerClass n v) : ℂ :=
  d.lineIntegral v fun x => if QuotientGroup.mk x = β then
    W x * ((modulus F v x ^ (1 / (n : ℝ)) : ℝ) : ℂ) else 0

/-- The product of the local moments at the exceptional places. -/
def moment {S : Finset (Place F)} (W : Weights S) (β : Classes n S) : ℂ :=
  ∏ v : S, d.classMoment v.val (W v) (β v)

/-- A test weight supported on one power class can be normalized to have moment one. -/
theorem exists_classMoment_single (v : Place F) (β : PowerClass n v) :
    ∃ W : Weight v, TestWeight v W ∧
      (∀ x : (LocalField F v)ˣ, QuotientGroup.mk x ≠ β → W x = 0) ∧
      ∀ γ, d.classMoment v W γ = if γ = β then 1 else 0 := by
  obtain ⟨a,ha⟩ := QuotientGroup.mk'_surjective _ β
  obtain ⟨g,hc,hk,hp,hg,hs,ht⟩ := exists_test_bump v (open_powerClass v β) a ha
  let m (x : (LocalField F v)ˣ) := modulus F v x.val ^ (1 / (n : ℝ))
  have hm (x) : 0 < m x := by
    apply Real.rpow_pos_of_pos
    exact lt_of_le_of_ne (by cases v <;> simp [modulus,pow_nonneg]) (modulus_ne_zero v x).symm
  have hcmod : Continuous (modulus F v) := by
    cases v with
    | inl w => exact continuous_norm.pow _
    | inr p => exact continuous_norm
  have hcm : Continuous m :=
    (Real.continuous_rpow_const (by positivity : 0 ≤ 1 / (n : ℝ))).comp (hcmod.comp Units.continuous_val)
  let f (x : (LocalField F v)ˣ) := g x * m x
  have hcf : Continuous f := hc.mul hcm
  let J := ∫ x, f x ∂(d.lineMeasure v)
  have hJ : 0 < J := integral_pos_of_integrable_nonneg_nonzero hcf
    (hcf.integrable_of_hasCompactSupport hk.mul_right) (fun x => mul_nonneg (hp x) (hm x).le)
    (x := a) (by simpa only [f,hg,one_mul] using (hm a).ne')
  let z := ((J : ℂ))⁻¹
  let W (x : (LocalField F v)ˣ) := z * (g x : ℂ)
  have off (x : (LocalField F v)ˣ) (hx : QuotientGroup.mk x ≠ β) : W x = 0 := by simp [W,hs x hx]
  refine ⟨W,ht z,off,fun γ => ?_⟩
  rw [classMoment,← d.integral_lineMeasure]
  by_cases he : γ = β
  · subst γ
    simp only [ite_true]
    have eqn (x : (LocalField F v)ˣ) : (if QuotientGroup.mk x = β then W x * (m x : ℂ) else 0) =
        z * (f x : ℂ) := by
      by_cases hx : QuotientGroup.mk x = β
      · simp [hx,W,f,mul_assoc]
      · simp [hx,f,hs x hx]
    change (∫ x, (if QuotientGroup.mk x = β then W x * (m x : ℂ) else 0) ∂_) = _
    simp_rw [eqn]
    rw [integral_const_mul,show (∫ x, (f x : ℂ) ∂(d.lineMeasure v)) = (J : ℂ) from integral_ofReal]
    exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hJ.ne')
  · have eqn (x : (LocalField F v)ˣ) : (if QuotientGroup.mk x = γ then W x * (m x : ℂ) else 0) = 0 := by
      split_ifs with hx
      · rw [off x (hx ▸ he),zero_mul]
      · rfl
    change (∫ x, (if QuotientGroup.mk x = γ then W x * (m x : ℂ) else 0) ∂_) = _
    simp only [eqn,integral_zero,if_neg he]

private theorem archSmooth_sum {K E : Type} [Field K] [NormedField E] [NormedAlgebra ℝ E]
    (e : K ≃+* E) {ι : Type*} (T : Finset ι) (a : ι → ℂ) (W : ι → Kˣ → ℂ)
    (h : ∀ i ∈ T, archSmooth e (W i)) : archSmooth e (∑ i ∈ T, a i • W i) := by
  let extW (i : ι) (x : E) := if hx : e.symm x ≠ 0 then W i (Units.mk0 _ hx) else 0
  have hs (i) (hi : i ∈ T) : ContDiffOn ℝ ∞ (fun x => a i * extW i x) {0}ᶜ :=
    contDiffOn_const.mul (h i hi)
  apply (ContDiffOn.sum hs).congr
  intro x hx
  have h₀ : e.symm x ≠ 0 := (map_ne_zero _).mpr hx
  have hx' : x ≠ 0 := hx
  simp [extW,h₀,hx',Finset.sum_apply]

theorem testWeight_sum (v : Place F) {ι : Type*} (T : Finset ι)
    (a : ι → ℂ) (W : ι → Weight v) (h : ∀ i ∈ T, TestWeight v (W i)) :
    TestWeight v (∑ i ∈ T, a i • W i) := by
  refine ⟨HasCompactSupport.finset_sum (fun i hi => (h i hi).1.mul_left),?_⟩
  cases v with
  | inr p =>
    have local_sum (T : Finset ι) (h : ∀ i ∈ T, IsLocallyConstant (W i)) :
        IsLocallyConstant (∑ i ∈ T, a i • W i) := by
      induction T using Finset.induction_on with
      | empty => rw [Finset.sum_empty]; exact IsLocallyConstant.const 0
      | insert i T hi ih =>
        rw [Finset.sum_insert hi]
        exact ((h i (Finset.mem_insert_self ..)).comp (a i * ·)).add
          (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
    exact local_sum T fun i hi => (h i hi).2
  | inl w =>
    have reg := fun i hi => (h i hi).2
    dsimp only at reg ⊢
    split <;> rename_i hw <;> simp only [hw,↓reduceDIte] at reg <;> exact archSmooth_sum _ _ _ _ reg

/-- The local moment vector can take arbitrary complex values, simultaneously on every class. -/
theorem exists_classMoment_vector (v : Place F) (a : PowerClass n v → ℂ) :
    ∃ W : Weight v, TestWeight v W ∧ d.classMoment v W = a := by
  letI : Fintype (PowerClass n v) := @Fintype.ofFinite _ (finite_power_classes v)
  choose B hB hoff hM using d.exists_classMoment_single v
  let W := ∑ β, a β • B β
  refine ⟨W,testWeight_sum v Finset.univ a B (fun β _ => hB β),?_⟩
  funext γ
  have same (x : (LocalField F v)ˣ) (hx : QuotientGroup.mk x = γ) : W x = a γ * B γ x := by
    simp only [W,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    exact Finset.sum_eq_single γ (fun β _ hβ => by rw [hoff β x (hx.trans_ne hβ.symm),mul_zero])
      (fun h => (h (Finset.mem_univ _)).elim)
  have eqn : d.classMoment v W γ = a γ * d.classMoment v (B γ) γ := by
    unfold classMoment
    simp_rw [← d.integral_lineMeasure]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    split_ifs with hx
    · rw [same x hx,mul_assoc]
    · rw [mul_zero]
  simp [eqn,hM]

/-- Compactly supported smooth (or locally constant) test weights form a complex vector space. -/
def testWeights (v : Place F) : Submodule ℂ (Weight v) :=
  Submodule.ofLinearComb {W | TestWeight v W}
    ⟨0,by simpa using testWeight_sum v (∅ : Finset Unit) (fun _ => 0) (fun _ => 0) (by simp)⟩
    (by
      intro x hx y hy a b
      let f : Bool → Weight v := fun i => if i then x else y
      let z : Bool → ℂ := fun i => if i then a else b
      have h : ∀ i ∈ (Finset.univ : Finset Bool), TestWeight v (f i) := by
        intro i _; cases i <;> first | exact hx | exact hy
      simpa [f,z,add_comm] using testWeight_sum v Finset.univ z f h)

private theorem classMoment_integrable (v : Place F) (W : testWeights v) (b : PowerClass n v) :
    Integrable (fun x : (LocalField F v)ˣ => if QuotientGroup.mk x = b then
      W.val x * ((modulus F v x.val ^ (1 / (n : ℝ)) : ℝ) : ℂ) else 0) (d.lineMeasure v) := by
  have hW : TestWeight v W.val := W.property
  have hc : Continuous (modulus F v) := by
    cases v with
    | inl w => exact continuous_norm.pow _
    | inr p => exact continuous_norm
  let f (x : (LocalField F v)ˣ) : ℂ := W.val x * ((modulus F v x.val ^ (1 / (n : ℝ)) : ℝ) : ℂ)
  have hm : Continuous (fun x : (LocalField F v)ˣ => modulus F v x.val ^ (1 / (n : ℝ))) :=
    (Real.continuous_rpow_const (by positivity)).comp (hc.comp Units.continuous_val)
  have hf : Continuous f := (TestWeight.continuous v hW).mul (Complex.continuous_ofReal.comp hm)
  have hi : Integrable f (d.lineMeasure v) := hf.integrable_of_hasCompactSupport hW.1.mul_right
  let U := {x : (LocalField F v)ˣ | QuotientGroup.mk x = b}
  have hU : MeasurableSet U := (open_powerClass v b).measurableSet
  refine (hi.indicator hU).congr (Filter.Eventually.of_forall fun x => ?_)
  change U.indicator f x = if QuotientGroup.mk x = b then f x else 0
  by_cases hx : QuotientGroup.mk x = b
  · rw [if_pos hx,Set.indicator_of_mem (show x ∈ U from hx)]
  · rw [if_neg hx,Set.indicator_of_notMem (show x ∉ U from hx)]

/-- The local moment map on test weights. -/
def momentMap (v : Place F) : testWeights v →ₗ[ℂ] (PowerClass n v → ℂ) where
  toFun W := d.classMoment v W.val
  map_add' W V := by
    funext b
    simp only [classMoment,← d.integral_lineMeasure,Pi.add_apply]
    rw [← integral_add (d.classMoment_integrable v W b) (d.classMoment_integrable v V b)]
    apply integral_congr_ae
    filter_upwards with x
    split_ifs <;> simp [add_mul]
  map_smul' a W := by
    funext b
    simp only [classMoment,← d.integral_lineMeasure,Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    split_ifs <;> simp [mul_assoc]

theorem momentMap_surjective (v : Place F) : Function.Surjective (d.momentMap v) := by
  intro a
  obtain ⟨W,hW,h⟩ := d.exists_classMoment_vector v a
  exact ⟨⟨W,hW⟩,h⟩

/-- Products of normalized local tests separate the tuples of power classes. -/
theorem exists_moment_single {S : Finset (Place F)} (α : Classes n S) :
    ∃ W : Weights S, Admissible W ∧ ∀ β, d.moment W β = if β = α then 1 else 0 := by
  choose W hW _ hM using fun v : S => d.exists_classMoment_single v.val (α v)
  refine ⟨W,hW,fun β => ?_⟩
  change ∏ v : S, d.classMoment v.val (W v) (β v) = _
  by_cases he : β = α
  · subst β
    simp [hM]
  · obtain ⟨v,hv⟩ := Function.ne_iff.mp he
    rw [if_neg he]
    exact Finset.prod_eq_zero (Finset.mem_univ v) (by rw [hM,if_neg hv])

end MetaplecticPoisson.Datum
