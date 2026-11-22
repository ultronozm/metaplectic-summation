import MetaplecticSummation.Jacquet.Basic

/-! Compact test sections lifting a weight under the Jacquet integral. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField MeasureTheory Filter Set
open scoped Topology
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n) (v : Place F)
local notation "K" => LocalField F v

def jacquetLiftX (W : Weight v) (β : K → ℂ) (x : Kˣ) (y : K) : ℂ :=
  (modulus F v x.val : ℂ)⁻¹ * W x * β (y/x.val)

def jacquetLift (W : Weight v) (β : K → ℂ) : Charts K :=
  (jacquetLiftX v W β, fun x y => if hx : x ≠ 0 then
    (d.symbol v (Units.mk0 x hx) y)⁻¹ * jacquetLiftX v W β (Units.mk0 x hx) y.val else 0)

theorem jacquetLift_glues (W : Weight v) (β : K → ℂ) : Glues (d.symbol v) (d.jacquetLift v W β) := by
  intro x y
  have h : d.symbol v x y ≠ 0 := (d.unitPairing v x y).ne_zero
  simp only [jacquetLift,dif_pos x.ne_zero,Units.mk0_val,← mul_assoc,mul_inv_cancel₀ h,one_mul]

theorem jacquetLift_support (W : Weight v) (hW : HasCompactSupport W) (β : K → ℂ) (hβ : HasCompactSupport β) :
    ∃ C : Set (K × K), IsCompact C ∧ (∀ z ∈ C, z.1 ≠ 0) ∧
      ∀ z ∉ C, xChart (d.jacquetLift v W β) z = 0 ∧ yChart (d.jacquetLift v W β) z = 0 := by
  let h (z : Kˣ × K) := (z.1.val,z.1.val*z.2)
  let C := h '' (tsupport W ×ˢ tsupport β)
  have hh : Continuous h := (Units.continuous_val.comp continuous_fst).prodMk
    ((Units.continuous_val.comp continuous_fst).mul continuous_snd)
  refine ⟨C,(hW.prod hβ).image hh,?_,?_⟩
  · rintro _ ⟨z,_,rfl⟩
    exact z.1.ne_zero
  · intro z hz
    have van (x : Kˣ) (hx : x.val = z.1) : jacquetLiftX v W β x z.2 = 0 := by
      by_cases hw : x ∈ tsupport W
      · have hb : z.2/x.val ∉ tsupport β := by
          intro hb
          apply hz
          exact ⟨(x,z.2/x.val),⟨hw,hb⟩,Prod.ext hx (mul_div_cancel₀ _ x.ne_zero)⟩
        simp [jacquetLiftX,image_eq_zero_of_notMem_tsupport hb]
      · simp [jacquetLiftX,image_eq_zero_of_notMem_tsupport hw]
    constructor
    · by_cases hx : z.1 = 0 <;> simp [xChart,jacquetLift,hx,van]
    · by_cases hx : z.1 = 0 <;> by_cases hy : z.2 = 0 <;> simp [yChart,jacquetLift,hx,hy,van]

theorem jacquetLift_evaluation (W : Weight v) (β : K → ℂ)
    (hβ : (∫ x, β x * d.character.localValue F v (-x) ∂selfDual F d.character v) = 1)
    (ht : d.jacquetLift v W β ∈ d.testSet v) :
    ∃ Φ : d.schwartz v, Φ.val ∈ d.testSet v ∧ d.jacquet v Φ = W := by
  let Φ : d.schwartz v := ⟨_,Submodule.subset_span (Or.inl ht)⟩
  refine ⟨Φ,ht,funext fun c => ?_⟩
  let m : ℂ := modulus F v c.val
  have hm : m ≠ 0 := Complex.ofReal_ne_zero.mpr (modulus_ne_zero v c)
  let g (y : K) := jacquetLiftX v W β c y * d.character.localValue F v (-y/c.val)
  have eval (x : K) : g (c.val*x) = (m⁻¹ * W c) * (β x * d.character.localValue F v (-x)) := by
    simp only [g,jacquetLiftX,mul_div_cancel_left₀ _ c.ne_zero,neg_div,mul_assoc,m]
  have h := d.integral_local_mul v c g
  dsimp only at h
  simp_rw [eval] at h
  rw [integral_const_mul,hβ,mul_one] at h
  change (∫ y, g y ∂selfDual F d.character v) = W c
  exact (eq_div_iff hm).mp h |>.symm.trans (by field_simp)

/-- A single normalized auxiliary works for every compact test weight at the place. -/
def IsJacquetLiftAuxiliary (β : K → ℂ) : Prop :=
  (∫ x, β x * d.character.localValue F v (-x) ∂selfDual F d.character v) = 1 ∧
    ∀ W : Weight v, TestWeight v W → d.jacquetLift v W β ∈ d.testSet v

section Finite
variable (p : Prime F)
local notation "vₚ" => (Sum.inr p : Place F)
local notation "Kₚ" => LocalField F vₚ

omit [NeZero n] in
private theorem finite_lift_auxiliary :
    ∃ β : Kₚ → ℂ, IsLocallyConstant β ∧ HasCompactSupport β ∧
      (∫ x, β x * d.character.localValue F vₚ (-x) ∂selfDual F d.character vₚ) = 1 := by
  letI : NontriviallyNormedField (p.adicCompletion F) := FinitePlace.nontriviallyNormedCompletion p
  letI : ProperSpace Kₚ := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace (p.adicCompletion F)
  letI : IsUltrametricDist Kₚ := inferInstanceAs (IsUltrametricDist (p.adicCompletion F))
  let μ := selfDual F d.character vₚ
  letI : μ.IsAddHaarMeasure := (existsUnique_selfDual F d.character vₚ).exists.choose_spec.1
  have near := (d.character.locallyConstant_finiteValue p).eventually_eq 0
  obtain ⟨r,hr,hs⟩ := Metric.mem_nhds_iff.mp near
  let B := Metric.closedBall (0 : Kₚ) (r/2)
  have hb : IsClopen B := IsUltrametricDist.isClopen_closedBall _ (half_pos hr).ne'
  have hc : IsCompact B := isCompact_closedBall _ _
  have hpos := hb.isOpen.measure_pos μ (show B.Nonempty from ⟨0,Metric.mem_closedBall_self (half_pos hr).le⟩)
  have hm : μ.real B ≠ 0 := (ENNReal.toReal_pos hpos.ne' hc.measure_lt_top.ne).ne'
  let β := B.indicator (fun _ => (μ.real B : ℂ)⁻¹)
  refine ⟨β,?_,HasCompactSupport.intro hc (fun x hx => indicator_of_notMem hx _),?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    by_cases hx : x ∈ B
    · filter_upwards [hb.isOpen.mem_nhds hx] with y hy
      simp [β,hx,hy]
    · filter_upwards [hb.isClosed.isOpen_compl.mem_nhds hx] with y hy
      simp [β,hx,show y ∉ B from hy]
  · have he (x : Kₚ) : β x * d.character.localValue F vₚ (-x) = β x := by
      by_cases hx : x ∈ B
      · have hnorm : ‖x‖ ≤ r/2 := by simpa [B,Metric.mem_closedBall,dist_zero_right] using hx
        have hphase := hs (show -x ∈ Metric.ball 0 r by simp [Metric.mem_ball,dist_zero_right]; linarith)
        rw [show d.character.localValue F vₚ (-x) = 1 from hphase.trans (d.character.localValue_zero _),mul_one]
      · simp [β,hx]
    simp_rw [he]
    change (∫ x, B.indicator _ x ∂μ) = 1
    rw [integral_indicator hb.isClosed.measurableSet,integral_const,measureReal_restrict_apply_univ,
      Complex.real_smul,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hm)]

private theorem finite_lift_test (W : Weight vₚ) (hW : TestWeight vₚ W)
    (β : Kₚ → ℂ) (hl : IsLocallyConstant β) (hc : HasCompactSupport β) :
    d.jacquetLift vₚ W β ∈ d.testSet vₚ := by
  letI : NontriviallyNormedField (p.adicCompletion F) := FinitePlace.nontriviallyNormedCompletion p
  letI : NontriviallyNormedField Kₚ := inferInstanceAs (NontriviallyNormedField (p.adicCompletion F))
  letI : IsUltrametricDist Kₚ := inferInstanceAs (IsUltrametricDist (p.adicCompletion F))
  let f := d.jacquetLift vₚ W β
  obtain ⟨C,hC,hn,ho⟩ := d.jacquetLift_support vₚ W hW.1 β hc
  have hw : IsLocallyConstant W := hW.2
  have hx : IsLocallyConstant (fun z : Kₚˣ × Kₚ => jacquetLiftX vₚ W β z.1 z.2) := by
    have hm := (locallyConstant_norm_units («K» := Kₚ)).comp (fun r : ℝ => (r : ℂ)⁻¹)
    exact ((hm.mul hw).comp_continuous continuous_fst).mul (hl.comp_continuous
      (continuous_snd.div (Units.continuous_val.comp continuous_fst) fun z => z.1.ne_zero))
  refine ⟨d.jacquetLift_glues _ _ _,hx,?_,C,hC,fun h => hn 0 h rfl,ho⟩
  rw [IsLocallyConstant.iff_eventually_eq]
  intro z
  by_cases hz : z.1 = 0
  · have hout : (z.1,z.2.val) ∉ C := fun he => hn _ he hz
    have hnear := (continuous_fst.prodMk (Units.continuous_val.comp continuous_snd)).continuousAt.eventually
      (hC.isClosed.isOpen_compl.mem_nhds hout)
    filter_upwards [hnear] with y hy
    have van (u : Kₚ × Kₚˣ) (hu : (u.1,u.2.val) ∉ C) : f.2 u.1 u.2 = 0 := by
      simpa only [yChart,dif_pos u.2.ne_zero,Units.mk0_val] using (ho (u.1,u.2.val) hu).2
    exact (van y hy).trans (van z hout).symm
  · have hx' : ContinuousAt (fun y : Kₚ × Kₚˣ => liftUnit y.1) z :=
      (liftUnit_continuousAt hz).comp continuous_fst.continuousAt
    have hpair := (hx'.prodMk continuous_snd.continuousAt).eventually
      ((d.locallyConstant_unitPairing vₚ).eventually_eq (liftUnit z.1,z.2))
    have hval := (hx'.prodMk (Units.continuous_val.comp continuous_snd).continuousAt).eventually
      (hx.eventually_eq (liftUnit z.1,z.2.val))
    filter_upwards [continuous_fst.continuousAt.eventually (eventually_ne_nhds hz),hpair,hval] with y hy hs hv
    change f.2 y.1 y.2 = f.2 z.1 z.2
    have hs' := congrArg Units.val hs
    change d.symbol vₚ (liftUnit y.1) y.2 = d.symbol vₚ (liftUnit z.1) z.2 at hs'
    change jacquetLiftX vₚ W β (liftUnit y.1) y.2.val = jacquetLiftX vₚ W β (liftUnit z.1) z.2.val at hv
    simp only [liftUnit,dif_pos hy,dif_pos hz] at hs' hv
    simp only [f,jacquetLift,dif_pos hy,dif_pos hz,hs',hv]

theorem finite_exists_jacquetLift_auxiliary : ∃ β, d.IsJacquetLiftAuxiliary vₚ β := by
  obtain ⟨β,hl,hc,hβ⟩ := d.finite_lift_auxiliary p
  exact ⟨β,hβ,fun W hW => d.finite_lift_test p W hW β hl hc⟩

end Finite

end MetaplecticPoisson.Datum
