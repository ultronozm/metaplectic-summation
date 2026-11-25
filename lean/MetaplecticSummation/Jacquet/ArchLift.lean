import MetaplecticSummation.Jacquet.Lift
import MetaplecticSummation.RapidCharts
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! Smooth compact Jacquet lifts at real and complex places. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField MeasureTheory Filter Set
open scoped Topology ContDiff
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n) (w : InfinitePlace F)
local notation "vᵥ" => (Sum.inl w : Place F)
local notation "Kᵥ" => LocalField F vᵥ
local notation "dxᵥ" => selfDual F d.character vᵥ
local notation "ψᵥ" => d.character.localValue F vᵥ

private theorem rapidChart_of_compact {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℂ} {C : Set E} (hf : ContDiff ℝ ∞ f) (hc : IsCompact C)
    (hz : (0:E) ∉ C) (ho : ∀ x ∉ C, f x = 0) : rapidChart univ f := by
  refine ⟨hf.contDiffOn,fun k N => ?_⟩
  let m (x : E) := min (‖x‖^N) (‖x‖^N)⁻¹
  have hm {x : E} (hx : x ∈ C) : 0 < m x := by
    have hn : x ≠ 0 := fun he => hz (he ▸ hx)
    exact lt_min (pow_pos (norm_pos_iff.mpr hn) _) (inv_pos.mpr (pow_pos (norm_pos_iff.mpr hn) _))
  have hcont : ContinuousOn m C := (continuous_norm.pow N).continuousOn.inf
    ((continuous_norm.pow N).continuousOn.inv₀ (fun x hx => pow_ne_zero _ (norm_ne_zero_iff.mpr (fun he => hz (he ▸ hx)))))
  obtain ⟨B,hB⟩ := hc.exists_bound_of_continuousOn
    ((hf.continuous_iteratedFDeriv (by exact_mod_cast le_top : (k : WithTop ℕ∞) ≤ ∞)).norm.continuousOn.div
      hcont (fun x hx => (hm hx).ne'))
  refine ⟨max B 0,fun x _ => ?_⟩
  by_cases hx : x ∈ C
  · apply (div_le_iff₀ (hm hx)).mp
    exact (le_abs_self _).trans ((hB x hx).trans (le_max_left ..))
  · have he : f =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [hc.isClosed.isOpen_compl.mem_nhds hx] with z hz using ho z hz
    rw [(he.iteratedFDeriv ℝ k).self_of_nhds]
    simp only [iteratedFDeriv_fun_zero,Pi.zero_apply,norm_zero]
    exact mul_nonneg (le_max_right ..) (le_min (pow_nonneg (norm_nonneg _) _) (inv_nonneg.mpr (pow_nonneg (norm_nonneg _) _)))

section Arch
variable {L : Type} [NormedField L] [NormedAlgebra ℝ L] [FiniteDimensional ℝ L]
    [MeasurableSpace L] [BorelSpace L]
    (e : w.Completion ≃+* L) (he : Isometry e)

include he
omit [NeZero n] in
private theorem arch_lift_auxiliary :
    ∃ β : L → ℂ, ContDiff ℝ ∞ β ∧ HasCompactSupport β ∧
      (∫ x : Kᵥ, β (e x) * ψᵥ (-x) ∂dxᵥ) = 1 := by
  letI : (dxᵥ).IsAddHaarMeasure := (existsUnique_selfDual F d.character vᵥ).exists.choose_spec.1
  let i : Kᵥ ≃ᵢ L := ⟨e.toEquiv,he⟩
  let ν := (dxᵥ).map i
  letI : ν.IsAddHaarMeasure := e.toAddEquiv.isAddHaarMeasure_map dxᵥ he.continuous i.symm.continuous
  let f (x : L) := ψᵥ (-(i.symm x))
  have hf : Continuous f := (d.character.continuous_localValue vᵥ).comp i.symm.continuous.neg
  have ex : ∃ φ : L → ℝ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
      (∫ x, (φ (e x) : ℂ) * ψᵥ (-x) ∂dxᵥ) ≠ 0 := by
    by_contra! hall
    have eqn : f = 0 := by
      apply (hf.ae_eq_iff_eq (μ := ν) continuous_zero).mp
      apply ae_eq_of_integral_contDiff_smul_eq hf.locallyIntegrable continuous_zero.locallyIntegrable
      intro φ hd hc
      simp only [Pi.zero_apply,smul_zero,integral_zero]
      rw [show ν = (dxᵥ).map i.toHomeomorph.toMeasurableEquiv from rfl,integral_map_equiv]
      change (∫ x : Kᵥ, φ (i x) • f (i x) ∂dxᵥ) = 0
      simp only [f,i.symm_apply_apply,Complex.real_smul]
      exact hall φ hd hc
    have h := congrFun eqn (i 0)
    exact one_ne_zero (by simpa only [f,i.symm_apply_apply,neg_zero,d.character.localValue_zero,Pi.zero_apply] using h : (1:ℂ) = 0)
  obtain ⟨φ,hd,hc,hz⟩ := ex
  let a := ∫ x, (φ (e x) : ℂ) * ψᵥ (-x) ∂dxᵥ
  let φc (x : L) : ℂ := φ x
  have hs : ContDiff ℝ ∞ φc := Complex.ofRealCLM.contDiff.comp hd
  have hsc : HasCompactSupport φc := hc.comp_left Complex.ofReal_zero
  refine ⟨fun x => a⁻¹*φc x,contDiff_const.mul hs,hsc.mul_left,?_⟩
  simp only [mul_assoc,integral_const_mul]
  exact inv_mul_cancel₀ hz

omit [FiniteDimensional ℝ L] [MeasurableSpace L] [BorelSpace L] in
private theorem arch_lift_test (hnorm : ∀ x : L, x ≠ 0 → ContDiffAt ℝ ∞ norm x) (W : Weight vᵥ) (hcW : HasCompactSupport W)
    (hW : archSmooth e W) (β : L → ℂ) (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β) :
    archTest e (d.jacquetLift vᵥ W (fun u => β (e u))) := by
  let i : Kᵥ ≃ᵢ L := ⟨e.toEquiv,he⟩
  let f := d.jacquetLift vᵥ W (fun u => β (e u))
  let P (z : L × L) : Kᵥ × Kᵥ := (e.symm z.1,e.symm z.2)
  let Q (z : Kᵥ × Kᵥ) : L × L := (e z.1,e z.2)
  let X (z : L × L) := xChart f (P z)
  let Y (z : L × L) := yChart f (P z)
  obtain ⟨C,hC,hfirst,hvan⟩ := d.jacquetLift_support vᵥ W hcW _ (hcβ.comp_homeomorph i.toHomeomorph)
  let D := Q '' C
  have hD : IsCompact D := hC.image ((he.continuous.comp continuous_fst).prodMk (he.continuous.comp continuous_snd))
  have hne (z : L × L) (hz : z ∈ D) : z.1 ≠ 0 := by
    obtain ⟨s,hs,rfl⟩ := hz
    exact fun h => hfirst _ hs (e.map_eq_zero_iff.mp h)
  have ho (z : L × L) (hz : z ∉ D) : X z = 0 ∧ Y z = 0 := by
    apply hvan (P z)
    intro h
    exact hz ⟨P z,h,by simp [Q,P]⟩
  let W₀ (x : L) : ℂ := if hx : e.symm x ≠ 0 then W (Units.mk0 _ hx) else 0
  have hcoord (z : L × L) (hz : z.1 ≠ 0) : X z =
      ((‖z.1‖^w.mult : ℝ) : ℂ)⁻¹ * W₀ z.1 * β (z.2/z.1) := by
    have ha := (map_ne_zero e.symm).mpr hz
    have hnorm : ‖e.symm z.1‖ = ‖z.1‖ := by simpa using (he.norm_map_of_map_zero (map_zero e) (e.symm z.1)).symm
    change (if h : e.symm z.1 ≠ 0 then jacquetLiftX vᵥ W (fun u => β (e u)) (Units.mk0 _ h) (e.symm z.2) else 0) = _
    rw [dif_pos ha]
    change ((‖e.symm z.1‖^w.mult : ℝ) : ℂ)⁻¹ * W _ * β (e (e.symm z.2 / e.symm z.1)) = _
    simp only [hnorm,map_div₀,e.apply_symm_apply,W₀,dif_pos ha]
  have hX : ContDiff ℝ ∞ X := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z.1 = 0
    · have hn : z ∉ D := fun h => hne _ h hz
      apply (contDiffAt_const (c := (0:ℂ))).congr_of_eventuallyEq
      filter_upwards [hD.isClosed.isOpen_compl.mem_nhds hn] with t ht using (ho _ ht).1
    · have hw : ContDiffAt ℝ ∞ W₀ z.1 := (hW z.1 hz).contDiffAt (isOpen_compl_singleton.mem_nhds hz)
      have hn := (hnorm z.1 hz).comp z (contDiff_fst.contDiffAt : ContDiffAt ℝ ∞ (Prod.fst : L × L → L) z)
      have hm := Complex.ofRealCLM.contDiff.contDiffAt.comp z (hn.pow w.mult)
      have hdiv : ContDiffAt ℝ ∞ (fun t : L × L => t.2 / t.1) z := by
        simpa only [div_eq_mul_inv] using (contDiff_snd.contDiffAt.mul (contDiff_fst.contDiffAt.inv hz) : ContDiffAt ℝ ∞ (fun t : L × L => t.2 * t.1⁻¹) z)
      apply (((hm.inv (Complex.ofReal_ne_zero.mpr (pow_ne_zero _ (norm_ne_zero_iff.mpr hz)))).mul
        (hw.comp z contDiff_fst.contDiffAt)).mul (hβ.contDiffAt.comp z hdiv)).congr_of_eventuallyEq
      filter_upwards [continuous_fst.continuousAt.eventually (eventually_ne_nhds hz)] with t ht using hcoord t ht
  have rapid := rapidChart_of_compact hX hD (fun h => hne 0 h rfl) (fun x hx => (ho x hx).1)
  refine ⟨⟨hX.contDiffOn,fun k N => ?_⟩,?_⟩
  · obtain ⟨M,hm⟩ := rapid.2 k N
    exact ⟨M,fun x _ => hm x trivial⟩
  · change rapidChart {z : L × L | z.2 ≠ 0} Y
    apply rapidChart_of_local_branches isOpen_univ isOpen_univ rapid rapid
    intro z hz
    left
    refine ⟨trivial,?_⟩
    by_cases hx : z.1 = 0
    · refine ⟨1,norm_one,?_⟩
      have hn : z ∉ D := fun h => hne _ h hx
      filter_upwards [hD.isClosed.isOpen_compl.mem_nhds hn] with y hy
      simp only [Pi.smul_apply,smul_eq_mul,one_mul,(ho y hy).1,(ho y hy).2]
    · let u (x : L) : Kᵥˣ := if h : e.symm x ≠ 0 then Units.mk0 _ h else 1
      have hu {x : L} (h : x ≠ 0) : ContinuousAt u x := by
        apply Units.isEmbedding_val₀.tendsto_nhds_iff.mpr
        have h' := (map_ne_zero e.symm).mpr h
        change Tendsto (fun t => (u t).val) (𝓝 x) (𝓝 (u x).val)
        rw [show (u x).val = e.symm x from by simp only [u,dif_pos h']; rfl]
        apply (i.symm.continuous.tendsto x).congr'
        filter_upwards [eventually_ne_nhds h] with t ht
        change e.symm t = (u t).val
        simp only [u,dif_pos ((map_ne_zero e.symm).mpr ht)]
        rfl
      have hs := ((hu hx).comp continuous_fst.continuousAt |>.prodMk
        ((hu hz).comp continuous_snd.continuousAt)).eventually
        ((d.locallyConstant_unitPairing vᵥ).eventually_eq (u z.1,u z.2))
      refine ⟨(d.symbol vᵥ (u z.1) (u z.2))⁻¹,by rw [norm_inv,d.norm_symbol,inv_one],?_⟩
      filter_upwards [hs,continuous_fst.continuousAt.eventually (eventually_ne_nhds hx),
        continuous_snd.continuousAt.eventually (eventually_ne_nhds hz)] with t ht ha hb
      have heq := congrArg Units.val ht
      change d.symbol vᵥ (u t.1) (u t.2) = d.symbol vᵥ (u z.1) (u z.2) at heq
      rw [← heq]
      have hta : (e.symm t.1 : Kᵥ) ≠ 0 := (map_ne_zero e.symm).mpr ha
      have htb : (e.symm t.2 : Kᵥ) ≠ 0 := (map_ne_zero e.symm).mpr hb
      change (if h : e.symm t.2 ≠ 0 then f.2 (e.symm t.1) (Units.mk0 _ h) else 0) =
        (d.symbol vᵥ (u t.1) (u t.2))⁻¹ *
          (if h : e.symm t.1 ≠ 0 then f.1 (Units.mk0 _ h) (e.symm t.2) else 0)
      rw [dif_pos htb,dif_pos hta]
      change (if h : e.symm t.1 ≠ 0 then _ else 0) = _
      rw [dif_pos hta]
      simp only [u,dif_pos hta,dif_pos htb,f,jacquetLift]
      rfl

end Arch

theorem arch_exists_jacquetLift_auxiliary : ∃ β, d.IsJacquetLiftAuxiliary vᵥ β := by
  by_cases hw : w.IsReal
  · let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
    have he : Isometry e := InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw
    obtain ⟨β,hd,hc,hβ⟩ := d.arch_lift_auxiliary w e he
    refine ⟨fun x => β (e x),hβ,?_⟩
    intro W hW
    refine ⟨d.jacquetLift_glues _ _ _,?_⟩
    simp only [dif_pos hw]
    apply d.arch_lift_test w e he (fun _ hx => contDiffAt_id.norm ℝ hx) W hW.1 _ β hd hc
    simpa only [dif_pos hw] using hW.2
  · let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex (InfinitePlace.not_isReal_iff_isComplex.mp hw)
    have he : Isometry e := InfinitePlace.Completion.isometry_extensionEmbedding w
    obtain ⟨β,hd,hc,hβ⟩ := d.arch_lift_auxiliary w e he
    refine ⟨fun x => β (e x),hβ,?_⟩
    intro W hW
    refine ⟨d.jacquetLift_glues _ _ _,?_⟩
    simp only [dif_neg hw]
    apply d.arch_lift_test w e he (fun _ hx => contDiffAt_id.norm ℝ hx) W hW.1 _ β hd hc
    simpa only [dif_neg hw] using hW.2

end MetaplecticPoisson.Datum
