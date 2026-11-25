import MetaplecticSummation.RadonConvergence

/-! Rapid decay in the determinant parameter in Lemma 4.2(i), and absolute
convergence of the outer Fourier integrals in Definition 4.4. -/
noncomputable section
namespace MetaplecticPoisson
open NumberField MeasureTheory Set Metric
open Classical

private theorem rapid_of_eq_for_large {K P : Type} [NormedField K] [ProperSpace K] [TopologicalSpace P]
    {f g : P → K → ℂ} (hf : Continuous (Function.uncurry f)) (hg : RapidRadonValues g)
    {n : ℕ} (hn : n ≠ 0) (he : ∀ T : Set P, IsCompact T → ∃ B : ℝ, ∀ q ∈ T, ∀ t : K,
      B < ‖t‖^n → f q t = g q t) : RapidRadonValues f := by
  refine ⟨hf,?_⟩
  intro T hT j
  obtain ⟨B,hB⟩ := he T hT
  obtain ⟨A,hA,H⟩ := hg.2 T hT j
  let S := closedBall (0 : K) (max 1 B)
  let w (z : P × K) := ‖f z.1 z.2‖*(1+‖z.2‖)^j
  have cw : Continuous w := hf.norm.mul ((continuous_const.add continuous_snd.norm).pow j)
  obtain ⟨D,hD⟩ := (hT.prod (show IsCompact S from isCompact_closedBall _ _)).bddAbove_image cw.continuousOn
  refine ⟨max D A,hA.trans (le_max_right ..),fun q hq t => ?_⟩
  by_cases ht : t ∈ S
  · rw [← div_eq_mul_inv,le_div_iff₀ (by positivity)]
    exact (hD (mem_image_of_mem w (show (q,t) ∈ T ×ˢ S from ⟨hq,ht⟩))).trans (le_max_left ..)
  · have ht' : max 1 B < ‖t‖ := lt_of_not_ge (fun h => ht (mem_closedBall_zero_iff.mpr h))
    rw [hB q hq t (((le_max_right ..).trans_lt ht').trans_le
      (le_self_pow₀ ((le_max_left ..).trans ht'.le) hn))]
    exact (H q hq t).trans (mul_le_mul_of_nonneg_right (le_max_right ..) (by positivity))

namespace Datum
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n) (v : Place F)
local notation "K" => LocalField F v
local notation "dx" => selfDual F d.character v

private theorem rapid_radon_of_compact_change [ProperSpace K] {f g : Charts K}
    (cx : Continuous fun q : (Kˣ × K) × K => (d.radonAt v f q.2).1 q.1.1 q.1.2)
    (cy : Continuous fun q : (K × Kˣ) × K => (d.radonAt v f q.2).2 q.1.1 q.1.2)
    (hx : RapidRadonValues fun (q : Kˣ × K) t => (d.radonAt v g t).1 q.1 q.2)
    (hy : RapidRadonValues fun (q : K × Kˣ) t => (d.radonAt v g t).2 q.1 q.2)
    {C : Set (K × K)} (hc : IsCompact C) (he : ∀ z ∉ C, xChart f z = xChart g z ∧ yChart f z = yChart g z) :
    (RapidRadonValues fun (q : Kˣ × K) t => (d.radonAt v f t).1 q.1 q.2) ∧
    (RapidRadonValues fun (q : K × Kˣ) t => (d.radonAt v f t).2 q.1 q.2) := by
  constructor
  · apply rapid_of_eq_for_large cx hx (NeZero.ne n)
    intro T hT
    let i (q : Kˣ × K) := (q.1.val,q.2)
    have ci : Continuous i := (Units.continuous_val.comp continuous_fst).prodMk continuous_snd
    obtain ⟨B,hB⟩ := radon_eq_off_compact dx hc he n (d.symbol v) (modulus F v) (hT.image ci)
    exact ⟨B,fun q hq t ht => (hB t ht).1 q.1 q.2 (mem_image_of_mem i hq)⟩
  · apply rapid_of_eq_for_large cy hy (NeZero.ne n)
    intro T hT
    let i (q : K × Kˣ) := (q.1,q.2.val)
    have ci : Continuous i := continuous_fst.prodMk (Units.continuous_val.comp continuous_snd)
    obtain ⟨B,hB⟩ := radon_eq_off_compact dx hc he n (d.symbol v) (modulus F v) (hT.image ci)
    exact ⟨B,fun q hq t ht => (hB t ht).2 q.1 q.2 (mem_image_of_mem i hq)⟩

private def cutoff (r : ℝ) : ℝ := min 1 (max 0 (r-1))

private theorem rapid_cutoff_chart {L : Type} [NormedField L] (f : Lˣ → L → ℂ)
    (hc : Continuous (Function.uncurry f))
    (hf : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a b, let r := max ‖a.val‖ ‖b‖
      1 ≤ r → ‖f a b‖*r^j ≤ C) :
    RapidLineChart (fun a b => (cutoff (max ‖a.val‖ ‖b‖) : ℂ) * f a b) := by
  have cc : Continuous cutoff := continuous_const.min (continuous_const.max (continuous_id.sub continuous_const))
  refine ⟨(Complex.continuous_ofReal.comp (cc.comp ((Units.continuous_val.comp continuous_fst).norm.max
    continuous_snd.norm))).mul hc,?_⟩
  intro j
  obtain ⟨C,hC,H⟩ := hf j
  refine ⟨C*2^j,by positivity,fun a b => ?_⟩
  let r := max ‖a.val‖ ‖b‖
  change ‖(cutoff r : ℂ)*f a b‖*(1+r)^j ≤ _
  by_cases hr : 1 ≤ r
  · have hc₀ : 0 ≤ cutoff r := le_min zero_le_one (le_max_left ..)
    have hnorm : ‖(cutoff r : ℂ)*f a b‖ ≤ ‖f a b‖ := by
      rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg hc₀]
      exact mul_le_of_le_one_left (norm_nonneg _) (min_le_left ..)
    calc
      _ ≤ ‖f a b‖*(r*2)^j := mul_le_mul hnorm (pow_le_pow_left₀ (by linarith) (by linarith) j)
          (pow_nonneg (by linarith) j) (norm_nonneg _)
      _ ≤ _ := by rw [mul_pow,← mul_assoc]; exact mul_le_mul_of_nonneg_right (H a b hr) (by positivity)
  · have hz : cutoff r = 0 := by simp [cutoff,max_eq_left (sub_nonpos.mpr (le_of_not_ge hr))]
    rw [hz,Complex.ofReal_zero,zero_mul,norm_zero,zero_mul]
    positivity

omit [NeZero n] in
theorem integrable_local_inv_cube :
    Integrable (fun x : K => ((1+‖x‖)^3)⁻¹) dx := by
  cases v with
  | inl w => exact d.arch_integrable_inv_cube w
  | inr p =>
    let vp : Place F := .inr p
    let L := LocalField F vp
    let f (x : L) := ((1+‖x‖)^3)⁻¹
    apply (d.lineMeasure_modulus vp f).1.mp
    have c : Continuous fun a : Lˣ => modulus F vp a.val • f a.val :=
      Units.continuous_val.norm.smul (((continuous_const.add Units.continuous_val.norm).pow 3).inv₀
        (fun a => pow_ne_zero _ (show (1:ℝ)+‖a.val‖ ≠ 0 by positivity)))
    apply (d.finite_integrable_min_rpow p zero_lt_one).mono' c.aestronglyMeasurable
    filter_upwards with a
    let r := ‖a.val‖
    have hr : 0 < r := norm_pos_iff.mpr a.ne_zero
    change ‖r * ((1+r)^3)⁻¹‖ ≤ min (r^(1:ℝ)) (r^(-(1:ℝ)))
    rw [Real.norm_of_nonneg (by positivity),Real.rpow_one,Real.rpow_neg_one,← div_eq_mul_inv]
    refine le_min ((div_le_self hr.le) (by nlinarith [sq_nonneg r,pow_nonneg hr.le 3])) ?_
    rw [le_inv_comm₀ (div_pos hr (by positivity)) hr, inv_div,le_div_iff₀ hr]
    nlinarith [sq_nonneg r,pow_nonneg hr.le 3]

omit [NeZero n] in
private theorem chart_decay_outside {f : Charts K}
    (hg : ∀ N : ℕ, 1 ≤ N → ChartGrowth v n N f) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : K × K, 1 ≤ ‖z‖ →
      ‖xChart f z‖*‖z‖^j ≤ C ∧ ‖yChart f z‖*‖z‖^j ≤ C := by
  obtain ⟨C,hC,H⟩ := hg (j+1) (by omega)
  refine ⟨C,hC,fun z hz => ?_⟩
  have hn : z ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans_le hz)
  let R := max (modulus F v z.1) (modulus F v z.2)
  have hr' : ‖z‖ ≤ R := by
    cases v with
    | inr p => exact le_rfl
    | inl w =>
      have hr : R = ‖z‖^w.mult := by
        change max (‖z.1‖^w.mult) (‖z.2‖^w.mult) = (max ‖z.1‖ ‖z.2‖)^w.mult
        rcases le_total ‖z.1‖ ‖z.2‖ with h|h
        · rw [max_eq_right h,max_eq_right (pow_le_pow_left₀ (norm_nonneg _) h _)]
        · rw [max_eq_left h,max_eq_left (pow_le_pow_left₀ (norm_nonneg _) h _)]
      exact hr ▸ le_self_pow₀ hz w.mult_ne_zero
  have hR : 0 < R := (zero_lt_one.trans_le hz).trans_le hr'
  have bound {b : ℝ} (hb : 0 ≤ b) (h : b ≤ C*min (R^(-growthExponent n)) (R^(-((j+1 : ℕ):ℝ)))) :
      b*‖z‖^j ≤ C := by
    have h' := h.trans (mul_le_mul_of_nonneg_left (min_le_right ..) hC)
    rw [Real.rpow_neg hR.le,Real.rpow_natCast,← div_eq_mul_inv,le_div_iff₀ (pow_pos hR _)] at h'
    exact (mul_le_mul_of_nonneg_left ((pow_le_pow_left₀ (norm_nonneg _) hr' j).trans
      (pow_le_pow_right₀ (hz.trans hr') (Nat.le_succ j))) hb).trans h'
  exact ⟨bound (norm_nonneg _) (H z hn).1,bound (norm_nonneg _) (H z hn).2⟩

/-- At every place the full growth condition of Lemma 4.2 implies rapid
decay of the two Radon slices, uniformly on compact sets of chart vectors. -/
theorem radon_decay_of_growth {f : Charts K}
    (hx : Continuous (Function.uncurry f.1)) (hy : Continuous (Function.uncurry f.2))
    (hg : ∀ N : ℕ, 1 ≤ N → ChartGrowth v n N f) :
    (RapidRadonValues fun (q : Kˣ × K) t => (d.radonAt v f t).1 q.1 q.2) ∧
    (RapidRadonValues fun (q : K × Kˣ) t => (d.radonAt v f t).2 q.1 q.2) := by
  let L := LocalField F v
  letI : ProperSpace L := by
    cases v with
    | inl w =>
      letI : LocallyCompactSpace (LocalField F (.inl w)) := inferInstanceAs (LocallyCompactSpace w.Completion)
      letI := archNontriviallyNormedCompletion w
      exact .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace (LocalField F (.inl w))
    | inr p =>
      letI := FinitePlace.nontriviallyNormedCompletion p
      exact .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace (p.adicCompletion F)
  let g : Charts L := (fun a b => (cutoff (max ‖a.val‖ ‖b‖) : ℂ)*f.1 a b,
    fun a b => (cutoff (max ‖b.val‖ ‖a‖) : ℂ)*f.2 a b)
  have gx : RapidLineChart g.1 := by
    apply rapid_cutoff_chart _ hx
    intro j
    obtain ⟨C,hC,H⟩ := chart_decay_outside v hg j
    exact ⟨C,hC,fun a b hr => by simpa only [xChart,dif_pos a.ne_zero,Units.mk0_val,Prod.norm_def] using! (H (a.val,b) hr).1⟩
  have gy : RapidLineChart (fun b a => g.2 a b) := by
    apply rapid_cutoff_chart (fun b a => f.2 a b) (hy.comp (f := Prod.swap) continuous_swap)
    intro j
    obtain ⟨C,hC,H⟩ := chart_decay_outside v hg j
    refine ⟨C,hC,fun b a hr => ?_⟩
    have hr' : 1 ≤ ‖(a,b.val)‖ := by simpa only [Prod.norm_def,max_comm ‖a‖] using hr
    simpa only [yChart,dif_pos b.ne_zero,Units.mk0_val,Prod.norm_def,max_comm ‖a‖] using! (H (a,b.val) hr').2
  obtain ⟨_,_,rx,ry⟩ := d.radon_of_rapid_charts v (d.integrable_local_inv_cube v) gx gy
  obtain ⟨_,_,cx,cy⟩ := d.radon_convergence_of_growth v f hx hy (hg 2 (by decide))
  apply d.rapid_radon_of_compact_change v cx cy rx ry (isCompact_closedBall (0 : L × L) 2)
  intro z hz
  have hr : 2 < ‖z‖ := lt_of_not_ge (fun h => hz (mem_closedBall_zero_iff.mpr h))
  have hc : cutoff (max ‖z.1‖ ‖z.2‖) = 1 :=
    min_eq_left ((show 1 ≤ ‖z‖-1 by linarith).trans (le_max_right ..))
  simp only [xChart,yChart,g,Units.val_mk0,max_comm ‖z.2‖ ‖z.1‖,hc,Complex.ofReal_one,one_mul,and_self]

/-- Lemma 4.2(i) for every local Schwartz section at every number-field place. -/
theorem schwartz_radon_rapid (Φ : d.schwartz v) :
    (RapidRadonValues fun (q : Kˣ × K) t => (d.radonAt v Φ.val t).1 q.1 q.2) ∧
    (RapidRadonValues fun (q : K × Kˣ) t => (d.radonAt v Φ.val t).2 q.1 q.2) := by
  obtain ⟨hx,hy⟩ := d.continuous_schwartz_charts v Φ
  exact d.radon_decay_of_growth v hx hy (d.schwartz_chart_growth v Φ)

/-- Both outer Fourier integrals converge absolutely on the entire local Schwartz space. -/
theorem schwartz_transform_integrable (Φ : d.schwartz v) : d.TransformIntegrable v Φ.val := by
  obtain ⟨hx,hy⟩ := d.schwartz_radon_rapid v Φ
  have phase {g : K → ℂ} (h : Integrable g dx) : Integrable (fun t => d.character.localValue F v t*g t) dx :=
    h.norm.mono' ((d.character.continuous_localValue v).aestronglyMeasurable.mul h.aestronglyMeasurable)
      (.of_forall fun t => by rw [norm_mul,d.character.norm_localValue,one_mul])
  exact ⟨fun a b => phase (hx.integrable dx (d.integrable_local_inv_cube v) (a,b)),
    fun a b => phase (hy.integrable dx (d.integrable_local_inv_cube v) (a,b))⟩

/-- The two explicit integrals define a linear map on the whole Schwartz space,
with values in pairs of chart functions. -/
def schwartzTransformToCharts : d.schwartz v →ₗ[ℂ] Charts K where
  toFun Φ := d.integralTransform v Φ.val
  map_add' Φ Ψ := by
    obtain ⟨fx,fy,_⟩ := d.schwartz_radon_convergence v Φ
    obtain ⟨gx,gy,_⟩ := d.schwartz_radon_convergence v Ψ
    exact (d.transform_add_of_radon_add v (d.schwartz_transform_integrable v Φ) (d.schwartz_transform_integrable v Ψ)
      (.of_forall fun t => d.radonAt_add_of_integrable v t (fx t) (fy t) (gx t) (gy t))).2
  map_smul' c Φ := d.integralTransform_smul v c Φ.val

/-- With convergence and linearity established, stability of the local
Schwartz space is equivalent to membership of the second transforms of tests. -/
theorem fourier_stability_iff_square_on_tests :
    (∃ L : d.schwartz v →ₗ[ℂ] d.schwartz v, ∀ Φ, (L Φ).val = d.integralTransform v Φ.val) ↔
      ∀ f ∈ d.testSet v, d.integralTransform v (d.integralTransform v f) ∈ d.schwartz v := by
  constructor
  · rintro ⟨L,hL⟩ f hf
    let Φ : d.schwartz v := ⟨d.integralTransform v f,Submodule.subset_span (Or.inr ⟨f,hf,rfl⟩)⟩
    exact hL Φ ▸ (L Φ).property
  · intro hs
    let T := d.schwartzTransformToCharts v
    have h : ⊤ ≤ (d.schwartz v).comap T := by
      rw [← show Submodule.span ℂ ((Subtype.val : d.schwartz v → _) ⁻¹'
        (d.testSet v ∪ d.integralTransform v '' d.testSet v)) = ⊤ from Submodule.span_span_coe_preimage,
        Submodule.span_le]
      rintro ⟨f,hf⟩ (ht | ⟨g,hg,rfl⟩)
      · exact Submodule.subset_span (Or.inr ⟨f,ht,rfl⟩)
      · exact hs g hg
    exact ⟨T.codRestrict _ (fun _ => h Submodule.mem_top),fun _ => rfl⟩

end Datum
end MetaplecticPoisson
