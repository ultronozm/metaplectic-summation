import MetaplecticSummation.Marginals.TestedRadon

/-! Joint absolute convergence in the finite-place reverse marginal identity. -/

noncomputable section
namespace MetaplecticPoisson
open NumberField IsDedekindDomain MeasureTheory Set Filter
open scoped Topology
open Classical

/-- Local constancy of the Y chart at the vertical axis is uniform in the
nonzero vertical coordinate. Near the deleted origin both values vanish. -/
theorem finiteTest_uniform_axis {K : Type} [NormedField K] {f : Charts K} (hf : finiteTest f) :
    ∃ r > (0 : ℝ), ∀ x : K, ‖x‖ < r → ∀ y : Kˣ, f.2 x y = f.2 0 y := by
  obtain ⟨_,hl,C,hC,h0,ho⟩ := hf
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp (hC.isClosed.isOpen_compl.mem_nhds h0)
  let Y := (Prod.snd '' C) \ Metric.ball (0 : K) δ
  have hY : IsCompact Y := (hC.image continuous_snd).diff Metric.isOpen_ball
  let V := (Units.val : Kˣ → K) ⁻¹' Y
  have hV : IsCompact V := Units.isEmbedding_val₀.isInducing.isCompact_preimage' hY (by
    intro y hy
    exact ⟨Units.mk0 y (fun h => hy.2 (h ▸ Metric.mem_ball_self hδ)),rfl⟩)
  let E : Set (K × Kˣ) := {z | f.2 z.1 z.2 = f.2 0 z.2}
  have he : IsOpen E := (hl.prodMk (hl.comp_continuous (continuous_const.prodMk continuous_snd))) {z | z.1 = z.2}
  obtain ⟨A,B,hA,_,hA₀,hBV,hsub⟩ := generalized_tube_lemma (isCompact_singleton (x := (0 : K))) hV he
    (by rintro ⟨x,y⟩ ⟨rfl : x = 0,_⟩; rfl)
  obtain ⟨r,hr,hrA⟩ := Metric.mem_nhds_iff.mp (hA.mem_nhds (hA₀ rfl))
  refine ⟨min r δ,lt_min hr hδ,fun x hx y => ?_⟩
  by_cases hy : y ∈ V
  · exact hsub (show (x,y) ∈ A ×ˢ B from ⟨hrA (mem_ball_zero_iff.mpr (lt_min_iff.mp hx).1),hBV hy⟩)
  have vanish (w : K) (hw : ‖w‖ < δ) : f.2 w y = 0 := by
    have hwy : (w,y.val) ∉ C := by
      intro hin
      have hyδ : y.val ∈ Metric.ball 0 δ := by
        by_contra hyδ
        exact hy ⟨⟨_,hin,rfl⟩,hyδ⟩
      apply hball _ hin
      rw [mem_ball_zero_iff,Prod.norm_def,max_lt_iff]
      exact ⟨hw,mem_ball_zero_iff.mp hyδ⟩
    simpa only [yChart,dif_pos y.ne_zero,Units.mk0_val] using (ho _ hwy).2
  rw [vanish x (lt_min_iff.mp hx).2,vanish 0 (by simpa using hδ)]

namespace Datum
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

/-- The subtracted three-variable integrand, extended by zero across y = 0. -/
def chartDifference (v : Place F) (f : Charts (LocalField F v)) (s u : (LocalField F v)ˣ)
    (t y : LocalField F v) : ℂ :=
  if hy : y ≠ 0 then d.symbol v u (-(s*Units.mk0 y hy)) *
    (f.2 ((t^n+s.val*y)*u.val) (Units.mk0 y hy) - f.2 u.val (Units.mk0 y hy)) else 0

private theorem small_chartDifference (p : HeightOneSpectrum (𝓞 F)) {f : Charts (LocalField F (.inr p))}
    (hf : f ∈ d.testSet (.inr p)) (s : (LocalField F (.inr p))ˣ) {h : LocalField F (.inr p) → ℂ}
    (hk : HasCompactSupport h) : ∃ ε > (0 : ℝ), ∀ u : (LocalField F (.inr p))ˣ, ‖u.val‖ < ε →
      ∀ t y, h t * d.chartDifference (.inr p) f s u t y = 0 := by
  let K := LocalField F (.inr p)
  obtain ⟨r,hr,hflat⟩ := finiteTest_uniform_axis hf.2
  obtain ⟨C,hC,_,ho⟩ := (show finiteTest f from hf.2).2.2
  obtain ⟨B,hB⟩ := (hk.prod (hC.image continuous_snd)).exists_bound_of_continuousOn
    (f := fun z : K × K => z.1^n+s.val*z.2) (((continuous_fst.pow n).add (continuous_const.mul continuous_snd)).continuousOn)
  let M := max 1 B
  have hM : 0 < M := zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨r/M,div_pos hr hM,fun u hu t y => ?_⟩
  by_cases ht : h t = 0
  · rw [ht,zero_mul]
  by_cases hy : y = 0
  · simp [chartDifference,hy]
  rw [chartDifference,dif_pos hy]
  by_cases hY : y ∈ Prod.snd '' C
  · have hty := hB (t,y) ⟨subset_tsupport h ht,hY⟩
    have huM : M*‖u.val‖ < r := by simpa [mul_comm] using (lt_div_iff₀ hM).mp hu
    have h₁ := (le_mul_of_one_le_left (norm_nonneg u.val) (le_max_left _ _ : 1 ≤ M)).trans_lt huM
    have h₂ : ‖(t^n+s.val*y)*u.val‖ < r := by
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (hty.trans (le_max_right _ _)) (norm_nonneg _)).trans_lt huM
    rw [hflat _ h₂,hflat _ h₁,sub_self,mul_zero,mul_zero]
  · have hvan (x : K) : f.2 x (Units.mk0 y hy) = 0 := by
      simpa [yChart,hy] using (ho (x,y) (fun hp => hY ⟨_,hp,rfl⟩)).2
    simp [hvan]

/-- The term subtracted in the scaling variable is independent of frequency. -/
def axisSubtraction (v : Place F) (f : Charts (LocalField F v)) (s u : (LocalField F v)ˣ)
    (y : LocalField F v) : ℂ :=
  if hy : y ≠ 0 then d.symbol v u (-(s*Units.mk0 y hy)) * f.2 u.val (Units.mk0 y hy) else 0

theorem chartDifference_eq (v : Place F) (f : Charts (LocalField F v)) (s u : (LocalField F v)ˣ)
    (t y : LocalField F v) : d.chartDifference v f s u t y =
      d.marginalSlice v f s u t y - d.axisSubtraction v f s u y := by
  by_cases hy : y = 0 <;> simp [hy,chartDifference,marginalSlice,axisSubtraction,mul_sub]

theorem chartTerm_measurable {Z : Type*} [MeasurableSpace Z] (v : Place F) [SecondCountableTopology (LocalField F v)]
    {f : Charts (LocalField F v)} (hf : Continuous (fun z : LocalField F v × (LocalField F v)ˣ => f.2 z.1 z.2))
    (s : (LocalField F v)ˣ) {u : Z → (LocalField F v)ˣ} {x y : Z → LocalField F v}
    (hu : Measurable u) (hx : Measurable x) (hy : Measurable y) :
    Measurable (fun z => if h : y z ≠ 0 then d.symbol v (u z) (-(s*Units.mk0 (y z) h)) *
      f.2 (x z) (Units.mk0 (y z) h) else 0) := by
  let K := LocalField F v
  letI : SecondCountableTopology Kˣ := Units.isEmbedding_val₀.secondCountableTopology
  let U (a : K) := if ha : a ≠ 0 then Units.mk0 a ha else 1
  have hU : Measurable U := by
    apply measurable_comap_iff.mpr
    have he : (Units.val ∘ U) = fun a => if a ≠ 0 then a else 1 := by
      funext a
      by_cases h : a = 0 <;> simp [Function.comp,U,h]
    rw [he]
    exact Measurable.ite (measurableSet_singleton (0 : K)).compl measurable_id measurable_const
  have hm := hU.comp hy
  let A (z : Z) := d.symbol v (u z) (-(s*U (y z))) * f.2 (x z) (U (y z))
  have hneg : Continuous (fun b : Kˣ => -(s*b)) := by
    apply Units.isEmbedding_val₀.continuous_iff.mpr
    change Continuous (fun b : Kˣ => -(s.val*b.val))
    fun_prop
  have hA : Measurable A := ((d.continuous_symbol v).measurable.comp
    (hu.prodMk (hneg.measurable.comp hm))).mul (hf.measurable.comp (hx.prodMk hm))
  have eqn (z : Z) : (if h : y z ≠ 0 then d.symbol v (u z) (-(s*Units.mk0 (y z) h)) *
      f.2 (x z) (Units.mk0 (y z) h) else 0) = (if y z ∈ ({0} : Set K)ᶜ then A z else 0) := by
    by_cases h : y z = 0 <;> simp [A,U,h]
  simp_rw [eqn]
  exact hA.ite (hy (measurableSet_singleton 0).compl) measurable_const

private instance finiteProper (p : HeightOneSpectrum (𝓞 F)) : ProperSpace (LocalField F (.inr p)) := by
  letI : NontriviallyNormedField (p.adicCompletion F) := FinitePlace.nontriviallyNormedCompletion p
  exact .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace (p.adicCompletion F)

private theorem finite_chart_bounds (p : HeightOneSpectrum (𝓞 F)) {f : Charts (LocalField F (.inr p))}
    (hf : f ∈ d.testSet (.inr p)) :
    let K := LocalField F (.inr p)
    ∃ (B R : ℝ) (χ : K → ℝ), 0 ≤ B ∧ 0 < R ∧ Continuous χ ∧ HasCompactSupport χ ∧ (∀ z, 0 ≤ χ z) ∧
      (∀ x (y : Kˣ), ‖f.2 x y‖ ≤ B * χ x) ∧
      (∀ (u y : Kˣ), ‖f.2 u.val y‖ ≤ (B*R*‖u.val‖⁻¹) * χ y.val) := by
  let K := LocalField F (.inr p)
  obtain ⟨C,hC,_,ho⟩ := (show finiteTest f from hf.2).2.2
  obtain ⟨A,hA⟩ := hC.exists_bound_of_continuousOn (f := id) continuous_id.continuousOn
  let R := max 1 A
  let S := Metric.closedBall (0 : K) R
  let χ := S.indicator (fun _ => (1 : ℝ))
  have hR : 0 < R := zero_lt_one.trans_le (le_max_left _ _)
  have hcl : IsClopen S := IsUltrametricDist.isClopen_closedBall (0 : p.adicCompletion F) hR.ne'
  obtain ⟨B,hB⟩ := finiteTest_chartNorm_bounded (d.norm_symbol (.inr p)) hf.1 hf.2
  have hb (x : K) (y : Kˣ) : ‖f.2 x y‖ ≤ B := (chartNorm_eq_y (d.norm_symbol _) hf.1 x y) ▸ hB (x,y.val)
  have hB₀ := (norm_nonneg _).trans (hb 0 1)
  have χpos (x : K) : 0 ≤ χ x := indicator_nonneg (fun _ _ => zero_le_one) _
  refine ⟨B,R,χ,hB₀,hR,hcl.continuous_indicator continuous_const,
    HasCompactSupport.intro (isCompact_closedBall (0 : K) R) (fun _ hx => indicator_of_notMem hx _),χpos,?_,?_⟩
  · intro x y
    by_cases hxy : (x,y.val) ∈ C
    · have hS : x ∈ S := mem_closedBall_zero_iff.mpr
        ((le_max_left _ _).trans ((hA _ hxy).trans (le_max_right _ _)))
      simpa [χ,hS] using hb x y
    · have hz := (ho _ hxy).2
      simp only [yChart,dif_pos y.ne_zero,Units.mk0_val] at hz
      rw [hz,norm_zero]
      exact mul_nonneg hB₀ (χpos _)
  · intro u y
    by_cases hxy : (u.val,y.val) ∈ C
    · have hle : max ‖u.val‖ ‖y.val‖ ≤ R := (hA _ hxy).trans (le_max_right _ _)
      have hS : y.val ∈ S := mem_closedBall_zero_iff.mpr ((le_max_right _ _).trans hle)
      rw [show χ y.val = 1 from indicator_of_mem hS _,mul_one,← div_eq_mul_inv,le_div_iff₀ (norm_pos_iff.mpr u.ne_zero)]
      exact mul_le_mul (hb _ _) ((le_max_left _ _).trans hle) (norm_nonneg _) hB₀
    · have hz := (ho _ hxy).2
      simp only [yChart,dif_pos y.ne_zero,Units.mk0_val] at hz
      rw [hz,norm_zero]
      exact mul_nonneg (mul_nonneg (mul_nonneg hB₀ hR.le) (inv_nonneg.mpr (norm_nonneg _))) (χpos _)

private theorem chartSection_bound (p : HeightOneSpectrum (𝓞 F)) {f : Charts (LocalField F (.inr p))}
    (hf : f ∈ d.testSet (.inr p)) (s : (LocalField F (.inr p))ˣ) :
    let v : Place F := .inr p
    let dx := selfDual F d.character v
    ∃ A : ℝ, ∀ (u : (LocalField F v)ˣ) (t : LocalField F v),
      Integrable (d.marginalSlice v f s u t) dx ∧ Integrable (d.axisSubtraction v f s u) dx ∧
      (∫ y, ‖d.chartDifference v f s u t y‖ ∂dx) ≤ A * ‖u.val‖⁻¹ := by
  let v : Place F := .inr p
  let K := LocalField F v
  let dx := selfDual F d.character v
  letI : dx.IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  obtain ⟨B,R,χ,hB,hR,hc,hk,hχ,hfirst,hsecond⟩ := d.finite_chart_bounds p hf
  let V := ∫ y, χ y ∂dx
  refine ⟨B*V/‖s.val‖ + (B*R)*V,fun u t => ?_⟩
  let q (y : K) := (t^n+s.val*y)*u.val
  let w := s*u
  let b := t^n*u.val
  have he (y : K) : q y = w.val*y + b := by simp only [q,w,b,Units.val_mul]; ring
  let e := (Homeomorph.mulLeft₀ w.val w.ne_zero).trans (Homeomorph.addRight b)
  have hq : q = e := funext he
  have hI : Integrable (fun y => χ (q y)) dx := by
    rw [hq]
    exact (hc.comp e.continuous).integrable_of_hasCompactSupport (hk.comp_homeomorph e)
  have hV : (∫ y, χ (q y) ∂dx) = V / ‖s.val‖ / ‖u.val‖ := by
    have h := d.integral_local_mul v w (fun z => ((χ (z+b) : ℝ) : ℂ))
    simp only [integral_complex_ofReal,integral_add_right_eq_self] at h
    apply Complex.ofReal_injective
    simp_rw [he]
    rw [h,div_div]
    simp [V,dx,v,modulus,w,norm_mul]
  let g := d.marginalSlice v f s u t
  let k := d.axisSubtraction v f s u
  have fc := (show finiteTest f from hf.2).2.1.continuous
  have gm : Measurable g := d.chartTerm_measurable v fc s measurable_const
    ((measurable_const.add (measurable_const.mul measurable_id)).mul measurable_const) measurable_id
  have km : Measurable k := d.chartTerm_measurable v fc s measurable_const measurable_const measurable_id
  have eg (y : K) : ‖g y‖ ≤ B * χ (q y) := by
    by_cases hy : y = 0
    · rw [show g y = 0 by simp [g,marginalSlice,hy],norm_zero]
      exact mul_nonneg (by assumption) (hχ _)
    · simpa only [g,marginalSlice,dif_pos hy,norm_mul,d.norm_symbol,one_mul,q] using hfirst (q y) (Units.mk0 y hy)
  have ek (y : K) : ‖k y‖ ≤ (B*R*‖u.val‖⁻¹) * χ y := by
    by_cases hy : y = 0
    · rw [show k y = 0 by simp [k,axisSubtraction,hy],norm_zero]
      apply mul_nonneg _ (hχ _)
      positivity
    · simpa only [k,axisSubtraction,dif_pos hy,norm_mul,d.norm_symbol,one_mul,Units.val_mk0] using hsecond u (Units.mk0 y hy)
  have hχi := hc.integrable_of_hasCompactSupport (μ := dx) hk
  have gi := (hI.const_mul B).mono' gm.aestronglyMeasurable (Eventually.of_forall eg)
  have ki := (hχi.const_mul (B*R*‖u.val‖⁻¹)).mono' km.aestronglyMeasurable (Eventually.of_forall ek)
  refine ⟨gi,ki,?_⟩
  simp_rw [d.chartDifference_eq]
  refine (integral_mono (gi.sub ki).norm ((hI.const_mul B).add (hχi.const_mul _))
    (fun y => (norm_sub_le _ _).trans (add_le_add (eg y) (ek y)))).trans ?_
  simp only [Pi.add_apply]
  rw [integral_add (hI.const_mul B) (hχi.const_mul _),integral_const_mul,integral_const_mul,hV]
  change B*(V/‖s.val‖/‖u.val‖) + _*V ≤ _
  simp only [div_eq_mul_inv]
  exact le_of_eq (by ring)

/-- Joint absolute convergence of the subtracted integral in the scaling
variable u, frequency t, and chart variable y at every finite place. -/
theorem finite_joint_difference_integrable (p : HeightOneSpectrum (𝓞 F)) {f : Charts (LocalField F (.inr p))}
    (hf : f ∈ d.testSet (.inr p)) (s : (LocalField F (.inr p))ˣ) {h : LocalField F (.inr p) → ℂ}
    (hh : Bruhat (.inr p) h) :
    let v : Place F := .inr p
    let dx := selfDual F d.character v
    Integrable (fun z : ((LocalField F v)ˣ × LocalField F v) × LocalField F v =>
      h z.1.2 * d.chartDifference v f s z.1.1 z.1.2 z.2) (((d.lineMeasure v).prod dx).prod dx) := by
  let v : Place F := .inr p
  let K := LocalField F v
  let dx := selfDual F d.character v
  let ν := d.lineMeasure v
  letI : dx.IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  let D (z : Kˣ × K) (y : K) := h z.2 * d.chartDifference v f s z.1 z.2 y
  let Z := (Kˣ × K) × K
  have fc := (show finiteTest f from hf.2).2.1.continuous
  have hm : Measurable (Function.uncurry D) := by
    have hu : Measurable (fun z : Z => z.1.1) := measurable_fst.comp measurable_fst
    have ht : Measurable (fun z : Z => z.1.2) := measurable_snd.comp measurable_fst
    have huv := Units.continuous_val.measurable.comp hu
    simp only [D,d.chartDifference_eq]
    exact (hh.1.continuous.measurable.comp ht).mul ((d.chartTerm_measurable v fc s hu
      (((ht.pow_const n).add (measurable_const.mul measurable_snd)).mul huv) measurable_snd).sub
      (d.chartTerm_measurable v fc s hu huv measurable_snd))
  obtain ⟨A,hA⟩ := d.chartSection_bound p hf s
  obtain ⟨ε,hε,hsmall⟩ := d.small_chartDifference p hf s hh.2
  change Integrable (Function.uncurry D) ((ν.prod dx).prod dx)
  refine (integrable_prod_iff hm.aestronglyMeasurable).2 ⟨?_,?_⟩
  · filter_upwards with z
    simp only [Function.uncurry,D,d.chartDifference_eq]
    exact ((hA z.1 z.2).1.sub (hA z.1 z.2).2.1).const_mul _
  · apply (((d.integrable_inv_tail p ε⁻¹).const_mul A).mul_prod (hh.integrable d).norm).mono'
      hm.aestronglyMeasurable.norm.integral_prod_right'
    filter_upwards with z
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    change (∫ y, ‖D z y‖ ∂dx) ≤ A * (if ‖z.1.val⁻¹‖ ≤ ε⁻¹ then ‖z.1.val‖⁻¹ else 0) * ‖h z.2‖
    by_cases hu : ‖z.1.val⁻¹‖ ≤ ε⁻¹
    · simp only [D,norm_mul,integral_const_mul,if_pos hu]
      rw [mul_comm (A*_)]
      exact mul_le_mul_of_nonneg_left (hA z.1 z.2).2.2 (norm_nonneg _)
    · have hu' : ‖z.1.val‖ < ε := (inv_lt_inv₀ hε (norm_pos_iff.mpr z.1.ne_zero)).mp (by simpa only [norm_inv,not_le] using hu)
      rw [if_neg hu]
      have hz (y : K) : D z y = 0 := hsmall z.1 hu' z.2 y
      simp [hz]

/-- Equation (axis-marginal-L) of Appendix A at a finite completion. The
zero Fourier mean removes the term independent of t before Fubini interchanges
the scaling and chart variables. -/
theorem finite_tested_marginal_difference_on_test (p : HeightOneSpectrum (𝓞 F)) (Φ : d.schwartz (.inr p))
    (hΦ : Φ.val ∈ d.testSet (.inr p)) (s : (LocalField F (.inr p))ˣ)
    {ρ : LocalField F (.inr p) → ℂ} (hρ : Bruhat (.inr p) ρ) (h₀ : ρ 0 = 0) :
    let v : Place F := .inr p
    let dx := selfDual F d.character v
    let h := d.hat v ρ
    (Real.sqrt (modulus F v (n : LocalField F v)) : ℂ) *
      d.lineIntegral v (fun μ => d.marginal v (d.transformTest v Φ hΦ) (μ^n*s) * ρ μ.val) =
      ∫ y, if hy : y ≠ 0 then
        ∫ t, h t * d.differenceIntegral v (fun x => Φ.val.2 x (Units.mk0 y hy))
          (-(s * Units.mk0 y hy)) (t^n+s.val*y) ∂dx else 0 ∂dx := by
  let v : Place F := .inr p
  let K := LocalField F v
  let dx := selfDual F d.character v
  let ν := d.lineMeasure v
  let h := d.hat v ρ
  letI : dx.IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  letI : NullSingletonClass dx := d.selfDual_nullSingleton v
  let D (z : Kˣ × K) (y : K) := h z.2 * d.chartDifference v Φ.val s z.1 z.2 y
  have hh := d.hat_finite_bruhat p hρ
  have hi : Integrable (Function.uncurry D) ((ν.prod dx).prod dx) := d.finite_joint_difference_integrable p hΦ s hh
  obtain ⟨A,hA⟩ := d.chartSection_bound p hΦ s
  have hz : (∫ t, h t ∂dx) = 0 := (d.integral_hat_finite p hρ).trans h₀
  refine (d.finite_tested_marginal_slice_on_test p Φ hΦ s hρ h₀).trans ?_
  rw [← d.integral_lineMeasure]
  trans ∫ z : Kˣ × K, ∫ y, D z y ∂dx ∂(ν.prod dx)
  · rw [integral_prod (fun z : Kˣ × K => ∫ y, D z y ∂dx) hi.integral_prod_left]
    apply integral_congr_ae
    filter_upwards [hi.integral_prod_left.prod_right_ae] with u hu
    let k := ∫ y, d.axisSubtraction v Φ.val s u y ∂dx
    have split (t : K) : h t * (∫ y, d.marginalSlice v Φ.val s u t y ∂dx) =
        (∫ y, D (u,t) y ∂dx) + h t*k := by
      simp only [D,d.chartDifference_eq,integral_const_mul,k]
      rw [integral_sub (f := d.marginalSlice v Φ.val s u t) (g := d.axisSubtraction v Φ.val s u)
        (μ := dx) (hA u t).1 (hA u t).2.1]
      ring
    change (∫ t, h t * (∫ y, d.marginalSlice v Φ.val s u t y ∂dx) ∂dx) = ∫ t, ∫ y, D (u,t) y ∂dx ∂dx
    change Integrable (fun t => ∫ y, D (u,t) y ∂dx) dx at hu
    simp_rw [split]
    rw [integral_add hu ((hh.integrable d).mul_const k),integral_mul_const,hz,zero_mul,add_zero]
  · rw [integral_integral_swap hi]
    apply integral_congr_ae
    filter_upwards [hi.prod_left_ae,dx.ae_ne 0] with y hyi hy
    change y ≠ 0 at hy
    rw [dif_pos hy,integral_prod_symm (fun z => D z y) hyi]
    apply integral_congr_ae
    let roots := Polynomial.nthRootsFinset n (-(s.val*y))
    filter_upwards [roots.finite_toSet.countable.ae_notMem dx] with t ht
    have ht₀ : t^n+s.val*y ≠ 0 := by
      intro he
      exact ht ((Polynomial.mem_nthRootsFinset (NeZero.pos n) _).mpr (eq_neg_of_add_eq_zero_left he))
    simp only [D,chartDifference,dif_pos (show y ≠ 0 from hy),integral_const_mul,
      differenceIntegral,dif_pos ht₀,← d.integral_lineMeasure,marginalDifference,Units.val_mul,Units.val_mk0]
    rfl


end Datum
end MetaplecticPoisson
