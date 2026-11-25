import MetaplecticSummation.ArchimedeanDifference
import MetaplecticSummation.Marginals.ArchimedeanDifferenceBounds
import MetaplecticSummation.Marginals.FrequencyTest

/-! The tested root-sum form of Lemma A.2 at real and complex places. A horizontal
slice of a test section's Y-chart is Schwartz, the subtracted integrand is jointly
integrable by the transverse bound of order one, and the single-root identity
evaluates the inner frequency integral. -/

noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField MeasureTheory Set Filter
open scoped Topology ContDiff
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n) (w : InfinitePlace F)
local notation "v" => (Sum.inl w : Place F)
local notation "K" => LocalField F v
local notation "dx" => selfDual F d.character v

/-- A Y-chart of an Archimedean test section decays to third order in the second coordinate. -/
theorem arch_test_Y_decay {f : Charts K} (hf : f ∈ d.testSet v) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : K) (y : Kˣ), ‖f.2 x y‖ ≤ C*((1+‖y.val‖)^3)⁻¹ := by
  have go {L : Type} [NormedField L] [NormedAlgebra ℝ L] (e : K ≃+* L) (he : Isometry e)
      (htest : archTest e f) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : K) (y : Kˣ), ‖f.2 x y‖ ≤ C*((1+‖y.val‖)^3)⁻¹ := by
    have norm_e := he.norm_map_of_map_zero e.map_zero
    obtain ⟨C,hC,H⟩ := rapidChart_derivative_polynomial htest.2 0 3
    refine ⟨C,hC,fun x y => ?_⟩
    have hy : (e x,e y.val).2 ≠ 0 := (map_ne_zero e).mpr y.ne_zero
    have h := H (e x,e y.val) hy
    rw [norm_iteratedFDeriv_zero] at h
    have hval : yChart f (e.symm (e x),e.symm (e y.val)) = f.2 x y := by
      simp [yChart,y.ne_zero]
    rw [hval] at h
    have hp : ‖y.val‖ ≤ ‖(e x,e y.val)‖ := by
      rw [Prod.norm_def,norm_e y.val]; exact le_max_right ‖e x‖ ‖y.val‖
    rw [← div_eq_mul_inv,le_div_iff₀ (by positivity)]
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) 3) (norm_nonneg _)).trans h
  by_cases hw : w.IsReal
  · exact go (InfinitePlace.Completion.ringEquivRealOfIsReal hw)
      (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw)
      (by simpa only [testSet,hw,↓reduceDIte] using! hf.2)
  · exact go (InfinitePlace.Completion.ringEquivComplexOfIsComplex (InfinitePlace.not_isReal_iff_isComplex.mp hw))
      (InfinitePlace.Completion.isometry_extensionEmbedding w)
      (by simpa only [testSet,hw,↓reduceDIte] using! hf.2)

/-- A horizontal slice of the Y-chart of an Archimedean test section is Schwartz. -/
theorem arch_test_slice_bruhat {f : Charts K} (hf : f ∈ d.testSet v) (y : Kˣ) :
    Bruhat v (fun x => f.2 x y) := by
  have go {L : Type} [NormedField L] [NormedAlgebra ℝ L] (e : K ≃+* L) (he : Isometry e)
      (htest : archTest e f) : ∃ g : SchwartzMap L ℂ, ∀ x, f.2 x y = g (e x) := by
    have norm_e := he.norm_map_of_map_zero e.map_zero
    let Y : L × L → ℂ := fun p => yChart f (e.symm p.1,e.symm p.2)
    let U : Set (L × L) := {p | p.2 ≠ 0}
    have hU : IsOpen U := isOpen_ne_fun continuous_snd continuous_const
    let A : L →L[ℝ] L × L := ContinuousLinearMap.inl ℝ L L
    let c : L × L := (0,e y.val)
    have hc : e y.val ≠ 0 := (map_ne_zero e).mpr y.ne_zero
    let g : L → ℂ := fun x => Y (c + A x)
    have hmem (x : L) : c + A x ∈ U := by simp [c,A,U,hc]
    have hsmooth : ContDiff ℝ ∞ g := contDiff_iff_contDiffAt.mpr fun x =>
      (htest.2.1.contDiffAt (hU.mem_nhds (hmem x))).comp x ((contDiff_const.add A.contDiff).contDiffAt)
    have hderiv (j : ℕ) (x : L) : iteratedFDeriv ℝ j g x =
        (iteratedFDeriv ℝ j Y (c + A x)).compContinuousLinearMap (fun _ => A) := by
      let V := (fun q : L × L => c + q) ⁻¹' U
      have hV : IsOpen V := hU.preimage (continuous_const.add continuous_id)
      have hG : ContDiffOn ℝ ∞ (fun q : L × L => Y (c+q)) V :=
        htest.2.1.comp ((contDiff_const.add contDiff_id).contDiffOn) (fun _ h => h)
      have pre : A ⁻¹' V = univ := eq_univ_of_forall hmem
      have hmemV : A x ∈ V := hmem x
      have h := A.iteratedFDerivWithin_comp_right hG hV.uniqueDiffOn
        (by rw [pre]; exact uniqueDiffOn_univ) hmemV (i := j) (by simp)
      rw [pre,iteratedFDerivWithin_univ,iteratedFDerivWithin_eq_iteratedFDeriv hV.uniqueDiffOn
        ((hG.contDiffAt (hV.mem_nhds hmemV)).of_le (by simp)) hmemV,iteratedFDeriv_comp_add_left] at h
      exact h
    refine ⟨⟨g,hsmooth,fun k j => ?_⟩,fun x => ?_⟩
    · obtain ⟨C,hC,H⟩ := rapidChart_derivative_polynomial htest.2 j k
      refine ⟨C,fun x => ?_⟩
      have hb := H (c + A x) (hmem x)
      have hn : ‖x‖ ≤ ‖c + A x‖ := by simp [c,A,Prod.norm_def]
      have hA : ‖A‖ ≤ 1 := ContinuousLinearMap.norm_inl_le_one _ _ _
      rw [hderiv]
      calc ‖x‖^k * ‖(iteratedFDeriv ℝ j Y (c + A x)).compContinuousLinearMap (fun _ => A)‖
          ≤ (1+‖c + A x‖)^k * (‖iteratedFDeriv ℝ j Y (c + A x)‖ * ∏ _ : Fin j, ‖A‖) := by
            gcongr
            · linarith
            · exact ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
        _ ≤ (1+‖c + A x‖)^k * (‖iteratedFDeriv ℝ j Y (c + A x)‖ * 1) := by
            gcongr
            rw [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
            exact pow_le_one₀ (norm_nonneg _) hA
        _ ≤ C := by rw [mul_one,mul_comm]; exact hb
    · show f.2 x y = g (e x)
      simp [g,Y,c,A,yChart,y.ne_zero]
  dsimp only [Bruhat]
  split <;> rename_i hw
  · exact go _ (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw)
      (by simpa only [testSet,hw,↓reduceDIte] using! hf.2)
  · exact go _ (InfinitePlace.Completion.isometry_extensionEmbedding w)
      (by simpa only [testSet,hw,↓reduceDIte] using! hf.2)

omit [NeZero n] in
/-- Polynomial weights preserve integrability of Archimedean Schwartz functions. -/
theorem Bruhat.integrable_pow_mul {f : K → ℂ} (hf : Bruhat v f) (k : ℕ) :
    Integrable (fun t => ‖t‖^k * ‖f t‖) dx := by
  let : (dx).IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  obtain ⟨⟨L,lip⟩,est,_⟩ := d.arch_bruhat_estimates w hf
  obtain ⟨A,hA⟩ := est k
  obtain ⟨B,hB⟩ := est (k+3)
  have hA0 : 0 ≤ A := (mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _)).trans (hA 0)
  have hB0 : 0 ≤ B := (mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _)).trans (hB 0)
  refine ((d.integrable_local_inv_cube v).const_mul (8*(A+B))).mono'
    ((continuous_norm.pow k).mul lip.continuous.norm).aestronglyMeasurable (.of_forall fun t => ?_)
  rw [Real.norm_of_nonneg (by positivity),← div_eq_mul_inv,le_div_iff₀ (by positivity)]
  by_cases ht : ‖t‖ ≤ 1
  · calc ‖t‖^k * ‖f t‖ * (1+‖t‖)^3 ≤ A * 2^3 := mul_le_mul (hA t) (pow_le_pow_left₀ (by positivity) (by linarith) 3)
          (by positivity) hA0
      _ ≤ 8*(A+B) := by nlinarith
  · have h1 : 1 ≤ ‖t‖ := (lt_of_not_ge ht).le
    have h2 : (1+‖t‖)^3 ≤ 8*‖t‖^3 := by
      calc (1+‖t‖)^3 ≤ (2*‖t‖)^3 := pow_le_pow_left₀ (by positivity) (by linarith) 3
        _ = 8*‖t‖^3 := by ring
    calc ‖t‖^k * ‖f t‖ * (1+‖t‖)^3 ≤ ‖t‖^k * ‖f t‖ * (8*‖t‖^3) := by gcongr
      _ = 8*(‖t‖^(k+3) * ‖f t‖) := by ring
      _ ≤ 8*B := by gcongr; exact hB t
      _ ≤ 8*(A+B) := by linarith

/-- Both terms of the subtracted Y-chart integrand are integrable in the chart variable. -/
theorem arch_test_slices {f : Charts K} (hf : f ∈ d.testSet v) (s u : Kˣ) (t : K) :
    Integrable (d.marginalSlice v f s u t) dx ∧ Integrable (d.axisSubtraction v f s u) dx := by
  let : (dx).IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  let : SecondCountableTopology K :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let Φ : d.schwartz v := ⟨f,Submodule.subset_span (Or.inl hf)⟩
  have fc : Continuous (fun z : K × Kˣ => f.2 z.1 z.2) := (d.continuous_schwartz_charts v Φ).2
  obtain ⟨C,hC,hdec⟩ := d.arch_test_Y_decay w hf
  have slice_bound {g : K → ℂ} (hg : ∀ y, ‖g y‖ ≤ C*((1+‖y‖)^3)⁻¹) (hgm : Measurable g) : Integrable g dx :=
    ((d.integrable_local_inv_cube v).const_mul C).mono' hgm.aestronglyMeasurable (.of_forall hg)
  have term_bound (x : K → K) (y : K) :
      ‖(if hy : y ≠ 0 then d.symbol v u (-(s*Units.mk0 y hy)) * f.2 (x y) (Units.mk0 y hy) else 0)‖ ≤
        C*((1+‖y‖)^3)⁻¹ := by
    by_cases hy : y = 0
    · simp only [hy,ne_eq,not_true_eq_false,dite_false,norm_zero]; positivity
    · simp only [ne_eq,hy,not_false_eq_true,dite_true,norm_mul,norm_symbol,one_mul]
      exact hdec _ _
  constructor
  · exact slice_bound (term_bound (fun y => (t^n+s.val*y)*u.val))
      (d.chartTerm_measurable v fc s measurable_const
        ((measurable_const.add (measurable_const.mul measurable_id)).mul measurable_const) measurable_id)
  · exact slice_bound (term_bound (fun _ => u.val))
      (d.chartTerm_measurable v fc s measurable_const measurable_const measurable_id)

/-- Joint absolute convergence of the subtracted integral in the scaling variable u,
frequency t and chart variable y at every infinite place. -/
theorem arch_joint_difference_integrable {f : Charts K} (hf : f ∈ d.testSet v) (s : Kˣ)
    {h : K → ℂ} (hh : Bruhat v h) :
    Integrable (fun z : (Kˣ × K) × K => h z.1.2 * d.chartDifference v f s z.1.1 z.1.2 z.2)
      (((d.lineMeasure v).prod dx).prod dx) := by
  let ν := d.lineMeasure v
  let : (dx).IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  let : SecondCountableTopology K :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let Φ : d.schwartz v := ⟨f,Submodule.subset_span (Or.inl hf)⟩
  have fc : Continuous (fun z : K × Kˣ => f.2 z.1 z.2) := (d.continuous_schwartz_charts v Φ).2
  obtain ⟨⟨L,lip⟩,-,-⟩ := d.arch_bruhat_estimates w hh
  let D (z : Kˣ × K) (y : K) := h z.2 * d.chartDifference v f s z.1 z.2 y
  let Z := (Kˣ × K) × K
  have hm : Measurable (Function.uncurry D) := by
    have hu : Measurable (fun z : Z => z.1.1) := measurable_fst.comp measurable_fst
    have ht : Measurable (fun z : Z => z.1.2) := measurable_snd.comp measurable_fst
    have huv := Units.continuous_val.measurable.comp hu
    simp only [D,d.chartDifference_eq]
    exact (lip.continuous.measurable.comp ht).mul ((d.chartTerm_measurable v fc s hu
      (((ht.pow_const n).add (measurable_const.mul measurable_snd)).mul huv) measurable_snd).sub
      (d.chartTerm_measurable v fc s hu huv measurable_snd))
  have slices := d.arch_test_slices w hf s
  obtain ⟨B,hB,hbound⟩ := d.arch_integral_chartDifference_bound w hf s
  have hweight : Integrable (fun t : K => ‖h t‖*(1+‖t‖^n+‖s.val‖)) dx := by
    have h1 := Bruhat.integrable_pow_mul d w hh n
    have h2 := (hh.integrable d).norm.const_mul (1+‖s.val‖)
    refine (h1.add h2).congr (.of_forall fun t => ?_)
    simp only [Pi.add_apply]
    ring
  change Integrable (Function.uncurry D) ((ν.prod dx).prod dx)
  refine (integrable_prod_iff hm.aestronglyMeasurable).2 ⟨?_,?_⟩
  · filter_upwards with z
    simp only [Function.uncurry,D,d.chartDifference_eq]
    exact ((slices z.1 z.2).1.sub (slices z.1 z.2).2).const_mul _
  · apply (((d.arch_min_weight w).const_mul B).mul_prod hweight).mono'
      hm.aestronglyMeasurable.norm.integral_prod_right'
    filter_upwards with z
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    change (∫ y, ‖D z y‖ ∂dx) ≤ B * min ‖z.1.val‖ ‖z.1.val‖⁻¹ * (‖h z.2‖*(1+‖z.2‖^n+‖s.val‖))
    simp only [D,norm_mul,integral_const_mul]
    calc ‖h z.2‖ * ∫ y, ‖d.chartDifference v f s z.1 z.2 y‖ ∂dx
        ≤ ‖h z.2‖ * (B*(1+‖z.2‖^n+‖s.val‖)*min ‖z.1.val‖ ‖z.1.val‖⁻¹) := by
          gcongr; exact hbound z.1 z.2
      _ = _ := by ring

/-- Equation (axis-marginal-L) of Appendix A at an infinite place. The zero Fourier
mean removes the term independent of t before Fubini interchanges the scaling and
chart variables. -/
theorem arch_tested_marginal_difference_on_test (Φ : d.schwartz v) (hΦ : Φ.val ∈ d.testSet v) (s : Kˣ)
    {ρ : K → ℂ} (hρ : Bruhat v ρ) (hk : HasCompactSupport ρ) (h₀ : 0 ∉ tsupport ρ) :
    let h := d.hat v ρ
    (Real.sqrt (modulus F v (n : K)) : ℂ) *
      d.lineIntegral v (fun μ => d.marginal v (d.transformTest v Φ hΦ) (μ^n*s) * ρ μ.val) =
      ∫ y, if hy : y ≠ 0 then
        ∫ t, h t * d.differenceIntegral v (fun x => Φ.val.2 x (Units.mk0 y hy))
          (-(s * Units.mk0 y hy)) (t^n+s.val*y) ∂dx else 0 ∂dx := by
  let ν := d.lineMeasure v
  let h := d.hat v ρ
  let : (dx).IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  let : NullSingletonClass dx := d.selfDual_nullSingleton v
  let D (z : Kˣ × K) (y : K) := h z.2 * d.chartDifference v Φ.val s z.1 z.2 y
  have hh := d.arch_hat_bruhat w hρ
  have hi : Integrable (Function.uncurry D) ((ν.prod dx).prod dx) := d.arch_joint_difference_integrable w hΦ s hh
  have hA := d.arch_test_slices w hΦ s
  have hz : (∫ t, h t ∂dx) = 0 := (d.integral_hat_arch w hρ).trans (image_eq_zero_of_notMem_tsupport h₀)
  have hc : Continuous ρ := (d.arch_bruhat_estimates w hρ).1.choose_spec.continuous
  refine (d.tested_marginal_slice_on_test v Φ hΦ s hc hk h₀).trans ?_
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
        (μ := dx) (hA u t).1 (hA u t).2]
      ring
    change (∫ t, h t * (∫ y, d.marginalSlice v Φ.val s u t y ∂dx) ∂dx) = ∫ t, ∫ y, D (u,t) y ∂dx ∂dx
    change Integrable (fun t => ∫ y, D (u,t) y ∂dx) dx at hu
    simp_rw [split]
    rw [integral_add hu ((hh.integrable d).mul_const k),integral_mul_const,hz,zero_mul,add_zero]
  · rw [integral_integral_swap hi]
    apply integral_congr_ae
    filter_upwards [hi.prod_left_ae,(dx).ae_ne 0] with y hyi hy
    change y ≠ 0 at hy
    simp only [ne_eq,hy,not_false_eq_true,dite_true]
    rw [integral_prod_symm (fun z => D z y) hyi]
    apply integral_congr_ae
    let roots := Polynomial.nthRootsFinset n (-(s.val*y))
    filter_upwards [roots.finite_toSet.countable.ae_notMem dx] with t ht
    have ht₀ : t^n+s.val*y ≠ 0 := by
      intro he
      exact ht ((Polynomial.mem_nthRootsFinset (NeZero.pos n) _).mpr (eq_neg_of_add_eq_zero_left he))
    simp only [D,chartDifference,ne_eq,hy,ht₀,not_false_eq_true,dite_true,integral_const_mul,
      differenceIntegral,← d.integral_lineMeasure,marginalDifference,Units.val_mul,Units.val_mk0]
    rfl

/-- Pairing the transformed marginal with a smooth test supported away from zero
gives the sum of Fourier integrals over the local n-th roots, at an infinite place. -/
theorem arch_tested_root_sum_on_test (Φ : d.schwartz v) (hΦ : Φ.val ∈ d.testSet v) (s : Kˣ)
    {ρ : K → ℂ} (hρ : Bruhat v ρ) (hk : HasCompactSupport ρ) (h₀ : 0 ∉ tsupport ρ) :
    (Real.sqrt (modulus F v (n : K)) : ℂ) *
      d.lineIntegral v (fun μ => d.marginal v (d.transformTest v Φ hΦ) (μ^n*s) * ρ μ.val) =
      ∫ y, (if hy : y ≠ 0 then d.axis v Φ (Units.mk0 y hy) else 0) *
        ∑ r ∈ Polynomial.nthRootsFinset n (-(s.val*y)),
          d.lineIntegral v (fun μ => ρ μ.val * d.character.localValue F v (μ.val*r)) ∂dx := by
  refine (d.arch_tested_marginal_difference_on_test w Φ hΦ s hρ hk h₀).trans (integral_congr_ae ?_)
  filter_upwards with y
  by_cases hy : y = 0
  · simp [hy]
  · let Y := Units.mk0 y hy
    have he := d.arch_root_sum w (d.arch_test_slice_bruhat w hΦ Y) hρ hk h₀ (-(s*Y))
    simpa only [Y,Units.val_neg,Units.val_mul,Units.val_mk0,sub_neg_eq_add,ne_eq,hy,not_false_eq_true,dite_true,axis] using he

end MetaplecticPoisson.Datum
