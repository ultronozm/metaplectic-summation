import MetaplecticSummation.DualBallVolumes
import MetaplecticSummation.FieldFourierIntegral
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Fourier inversion with frequency cutoffs and Plancherel on an ultrametric local field. -/
noncomputable section
namespace MetaplecticPoisson
open MeasureTheory Metric Set Filter
open scoped Topology ComplexConjugate ENNReal
open Classical
open Datum (fourierIntegral fourierIntegral_swap)
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K]
  [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsAddHaarMeasure]
  (ψ : AddChar K ℂ)

/-- For a continuous compactly supported function, integrating its transform
over increasing balls recovers the value at zero. -/
theorem tendsto_integral_fourier_closedBall (hc : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1)
    (hn : ∃ z, ψ z ≠ 1) (hV : DualBallVolumes ψ μ) {f : K → ℂ}
    (hf : Continuous f) (hk : HasCompactSupport f) (a : Kˣ) (ha : 1 < ‖a.val‖) :
    Tendsto (fun j : ℕ => ∫ u in closedBall 0 (‖a.val‖^j), fourierIntegral μ ψ f u ∂μ)
      atTop (𝓝 (f 0)) := by
  obtain ⟨z,hz⟩ := hn
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp ((hf.tendsto 0).eventually
    (ball_mem_nhds (f 0) (half_pos hε)))
  obtain ⟨N,hN⟩ := eventually_atTop.mp ((tendsto_pow_atTop_atTop_of_one_lt ha).eventually_gt_atTop (‖z‖/δ))
  refine ⟨N,fun j hj => ?_⟩
  let B := closedBallSubgroup (K := K) (‖a.val‖^j) (by positivity)
  let D := {x : K | ∀ y ∈ B, ψ (x*y) = 1}
  have hd : IsClosed D := by
    dsimp only [D]
    simp only [setOf_forall]
    exact isClosed_iInter (fun y => isClosed_iInter (fun _ =>
      isClosed_eq (hc.comp (continuous_id.mul_const y)) continuous_const))
  have hB : (B : Set K) = closedBall 0 (‖a.val‖^j) := rfl
  have vol : μ.real B * μ.real D = 1 := by
    change μ.real (B : Set K) * μ.real {x : K | ∀ y ∈ (B : Set K), ψ (x*y) = 1} = 1
    simp only [hB]
    simpa only [Units.val_pow_eq_pow_val,norm_pow] using hV (a^j)
  have hfin : μ D < ⊤ := by
    by_contra! h
    have h₀ : μ.real D = 0 := by simp [measureReal_def,top_unique h]
    simp [h₀] at vol
  have near (x : K) (hx : x ∈ D) : ‖f x - f 0‖ ≤ ε/2 := by
    apply le_of_lt
    apply (show dist (f x) (f 0) < ε/2 → _ by simp only [dist_eq_norm,imp_self])
    apply hball
    rw [mem_ball_zero_iff]
    by_contra! hlarge
    have hx₀ := norm_pos_iff.mp (hδ.trans_le hlarge)
    have hbound : ‖z / x‖ ≤ ‖a.val‖^j := by
      rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr hx₀)]
      exact (div_lt_iff₀ hδ |>.mp (hN j hj)).le.trans
        (mul_le_mul_of_nonneg_left hlarge (by positivity))
    exact hz (by simpa only [mul_div_cancel₀ _ hx₀] using hx (z/x) (mem_closedBall_zero_iff.mpr hbound))
  have cl := IsUltrametricDist.isClopen_closedBall (0:K) (pow_ne_zero j (norm_ne_zero_iff.mpr a.ne_zero))
  let g := (B : Set K).indicator (fun _ => (1:ℂ))
  have hgc : Continuous g := cl.continuous_indicator continuous_const
  have hgk : HasCompactSupport g := HasCompactSupport.intro (isCompact_closedBall _ _) (fun _ h => indicator_of_notMem h _)
  have hg (u : K) : fourierIntegral μ ψ g u = D.indicator (fun _ => (μ.real B : ℂ)) u := by
    unfold fourierIntegral
    simpa only [mul_comm u] using Datum.hat_addSubgroup_indicator B D cl.isClosed.measurableSet μ ψ ψ.map_add_eq_mul (fun _ => Iff.rfl) u
  have swap := fourierIntegral_swap μ hc hu hf hgc (hf.integrable_of_hasCompactSupport hk)
    (hgc.integrable_of_hasCompactSupport hgk)
  simp_rw [hg] at swap
  have cut : (∫ u in B, fourierIntegral μ ψ f u ∂μ) = (μ.real B : ℂ) * ∫ x in D, f x ∂μ := by
    convert swap using 1
    · rw [hB,← integral_indicator cl.isClosed.measurableSet]
      congr 1
      ext x
      by_cases hx : x ∈ B <;> simp [g,← hB,hx]
    · rw [← integral_const_mul,← integral_indicator hd.measurableSet]
      congr 1
      ext x
      by_cases hx : x ∈ D <;> simp [hx,mul_comm]
  rw [dist_eq_norm,← hB,cut]
  have avg : (μ.real B : ℂ) * (∫ x in D, f x ∂μ) - f 0 =
      (μ.real B : ℂ) * ∫ x in D, f x - f 0 ∂μ := by
    rw [integral_sub (hf.integrable_of_hasCompactSupport hk).integrableOn (integrableOn_const hfin.ne),
      setIntegral_const,Complex.real_smul,mul_sub,← mul_assoc,← Complex.ofReal_mul,vol,Complex.ofReal_one,one_mul]
  rw [avg,norm_mul,Complex.norm_real,Real.norm_of_nonneg measureReal_nonneg]
  have hle := norm_setIntegral_le_of_norm_le_const hfin near
  calc
    _ ≤ μ.real B * (ε/2 * μ.real D) := mul_le_mul_of_nonneg_left hle measureReal_nonneg
    _ = ε/2 := by rw [mul_left_comm,vol,mul_one]
    _ < ε := half_lt_self hε

private theorem fourier_convolution (hc : Continuous ψ) {f g : K → ℂ}
    (hf : Continuous f) (hk : HasCompactSupport f) (hg : Continuous g) (hl : HasCompactSupport g) (u : K) :
    fourierIntegral μ ψ (MeasureTheory.convolution f g (ContinuousLinearMap.mul ℂ ℂ) μ) u =
      fourierIntegral μ ψ f u * fourierIntegral μ ψ g u := by
  let twist (f : K → ℂ) (x : K) := f x * ψ (u*x)
  have hi {f : K → ℂ} (hc' : Continuous f) (hk' : HasCompactSupport f) : Integrable (twist f) μ :=
    (hc'.mul (hc.comp (continuous_const.mul continuous_id))).integrable_of_hasCompactSupport hk'.mul_right
  let L := ContinuousLinearMap.mul ℂ ℂ
  have he (x : K) : twist (MeasureTheory.convolution f g L μ) x =
      MeasureTheory.convolution (twist f) (twist g) L μ x := by
    change (∫ y, f y * g (x-y) ∂μ) * ψ (u*x) = ∫ y, (f y * ψ (u*y)) * (g (x-y) * ψ (u*(x-y))) ∂μ
    rw [← integral_mul_const]
    apply integral_congr_ae
    filter_upwards with y
    rw [show u*x = u*y + u*(x-y) by ring,ψ.map_add_eq_mul]
    ring
  exact (integral_congr_ae (Eventually.of_forall he)).trans (integral_convolution L (hi hf hk) (hi hg hl))

/-- Dual-ball normalization implies Plancherel for the ordinary defining integral
of every continuous compactly supported function. -/
theorem kernelPlancherel_of_dualBallVolumes (hc : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1)
    (hn : ∃ z, ψ z ≠ 1) (hV : DualBallVolumes ψ μ) : KernelPlancherel (fun x y => ψ (x*y)) μ := by
  intro f hf hk
  let g (t : K) := conj (f (-t))
  have hg : Continuous g := Complex.continuous_conj.comp (hf.comp continuous_neg)
  have hl : HasCompactSupport g := (hk.comp_homeomorph (Homeomorph.neg K)).comp_left (map_zero _)
  let L := ContinuousLinearMap.mul ℂ ℂ
  let H := MeasureTheory.convolution f g L μ
  have hH : Continuous H := hl.continuous_convolution_right L
    (hf.integrable_of_hasCompactSupport hk).locallyIntegrable hg
  have hK : HasCompactSupport H := hk.convolution L hl
  have hneg (t : K) : ψ (-t) = conj (ψ t) := by
    apply mul_left_cancel₀ (a := ψ t) (by intro h; simpa [h] using hu t)
    rw [← ψ.map_add_eq_mul,add_neg_cancel,ψ.map_zero_eq_one,Complex.mul_conj',hu]
    simp
  let T := fourierIntegral μ ψ f
  have hghat (u : K) : fourierIntegral μ ψ g u = conj (T u) := by
    unfold fourierIntegral
    simp only [T,fourierIntegral,← integral_conj]
    rw [← integral_neg_eq_self (fun t : K => g t * ψ (u*t)) μ]
    simp [g,mul_neg,hneg]
  have hHhat (u : K) : fourierIntegral μ ψ H u = ((‖T u‖^2 : ℝ) : ℂ) := by
    rw [show fourierIntegral μ ψ H u = _ from fourier_convolution μ ψ hc hf hk hg hl u,hghat]
    simpa only [Complex.ofReal_pow] using Complex.mul_conj' (T u)
  have hH0 : H 0 = ((∫ x, ‖f x‖^2 ∂μ : ℝ) : ℂ) := by
    change (∫ x, f x * conj (f (-(0-x))) ∂μ) = _
    simp only [zero_sub,neg_neg,Complex.mul_conj',← Complex.ofReal_pow]
    exact integral_ofReal
  obtain ⟨w,hw⟩ := NormedField.exists_lt_norm K 1
  let a := Units.mk0 w (norm_pos_iff.mp (zero_lt_one.trans hw))
  let B (j : ℕ) := closedBall (0:K) (‖w‖^j)
  have cutoff := tendsto_integral_fourier_closedBall μ ψ hc hu hn hV hH hK a hw
  change Tendsto (fun j => ∫ u in B j, fourierIntegral μ ψ H u ∂μ) atTop (𝓝 (H 0)) at cutoff
  have real_integral (j : ℕ) : (∫ u in B j, ((‖T u‖^2 : ℝ) : ℂ) ∂μ) =
      ((∫ u in B j, ‖T u‖^2 ∂μ : ℝ) : ℂ) := integral_ofReal
  simp only [hHhat,real_integral,hH0] at cutoff
  have limit : Tendsto (fun j => ∫ u in B j, ‖T u‖^2 ∂μ) atTop (𝓝 (∫ x, ‖f x‖^2 ∂μ)) := by
    simpa only [Complex.ofReal_re,Function.comp_def] using Complex.continuous_re.continuousAt.tendsto.comp cutoff
  have hT : Continuous T := by
    let G (u t : K) := f t * ψ (u*t)
    have hG : Continuous (Function.uncurry G) := hf.comp continuous_snd |>.mul (hc.comp (continuous_fst.mul continuous_snd))
    have he (u : K) : (∫ t in tsupport f, G u t ∂μ) = T u :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun t ht => by simp [G,image_eq_zero_of_notMem_tsupport ht])
    simpa only [← funext he] using continuous_parametric_integral_of_continuous hG hk
  have energy {h : K → ℂ} {ν : Measure K} (hi : Integrable (fun x => ‖h x‖^2) ν) :
      ENNReal.ofReal (∫ x, ‖h x‖^2 ∂ν) = ∫⁻ x, ‖h x‖ₑ^2 ∂ν := by
    rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun x => sq_nonneg _))]
    simp only [ENNReal.ofReal_pow (norm_nonneg _),ofReal_norm]
  have hbi (j : ℕ) : IntegrableOn (fun x => ‖T x‖^2) (B j) μ :=
    (hT.norm.pow 2).continuousOn.integrableOn_compact (isCompact_closedBall _ _)
  have hfi := (hf.norm.pow 2).integrable_of_hasCompactSupport (μ := μ)
    (by simpa only [pow_two] using hk.norm.mul_right (f' := fun x => ‖f x‖))
  have hlim := ENNReal.continuous_ofReal.continuousAt.tendsto.comp limit
  change Tendsto (fun j => ENNReal.ofReal (∫ u in B j, ‖T u‖^2 ∂μ)) atTop
    (𝓝 (ENNReal.ofReal (∫ x, ‖f x‖^2 ∂μ))) at hlim
  simp_rw [energy (hbi _),energy hfi] at hlim
  let ν := μ.withDensity (fun x => ‖T x‖ₑ^2)
  have hmono : Monotone B := fun i j h => closedBall_subset_closedBall (pow_le_pow_right₀ hw.le h)
  have union : (⋃ j, B j) = univ := eq_univ_of_forall fun x => by
    obtain ⟨j,hj⟩ := pow_unbounded_of_one_lt ‖x‖ hw
    exact mem_iUnion.mpr ⟨j,mem_closedBall_zero_iff.mpr hj.le⟩
  have hfull := tendsto_measure_iUnion_atTop (μ := ν) hmono
  rw [union] at hfull
  change Tendsto (fun j => ν (B j)) atTop (𝓝 (ν univ)) at hfull
  simp only [ν,withDensity_apply _ isClosed_closedBall.measurableSet,withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ,B] at hfull
  have he := tendsto_nhds_unique hfull hlim
  simpa only [T,fourierIntegral,mul_comm] using he

end MetaplecticPoisson
