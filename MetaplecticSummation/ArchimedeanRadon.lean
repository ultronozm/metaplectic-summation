import MetaplecticSummation.FiniteLeading
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-! Decay and absolute convergence of the archimedean Radon slices in §4. -/
noncomputable section
namespace MetaplecticPoisson
open MeasureTheory Set Filter NumberField
open scoped Topology
open Classical

/-- A chart with the unit coordinate first, including its estimates at infinity. -/
private def RapidLineChart {K : Type} [NormedField K] (f : Kˣ → K → ℂ) : Prop :=
  Continuous (Function.uncurry f) ∧ ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a b,
    ‖f a b‖ * (1 + max ‖a.val‖ ‖b‖)^j ≤ C

private theorem rapidChart_polynomial {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} {g : E → ℂ} (hg : rapidChart U g) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ U, ‖g z‖*(1+‖z‖)^j ≤ C := by
  obtain ⟨A,ha⟩ := hg.2 0 0
  obtain ⟨B,hb⟩ := hg.2 0 j
  let M := max 0 (max A B)
  have hM : 0 ≤ M := le_max_left ..
  refine ⟨M*2^j,by positivity,?_⟩
  intro z hz
  have H : ‖g z‖ * (max 1 ‖z‖)^j ≤ M := by
    rcases le_total ‖z‖ 1 with h | h
    · rw [max_eq_left h,one_pow,mul_one]
      exact (by simpa using ha z hz : ‖g z‖ ≤ A).trans ((le_max_left A B).trans (le_max_right ..))
    · rw [max_eq_right h]
      have hp : 0 < ‖z‖^j := pow_pos (zero_lt_one.trans_le h) _
      have hh := hb z hz
      rw [norm_iteratedFDeriv_zero] at hh
      have hB : B ≤ M := (le_max_right A B).trans (le_max_right ..)
      have he : ‖g z‖ ≤ M*(‖z‖^j)⁻¹ := hh.trans
        ((mul_le_mul_of_nonneg_right hB (le_min hp.le (inv_nonneg.mpr hp.le))).trans
          (mul_le_mul_of_nonneg_left (min_le_right ..) hM))
      exact (le_div_iff₀ hp).mp (by simpa only [div_eq_mul_inv] using he)
  have hs : 1+‖z‖ ≤ (max 1 ‖z‖)*2 := by linarith [le_max_left 1 ‖z‖,le_max_right 1 ‖z‖]
  calc
    _ ≤ ‖g z‖*((max 1 ‖z‖)*2)^j := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hs _) (norm_nonneg _)
    _ ≤ _ := by rw [mul_pow,← mul_assoc]; exact mul_le_mul_of_nonneg_right H (by positivity)

private theorem archTest_lineCharts {K L : Type} [NormedField K] [NormedField L] [NormedAlgebra ℝ L]
    (e : K ≃+* L) (he : Isometry e) {f : Charts K} (hf : archTest e f) :
    RapidLineChart f.1 ∧ RapidLineChart (fun b a => f.2 a b) := by
  let X (q : Kˣ × K) := (e q.1.val,e q.2)
  let Y (q : Kˣ × K) := (e q.2,e q.1.val)
  have hx (q : Kˣ × K) : (X q).1 ≠ 0 := (map_ne_zero e).mpr q.1.ne_zero
  have hy (q : Kˣ × K) : (Y q).2 ≠ 0 := (map_ne_zero e).mpr q.1.ne_zero
  have cx : Continuous X := (he.continuous.comp (Units.continuous_val.comp continuous_fst)).prodMk
    (he.continuous.comp continuous_snd)
  have cy : Continuous Y := (he.continuous.comp continuous_snd).prodMk
    (he.continuous.comp (Units.continuous_val.comp continuous_fst))
  have ex (q : Kˣ × K) : xChart f (e.symm (X q).1,e.symm (X q).2) = f.1 q.1 q.2 := by
    simp [X,xChart,q.1.ne_zero]
  have ey (q : Kˣ × K) : yChart f (e.symm (Y q).1,e.symm (Y q).2) = f.2 q.2 q.1 := by
    simp [Y,yChart,q.1.ne_zero]
  constructor
  · refine ⟨(hf.1.1.continuousOn.comp_continuous cx hx).congr ex,?_⟩
    intro j
    obtain ⟨C,hC,H⟩ := rapidChart_polynomial hf.1 j
    refine ⟨C,hC,fun a b => ?_⟩
    simpa [Prod.norm_def,X,he.norm_map_of_map_zero e.map_zero,xChart,a.ne_zero] using H (X (a,b)) (hx _)
  · refine ⟨(hf.2.1.continuousOn.comp_continuous cy hy).congr ey,?_⟩
    intro j
    obtain ⟨C,hC,H⟩ := rapidChart_polynomial hf.2 j
    refine ⟨C,hC,fun a b => ?_⟩
    simpa [Prod.norm_def,Y,he.norm_map_of_map_zero e.map_zero,max_comm ‖b‖,yChart,a.ne_zero] using H (Y (a,b)) (hy _)

section Slice
variable {K : Type} [NormedField K] [MeasurableSpace K] [BorelSpace K]
variable {f : Kˣ → K → ℂ} {phase : Kˣ → Kˣ → ℂ} {p : K → K}

/-- Use the coordinate x on the line whose other coordinate is (xb + p(t))/a. -/
private def sliceKernel (f : Kˣ → K → ℂ) (phase : Kˣ → Kˣ → ℂ)
    (p : K → K) (q : Kˣ × K) (t x : K) : ℂ :=
  if hx : x ≠ 0 then f (Units.mk0 x hx) ((x*q.2+p t)/q.1.val) * phase (Units.mk0 x hx) q.1 else 0

private theorem kernel_measurable (hf : Continuous (Function.uncurry f)) (hphase : Continuous (Function.uncurry phase))
    (q : Kˣ × K) (t : K) : Measurable (sliceKernel f phase p q t) := by
  apply measurable_of_measurable_on_compl_singleton 0
  let lift (z : {x : K // x ≠ 0}) := Units.mk0 z.val z.property
  have hl : Continuous lift := Units.isEmbedding_val₀.continuous_iff.mpr continuous_subtype_val
  have hy : Continuous (fun x : {x : K // x ≠ 0} => (x.val*q.2+p t)/q.1.val) := by fun_prop
  exact (((hf.comp (hl.prodMk hy)).mul (hphase.comp (hl.prodMk (continuous_const (y := q.1))))).congr
    (fun x => by simp [sliceKernel,lift,x.property,Function.uncurry])).measurable

omit [MeasurableSpace K] [BorelSpace K] in
/-- The determinant bounds |t|^n by (|a|+|b|) times the norm of the input vector. -/
private theorem kernel_bound (hf : RapidLineChart f) (hphase : ∀ x a, ‖phase x a‖ = 1)
    {n : ℕ} (hn : 1 ≤ n) (hp : ∀ t, ‖p t‖ = ‖t‖^n) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q t x,
      ‖sliceKernel f phase p q t x‖ ≤ C*(2+‖q.1.val‖+‖q.2‖)^j*((1+‖t‖)^j)⁻¹*((1+‖x‖)^3)⁻¹ := by
  obtain ⟨C,hC,H⟩ := hf.2 (3+j)
  refine ⟨C,hC,fun q t x => ?_⟩
  by_cases hx : x = 0
  · rw [sliceKernel,dif_neg (not_ne_iff.mpr hx),norm_zero]
    positivity
  let a := Units.mk0 x hx
  let y := (x*q.2+p t)/q.1.val
  let r := max ‖x‖ ‖y‖
  let D := 2+‖q.1.val‖+‖q.2‖
  have hR : 0 ≤ r := (norm_nonneg x).trans (le_max_left ..)
  have he : p t = y*q.1.val - x*q.2 := by dsimp [y]; field_simp; ring
  have ht : ‖t‖^n ≤ r*(‖q.1.val‖+‖q.2‖) := by
    rw [← hp t,he]
    apply (norm_sub_le ..).trans
    rw [norm_mul,norm_mul,mul_add]
    exact add_le_add (mul_le_mul_of_nonneg_right (le_max_right ..) (norm_nonneg _))
      (mul_le_mul_of_nonneg_right (le_max_left ..) (norm_nonneg _))
  have ht' : 1+‖t‖ ≤ D*(1+r) := by
    dsimp [D]
    rcases le_total ‖t‖ 1 with h | h
    · nlinarith [norm_nonneg q.1.val,norm_nonneg q.2,mul_nonneg hR (add_nonneg (norm_nonneg q.1.val) (norm_nonneg q.2))]
    · nlinarith [le_self_pow₀ h (Nat.ne_of_gt hn),norm_nonneg q.1.val,norm_nonneg q.2]
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hh : (1+‖x‖)^3*(1+‖t‖)^j ≤ (1+r)^(3+j)*D^j := by
    have H₁ := pow_le_pow_left₀ (by positivity : 0 ≤ 1+‖x‖) (add_le_add_right (le_max_left ‖x‖ ‖y‖) 1) 3
    have H₂ := pow_le_pow_left₀ (by positivity) ht' j
    calc
      _ ≤ (1+r)^3*(D*(1+r))^j := mul_le_mul H₁ H₂ (by positivity) (by positivity)
      _ = _ := by rw [pow_add,mul_pow]; ring
  rw [sliceKernel,dif_pos hx,norm_mul,hphase,mul_one]
  change ‖f a y‖ ≤ C*D^j*((1+‖t‖)^j)⁻¹*((1+‖x‖)^3)⁻¹
  rw [← div_eq_mul_inv,le_div_iff₀ (by positivity),← div_eq_mul_inv,le_div_iff₀ (by positivity),mul_assoc]
  calc
    _ ≤ ‖f a y‖*((1+r)^(3+j)*D^j) := mul_le_mul_of_nonneg_left hh (norm_nonneg _)
    _ ≤ _ := by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (H a y) (by positivity)

private theorem slice_analysis (μ : Measure K) (hint : Integrable (fun x : K => ((1+‖x‖)^3)⁻¹) μ)
    (hf : RapidLineChart f) (hc : Continuous (Function.uncurry phase)) (hphase : ∀ x a, ‖phase x a‖ = 1)
    {n : ℕ} (hn : 1 ≤ n) (hc' : Continuous p) (hp : ∀ t, ‖p t‖ = ‖t‖^n) :
    let G := sliceKernel f phase p
    let I (q : Kˣ × K) (t : K) := ∫ x, G q t x ∂μ
    (∀ q t, Integrable (G q t) μ) ∧ Continuous (Function.uncurry I) ∧
      ∀ j : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ q t, ‖I q t‖ ≤ B*(2+‖q.1.val‖+‖q.2‖)^j*((1+‖t‖)^j)⁻¹ := by
  letI : FirstCountableTopology Kˣ := Units.isEmbedding_val₀.firstCountableTopology
  dsimp only
  obtain ⟨A,hA,ha⟩ := kernel_bound hf hphase hn hp 0
  simp only [pow_zero,inv_one,mul_one] at ha
  have hi q t := (hint.const_mul A).mono' (kernel_measurable hf.1 hc q t).aestronglyMeasurable
    (.of_forall (ha q t))
  refine ⟨hi,?_,?_⟩
  · change Continuous (fun z : (Kˣ × K) × K => ∫ x, sliceKernel f phase p z.1 z.2 x ∂μ)
    apply continuous_of_dominated (F := fun (z : (Kˣ × K) × K) x => sliceKernel f phase p z.1 z.2 x) (μ := μ) (bound := fun x : K => A*((1+‖x‖)^3)⁻¹)
      (fun z => (hi z.1 z.2).aestronglyMeasurable) (fun z => .of_forall (ha z.1 z.2)) (hint.const_mul A)
    filter_upwards with x
    by_cases hx : x ≠ 0
    · simp only [sliceKernel,dif_pos hx]
      apply Continuous.mul
      · apply hf.1.comp (continuous_const.prodMk _)
        fun_prop (disch := exact fun z => z.1.1.ne_zero)
      · exact hc.comp (continuous_const.prodMk (continuous_fst.comp continuous_fst))
    · simpa only [sliceKernel,dif_neg hx] using (continuous_const (y := (0:ℂ)) : Continuous (fun _ : (Kˣ × K) × K => (0:ℂ)))
  · intro j
    obtain ⟨C,hC,H⟩ := kernel_bound hf hphase hn hp j
    let V := ∫ x : K, ((1+‖x‖)^3)⁻¹ ∂μ
    have hV : 0 ≤ V := integral_nonneg (fun _ => by positivity)
    refine ⟨C*V,mul_nonneg hC hV,fun q t => ?_⟩
    have hi' := norm_integral_le_of_norm_le (hint.const_mul (C*(2+‖q.1.val‖+‖q.2‖)^j*((1+‖t‖)^j)⁻¹))
      (.of_forall (H q t))
    exact hi'.trans_eq (by rw [integral_const_mul]; dsimp only [V]; ring)

/-- Joint continuity and rapid decay in the line parameter, uniform on every
compact subset of the output chart. The coordinates in P are chart coordinates. -/
def RapidRadonValues {K P : Type} [NormedField K] [TopologicalSpace P] (R : P → K → ℂ) : Prop :=
  Continuous (Function.uncurry R) ∧ ∀ T : Set P, IsCompact T → ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ q ∈ T, ∀ t, ‖R q t‖ ≤ C*((1+‖t‖)^j)⁻¹

omit [MeasurableSpace K] [BorelSpace K] in
theorem RapidRadonValues.comp {P Q : Type} [TopologicalSpace P] [TopologicalSpace Q]
    {R : P → K → ℂ} (hR : RapidRadonValues R) (i : Q → P) (hi : Continuous i) :
    RapidRadonValues (fun q t => R (i q) t) := by
  constructor
  · exact hR.1.comp ((hi.comp (continuous_fst : Continuous (Prod.fst : Q × K → Q))).prodMk continuous_snd)
  · intro T hT j
    obtain ⟨C,hC,H⟩ := hR.2 (i '' T) (hT.image hi) j
    exact ⟨C,hC,fun q hq t => H (i q) ⟨q,hq,rfl⟩ t⟩

private theorem normalize_slice (μ : Measure K) (hint : Integrable (fun x : K => ((1+‖x‖)^3)⁻¹) μ)
    (hf : RapidLineChart f) (hc : Continuous (Function.uncurry phase)) (hphase : ∀ x a, ‖phase x a‖ = 1)
    {n : ℕ} (hn : 1 ≤ n) (hc' : Continuous p) (hp : ∀ t, ‖p t‖ = ‖t‖^n)
    (m : Kˣ → ℝ) (hm : Continuous m) (hm' : ∀ a, 0 < m a) :
    let G := sliceKernel f phase p
    (∀ q t, Integrable (G q t) μ) ∧ RapidRadonValues (fun q t => (∫ x, G q t x ∂μ)/(m q.1 : ℂ)) := by
  obtain ⟨hi,hi',hB⟩ := slice_analysis μ hint hf hc hphase hn hc' hp
  refine ⟨hi,hi'.div (Complex.continuous_ofReal.comp (hm.comp (continuous_fst.comp continuous_fst)))
    (fun z => Complex.ofReal_ne_zero.mpr (hm' z.1.1).ne'),?_⟩
  intro T hT j
  obtain ⟨B,hB₀,H⟩ := hB j
  let A (q : Kˣ × K) : ℝ := B*(2+‖q.1.val‖+‖q.2‖)^j/m q.1
  have hA : Continuous A := by dsimp [A]; fun_prop (disch := exact fun q => (hm' q.1).ne')
  obtain ⟨C,hC⟩ := hT.bddAbove_image hA.continuousOn
  refine ⟨max C 0,le_max_right ..,fun q hq t => ?_⟩
  have h := div_le_div_of_nonneg_right (H q t) (hm' q.1).le
  rw [norm_div,Complex.norm_real,Real.norm_of_nonneg (hm' _).le]
  apply h.trans
  calc
    _ = A q * ((1+‖t‖)^j)⁻¹ := by dsimp [A]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right ((hC (mem_image_of_mem _ hq)).trans (le_max_left ..)) (by positivity)

theorem RapidRadonValues.integrable {P : Type} [TopologicalSpace P] {R : P → K → ℂ} (hR : RapidRadonValues R)
    (μ : Measure K) (hint : Integrable (fun x : K => ((1+‖x‖)^3)⁻¹) μ) (q : P) : Integrable (R q) μ := by
  obtain ⟨C,_,hC⟩ := hR.2 {q} isCompact_singleton 3
  exact (hint.const_mul C).mono' (hR.1.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    (.of_forall (hC q rfl))

/-- A compact family of rapidly decreasing line slices has uniformly bounded
Fourier integrals, jointly continuous in the output vector and frequency. -/
theorem RapidRadonValues.fourier {P : Type} [TopologicalSpace P] [FirstCountableTopology P]
    [WeaklyLocallyCompactSpace P] {R : P → K → ℂ} (hR : RapidRadonValues R)
    (μ : Measure K) (hint : Integrable (fun x : K => ((1+‖x‖)^3)⁻¹) μ)
    {ψ : K → ℂ} (hc : Continuous ψ) (hψ : ∀ x, ‖ψ x‖ = 1) :
    let H (q : P) (u : K) := ∫ t, R q t * ψ (u*t) ∂μ
    Continuous (Function.uncurry H) ∧ ∀ T : Set P, IsCompact T → ∃ M : ℝ, 0 ≤ M ∧ ∀ q ∈ T, ∀ u, ‖H q u‖ ≤ M := by
  let G (z : P × K) (t : K) := R z.1 t * ψ (z.2*t)
  have hmeas z : AEStronglyMeasurable (G z) μ :=
    ((hR.1.comp (continuous_const.prodMk continuous_id)).mul (hc.comp (continuous_const.mul continuous_id))).aestronglyMeasurable
  have hn (z : P × K) (t : K) : ‖G z t‖ = ‖R z.1 t‖ := by simp only [G,norm_mul,hψ,mul_one]
  constructor
  · apply continuous_iff_continuousAt.mpr
    intro z
    obtain ⟨T,hT,hz⟩ := exists_compact_mem_nhds z.1
    obtain ⟨C,_,H⟩ := hR.2 T hT 3
    refine continuousAt_of_dominated (F := G) (μ := μ) (bound := fun t => C*((1+‖t‖)^3)⁻¹)
      (.of_forall hmeas) ?_ (hint.const_mul C) ?_
    · exact ((continuous_fst.tendsto z).eventually hz).mono (fun q hq => .of_forall fun t => (hn q t).trans_le (H q.1 hq t))
    · exact .of_forall fun t => ((hR.1.comp (continuous_fst.prodMk (continuous_const (y := t)))).mul
        (hc.comp (continuous_snd.mul_const t))).continuousAt
  · intro T hT
    obtain ⟨C,hC,H⟩ := hR.2 T hT 3
    refine ⟨∫ t : K, C*((1+‖t‖)^3)⁻¹ ∂μ,integral_nonneg (fun t : K => mul_nonneg hC (inv_nonneg.mpr (pow_nonneg (by positivity) 3))),?_⟩
    intro q hq u
    exact norm_integral_le_of_norm_le (hint.const_mul C) (.of_forall fun t => (hn (q,u) t).trans_le (H q hq t))

end Slice

namespace Datum
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

private theorem arch_test_lineCharts (w : InfinitePlace F) {f : Charts (LocalField F (.inl w))}
    (hf : f ∈ d.testSet (.inl w)) : RapidLineChart f.1 ∧ RapidLineChart (fun b a => f.2 a b) := by
  by_cases hw : w.IsReal
  · exact archTest_lineCharts _ (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw)
      (by simpa only [testSet,dif_pos hw] using! hf.2)
  · exact archTest_lineCharts _ (InfinitePlace.Completion.isometry_extensionEmbedding w)
      (by simpa only [testSet,dif_neg hw] using! hf.2)

omit [NeZero n] in
/-- An integrable majorant at every infinite place, in the ordinary metric norm. -/
theorem arch_integrable_inv_cube (w : InfinitePlace F) :
    Integrable (fun x : LocalField F (.inl w) => ((1+‖x‖)^3)⁻¹) (selfDual F d.character (.inl w)) := by
  letI : MeasurableSpace w.Completion := borel _
  letI : BorelSpace w.Completion := ⟨rfl⟩
  let μ : Measure w.Completion := selfDual F d.character (.inl w)
  letI : μ.IsAddHaarMeasure := (existsUnique_selfDual F d.character (.inl w)).exists.choose_spec.1
  have pull {L : Type} [NormedField L] [NormedAlgebra ℝ L] [FiniteDimensional ℝ L]
      [MeasurableSpace L] [BorelSpace L] [SecondCountableTopology L] (e : w.Completion ≃+* L)
      (he : Isometry e) (hd : (Module.finrank ℝ L : ℝ) < 3) :
      Integrable (fun x : w.Completion => ((1+‖x‖)^3)⁻¹) μ := by
    let i : w.Completion ≃ᵢ L := ⟨e.toEquiv,he⟩
    letI : (μ.map e).IsAddHaarMeasure := e.toAddEquiv.isAddHaarMeasure_map μ he.continuous i.symm.continuous
    have h := (integrable_one_add_norm (μ := μ.map e) hd)
    have heq (x : L) : (1+‖x‖)^(-(3:ℝ)) = ((1+‖x‖)^3)⁻¹ := by rw [Real.rpow_neg (by positivity),show (3 : ℝ) = (3 : ℕ) from rfl, Real.rpow_natCast]
    simp_rw [heq] at h
    have H := (integrable_map_measure (g := fun x : L => ((1+‖x‖)^3)⁻¹)
      (by fun_prop) he.continuous.aemeasurable).mp h
    simpa only [Function.comp_def,he.norm_map_of_map_zero e.map_zero] using H
  by_cases hw : w.IsReal
  · exact pull (InfinitePlace.Completion.ringEquivRealOfIsReal hw) (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw) (by norm_num)
  · exact pull (InfinitePlace.Completion.ringEquivComplexOfIsComplex (InfinitePlace.not_isReal_iff_isComplex.mp hw)) (InfinitePlace.Completion.isometry_extensionEmbedding w) (by norm_num)

set_option maxHeartbeats 800000 in
/-- Lemma 4.2(i) on archimedean test sections. The two inner integrals converge
absolutely, and the Radon slices are jointly continuous and rapidly decreasing
in the line parameter, uniformly on compact sets of output vectors. -/
theorem arch_test_radon (w : InfinitePlace F) {f : Charts (LocalField F (.inl w))}
    (hf : f ∈ d.testSet (.inl w)) :
    let v : Place F := .inl w
    let K := LocalField F v
    let dx := selfDual F d.character v
    let R := radon n (d.symbol v) (modulus F v) dx f
    (∀ (a : Kˣ) (b t : K), Integrable (fun x : K => if hx : x ≠ 0 then
      f.1 (Units.mk0 x hx) ((x*b-t^n)/a.val) * d.symbol v (Units.mk0 x hx) (-a) else 0) dx) ∧
    (∀ (a : K) (b : Kˣ) (t : K), Integrable (fun y : K => if hy : y ≠ 0 then
      f.2 ((a*y+t^n)/b.val) (Units.mk0 y hy) * d.symbol v (Units.mk0 y hy) b * d.symbol v (-1) b else 0) dx) ∧
    RapidRadonValues (fun (q : Kˣ × K) t => (R t).1 q.1 q.2) ∧
    RapidRadonValues (fun (q : K × Kˣ) t => (R t).2 q.1 q.2) := by
  let v : Place F := .inl w
  let K := LocalField F v
  let dx := selfDual F d.character v
  obtain ⟨hx,hy⟩ := d.arch_test_lineCharts w hf
  let m (a : Kˣ) := ‖a.val‖^w.mult
  have hm : Continuous m := Units.continuous_val.norm.pow _
  have hm' (a : Kˣ) : 0 < m a := pow_pos (norm_pos_iff.mpr a.ne_zero) _
  let S := d.symbol v
  have hs := d.continuous_symbol v
  have hneg : Continuous (fun a : Kˣ => -a) := Units.isEmbedding_val₀.continuous_iff.mpr Units.continuous_val.neg
  have cx : Continuous (Function.uncurry (fun x a : Kˣ => S x (-a))) :=
    hs.comp (continuous_fst.prodMk (hneg.comp continuous_snd))
  have cy : Continuous (Function.uncurry (fun y b : Kˣ => S y b * S (-1) b)) :=
    hs.mul (hs.comp (continuous_const.prodMk continuous_snd))
  obtain ⟨ix,X⟩ := normalize_slice dx (d.arch_integrable_inv_cube w) hx cx (fun x a => d.norm_symbol v x (-a))
    (NeZero.pos n) (show Continuous (fun t : K => -(t^n)) by fun_prop) (fun t => by rw [norm_neg,norm_pow]) m hm hm'
  obtain ⟨iy,Y⟩ := normalize_slice dx (d.arch_integrable_inv_cube w) hy cy
    (fun x a => by simp [S]) (NeZero.pos n) (show Continuous (fun t : K => t^n) by fun_prop) (fun t => norm_pow t n) m hm hm'
  refine ⟨fun a b t => ?_,fun a b t => ?_,?_,?_⟩
  · have h := ix (a,b) t
    unfold sliceKernel at h
    simpa only [← sub_eq_add_neg] using! h
  · have h := iy (b,a) t
    unfold sliceKernel at h
    simpa only [mul_comm _ a,← mul_assoc] using! h
  · simpa only [radon,sliceKernel,← sub_eq_add_neg] using! X
  · let R := radon n (d.symbol v) (modulus F v) dx f
    have hY : RapidRadonValues (fun (q : Kˣ × K) t => (R t).2 q.2 q.1) := by
      simpa only [R,radon,sliceKernel,mul_comm _ (Prod.snd _),← mul_assoc] using! Y
    exact hY.comp (Prod.swap : K × Kˣ → Kˣ × K) continuous_swap

theorem arch_test_integrable_slices (w : InfinitePlace F) {f : Charts (LocalField F (.inl w))}
    (hf : f ∈ d.testSet (.inl w)) :
    let v : Place F := .inl w
    let dx := selfDual F d.character v
    let R := radon n (d.symbol v) (modulus F v) dx f
    (∀ a b, Integrable (fun t => (R t).1 a b) dx) ∧ (∀ a b, Integrable (fun t => (R t).2 a b) dx) := by
  obtain ⟨_,_,hx,hy⟩ := d.arch_test_radon w hf
  exact ⟨fun a b => hx.integrable _ (d.arch_integrable_inv_cube w) (a,b),
    fun a b => hy.integrable _ (d.arch_integrable_inv_cube w) (a,b)⟩

/-- The two outer integrals defining the metaplectic transform of a test
section converge absolutely at every place. -/
theorem integrable_test_transform (v : Place F) {f : Charts (LocalField F v)} (hf : f ∈ d.testSet v) :
    let dx := selfDual F d.character v
    let R := radon n (d.symbol v) (modulus F v) dx f
    (∀ q : (LocalField F v)ˣ × LocalField F v,
      Integrable (fun t => d.character.localValue F v t * (R t).1 q.1 q.2) dx) ∧
    (∀ q : LocalField F v × (LocalField F v)ˣ,
      Integrable (fun t => d.character.localValue F v t * (R t).2 q.1 q.2) dx) := by
  cases v with
  | inr p => exact d.integrable_finiteTest_transform p hf
  | inl w =>
    let v : Place F := .inl w
    let μ := selfDual F d.character v
    have weight {g : LocalField F v → ℂ} (h : Integrable g μ) :
        Integrable (fun t => d.character.localValue F v t * g t) μ := by
      apply h.norm.mono' ((d.character.continuous_localValue v).aestronglyMeasurable.mul h.aestronglyMeasurable)
      exact .of_forall fun t => by rw [Pi.mul_apply,norm_mul,d.character.norm_localValue,one_mul]
    obtain ⟨hx,hy⟩ := d.arch_test_integrable_slices w hf
    exact ⟨fun q => weight (hx q.1 q.2),fun q => weight (hy q.1 q.2)⟩

end Datum
end MetaplecticPoisson
