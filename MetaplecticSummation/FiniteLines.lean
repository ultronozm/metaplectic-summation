import MetaplecticSummation.LocalSymbols

noncomputable section
namespace MetaplecticPoisson

open MeasureTheory Filter Set
open scoped Topology
open Classical
variable {K : Type} [NormedField K] {f : Charts K}

/-- Absolute value of a section, extended by zero at the deleted origin. -/
def chartNorm (f : Charts K) (p : K × K) : ℝ :=
  if p.1 = 0 then ‖yChart f p‖ else ‖xChart f p‖

private theorem chartNorm_eq_y {h : Kˣ → Kˣ → ℂ} (hu : ∀ x y, ‖h x y‖ = 1)
    (hf : Glues h f) (x : K) (y : Kˣ) : chartNorm f (x, y) = ‖f.2 x y‖ := by
  by_cases hx : x = 0
  · simp [chartNorm, hx, yChart, y.ne_zero]
  · simp [chartNorm, xChart, hx, hf (Units.mk0 x hx) y, hu]

private theorem xChart_continuousOn (hf : Continuous (fun p : Kˣ × K => f.1 p.1 p.2)) :
    ContinuousOn (xChart f) {p | p.1 ≠ 0} := by
  rw [continuousOn_iff_continuous_restrict]
  let g (p : {z : K × K // z.1 ≠ 0}) := Units.mk0 p.val.1 p.property
  have hg : Continuous g :=
    Units.isEmbedding_val₀.continuous_iff.mpr (continuous_fst.comp continuous_subtype_val)
  refine (hf.comp (hg.prodMk (continuous_snd.comp continuous_subtype_val))).congr ?_
  intro z
  simp [xChart, g, z.property]

private theorem yChart_continuousOn (hf : Continuous (fun p : K × Kˣ => f.2 p.1 p.2)) :
    ContinuousOn (yChart f) {p | p.2 ≠ 0} := by
  rw [continuousOn_iff_continuous_restrict]
  let g (p : {z : K × K // z.2 ≠ 0}) := Units.mk0 p.val.2 p.property
  have hg : Continuous g :=
    Units.isEmbedding_val₀.continuous_iff.mpr (continuous_snd.comp continuous_subtype_val)
  refine (hf.comp ((continuous_fst.comp continuous_subtype_val).prodMk hg)).congr ?_
  intro z
  simp [yChart, g, z.property]

/-- The norm is continuous even across a chart axis. The compact support
away from zero ensures continuity of its extension at the origin. -/
theorem finiteTest_continuous_chartNorm {h : Kˣ → Kˣ → ℂ} (hu : ∀ x y, ‖h x y‖ = 1)
    (gl : Glues h f) (hf : finiteTest f) : Continuous (chartNorm f) := by
  obtain ⟨hx, hy, C, hC, h0, hs⟩ := hf
  rw [continuous_iff_continuousAt]
  intro p
  by_cases h₁ : p.1 ≠ 0
  · have hopen : IsOpen {p : K × K | p.1 ≠ 0} := isOpen_ne_fun continuous_fst (continuous_const (y := (0:K)))
    apply ((xChart_continuousOn hx.continuous).continuousAt (hopen.mem_nhds h₁)).norm.congr_of_eventuallyEq
    filter_upwards [hopen.mem_nhds h₁] with z hz
    simp [chartNorm, hz]
  by_cases h₂ : p.2 ≠ 0
  · have hopen : IsOpen {p : K × K | p.2 ≠ 0} := isOpen_ne_fun continuous_snd (continuous_const (y := (0:K)))
    apply ((yChart_continuousOn hy.continuous).continuousAt (hopen.mem_nhds h₂)).norm.congr_of_eventuallyEq
    filter_upwards [hopen.mem_nhds h₂] with z hz
    simpa [yChart, hz] using chartNorm_eq_y hu gl z.1 (Units.mk0 z.2 hz)
  have hp : p = 0 := Prod.ext (not_ne_iff.mp h₁) (not_ne_iff.mp h₂)
  subst p
  apply (continuousAt_const (y := (0:ℝ))).congr_of_eventuallyEq
  filter_upwards [hC.isClosed.isOpen_compl.mem_nhds h0] with z hz
  simp [chartNorm, (hs z hz).1, (hs z hz).2]

theorem finiteTest_chartNorm_bounded {h : Kˣ → Kˣ → ℂ} (hu : ∀ x y, ‖h x y‖ = 1)
    (gl : Glues h f) (hf : finiteTest f) : ∃ B : ℝ, ∀ z, chartNorm f z ≤ B := by
  obtain ⟨C, hC, _, hs⟩ := hf.2.2
  obtain ⟨B, hB⟩ := hC.bddAbove_image (finiteTest_continuous_chartNorm hu gl hf).continuousOn
  refine ⟨max B 0, fun z => ?_⟩
  by_cases hz : z ∈ C
  · exact (hB (mem_image_of_mem _ hz)).trans (le_max_left ..)
  · simp [chartNorm, (hs z hz).1, (hs z hz).2]

variable [MeasurableSpace K] [BorelSpace K] (dx : Measure K) [IsFiniteMeasureOnCompacts dx]

private theorem integrable_off_zero {g : Kˣ → ℂ} (hg : Continuous g) {B : ℝ}
    (hb : ∀ x, ‖g x‖ ≤ B) {C : Set K} (hc : IsCompact C)
    (hs : ∀ x : Kˣ, (x : K) ∉ C → g x = 0) :
    Integrable (fun x : K => if hx : x ≠ 0 then g (Units.mk0 x hx) else 0) dx := by
  let G (x : K) := if hx : x ≠ 0 then g (Units.mk0 x hx) else 0
  have hm : Measurable G := by
    apply measurable_of_measurable_on_compl_singleton 0
    let lift (z : {x : K // x ≠ 0}) := Units.mk0 z.val z.property
    have hLift : Continuous lift := Units.isEmbedding_val₀.continuous_iff.mpr continuous_subtype_val
    exact ((hg.comp hLift).congr (fun z => by simp [G, lift, z.property])).measurable
  change Integrable G dx
  apply IntegrableOn.integrable_of_forall_notMem_eq_zero (s := C)
  · apply (integrableOn_const (C := max B 0) hc.measure_lt_top.ne).mono' hm.aestronglyMeasurable
    filter_upwards with x
    by_cases hx : x ≠ 0
    · simpa [G, hx] using (hb (Units.mk0 x hx)).trans (le_max_left B 0)
    · simp [G, hx]
  · intro x hx
    by_cases h0 : x ≠ 0
    · simp [G, h0, hs (Units.mk0 x h0) hx]
    · simp [G, h0]

/-- Absolute convergence in the X chart for a test function on the punctured plane. -/
theorem integrable_radon_x {h : Kˣ → Kˣ → ℂ} (hu : ∀ x y, ‖h x y‖ = 1)
    (hcont : ∀ a, Continuous (fun x => h x a)) (gl : Glues h f) (hf : finiteTest f)
    (n : ℕ) (a : Kˣ) (b t : K) :
    Integrable (fun x : K => if hx : x ≠ 0 then
      f.1 (Units.mk0 x hx) ((x*b-t^n)/a) * h (Units.mk0 x hx) (-a) else 0) dx := by
  obtain ⟨C, hC, _, hs⟩ := hf.2.2
  obtain ⟨B, hB⟩ := finiteTest_chartNorm_bounded hu gl hf
  let y (x : K) := (x*b-t^n)/(a : K)
  apply integrable_off_zero dx (g := fun x => f.1 x (y x) * h x (-a)) (B := B)
      (C := Prod.fst '' C)
  · apply Continuous.mul _ (hcont _)
    exact hf.1.continuous.comp (continuous_id.prodMk (show Continuous (fun x : Kˣ => y x) by dsimp [y]; fun_prop))
  · intro x
    simpa [norm_mul, hu, chartNorm, xChart, x.ne_zero] using hB ((x : K), y x)
  · exact hC.image continuous_fst
  · intro x hx
    have hp : ((x : K), y x) ∉ C := fun hz => hx ⟨_, hz, rfl⟩
    have hz := (hs _ hp).1
    simp [xChart, x.ne_zero] at hz
    simp [hz]

/-- Absolute convergence in the Y chart, including the extra symbol at -1. -/
theorem integrable_radon_y {h : Kˣ → Kˣ → ℂ} (hu : ∀ x y, ‖h x y‖ = 1)
    (hcont : ∀ a, Continuous (fun y => h y a)) (gl : Glues h f) (hf : finiteTest f)
    (n : ℕ) (a : K) (b : Kˣ) (t : K) :
    Integrable (fun y : K => if hy : y ≠ 0 then
      f.2 ((a*y+t^n)/b) (Units.mk0 y hy) * h (Units.mk0 y hy) b * h (-1) b else 0) dx := by
  obtain ⟨C, hC, _, hs⟩ := hf.2.2
  obtain ⟨B, hB⟩ := finiteTest_chartNorm_bounded hu gl hf
  let x (y : K) := (a*y+t^n)/(b : K)
  apply integrable_off_zero dx (g := fun y => f.2 (x y) y * h y b * h (-1) b) (B := B)
      (C := Prod.snd '' C)
  · apply Continuous.mul _ continuous_const
    apply Continuous.mul _ (hcont _)
    exact hf.2.1.continuous.comp ((show Continuous (fun y : Kˣ => x y) by dsimp [x]; fun_prop).prodMk continuous_id)
  · intro y
    simpa [norm_mul, hu, chartNorm_eq_y hu gl] using hB (x y, (y : K))
  · exact hC.image continuous_snd
  · intro y hy
    have hp : (x y, (y : K)) ∉ C := fun hz => hy ⟨_, hz, rfl⟩
    have hz := (hs _ hp).2
    simp [yChart, y.ne_zero] at hz
    simp [hz]

private theorem continuous_line_integral {P : Type*} [TopologicalSpace P] [FirstCountableTopology P]
    {g : P → K → ℂ} {C : Set K} (hc : IsCompact C) {B : ℝ}
    (hi : ∀ p, Integrable (g p) dx) (hb : ∀ p x, ‖g p x‖ ≤ max B 0)
    (hs : ∀ p x, x ∉ C → g p x = 0) (hp : ∀ x, Continuous fun p => g p x) :
    Continuous fun p => ∫ x, g p x ∂dx := by
  apply continuous_of_dominated (bound := C.indicator (fun _ => max B 0))
    (fun p => (hi p).aestronglyMeasurable)
  · intro p
    filter_upwards with x
    by_cases hx : x ∈ C
    · simpa [hx] using hb p x
    · simp [hx, hs p x hx]
  · exact (integrableOn_const hc.measure_lt_top.ne).integrable_indicator hc.measurableSet
  · exact Filter.Eventually.of_forall hp

/-- Joint continuity in the output vector and the line parameter, with
the finite-place normalization of the measure. -/
theorem finiteTest_continuous_radon {h : Kˣ → Kˣ → ℂ} (hu : ∀ x y, ‖h x y‖ = 1)
    (hc : Continuous (fun p : Kˣ × Kˣ => h p.1 p.2))
    (gl : Glues h f) (hf : finiteTest f) (n : ℕ) :
    (Continuous fun p : (Kˣ × K) × K => (radon n h norm dx f p.2).1 p.1.1 p.1.2) ∧
    (Continuous fun p : (K × Kˣ) × K => (radon n h norm dx f p.2).2 p.1.1 p.1.2) := by
  obtain ⟨C, hC, _, hs⟩ := hf.2.2
  obtain ⟨B, hB⟩ := finiteTest_chartNorm_bounded hu gl hf
  have hc' (a : Kˣ) : Continuous (fun x => h x a) := hc.comp (continuous_id.prodMk continuous_const)
  letI : FirstCountableTopology Kˣ := Units.isEmbedding_val₀.firstCountableTopology
  dsimp only [radon]
  constructor
  · let g (p : (Kˣ × K) × K) (x : K) := if hx : x ≠ 0 then
        f.1 (Units.mk0 x hx) ((x*p.1.2-p.2^n)/(p.1.1 : K)) * h (Units.mk0 x hx) (-p.1.1) else 0
    change Continuous (fun p => (∫ x, g p x ∂dx) / (‖(p.1.1 : K)‖ : ℂ))
    refine Continuous.div ?_ (by fun_prop) (fun p => by simp)
    refine continuous_line_integral dx (g := g) (hC.image continuous_fst) (B := B)
      (fun p => integrable_radon_x dx hu hc' gl hf n p.1.1 p.1.2 p.2) ?_ ?_ ?_
    · intro p x
      dsimp only [g]
      split_ifs with hx
      · simpa [chartNorm, xChart, hx, norm_mul, hu] using
          (hB (x, (x*p.1.2-p.2^n)/(p.1.1 : K))).trans (le_max_left B 0)
      · simp
    · intro p x hx
      dsimp only [g]
      split_ifs with h0
      · have hz := (hs (x, (x*p.1.2-p.2^n)/(p.1.1 : K)) (fun hz => hx ⟨_, hz, rfl⟩)).1
        simp [xChart, h0] at hz
        simp [hz]
      · rfl
    · intro x
      dsimp only [g]
      by_cases hx : x ≠ 0
      · simp only [dif_pos hx]
        refine (hf.1.continuous.comp (continuous_const.prodMk ?_)).mul (hc.comp (continuous_const.prodMk ?_))
        · fun_prop (disch := simp)
        · apply Units.isEmbedding_val₀.continuous_iff.mpr
          change Continuous fun p : (Kˣ × K) × K => -(p.1.1 : K)
          fun_prop
      · simp [hx, continuous_const]
  · let g (p : (K × Kˣ) × K) (x : K) := if hy : x ≠ 0 then
        f.2 ((p.1.1*x+p.2^n)/(p.1.2 : K)) (Units.mk0 x hy) * h (Units.mk0 x hy) p.1.2 *
          h (-1) p.1.2 else 0
    change Continuous (fun p => (∫ x, g p x ∂dx) / (‖(p.1.2 : K)‖ : ℂ))
    refine Continuous.div ?_ (by fun_prop) (fun p => by simp)
    refine continuous_line_integral dx (g := g) (hC.image continuous_snd) (B := B)
      (fun p => integrable_radon_y dx hu hc' gl hf n p.1.1 p.1.2 p.2) ?_ ?_ ?_
    · intro p y
      dsimp only [g]
      split_ifs with hy
      · rw [norm_mul, norm_mul, hu, hu, mul_one, mul_one,
          ← chartNorm_eq_y hu gl _ (Units.mk0 y hy)]
        exact (hB _).trans (le_max_left B 0)
      · simp
    · intro p y hy
      dsimp only [g]
      split_ifs with h0
      · have hz := (hs ((p.1.1*y+p.2^n)/(p.1.2 : K), y) (fun hz => hy ⟨_, hz, rfl⟩)).2
        simp [yChart, h0] at hz
        simp [hz]
      · rfl
    · intro y
      dsimp only [g]
      by_cases hy : y ≠ 0
      · simp only [dif_pos hy]
        refine ((hf.2.1.continuous.comp (Continuous.prodMk ?_ continuous_const)).mul
            (hc.comp (continuous_const.prodMk ?_))).mul (hc.comp (continuous_const.prodMk ?_))
        · fun_prop (disch := simp)
        · fun_prop
        · fun_prop
      · simp [hy, continuous_const]

omit [BorelSpace K] [IsFiniteMeasureOnCompacts dx] in
/-- Uniform vanishing in the line parameter over a compact set of output vectors.
The bound uses the determinant on the product of the two compact sets. -/
theorem finiteTest_radon_vanishes (hf : finiteTest f) (n : ℕ) (h : Kˣ → Kˣ → ℂ)
    (m : K → ℝ) {T : Set (K × K)} (hT : IsCompact T) :
    ∃ B : ℝ, ∀ t : K, B < ‖t‖ ^ n →
      (∀ (a : Kˣ) (b : K), ((a : K), b) ∈ T → (radon n h m dx f t).1 a b = 0) ∧
      (∀ (a : K) (b : Kˣ), (a, (b : K)) ∈ T → (radon n h m dx f t).2 a b = 0) := by
  obtain ⟨C, hC, _, hs⟩ := hf.2.2
  let det (z : (K × K) × (K × K)) := z.1.1 * z.2.2 - z.1.2 * z.2.1
  have hc : Continuous (fun z => ‖det z‖) := by dsimp [det]; fun_prop
  obtain ⟨B, hB⟩ := (hC.prod hT).bddAbove_image hc.continuousOn
  refine ⟨B, fun t ht => ?_⟩
  have outside (v w : K × K) (hw : w ∈ T) (he : det (v,w) = t^n) : v ∉ C := by
    intro hv
    have hle := hB (mem_image_of_mem (fun z => ‖det z‖) (show (v,w) ∈ C ×ˢ T from ⟨hv, hw⟩))
    exact ht.not_ge (by simpa [he] using hle)
  constructor
  · intro a b hw
    dsimp [radon]
    suffices ∀ x : K, (if hx : x ≠ 0 then
        f.1 (Units.mk0 x hx) ((x*b-t^n)/a) * h (Units.mk0 x hx) (-a) else 0) = 0 by
      simp [this]
    intro x
    split_ifs with hx
    · have hz := (hs _ (outside (x, (x*b-t^n)/a) _ hw (by
          dsimp [det]; field_simp; ring))).1
      simpa [xChart, hx] using mul_eq_zero_of_left hz (h (Units.mk0 x hx) (-a))
    · rfl
  · intro a b hw
    dsimp [radon]
    suffices ∀ y : K, (if hy : y ≠ 0 then
        f.2 ((a*y+t^n)/b) (Units.mk0 y hy) * h (Units.mk0 y hy) b * h (-1) b else 0) = 0 by
      simp [this]
    intro y
    split_ifs with hy
    · have hz := (hs _ (outside ((a*y+t^n)/b, y) _ hw (by
          dsimp [det]; field_simp; ring))).2
      simp [yChart, hy] at hz
      simp [hz]
    · rfl

namespace Datum
open NumberField IsDedekindDomain
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

/-- Absolute convergence in Definition 4.1 for the number-field test space
at every finite place and every line parameter. -/
theorem finiteTest_line_integrals (p : HeightOneSpectrum (𝓞 F))
    {φ : Charts (LocalField F (.inr p))} (hφ : φ ∈ d.testSet (.inr p))
    (t : LocalField F (.inr p)) :
    let v : Place F := .inr p
    let dx := selfDual F d.character v
    (∀ (a : (LocalField F v)ˣ) (b : LocalField F v),
      Integrable (fun x : LocalField F v => if hx : x ≠ 0 then
        φ.1 (Units.mk0 x hx) ((x*b-t^n)/a) * d.symbol v (Units.mk0 x hx) (-a) else 0) dx) ∧
    (∀ (a : LocalField F v) (b : (LocalField F v)ˣ),
      Integrable (fun y : LocalField F v => if hy : y ≠ 0 then
        φ.2 ((a*y+t^n)/b) (Units.mk0 y hy) * d.symbol v (Units.mk0 y hy) b *
          d.symbol v (-1) b else 0) dx) := by
  let v : Place F := .inr p
  let dx := selfDual F d.character v
  letI : dx.IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  have ht : Glues (d.symbol v) φ ∧ finiteTest φ := hφ
  have hc (a : (LocalField F v)ˣ) : Continuous (fun x => d.symbol v x a) :=
    (d.continuous_symbol v).comp (continuous_id.prodMk continuous_const)
  exact ⟨fun a b => integrable_radon_x dx (d.norm_symbol v) hc ht.1 ht.2 n a b t,
    fun a b => integrable_radon_y dx (d.norm_symbol v) hc ht.1 ht.2 n a b t⟩

/-- The two Radon charts attached to the given datum vary continuously in all
parameters for finite-place test functions. -/
theorem continuous_finiteTest_lines (p : HeightOneSpectrum (𝓞 F))
    {φ : Charts (LocalField F (.inr p))} (hφ : φ ∈ d.testSet (.inr p)) :
    let v : Place F := .inr p
    let R := radon n (d.symbol v) (modulus F v) (selfDual F d.character v) φ
    (Continuous fun z : ((LocalField F v)ˣ × LocalField F v) × LocalField F v =>
      (R z.2).1 z.1.1 z.1.2) ∧
    (Continuous fun z : (LocalField F v × (LocalField F v)ˣ) × LocalField F v =>
      (R z.2).2 z.1.1 z.1.2) := by
  let v : Place F := .inr p
  let dx := selfDual F d.character v
  letI : dx.IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  have ht : Glues (d.symbol v) φ ∧ finiteTest φ := hφ
  exact finiteTest_continuous_radon dx (d.norm_symbol v) (d.continuous_symbol v) ht.1 ht.2 n

end Datum
end MetaplecticPoisson
