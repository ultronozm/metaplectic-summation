import MetaplecticSummation.MultiplicativeMeasure
import MetaplecticSummation.FiniteFourierInversion
import MetaplecticSummation.ArchimedeanFourierSchwartz

/-! The Fourier kernel of the local Jacquet transform (§10). -/
noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField MeasureTheory Filter Set
open scoped Topology ContDiff
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n) (v : Place F)
local notation "K" => LocalField F v
local notation "dx" => selfDual F d.character v

/-- Before composing with the power map, the kernel is the ordinary Fourier
transform of this function, extended by zero at zero. -/
def kernelAmplitude (W : Weight v) (c : Kˣ) (x : K) : ℂ :=
  if h : x ≠ 0 then
    let u := Units.mk0 x h
    W u⁻¹ * d.symbol v u⁻¹ (-c) / (modulus F v x : ℂ)
  else 0

@[simp] theorem kernelAmplitude_unit (W : Weight v) (c u : Kˣ) :
    d.kernelAmplitude v W c u.val = W u⁻¹ * d.symbol v u⁻¹ (-c) / (modulus F v u.val : ℂ) := by
  simp only [kernelAmplitude,dif_pos u.ne_zero,Units.mk0_val]

theorem kernelIntegral_eq_hat (W : Weight v) (c : Kˣ) (t : K) :
    d.kernelIntegral v W c t = d.hat v (d.kernelAmplitude v W c) (-(t^n)/c.val) := by
  unfold kernelIntegral
  rw [← d.lineIntegral_inv]
  unfold lineIntegral hat
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x = 0
  · simp [hx,kernelAmplitude]
  · simp only [kernelAmplitude,dif_pos hx,Units.val_inv_eq_inv_val,Units.val_mk0]
    rw [show -(t^n)/(c.val*x⁻¹) = -(t^n)/c.val*x by field_simp]
    ring

private theorem kernelAmplitude_support (W : Weight v) (hW : HasCompactSupport W) (c : Kˣ) :
    ∃ C : Set K, IsCompact C ∧ 0 ∉ C ∧ ∀ x ∉ C, d.kernelAmplitude v W c x = 0 := by
  let C := (fun u : Kˣ => u⁻¹.val) '' tsupport W
  refine ⟨C,hW.image (Units.continuous_val.comp continuous_inv),?_,?_⟩
  · rintro ⟨u,_,hu⟩
    exact u⁻¹.ne_zero hu
  · intro x hx
    by_cases hz : x = 0
    · simp [hz,kernelAmplitude]
    · let u := Units.mk0 x hz
      have ho : u⁻¹ ∉ tsupport W := fun h => hx ⟨u⁻¹,h,by simp [u]⟩
      rw [kernelAmplitude,dif_pos hz]
      change W u⁻¹ * _ / _ = 0
      rw [image_eq_zero_of_notMem_tsupport ho,zero_mul,zero_div]

section Finite
variable (p : Prime F)
local notation "vp" => (Sum.inr p : Place F)
local notation "L" => LocalField F vp

theorem finite_kernelAmplitude_bruhat {W : Weight (.inr p)}
    (hw : TestWeight (.inr p) W) (c : (LocalField F (.inr p))ˣ) :
    Bruhat (.inr p) (d.kernelAmplitude (.inr p) W c) := by
  letI : NontriviallyNormedField (p.adicCompletion F) := FinitePlace.nontriviallyNormedCompletion p
  letI : NontriviallyNormedField L := inferInstanceAs (NontriviallyNormedField (p.adicCompletion F))
  letI : IsUltrametricDist L := inferInstanceAs (IsUltrametricDist (p.adicCompletion F))
  obtain ⟨C,hC,h₀,hout⟩ := d.kernelAmplitude_support vp W hw.1 c
  refine ⟨?_,HasCompactSupport.intro hC hout⟩
  have hW : IsLocallyConstant W := hw.2
  let g (u : Lˣ) := W u⁻¹ * d.symbol vp u⁻¹ (-c) / (‖u.val‖ : ℂ)
  have hg : IsLocallyConstant g :=
    ((hW.comp_continuous continuous_inv).mul (((d.locallyConstant_unitPairing vp).comp Units.val).comp_continuous
      (continuous_inv.prodMk continuous_const))).div (locallyConstant_norm_units.comp (fun r : ℝ => (r : ℂ)))
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x = 0
  · subst x
    filter_upwards [hC.isClosed.isOpen_compl.mem_nhds h₀] with y hy
    rw [hout y hy,hout 0 h₀]
  · have he := (liftUnit_continuousAt hx).eventually (hg.eventually_eq (liftUnit x))
    filter_upwards [he,eventually_ne_nhds hx] with y hy hn
    simpa only [g,liftUnit,dif_pos hx,dif_pos hn,Units.val_mk0,kernelAmplitude,modulus] using hy

theorem finite_kernelIntegral_bruhat {W : Weight (.inr p)}
    (hw : TestWeight (.inr p) W) (c : (LocalField F (.inr p))ˣ) :
    Bruhat (.inr p) (d.kernelIntegral (.inr p) W c) := by
  letI : NontriviallyNormedField (p.adicCompletion F) := FinitePlace.nontriviallyNormedCompletion p
  letI : NontriviallyNormedField L := inferInstanceAs (NontriviallyNormedField (p.adicCompletion F))
  letI : ProperSpace L := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace (p.adicCompletion F)
  let h := d.hat vp (d.kernelAmplitude vp W c)
  obtain ⟨hl,hc⟩ : IsLocallyConstant h ∧ HasCompactSupport h :=
    d.hat_finite_bruhat p (d.finite_kernelAmplitude_bruhat p hw c)
  let f (x : L) := -(x^n)/c.val
  have he : d.kernelIntegral vp W c = h ∘ f := funext (d.kernelIntegral_eq_hat vp W c)
  rw [he]
  refine ⟨hl.comp_continuous (((continuous_id.pow n).neg).div_const _),?_⟩
  obtain ⟨B,hB⟩ := hc.exists_bound_of_continuousOn (f := id) continuous_id.continuousOn
  apply HasCompactSupport.intro (isCompact_closedBall (0:L) (max 1 (B*‖c.val‖)))
  intro x hx
  change h (f x) = 0
  apply image_eq_zero_of_notMem_tsupport
  intro hh
  apply hx
  rw [Metric.mem_closedBall,dist_zero_right]
  by_cases hx₁ : ‖x‖ ≤ 1
  · exact hx₁.trans (le_max_left ..)
  · have hb := hB (f x) hh
    change ‖-(x^n)/c.val‖ ≤ B at hb
    rw [norm_div,norm_neg,norm_pow,div_le_iff₀ (norm_pos_iff.mpr c.ne_zero)] at hb
    exact ((le_self_pow₀ (le_of_not_ge hx₁) (NeZero.ne n)).trans hb).trans (le_max_right ..)

end Finite

section Arch
variable (w : InfinitePlace F)
local notation "vi" => (Sum.inl w : Place F)
local notation "L₀" => LocalField F vi

private theorem arch_amplitude_coordinates {L : Type} [NormedField L] [NormedAlgebra ℝ L]
    (e : w.Completion ≃+* L) (he : Isometry e)
    (hnorm : ∀ x : L, x ≠ 0 → ContDiffAt ℝ ∞ norm x)
    {W : Weight vi} (hcW : HasCompactSupport W) (hsW : archSmooth e W) (c : L₀ˣ) :
    ∃ g : SchwartzMap L ℂ, ∀ x, d.kernelAmplitude vi W c x = g (e x) := by
  let i : L₀ ≃ᵢ L := ⟨e.toEquiv,he⟩
  let A (z : L) := d.kernelAmplitude vi W c (e.symm z)
  obtain ⟨C,hC,h₀,hout⟩ := d.kernelAmplitude_support vi W hcW c
  let D := e '' C
  have hD : IsCompact D := hC.image he.continuous
  have off (z : L) (hz : z ∉ D) : A z = 0 := hout _ (fun h => hz ⟨_,h,e.apply_symm_apply _⟩)
  have hc : HasCompactSupport A := .intro hD off
  let U (z : L) : L₀ˣ := if h : e.symm z ≠ 0 then Units.mk0 _ h else 1
  let W₀ (z : L) : ℂ := if h : e.symm z ≠ 0 then W (Units.mk0 _ h) else 0
  have smooth : ContDiff ℝ ∞ A := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z = 0
    · subst z
      have hn : 0 ∉ D := by rintro ⟨s,hs,eqn⟩; exact h₀ (e.map_eq_zero_iff.mp eqn ▸ hs)
      apply (contDiffAt_const (c := (0:ℂ))).congr_of_eventuallyEq
      filter_upwards [hD.isClosed.isOpen_compl.mem_nhds hn] with t ht using off t ht
    · have hu : ContinuousAt U z := by
        apply Units.isEmbedding_val₀.tendsto_nhds_iff.mpr
        change Tendsto (fun t => (U t).val) (𝓝 z) (𝓝 (U z).val)
        rw [show (U z).val = e.symm z from by simp only [U,dif_pos ((map_ne_zero e.symm).mpr hz),Units.val_mk0]]
        apply (i.symm.continuous.tendsto z).congr'
        filter_upwards [eventually_ne_nhds hz] with t ht
        change e.symm t = (U t).val
        simp only [U,dif_pos ((map_ne_zero e.symm).mpr ht),Units.val_mk0]
      have near := (hu.inv.prodMk (continuousAt_const (y := -c))).eventually
        (((d.locallyConstant_unitPairing vi).comp Units.val).eventually_eq ((U z)⁻¹,-c))
      have hw : ContDiffAt ℝ ∞ W₀ z⁻¹ := (hsW z⁻¹ (inv_ne_zero hz)).contDiffAt
        (isOpen_compl_singleton.mem_nhds (inv_ne_zero hz))
      have hm := Complex.ofRealCLM.contDiff.contDiffAt.comp z ((hnorm z hz).pow w.mult)
      apply (((hw.comp z (contDiffAt_inv ℝ hz)).mul (contDiffAt_const (c := d.symbol vi (U z)⁻¹ (-c)))).mul
        (hm.inv (Complex.ofReal_ne_zero.mpr (pow_ne_zero _ (norm_ne_zero_iff.mpr hz))))).congr_of_eventuallyEq
      filter_upwards [near,eventually_ne_nhds hz] with t hs ht
      change d.symbol vi (U t)⁻¹ (-c) = d.symbol vi (U z)⁻¹ (-c) at hs
      have ht' := (map_ne_zero e.symm).mpr ht
      have ha : (Units.mk0 (e.symm t : L₀) ht')⁻¹ = Units.mk0 (e.symm t⁻¹) ((map_ne_zero e.symm).mpr (inv_ne_zero ht)) :=
        Units.ext (map_inv₀ e.symm t).symm
      have hn : ‖e.symm t‖ = ‖t‖ := by simpa using (he.norm_map_of_map_zero e.map_zero (e.symm t)).symm
      change d.kernelAmplitude vi W c (e.symm t) = W₀ t⁻¹ * d.symbol vi (U z)⁻¹ (-c) * ((‖t‖^w.mult : ℝ) : ℂ)⁻¹
      rw [← hs]
      rw [show d.kernelAmplitude vi W c (e.symm t) = _ from d.kernelAmplitude_unit vi W c (Units.mk0 _ ht')]
      simp only [U,W₀,dif_pos ht',dif_pos ((map_ne_zero e.symm).mpr (inv_ne_zero ht)),modulus,div_eq_mul_inv]
      exact congrArg₂ (fun (a : L₀ˣ) (r : ℝ) => W a * d.symbol vi (Units.mk0 (e.symm t) ht')⁻¹ (-c) *
        ((r^w.mult : ℝ) : ℂ)⁻¹) ha hn
  exact ⟨hc.toSchwartzMap smooth,fun x => by change _ = d.kernelAmplitude vi W c (e.symm (e x)); rw [e.symm_apply_apply]⟩

theorem arch_kernelAmplitude_bruhat {W : Weight vi} (hw : TestWeight vi W) (c : L₀ˣ) :
    Bruhat vi (d.kernelAmplitude vi W c) := by
  dsimp only [Bruhat]
  split <;> rename_i h
  · apply d.arch_amplitude_coordinates w _ (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal h)
      (fun _ hz => contDiffAt_id.norm ℝ hz) hw.1 _ c
    simpa only [dif_pos h] using hw.2
  · apply d.arch_amplitude_coordinates w _ (InfinitePlace.Completion.isometry_extensionEmbedding w)
      (fun _ hz => contDiffAt_id.norm ℝ hz) hw.1 _ c
    simpa only [dif_neg h] using hw.2
private theorem schwartz_power_coordinates {L : Type} [RCLike L] (e : w.Completion ≃+* L)
    {f : L₀ → ℂ} (g : SchwartzMap L ℂ) (hg : ∀ x, f x = g (e x)) (c : L₀ˣ) :
    ∃ G : SchwartzMap L ℂ, ∀ x : L₀, f (-(x^n)/c.val) = G (e x) := by
  let b := e c.val
  have hb : b ≠ 0 := (map_ne_zero e).mpr c.ne_zero
  let P (z : L) := -(z^n)/b
  have ht : P.HasTemperateGrowth := by simp only [P,div_eq_mul_inv]; fun_prop
  have bound (z : L) : ‖z‖ ≤ (1+‖b‖)*(1+‖P z‖)^1 := by
    rw [pow_one]
    have hn : ‖P z‖*‖b‖ = ‖z‖^n := by
      simp only [P,norm_div,norm_neg,norm_pow,div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hb)]
    by_cases hz : ‖z‖ ≤ 1
    · nlinarith [norm_nonneg b,norm_nonneg (P z),mul_nonneg (norm_nonneg b) (norm_nonneg (P z))]
    · have h := le_self_pow₀ (le_of_not_ge hz) (NeZero.ne n)
      nlinarith [norm_nonneg b,norm_nonneg (P z)]
  refine ⟨SchwartzMap.compCLM ℂ ht ⟨1,1+‖b‖,bound⟩ g, fun x => ?_⟩
  change f (-(x^n)/c.val) = g (-(e x ^n)/e c.val)
  rw [hg]
  apply congrArg g
  calc
    _ = e (-(x^n)) / e c.val := map_div₀ e _ _
    _ = _ := congrArg (· / e c.val) ((map_neg e _).trans (congrArg Neg.neg (map_pow e x n)))

theorem arch_kernelIntegral_bruhat {W : Weight vi} (hw : TestWeight vi W) (c : L₀ˣ) :
    Bruhat vi (d.kernelIntegral vi W c) := by
  have hh := d.arch_hat_bruhat w (d.arch_kernelAmplitude_bruhat w hw c)
  rw [show d.kernelIntegral vi W c = (fun x => d.hat vi (d.kernelAmplitude vi W c) (-(x^n)/c.val)) from
    funext (d.kernelIntegral_eq_hat vi W c)]
  dsimp only [Bruhat] at hh ⊢
  split at hh <;> rename_i h
  · rw [dif_pos h]
    obtain ⟨g,hg⟩ := hh
    exact schwartz_power_coordinates w _ g hg c
  · rw [dif_neg h]
    obtain ⟨g,hg⟩ := hh
    exact schwartz_power_coordinates w _ g hg c
end Arch

/-- The kernel H_c of Proposition 10.8 is Schwartz–Bruhat at every place. -/
theorem kernelIntegral_bruhat {W : Weight v} (hw : TestWeight v W) (c : Kˣ) :
    Bruhat v (d.kernelIntegral v W c) := by
  cases v with
  | inl w => exact d.arch_kernelIntegral_bruhat w hw c
  | inr p => exact d.finite_kernelIntegral_bruhat p hw c

theorem integrable_kernelFourier {W : Weight v} (hw : TestWeight v W) (c : Kˣ) (freq : K) :
    Integrable (fun t => d.kernelIntegral v W c t * d.character.localValue F v (freq*t)) dx := by
  exact d.integrable_phase v (Bruhat.integrable d (d.kernelIntegral_bruhat v hw c)) freq

private theorem archSmooth_continuous {w : InfinitePlace F} {L : Type} [NormedField L] [NormedAlgebra ℝ L]
    (e : w.Completion ≃+* L) (he : Continuous e) {W : Weight (.inl w)} (h : archSmooth e W) : Continuous W := by
  have hc := h.continuousOn.comp_continuous (he.comp Units.continuous_val)
    (fun u => show e u.val ≠ 0 from (map_ne_zero e).mpr u.ne_zero)
  apply hc.congr
  intro u
  simp only [Function.comp_apply,e.symm_apply_apply,dif_pos u.ne_zero,Units.mk0_val]

theorem TestWeight.continuous {W : Weight v} (hW : TestWeight v W) : Continuous W := by
  cases v with
  | inr p => exact (show IsLocallyConstant W from hW.2).continuous
  | inl w =>
    by_cases hw : w.IsReal
    · apply archSmooth_continuous (InfinitePlace.Completion.ringEquivRealOfIsReal hw)
        (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).continuous
      simpa only [dif_pos hw] using hW.2
    · apply archSmooth_continuous (InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (InfinitePlace.not_isReal_iff_isComplex.mp hw)) (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous
      simpa only [dif_neg hw] using hW.2

/-- The absolute integral defining H_c(t) equals the L¹ norm of W,
independently of t and c. -/
theorem kernelIntegral_estimates {W : Weight v} (hW : Integrable W (d.lineMeasure v)) (c : Kˣ) :
    Continuous (d.kernelIntegral v W c) ∧ ∀ t : K,
      Integrable (fun x : Kˣ => W x * d.symbol v x (-c) *
        d.character.localValue F v (-(t^n)/(c.val*x.val))) (d.lineMeasure v) ∧
      ‖d.kernelIntegral v W c t‖ ≤ ∫ x, ‖W x‖ ∂d.lineMeasure v := by
  let f (t : K) (x : Kˣ) := W x * d.symbol v x (-c) * d.character.localValue F v (-(t^n)/(c.val*x.val))
  have meas (t : K) : AEStronglyMeasurable (f t) (d.lineMeasure v) := by
    have hsym := (d.continuous_symbol v).comp (continuous_id.prodMk (continuous_const (y := -c)))
    have hphase : Continuous (fun x : Kˣ => d.character.localValue F v (-(t^n)/(c.val*x.val))) :=
      (d.character.continuous_localValue v).comp (continuous_const.div
        (continuous_const.mul Units.continuous_val) (fun x => mul_ne_zero c.ne_zero x.ne_zero))
    exact (hW.aestronglyMeasurable.mul hsym.aestronglyMeasurable).mul hphase.aestronglyMeasurable
  have hn (t : K) (x : Kˣ) : ‖f t x‖ = ‖W x‖ := by
    simp only [f,norm_mul,d.norm_symbol,d.character.norm_localValue,mul_one]
  have hk (t : K) : d.kernelIntegral v W c t = ∫ x, f t x ∂d.lineMeasure v := (d.integral_lineMeasure v _).symm
  rw [show d.kernelIntegral v W c = _ from funext hk]
  constructor
  · apply continuous_of_dominated (bound := fun x => ‖W x‖) meas (fun t => .of_forall fun x => (hn t x).le) hW.norm
    filter_upwards with x
    exact continuous_const.mul ((d.character.continuous_localValue v).comp
      (((continuous_id.pow n).neg).div_const _))
  · intro t
    exact ⟨hW.norm.mono' (meas t) (.of_forall fun x => (hn t x).le),
      (norm_integral_le_integral_norm _).trans_eq (by simp_rw [hn])⟩

omit [NeZero n] in
theorem testWeight_integrable {W : Weight v} (hW : TestWeight v W) : Integrable W (d.lineMeasure v) :=
  (TestWeight.continuous v hW).integrable_of_hasCompactSupport hW.1

end MetaplecticPoisson.Datum
