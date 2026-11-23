import MetaplecticSummation.ArchimedeanSlice
import MetaplecticSummation.Marginals.Basic

/-! Schwartz regularity of the axis density of an archimedean test section. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace MetaplecticPoisson
open Filter Set Asymptotics NumberField MeasureTheory
open scoped Topology ContDiff
open Classical

/-- A function smooth off zero whose derivatives vanish to second order extends
smoothly by zero, with every derivative zero at the origin. -/
private theorem smooth_flat_extension {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] {g : E → V} (hg : g 0 = 0)
    (hs : ∀ x ≠ 0, ContDiffAt ℝ ∞ g x)
    (hb : ∀ j : ℕ, ∃ C : ℝ, ∀ x ≠ 0, ‖iteratedFDeriv ℝ j g x‖ ≤ C*‖x‖^2) :
    ContDiff ℝ ∞ g ∧ ∀ j, iteratedFDeriv ℝ j g 0 = 0 := by
  have hd (k : ℕ) (hz : iteratedFDeriv ℝ k g 0 = 0) :
      HasFDerivAt (iteratedFDeriv ℝ k g) (0 : E →L[ℝ] _) 0 := by
    apply Asymptotics.IsBigO.hasFDerivAt (n := 2) _ one_lt_two
    obtain ⟨C,H⟩ := hb k
    apply IsBigO.of_bound C
    filter_upwards with x
    by_cases hx : x = 0
    · simp [hx,hz]
    · simpa using H x hx
  have flat (k : ℕ) : iteratedFDeriv ℝ k g 0 = 0 := by
    induction k with
    | zero => apply norm_eq_zero.mp; simp [norm_iteratedFDeriv_zero,hg]
    | succ k ih => simp [iteratedFDeriv_succ_eq_comp_left,(hd k ih).fderiv]; ext v; rfl
  refine ⟨contDiff_of_differentiable_iteratedFDeriv (fun k _ x => ?_),flat⟩
  by_cases hx : x = 0
  · exact hx ▸ (hd k (flat k)).differentiableAt
  · exact (hs x hx).differentiableAt_iteratedFDeriv (by exact_mod_cast ENat.coe_lt_top k)

/-- A rapid chart restricted to the vertical axis, extended through zero. -/
private theorem rapid_vertical_schwartz {L : Type} [NormedField L] [NormedAlgebra ℝ L]
    {f : L×L → ℂ} (hf : rapidChart {z | z.2 ≠ 0} f) (h0 : f 0 = 0) :
    ∃ g : SchwartzMap L ℂ, (∀ x, g x = f (0,x)) ∧ ∀ j, iteratedFDeriv ℝ j g 0 = 0 := by
  let A : L →L[ℝ] L×L := (0 : L →L[ℝ] L).prod (.id ℝ L)
  let g := f ∘ A
  let U : Set (L×L) := {z | z.2 ≠ 0}
  have ho : IsOpen U := isOpen_ne_fun continuous_snd continuous_const
  have pre : IsOpen (A ⁻¹' U) := ho.preimage A.continuous
  have hx {x : L} (h : x ≠ 0) : A x ∈ U := h
  have hs (x : L) (h : x ≠ 0) : ContDiffAt ℝ ∞ g x :=
    (hf.1.contDiffAt (ho.mem_nhds (hx h))).comp x A.contDiff.contDiffAt
  have normA (x : L) : ‖A x‖ = ‖x‖ := by simp [A,Prod.norm_def]
  have bound (j : ℕ) (x : L) (h : x ≠ 0) :
      ‖iteratedFDeriv ℝ j g x‖ ≤ ‖iteratedFDeriv ℝ j f (A x)‖ * ‖A‖^j := by
    have he := A.iteratedFDerivWithin_comp_right hf.1 ho.uniqueDiffOn pre.uniqueDiffOn (hx h)
      (i := j) (by exact_mod_cast le_top)
    rw [iteratedFDerivWithin_eq_iteratedFDeriv pre.uniqueDiffOn ((hs x h).of_le (by exact_mod_cast le_top)) (hx h),
      iteratedFDerivWithin_eq_iteratedFDeriv ho.uniqueDiffOn
        ((hf.1.contDiffAt (ho.mem_nhds (hx h))).of_le (by exact_mod_cast le_top)) (hx h)] at he
    rw [show iteratedFDeriv ℝ j g x = _ from he]
    simpa using (iteratedFDeriv ℝ j f (A x)).norm_compContinuousLinearMap_le (fun _ => A)
  have near (j : ℕ) : ∃ C : ℝ, ∀ x ≠ 0, ‖iteratedFDeriv ℝ j g x‖ ≤ C*‖x‖^2 := by
    obtain ⟨C,H⟩ := hf.2 j 2
    refine ⟨max C 0 * ‖A‖^j,fun x h => ?_⟩
    have hC := H (A x) (hx h)
    rw [normA] at hC
    have ha : ‖iteratedFDeriv ℝ j f (A x)‖ ≤ max C 0 * ‖x‖^2 := hC.trans
      (mul_le_mul (le_max_left ..) (min_le_left ..) (le_min (by positivity) (by positivity)) (le_max_right ..))
    exact (bound j x h).trans ((mul_le_mul_of_nonneg_right ha (by positivity)).trans_eq (by ring))
  obtain ⟨smooth,flat⟩ := smooth_flat_extension (g := g) (by simpa [g] using h0) hs near
  refine ⟨⟨g,smooth,?_⟩,fun _ => rfl,flat⟩
  intro k j
  obtain ⟨C,hC,H⟩ := rapidChart_derivative_polynomial hf j k
  refine ⟨C*‖A‖^j,fun x => ?_⟩
  by_cases h : x = 0
  · simp [h,flat,mul_nonneg hC (pow_nonneg (norm_nonneg _) _)]
  · have est := H (A x) (hx h)
    rw [normA] at est
    calc
      _ ≤ (1+‖x‖)^k * (‖iteratedFDeriv ℝ j f (A x)‖ * ‖A‖^j) :=
        mul_le_mul (pow_le_pow_left₀ (norm_nonneg x) (by linarith) _) (bound j x h) (norm_nonneg _) (by positivity)
      _ = (‖iteratedFDeriv ℝ j f (A x)‖*(1+‖x‖)^k)*‖A‖^j := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right est (by positivity)

/-- Pullback by a nonconstant power map preserves Schwartz decay and the
vanishing of every derivative at zero. -/
private theorem flat_power_pullback {L : Type} [RCLike L] (g : SchwartzMap L ℂ)
    (flat : ∀ j, iteratedFDeriv ℝ j g 0 = 0) (b : L) (hb : b ≠ 0) (n : ℕ) [NeZero n] :
    ∃ G : SchwartzMap L ℂ, (∀ t, G t = g (b*t^n)) ∧ ∀ j, iteratedFDeriv ℝ j G 0 = 0 := by
  let P (t : L) := b*t^n
  have ht : P.HasTemperateGrowth := by dsimp [P]; fun_prop
  have grow (x : L) : ‖x‖ ≤ (1+‖b⁻¹‖)*(1+‖P x‖)^1 := by
    have he : ‖b⁻¹‖*‖P x‖ = ‖x‖^n := by simp [P,norm_mul,norm_pow,hb]
    rw [pow_one]
    rcases le_total ‖x‖ 1 with h | h
    · nlinarith [norm_nonneg b⁻¹,norm_nonneg (P x),mul_nonneg (norm_nonneg b⁻¹) (norm_nonneg (P x))]
    · nlinarith [le_self_pow₀ h (NeZero.ne n),norm_nonneg b⁻¹,norm_nonneg (P x)]
  refine ⟨SchwartzMap.compCLM ℂ ht ⟨1,1+‖b⁻¹‖,grow⟩ g,fun _ => rfl,?_⟩
  intro j
  change iteratedFDeriv ℝ j ((g : L → ℂ) ∘ P) 0 = 0
  have hz : P 0 = 0 := by simp [P,NeZero.ne n]
  rw [iteratedFDeriv_comp ((g.smooth ⊤).contDiffAt) ht.1.contDiffAt (by exact_mod_cast le_top),hz]
  apply Finset.sum_eq_zero
  intro c _
  ext v
  simp [ftaylorSeries,flat]

/-- Cutting a flat real Schwartz function to the positive half-line keeps
it Schwartz. Its iterated derivatives are the same cutoffs of the derivatives. -/
private theorem flat_positive_cut (g : SchwartzMap ℝ ℂ) (flat : ∀ j, iteratedFDeriv ℝ j g 0 = 0) :
    ∃ G : SchwartzMap ℝ ℂ, ∀ t, G t = if 0 < t then g t else 0 := by
  let f (x : ℝ) := if 0 < x then g x else 0
  let J (k : ℕ) (x : ℝ) := if 0 < x then iteratedFDeriv ℝ k g x else 0
  have pos (x : ℝ) (h : 0 < x) (k : ℕ) : J k =ᶠ[𝓝 x] iteratedFDeriv ℝ k g :=
    (lt_mem_nhds h).mono fun t ht => if_pos ht
  have neg (x : ℝ) (h : x < 0) (k : ℕ) : J k =ᶠ[𝓝 x] 0 :=
    (gt_mem_nhds h).mono fun t ht => if_neg (not_lt.mpr ht.le)
  have at0 (k : ℕ) : HasFDerivAt (J k) (0 : ℝ →L[ℝ] _) 0 := by
    have hd := ((g.smooth ⊤).contDiffAt.differentiableAt_iteratedFDeriv (x := 0)
      (by exact_mod_cast ENat.coe_lt_top k)).hasFDerivAt
    have hz : fderiv ℝ (iteratedFDeriv ℝ k g) 0 = 0 := by
      have h := congrArg (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k+1) => ℝ) ℂ) (flat (k+1))
      simp only [iteratedFDeriv_succ_eq_comp_left,Function.comp_apply,LinearIsometryEquiv.apply_symm_apply] at h
      exact h.trans (by ext; rfl)
    rw [hz] at hd
    have little := hd.isLittleO
    simp only [flat,sub_zero,zero_apply] at little
    rw [hasFDerivAt_iff_isLittleO]
    simp only [show J k 0 = 0 from if_neg (lt_irrefl _),sub_zero,zero_apply]
    apply (IsBigO.of_bound 1 ?_).trans_isLittleO little
    filter_upwards with x
    by_cases hx : 0 < x <;> simp [J,hx]
  have der (k : ℕ) : iteratedFDeriv ℝ k f = J k := by
    induction k with
    | zero =>
      funext t
      by_cases ht : 0 < t <;> simp [f,J,ht,iteratedFDeriv_zero_eq_comp]
      rfl
    | succ k ih =>
      funext t
      rw [iteratedFDeriv_succ_eq_comp_left,Function.comp_apply,ih]
      rcases lt_trichotomy t 0 with ht | rfl | ht
      · rw [(neg t ht k).fderiv_eq]
        simp [J,ht.not_gt]; ext; rfl
      · rw [(at0 k).fderiv]
        simp [J]; ext; rfl
      · rw [(pos t ht k).fderiv_eq]
        simp [J,ht,iteratedFDeriv_succ_eq_comp_left]
  have smooth : ContDiff ℝ ∞ f := by
    apply contDiff_of_differentiable_iteratedFDeriv
    intro k _ x
    rw [der]
    rcases lt_trichotomy x 0 with h | rfl | h
    · exact (differentiableAt_const (c := (0 : ℝ [×k]→L[ℝ] ℂ))).congr_of_eventuallyEq (neg x h k)
    · exact (at0 k).differentiableAt
    · exact ((g.smooth ⊤).contDiffAt.differentiableAt_iteratedFDeriv
        (by exact_mod_cast ENat.coe_lt_top k)).congr_of_eventuallyEq (pos x h k)
  refine ⟨⟨f,smooth,fun k j => ?_⟩,fun _ => rfl⟩
  obtain ⟨C,H⟩ := g.decay' k j
  refine ⟨max 0 C,fun x => ?_⟩
  rw [der]
  by_cases h : 0 < x
  · rw [show J j x = iteratedFDeriv ℝ j g x from if_pos h]
    exact (H x).trans (le_max_right ..)
  · simp [J,h]


private theorem real_weighted_flat (g : SchwartzMap ℝ ℂ) (flat : ∀ j, iteratedFDeriv ℝ j g 0 = 0) (k : ℕ) :
    ∃ G : SchwartzMap ℝ ℂ, ∀ t, G t = ((‖t‖ : ℝ) : ℂ)^k * g t := by
  obtain ⟨P,hP⟩ := flat_positive_cut g flat
  let a (t : ℝ) := t^k
  let b (t : ℝ) := (-t)^k
  have ha : a.HasTemperateGrowth := by dsimp [a]; fun_prop
  have hb : b.HasTemperateGrowth := by dsimp [b]; fun_prop
  refine ⟨SchwartzMap.smulLeftCLM ℂ a P + SchwartzMap.smulLeftCLM ℂ b (g-P),fun t => ?_⟩
  simp only [add_apply,SchwartzMap.smulLeftCLM_apply_apply ha,
    SchwartzMap.smulLeftCLM_apply_apply hb,sub_apply,Complex.real_smul,hP]
  by_cases ht : 0 < t
  · simp [a,b,ht,Real.norm_eq_abs,abs_of_pos ht]
  · simp [a,b,ht,Real.norm_eq_abs,abs_of_nonpos (le_of_not_gt ht)]

private theorem complex_weighted_flat (g : SchwartzMap ℂ ℂ) (k : ℕ) :
    ∃ G : SchwartzMap ℂ ℂ, ∀ t, G t = ((‖t‖^2 : ℝ) : ℂ)^k * g t := by
  let a (t : ℂ) := (‖t‖^2)^k
  have ha : a.HasTemperateGrowth := (Function.hasTemperateGrowth_norm_sq ℂ).pow k
  refine ⟨SchwartzMap.smulLeftCLM ℂ a g,fun t => ?_⟩
  rw [SchwartzMap.smulLeftCLM_apply_apply ha]
  simp only [Complex.real_smul,a,Complex.ofReal_pow]

namespace Datum
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)
variable (w : InfinitePlace F)
local notation "vₐ" => (Sum.inl w : Place F)
local notation "K" => LocalField F vₐ

private theorem axisDensity_test_coordinates {L : Type} [RCLike L] (e : w.Completion ≃+* L) (he : Isometry e)
    (weight : ∀ g : SchwartzMap L ℂ, (∀ j, iteratedFDeriv ℝ j g 0 = 0) →
      ∃ G : SchwartzMap L ℂ, ∀ t, G t = ((‖t‖^w.mult : ℝ) : ℂ)^(n-1)*g t)
    (Φ : d.schwartz vₐ) (hΦ : Φ.val ∈ d.testSet vₐ) (hT : archTest e Φ.val) (x : Kˣ) :
    ∃ G : SchwartzMap L ℂ, ∀ t, d.axisDensity vₐ Φ x t = G (e t) := by
  let f (z : L×L) := yChart Φ.val (e.symm z.1,e.symm z.2)
  have h0 : f 0 = 0 := by
    change yChart Φ.val (e.symm 0,e.symm 0) = 0
    simp only [map_zero,yChart]
    exact dif_neg (fun h => h rfl)
  obtain ⟨g,hg,hflat⟩ := rapid_vertical_schwartz (f := f) hT.2 h0
  let b : L := -(e x.val)⁻¹
  have hb : b ≠ 0 := neg_ne_zero.mpr (inv_ne_zero ((map_ne_zero e).mpr x.ne_zero))
  obtain ⟨G,hG,flat⟩ := flat_power_pullback g hflat b hb n
  obtain ⟨T,hT⟩ := weight G flat
  let c : ℂ := (modulus F vₐ (n : K) : ℂ)/(modulus F vₐ x.val : ℂ)
  refine ⟨c • T,fun t => ?_⟩
  change d.axisDensity vₐ Φ x t = c * T (e t)
  rw [hT,hG,hg]
  by_cases ht : t = 0
  · subst t
    rw [d.axisDensity_zero,d.leading_archTest_eq_zero w Φ hΦ]
    have hz : e (0 : K) = (0 : L) := e.map_zero
    rw [hz,zero_pow (NeZero.ne n),mul_zero,show f (0,0) = 0 from h0,mul_zero,mul_zero]
    exact mul_zero _
  · let u := Units.mk0 t ht
    have E : e.symm (b*(e t)^n) = (-(u^n)/x).val := by
      simp [b,u,div_eq_mul_inv,mul_comm]
    have hh : f (0,b*(e t)^n) = d.axis vₐ Φ (-(u^n)/x) := by
      simp only [f,yChart,map_zero,E,dif_pos (Units.ne_zero _),Units.mk0_val,axis]
    rw [hh,he.norm_map_of_map_zero e.map_zero]
    change d.axisDensity vₐ Φ x u.val = _
    rw [d.axisDensity_unit,mul_assoc]
    rfl

/-- The density of a test section is Schwartz at every infinite place,
with its prescribed value at the origin. -/
theorem arch_axisDensity_test_bruhat (Φ : d.schwartz vₐ) (hΦ : Φ.val ∈ d.testSet vₐ) (x : Kˣ) :
    Bruhat vₐ (d.axisDensity vₐ Φ x) := by
  dsimp only [Bruhat]
  split <;> rename_i h
  · exact d.axisDensity_test_coordinates w _ (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal h)
      (fun g hg => by simpa only [InfinitePlace.mult_isReal ⟨w,h⟩,pow_one] using real_weighted_flat g hg (n-1))
      Φ hΦ (by simpa only [testSet,dif_pos h] using! hΦ.2) x
  · have hc := InfinitePlace.not_isReal_iff_isComplex.mp h
    exact d.axisDensity_test_coordinates w _ (InfinitePlace.Completion.isometry_extensionEmbedding w)
      (fun g _ => by simpa only [InfinitePlace.mult_isComplex ⟨w,hc⟩] using complex_weighted_flat g (n-1))
      Φ hΦ (by simpa only [testSet,dif_neg h] using! hΦ.2) x

end Datum

end MetaplecticPoisson
