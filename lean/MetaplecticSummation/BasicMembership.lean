import MetaplecticSummation.BasicConductor
import MetaplecticSummation.Dilations
import MetaplecticSummation.PrimitiveLayer

/-! Membership of the explicit basic vector in the local Schwartz space. -/

noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField IsDedekindDomain MeasureTheory Filter
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n) (p : Prime F)
local notation "v" => (Sum.inr p : Place F)
local notation "K" => LocalField F v
local notation "B" => d.basicCharts p
local notation "T" => d.integralTransform v
local notation "dx" => selfDual F d.character v
local notation "ψ" => d.character.localValue F v
local notation "R" => radon n (d.symbol v) (modulus F v) dx

private def ShearInvariant {L : Type} [NormedField L] (f : Charts L) : Prop :=
  (∀ u : L, ‖u‖ ≤ 1 → ∀ x y, f.1 x (y + u*x.val) = f.1 x y) ∧
  (∀ u : L, ‖u‖ ≤ 1 → ∀ x y, f.2 (x + u*y.val) y = f.2 x y)

private theorem ShearInvariant.dilate {L : Type} [NormedField L] {f : Charts L}
    (h : ShearInvariant f) (a : Lˣ) : ShearInvariant (dilateCharts a f) := by
  constructor
  · intro u hu x y
    simpa only [dilateCharts,mul_add,Units.val_mul,mul_left_comm a.val u] using h.1 u hu (a*x) (a.val*y)
  · intro u hu x y
    simpa only [dilateCharts,mul_add,Units.val_mul,mul_left_comm a.val u] using h.2 u hu (a.val*x) (a*y)

private theorem ShearInvariant.sub_smul {L : Type} [NormedField L] {f g : Charts L}
    (hf : ShearInvariant f) (hg : ShearInvariant g) (c : ℂ) : ShearInvariant (f - c • g) := by
  exact ⟨fun u hu x y => congrArg₂ (fun a b => a-c*b) (hf.1 u hu x y) (hg.1 u hu x y),
    fun u hu x y => congrArg₂ (fun a b => a-c*b) (hf.2 u hu x y) (hg.2 u hu x y)⟩

private theorem transform_fst_congr {L : Type} [Field L] [MeasurableSpace L] (n : ℕ)
    (χ : L → ℂ) (h : Lˣ → Lˣ → ℂ) (m : L → ℝ) (μ : Measure L) {f g : Charts L}
    (he : f.1 = g.1) (x : Lˣ) (y : L) :
    (transform n χ h m μ f).1 x y = (transform n χ h m μ g).1 x y := by simp only [transform,radon,he]

private theorem transform_snd_congr {L : Type} [Field L] [MeasurableSpace L] (n : ℕ)
    (χ : L → ℂ) (h : Lˣ → Lˣ → ℂ) (m : L → ℝ) (μ : Measure L) {f g : Charts L}
    (he : f.2 = g.2) (x : L) (y : Lˣ) :
    (transform n χ h m μ f).2 x y = (transform n χ h m μ g).2 x y := by simp only [transform,radon,he]

private theorem invariant_transform {f : Charts K} (hf : ShearInvariant f) : ShearInvariant (T f) := by
  constructor
  · intro u hu x y
    have he : (upperShear (d.symbol v) u f).1 = f.1 := funext fun a => funext (hf.1 u hu a)
    change (transform n ψ (d.symbol v) (modulus F v) dx f).1 x (y+u*x.val) = _
    rw [← transform_upper (d.symbol v) n (modulus F v) dx ψ u f x y]
    exact transform_fst_congr n ψ (d.symbol v) (modulus F v) dx (g := f) (f := upperShear (d.symbol v) u f) he x y
  · intro u hu x y
    have he : (lowerShear (d.symbol v) u f).2 = f.2 := funext fun a => funext (hf.2 u hu a)
    change (transform n ψ (d.symbol v) (modulus F v) dx f).2 (x+u*y.val) y = _
    rw [← transform_lower (d.symbol v) n (modulus F v) dx ψ u f x y]
    exact transform_snd_congr n ψ (d.symbol v) (modulus F v) dx (g := f) (f := lowerShear (d.symbol v) u f) he x y

private theorem basic_invariant (hp : p.asIdeal.absNorm.Coprime n) : ShearInvariant B :=
  ⟨fun u hu x y => congrArg (fun z : Charts K => z.1 x y) (d.basicCharts_shear p hp u hu).1,
    fun u hu x y => congrArg (fun z : Charts K => z.2 x y) (d.basicCharts_shear p hp u hu).2⟩

private theorem basic_slice_integrable (a x : Kˣ) :
    Integrable (fun z => (dilateCharts a B).1 x z) dx := by
  letI : ProperSpace K := by
    letI := FinitePlace.nontriviallyNormedCompletion p
    exact .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace (p.adicCompletion F)
  letI : (dx).IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  have hc := (d.basicCharts_locallyConstant p).1.continuous.comp
    (continuous_const (y := a*x) |>.prodMk (continuous_const (y := a.val) |>.mul continuous_id))
  apply hc.integrable_of_hasCompactSupport
  apply HasCompactSupport.intro' (isCompact_closedBall (0 : K) ‖a.val‖⁻¹) Metric.isClosed_closedBall
  intro z hz
  have hn : 1 < ‖a.val*z‖ := by
    rw [norm_mul,← inv_lt_iff_one_lt_mul₀' (norm_pos_iff.mpr a.ne_zero)]
    simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hz
  have hq : 1 < (p.asIdeal.absNorm : ℝ) := by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm p
  have he (k : ℕ) : max ‖(a*x).val‖ ‖a.val*z‖ ≠ ((p.asIdeal.absNorm : ℝ)^(n*k))⁻¹ :=
    ne_of_gt ((inv_le_one_of_one_le₀ (one_le_pow₀ hq.le)).trans_lt (hn.trans_le (le_max_right _ _)))
  change B.1 (a*x) (a.val*z) = 0
  simp only [basicCharts,if_neg (he _),tsum_zero,zero_mul]

private theorem glues_sub_smul {L : Type} [Field L] {h : Lˣ → Lˣ → ℂ} {f g : Charts L}
    (hf : Glues h f) (hg : Glues h g) (c : ℂ) : Glues h (f - c • g) := by
  intro x y
  change f.1 x y - c*g.1 x y = h x y * (f.2 x y - c*g.2 x y)
  rw [hf,hg]
  ring

/-- Linearity on the difference of two dilates, established before either
basic section has been placed in the Schwartz space. -/
private theorem transform_basic_sub_dilate (hp : p.asIdeal.absNorm.Coprime n) (hψ : d.UnramifiedAt v)
    (a : Kˣ) (c : ℂ) :
    T (B - c • dilateCharts (a^n) B) = T B - c • T (dilateCharts (a^n) B) := by
  let D := dilateCharts (a^n) B
  have gb := d.basicCharts_glues p hp
  have gd := d.dilateCharts_glues v a gb
  have gs := glues_sub_smul gb gd c
  have hb := d.basic_invariant p hp
  have hd := hb.dilate (a^n)
  have hL := d.invariant_transform p (hb.sub_smul hd c)
  have hR := (d.invariant_transform p hb).sub_smul (d.invariant_transform p hd) c
  apply d.eq_of_integral_shears_of_axis p (d.integralTransform_glues v gs)
    (glues_sub_smul (d.integralTransform_glues v gb) (d.integralTransform_glues v gd) c)
    (fun u hu x y => congrArg₂ (·-·) (hL.1 u hu x y) (hR.1 u hu x y))
    (fun u hu x y => congrArg₂ (·-·) (hL.2 u hu x y) (hR.2 u hu x y))
  intro y
  have hi (x : Kˣ) : Integrable (fun z => B.1 x z) dx := by
    simpa only [dilateCharts_one] using d.basic_slice_integrable p 1 x
  have hr (t : Kˣ) : (R (B-c • D) t.val).2 0 y = (R B t.val).2 0 y - c*(R D t.val).2 0 y := by
    rw [d.radon_axis_unit v _ gs,d.radon_axis_unit v _ gb,d.radon_axis_unit v _ gd]
    let x := t^n/y
    change _ * (∫ z, B.1 x z - c * D.1 x z ∂dx) = _
    rw [integral_sub (hi x) ((d.basic_slice_integrable p _ x).const_mul c),integral_const_mul]
    ring
  let k : ℂ := ((modulus F v (a^n).val : ℂ)^2)⁻¹
  have hdR (t : K) : (R D t).2 0 y = k * (R B t).2 0 ((a^n)⁻¹*y) := by
    have he := congrArg (fun f : Charts K => f.2 0 y) (d.radon_dilateCharts v a B t)
    simpa only [D,k,Prod.smul_snd,Pi.smul_apply,dilateCharts,mul_zero,smul_eq_mul] using he
  have hdI : Integrable (fun t => ψ t * (R D t).2 0 y) dx := by
    simp_rw [hdR,mul_left_comm (ψ _) k]
    exact (d.basic_axis_integrable p hp hψ _).const_mul k
  letI : NullSingletonClass (dx) := d.selfDual_nullSingleton v
  have he : (fun t => ψ t * (R (B-c • D) t).2 0 y) =ᵐ[dx]
      fun t => ψ t * (R B t).2 0 y - c*(ψ t * (R D t).2 0 y) := by
    filter_upwards [(dx).ae_ne 0] with t ht
    rw [show (R (B-c • D) t).2 0 y = _ from hr (Units.mk0 t ht)]
    simp only [Units.val_mk0]
    ring
  change _ * (∫ t, ψ t * (R (B-c • D) t).2 0 y ∂dx) =
    _ * (∫ t, ψ t * (R B t).2 0 y ∂dx) - c * (_ * (∫ t, ψ t * (R D t).2 0 y ∂dx))
  rw [integral_congr_ae he,integral_sub (d.basic_axis_integrable p hp hψ y) (hdI.const_mul c),integral_const_mul]
  ring

private theorem unramified_basic_mem (hp : p.asIdeal.absNorm.Coprime n) (hψ : d.UnramifiedAt v) :
    B ∈ d.schwartz v := by
  let q : ℂ := p.asIdeal.absNorm
  let c := q^(n-1)
  obtain ⟨π,hπ⟩ : ∃ π : Kˣ, ‖π.val‖ = (p.asIdeal.absNorm : ℝ)⁻¹ := FinitePlace.exists_norm_uniformizer p
  let A := π^n
  let P := d.primitiveCharts p
  have ht := d.primitive_test p hp
  have e : P = B - c • dilateCharts (π⁻¹^n) B := d.primitive_eq_basic_sub_dilate p π hπ
  have eD : dilateCharts A P = dilateCharts A B - c • B := by
    rw [e]
    rw [dilateCharts_sub,dilateCharts_smul]
    rw [dilateCharts_mul,inv_pow,show (π^n)⁻¹*A = 1 from inv_mul_cancel _,dilateCharts_one]
  let m := c * (q^n)^(-2 : ℤ)
  have heT : T P = B - m • dilateCharts A B := by
    rw [e,d.transform_basic_sub_dilate p hp hψ,d.integralTransform_dilateCharts,d.basicCharts_fourier_fixed p hp hψ]
    have he : (modulus F v (π⁻¹^n).val : ℂ) = q^n := by
      change (‖(π⁻¹^n).val‖ : ℂ) = _
      rw [Units.val_pow_eq_pow_val,Units.val_inv_eq_inv_val,norm_pow,norm_inv,hπ,inv_inv,Complex.ofReal_pow,Complex.ofReal_natCast]
    rw [he,smul_smul,inv_pow,inv_inv]
    rfl
  have eqn : (1-m*c) • B = T P + m • dilateCharts A P := by
    rw [heT,eD,smul_sub,smul_smul,sub_smul,one_smul]
    abel
  have q₀ : q ≠ 0 := by
    dsimp [q]
    exact_mod_cast (Nat.zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm p)).ne'
  have hn : q^n = c*q := by
    rw [← pow_succ, Nat.sub_add_cancel (NeZero.pos n)]
  have hc : c ≠ 0 := pow_ne_zero _ q₀
  have hmc : m*c = (q^2)⁻¹ := by
    simp only [m,zpow_neg,hn]
    field_simp
  have hq : (1 : ℝ) < (p.asIdeal.absNorm : ℝ) := by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm p
  have h₂ : (1 : ℝ) < (p.asIdeal.absNorm : ℝ)^2 := one_lt_pow₀ hq (by decide)
  have hq' : (1 : ℝ) ≠ ((p.asIdeal.absNorm : ℝ)^2)⁻¹ := (inv_lt_one_of_one_lt₀ h₂).ne'
  have h : 1-m*c ≠ 0 := by
    rw [hmc,sub_ne_zero]
    intro he
    apply hq'
    apply Complex.ofReal_injective
    simpa only [Complex.ofReal_one,Complex.ofReal_inv,Complex.ofReal_pow,Complex.ofReal_natCast] using he
  have hmem : (1-m*c) • B ∈ d.schwartz v := eqn ▸ Submodule.add_mem _
    (Submodule.subset_span (Or.inr ⟨P,ht,rfl⟩))
    (Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl (d.finite_dilate_test p π ht))))
  simpa only [smul_smul,inv_mul_cancel₀ h,one_smul] using (d.schwartz v).smul_mem (1-m*c)⁻¹ hmem

/-- Proposition 6.3(ii) at every tame finite place, for any conductor. -/
theorem basic_mem (hp : p.asIdeal.absNorm.Coprime n) : B ∈ d.schwartz v := by
  obtain ⟨a,ha⟩ := d.exists_unramified_scaling p
  have h : (d.scaled a).schwartz v ≤ d.schwartz v := by
    apply Submodule.span_le.mpr
    rintro g (hg | ⟨f,hf,rfl⟩)
    · exact Submodule.subset_span (Or.inl hg)
    · rw [d.integralTransform_scaled]
      exact Submodule.smul_mem _ _ (d.finite_dilate_schwartz p _ (Submodule.subset_span (Or.inr ⟨f,hf,rfl⟩)))
  exact h ((d.scaled a).unramified_basic_mem p hp ha)

end MetaplecticPoisson.Datum
