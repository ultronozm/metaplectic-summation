import MetaplecticSummation.Jacquet
import MetaplecticSummation.LocalGrowth

/-! Absolute convergence and linearity of the Jacquet integral on the local Schwartz space. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField MeasureTheory Filter Set
open scoped Topology
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)
private theorem xChart_unit_eval {k : Type} [Field k] (g : Charts k) (x : kˣ) (y : k) :
    xChart g (x.val,y) = g.1 x y := by simp only [xChart,dif_pos x.ne_zero,Units.mk0_val]

section Arch
variable (w : InfinitePlace F)
local notation "vi" => (Sum.inl w : Place F)
local notation "K" => LocalField F vi

theorem continuous_arch_schwartz_charts (Φ : d.schwartz vi) :
    Continuous (Function.uncurry Φ.val.1) ∧ Continuous (Function.uncurry Φ.val.2) := by
  refine Submodule.span_induction (p := fun g _ =>
    Continuous (Function.uncurry g.1) ∧ Continuous (Function.uncurry g.2)) ?_ ?_ ?_ ?_ Φ.property
  · rintro g (hg | ⟨f,hf,rfl⟩)
    · obtain ⟨hx,hy⟩ := d.arch_test_lineCharts w hg
      exact ⟨hx.1,hy.1.comp (f := Prod.swap) continuous_swap⟩
    · have hc := (d.arch_radon_hat_bounded w hf).1.comp
        (continuous_id.prodMk (continuous_const (y := (1:K))))
      let s : ℂ := (Real.sqrt (modulus F vi (n : K)) : ℂ)⁻¹
      constructor
      · apply ((continuous_const (y := s)).mul hc.fst).congr
        intro z
        change s * d.hat vi _ 1 = s * _
        simp only [hat,one_mul]
        congr 1
        apply integral_congr_ae
        filter_upwards with t using mul_comm _ _
      · apply ((continuous_const (y := s)).mul (hc.snd.comp continuous_swap)).congr
        intro z
        change s * d.hat vi _ 1 = s * _
        simp only [hat,one_mul]
        congr 1
        apply integral_congr_ae
        filter_upwards with t using mul_comm _ _
  · exact ⟨continuous_const,continuous_const⟩
  · intro f g _ _ hf hg
    exact ⟨hf.1.add hg.1,hf.2.add hg.2⟩
  · intro c g _ hg
    exact ⟨continuous_const.mul hg.1,continuous_const.mul hg.2⟩

theorem continuous_arch_schwartz_X (Φ : d.schwartz vi) : Continuous (Function.uncurry Φ.val.1) :=
  (d.continuous_arch_schwartz_charts w Φ).1

/-- On any region where the modulus of the first coordinate is bounded
below, the vertical slices have one integrable majorant. -/
theorem arch_jacquet_majorant (Φ : d.schwartz vi) {m : ℝ} (hm : 0 < m) :
    ∃ B : ℝ, ∀ x : Kˣ, m ≤ modulus F vi x.val → ∀ y : K,
      ‖Φ.val.1 x y‖ ≤ B * ((1 + ‖y‖)^3)⁻¹ := by
  obtain ⟨C,hC,H⟩ := d.arch_local_growth w Φ 3 (by decide)
  let D := 2 + 2/m
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨C * D^3,fun x hx y => ?_⟩
  let r := max (modulus F vi x.val) (modulus F vi y)
  have hmr : m ≤ r := hx.trans (le_max_left ..)
  have hr : 0 < r := hm.trans_le hmr
  have hz : (x.val,y) ≠ (0 : K × K) := fun h => x.ne_zero (congrArg Prod.fst h)
  have h := (H (x.val,y) hz).1
  rw [xChart_unit_eval] at h
  have bound : ‖Φ.val.1 x y‖ ≤ C * (r^3)⁻¹ := by
    apply h.trans
    apply mul_le_mul_of_nonneg_left _ hC
    apply (min_le_right ..).trans_eq
    rw [Real.rpow_neg hr.le,Real.rpow_natCast]
  have hd : 1 + ‖y‖ ≤ D * r := by
    by_cases hy : ‖y‖ ≤ 1
    · have ht := mul_le_mul_of_nonneg_left hmr (show 0 ≤ 2/m by positivity)
      rw [div_mul_cancel₀ _ hm.ne'] at ht
      dsimp [D]
      nlinarith
    · have hr' : ‖y‖ ≤ r := (le_self_pow₀ (le_of_not_ge hy) (InfinitePlace.mult_ne_zero (w := w))).trans (le_max_right ..)
      have hpos : 0 ≤ (2/m)*r := by positivity
      dsimp [D]
      nlinarith
  rw [← div_eq_mul_inv,le_div_iff₀ (by positivity)]
  calc
    _ ≤ (C*(r^3)⁻¹) * (D*r)^3 := mul_le_mul bound (pow_le_pow_left₀ (by positivity) hd 3) (by positivity) (by positivity)
    _ = _ := by rw [mul_pow]; field_simp

end Arch

theorem integrable_jacquet_slice (v : Place F) (Φ : d.schwartz v) (x : (LocalField F v)ˣ) :
    Integrable (Φ.val.1 x) (selfDual F d.character v) := by
  cases v with
  | inl w =>
    have hm : 0 < modulus F (.inl w) x.val := pow_pos (norm_pos_iff.mpr x.ne_zero) _
    obtain ⟨B,hB⟩ := d.arch_jacquet_majorant w Φ hm
    exact ((d.arch_integrable_inv_cube w).const_mul B).mono'
      (((d.continuous_arch_schwartz_X w Φ).comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
      (.of_forall (hB x le_rfl))
  | inr p =>
    let dx := selfDual F d.character (Sum.inr p)
    letI : dx.IsAddHaarMeasure := (existsUnique_selfDual F d.character (.inr p)).exists.choose_spec.1
    obtain ⟨L,hL⟩ := d.exists_leading_finite p
    obtain ⟨C,hC,hout⟩ := (d.finite_support_and_germ_of_isLeadingTerm p Φ (hL Φ)).1
    have hc : Continuous (Φ.val.1 x) := (d.locallyConstant_finite_schwartz p Φ).1.continuous.comp ((continuous_const (y := x)).prodMk continuous_id)
    apply hc.integrable_of_hasCompactSupport (μ := dx)
    apply HasCompactSupport.intro (hC.image continuous_snd)
    intro y hy
    have h := (hout (x.val,y) (fun hin => hy ⟨_,hin,rfl⟩)).1
    simpa only [xChart,dif_pos x.ne_zero,Units.mk0_val] using h

theorem integrable_jacquet (v : Place F) (Φ : d.schwartz v) (x : (LocalField F v)ˣ) :
    Integrable (fun y => Φ.val.1 x y * d.character.localValue F v (-y/x.val)) (selfDual F d.character v) := by
  have hi := d.integrable_phase v (d.integrable_jacquet_slice v Φ x) (-x.val⁻¹)
  convert hi using 1
  funext y
  congr 2
  ring

theorem locallyConstant_finite_jacquet (p : Prime F) (Φ : d.schwartz (.inr p)) :
    IsLocallyConstant (d.jacquet (.inr p) Φ) := by
  let vp : Place F := .inr p
  let K := LocalField F vp
  let G (z : Kˣ × K) := Φ.val.1 z.1 z.2 * d.character.localValue F vp (-z.2 / z.1.val)
  have hl : IsLocallyConstant G := (d.locallyConstant_finite_schwartz p Φ).1.mul
    ((d.character.locallyConstant_finiteValue p).comp_continuous
      (continuous_snd.neg.div (Units.continuous_val.comp continuous_fst) (fun x => x.1.ne_zero)))
  obtain ⟨L,hL⟩ := d.exists_leading_finite p
  obtain ⟨C,hC,hout⟩ := (d.finite_support_and_germ_of_isLeadingTerm p Φ (hL Φ)).1
  have hs := locallyConstant_slices_of_localSupport hl (fun a => ⟨Prod.snd '' C,hC.image continuous_snd,
    Eventually.of_forall (fun (b : Kˣ) (y : K) hy => by
      have h := (hout (b.val,y) (fun hin => hy ⟨_,hin,rfl⟩)).1
      rw [xChart_unit_eval] at h
      change Φ.val.1 b y * _ = 0
      rw [h,zero_mul])⟩)
  exact hs.comp (fun f => ∫ y, f y ∂selfDual F d.character vp)

theorem continuous_jacquet (v : Place F) (Φ : d.schwartz v) : Continuous (d.jacquet v Φ) := by
  cases v with
  | inr p => exact (d.locallyConstant_finite_jacquet p Φ).continuous
  | inl w =>
    let vi : Place F := .inl w
    let K := LocalField F vi
    letI : FirstCountableTopology Kˣ := Units.isEmbedding_val₀.firstCountableTopology
    rw [continuous_iff_continuousAt]
    intro x
    let m := modulus F vi x.val / 2
    have hpos : 0 < modulus F vi x.val := pow_pos (norm_pos_iff.mpr x.ne_zero) _
    obtain ⟨B,hB⟩ := d.arch_jacquet_majorant w Φ (half_pos hpos)
    have near : ∀ᶠ a : Kˣ in 𝓝 x, m < modulus F vi a.val :=
      ((Units.continuous_val.norm.pow w.mult).continuousAt).eventually (lt_mem_nhds (half_lt_self hpos))
    refine continuousAt_of_dominated (bound := fun y : K => B*((1+‖y‖)^3)⁻¹)
      (.of_forall fun a => (d.integrable_jacquet vi Φ a).aestronglyMeasurable) ?_ ((d.arch_integrable_inv_cube w).const_mul B) ?_
    · filter_upwards [near] with a ha
      exact .of_forall fun y => by simpa only [norm_mul,d.character.norm_localValue,mul_one] using hB a ha.le y
    · filter_upwards with y
      exact (((d.continuous_arch_schwartz_X w Φ).comp (continuous_id.prodMk continuous_const)).mul
        ((d.character.continuous_localValue vi).comp (continuous_const.div Units.continuous_val (fun a => a.ne_zero)))).continuousAt

theorem jacquet_sub (v : Place F) (Φ Ψ : d.schwartz v) :
    d.jacquet v (Φ-Ψ) = d.jacquet v Φ - d.jacquet v Ψ := by
  funext x
  unfold jacquet
  change (∫ y, (Φ.val.1 x y - Ψ.val.1 x y) * _ ∂_) = _ - _
  simp_rw [sub_mul]
  exact integral_sub (d.integrable_jacquet v Φ x) (d.integrable_jacquet v Ψ x)

theorem jacquet_smul (v : Place F) (a : ℂ) (Φ : d.schwartz v) :
    d.jacquet v (a • Φ) = a • d.jacquet v Φ := by
  funext x
  unfold jacquet
  change (∫ y, (a * Φ.val.1 x y) * _ ∂_) = a * _
  simp_rw [mul_assoc,integral_const_mul]

/-- The action of an upper unipotent multiplies the Jacquet integral by ψ(u). -/
theorem jacquet_upper (v : Place F) (u : LocalField F v) {g : d.Operators v} (hg : d.IsUpper v u g)
    (Φ : d.schwartz v) : d.jacquet v (g Φ) = d.character.localValue F v u • d.jacquet v Φ := by
  funext x
  let dx := selfDual F d.character v
  letI : dx.IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  let ψ := d.character.localValue F v
  let A (y : LocalField F v) := Φ.val.1 x y * ψ (-y/x.val)
  have he (y : LocalField F v) : (g Φ).val.1 x y * ψ (-y/x.val) = ψ u * A (y + u*x.val) := by
    rw [(hg Φ).1]
    have phase := d.character.localValue_add v u (-(y+u*x.val)/x.val)
    rw [show u + -(y+u*x.val)/x.val = -y/x.val by field_simp; ring] at phase
    change _ = ψ u * (Φ.val.1 x (y+u*x.val) * ψ (-(y+u*x.val)/x.val))
    change ψ (-y/x.val) = _ at phase
    rw [phase]
    ring
  change (∫ y, (g Φ).val.1 x y * ψ (-y/x.val) ∂dx) = ψ u * ∫ y, A y ∂dx
  simp_rw [he,integral_const_mul,integral_add_right_eq_self]

/-- Normalized shear difference used to regularize the line integral in §10. -/
def jacquetDifference (v : Place F) (u : LocalField F v) (g : d.Operators v) :
    d.schwartz v →ₗ[ℂ] d.schwartz v :=
  (d.character.localValue F v u - 1)⁻¹ • (g.toLinearMap - LinearMap.id)

theorem jacquet_difference (v : Place F) (u : LocalField F v) (hu : d.character.localValue F v u ≠ 1)
    {g : d.Operators v} (hg : d.IsUpper v u g) (Φ : d.schwartz v) :
    d.jacquet v (d.jacquetDifference v u g Φ) = d.jacquet v Φ := by
  change d.jacquet v ((d.character.localValue F v u - 1)⁻¹ • (g Φ - Φ)) = _
  rw [d.jacquet_smul,d.jacquet_sub,d.jacquet_upper v u hg]
  rw [show d.character.localValue F v u • d.jacquet v Φ - d.jacquet v Φ =
    (d.character.localValue F v u - 1) • d.jacquet v Φ from by rw [sub_smul,one_smul]]
  rw [smul_smul,inv_mul_cancel₀ (sub_ne_zero.mpr hu),one_smul]

theorem fourier_difference (v : Place F) (u : LocalField F v) {g : d.Operators v} (hg : d.IsUpper v u g)
    (Φ : d.schwartz v) :
    d.fourier v (d.jacquetDifference v u g Φ) = d.jacquetDifference v u g (d.fourier v Φ) := by
  change d.fourier v ((d.character.localValue F v u - 1)⁻¹ • (g Φ - Φ)) = (d.character.localValue F v u - 1)⁻¹ • (g (d.fourier v Φ) - d.fourier v Φ)
  rw [map_smul,map_sub,d.fourier_upper v u hg]

/-- Iteration preserves both Jacquet integrals. The paper uses k = 3. -/
theorem jacquet_difference_iterate (v : Place F) (u : LocalField F v) (hu : d.character.localValue F v u ≠ 1)
    {g : d.Operators v} (hg : d.IsUpper v u g) (k : ℕ) (Φ : d.schwartz v) :
    let Ξ := (d.jacquetDifference v u g)^[k] Φ
    d.jacquet v Ξ = d.jacquet v Φ ∧ d.jacquet v (d.fourier v Ξ) = d.jacquet v (d.fourier v Φ) := by
  induction k with
  | zero => exact ⟨rfl,rfl⟩
  | succ k ih =>
    simp only [Function.iterate_succ_apply',d.fourier_difference v u hg,d.jacquet_difference v u hu hg]
    exact ih

/-- Binomial expansion of the normalized shear differences on the X-chart.
For k = 3 this is the paper's third-difference formula. -/
theorem jacquetDifference_iterate_X (v : Place F) (u : LocalField F v) {g : d.Operators v}
    (hg : d.IsUpper v u g) (Φ : d.schwartz v) (k : ℕ) (x : (LocalField F v)ˣ) (y : LocalField F v) :
    (((d.jacquetDifference v u g)^[k] Φ).val.1 x y) = (d.character.localValue F v u - 1)⁻¹ ^ k *
      ∑ j ∈ Finset.range (k+1), ((-1 : ℤ)^(k-j) * k.choose j) • Φ.val.1 x (y+j • (u*x.val)) := by
  rw [← fwdDiff_iter_eq_sum_shift]
  induction k generalizing y with
  | zero => simp
  | succ k ih =>
    let Ψ := (d.jacquetDifference v u g)^[k] Φ
    let a := (d.character.localValue F v u - 1)⁻¹
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply']
    change a * ((g Ψ).val.1 x y - Ψ.val.1 x y) = _
    rw [(hg Ψ).1]
    dsimp only [Ψ]
    rw [ih,ih,pow_succ']
    unfold fwdDiff
    ring

theorem jacquetDifference_axis (v : Place F) (u : LocalField F v) {g : d.Operators v}
    (hg : d.IsUpper v u g) (Φ : d.schwartz v) (y : (LocalField F v)ˣ) :
    (d.jacquetDifference v u g Φ).val.2 0 y = 0 := by
  change _ * ((g Φ).val.2 0 y - Φ.val.2 0 y) = 0
  rw [(hg Φ).2,sub_self,mul_zero]

end MetaplecticPoisson.Datum
