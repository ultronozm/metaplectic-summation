import MetaplecticSummation.MultiplicativeMeasure
import MetaplecticSummation.FiniteFourierInversion
import MetaplecticSummation.MarginalRoots

/-! The linear-factor calculation of Appendix A at finite places. -/

noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField IsDedekindDomain MeasureTheory Set
open scoped Topology
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

private instance finiteProper (p : HeightOneSpectrum (𝓞 F)) : ProperSpace (LocalField F (.inr p)) := by
  letI : NontriviallyNormedField (p.adicCompletion F) := FinitePlace.nontriviallyNormedCompletion p
  exact .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace (p.adicCompletion F)

omit [NeZero n] in
/-- The tail of |u|⁻¹ is integrable for multiplicative Haar measure.
Inversion changes the tail to an additive ball of finite volume. -/
theorem integrable_inv_tail (p : HeightOneSpectrum (𝓞 F)) (R : ℝ) :
    let v : Place F := .inr p
    Integrable (fun u : (LocalField F v)ˣ => if ‖u.val⁻¹‖ ≤ R then ‖u.val‖⁻¹ else 0) (d.lineMeasure v) := by
  let v : Place F := .inr p
  let K := LocalField F v
  let dx := selfDual F d.character v
  letI : dx.IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  let B := Metric.closedBall (0 : K) R
  let f := B.indicator (fun _ => (1 : ℝ))
  have hi : Integrable f dx := by
    apply (integrable_indicator_iff Metric.isClosed_closedBall.measurableSet).mpr
    exact integrableOn_const (isCompact_closedBall (0 : K) R).measure_ne_top
  have h := (d.reciprocal_integral v 1 f hi).1
  apply h.congr
  filter_upwards with u
  by_cases hu : ‖u.val‖⁻¹ ≤ R <;> simp [v,modulus,f,B,Metric.mem_closedBall,hu]

/-- A single cutoff near zero suffices for all affine factors whose test
frequency lies in the support of h. -/
private theorem uniform_difference_cutoff {K : Type*} [NormedField K] {f h : K → ℂ}
    (hl : IsLocallyConstant f) (hk : HasCompactSupport h) (a : K) :
    ∃ ε > (0 : ℝ), ∀ t u : K, ‖u‖ < ε → h t * (f ((t-a)*u) - f u) = 0 := by
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hl.eventually_eq 0)
  obtain ⟨B,hB⟩ := hk.exists_bound_of_continuousOn (f := fun t : K => t-a)
    (continuous_id.sub continuous_const).continuousOn
  let M := max 1 B
  have hM : 0 < M := zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨r/M,div_pos hr hM,fun t u hu => ?_⟩
  by_cases ht : h t = 0
  · rw [ht,zero_mul]
  have ht' := hB t (subset_tsupport h (Function.mem_support.mpr ht))
  have hu' : M*‖u‖ < r := by simpa [mul_comm] using (lt_div_iff₀ hM).mp hu
  have hsmall : ‖u‖ < r := (le_mul_of_one_le_left (norm_nonneg _) (le_max_left _ _ : 1 ≤ M)).trans_lt hu'
  have hprod : ‖(t-a)*u‖ < r := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (ht'.trans (le_max_right _ _)) (norm_nonneg _)).trans_lt hu'
  have e₁ := hball (show (t-a)*u ∈ Metric.ball 0 r by simpa using hprod)
  have e₂ := hball (show u ∈ Metric.ball 0 r by simpa using hsmall)
  change f ((t-a)*u) = f 0 at e₁
  change f u = f 0 at e₂
  rw [e₁,e₂,sub_self,mul_zero]

private theorem norm_bounded {K E : Type*} [TopologicalSpace K] [NormedAddCommGroup E]
    {f : K → E} (hc : Continuous f) (hk : HasCompactSupport f) : ∃ B : ℝ, ∀ t, ‖f t‖ ≤ B := by
  obtain ⟨B,hB⟩ := (hk.isCompact_range hc).exists_bound_of_continuousOn (f := id) continuous_id.continuousOn
  exact ⟨B,fun t => hB (f t) ⟨t,rfl⟩⟩

omit [NeZero n] in
/-- Absolute convergence of the double integral before the zero-mean subtraction
is removed. Its only possible singularities are at zero and infinity in u. -/
theorem finite_difference_pair_integrable (p : HeightOneSpectrum (𝓞 F)) {f h : LocalField F (.inr p) → ℂ}
    (hf : Bruhat (.inr p) f) (hh : Bruhat (.inr p) h) (a : LocalField F (.inr p)) :
    let v : Place F := .inr p
    Integrable (fun z : (LocalField F v)ˣ × LocalField F v =>
      h z.2 * (f ((z.2-a)*z.1.val) - f z.1.val)) ((d.lineMeasure v).prod (selfDual F d.character v)) := by
  let v : Place F := .inr p
  let K := LocalField F v
  let dx := selfDual F d.character v
  let ν := d.lineMeasure v
  letI : dx.IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  have fc : Continuous f := hf.1.continuous
  have hc : Continuous h := hh.1.continuous
  let D (u : Kˣ) (t : K) := h t * (f ((t-a)*u.val) - f u.val)
  have hmeas : AEStronglyMeasurable (Function.uncurry D) (ν.prod dx) := by
    apply Continuous.aestronglyMeasurable
    dsimp [Function.uncurry,D]
    fun_prop
  obtain ⟨B,hB⟩ := norm_bounded hc hh.2
  have hweight : HasCompactSupport (fun t : K => ‖t‖ * ‖f t‖) := hf.2.norm.mul_left
  obtain ⟨C,hC⟩ := norm_bounded (continuous_norm.mul fc.norm) hweight
  have sectionInt (u : Kˣ) : Integrable (D u) dx :=
    (hc.mul ((fc.comp ((continuous_id.sub continuous_const).mul continuous_const)).sub continuous_const)).integrable_of_hasCompactSupport hh.2.mul_right
  have hhi := hh.integrable d
  let A := B * (∫ x, ‖f x‖ ∂dx) + (∫ x, ‖h x‖ ∂dx)*C
  obtain ⟨ε,hε,hs⟩ := uniform_difference_cutoff hf.1 hh.2 a
  change Integrable (Function.uncurry D) (ν.prod dx)
  refine (integrable_prod_iff hmeas).2 ⟨Filter.Eventually.of_forall sectionInt,?_⟩
  apply ((d.integrable_inv_tail p ε⁻¹).const_mul A).mono'
    (hmeas.norm.integral_prod_right')
  filter_upwards with u
  rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
  by_cases hu : ‖u.val⁻¹‖ ≤ ε⁻¹
  · rw [if_pos hu]
    let g (t : K) := f ((t-a)*u.val)
    let e := (Homeomorph.addRight (-a)).trans (Homeomorph.mulRight₀ u.val u.ne_zero)
    have gk : HasCompactSupport g := by
      have hg := hf.2.comp_homeomorph e
      change HasCompactSupport (fun t : K => f ((t + -a)*u.val)) at hg
      simpa only [g,sub_eq_add_neg] using hg
    have gc : Continuous g := fc.comp ((continuous_id.sub continuous_const).mul continuous_const)
    have gInt := gc.integrable_of_hasCompactSupport (μ := dx) gk
    have he := d.hat_affine v (fun x => (‖f x‖ : ℂ)) a 0 u
    have hscale : (∫ t, ‖g t‖ ∂dx) = (∫ x, ‖f x‖ ∂dx) / ‖u.val‖ := by
      apply Complex.ofReal_injective
      simpa only [hat,zero_mul,zero_div,Character.localValue_zero,mul_one,integral_complex_ofReal,
        Complex.ofReal_div,g,dx,v,modulus] using he
    have hbnd : ‖f u.val‖ ≤ C * ‖u.val‖⁻¹ := by
      rw [← div_eq_mul_inv,le_div_iff₀ (norm_pos_iff.mpr u.ne_zero),mul_comm]
      simpa only [Pi.mul_apply,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))] using hC u.val
    calc
      _ ≤ ∫ t, B * ‖g t‖ + ‖h t‖ * ‖f u.val‖ ∂dx := by
        apply integral_mono (sectionInt u).norm ((gInt.norm.const_mul B).add (hhi.norm.mul_const _))
        intro t
        change ‖h t * (g t - f u.val)‖ ≤ _
        rw [norm_mul]
        calc
          _ ≤ ‖h t‖ * (‖g t‖ + ‖f u.val‖) := mul_le_mul_of_nonneg_left (norm_sub_le ..) (norm_nonneg _)
          _ ≤ _ := by rw [mul_add]; exact add_le_add (mul_le_mul_of_nonneg_right (hB t) (norm_nonneg _)) le_rfl
      _ = B * ((∫ x, ‖f x‖ ∂dx) / ‖u.val‖) + (∫ x, ‖h x‖ ∂dx)*‖f u.val‖ := by
        rw [integral_add (gInt.norm.const_mul B) (hhi.norm.mul_const _),integral_const_mul,integral_mul_const,hscale]
      _ ≤ _ := by
        dsimp only [A]
        rw [add_mul,mul_assoc,mul_assoc,div_eq_mul_inv]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hbnd (integral_nonneg fun _ => norm_nonneg _))
  · have hu' : ‖u.val‖ < ε := by
      rw [norm_inv,not_le] at hu
      exact (inv_lt_inv₀ hε (norm_pos_iff.mpr u.ne_zero)).mp hu
    have hz (t : K) : D u t = 0 := hs t u.val hu'
    rw [if_neg hu]
    simp [hz]

omit [NeZero n] in
private theorem integrable_weight_div_norm (p : HeightOneSpectrum (𝓞 F)) {ρ : LocalField F (.inr p) → ℂ}
    (hρ : Bruhat (.inr p) ρ) (h₀ : ρ 0 = 0) :
    Integrable (fun x => ‖ρ x‖ / ‖x‖) (selfDual F d.character (.inr p)) := by
  let dx := selfDual F d.character (.inr p)
  letI : dx.IsAddHaarMeasure := (existsUnique_selfDual F d.character (.inr p)).exists.choose_spec.1
  apply Continuous.integrable_of_hasCompactSupport (μ := dx)
  · apply continuous_iff_continuousAt.mpr
    intro x
    by_cases hx : x = 0
    · subst x
      apply (continuousAt_const (y := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [hρ.1.eventually_eq 0] with y hy
      change ρ y = ρ 0 at hy
      simp [hy,h₀]
    · exact hρ.1.continuous.norm.continuousAt.div continuous_norm.continuousAt (norm_ne_zero_iff.mpr hx)
  · simp only [div_eq_mul_inv]
    exact hρ.2.norm.mul_right

omit [NeZero n] in
/-- Absolute convergence and evaluation of the double integral after affine
Fourier pairing. The test ρ vanishes near zero and can have arbitrary conductor. -/
private theorem finite_linearFactor_dual (p : HeightOneSpectrum (𝓞 F)) {f ρ : LocalField F (.inr p) → ℂ}
    (hf : Bruhat (.inr p) f) (hρ : Bruhat (.inr p) ρ) (h₀ : ρ 0 = 0) (a : LocalField F (.inr p)) :
    let v : Place F := .inr p
    let J := fun (μ : LocalField F v) (u : (LocalField F v)ˣ) =>
      ρ μ * (d.hat v f (μ/u.val) / (modulus F v u.val : ℂ)) * d.character.localValue F v (μ*a)
    let dx := selfDual F d.character v
    let ν := d.lineMeasure v
    Integrable (Function.uncurry J) (dx.prod ν) ∧
      (∫ u, ∫ μ, J μ u ∂dx ∂ν) =
        f 0 * d.lineIntegral v (fun μ => ρ μ.val * d.character.localValue F v (μ.val*a)) := by
  let v : Place F := .inr p
  let K := LocalField F v
  let dx := selfDual F d.character v
  let ν := d.lineMeasure v
  letI : dx.IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  letI : NullSingletonClass dx := d.selfDual_nullSingleton v
  let g := d.hat v f
  have hg := d.hat_finite_bruhat p hf
  have gi : Integrable g dx := hg.integrable d
  let c (μ : K) := ρ μ * d.character.localValue F v (μ*a)
  let J (μ : K) (u : Kˣ) := ρ μ * (g (μ/u.val) / (modulus F v u.val : ℂ)) * d.character.localValue F v (μ*a)
  have jmeas : AEStronglyMeasurable (Function.uncurry J) (dx.prod ν) := by
    have gc : Continuous g := hg.1.continuous
    have hc : Continuous ρ := hρ.1.continuous
    have ψc := d.character.continuous_localValue v
    apply Continuous.aestronglyMeasurable
    have hu : Continuous (fun z : K × Kˣ => z.2.val) := Units.continuous_val.comp continuous_snd
    have ht := continuous_fst.div hu (fun z => z.2.ne_zero)
    have hden := (Complex.continuous_ofReal.comp hu.norm)
    exact ((hc.comp continuous_fst).mul ((gc.comp ht).div hden
      (fun z => Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr z.2.ne_zero)))).mul
      (ψc.comp (continuous_fst.mul continuous_const))
  have eqn (μ : K) (u : Kˣ) : J μ u = c μ * ((‖u.val‖⁻¹ : ℝ) • g (μ/u.val)) := by
    simp only [J,c,v,modulus,Complex.real_smul,Complex.ofReal_inv,div_eq_mul_inv]
    ring
  have jInt : Integrable (Function.uncurry J) (dx.prod ν) := by
    apply (integrable_prod_iff jmeas).2
    constructor
    · filter_upwards [dx.ae_ne 0] with μ hμ
      simp_rw [Function.uncurry,eqn]
      exact ((d.reciprocal_integral v (Units.mk0 μ hμ) g gi).1).const_mul (c μ)
    · have hi := (d.integrable_weight_div_norm p hρ h₀).mul_const (∫ t, ‖g t‖ ∂dx)
      apply hi.congr
      filter_upwards [dx.ae_ne 0] with μ hμ
      have hr := (d.reciprocal_integral v (Units.mk0 μ hμ) (fun x => ‖g x‖) gi.norm).2
      change (∫ u : Kˣ, ‖u.val‖⁻¹ * ‖g (μ/u.val)‖ ∂ν) = ‖μ‖⁻¹ * ∫ x, ‖g x‖ ∂dx at hr
      have hc : ‖c μ‖ = ‖ρ μ‖ := by simp only [c,norm_mul,d.character.norm_localValue,mul_one]
      have hab (u : Kˣ) : |‖u.val‖| = ‖u.val‖ := abs_of_nonneg (norm_nonneg _)
      simp only [Function.uncurry,eqn,norm_mul,norm_smul,Real.norm_eq_abs,abs_inv,hab,hc,
        integral_const_mul]
      rw [hr,div_eq_mul_inv,mul_assoc]
  refine ⟨jInt,(integral_integral_swap jInt).symm.trans ?_⟩
  unfold lineIntegral
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [dx.ae_ne 0] with μ hμ
  have hr := (d.reciprocal_integral v (Units.mk0 μ hμ) g gi).2
  change (∫ u : Kˣ, ‖u.val‖⁻¹ • g (μ/u.val) ∂ν) = ‖μ‖⁻¹ • ∫ x, g x ∂dx at hr
  change (∫ u, J μ u ∂ν) = _
  simp_rw [eqn]
  rw [integral_const_mul,hr]
  rw [show (∫ x, g x ∂dx) = f 0 from d.integral_hat_finite p hf]
  change c μ * ((‖μ‖⁻¹ : ℝ) • f 0) = f 0 *
    (if hz : μ ≠ 0 then ρ (Units.mk0 μ hz).val * d.character.localValue F v ((Units.mk0 μ hz).val*a) / (‖μ‖ : ℂ) else 0)
  rw [dif_pos (show μ ≠ 0 from hμ)]
  simp only [Units.val_mk0,c,Complex.real_smul,Complex.ofReal_inv,div_eq_mul_inv]
  ring

/-- The linear-factor identity of Appendix A, including absolute convergence,
for any finite completion and the positive-phase Fourier convention. -/
theorem finite_linearFactor (p : HeightOneSpectrum (𝓞 F)) {f ρ : LocalField F (.inr p) → ℂ}
    (hf : Bruhat (.inr p) f) (hρ : Bruhat (.inr p) ρ) (h₀ : ρ 0 = 0)
    (b : (LocalField F (.inr p))ˣ) (a : LocalField F (.inr p)) :
    let v : Place F := .inr p
    let H := fun t => d.hat v ρ t * d.differenceIntegral v f (b^n) (t-a)
    Integrable H (selfDual F d.character v) ∧
      (∫ t, H t ∂(selfDual F d.character v)) = f 0 *
        d.lineIntegral v (fun μ => ρ μ.val * d.character.localValue F v (μ.val*a)) := by
  let v : Place F := .inr p
  let K := LocalField F v
  let dx := selfDual F d.character v
  let ν := d.lineMeasure v
  letI : dx.IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  letI : NullSingletonClass dx := d.selfDual_nullSingleton v
  let h := d.hat v ρ
  have hh := d.hat_finite_bruhat p hρ
  let D (u : Kˣ) (t : K) := h t * (f ((t-a)*u.val) - f u.val)
  have hD : Integrable (Function.uncurry D) (ν.prod dx) := d.finite_difference_pair_integrable p hf hh a
  have he : (fun t => ∫ u, D u t ∂ν) =ᵐ[dx] (fun t => h t * d.differenceIntegral v f (b^n) (t-a)) := by
    filter_upwards [dx.ae_ne a] with t ht
    have hne := sub_ne_zero.mpr ht
    simp only [differenceIntegral,dif_pos hne,← d.integral_lineMeasure,D,integral_const_mul]
    congr 1
    apply integral_congr_ae
    filter_upwards with u
    have hs : d.symbol v u (b^n) = 1 := by
      change (d.unitPairing v u (b^n)).val = 1
      rw [map_pow,d.unitPairing_pow,Units.val_one]
    simp [marginalDifference,hs]
  refine ⟨hD.integral_prod_right.congr he, (integral_congr_ae he.symm).trans ?_⟩
  refine (integral_integral_swap hD).symm.trans ?_
  refine Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun u => ?_))
    (d.finite_linearFactor_dual p hf hρ h₀ a).2
  refine Eq.trans ?_ (d.finite_linearFactor_pairing p hf hρ a u)
  let g (t : K) := f ((t-a)*u.val)
  have gc : Continuous g := hf.1.continuous.comp ((continuous_id.sub continuous_const).mul continuous_const)
  have hc : Continuous h := hh.1.continuous
  have hi : Integrable (fun t => h t * g t) dx := (hc.mul gc).integrable_of_hasCompactSupport hh.2.mul_right
  have hz : (∫ t, h t ∂dx) = 0 := (d.integral_hat_finite p hρ).trans h₀
  change (∫ t, h t * (g t - f u.val) ∂dx) = ∫ t, h t * g t ∂dx
  simp_rw [mul_sub]
  rw [integral_sub hi ((hh.integrable d).mul_const _),integral_mul_const,hz,zero_mul,sub_zero]

/-- The tested integral for an n-th power equals the sum of the multiplicative
Fourier integrals attached to its distinct roots. -/
theorem finite_root_contribution (p : HeightOneSpectrum (𝓞 F)) {f ρ : LocalField F (.inr p) → ℂ}
    (hf : Bruhat (.inr p) f) (hρ : Bruhat (.inr p) ρ) (h₀ : ρ 0 = 0)
    (b : (LocalField F (.inr p))ˣ) :
    let v : Place F := .inr p
    (∫ t, d.hat v ρ t * d.differenceIntegral v f (b^n) (t^n-(b^n).val) ∂(selfDual F d.character v)) =
      f 0 * ∑ a ∈ Polynomial.nthRootsFinset n (b^n).val,
        d.lineIntegral v (fun μ => ρ μ.val * d.character.localValue F v (μ.val*a)) := by
  dsimp only
  rw [d.integral_difference_roots _ f _ _ ⟨b,rfl⟩
    (fun c => d.marginalDifference_finite_integrable p hf _ c)
    (fun a _ => (d.finite_linearFactor p hf hρ h₀ b a).1),Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => (d.finite_linearFactor p hf hρ h₀ b a).2

end MetaplecticPoisson.Datum
