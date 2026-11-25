import MetaplecticSummation.ArchimedeanFourierSchwartz
import MetaplecticSummation.Jacquet.WeightIntegrability
import MetaplecticSummation.LinearFactor
import MetaplecticSummation.Hilbert.ArchimedeanRadical

/-! Absolute convergence of the subtracted, one-root integral in Appendix A. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField MeasureTheory Set
open scoped Topology
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} (d : Datum F n) (w : InfinitePlace F)
local notation "v" => (Sum.inl w : Place F)
local notation "K" => LocalField F v
local notation "dx" => selfDual F d.character v

theorem arch_bruhat_estimates {f : K → ℂ} (hf : Bruhat v f) :
    (∃ C : NNReal, LipschitzWith C f) ∧ (∀ k : ℕ, ∃ C : ℝ, ∀ x, ‖x‖^k * ‖f x‖ ≤ C) ∧
    Integrable (fun x => ‖x‖ * ‖f x‖) dx := by
  letI : MeasurableSpace w.Completion := borel _
  letI : BorelSpace w.Completion := ⟨rfl⟩
  let μ : Measure w.Completion := dx
  letI : μ.IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  have go {L : Type} [NormedField L] [NormedAlgebra ℝ L] [FiniteDimensional ℝ L]
      [MeasurableSpace L] [BorelSpace L] [SecondCountableTopology L]
      (e : w.Completion ≃+* L) (he : Isometry e) (g : SchwartzMap L ℂ) (hg : ∀ x, f x = g (e x)) :
      (∃ C : NNReal, LipschitzWith C f) ∧ (∀ k : ℕ, ∃ C : ℝ, ∀ x, ‖x‖^k * ‖f x‖ ≤ C) ∧
      Integrable (fun x => ‖x‖ * ‖f x‖) dx := by
    let i : w.Completion ≃ᵢ L := ⟨e.toEquiv,he⟩
    letI : (μ.map e).IsAddHaarMeasure := e.toAddEquiv.isAddHaarMeasure_map μ he.continuous i.symm.continuous
    let C : NNReal := ⟨SchwartzMap.seminorm ℝ 0 1 g,apply_nonneg _ _⟩
    have lip : LipschitzWith C g := by
      apply lipschitzWith_of_nnnorm_fderiv_le g.differentiable
      intro t
      change ‖fderiv ℝ g t‖ ≤ SchwartzMap.seminorm ℝ 0 1 g
      simpa only [norm_iteratedFDeriv_one] using g.norm_iteratedFDeriv_le_seminorm ℝ 1 t
    refine ⟨⟨C,by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      rw [hg x,hg y]
      have hd := lip.dist_le_mul (e x) (e y)
      rw [he.dist_eq x y] at hd
      exact hd⟩,fun k => ⟨SchwartzMap.seminorm ℝ k 0 g,fun x => ?_⟩,?_⟩
    · have bound := g.norm_pow_mul_le_seminorm ℝ k (e x)
      exact (congrArg₂ (fun r : ℝ => fun z : ℂ => r^k * ‖z‖)
        (he.norm_map_of_map_zero e.map_zero x).symm (hg x)).trans_le bound
    · let H (y : L) := ‖y‖ * ‖g y‖
      have hi : Integrable H (μ.map e) := by
        simpa only [H,pow_one] using g.integrable_pow_mul (μ.map e) 1
      have hc : Continuous H := by fun_prop
      have hp := (integrable_map_measure hc.aestronglyMeasurable he.continuous.aemeasurable).mp hi
      apply hp.congr
      filter_upwards with x
      change ‖e x‖ * ‖g (e x)‖ = _
      exact congrArg₂ (fun r : ℝ => fun z : ℂ => r * ‖z‖)
        (he.norm_map_of_map_zero e.map_zero x) (hg x).symm
  dsimp only [Bruhat] at hf
  split at hf <;> obtain ⟨g,hg⟩ := hf
  · exact go _ (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal _) g hg
  · exact go _ (InfinitePlace.Completion.isometry_extensionEmbedding w) g hg

private theorem affine_integrable {f : K → ℂ} (hf : Integrable f dx) (a : K) (u : Kˣ) :
    Integrable (fun t => f ((t-a)*u.val)) dx := by
  letI : (dx).IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  let e := MeasurableEquiv.smul (α := K) u
  have hi : Integrable (fun t : K => f (u.val*t)) dx := by
    apply (e.measurableEmbedding.integrable_map_iff (g := f)).mp
    change Integrable f (Measure.map (fun t => u.val*t) dx)
    rw [d.map_local_mul]
    exact hf.smul_measure_nnreal
  simpa only [Function.comp_def,sub_eq_add_neg,mul_comm u.val] using
    (measurePreserving_add_right dx (-a)).integrable_comp_of_integrable hi

theorem arch_min_weight :
    Integrable (fun u : Kˣ => min ‖u.val‖ ‖u.val‖⁻¹) (d.lineMeasure v) := by
  letI : LocallyCompactSpace K := inferInstanceAs (LocallyCompactSpace w.Completion)
  letI : NontriviallyNormedField K := archNontriviallyNormedCompletion w
  letI : ProperSpace K := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace _
  letI : SecondCountableTopology Kˣ := Units.isEmbedding_val₀.secondCountableTopology
  obtain ⟨c,hc₀,hc₁⟩ := NormedField.exists_norm_lt_one K
  have hweight := integrable_units_min_rpow (d.lineMeasure v) (Units.mk0 c (norm_pos_iff.mp hc₀)) hc₁ (zero_lt_one : (0:ℝ) < 1)
  simpa only [Real.rpow_one,Real.rpow_neg_one] using hweight

/-- Absolute convergence of the subtracted affine integral at a real or complex place. -/
theorem arch_difference_pair_integrable {f h : K → ℂ}
    (hf : Bruhat v f) (hh : Bruhat v h) (a : K) :
    Integrable (fun z : Kˣ × K => h z.2 * (f ((z.2-a)*z.1.val) - f z.1.val))
      ((d.lineMeasure v).prod dx) := by
  letI : (dx).IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  let ν := d.lineMeasure v
  let D (u : Kˣ) (t : K) := h t * (f ((t-a)*u.val) - f u.val)
  obtain ⟨⟨L,lip⟩,fBound,_⟩ := d.arch_bruhat_estimates w hf
  obtain ⟨⟨_,hlip⟩,hBound,hMoment⟩ := d.arch_bruhat_estimates w hh
  obtain ⟨B,hB⟩ := hBound 0
  obtain ⟨C,hC⟩ := fBound 1
  obtain ⟨M,hM⟩ := fBound 0
  simp only [pow_zero,one_mul] at hB hM
  simp only [pow_one] at hC
  have fc := lip.continuous
  have hc := hlip.continuous
  have hhi := hh.integrable d
  have hmeas : AEStronglyMeasurable (Function.uncurry D) (ν.prod dx) := by
    apply Continuous.aestronglyMeasurable
    dsimp [Function.uncurry,D]
    fun_prop
  have sectionInt (u : Kˣ) : Integrable (D u) dx := by
    apply hhi.mul_bdd ((fc.comp ((continuous_id.sub continuous_const).mul continuous_const)).sub
      continuous_const).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun t => (norm_sub_le ..).trans (add_le_add (hM _) (hM _))
  let W (t : K) := ‖t‖ * ‖h t‖ + (‖a‖ + 1) * ‖h t‖
  have wInt : Integrable W dx := hMoment.add (hhi.norm.const_mul _)
  let A := (L : ℝ) * ∫ t, W t ∂dx
  let T := B * (∫ x, ‖f x‖ ∂dx) + (∫ x, ‖h x‖ ∂dx)*C
  change Integrable (Function.uncurry D) (ν.prod dx)
  refine (integrable_prod_iff hmeas).2 ⟨Filter.Eventually.of_forall sectionInt,?_⟩
  apply ((d.arch_min_weight w).const_mul (max A T)).mono' hmeas.norm.integral_prod_right'
  filter_upwards with u
  rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
  have hu := norm_pos_iff.mpr u.ne_zero
  by_cases hs : ‖u.val‖ ≤ 1
  · rw [min_eq_left (hs.trans (one_le_inv₀ hu |>.2 hs))]
    calc
      _ ≤ ∫ t, ((L : ℝ)*‖u.val‖) * W t ∂dx := by
        apply integral_mono (sectionInt u).norm (wInt.const_mul _)
        intro t
        have hd := lip.dist_le_mul ((t-a)*u.val) u.val
        rw [dist_eq_norm,dist_eq_norm,show (t-a)*u.val-u.val = (t-a-1)*u.val by ring,norm_mul] at hd
        have ht : ‖t-a-1‖ ≤ ‖t‖+‖a‖+1 :=
          (norm_sub_le ..).trans (add_le_add (norm_sub_le ..) (norm_one.le))
        dsimp only [D,W]
        rw [norm_mul]
        calc
          _ ≤ ‖h t‖ * ((L : ℝ) * ((‖t‖+‖a‖+1)*‖u.val‖)) := mul_le_mul_of_nonneg_left
            (hd.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ht hu.le) L.coe_nonneg)) (norm_nonneg _)
          _ = _ := by ring
      _ = A * ‖u.val‖ := by rw [integral_const_mul]; dsimp [A]; ring
      _ ≤ _ := by gcongr; exact le_max_left _ _
  · have hs' : 1 ≤ ‖u.val‖ := le_of_not_ge hs
    rw [min_eq_right ((inv_le_one_of_one_le₀ hs').trans hs')]
    let g (t : K) := f ((t-a)*u.val)
    have gi : Integrable g dx := d.affine_integrable w (hf.integrable d) a u
    have he := d.hat_affine v (fun x => (‖f x‖ : ℂ)) a 0 u
    have hscale : (∫ t, ‖g t‖ ∂dx) = (∫ x, ‖f x‖ ∂dx) / modulus F v u.val := by
      apply Complex.ofReal_injective
      simpa only [hat,zero_mul,zero_div,Character.localValue_zero,mul_one,integral_complex_ofReal,
        Complex.ofReal_div,g] using he
    have hm : ‖u.val‖ ≤ modulus F v u.val := by
      exact le_self_pow₀ hs' w.mult_ne_zero
    have hbnd : ‖f u.val‖ ≤ C * ‖u.val‖⁻¹ := by
      rw [← div_eq_mul_inv,le_div_iff₀ hu,mul_comm]
      exact hC _
    calc
      _ ≤ ∫ t, B * ‖g t‖ + ‖h t‖ * ‖f u.val‖ ∂dx := by
        apply integral_mono (sectionInt u).norm ((gi.norm.const_mul B).add (hhi.norm.mul_const _))
        intro t
        change ‖h t * (g t - f u.val)‖ ≤ _
        rw [norm_mul]
        calc
          _ ≤ ‖h t‖ * (‖g t‖ + ‖f u.val‖) := by gcongr; apply norm_sub_le
          _ ≤ _ := by
            rw [mul_add]
            exact add_le_add (mul_le_mul_of_nonneg_right (hB t) (norm_nonneg _)) le_rfl
      _ = B * ((∫ x, ‖f x‖ ∂dx) / modulus F v u.val) + (∫ x, ‖h x‖ ∂dx)*‖f u.val‖ := by
        rw [integral_add (gi.norm.const_mul B) (hhi.norm.mul_const _),integral_const_mul,integral_mul_const,hscale]
      _ ≤ T * ‖u.val‖⁻¹ := by
        dsimp only [T]
        rw [add_mul,mul_assoc,mul_assoc,div_eq_mul_inv]
        have hB₀ := (norm_nonneg (h 0)).trans (hB 0)
        gcongr
      _ ≤ _ := by gcongr; exact le_max_right _ _

theorem integral_hat_arch {f : K → ℂ} (hf : Bruhat v f) :
    (∫ t, d.hat v f t ∂dx) = f 0 := by
  have he := congrFun (d.arch_hat_hat w f hf) 0
  simpa only [hat,zero_mul,Character.localValue_zero,mul_one,neg_zero] using he

/-- Evaluate the subtracted Fourier integral of a single affine factor at an
infinite place. The identity uses only the character and its Haar measures. -/
theorem arch_linearFactor_integral {f ρ : K → ℂ} (hf : Bruhat v f) (hρ : Bruhat v ρ)
    (hk : HasCompactSupport ρ) (h₀ : 0 ∉ tsupport ρ) (a : K) :
    let D (u : Kˣ) (t : K) := d.hat v ρ t * (f ((t-a)*u.val) - f u.val)
    Integrable (Function.uncurry D) ((d.lineMeasure v).prod dx) ∧
      (∫ t, ∫ u, D u t ∂(d.lineMeasure v) ∂dx) = f 0 *
        d.lineIntegral v (fun μ => ρ μ.val * d.character.localValue F v (μ.val*a)) := by
  let ν := d.lineMeasure v
  letI : (dx).IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  have cont {g : K → ℂ} (hg : Bruhat v g) : Continuous g :=
    (d.arch_bruhat_estimates w hg).1.choose_spec.continuous
  have fc := cont hf
  have rc := cont hρ
  have hweight : Integrable (fun x => ‖ρ x‖ / modulus F v x) dx := by
    apply Continuous.integrable_of_hasCompactSupport
    · apply continuous_iff_continuousAt.mpr
      intro x
      by_cases hx : x = 0
      · subst x
        apply (continuousAt_const (y := (0 : ℝ))).congr_of_eventuallyEq
        filter_upwards [(isClosed_tsupport ρ).isOpen_compl.mem_nhds h₀] with y hy
        simp [image_eq_zero_of_notMem_tsupport (show y ∉ tsupport ρ from hy)]
      · exact rc.norm.continuousAt.div (continuous_norm.pow w.mult).continuousAt
          (pow_ne_zero _ (norm_ne_zero_iff.mpr hx))
    · simp only [div_eq_mul_inv]
      exact hk.norm.mul_right
  have hgf := d.arch_hat_bruhat w hf
  have hdual := (d.linearFactor_dual v rc (cont hgf) (hgf.integrable d)
    (d.integral_hat_arch w hf) hweight a).2
  let h := d.hat v ρ
  have hh := d.arch_hat_bruhat w hρ
  let D (u : Kˣ) (t : K) := h t * (f ((t-a)*u.val) - f u.val)
  have hD : Integrable (Function.uncurry D) (ν.prod dx) := d.arch_difference_pair_integrable w hf hh a
  refine ⟨hD,?_⟩
  refine (integral_integral_swap hD).symm.trans ((integral_congr_ae ?_).trans hdual)
  filter_upwards with u
  let g (t : K) := f ((t-a)*u.val)
  have gc : Continuous g := fc.comp ((continuous_id.sub continuous_const).mul continuous_const)
  obtain ⟨M,hM⟩ := (d.arch_bruhat_estimates w hf).2.1 0
  simp only [pow_zero,one_mul] at hM
  have hi : Integrable (fun t => h t * g t) dx := (hh.integrable d).mul_bdd
    gc.aestronglyMeasurable (Filter.Eventually.of_forall fun t => hM _)
  have hz : (∫ t, h t ∂dx) = 0 := (d.integral_hat_arch w hρ).trans (image_eq_zero_of_notMem_tsupport h₀)
  have hswap := d.hat_pair_swap v rc gc (hρ.integrable d) (d.affine_integrable w (hf.integrable d) a u)
  change (∫ t, h t * (g t - f u.val) ∂dx) = _
  simp_rw [mul_sub]
  rw [integral_sub hi ((hh.integrable d).mul_const _),integral_mul_const,hz,zero_mul,sub_zero]
  apply hswap.trans
  apply integral_congr_ae
  filter_upwards with μ
  rw [show d.hat v g μ = _ from d.hat_affine v f a μ u]
  exact (mul_assoc ..).symm

/-- The single-root identity of Appendix A for real and complex Schwartz functions.
The test frequency is compactly supported away from zero. -/
theorem arch_linearFactor [NeZero n] {f ρ : K → ℂ} (hf : Bruhat v f) (hρ : Bruhat v ρ)
    (hk : HasCompactSupport ρ) (h₀ : 0 ∉ tsupport ρ) (b : Kˣ) (a : K) :
    let H := fun t => d.hat v ρ t * d.differenceIntegral v f (b^n) (t-a)
    Integrable H dx ∧ (∫ t, H t ∂dx) = f 0 *
      d.lineIntegral v (fun μ => ρ μ.val * d.character.localValue F v (μ.val*a)) := by
  let ν := d.lineMeasure v
  letI : (dx).IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  letI : NullSingletonClass (dx) := d.selfDual_nullSingleton v
  let h := d.hat v ρ
  let D (u : Kˣ) (t : K) := h t * (f ((t-a)*u.val) - f u.val)
  obtain ⟨hD,hval⟩ := d.arch_linearFactor_integral w hf hρ hk h₀ a
  have he : (fun t => ∫ u, D u t ∂ν) =ᵐ[dx] (fun t => h t * d.differenceIntegral v f (b^n) (t-a)) := by
    filter_upwards [(dx).ae_ne a] with t ht
    have hne := sub_ne_zero.mpr ht
    simp only [differenceIntegral,dif_pos hne,← d.integral_lineMeasure,D,integral_const_mul]
    congr 1
    apply integral_congr_ae
    filter_upwards with u
    have hs : d.symbol v u (b^n) = 1 := by
      change (d.unitPairing v u (b^n)).val = 1
      rw [map_pow,d.unitPairing_pow,Units.val_one]
    simp [marginalDifference,hs]
  exact ⟨hD.integral_prod_right.congr he, (integral_congr_ae he.symm).trans hval⟩

/-- With a fixed nonzero dilation the subtraction is integrable against multiplicative
Haar measure, including the Hilbert-character twist. -/
theorem marginalDifference_arch_integrable [NeZero n] {f : K → ℂ}
    (hf : Bruhat v f) (a b : Kˣ) : d.LineIntegrable v (d.marginalDifference v f a b) := by
  let W := d.marginalDifference v f a b
  obtain ⟨⟨L,lip⟩,fBound,_⟩ := d.arch_bruhat_estimates w hf
  have fc := lip.continuous
  obtain ⟨C,hC⟩ := fBound 1
  simp only [pow_one] at hC
  let A := (L : ℝ)*‖b.val-1‖
  let B := C * (‖b.val‖⁻¹ + 1)
  have hsmall (u : Kˣ) : ‖W u‖ ≤ A*‖u.val‖ := by
    simp only [W,marginalDifference,norm_mul,d.norm_symbol,one_mul,Units.val_mul]
    have hd := lip.dist_le_mul (b.val*u.val) u.val
    simpa only [dist_eq_norm,show b.val*u.val-u.val = (b.val-1)*u.val by ring,
      norm_mul,A,mul_assoc] using hd
  have hbig (u : Kˣ) : ‖W u‖ ≤ B*‖u.val‖⁻¹ := by
    have hb (z : Kˣ) : ‖f z.val‖ ≤ C*‖z.val‖⁻¹ := by
      rw [← div_eq_mul_inv,le_div_iff₀ (norm_pos_iff.mpr z.ne_zero),mul_comm]
      exact hC _
    simp only [W,marginalDifference,norm_mul,d.norm_symbol,one_mul]
    refine (norm_sub_le ..).trans ((add_le_add (hb (b*u)) (hb u)).trans_eq ?_)
    simp only [Units.val_mul,norm_mul,mul_inv,B]
    ring
  have hc : Continuous W := ((d.continuous_symbol v).comp (continuous_id.prodMk continuous_const)).mul
    ((fc.comp (continuous_const.mul Units.continuous_val)).sub (fc.comp Units.continuous_val))
  have hi : Integrable W (d.lineMeasure v) := by
    apply ((d.arch_min_weight w).const_mul (max A B)).mono' hc.aestronglyMeasurable
    filter_upwards with u
    by_cases hu : ‖u.val‖ ≤ ‖u.val‖⁻¹
    · rw [min_eq_left hu]
      exact (hsmall u).trans (mul_le_mul_of_nonneg_right (le_max_left ..) (norm_nonneg _))
    · rw [min_eq_right (le_of_not_ge hu)]
      exact (hbig u).trans (mul_le_mul_of_nonneg_right (le_max_right ..) (inv_nonneg.mpr (norm_nonneg _)))
  let G (x : K) := if hx : x ≠ 0 then W (Units.mk0 x hx) / (modulus F v x : ℂ) else 0
  change Integrable G dx
  apply (d.lineMeasure_modulus v G).1.mp
  apply hi.congr
  filter_upwards with u
  simp only [G,dif_pos u.ne_zero,Units.mk0_val,Complex.real_smul]
  field_simp [Complex.ofReal_ne_zero.mpr (modulus_ne_zero v u)]

/-- Evaluation of the Archimedean tested integral as a sum over all distinct
roots of an n-th power. -/
theorem arch_root_contribution [NeZero n] {f ρ : K → ℂ} (hf : Bruhat v f) (hρ : Bruhat v ρ)
    (hk : HasCompactSupport ρ) (h₀ : 0 ∉ tsupport ρ) (b : Kˣ) :
    (∫ t, d.hat v ρ t * d.differenceIntegral v f (b^n) (t^n-(b^n).val) ∂dx) =
      f 0 * ∑ a ∈ Polynomial.nthRootsFinset n (b^n).val,
        d.lineIntegral v (fun μ => ρ μ.val * d.character.localValue F v (μ.val*a)) := by
  rw [d.integral_difference_roots _ f _ _ ⟨b,rfl⟩
    (fun c => d.marginalDifference_arch_integrable w hf _ c)
    (fun a _ => (d.arch_linearFactor w hf hρ hk h₀ b a).1),Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => (d.arch_linearFactor w hf hρ hk h₀ b a).2

/-- The tested root sum at an infinite place, including the empty sum
when the coefficient is outside the subgroup of powers. -/
theorem arch_root_sum_of_right_kernel [NeZero n] {f ρ : K → ℂ} (hf : Bruhat v f)
    (hρ : Bruhat v ρ) (hk : HasCompactSupport ρ) (h₀ : 0 ∉ tsupport ρ) (a : Kˣ)
    (hpow : (∀ u, d.symbol v u a = 1) → ∃ b, b^n = a) :
    (∫ t, d.hat v ρ t * d.differenceIntegral v f a (t^n-a.val) ∂dx) =
      f 0 * ∑ r ∈ Polynomial.nthRootsFinset n a.val,
        d.lineIntegral v (fun μ => ρ μ.val * d.character.localValue F v (μ.val*r)) := by
  by_cases ha : ∃ b, b^n = a
  · obtain ⟨b,rfl⟩ := ha
    exact d.arch_root_contribution w hf hρ hk h₀ b
  obtain ⟨he,hz⟩ := d.differenceIntegral_nonpower v f a ha
    (d.marginalDifference_arch_integrable w hf a)
    (by simpa only [not_forall] using mt hpow ha)
  simp only [hz,mul_zero,integral_zero,he,Finset.sum_empty]

/-- At a complex place every nonzero coefficient has a root, so the tested
root sum holds for arbitrary coefficients. -/
theorem complex_root_sum [NeZero n] (hw : w.IsComplex) {f ρ : K → ℂ}
    (hf : Bruhat v f) (hρ : Bruhat v ρ) (hk : HasCompactSupport ρ)
    (h₀ : 0 ∉ tsupport ρ) (a : Kˣ) :
    (∫ t, d.hat v ρ t * d.differenceIntegral v f a (t^n-a.val) ∂dx) =
      f 0 * ∑ r ∈ Polynomial.nthRootsFinset n a.val,
        d.lineIntegral v (fun μ => ρ μ.val * d.character.localValue F v (μ.val*r)) := by
  obtain ⟨b,hb⟩ := complex_unit_power (n := n) w hw a
  exact hb ▸ d.arch_root_contribution w hf hρ hk h₀ b

/-- The root-sum identity for arbitrary nonzero coefficients at every infinite place. -/
theorem arch_root_sum [NeZero n] {f ρ : K → ℂ} (hf : Bruhat v f) (hρ : Bruhat v ρ)
    (hk : HasCompactSupport ρ) (h₀ : 0 ∉ tsupport ρ) (a : Kˣ) :
    (∫ t, d.hat v ρ t * d.differenceIntegral v f a (t^n-a.val) ∂dx) =
      f 0 * ∑ r ∈ Polynomial.nthRootsFinset n a.val,
        d.lineIntegral v (fun μ => ρ μ.val * d.character.localValue F v (μ.val*r)) := by
  by_cases hw : w.IsReal
  · exact d.arch_root_sum_of_right_kernel w hf hρ hk h₀ a (d.real_symbol_power w hw a)
  · exact d.complex_root_sum w (InfinitePlace.not_isReal_iff_isComplex.mp hw) hf hρ hk h₀ a

end MetaplecticPoisson.Datum
