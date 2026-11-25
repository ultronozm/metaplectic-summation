import MetaplecticSummation.FourierCoefficients.Unfolding
import MetaplecticSummation.AdelicFourierIntegrals

/-! Local factors of the adelic Fourier coefficients in Lemma B.2. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField IsDedekindDomain MeasureTheory Filter
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

private def slopeFactor (Φ : ∀ v, d.schwartz v) (x : Fˣ) (v : Place F) (u : LocalField F v) :=
  (Φ v).val.1 (atPlace v x) ((atPlace v x).val*u)

private theorem slopeFactor_finite (Φ : ∀ v, d.schwartz v) (x : Fˣ) (p : Prime F) :
    Bruhat (.inr p) (d.slopeFactor Φ x (.inr p)) := by
  let v : Place F := .inr p
  let c := atPlace v x
  let e := Homeomorph.mulLeft₀ c.val c.ne_zero
  have lc := (d.locallyConstant_finite_schwartz p (Φ v)).1
  have lc' : IsLocallyConstant ((Φ v).val.1 c) := lc.comp_continuous (continuous_const.prodMk continuous_id)
  have hc : HasCompactSupport ((Φ v).val.1 c) := by
    obtain ⟨L,hL⟩ := d.exists_leading_finite p
    obtain ⟨C,hC,hout⟩ := (d.finite_support_and_germ_of_isLeadingTerm p (Φ v) (hL (Φ v))).1
    apply HasCompactSupport.intro (hC.image continuous_snd)
    intro y hy
    have h := (hout (c.val,y) (fun hin => hy ⟨_,hin,rfl⟩)).1
    simpa only [xChart,dite_eq_left c.ne_zero,Units.mk0_val] using h
  exact ⟨lc'.comp_continuous e.continuous,hc.comp_homeomorph e⟩

private theorem slopeFactor_basic (Φ : ∀ v, d.schwartz v) (hΦ : ∀ᶠ v in cofinite, Φ v = d.basic v) (x : Fˣ) :
    ∀ᶠ p : Prime F in cofinite, ∀ t, d.slopeFactor Φ x (.inr p) t = if ‖t‖ ≤ 1 then 1 else 0 := by
  filter_upwards [(Sum.inr_injective (α := InfinitePlace F)).tendsto_cofinite.eventually hΦ,
    eventually_tame (F := F) (n := n),eventually_diagonal_norm_one x.ne_zero] with p h ht hx
  let v : Place F := .inr p
  let c := atPlace v x
  change Φ v = _ at h
  have hc : ‖c.val‖ = 1 := hx
  intro t
  change (Φ v).val.1 c (c.val*t) = _
  rw [h]
  have mul : ‖c.val*t‖ = ‖t‖ := by rw [norm_mul,hc,one_mul]
  split
  next hi =>
    have he := d.basic_xChart_unit p ht c.val (c.val*t) hc (mul.trans_le hi)
    simpa only [xChart,dite_eq_left c.ne_zero,Units.mk0_val] using he
  next ho => exact d.basic_x_outside p ht c _ ((lt_of_not_ge ho).trans_le (mul.symm.trans_le (le_max_right ..)))

/-- The Fourier integral of an adelic slope factors into the local vertical integrals. -/
theorem slope_integral_factorization (Φ : ∀ v, d.schwartz v) (hΦ : ∀ᶠ v in cofinite, Φ v = d.basic v)
    (x : Fˣ) (a : F) :
    (∫ u : Adeles F, d.adelicSlopeSlice Φ x u * (d.character.toChar (-(algebraMap F (Adeles F) a * u)) : ℂ)
      ∂GroundTheory.Global.adeleMeasure F) =
    ∏ᶠ v, ∫ y, (Φ v).val.1 (atPlace v x) y *
      d.character.localValue F v (diagonal F v (-a)*y/(atPlace v x).val) ∂selfDual F d.character v := by
  let f := d.slopeFactor Φ x
  let t := algebraMap F (Adeles F) (-a)
  let H (v : Place F) := d.hat v (f v) (diagonal F v (-a))
  let m (v : Place F) : ℂ := (modulus F v (atPlace v x).val : ℝ)
  have hb := d.slopeFactor_basic Φ hΦ x
  have hhat := d.hat_tensor_basic f hb
  have he : d.adelicSlopeSlice Φ x = adelicTensor f := funext fun u => (adelicTensor_eq_finprod f hb u).symm
  have phase (u : Adeles F) : -(algebraMap F (Adeles F) a * u) = u*t := by simp [t,mul_comm]
  simp_rw [he,phase]
  change d.character.adelicHat (adelicTensor f) t = _
  rw [d.adelicHat_tensor_of_finite_bruhat f (d.slopeFactor_finite Φ x) hb t,adelicTensor_eq_finprod _ hhat]
  have freq (v : Place F) : component t v = diagonal F v (-a) := by cases v <;> rfl
  simp_rw [freq]
  have hm := modulus_eventually_one x.ne_zero
  have hm' : ∀ᶠ v in cofinite, m v = 1 := hm.mono fun v hv => (congrArg Complex.ofReal hv).trans Complex.ofReal_one
  have prod : ∏ᶠ v, m v = 1 := by
    change (∏ᶠ v, Complex.ofRealHom.toMonoidHom (modulus F v (diagonal F v x.val))) = 1
    rw [← MonoidHom.map_finprod _ (eventually_cofinite.mp hm),diagonal_modulus_product x.ne_zero,map_one]
  have hH : ∀ᶠ v in cofinite, H v = 1 := by
    apply eventually_place_of_finite
    filter_upwards [hhat,t.2.2] with p hp ht
    exact (hp _).trans (ite_eq_left ((mem_localIntegers_iff p _).mp ht))
  calc
    ∏ᶠ v, H v = ∏ᶠ v, m v * H v := by rw [finprod_mul_distrib (eventually_cofinite.mp hm') (eventually_cofinite.mp hH),prod,one_mul]
    _ = _ := by
      apply finprod_congr
      intro v
      let c := atPlace v x
      let g (y : LocalField F v) := (Φ v).val.1 c y * d.character.localValue F v (diagonal F v (-a)*y/c.val)
      have J := d.integral_local_mul v c g
      have eqn (u : LocalField F v) : g (c.val*u) = f v u * d.character.localValue F v (diagonal F v (-a)*u) := by
        apply congrArg (f v u * ·)
        apply congrArg (d.character.localValue F v)
        field_simp [c.ne_zero]
      simp_rw [eqn] at J
      change H v = (∫ y, g y ∂selfDual F d.character v) / m v at J
      exact (mul_comm (m v) (H v)).trans ((eq_div_iff (Complex.ofReal_ne_zero.mpr (modulus_ne_zero v c))).mp J)

private def slopeFourierIntegral (Φ : ∀ v, d.schwartz v) (x : Fˣ) (a : F) :=
  ∫ u : Adeles F, d.adelicSlopeSlice Φ x u * (d.character.toChar (-(algebraMap F (Adeles F) a * u)) : ℂ)
    ∂GroundTheory.Global.adeleMeasure F

private theorem summable_slopeFourierIntegral (Φ : ∀ v, d.schwartz v)
    (h : ∀ᶠ v in cofinite, Φ v = d.basic v) (a : F) :
    Summable (fun x => ‖d.slopeFourierIntegral Φ x a‖) := by
  apply (ENNReal.tsum_coe_ne_top_iff_summable_coe (f := fun x => ‖d.slopeFourierIntegral Φ x a‖₊)).mp
  apply ne_top_of_le_ne_top (d.summable_slope_integrals Φ h)
  apply ENNReal.tsum_le_tsum
  intro x
  change ‖d.slopeFourierIntegral Φ x a‖ₑ ≤ _
  simpa only [slopeFourierIntegral,enorm_mul,Circle.enorm_coe,mul_one] using
    (enorm_integral_le_lintegral_enorm (μ := GroundTheory.Global.adeleMeasure F)
      (fun u : Adeles F => d.adelicSlopeSlice Φ x u * (d.character.toChar (-(algebraMap F (Adeles F) a * u)) : ℂ)))

private theorem slopeFourierIntegral_zero (Φ : ∀ v, d.schwartz v)
    (h : ∀ᶠ v in cofinite, Φ v = d.basic v) (x : Fˣ) :
    d.slopeFourierIntegral Φ x 0 = ∏ᶠ v, d.marginal v (Φ v) (atPlace v x) := by
  simpa only [neg_zero,map_zero,zero_mul,zero_div,Character.localValue_zero,mul_one,marginal,slopeFourierIntegral]
    using d.slope_integral_factorization Φ h x 0

/-- Absolute convergence of the rational marginal series in the constant term. -/
theorem summable_rational_marginal (Φ : ∀ v, d.schwartz v) (h : ∀ᶠ v in cofinite, Φ v = d.basic v) :
    Summable (fun x : Fˣ => ‖∏ᶠ v, d.marginal v (Φ v) (atPlace v x)‖) := by
  simpa only [d.slopeFourierIntegral_zero Φ h] using d.summable_slopeFourierIntegral Φ h 0

/-- The constant term and first Fourier coefficient of the theta sum, with absolute convergence. -/
theorem unfolding (Φ : ∀ v, d.schwartz v) (h : ∀ᶠ v in cofinite, Φ v = d.basic v) :
    d.coefficient Φ 0 = d.constantTerm Φ ∧
    Summable (fun c : Fˣ => ‖∏ᶠ v, d.jacquet v (Φ v) (atPlace v c)‖) ∧
    d.coefficient Φ 1 = ∑' c : Fˣ, ∏ᶠ v, d.jacquet v (Φ v) (atPlace v c) := by
  have one (x : Fˣ) : d.slopeFourierIntegral Φ x 1 = ∏ᶠ v, d.jacquet v (Φ v) (atPlace v x) := by
    simpa only [map_neg,map_one,neg_one_mul,jacquet,slopeFourierIntegral] using d.slope_integral_factorization Φ h x 1
  refine ⟨?_,by simpa only [one] using d.summable_slopeFourierIntegral Φ h 1,?_⟩
  · have eqn := (d.coefficient_eq_slope_integrals Φ h 0).2
    change d.coefficient Φ 0 = (if (0 : F) = 0 then _ else _) + ∑' x, d.slopeFourierIntegral Φ x 0 at eqn
    simpa only [ite_true,d.slopeFourierIntegral_zero Φ h,constantTerm] using eqn
  · have eqn := (d.coefficient_eq_slope_integrals Φ h 1).2
    change d.coefficient Φ 1 = (if (1 : F) = 0 then _ else _) + ∑' x, d.slopeFourierIntegral Φ x 1 at eqn
    simpa only [one_ne_zero,ite_false,zero_add,one] using eqn

end MetaplecticPoisson.Datum
