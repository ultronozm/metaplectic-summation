import MetaplecticSummation.Jacquet.Convergence
import MetaplecticSummation.RadonDecay

/-! The two regions of absolute convergence in the shear estimate that
follow directly from (4.2), before using cancellation of differences. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField MeasureTheory Set
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n) (v : Place F)
local notation "K" => LocalField F v
local notation "dx" => selfDual F d.character v
local notation "m" => modulus F v

/-- Absolute integrability of the X-chart for d×x dy outside the region
where |x| is small and the second coordinate dominates. -/
theorem integrableOn_X_outside_vertical_cone (Φ : d.schwartz v) :
    IntegrableOn (Function.uncurry Φ.val.1)
      {z : Kˣ × K | 1 ≤ m z.1.val ∨ ‖z.2‖ ≤ ‖z.1.val‖} ((d.lineMeasure v).prod dx) := by
  letI : (dx).IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  let P := {z : Kˣ × K | 1 ≤ m z.1.val ∨ ‖z.2‖ ≤ ‖z.1.val‖}
  have cm : Continuous fun a : Kˣ => m a.val := by
    cases v <;> first | exact Units.continuous_val.norm.pow _ | exact Units.continuous_val.norm
  have hP : MeasurableSet P := (isClosed_le continuous_const (cm.comp continuous_fst)).measurableSet.union
    (isClosed_le continuous_snd.norm (Units.continuous_val.comp continuous_fst).norm).measurableSet
  let G := P.indicator (Function.uncurry Φ.val.1)
  have hg : StronglyMeasurable G := (d.continuous_schwartz_charts v Φ).1.stronglyMeasurable.indicator hP
  apply (integrable_indicator_iff hP).mp
  apply (integrable_prod_iff hg.aestronglyMeasurable).mpr
  refine ⟨.of_forall (fun a => (d.integrable_jacquet_slice v Φ a).norm.mono'
    (hg.comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    (.of_forall fun y => ?_)),?_⟩
  · change ‖G (a,y)‖ ≤ _
    by_cases h : (a,y) ∈ P <;> simp [G,h,Function.uncurry]
  obtain ⟨C,hC,H⟩ := d.schwartz_chart_growth v Φ 3 (by decide)
  let e := 1/(n:ℝ)
  have he : 0 < e := one_div_pos.mpr (by exact_mod_cast NeZero.pos n)
  have he' : e ≤ 1 := (one_div_le_one_div_of_le zero_lt_one (by exact_mod_cast NeZero.one_le (n := n))).trans_eq (by norm_num)
  have hk : 1 - growthExponent n = e := by
    dsimp only [growthExponent,e]; rw [Nat.cast_sub (NeZero.one_le : 1 ≤ n),Nat.cast_one]
    field_simp [show (n:ℝ) ≠ 0 by exact_mod_cast NeZero.ne n]; ring
  let J := ∫ t : K, ((1+‖t‖)^3)⁻¹ ∂dx
  let W (a : Kˣ) := min ((m a.val)^e) ((m a.val)^(-e))
  apply ((d.integrable_modulus_min_rpow v he).const_mul (8*C*J)).mono'
    hg.aestronglyMeasurable.norm.integral_prod_right'
  filter_upwards with a
  let r := m a.val
  have hr : 0 < r := by cases v <;> simp [r,modulus,norm_pos_iff,a.ne_zero,pow_pos]
  have hW : 0 ≤ W a := le_min (Real.rpow_nonneg hr.le _) (Real.rpow_nonneg hr.le _)
  have bound (t : K) : r*‖G (a,a.val*t)‖ ≤ (8*C*W a)*((1+‖t‖)^3)⁻¹ := by
    rw [← div_eq_mul_inv,le_div_iff₀ (by positivity)]
    by_cases hp : (a,a.val*t) ∈ P
    · rw [show G (a,a.val*t) = Φ.val.1 a (a.val*t) from indicator_of_mem hp _]
      let S := max 1 (m t)
      have hs : 1 ≤ S := le_max_left ..
      have rad : max (m a.val) (m (a.val*t)) = r*S := by
        rw [show m (a.val*t) = r*m t by cases v <;> simp [r,modulus,mul_pow],mul_max_of_nonneg _ _ hr.le,mul_one]
      have hf : ‖Φ.val.1 a (a.val*t)‖ ≤ C*min ((r*S)^(-growthExponent n)) ((r*S)^(-((3:ℕ):ℝ))) := by
        have hn : (a.val,a.val*t) ≠ (0 : K × K) := fun h => a.ne_zero (congrArg Prod.fst h)
        simpa only [xChart,dif_pos a.ne_zero,Units.mk0_val,rad] using (H _ hn).1
      by_cases h : 1 ≤ r
      · have hrS := mul_pos hr (zero_lt_one.trans_le hs)
        have hb := hf.trans (mul_le_mul_of_nonneg_left (min_le_right ..) hC)
        rw [Real.rpow_neg hrS.le,Real.rpow_natCast,← div_eq_mul_inv,le_div_iff₀ (pow_pos hrS _)] at hb
        have ht : ‖t‖ ≤ S := by
          rcases le_total ‖t‖ 1 with ht|ht
          · exact ht.trans hs
          · apply le_trans _ (le_max_right ..)
            cases v with
            | inl w => exact le_self_pow₀ ht w.mult_ne_zero
            | inr p => exact le_rfl
        have hd : ‖Φ.val.1 a (a.val*t)‖*(1+‖t‖)^3 ≤ 8*C/r^3 := by
          rw [le_div_iff₀ (pow_pos hr 3)]
          have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ 1+‖t‖) (by linarith : 1+‖t‖ ≤ 2*S) 3
          calc
            _ ≤ ‖Φ.val.1 a (a.val*t)‖*(2*S)^3*r^3 :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (norm_nonneg _)) (pow_nonneg hr.le _)
            _ = 8*(‖Φ.val.1 a (a.val*t)‖*(r*S)^3) := by ring
            _ ≤ _ := by linarith
        have hmin : W a = r^(-e) := min_eq_right (Real.rpow_le_rpow_of_exponent_le h (by linarith))
        rw [mul_assoc,hmin]
        calc
          _ ≤ r*(8*C/r^3) := mul_le_mul_of_nonneg_left hd hr.le
          _ = 8*C*r^(-(2:ℝ)) := by rw [Real.rpow_neg hr.le,show (2:ℝ) = (2:ℕ) from rfl,Real.rpow_natCast]; field_simp
          _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le h (by linarith)) (by positivity)
      · have hcone : ‖a.val*t‖ ≤ ‖a.val‖ := hp.resolve_left h
        rw [norm_mul] at hcone
        have ht : ‖t‖ ≤ 1 := (mul_le_mul_iff_right₀ (norm_pos_iff.mpr a.ne_zero)).mp (by simpa only [mul_one] using hcone)
        have hb := hf.trans (mul_le_mul_of_nonneg_left (min_le_left ..) hC)
        have hb' := hb.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hr
          (le_mul_of_one_le_right hr.le hs) (neg_nonpos.mpr (growthExponent_nonneg n))) hC)
        have hmin : W a = r^e := min_eq_left (Real.rpow_le_rpow_of_exponent_ge hr (le_of_not_ge h) (by linarith))
        rw [hmin]
        calc
          _ ≤ (r*(C*r^(-growthExponent n)))*2^3 := mul_le_mul (mul_le_mul_of_nonneg_left hb' hr.le)
            (pow_le_pow_left₀ (by positivity) (by linarith) 3) (by positivity) (by positivity)
          _ = 8*C*r^e := by rw [← hk,sub_eq_add_neg,Real.rpow_add hr,Real.rpow_one]; ring
    · rw [show G (a,a.val*t) = 0 from indicator_of_notMem hp _,norm_zero,mul_zero,zero_mul]
      positivity
  have H' := integral_mono_of_nonneg (μ := dx) (.of_forall (fun t => mul_nonneg hr.le (norm_nonneg _)))
    ((d.integrable_local_inv_cube v).const_mul (8*C*W a)) (.of_forall bound)
  simp only [integral_const_mul] at H'
  have eqn := d.integral_local_mul v a (fun y => (‖G (a,y)‖ : ℂ))
  rw [eq_div_iff (Complex.ofReal_ne_zero.mpr hr.ne')] at eqn
  simp only [integral_complex_ofReal,← Complex.ofReal_mul,Complex.ofReal_inj] at eqn
  change ‖∫ y, ‖G (a,y)‖ ∂dx‖ ≤ 8*C*J*W a
  rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _),← eqn,mul_comm]
  exact H'.trans_eq (by dsimp only [J]; ring)

end MetaplecticPoisson.Datum
