import MetaplecticSummation.PowerHaar
import MetaplecticSummation.RadonDecay
import Mathlib.MeasureTheory.Group.Prod

/-! Absolute convergence and the exchange of integrals in the proof of Lemma 8.3. -/
noncomputable section
namespace MetaplecticPoisson
open MeasureTheory NumberField Filter Set Function
open Classical

private theorem finiteTest_rapidLineCharts {K : Type} [NormedField K] {f : Charts K}
    {h : Kˣ → Kˣ → ℂ} (hu : ∀ x y, ‖h x y‖ = 1) (gl : Glues h f) (ht : finiteTest f) :
    RapidLineChart f.1 ∧ RapidLineChart (fun a b => f.2 b a) := by
  have bound (j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ z : K × K, chartNorm f z * (1+‖z‖)^j ≤ C := by
    obtain ⟨T,hT,_,hs⟩ := ht.2.2
    have hc : Continuous (fun z : K × K => chartNorm f z * (1+‖z‖)^j) :=
      (finiteTest_continuous_chartNorm hu gl ht).mul ((continuous_const.add continuous_norm).pow _)
    obtain ⟨C,hC⟩ := hT.bddAbove_image hc.continuousOn
    refine ⟨max 0 C,le_max_left ..,fun z => ?_⟩
    by_cases hz : z ∈ T
    · exact (hC (mem_image_of_mem _ hz)).trans (le_max_right ..)
    · simp [chartNorm,(hs z hz).1,(hs z hz).2]
  constructor
  · refine ⟨ht.1.continuous,fun j => ?_⟩
    obtain ⟨C,hC,h⟩ := bound j
    exact ⟨C,hC,fun a b => by simpa [chartNorm,xChart,a.ne_zero,Prod.norm_def] using h (a.val,b)⟩
  · refine ⟨ht.2.1.continuous.comp (continuous_snd.prodMk continuous_fst),fun j => ?_⟩
    obtain ⟨C,hC,h⟩ := bound j
    exact ⟨C,hC,fun a b => by simpa only [chartNorm_eq_y hu gl,Prod.norm_def,max_comm ‖b‖] using h (b,a.val)⟩

namespace Datum
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n) (v : Place F)
local notation "K" => LocalField F v
local notation "μ" => d.lineMeasure v
local notation "dx" => selfDual F d.character v

theorem test_rapidLineCharts {f : Charts K} (ht : f ∈ d.testSet v) :
    RapidLineChart f.1 ∧ RapidLineChart (fun a b => f.2 b a) := by
  cases v with
  | inl w => exact d.arch_test_lineCharts w ht
  | inr p => exact finiteTest_rapidLineCharts (d.norm_symbol _) ht.1 ht.2

private theorem modulus_units_continuous : Continuous (fun u : Kˣ => modulus F v u.val) := by
  cases v with
  | inr p => exact Units.continuous_val.norm
  | inl w => exact Units.continuous_val.norm.pow _

/-- Absolute convergence of the two-variable integral before the n-th-power shear. -/
private theorem integrable_leading_kernel {f : Kˣ → K → ℂ} (hf : RapidLineChart f)
    (c : Kˣ) (b s : K) (hs : ‖s‖ = 1) (phase : Kˣ → ℂ) (hc : Continuous phase) (hu : ∀ x, ‖phase x‖ = 1) :
    Integrable (fun z : Kˣ × Kˣ => (modulus F v z.1.val : ℂ) * (modulus F v z.2.val : ℂ) *
      (f z.2 ((z.2.val*b+s*z.1.val^n)/c.val) * phase z.2)) ((μ).prod μ) := by
  letI : SecondCountableTopology Kˣ := Units.isEmbedding_val₀.secondCountableTopology
  let m (x : Kˣ) := modulus F v x.val
  have mpos (x : Kˣ) : 0 ≤ m x := by cases v <;> simp [m,modulus,pow_nonneg]
  let g (x : Kˣ) := m x * ((1+‖x.val‖)^3)⁻¹
  have hg : Integrable g μ := (d.lineMeasure_modulus v fun x => ((1+‖x‖)^3)⁻¹).1.mpr (d.integrable_local_inv_cube v)
  obtain ⟨B,H⟩ := hf.bound_on_lines (NeZero.pos n) c b s hs
  have bound (t x : Kˣ) : ‖f x ((x.val*b+s*t.val^n)/c.val)*phase x‖ ≤ B*((1+‖t.val‖)^3)⁻¹*((1+‖x.val‖)^3)⁻¹ := by
    simpa only [norm_mul,hu,mul_one] using H t x
  have M := modulus_units_continuous v
  have coord : Continuous (fun z : Kˣ × Kˣ => (z.2.val*b+s*z.1.val^n)/c.val) := by fun_prop
  have cont := (((Complex.continuous_ofReal.comp M).comp continuous_fst).mul
    ((Complex.continuous_ofReal.comp M).comp continuous_snd)).mul
    ((hf.1.comp (continuous_snd.prodMk coord)).mul (hc.comp continuous_snd))
  apply ((hg.mul_prod hg).const_mul B).mono' cont.aestronglyMeasurable
  filter_upwards with z
  change ‖(m z.1 : ℂ)*(m z.2 : ℂ)*(f z.2 ((z.2.val*b+s*z.1.val^n)/c.val)*phase z.2)‖ ≤ B*(g z.1*g z.2)
  rw [norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_of_nonneg (mpos _),Real.norm_of_nonneg (mpos _)]
  calc
    _ ≤ _ := mul_le_mul_of_nonneg_left (bound z.1 z.2) (mul_nonneg (mpos _) (mpos _))
    _ = _ := by dsimp [g,m]; ring

omit [NeZero n] in
private theorem integral_field_on_units (g : Kˣ → ℂ) :
    (∫ x : K, if hx : x ≠ 0 then g (Units.mk0 x hx) else 0 ∂dx) =
      ∫ x : Kˣ, (modulus F v x.val : ℂ) * g x ∂μ := by
  simpa only [dif_pos (Units.ne_zero _),Units.mk0_val,Complex.real_smul] using
    (d.lineMeasure_modulus v (fun x => if hx : x ≠ 0 then g (Units.mk0 x hx) else 0)).2.symm

/-- Unnormalized integral of one chart on a line of determinant ±tⁿ. -/
def leadingLine (f : Kˣ → K → ℂ) (phase : Kˣ → ℂ) (c : Kˣ) (b s t : K) : ℂ :=
  ∫ x, if hx : x ≠ 0 then f (Units.mk0 x hx) ((x*b+s*t^n)/c.val) * phase (Units.mk0 x hx)
    else 0 ∂dx

/-- Interchanging the power average and a single line integral, with both
the covering multiplicity and the Jacobian of the power map. -/
theorem leadingLine_average {f : Kˣ → K → ℂ} (hf : RapidLineChart f)
    (c : Kˣ) (b s : K) (hs : ‖s‖ = 1) (phase : Kˣ → ℂ) (hc : Continuous phase)
    (hu : ∀ x, ‖phase x‖ = 1) (hinv : ∀ t x : Kˣ, phase (t^n*x) = phase x) :
    let avg (x : Kˣ) (y : K) := d.lineIntegral v fun a =>
      if ∃ u : Kˣ, a = u^n then
        ((modulus F v a.val ^ (1+1/(n:ℝ)) : ℝ) : ℂ) * f (a*x) (a.val*y) else 0
    d.leadingLine v avg phase c b s 1 = ((modulus F v (n : K) : ℂ)/(n:ℂ)) *
      ∫ t, d.leadingLine v f phase c b s t ∂dx := by
  letI : SecondCountableTopology Kˣ := Units.isEmbedding_val₀.secondCountableTopology
  let m (x : Kˣ) := modulus F v x.val
  let e : ℝ := 1+1/(n:ℝ)
  let k : ℂ := (modulus F v (n : K) : ℂ)/(n:ℂ)
  let L (t x : Kˣ) := (m t : ℂ) * (m x : ℂ) * (f x ((x.val*b+s*t.val^n)/c.val) * phase x)
  let G (t x : Kˣ) := L t (t^n*x)
  have hm : MeasurePreserving (fun z : Kˣ×Kˣ => (z.1,z.1^n*z.2)) ((μ).prod μ) ((μ).prod μ) :=
    (MeasurePreserving.id μ).skew_product ((measurable_fst.pow_const n).mul measurable_snd)
      (Eventually.of_forall fun t => map_mul_left_eq_self μ (t^n))
  have hL : Integrable (uncurry L) ((μ).prod μ) := d.integrable_leading_kernel v hf c b s hs phase hc hu
  have hG : Integrable (uncurry G) ((μ).prod μ) := (hm.integrable_comp hL.aestronglyMeasurable).mpr hL
  have hp (x : Kˣ) : 0 < m x := by cases v <;> simp [m,modulus,norm_pos_iff,x.ne_zero,pow_pos (norm_pos_iff.mpr x.ne_zero)]
  have hpow (t x : Kˣ) : m (t^n*x) = (m t)^n*m x := by
    cases v <;> simp [m,modulus,norm_mul,norm_pow,mul_pow,← pow_mul,Nat.mul_comm n]
  have hw (t : Kˣ) : (m (t^n))^e = (m t)^n * m t := by
    have h : m (t^n) = (m t)^n := by cases v <;> simp [m,modulus,norm_pow,← pow_mul,Nat.mul_comm n]
    rw [h,Real.rpow_add (pow_pos (hp t) n),Real.rpow_one,← Real.rpow_natCast_mul (hp t).le]
    simp [NeZero.ne n]
  let avg (x : Kˣ) (y : K) := d.lineIntegral v fun a =>
    if ∃ u : Kˣ, a=u^n then ((m a ^ e : ℝ) : ℂ) * f (a*x) (a.val*y) else 0
  let y (x : Kˣ) := (x.val*b+s)/c.val
  have havg (x : Kˣ) : (m x : ℂ) * (avg x (y x) * phase x) = k * ∫ t, G t x ∂μ := by
    let g (a : Kˣ) := ((m a^e : ℝ) : ℂ) * f (a*x) (a.val*y x)
    have cm := modulus_units_continuous v
    have he : 0 ≤ e := by dsimp [e]; positivity
    have cg : Continuous g := (Complex.continuous_ofReal.comp ((Real.continuous_rpow_const he).comp cm)).mul
      (hf.1.comp ((continuous_id.mul continuous_const).prodMk (Units.continuous_val.mul continuous_const)))
    have hav : avg x (y x) = k * ∫ t, g (t^n) ∂μ := d.lineIntegral_on_powers v g cg.measurable
    rw [hav]
    calc
      _ = k * ((m x : ℂ) * ((∫ t, g (t^n) ∂μ) * phase x)) := by ring
      _ = _ := by
        congr 1
        rw [← integral_mul_const,← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with t
        have coord : (((t^n)*x).val*b+s*t.val^n)/c.val = (t^n).val * y x := by
          simp only [y,Units.val_mul,Units.val_pow_eq_pow_val]; ring
        dsimp only [G,L,g]
        rw [coord,hinv,hw,hpow,Complex.ofReal_mul,Complex.ofReal_mul]
        ring
  change d.leadingLine v avg phase c b s 1 = k * _
  have lhs : d.leadingLine v avg phase c b s 1 = ∫ x, (m x : ℂ)*(avg x (y x)*phase x) ∂μ := by
    simpa only [leadingLine,y,m,Units.val_mk0,one_pow,mul_one] using
      d.integral_field_on_units v (fun x => avg x (y x)*phase x)
  have rhs : (∫ t, d.leadingLine v f phase c b s t ∂dx) = ∫ t, ∫ x, L t x ∂μ ∂μ := by
    rw [← (d.lineMeasure_modulus v (d.leadingLine v f phase c b s)).2]
    apply integral_congr_ae
    filter_upwards with t
    have H := d.integral_field_on_units v (fun x => f x ((x.val*b+s*t.val^n)/c.val)*phase x)
    change (m t : ℂ) * d.leadingLine v f phase c b s t.val = _
    rw [show d.leadingLine v f phase c b s t.val = _ from H,← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    dsimp only [L]
    ring
  rw [lhs,rhs]
  simp_rw [havg]
  rw [integral_const_mul,← integral_integral_swap hG]
  congr 1
  exact integral_congr_ae (Eventually.of_forall fun t => integral_mul_left_eq_self (L t) (t^n))

end Datum
end MetaplecticPoisson
