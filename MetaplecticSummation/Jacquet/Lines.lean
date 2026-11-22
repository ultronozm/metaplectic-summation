import MetaplecticSummation.Jacquet.Kernel
import MetaplecticSummation.Jacquet.Convergence
import MetaplecticSummation.TestedMarginal

/-! The absolutely convergent change of variables in the weak Jacquet formula. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField MeasureTheory Filter Set
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n) (v : Place F)
local notation "K" => LocalField F v
local notation "dx" => selfDual F d.character v
local notation "ν" => d.lineMeasure v
local notation "ψ" => d.character.localValue F v

omit [NeZero n] in
private theorem integrable_local_affine {f : K → ℂ} (hf : Integrable f dx) (k : Kˣ) (b : K) :
    Integrable (fun z => f (k.val*z+b)) dx := by
  letI : (dx).IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  let e := MeasurableEquiv.smul (α := K) k
  have hi := (measurePreserving_add_right dx b).integrable_comp_of_integrable hf
  apply (e.measurableEmbedding.integrable_map_iff (g := fun t => f (t+b))).mp
  change Integrable _ (Measure.map (fun t => k.val*t) dx)
  rw [d.map_local_mul]
  exact hi.smul_measure_nnreal

omit [NeZero n] in
private theorem integral_local_affine (f : K → ℂ) (k : Kˣ) (b : K) :
    (∫ z, f (k.val*z+b) ∂dx) = (∫ z, f z ∂dx) / (modulus F v k.val : ℂ) := by
  letI : (dx).IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  exact (d.integral_local_mul v k (fun y => f (y+b))).trans (by rw [integral_add_right_eq_self])

/-- Fixed-t line identity and its uniform L¹ estimate from the proof of
the weak Jacquet formula. The hypothesis is the paper's absolute integral
over the X-chart with measure d×x dy. -/
theorem jacquet_radon_lines (Φ : d.schwartz v) (hΦ : Integrable (Function.uncurry Φ.val.1) ((ν).prod dx))
    (c : Kˣ) (t : K) :
    let R := (radon n (d.symbol v) (modulus F v) dx Φ.val t).1 c
    Integrable R dx ∧ (∫ y, R y * ψ (-y/c.val) ∂dx) = d.kernelIntegral v (d.jacquet v Φ) c t ∧
      (∫ y, ‖R y‖ ∂dx) ≤ ∫ z, ‖Φ.val.1 z.1 z.2‖ ∂((ν).prod dx) := by
  letI : (dx).IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  letI : SigmaFinite dx := inferInstance
  let R := (radon n (d.symbol v) (modulus F v) dx Φ.val t).1 c
  let k (x : Kˣ) := x/c
  let b := -(t^n)/c.val
  let Y (x : Kˣ) (y : K) := (k x).val*y+b
  let m (x : Kˣ) := modulus F v (k x).val
  let G (x : Kˣ) (y : K) := (m x : ℂ) * (Φ.val.1 x (Y x y) * d.symbol v x (-c))
  have hm (x : Kˣ) : 0 < m x := by
    cases v <;> simp [m,modulus,norm_pos_iff,(k x).ne_zero,pow_pos (norm_pos_iff.mpr (k x).ne_zero)]
  have hdiv (x : Kˣ) : m x = modulus F v x.val / modulus F v c.val := by
    cases v <;> simp [m,k,modulus,div_pow]
  have hY (x : Kˣ) (y : K) : Y x y = (x.val*y-t^n)/c.val := by
    change (x/c).val*y + -(t^n)/c.val = _
    rw [Units.val_div_eq_div_val]; ring
  have hc : Continuous (Function.uncurry Φ.val.1) := by
    cases v with
    | inl w => exact d.continuous_arch_schwartz_X w Φ
    | inr p => exact (d.locallyConstant_finite_schwartz p Φ).1.continuous
  have hgc : Continuous (Function.uncurry G) := by
    have hk : Continuous (fun x : Kˣ => (k x).val) := Units.continuous_val.comp (continuous_id.div_const c)
    have hmc : Continuous m := by cases v <;> first | exact hk.norm.pow _ | exact hk.norm
    apply (Complex.continuous_ofReal.comp (hmc.comp continuous_fst)).mul
    exact (hc.comp (continuous_fst.prodMk (((hk.comp continuous_fst).mul continuous_snd).add continuous_const))).mul
      ((d.continuous_symbol v).comp (continuous_fst.prodMk continuous_const))
  have hn (x : Kˣ) (y : K) : ‖G x y‖ = m x * ‖Φ.val.1 x (Y x y)‖ := by
    simp only [G,norm_mul,d.norm_symbol,mul_one,Complex.norm_real,Real.norm_of_nonneg (hm x).le]
  have hsection (x : Kˣ) : (∫ y, ‖G x y‖ ∂dx) = ∫ y, ‖Φ.val.1 x y‖ ∂dx := by
    simp_rw [hn,integral_const_mul]
    have eqn := d.integral_local_affine v (fun y => (‖Φ.val.1 x y‖ : ℂ)) (k x) b
    rw [eq_div_iff (Complex.ofReal_ne_zero.mpr (hm x).ne')] at eqn
    rw [integral_complex_ofReal,integral_complex_ofReal,← Complex.ofReal_mul,Complex.ofReal_inj] at eqn
    exact (mul_comm ..).trans eqn
  have hi : Integrable (Function.uncurry G) ((ν).prod dx) := by
    apply (integrable_prod_iff hgc.aestronglyMeasurable).mpr
    constructor
    · apply Eventually.of_forall
      intro x
      exact ((d.integrable_local_affine v (d.integrable_jacquet_slice v Φ x) (k x) b).mul_const (d.symbol v x (-c))).const_mul (m x : ℂ)
    · simpa only [Function.uncurry,hsection] using hΦ.integral_norm_prod_left
  have hR (y : K) : R y = ∫ x, G x y ∂ν := by
    rw [d.integral_lineMeasure]
    unfold lineIntegral
    change (∫ x, _ ∂dx) / _ = _
    rw [← integral_div]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x = 0
    · simp [hx]
    · let u := Units.mk0 x hx
      simp only [dif_pos hx]
      change (Φ.val.1 u _ * d.symbol v u (-c)) / _ = G u y / _
      dsimp only [G]
      rw [hY,hdiv,Complex.ofReal_div]
      change (Φ.val.1 u ((x*y-t^n)/c.val) * d.symbol v u (-c)) / _ =
        (((modulus F v x : ℂ) / (modulus F v c.val : ℂ)) * (Φ.val.1 u ((x*y-t^n)/c.val) * d.symbol v u (-c))) / _
      have hx' : (modulus F v x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (modulus_ne_zero v u)
      field_simp [hx',Complex.ofReal_ne_zero.mpr (modulus_ne_zero v c)]
  have ri : Integrable R dx := by
    rw [funext hR]
    exact hi.integral_prod_right
  let D (x : Kˣ) (y : K) := G x y * ψ (-y/c.val)
  have hd : Integrable (Function.uncurry D) ((ν).prod dx) := by
    have hcont : Continuous (Function.uncurry D) := hgc.mul ((d.character.continuous_localValue v).comp
      (continuous_snd.neg.div_const c.val))
    exact hi.norm.mono' hcont.aestronglyMeasurable (.of_forall fun z => by simp [D,Function.uncurry])
  have inner (x : Kˣ) : (∫ y, D x y ∂dx) =
      d.jacquet v Φ x * d.symbol v x (-c) * ψ (-(t^n)/(c.val*x.val)) := by
    let s := d.symbol v x (-c) * ψ (-(t^n)/(c.val*x.val))
    let f (y : K) := Φ.val.1 x y * ψ (-y/x.val)
    have eval (y : K) : D x y = (m x : ℂ) * (f (Y x y) * s) := by
      have hh := d.character.localValue_add v (-(Y x y)/x.val) (-(t^n)/(c.val*x.val))
      rw [show -(Y x y)/x.val + -(t^n)/(c.val*x.val) = -y/c.val by rw [hY]; field_simp; ring] at hh
      dsimp only [D,G,s,f]; rw [hh]; ring
    simp_rw [eval,integral_const_mul,integral_mul_const]
    rw [show (∫ y, f (Y x y) ∂dx) = _ from d.integral_local_affine v f (k x) b]
    change (m x : ℂ) * (((d.jacquet v Φ x) / (m x : ℂ)) * s) = _
    dsimp only [s]
    field_simp [Complex.ofReal_ne_zero.mpr (hm x).ne']
  refine ⟨ri,?_,?_⟩
  · change (∫ y, R y * _ ∂dx) = _
    simp_rw [hR,← integral_mul_const]
    exact (integral_integral_swap hd).symm.trans (by simp_rw [inner]; exact d.integral_lineMeasure v _)
  · change (∫ y, ‖R y‖ ∂dx) ≤ _
    calc
      _ ≤ ∫ y, ∫ x, ‖G x y‖ ∂ν ∂dx := integral_mono ri.norm hi.integral_norm_prod_right
        (fun y => by rw [hR]; exact norm_integral_le_integral_norm _)
      _ = ∫ x, ∫ y, ‖G x y‖ ∂dx ∂ν := (integral_integral_swap hi.norm).symm
      _ = _ := by simp_rw [hsection]; exact (integral_prod _ hΦ.norm).symm

/-- Each normalized test lift has an absolutely integrable X-chart for d×x dy.
Integration along the fiber cancels the inverse modulus in its definition. -/
theorem integrable_jacquetLift_chart {W : Weight v} (hw : TestWeight v W) (β : K → ℂ)
    (ht : d.jacquetLift v W β ∈ d.testSet v) :
    Integrable (Function.uncurry (d.jacquetLift v W β).1) ((ν).prod dx) := by
  let Φ : d.schwartz v := ⟨_,Submodule.subset_span (Or.inl ht)⟩
  letI : (dx).IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  have hc : Continuous (Function.uncurry Φ.val.1) := by
    cases v with
    | inl w => exact d.continuous_arch_schwartz_X w Φ
    | inr p => exact (d.locallyConstant_finite_schwartz p Φ).1.continuous
  apply (integrable_prod_iff hc.aestronglyMeasurable).mpr
  refine ⟨.of_forall (d.integrable_jacquet_slice v Φ),?_⟩
  let B := ∫ y, ‖β y‖ ∂dx
  apply ((d.testWeight_integrable v hw).norm.mul_const B).congr
  filter_upwards with x
  have hx : 0 < modulus F v x.val := by cases v <;> simp [modulus,norm_pos_iff,x.ne_zero,pow_pos (norm_pos_iff.mpr x.ne_zero)]
  let h (y : K) := ‖Φ.val.1 x y‖
  have eval (y : K) : h (x.val*y) = ((modulus F v x.val)⁻¹ * ‖W x‖) * ‖β y‖ := by
    simp only [h,Φ,jacquetLift,jacquetLiftX,mul_div_cancel_left₀ _ x.ne_zero,norm_mul,norm_inv,
      Complex.norm_real,Real.norm_of_nonneg hx.le]
  have eqn := d.integral_local_mul v x (fun y => (h y : ℂ))
  rw [eq_div_iff (Complex.ofReal_ne_zero.mpr hx.ne')] at eqn
  simp only [integral_complex_ofReal,← Complex.ofReal_mul,Complex.ofReal_inj] at eqn
  simp_rw [eval,integral_const_mul] at eqn
  change ‖W x‖ * B = ∫ y, h y ∂dx
  rw [← eqn]
  dsimp only [B]
  field_simp

/-- For compact test weights the fixed-parameter line identity is realized
by an actual lift, with a single L¹ bound for all c and t. -/
theorem exists_jacquetLift_lines {W : Weight v} (hw : TestWeight v W) :
    ∃ Φ : d.schwartz v, Φ.val ∈ d.testSet v ∧ d.jacquet v Φ = W ∧
      ∃ B : ℝ, ∀ (c : Kˣ) (t : K),
        let R := (radon n (d.symbol v) (modulus F v) dx Φ.val t).1 c
        Integrable R dx ∧ (∫ y, R y * ψ (-y/c.val) ∂dx) = d.kernelIntegral v W c t ∧
          (∫ y, ‖R y‖ ∂dx) ≤ B := by
  obtain ⟨β,hβ,ht⟩ := d.exists_jacquetLift_auxiliary v
  let Φ : d.schwartz v := ⟨_,Submodule.subset_span (Or.inl (ht W hw))⟩
  have hJ : d.jacquet v Φ = W := d.jacquet_jacquetLift v W β hβ (ht W hw)
  refine ⟨Φ,ht W hw,hJ,∫ z, ‖Φ.val.1 z.1 z.2‖ ∂((ν).prod dx),fun c t => ?_⟩
  simpa only [hJ] using d.jacquet_radon_lines v Φ (d.integrable_jacquetLift_chart v hw β (ht W hw)) c t

/-- Before testing in the frequency variable, the Jacquet integral of the
transformed section is the transverse integral of the Fourier transformed
Radon slices. The phase survives the n-th power change of variables. -/
theorem jacquet_scaled_radon (Φ : d.schwartz v) (c u : Kˣ) :
    (Real.sqrt (modulus F v (n : K)) : ℂ) * d.jacquet v (d.fourier v Φ) (u^n*c) =
      (modulus F v u.val : ℂ) * ∫ y, d.hat v
        (fun t => (radon n (d.symbol v) (modulus F v) dx Φ.val t).1 c y) u.val * ψ (-y/c.val) ∂dx := by
  let m : ℂ := modulus F v u.val
  let s : ℂ := Real.sqrt (modulus F v (n : K))
  let f (y : K) := (d.fourier v Φ).val.1 (u^n*c) y * ψ (-y/(u^n*c).val)
  have phase (y : K) : -(u.val^n*y)/(u^n*c).val = -y/c.val := by
    rw [Units.val_mul,Units.val_pow_eq_pow_val]
    field_simp
  have h (y : K) : d.hat v (fun t => (radon n (d.symbol v) (modulus F v) dx Φ.val t).1 c y) u.val *
      ψ (-y/c.val) = (s*m^(n-1)) * f ((u^n).val*y) := by
    rw [d.hat_radon_scaled v Φ c u]
    simp only [f,phase,Units.val_pow_eq_pow_val,s,m,mul_assoc]
  simp_rw [h,integral_const_mul]
  rw [d.integral_local_mul]
  have hm : modulus F v (u^n).val = (modulus F v u.val)^n := by
    cases v <;> simp [modulus,norm_pow,pow_right_comm]
  rw [hm,Complex.ofReal_pow]
  change s * (∫ y, f y ∂dx) = m * ((s*m^(n-1))*((∫ y, f y ∂dx)/m^n))
  have hm' : m ≠ 0 := Complex.ofReal_ne_zero.mpr (modulus_ne_zero v u)
  have pow_eq : m*m^(n-1) = m^n := by rw [← pow_succ',Nat.sub_add_cancel (NeZero.pos n)]
  field_simp
  linear_combination -s*(∫ y, f y ∂dx)*pow_eq

end MetaplecticPoisson.Datum
