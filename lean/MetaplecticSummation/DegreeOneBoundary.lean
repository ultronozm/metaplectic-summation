import MetaplecticSummation.FourierCoefficients

/-! The degree-one boundary value after Theorem 9.1. Every local leading term
is constant, since the frequency-zero Radon integral of a test section is its
integral over the plane. Averaging the Poisson formula over adelic upper
unipotents and applying the constant-term identity then evaluates the boundary
functional on the Y-axis. -/

noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField MeasureTheory Filter Set
open Classical
variable {F : Type} [Field F] [NumberField F] (d : Datum F 1) (v : Place F)
local notation "K" => LocalField F v
local notation "dx" => selfDual F d.character v

/-- In degree one every local symbol is trivial. -/
theorem symbol_degree_one (a b : Kˣ) : d.symbol v a b = 1 := by
  have h := d.unitPairing_pow v a b
  rw [pow_one] at h
  rw [← coe_unitPairing,h,Units.val_one]

private theorem le_modulus_of_one_le {x : K} (hx : 1 ≤ ‖x‖) : ‖x‖ ≤ modulus F v x := by
  cases v with
  | inl w => exact le_self_pow₀ hx w.mult_ne_zero
  | inr p => exact le_rfl

private theorem isOpen_fst_ne : IsOpen {z : K × K | z.1 ≠ 0} := by
  convert isOpen_lt (continuous_const : Continuous fun _ : K × K => (0:ℝ)) (continuous_norm.comp continuous_fst) using 1
  ext z
  simp only [Set.mem_ofPred_eq,Function.comp_apply,norm_pos_iff]

private theorem isOpen_snd_ne : IsOpen {z : K × K | z.2 ≠ 0} := by
  convert isOpen_lt (continuous_const : Continuous fun _ : K × K => (0:ℝ)) (continuous_norm.comp continuous_snd) using 1
  ext z
  simp only [Set.mem_ofPred_eq,Function.comp_apply,norm_pos_iff]

private theorem aestronglyMeasurable_of_continuousOn {G : K × K → ℂ} {s : Set (K × K)} (hs : IsOpen s)
    (hG : ContinuousOn G s) (h0 : ∀ z ∉ s, G z = 0) (μ : Measure (K × K)) : AEStronglyMeasurable G μ := by
  have he : s.indicator G = G := indicator_eq_self.mpr fun z hz => by
    by_contra h
    exact hz (h0 z h)
  rw [← he]
  exact (aestronglyMeasurable_indicator_iff hs.measurableSet).mpr (hG.aestronglyMeasurable hs.measurableSet)

theorem continuousOn_xChart (Φ : d.schwartz v) : ContinuousOn (xChart Φ.val) {z : K × K | z.1 ≠ 0} := by
  let : NontriviallyNormedField K := { localNormedField F v with
    non_trivial := by
      cases v with
      | inl w => exact (archNontriviallyNormedCompletion w).non_trivial
      | inr p => exact (FinitePlace.nontriviallyNormedCompletion p).non_trivial }
  intro z hz
  have hz' : z.1 ≠ 0 := hz
  have hc : ContinuousAt (fun p : K × K => Function.uncurry Φ.val.1 (liftUnit p.1,p.2)) z :=
    (d.continuous_schwartz_charts v Φ).1.continuousAt.comp
      (((liftUnit_continuousAt hz').comp continuousAt_fst).prodMk continuousAt_snd)
  refine (hc.congr ?_).continuousWithinAt
  filter_upwards [(isOpen_fst_ne v).mem_nhds hz'] with p hp
  have hp' : p.1 ≠ 0 := hp
  simp only [Function.uncurry,xChart,ne_eq,hp',not_false_eq_true,dite_true]
  rw [show liftUnit p.1 = Units.mk0 p.1 hp' from Units.ext (liftUnit_val hp')]

theorem continuousOn_yChart (Φ : d.schwartz v) : ContinuousOn (yChart Φ.val) {z : K × K | z.2 ≠ 0} := by
  let : NontriviallyNormedField K := { localNormedField F v with
    non_trivial := by
      cases v with
      | inl w => exact (archNontriviallyNormedCompletion w).non_trivial
      | inr p => exact (FinitePlace.nontriviallyNormedCompletion p).non_trivial }
  intro z hz
  have hz' : z.2 ≠ 0 := hz
  have hc : ContinuousAt (fun p : K × K => Function.uncurry Φ.val.2 (p.1,liftUnit p.2)) z :=
    (d.continuous_schwartz_charts v Φ).2.continuousAt.comp
      (continuousAt_fst.prodMk ((liftUnit_continuousAt hz').comp continuousAt_snd))
  refine (hc.congr ?_).continuousWithinAt
  filter_upwards [(isOpen_snd_ne v).mem_nhds hz'] with p hp
  have hp' : p.2 ≠ 0 := hp
  simp only [Function.uncurry,yChart,ne_eq,hp',not_false_eq_true,dite_true]
  rw [show liftUnit p.2 = Units.mk0 p.2 hp' from Units.ext (liftUnit_val hp')]

/-- In degree one the chart bound (4.2) has exponent zero at the origin, so
both charts are integrable on the plane. -/
theorem integrable_charts_degree_one (Φ : d.schwartz v) :
    Integrable (xChart Φ.val) ((dx).prod dx) ∧ Integrable (yChart Φ.val) ((dx).prod dx) := by
  let : (dx).IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  obtain ⟨C,hC,H⟩ := d.schwartz_chart_growth v Φ 6 (by decide)
  let φ (t : K) := ((1+‖t‖)^3)⁻¹
  have hφ : Integrable φ dx := d.integrable_local_inv_cube v
  have hM : Integrable (fun z : K × K => C * (64 * (φ z.1 * φ z.2))) ((dx).prod dx) :=
    ((hφ.mul_prod hφ).const_mul _).const_mul _
  have bound (z : K × K) (hz : z ≠ 0) :
      C * min ((max (modulus F v z.1) (modulus F v z.2))^(-(growthExponent 1)))
        ((max (modulus F v z.1) (modulus F v z.2))^(-((6:ℕ):ℝ))) ≤ C * (64 * (φ z.1 * φ z.2)) := by
    set r := max (modulus F v z.1) (modulus F v z.2)
    have hg : growthExponent 1 = 0 := by simp [growthExponent]
    rw [hg,neg_zero,Real.rpow_zero]
    apply mul_le_mul_of_nonneg_left _ hC
    set M := max ‖z.1‖ ‖z.2‖
    have hx : 0 ≤ ‖z.1‖ := norm_nonneg _
    have hy : 0 ≤ ‖z.2‖ := norm_nonneg _
    have hprod : (1+‖z.1‖)^3*(1+‖z.2‖)^3 ≤ (1+M)^6 := by
      rw [show (1+M)^6 = (1+M)^3*(1+M)^3 by ring]
      exact mul_le_mul (pow_le_pow_left₀ (by positivity) (by linarith [le_max_left ‖z.1‖ ‖z.2‖]) 3)
        (pow_le_pow_left₀ (by positivity) (by linarith [le_max_right ‖z.1‖ ‖z.2‖]) 3) (by positivity) (by positivity)
    have hpos : 0 < (1+‖z.1‖)^3*(1+‖z.2‖)^3 := by positivity
    have hφφ : φ z.1 * φ z.2 = ((1+‖z.1‖)^3*(1+‖z.2‖)^3)⁻¹ := by simp only [φ,mul_inv]
    rw [hφφ,← div_eq_mul_inv,le_div_iff₀ hpos]
    by_cases hM1 : M ≤ 1
    · calc min 1 (r^(-((6:ℕ):ℝ))) * ((1+‖z.1‖)^3*(1+‖z.2‖)^3) ≤ 1 * (1+M)^6 :=
            mul_le_mul (min_le_left _ _) hprod hpos.le zero_le_one
        _ ≤ 64 := by nlinarith [pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 1+M) (by linarith : 1+M ≤ 2) 6]
    · have hM1' : 1 ≤ M := (lt_of_not_ge hM1).le
      have hrM : M ≤ r := by
        rcases le_total ‖z.1‖ ‖z.2‖ with h|h
        · rw [show M = ‖z.2‖ from max_eq_right h]
          exact (le_modulus_of_one_le v (show 1 ≤ ‖z.2‖ by rwa [← max_eq_right h])).trans (le_max_right _ _)
        · rw [show M = ‖z.1‖ from max_eq_left h]
          exact (le_modulus_of_one_le v (show 1 ≤ ‖z.1‖ by rwa [← max_eq_left h])).trans (le_max_left _ _)
      have hr : 0 < r := zero_lt_one.trans_le (hM1'.trans hrM)
      have hr6 : r^(-((6:ℕ):ℝ)) = (r^6)⁻¹ := by rw [Real.rpow_neg hr.le,Real.rpow_natCast]
      calc min 1 (r^(-((6:ℕ):ℝ))) * ((1+‖z.1‖)^3*(1+‖z.2‖)^3) ≤ (M^6)⁻¹ * (2*M)^6 := by
            apply mul_le_mul _ (hprod.trans (pow_le_pow_left₀ (by positivity) (by linarith) 6)) hpos.le (by positivity)
            rw [hr6]
            exact (min_le_right _ _).trans (inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hrM 6))
        _ = 64 := by
            have : M^6 ≠ 0 := pow_ne_zero _ (by positivity)
            field_simp
            ring
  constructor
  · refine hM.mono' (aestronglyMeasurable_of_continuousOn v (isOpen_fst_ne v)
      (d.continuousOn_xChart v Φ) (fun z hz => by simp_all [xChart]) _) (.of_forall fun z => ?_)
    by_cases hz : z = 0
    · simp only [hz,xChart,Prod.fst_zero,ne_eq,not_true_eq_false,dite_false,norm_zero]
      positivity
    · exact (H z hz).1.trans (bound z hz)
  · refine hM.mono' (aestronglyMeasurable_of_continuousOn v (isOpen_snd_ne v)
      (d.continuousOn_yChart v Φ) (fun z hz => by simp_all [yChart]) _) (.of_forall fun z => ?_)
    by_cases hz : z = 0
    · simp only [hz,yChart,Prod.snd_zero,ne_eq,not_true_eq_false,dite_false,norm_zero]
      positivity
    · exact (H z hz).2.trans (bound z hz)

private theorem modulus_pos {x : K} (hx : x ≠ 0) : 0 < modulus F v x := by
  cases v <;> simp [modulus,norm_pos_iff.mpr hx,pow_pos]

private theorem integrable_affine {f : K → ℂ} (hf : Integrable f dx) (k : Kˣ) (b : K) :
    Integrable (fun z => f (k.val*z+b)) dx := by
  let : (dx).IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  let e := MeasurableEquiv.smul (α := K) k
  have hi := (measurePreserving_add_right dx b).integrable_comp_of_integrable hf
  apply (e.measurableEmbedding.integrable_map_iff (g := fun t => f (t+b))).mp
  change Integrable _ (Measure.map (fun t => k.val*t) dx)
  rw [d.map_local_mul]
  exact hi.smul_measure_nnreal

private theorem integral_affine {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : K → E) (k : Kˣ) (b : K) :
    (∫ z, f (k.val*z+b) ∂dx) = (modulus F v k.val)⁻¹ • ∫ z, f z ∂dx := by
  let : (dx).IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  let e := MeasurableEquiv.smul (α := K) k
  have h := e.measurableEmbedding.integral_map (μ := dx) (fun t => f (t+b))
  change (∫ t, f (t+b) ∂Measure.map (fun t => k.val*t) dx) = ∫ z, f (k.val*z+b) ∂dx at h
  rw [← h,d.map_local_mul,integral_smul_nnreal_measure,integral_add_right_eq_self,NNReal.smul_def,
    NNReal.coe_inv,Real.coe_toNNReal _ (modulus_pos v k.ne_zero).le]

private theorem modulus_one : modulus F v (1 : K) = 1 := by
  cases v <;> simp [modulus]

/-- The two charts of a degree-one section agree almost everywhere on the plane. -/
theorem xChart_ae_eq_yChart {f : Charts K} (hf : Glues (d.symbol v) f) :
    xChart f =ᵐ[(dx).prod dx] yChart f := by
  let : (dx).IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  let : NullSingletonClass dx := d.selfDual_nullSingleton v
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae ((dx).ae_ne 0),
    Measure.quasiMeasurePreserving_snd.ae ((dx).ae_ne 0)] with z h₁ h₂
  have h := hf (Units.mk0 z.1 h₁) (Units.mk0 z.2 h₂)
  simp only [Units.val_mk0,d.symbol_degree_one,one_mul] at h
  simp only [xChart,yChart,ne_eq,h₁,h₂,not_false_eq_true,dite_true,h]

/-- In degree one, both charts of the frequency-zero Radon integral of a test
section equal the integral of its X-chart over the plane. -/
theorem radonLeading_degree_one {f : Charts K} (hf : f ∈ d.testSet v) :
    (∀ a b, (d.radonLeading v f).1 a b = ∫ z, xChart f z ∂((dx).prod dx)) ∧
      ∀ a b, (d.radonLeading v f).2 a b = ∫ z, xChart f z ∂((dx).prod dx) := by
  let : (dx).IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  let Φ : d.schwartz v := ⟨f,Submodule.subset_span (Or.inl hf)⟩
  obtain ⟨hX,hY⟩ : Integrable (xChart f) ((dx).prod dx) ∧ Integrable (yChart f) ((dx).prod dx) :=
    d.integrable_charts_degree_one v Φ
  have hc : ((Real.sqrt (modulus F v ((1 : ℕ) : K)))⁻¹ : ℂ) = 1 := by
    rw [Nat.cast_one,modulus_one,Real.sqrt_one,Complex.ofReal_one,inv_one]
  constructor
  · intro a b
    let G (x t : K) := xChart f (x,(x*b-t)/a.val)
    let k : Kˣ := -a⁻¹
    have hk (x t : K) : (x*b-t)/a.val = k.val*t + x*b/a.val := by
      simp only [k,Units.val_neg,Units.val_inv_eq_inv_val]
      field_simp
      ring
    have hmk : (modulus F v k.val)⁻¹ = modulus F v a.val := by
      cases v <;> simp [k,modulus,norm_inv,inv_pow]
    have hR (t : K) : (radon 1 (d.symbol v) (modulus F v) dx f t).1 a b =
        (∫ x, G x t ∂dx) / (modulus F v a.val : ℂ) := by
      unfold radon
      dsimp only
      congr 2
      funext x
      by_cases hx : x = 0
      · simp [G,xChart,hx]
      · simp [G,xChart,hx,d.symbol_degree_one]
    have hslice (x : K) : (∫ t, G x t ∂dx) = (modulus F v a.val : ℂ) * ∫ y, xChart f (x,y) ∂dx := by
      simp only [G,hk]
      rw [d.integral_affine v (fun y => xChart f (x,y)) k (x*b/a.val),hmk,Complex.real_smul]
    have hnorm (x : K) : (∫ t, ‖G x t‖ ∂dx) = modulus F v a.val * ∫ y, ‖xChart f (x,y)‖ ∂dx := by
      simp only [G,hk]
      rw [d.integral_affine v (fun y => ‖xChart f (x,y)‖) k (x*b/a.val),hmk,smul_eq_mul]
    have hG : Integrable (Function.uncurry G) ((dx).prod dx) := by
      have hm : AEStronglyMeasurable (Function.uncurry G) ((dx).prod dx) := by
        apply aestronglyMeasurable_of_continuousOn v (s := {p : K × K | p.1 ≠ 0})
          (isOpen_fst_ne v)
        · exact (d.continuousOn_xChart v Φ).comp (Continuous.continuousOn (by fun_prop)) (fun p hp => hp)
        · intro p hp
          simp only [Set.mem_ofPred_eq,not_not] at hp
          simp [Function.uncurry,G,xChart,hp]
      refine (integrable_prod_iff hm).mpr ⟨?_,?_⟩
      · filter_upwards [hX.prod_right_ae] with x hx
        simpa only [Function.uncurry,G,hk] using d.integrable_affine v hx k (x*b/a.val)
      · simpa only [Function.uncurry,hnorm] using hX.integral_norm_prod_left.const_mul (modulus F v a.val)
    have ha : (modulus F v a.val : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (modulus_pos v a.ne_zero).ne'
    unfold radonLeading
    simp only [hc,one_mul,hR,integral_div]
    rw [← integral_integral_swap hG]
    simp only [hslice,integral_const_mul]
    rw [integral_prod _ hX]
    field_simp
  · intro a b
    let G (y t : K) := yChart f ((a*y+t)/b.val,y)
    let k : Kˣ := b⁻¹
    have hk (y t : K) : (a*y+t)/b.val = k.val*t + a*y/b.val := by
      simp only [k,Units.val_inv_eq_inv_val]
      field_simp
      ring
    have hmk : (modulus F v k.val)⁻¹ = modulus F v b.val := by
      cases v <;> simp [k,modulus,norm_inv,inv_pow]
    have hR (t : K) : (radon 1 (d.symbol v) (modulus F v) dx f t).2 a b =
        (∫ y, G y t ∂dx) / (modulus F v b.val : ℂ) := by
      unfold radon
      dsimp only
      congr 2
      funext y
      by_cases hy : y = 0
      · simp [G,yChart,hy]
      · simp [G,yChart,hy,d.symbol_degree_one]
    have hslice (y : K) : (∫ t, G y t ∂dx) = (modulus F v b.val : ℂ) * ∫ z, yChart f (z,y) ∂dx := by
      simp only [G,hk]
      rw [d.integral_affine v (fun z => yChart f (z,y)) k (a*y/b.val),hmk,Complex.real_smul]
    have hnorm (y : K) : (∫ t, ‖G y t‖ ∂dx) = modulus F v b.val * ∫ z, ‖yChart f (z,y)‖ ∂dx := by
      simp only [G,hk]
      rw [d.integral_affine v (fun z => ‖yChart f (z,y)‖) k (a*y/b.val),hmk,smul_eq_mul]
    have hG : Integrable (Function.uncurry G) ((dx).prod dx) := by
      have hm : AEStronglyMeasurable (Function.uncurry G) ((dx).prod dx) := by
        apply aestronglyMeasurable_of_continuousOn v (s := {p : K × K | p.1 ≠ 0})
          (isOpen_fst_ne v)
        · exact (d.continuousOn_yChart v Φ).comp (Continuous.continuousOn (by fun_prop)) (fun p hp => hp)
        · intro p hp
          simp only [Set.mem_ofPred_eq,not_not] at hp
          simp [Function.uncurry,G,yChart,hp]
      refine (integrable_prod_iff hm).mpr ⟨?_,?_⟩
      · filter_upwards [hY.prod_left_ae] with y hy
        simpa only [Function.uncurry,G,hk] using d.integrable_affine v hy k (a*y/b.val)
      · simpa only [Function.uncurry,hnorm] using hY.integral_norm_prod_right.const_mul (modulus F v b.val)
    have hb : (modulus F v b.val : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (modulus_pos v b.ne_zero).ne'
    unfold radonLeading
    simp only [hc,one_mul,hR,integral_div]
    rw [← integral_integral_swap hG]
    simp only [hslice,integral_const_mul]
    rw [← integral_prod_symm _ hY,integral_congr_ae (d.xChart_ae_eq_yChart v hf.1)]
    field_simp

/-- In degree one the leading term of every local Schwartz section takes a
single value in both charts, as in the paragraph after Proposition 8.1. -/
theorem leading_const_degree_one (Ψ : d.schwartz v) :
    ∃ c : ℂ, (∀ x y, (d.leading v Ψ).1 x y = c) ∧ ∀ x y, (d.leading v Ψ).2 x y = c := by
  obtain ⟨f,hf⟩ := Ψ
  induction hf using Submodule.span_induction with
  | mem f hf =>
    rcases hf with hf|⟨g,hg,rfl⟩
    · refine ⟨0,fun x y => ?_,fun x y => ?_⟩ <;>
      · cases v with
        | inl w => rw [d.leading_archTest_eq_zero w _ hf]; rfl
        | inr p => rw [d.leading_finiteTest_eq_zero p _ hf]; rfl
    · obtain ⟨h₁,h₂⟩ := d.radonLeading_degree_one v hg
      have he : d.leading v ⟨d.integralTransform v g,Submodule.subset_span (Or.inr ⟨g,hg,rfl⟩)⟩ =
          d.radonLeading v g := by
        cases v with
        | inl w => exact d.leading_archTest_transform w hg
        | inr p => exact d.leading_finiteTest_transform p hg
      exact ⟨_,fun x y => (congrArg (·.1 x y) he).trans (h₁ x y),
        fun x y => (congrArg (·.2 x y) he).trans (h₂ x y)⟩
  | zero =>
    refine ⟨0,fun x y => ?_,fun x y => ?_⟩ <;>
    · rw [show (⟨0,_⟩ : d.schwartz v) = 0 from rfl,map_zero]; rfl
  | add f g hf hg ihf ihg =>
    obtain ⟨a,ha₁,ha₂⟩ := ihf
    obtain ⟨b,hb₁,hb₂⟩ := ihg
    have he : (⟨f+g,add_mem hf hg⟩ : d.schwartz v) = ⟨f,hf⟩ + ⟨g,hg⟩ := rfl
    refine ⟨a+b,fun x y => ?_,fun x y => ?_⟩
    · rw [he,map_add]; exact congrArg₂ (·+·) (ha₁ x y) (hb₁ x y)
    · rw [he,map_add]; exact congrArg₂ (·+·) (ha₂ x y) (hb₂ x y)
  | smul r f hf ih =>
    obtain ⟨a,ha₁,ha₂⟩ := ih
    have he : (⟨r • f,Submodule.smul_mem _ r hf⟩ : d.schwartz v) = r • ⟨f,hf⟩ := rfl
    refine ⟨r*a,fun x y => ?_,fun x y => ?_⟩
    · rw [he,map_smul]; exact congrArg (r * ·) (ha₁ x y)
    · rw [he,map_smul]; exact congrArg (r * ·) (ha₂ x y)

/-- In degree one the upper shears fix every local leading term. -/
theorem upperShear_leading_degree_one (u : K) (Ψ : d.schwartz v) :
    upperShear (d.symbol v) u (d.leading v Ψ) = d.leading v Ψ := by
  obtain ⟨c,h₁,h₂⟩ := d.leading_const_degree_one v Ψ
  ext x y
  · simp only [upperShear,h₁]
  · simp [upperShear,h₁,h₂,d.symbol_degree_one]

/-- In degree one the leading term on the Y-axis is its value at (1,0). -/
theorem leading_axis_degree_one (Ψ : d.schwartz v) (y : Kˣ) :
    (d.leading v Ψ).2 0 y = (d.leading v Ψ).1 1 0 := by
  obtain ⟨c,h₁,h₂⟩ := d.leading_const_degree_one v Ψ
  rw [h₁,h₂]

local instance : MeasurableSpace (AdeleQuotient F) := borel _
local instance : BorelSpace (AdeleQuotient F) := ⟨rfl⟩

private theorem axisBoundary_degree_one (Φ : ∀ v, d.schwartz v) :
    d.axisBoundary Φ = ∏ᶠ v, (d.leading v (Φ v)).1 1 0 := by
  have htop : (powMonoidHom 1 : Fˣ →* Fˣ).range = ⊤ :=
    MonoidHom.range_eq_top.mpr fun x => ⟨x,pow_one x⟩
  let : Subsingleton (GlobalClass 1 F) := ⟨fun a b => Quotient.inductionOn₂' a b fun x y =>
    QuotientGroup.eq.mpr (htop ▸ Subgroup.mem_top _)⟩
  let : Unique (GlobalClass 1 F) := uniqueOfSubsingleton (1 : GlobalClass 1 F)
  unfold axisBoundary
  simp_rw [d.leading_axis_degree_one]
  rw [finsum_unique,Nat.cast_one,inv_one,one_mul]

/-- The paragraph following Theorem 9.1. In degree one the leading term
in the direction (1,0) gives the local Schwartz function's value at zero. -/
theorem boundary_degree_one (f : ∀ v, d.schwartz v)
    (hf : ∀ᶠ v in cofinite, f v = d.basic v) :
    d.poisson.exists.choose (d.adelicLeading (d.pure f hf)) =
      ∏ᶠ v, ((d.leading v) (f v)).1 1 0 := by
  have hB : d.IsPoissonBoundary d.poisson.exists.choose := d.poisson.exists.choose_spec
  generalize d.poisson.exists.choose = B at hB ⊢
  obtain ⟨I,hI,hprime⟩ := Ring.not_isField_iff_exists_prime.mp (NumberField.RingOfIntegers.not_isField F)
  let p : Prime F := ⟨I,hprime,hI⟩
  let w : Place F := .inr p
  obtain ⟨π,hπ⟩ := FinitePlace.exists_norm_uniformizer p
  let g := Function.update f w (d.boundaryModification p π (f w))
  have hg : ∀ᶠ v in cofinite, g v = d.basic v := by
    filter_upwards [hf,eventually_cofinite_ne w] with v hv hw
    exact (Function.update_of_ne hw _ _).trans hv
  have hs := d.boundaryModification_spec p π hπ (f w)
  have hgw : g w = d.boundaryModification p π (f w) := Function.update_self ..
  have hlead (v : Place F) : d.leading v (g v) = d.leading v (f v) := by
    by_cases h : v = w
    · subst h
      rw [hgw]
      exact hs.1
    · simp only [g,Function.update_of_ne h]
  let dual := fun v => d.fourier v (g v)
  have hd : ∀ᶠ v in cofinite, dual v = d.basic v := by
    filter_upwards [hg,d.eventually_fourier_basic] with v h h'
    exact (congrArg (d.fourier v) h).trans h'
  have hdw : d.leading w (dual w) = 0 := by
    change d.leading w (d.fourier w (g w)) = 0
    rw [hgw]
    exact hs.2
  -- Poisson at every upper unipotent translate of the modified tensor.
  have key (u : Adeles F) :
      d.translatedTheta dual u = d.translatedTheta g u + B (d.adelicLeading (d.pure f hf)) := by
    choose s hs' _ using fun v => d.exists_upper v (component u v)
    have hΦ : ∀ᶠ v in cofinite, s v (g v) = d.basic v :=
      hg.and (d.eventually_upper_basic u s hs') |>.mono fun v e => by rw [e.1,e.2]
    have hΨ : ∀ᶠ v in cofinite, s v (dual v) = d.basic v := by
      filter_upwards [hd,d.eventually_upper_basic u s hs'] with v h₁ h₂
      rw [h₁,h₂]
    rw [d.translatedTheta_eq_upper u s hs' g hΦ,d.translatedTheta_eq_upper u s hs' dual hΨ]
    have hF : d.adelicFourier (d.pure (fun v => s v (g v)) hΦ) = d.pure (fun v => s v (dual v)) hΨ := by
      rw [d.adelicFourier_pure]
      congr 1
      funext v
      exact d.fourier_upper v _ (hs' v) (g v)
    have hz : d.adelicLeading (d.pure (fun v => s v (dual v)) hΨ) = 0 := by
      apply d.adelicLeading_pure_eq_zero _ _ w
      rw [d.leading_upper w _ (hs' w),hdw]
      exact (upperShearLinear _ _).map_zero
    have he : d.adelicLeading (d.pure (fun v => s v (g v)) hΦ) = d.adelicLeading (d.pure f hf) := by
      apply Subtype.ext
      change PiTensorProduct.map _ (PiTensorProduct.tprod ℂ _) = PiTensorProduct.map _ (PiTensorProduct.tprod ℂ f)
      rw [PiTensorProduct.map_tprod,PiTensorProduct.map_tprod]
      apply congrArg (PiTensorProduct.tprod ℂ)
      funext v
      apply Subtype.ext
      change d.leading v (s v (g v)) = d.leading v (f v)
      rw [d.leading_upper v _ (hs' v),d.upperShear_leading_degree_one,hlead]
    have hP := (hB (d.pure (fun v => s v (g v)) hΦ)).2.2
    have hz' : B (d.adelicLeading (d.pure (fun v => s v (dual v)) hΨ)) = 0 := by
      rw [hz]
      exact B.map_zero
    rw [hF,hz'] at hP
    have hP' : d.theta (d.pure (fun v => s v (g v)) hΦ) + B (d.adelicLeading (d.pure (fun v => s v (g v)) hΦ)) =
        d.theta (d.pure (fun v => s v (dual v)) hΨ) + 0 := hP
    linear_combination -hP' + congrArg B he
  generalize B (d.adelicLeading (d.pure f hf)) = c at key ⊢
  -- Integrate over the adelic quotient.
  let := (exists_quotient_measure (F := F)).exists.choose_spec.2
  have hint : d.coefficient dual 0 = d.coefficient g 0 + c := by
    have hi := (d.coefficient_eq_slope_integrals g hg 0).1
    unfold coefficient
    calc _ = ∫ q, (d.quotientIntegrand g 0 q + c)
          ∂(exists_quotient_measure (F := F)).exists.choose := by
          apply integral_congr_ae
          filter_upwards with q
          induction q using Quotient.inductionOn with | _ u => _
          simp only [quotientIntegrand_mk,map_zero,zero_mul,neg_zero,AddChar.map_zero_eq_one,
            Circle.coe_one,mul_one]
          exact key u
      _ = _ := by rw [integral_add hi (integrable_const _),integral_const,probReal_univ,one_smul]
  have hone : ∀ᶠ v in cofinite, (d.leading v (dual v)).1 1 0 = 1 := by
    apply eventually_place_of_finite (P := fun v => (d.leading v (dual v)).1 1 0 = 1)
    filter_upwards [d.eventually_axisDensity_basic dual hd 1] with q hq
    have h0 := hq 0
    rw [axisDensity_zero,d.leading_axis_degree_one] at h0
    simpa [modulus] using h0
  have hfin : Function.HasFiniteMulSupport fun v => (d.leading v (dual v)).1 1 0 :=
    (eventually_cofinite.mp hone).subset fun _ hv => hv
  have hzero : d.axisBoundary dual = 0 := by
    rw [axisBoundary_degree_one]
    exact finprod_eq_zero _ w (by rw [hdw]; rfl) hfin
  have h₁ := (d.unfolding g hg).1
  have h₂ := (d.unfolding dual hd).1
  have h₃ : d.constantTerm g + d.axisBoundary g = d.constantTerm dual + d.axisBoundary dual :=
    d.constantTerm_identity g hg
  rw [hzero,axisBoundary_degree_one] at h₃
  simp only [hlead] at h₃
  linear_combination -hint + h₂ - h₁ - h₃

end MetaplecticPoisson.Datum
