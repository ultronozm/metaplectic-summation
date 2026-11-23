import MetaplecticSummation.PowerClassFourier
import MetaplecticSummation.LineMoments
import MetaplecticSummation.PowerHaar
import MetaplecticSummation.BasicMarginals
import MetaplecticSummation.TamePowerClassFourier

/-! Class integrals of the axis values in the proof of Proposition B.4. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField MeasureTheory Set Filter
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n) (v : Place F)
local notation "K" => LocalField F v
local notation "G" => PowerClass n v
local notation "dx" => selfDual F d.character v

private def classFiber (c : G) : Set K := Units.val '' {u : Kˣ | QuotientGroup.mk u = c}

private theorem classFiber_measurable (c : G) : MeasurableSet (classFiber v c) := by
  have he : Topology.IsOpenEmbedding (Units.val : Kˣ → K) :=
    (IsOpen.isOpenEmbedding_subtypeVal isOpen_compl_singleton).comp unitsHomeomorphNeZero.isOpenEmbedding
  exact (he.isOpenMap _ (open_powerClass v c)).measurableSet

private theorem mem_classFiber (c : G) (u : Kˣ) : u.val ∈ classFiber v c ↔ QuotientGroup.mk u = c :=
  ⟨fun ⟨a,ha,he⟩ => Units.val_injective he ▸ ha,fun h => ⟨u,h,rfl⟩⟩

/-- The local function β used to cancel the two power-class sums in Proposition B.4. -/
def axisClassIntegral (Φ : d.schwartz v) (c : G) : ℂ :=
  (n : ℂ) * ∫ y in classFiber v c, (if hy : y ≠ 0 then d.axis v Φ (Units.mk0 y hy) else 0) ∂dx

/-- Its finite Hilbert transform is the symbol-weighted additive integral
of the axis. The factor n from the class integrals cancels the counting normalization. -/
theorem powerClassTransform_axisClassIntegral (Φ : d.schwartz v) (a : Kˣ)
    (hi : Integrable (fun y : K => if hy : y ≠ 0 then d.axis v Φ (Units.mk0 y hy) else 0) dx) :
    d.powerClassTransform v (d.axisClassIntegral v Φ) (QuotientGroup.mk a) =
      ∫ y, (if hy : y ≠ 0 then d.symbol v (Units.mk0 y hy) a * d.axis v Φ (Units.mk0 y hy) else 0) ∂dx := by
  let := finite_power_classes (n := n) v
  letI := Fintype.ofFinite G
  let f (y : K) := if hy : y ≠ 0 then d.axis v Φ (Units.mk0 y hy) else 0
  let χ (c : G) : ℂ := d.localClassPairing v c (QuotientGroup.mk a)
  let g (c : G) := (classFiber v c).indicator (fun y => χ c * f y)
  have hg (c : G) : Integrable (g c) dx := (hi.const_mul (χ c)).indicator (classFiber_measurable v c)
  have term (c : G) : χ c * d.axisClassIntegral v Φ c = (n : ℂ) * ∫ y, g c y ∂dx := by
    rw [show (∫ y, g c y ∂dx) = _ from integral_indicator (classFiber_measurable v c),integral_const_mul]
    change χ c * ((n : ℂ) * _) = n * (χ c * _)
    ring
  rw [powerClassTransform,finsum_eq_sum_of_fintype]
  change (n : ℂ)⁻¹ * (∑ c : G, χ c * d.axisClassIntegral v Φ c) = _
  simp_rw [term]
  rw [← Finset.mul_sum,← mul_assoc,inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne n)),one_mul,
    ← integral_finsetSum _ (fun c _ => hg c)]
  apply integral_congr_ae
  filter_upwards with y
  by_cases hy : y = 0
  · subst y
    have he (c : G) : g c 0 = 0 := by
      apply indicator_of_notMem
      rintro ⟨u,_,hu⟩
      exact u.ne_zero hu
    simp [he]
  · let u := Units.mk0 y hy
    rw [Finset.sum_eq_single (QuotientGroup.mk u)]
    · change (classFiber v _).indicator _ u.val = _
      rw [indicator_of_mem ((mem_classFiber v _ u).mpr rfl)]
      simp only [χ,localClassPairing_mk,coe_unitPairing,f,dif_pos hy]
      rw [dif_pos u.ne_zero]
      rfl
    · intro c _ hne
      exact indicator_of_notMem (fun h => hne ((mem_classFiber v c u).mp h).symm) _
    · simp

/-- The untwisted vertical-axis integral converges at every place. -/
theorem integrable_axis (Φ : d.schwartz v) :
    Integrable (fun z : K => if hz : z ≠ 0 then d.axis v Φ (Units.mk0 z hz) else 0) dx := by
  have h (a : Kˣ) : d.symbol v a 1 = 1 := congrArg Units.val ((d.unitPairing v a).map_one)
  apply ((d.schwartz_radon_convergence v Φ).2.1 0 0 1).congr
  filter_upwards with z
  simp only [lineIntegrandY,zero_mul,zero_pow (NeZero.ne n),zero_add,zero_div,h,mul_one,axis]


/-- Parametrizing a power class by the power map gives the additive integral
of the normalized axis density in Proposition B.4. -/
theorem axisClassIntegral_eq_integral_density (Φ : d.schwartz v) (a : Kˣ) :
    d.axisClassIntegral v Φ (QuotientGroup.mk a) = ∫ t, d.axisDensity v Φ (-1/a) t ∂dx := by
  let m (u : Kˣ) : ℂ := modulus F v u.val
  let N : ℂ := modulus F v (n : K)
  let q : Kˣ →* G := QuotientGroup.mk' (powMonoidHom n : Kˣ →* Kˣ).range
  let f (u : Kˣ) := m u * d.axis v Φ u
  have hc : Continuous f := by
    have hm : Continuous (fun u : Kˣ => modulus F v u.val) := by
      cases v <;> dsimp [modulus] <;> fun_prop
    exact (Complex.continuous_ofReal.comp hm).mul ((d.continuous_schwartz_charts v Φ).2.comp
      (continuous_const.prodMk continuous_id))
  have hcoset (u : Kˣ) : q (a*u) = q a ↔ ∃ t : Kˣ, u=t^n := by
    rw [map_mul,(Group.isUnit (q a)).mul_eq_left]
    change QuotientGroup.mk u = (1 : G) ↔ _
    rw [QuotientGroup.eq_one_iff]
    exact ⟨fun ⟨t,h⟩ => ⟨t,h.symm⟩,fun ⟨t,h⟩ => ⟨t,h.symm⟩⟩
  have hclass : d.axisClassIntegral v Φ (QuotientGroup.mk a) =
      n * d.lineIntegral v (fun u => if q u = q a then f u else 0) := by
    unfold axisClassIntegral lineIntegral
    rw [← integral_indicator (classFiber_measurable v _)]
    congr 1
    apply integral_congr_ae
    letI := d.selfDual_nullSingleton v
    filter_upwards [(dx).ae_ne 0] with y hy
    let u := Units.mk0 y hy
    change (classFiber v (q a)).indicator _ u.val = _
    by_cases h : q u = q a
    · rw [indicator_of_mem ((mem_classFiber v _ u).mpr h),dif_pos u.ne_zero,dif_pos hy,if_pos h]
      change d.axis v Φ u = m u * d.axis v Φ u / m u
      field_simp [show m u ≠ 0 from Complex.ofReal_ne_zero.mpr (modulus_ne_zero v u)]
    · rw [indicator_of_notMem (mt (mem_classFiber v _ u).mp h),dif_pos hy,if_neg h,zero_div]
  rw [hclass,← d.lineIntegral_mul v a]
  simp_rw [hcoset]
  rw [d.lineIntegral_on_powers v (fun u => f (a*u)) (hc.comp (continuous_const.mul continuous_id)).measurable,
    ← mul_assoc,show (n:ℂ) * (N / n) = N by field_simp [NeZero.ne (n : ℂ)],← integral_const_mul,
    ← (d.lineMeasure_modulus v (d.axisDensity v Φ (-1/a))).2]
  apply integral_congr_ae
  filter_upwards with u
  have hmod : m (a*u^n) = m a * m u ^ n := by
    cases v <;> simp [m,modulus,norm_mul,norm_pow,mul_pow,← pow_mul,Nat.mul_comm n]
  have hinv : (modulus F v (-1/a).val : ℂ) = (m a)⁻¹ := by
    cases v <;> simp [m,modulus,inv_pow]
  have hu : -(u^n) / (-1/a) = a*u^n := by simp [div_eq_mul_inv,mul_comm]
  rw [d.axisDensity_unit,hu,hinv,Complex.real_smul]
  dsimp only [f]
  have hp : m u ^ n = m u ^ (n-1) * m u := by
    rw [← pow_succ, Nat.sub_add_cancel (NeZero.pos n)]
  rw [hmod,hp,div_inv_eq_mul]
  dsimp only [m,N]
  ring

/-- The tame basic axis is supported on classes represented by integral units. -/
theorem axis_basic_zero_of_not_unitClass (p : Prime F) (hp : p.asIdeal.absNorm.Coprime n)
    (u : (LocalField F (.inr p))ˣ) (h : (QuotientGroup.mk u : PowerClass n (.inr p)) ∉ integralUnitClasses p n) :
    d.axis (.inr p) (d.basic (.inr p)) u = 0 := by
  rw [d.axis_basic p hp]
  let q := QuotientGroup.mk' (powMonoidHom n : (LocalField F (.inr p))ˣ →* _).range
  obtain ⟨π,hπ⟩ : ∃ π : (LocalField F (.inr p))ˣ, ‖π.val‖ = (p.asIdeal.absNorm : ℝ)⁻¹ := FinitePlace.exists_norm_uniformizer p
  apply (tsum_congr (g := fun _ => (0 : ℂ)) ?_).trans tsum_zero
  intro k
  apply ite_eq_right
  intro he
  apply h
  refine ⟨u / (π^k)^n,?_,?_⟩
  · change ‖(u / (π^k)^n).val‖ = 1
    rw [Units.val_div_eq_div_val,Units.val_pow_eq_pow_val,Units.val_pow_eq_pow_val,
      norm_div,norm_pow,norm_pow,hπ,inv_pow,inv_pow,← pow_mul,Nat.mul_comm k,he,div_self]
    have hq : 0 < (p.asIdeal.absNorm : ℝ) := by exact_mod_cast (Nat.zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm p))
    positivity
  · change q (u/(π^k)^n) = q u
    rw [map_div,show q ((π^k)^n) = 1 from (QuotientGroup.eq_one_iff _).mpr ⟨π^k,rfl⟩,div_one]

/-- At a tame place with unramified character, all basic axis class integrals
are the indicator of the integral-unit classes. -/
theorem axisClassIntegral_basic (p : Prime F) (hp : p.asIdeal.absNorm.Coprime n)
    (hψ : d.UnramifiedAt (.inr p)) :
    d.axisClassIntegral (.inr p) (d.basic (.inr p)) = unitClassTest p n := by
  let w : Place F := .inr p
  let B := d.basic w
  let q := QuotientGroup.mk' (powMonoidHom n : (LocalField F w)ˣ →* _).range
  funext c
  by_cases h : c ∈ integralUnitClasses p n
  · obtain ⟨a,ha,rfl⟩ := h
    change ‖a.val‖ = 1 at ha
    change d.axisClassIntegral (.inr p) _ (QuotientGroup.mk a) = unitClassTest p n (q a)
    rw [axisClassIntegral_eq_integral_density]
    have hunit : ‖(-1/a).val‖ = 1 := by simp [ha]
    simp_rw [d.axisDensity_basic p hp (FinitePlace.norm_degree_of_tame p hp) _ hunit]
    have hO : MeasurableSet {t : LocalField F w | ‖t‖ ≤ 1} := (isClosed_le continuous_norm continuous_const).measurableSet
    change (∫ t, {t : LocalField F w | ‖t‖ ≤ 1}.indicator (fun _ => (1:ℂ)) t ∂_) = _
    rw [integral_indicator hO,integral_const,measureReal_restrict_apply_univ,d.selfDual_volume_unramified p hψ,one_smul]
    exact (if_pos (show q a ∈ integralUnitClasses p n from ⟨a,ha,rfl⟩)).symm
  · rw [unitClassTest,if_neg h,axisClassIntegral]
    suffices H : ∀ y ∈ classFiber (.inr p) c, (if hy : y ≠ 0 then d.axis w B (Units.mk0 y hy) else 0) = 0 by
      rw [setIntegral_eq_zero_of_forall_eq_zero H,mul_zero]
    rintro y ⟨u,hu,rfl⟩
    rw [dif_pos u.ne_zero,Units.mk0_val]
    exact d.axis_basic_zero_of_not_unitClass p hp u (hu ▸ h)

/-- The reference factor for the multiplicative Poisson step of Proposition B.4. -/
theorem eventually_axisClassIntegral_basic (Φ : ∀ w, d.schwartz w)
    (hΦ : ∀ᶠ w in Filter.cofinite, Φ w = d.basic w) :
    ∀ᶠ p : Prime F in Filter.cofinite, d.axisClassIntegral (.inr p) (Φ (.inr p)) = unitClassTest p n := by
  have he := (Sum.inr_injective (α := InfinitePlace F)).tendsto_cofinite.eventually hΦ
  have ht := (FinitePlace.finite_places_over_degree («K» := F) n).eventually_cofinite_notMem
  filter_upwards [he,ht,
    d.eventually_unramified] with p h ht hψ
  rw [h]
  exact d.axisClassIntegral_basic p (FinitePlace.tame_of_degree_not_mem n p ht) hψ

/-- On an integral-unit line the unramified basic Radon marginal is the
indicator of the ring of integers, including at the zero parameter. -/
theorem axisLine_basic (p : Prime F) (hp : p.asIdeal.absNorm.Coprime n)
    (hψ : d.UnramifiedAt (.inr p)) (y : (LocalField F (.inr p))ˣ) (hy : ‖y.val‖ = 1)
    (t : LocalField F (.inr p)) :
    d.axisLine (.inr p) (d.basic (.inr p)) y t = if ‖t‖ ≤ 1 then 1 else 0 := by
  let w : Place F := .inr p
  have hsym : d.symbol w (-1) y = 1 := d.symbol_one_of_norm_powers p hp _ _ 1 1 (by simp) (by simpa using hy)
  by_cases ht : t = 0
  · subst t
    rw [d.axisLine_zero,← d.powerClassTransform_axisClassIntegral _ _ _ (d.integrable_axis _ _),
      d.axisClassIntegral_basic p hp hψ,d.powerClassTransform_unitClassTest p hp]
    have hc : QuotientGroup.mk y ∈ integralUnitClasses p n := ⟨y,hy,rfl⟩
    simp [unitClassTest,hc,hsym,w,modulus,hy]
  · let u := Units.mk0 t ht
    have e : (∃ k : ℕ, ‖(u^n/y).val‖ = ((p.asIdeal.absNorm : ℝ)^(n*k))⁻¹) ↔ ‖t‖ ≤ 1 := by
      simp only [Units.val_div_eq_div_val,Units.val_pow_eq_pow_val,norm_div,norm_pow,hy,div_one]
      have hq : 1 ≤ (p.asIdeal.absNorm : ℝ) := by exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm p).le
      constructor
      · rintro ⟨k,hk⟩
        by_contra! h
        exact (one_lt_pow₀ h (NeZero.ne n)).not_ge (hk.le.trans (inv_le_one_of_one_le₀ (one_le_pow₀ hq)))
      · intro h
        obtain ⟨k,hk⟩ := integral_norm_power p u h
        change ‖u.val‖ = ((p.asIdeal.absNorm : ℝ)^k)⁻¹ at hk
        exact ⟨k,by rw [hk,inv_pow,← pow_mul,Nat.mul_comm k]⟩
    change d.axisLine w (d.basic w) y u.val = _
    rw [d.axisLine_unit,hsym]
    have hm := d.basicCharts_marginal p hp hψ (u^n/y)
    have hb : (d.basic w).val = d.basicCharts p := by
      change (if h : p.asIdeal.absNorm.Coprime n then (⟨_,d.basic_mem p h⟩ : d.schwartz (.inr p)) else 0).val = _
      rw [dif_pos hp]
    rw [marginal,hb,hm,if_congr e rfl rfl]
    simp [w,modulus,hy]

/-- The Radon test in the first additive Poisson formula of Proposition B.4
is the integral-unit ball at almost every finite place. -/
theorem eventually_axisLine_basic (Φ : ∀ w, d.schwartz w)
    (hΦ : ∀ᶠ w in cofinite, Φ w = d.basic w) (y : Fˣ) :
    ∀ᶠ p : Prime F in cofinite, ∀ t : LocalField F (.inr p),
      d.axisLine (.inr p) (Φ (.inr p)) (atPlace (.inr p) y) t = if ‖t‖ ≤ 1 then 1 else 0 := by
  have he := (Sum.inr_injective (α := InfinitePlace F)).tendsto_cofinite.eventually hΦ
  have ht := (FinitePlace.finite_places_over_degree («K» := F) n).eventually_cofinite_notMem
  filter_upwards [he,ht,d.eventually_unramified,eventually_diagonal_norm_one y.ne_zero] with p h ht hψ hy
  rw [h]
  exact d.axisLine_basic p (FinitePlace.tame_of_degree_not_mem n p ht) hψ _ hy

end MetaplecticPoisson.Datum
