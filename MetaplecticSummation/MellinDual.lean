import MetaplecticSummation.TateLocal
import MetaplecticSummation.Jacquet.ArchWeak
import MetaplecticSummation.Jacquet.Convergence
import MetaplecticSummation.PowerHaar
import MetaplecticSummation.LocalPowerClasses
import MetaplecticSummation.Marginals.Density

/-! Proposition 10.20: the Mellin transform of W^∨ for W supported on one class βKˣⁿ.

The proof follows the paper. With H the Fourier transform of x ↦ |x|^{-1} W(1/x),
the root-Fourier formula gives W^∨(dμⁿ) = |n|^{-1/2} {β,−d} |μ| V̂_d(μ), where
V_d(τ) = H(−τⁿ/d). Splitting Z(W^∨, ω, s) over the finitely many classes dKˣⁿ, Tate's
equation for ω⁻ⁿ turns each piece into an integral of H over the class −d⁻¹Kˣⁿ.
Summing, and applying Tate's equation for η = ω{β,·} to H, gives the proposition. -/

noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField MeasureTheory Filter Set
open scoped Topology
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n) (v : Place F)
local notation "Kv" => LocalField F v
local notation "dx" => selfDual F d.character v
local notation "m" => modulus F v
local notation "μ" => d.lineMeasure v

theorem symbol_mul_left (a b c : (Kv)ˣ) : d.symbol v (a*b) c = d.symbol v a c * d.symbol v b c := by
  simp only [← coe_unitPairing,map_mul,MonoidHom.mul_apply,Units.val_mul]

theorem symbol_mul_right (a b c : (Kv)ˣ) : d.symbol v a (b*c) = d.symbol v a b * d.symbol v a c := by
  simp only [← coe_unitPairing,map_mul,Units.val_mul]

theorem symbol_pow_left (a c : (Kv)ˣ) : d.symbol v (a^n) c = 1 := by
  simp only [← coe_unitPairing,map_pow,MonoidHom.pow_apply,d.unitPairing_pow,Units.val_one]

theorem symbol_pow_right (a c : (Kv)ˣ) : d.symbol v a (c^n) = 1 := by
  simp only [← coe_unitPairing,map_pow,d.unitPairing_pow,Units.val_one]

theorem symbol_one_right (a : (Kv)ˣ) : d.symbol v a 1 = 1 := by
  simp only [← coe_unitPairing,map_one,Units.val_one]

/-- {β, β} = {β, −1}, and {β, −1}² = 1. -/
theorem symbol_self (β : (Kv)ˣ) : d.symbol v β β = d.symbol v β (-1) ∧ d.symbol v β (-1) ^ 2 = 1 := by
  have h0 : d.symbol v β (-β) = 1 := by
    rw [← coe_unitPairing,d.unitPairing_neg_self v β,Units.val_one]
  have h2 : d.symbol v β (-1) ^ 2 = 1 := by
    rw [sq,← symbol_mul_right,neg_one_mul,neg_neg,symbol_one_right]
  refine ⟨?_,h2⟩
  rw [show -β = (-1) * β by simp,symbol_mul_right] at h0
  have h1 : d.symbol v β (-1) * d.symbol v β (-1) = 1 := by rw [← sq,h2]
  calc d.symbol v β β = d.symbol v β (-1) * (d.symbol v β (-1) * d.symbol v β β) := by
        rw [← mul_assoc,h1,one_mul]
    _ = _ := by rw [h0,mul_one]

/-- On the class β Kˣⁿ the symbol {x, c} is {β, c}. -/
theorem symbol_on_class {β x : (Kv)ˣ} (hx : ∃ u : (Kv)ˣ, x = β * u^n) (c : (Kv)ˣ) :
    d.symbol v x c = d.symbol v β c := by
  obtain ⟨u,rfl⟩ := hx
  rw [symbol_mul_left,symbol_pow_left,mul_one]

omit [NeZero n] in
theorem hat_const_mul (k : ℂ) (f : Kv → ℂ) (y : Kv) : d.hat v (fun x => k * f x) y = k * d.hat v f y := by
  unfold hat; simp_rw [mul_assoc]; rw [integral_const_mul]

variable {v} in
/-- On the support class the amplitude of the kernel is {β,−c} times the zero
extension of W(1/x)/|x|. -/
theorem kernelAmplitude_on_class {W : Weight v} {β : (Kv)ˣ}
    (support : ∀ x, W x ≠ 0 → ∃ u : (Kv)ˣ, x = β * u ^ n) (c : (Kv)ˣ) :
    d.kernelAmplitude v W c = fun x => d.symbol v β (-c) * extWeight v (invWeight v W) x := by
  funext x
  by_cases hx : x = 0
  · simp [hx,kernelAmplitude,extWeight]
  have hk := d.kernelAmplitude_unit v W c (Units.mk0 x hx)
  simp only [Units.val_mk0] at hk
  rw [hk]
  simp only [extWeight,ne_eq,hx,not_false_eq_true,dite_true,invWeight,Units.val_mk0]
  by_cases h0 : W (Units.mk0 x hx)⁻¹ = 0
  · simp [h0]
  have hs := d.symbol_on_class v (support _ h0) (-c)
  rw [hs]; ring

/-- Proposition 10.8's kernel on the support class: H_c(t) = {β,−c} H(−tⁿ/c). -/
theorem kernelIntegral_on_class {W : Weight v} {β : (Kv)ˣ}
    (support : ∀ x, W x ≠ 0 → ∃ u : (Kv)ˣ, x = β * u ^ n) (c : (Kv)ˣ) (t : Kv) :
    d.kernelIntegral v W c t =
      d.symbol v β (-c) * d.hat v (extWeight v (invWeight v W)) (-(t^n)/c.val) := by
  rw [d.kernelIntegral_eq_hat,d.kernelAmplitude_on_class support c,hat_const_mul]

/-- The root-Fourier formula: W^∨(dμⁿ) = |n|^{-1/2} {β,−d} |μ| V̂_d(μ) with V_d(τ) = H(−τⁿ/d). -/
theorem dualWeight_on_powers {W : Weight v} {β : (Kv)ˣ}
    (support : ∀ x, W x ≠ 0 → ∃ u : (Kv)ˣ, x = β * u ^ n) (d0 μ' : (Kv)ˣ) :
    d.dualWeight v W (d0 * μ'^n) = (Real.sqrt (m (n : Kv)) : ℂ)⁻¹ * d.symbol v β (-d0) * (m μ'.val : ℂ) *
      d.hat v (fun τ => d.hat v (extWeight v (invWeight v W)) (-(τ^n)/d0.val)) μ'.val := by
  set H := d.hat v (extWeight v (invWeight v W))
  have hsym : d.symbol v β (-(d0 * μ'^n)) = d.symbol v β (-d0) := by
    rw [show -(d0 * μ'^n) = (-d0) * μ'^n by simp,symbol_mul_right,symbol_pow_right,mul_one]
  unfold dualWeight
  simp_rw [d.kernelIntegral_on_class v support,hsym]
  have hg := d.integral_local_mul v μ' (fun t => d.character.localValue F v t * H (-(t^n)/(d0*μ'^n).val))
  dsimp only at hg
  have hm : (m μ'.val : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (modulus_ne_zero v μ')
  have e : (∫ t, d.character.localValue F v t * (d.symbol v β (-d0) * H (-(t^n)/(d0*μ'^n).val)) ∂dx) =
      d.symbol v β (-d0) * (m μ'.val : ℂ) *
        ∫ x, d.character.localValue F v (μ'.val*x) * H (-((μ'.val*x)^n)/(d0*μ'^n).val) ∂dx := by
    rw [hg]
    simp_rw [mul_left_comm (d.character.localValue F v _) (d.symbol v β (-d0))]
    rw [integral_const_mul]
    field_simp
  rw [e]
  unfold hat
  have hx (x : Kv) : -((μ'.val*x)^n)/(d0*μ'^n).val = -(x^n)/d0.val := by
    have : (μ'.val)^n ≠ 0 := pow_ne_zero _ μ'.ne_zero
    simp only [Units.val_mul,Units.val_pow_eq_pow_val,mul_pow]
    field_simp
  simp_rw [hx]
  simp_rw [mul_comm (d.character.localValue F v _) (H _)]
  ring

theorem isOpen_powers : IsOpen ((powMonoidHom n : (Kv)ˣ →* (Kv)ˣ).range : Set (Kv)ˣ) := by
  cases v with
  | inl w =>
    let : NontriviallyNormedField w.Completion := { (inferInstance : NormedField w.Completion) with
      non_trivial := (archNontriviallyNormedCompletion w).non_trivial }
    let : CharZero w.Completion := charZero_of_injective_ringHom (algebraMap F w.Completion).injective
    exact isOpen_unit_powers (K := w.Completion) n (Nat.cast_ne_zero.mpr (NeZero.ne n))
  | inr p =>
    let := FinitePlace.nontriviallyNormedCompletion p
    let : CharZero (p.adicCompletion F) := charZero_of_injective_ringHom (diagonal F (.inr p)).injective
    exact isOpen_unit_powers (K := p.adicCompletion F) n (Nat.cast_ne_zero.mpr (NeZero.ne n))

variable (n) in
/-- The restriction of a weight to the class d Kˣⁿ. -/
def classInd (d0 : (Kv)ˣ) (f : Weight v) : Weight v := fun c => if ∃ u : (Kv)ˣ, c = d0 * u^n then f c else 0

omit [NeZero n] in
theorem classInd_translate (d0 : (Kv)ˣ) (f : Weight v) (c : (Kv)ˣ) :
    classInd n v d0 f (d0 * c) = if ∃ u : (Kv)ˣ, c = u^n then f (d0 * c) else 0 := by
  simp only [classInd,mul_right_inj]

/-- Integration over one class, through the n-th power map. -/
theorem lineIntegral_classInd (d0 : (Kv)ˣ) (f : Weight v) (hf : Measurable f) :
    d.lineIntegral v (classInd n v d0 f) = ((m (n : Kv) : ℂ) / (n : ℂ)) * ∫ u, f (d0 * u^n) ∂μ := by
  rw [← d.lineIntegral_mul v d0]
  simp_rw [classInd_translate]
  exact d.lineIntegral_on_powers v (fun a => f (d0 * a)) (hf.comp (measurable_const_mul d0))

/-- A weight whose pullback by d·(·)ⁿ is integrable is integrable on the class d Kˣⁿ. -/
theorem integrable_classInd (d0 : (Kv)ˣ) (f : Weight v) (hf : Measurable f)
    (hi : Integrable (fun u => f (d0 * u^n)) μ) : Integrable (classInd n v d0 f) μ := by
  let : SecondCountableTopology (Kv)ˣ := Units.isEmbedding_val₀.secondCountableTopology
  let H := (powMonoidHom n : (Kv)ˣ →* (Kv)ˣ).range
  let g := fun a => f (d0 * a)
  have hg : Measurable g := hf.comp (measurable_const_mul d0)
  have hpow : Measurable (fun x : (Kv)ˣ => x^n) := (continuous_id.pow n).measurable
  have h1 : Integrable g ((μ).map (fun x : (Kv)ˣ => x^n)) :=
    (integrable_map_measure hg.aestronglyMeasurable hpow.aemeasurable).mpr hi
  rw [d.map_lineMeasure_pow v] at h1
  have hp : 0 < (n : ℝ) / m (n : Kv) := by
    have hnz := (diagonal F v).injective.ne (Nat.cast_ne_zero.mpr (NeZero.ne n) : (n:F) ≠ 0)
    have hn : (n : Kv) ≠ 0 := by simpa only [map_natCast,map_zero] using hnz
    have : 0 < m (n : Kv) := by cases v <;> simp [modulus,norm_pos_iff,hn,pow_pos (norm_pos_iff.mpr hn)]
    exact div_pos (Nat.cast_pos.mpr (NeZero.pos n)) this
  have h2 : IntegrableOn g H μ := by
    have h1' : Integrable g ((((n : ℝ) / m (n : Kv)).toNNReal : ENNReal) • (μ).restrict (H : Set (Kv)ˣ)) := h1
    rwa [integrable_smul_measure (by simpa using hp) ENNReal.coe_ne_top] at h1'
  have hH : MeasurableSet (H : Set (Kv)ˣ) := (isOpen_powers v).measurableSet
  have h3 := ((integrable_indicator_iff hH).mpr h2).comp_mul_left d0⁻¹
  refine h3.congr (Eventually.of_forall fun c => ?_)
  simp only [classInd,indicator,g,mul_inv_cancel_left]
  congr 1
  apply propext
  constructor
  · rintro ⟨u,hu⟩; exact ⟨u,by rw [show u^n = d0⁻¹*c from hu]; simp⟩
  · rintro ⟨u,hu⟩; exact ⟨u,by simp [hu]⟩

omit [NeZero n] in
theorem mem_class_iff (d0 c : (Kv)ˣ) :
    (∃ u : (Kv)ˣ, c = d0 * u^n) ↔ (QuotientGroup.mk c : PowerClass n v) = QuotientGroup.mk d0 := by
  rw [QuotientGroup.eq]
  constructor
  · rintro ⟨u,rfl⟩
    exact ⟨u⁻¹,by simp [mul_comm]⟩
  · rintro ⟨u,hu⟩
    refine ⟨u⁻¹,?_⟩
    have hu' : u^n = c⁻¹ * d0 := hu
    rw [inv_pow,hu']; group

/-- A finite decomposition of a zeta integral over the power classes, indexed through an
equivalence of the class group. -/
theorem integral_sum_classes (r : PowerClass n v → (Kv)ˣ) (e : PowerClass n v ≃ PowerClass n v)
    (hr : ∀ C, (QuotientGroup.mk (r C) : PowerClass n v) = e C) (f : Weight v)
    (hi : ∀ C, Integrable (classInd n v (r C) f) μ) :
    let : Fintype (PowerClass n v) := @Fintype.ofFinite _ (finite_power_classes v)
    ∫ c, f c ∂μ = ∑ C, ∫ c, classInd n v (r C) f c ∂μ := by
  intro _
  rw [← integral_finsetSum _ (fun C _ => hi C)]
  congr 1; funext c
  simp only [classInd,mem_class_iff,hr]
  rw [Equiv.sum_comp e (fun C => if (QuotientGroup.mk c : PowerClass n v) = C then f c else 0)]
  simp

theorem continuous_dualWeight {W : Weight v} (hw : TestWeight v W) : Continuous (d.dualWeight v W) := by
  obtain ⟨β',hβ'⟩ := d.exists_jacquetLift_auxiliary v
  have h := d.jacquetLift_dual v hw hβ'
  dsimp only at h
  rw [← h]
  exact d.continuous_jacquet v _

omit [NeZero n] in
theorem cpow_modulus_pow (u : (Kv)ˣ) (k : ℕ) (w : ℂ) :
    ((m (u^k).val : ℝ) : ℂ)^w = ((m u.val : ℝ) : ℂ)^((k:ℂ)*w) := by
  have hm : 0 < m u.val := by cases v <;> simp [modulus,u.ne_zero,pow_pos]
  have hp : m (u^k).val = m u.val ^ k := by
    rw [Units.val_pow_eq_pow_val]; cases v <;> simp [modulus,norm_pow,← pow_mul,mul_comm]
  rw [hp,Complex.cpow_def_of_ne_zero (by exact_mod_cast (pow_pos hm k).ne'),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hm.ne'),← Complex.ofReal_log (pow_pos hm k).le,
    ← Complex.ofReal_log hm.le,Real.log_pow]
  push_cast; ring_nf

omit [NeZero n] in
theorem cpow_modulus_mul (a b : (Kv)ˣ) (w : ℂ) :
    ((m (a*b).val : ℝ) : ℂ)^w = ((m a.val : ℝ) : ℂ)^w * ((m b.val : ℝ) : ℂ)^w := by
  rw [Units.val_mul,modulus_mul,Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (modulus_nonneg' v _) (modulus_nonneg' v _)]

omit [NeZero n] in
theorem modulus_neg (a : Kv) : m (-a) = m a := by cases v <;> simp [modulus]

theorem symbol_inv_right (a b : (Kv)ˣ) : d.symbol v a b⁻¹ = (d.symbol v a b)⁻¹ := by
  simp only [← coe_unitPairing,map_inv,Units.val_inv_eq_inv_val]

theorem symbol_ne_zero (a b : (Kv)ˣ) : d.symbol v a b ≠ 0 := by
  intro h; have := d.norm_symbol v a b; simp [h] at this

/-- The contribution of one class d Kˣⁿ to Z(W^∨, ω, s), after Tate's equation for ω⁻ⁿ. -/
theorem class_identity {W : Weight v} (hw : TestWeight v W) {β : (Kv)ˣ}
    (support : ∀ x, W x ≠ 0 → ∃ u : (Kv)ˣ, x = β * u ^ n)
    (ω : (Kv)ˣ →* Circle) (hω : Continuous ω) {s : ℂ}
    (lo : -(1/(n : ℝ)) < s.re) (hi : s.re < 0) (γ₁ : ℂ)
    (hγ : ∀ G : Kv → ℂ, Bruhat v G →
      d.mellin v (fun y => d.hat v G y.val) (fun x => (((ω x : ℂ)^n)⁻¹)⁻¹) (1-(-(n : ℂ)*s)) =
        γ₁ * d.mellin v (fun u => G u.val) (fun x => ((ω x : ℂ)^n)⁻¹) (-(n : ℂ)*s))
    (d0 : (Kv)ˣ) :
    let H := d.hat v (extWeight v (invWeight v W))
    let Fw : Weight v := fun c => d.dualWeight v W c * (ω c : ℂ) * ((m c.val : ℝ) : ℂ)^s
    let G : Weight v := fun y => H y.val * ((ω y : ℂ) * d.symbol v β y)⁻¹ * ((m y.val : ℝ) : ℂ)^(-s)
    Integrable (classInd n v d0 Fw) μ ∧
      ∫ c, classInd n v d0 Fw c ∂μ =
        (Real.sqrt (m (n : Kv)) : ℂ)⁻¹ * ((ω (-1) : ℂ))⁻¹ * γ₁ * ∫ y, classInd n v (-d0)⁻¹ G y ∂μ := by
  intro H Fw G
  have hHb : Bruhat v H := d.hat_bruhat v (d.extWeight_bruhat v (testWeight_invWeight v hw))
  have hHc : Continuous H := (d.bruhat_bound v hHb).1
  have hωc : Continuous fun x => (ω x : ℂ) := continuous_subtype_val.comp hω
  have hω0 (x : (Kv)ˣ) : (ω x : ℂ) ≠ 0 := Circle.coe_ne_zero _
  have hs0 := d.symbol_ne_zero v β (-d0)
  let V := fun τ : Kv => H (-(τ^n)/d0.val)
  have hV : Bruhat v V := by
    have e : V = fun t => (d.symbol v β (-d0))⁻¹ * d.kernelIntegral v W d0 t := by
      funext t; rw [d.kernelIntegral_on_class v support,← mul_assoc,inv_mul_cancel₀ hs0,one_mul]
    rw [e]; exact Bruhat.const_mul v (d.kernelIntegral_bruhat v hw d0) _
  have hmu (u : (Kv)ˣ) : ((m u.val : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (modulus_ne_zero v u)
  let K := (Real.sqrt (m (n : Kv)) : ℂ)⁻¹ * d.symbol v β (-d0) * (ω d0 : ℂ) * ((m d0.val : ℝ) : ℂ)^s
  have hpt (u : (Kv)ˣ) : Fw (d0 * u^n) =
      K * (d.hat v V u.val * (((ω u : ℂ)^n)⁻¹)⁻¹ * ((m u.val : ℝ) : ℂ)^(1-(-(n : ℂ)*s))) := by
    simp only [Fw]
    rw [d.dualWeight_on_powers v support d0 u,cpow_modulus_mul,cpow_modulus_pow,map_mul,map_pow,
      Circle.coe_mul,Circle.coe_pow,inv_inv]
    have e1 : ((m u.val : ℝ) : ℂ)^(1-(-(n : ℂ)*s)) = (m u.val : ℂ) * ((m u.val : ℝ) : ℂ)^((n : ℂ)*s) := by
      rw [show 1-(-(n : ℂ)*s) = 1 + (n : ℂ)*s by ring,Complex.cpow_add _ _ (hmu u),Complex.cpow_one]
    rw [e1]; simp only [K,V]; ring
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
  have hre : (1-(-(n : ℂ)*s)).re = 1 + n * s.re := by simp
  have hns : -1 < (n : ℝ) * s.re := by
    have := mul_lt_mul_of_pos_left lo hn0
    rwa [show (n : ℝ) * -(1/(n : ℝ)) = -1 by field_simp] at this
  have hint : Integrable (fun u => Fw (d0 * u^n)) μ := by
    simp_rw [hpt]
    refine Integrable.const_mul ?_ K
    refine d.integrable_mellin_bruhat v (d.hat_bruhat v hV) (χ := fun x => (((ω x : ℂ)^n)⁻¹)⁻¹) ?_ ?_ ?_ ?_
    · simp only [inv_inv]; exact hωc.pow n
    · intro x; simp
    · rw [hre]; linarith
    · rw [hre]; nlinarith
  have hFm : Measurable Fw :=
    (((d.continuous_dualWeight v hw).mul hωc).mul (continuous_cpow_modulus v s)).measurable
  refine ⟨d.integrable_classInd v d0 Fw hFm hint,?_⟩
  have hmn : 0 < m (n : Kv) := by
    have hnz := (diagonal F v).injective.ne (Nat.cast_ne_zero.mpr (NeZero.ne n) : (n:F) ≠ 0)
    have hn : (n : Kv) ≠ 0 := by simpa only [map_natCast,map_zero] using hnz
    cases v <;> simp [modulus,norm_pos_iff,hn,pow_pos (norm_pos_iff.mpr hn)]
  have hmn' : (m (n : Kv) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hmn.ne'
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  -- the second zeta integral, back on the class
  let g' : Weight v := fun a => H (-a.val/d0.val) * (ω a : ℂ)⁻¹ * ((m a.val : ℝ) : ℂ)^(-s)
  have hg'm : Measurable g' :=
    (((hHc.comp ((Units.continuous_val.neg).div_const _)).mul (hωc.inv₀ hω0)).mul
      (continuous_cpow_modulus v (-s))).measurable
  let c₀ := (d.symbol v β (-d0))⁻¹ * ((ω (-d0) : ℂ))⁻¹ * ((m d0.val : ℝ) : ℂ)^(-s)
  have hM2 : d.mellin v (fun u => V u.val) (fun x => ((ω x : ℂ)^n)⁻¹) (-(n : ℂ)*s) =
      ((n : ℂ) / (m (n : Kv) : ℂ)) * (c₀ * ∫ y, classInd n v (-d0)⁻¹ G y ∂μ) := by
    have e1 : d.mellin v (fun u => V u.val) (fun x => ((ω x : ℂ)^n)⁻¹) (-(n : ℂ)*s) =
        ∫ u, g' (u^n) ∂μ := by
      rw [mellin_eq_integral]
      congr 1; funext u
      simp only [g',V]
      rw [cpow_modulus_pow,map_pow,Circle.coe_pow,Units.val_pow_eq_pow_val,show (n:ℂ) * -s = -(n:ℂ)*s by ring]
    have e2 := d.lineIntegral_on_powers v g' hg'm
    have e3 : d.lineIntegral v (fun a => if ∃ u : (Kv)ˣ, a = u^n then g' a else 0) =
        c₀ * ∫ y, classInd n v (-d0)⁻¹ G y ∂μ := by
      rw [← d.lineIntegral_mul v (-d0),d.integral_lineMeasure,← d.lineIntegral_const_mul]
      congr 1; funext y
      have hc : (∃ u : (Kv)ˣ, -d0 * y = u^n) ↔ ∃ u : (Kv)ˣ, y = (-d0)⁻¹ * u^n :=
        exists_congr fun u => eq_inv_mul_iff_mul_eq.symm
      simp only [classInd,hc]
      split_ifs with h
      · obtain ⟨u,hu⟩ := h
        have hsy : d.symbol v β y = (d.symbol v β (-d0))⁻¹ := by
          rw [hu,symbol_mul_right,symbol_pow_right,mul_one,symbol_inv_right]
        have hy : -(-d0 * y).val / d0.val = y.val := by
          simp only [Units.val_mul,Units.val_neg]; field_simp [d0.ne_zero]
        simp only [g',G,c₀,hy,hsy,map_mul,Circle.coe_mul,cpow_modulus_mul]
        rw [show ((-d0 : (Kv)ˣ)).val = -d0.val from Units.val_neg d0]
        rw [show ((m (-d0.val) : ℝ) : ℂ) = (m d0.val : ℂ) by rw [modulus_neg]]
        field_simp
      · simp
    rw [e1]
    rw [e3] at e2
    rw [e2]
    field_simp
  have hω1 : (ω (-d0) : ℂ) = (ω (-1) : ℂ) * (ω d0 : ℂ) := by
    rw [show (-d0 : (Kv)ˣ) = (-1) * d0 by simp,map_mul,Circle.coe_mul]
  have hcp : ((m d0.val : ℝ) : ℂ)^s ≠ 0 := by
    rw [Ne,Complex.cpow_eq_zero_iff]; exact fun h => hmu d0 h.1
  calc ∫ c, classInd n v d0 Fw c ∂μ = d.lineIntegral v (classInd n v d0 Fw) := d.integral_lineMeasure v _
    _ = ((m (n : Kv) : ℂ) / (n : ℂ)) * ∫ u, Fw (d0 * u^n) ∂μ := d.lineIntegral_classInd v d0 Fw hFm
    _ = ((m (n : Kv) : ℂ) / (n : ℂ)) * (K * d.mellin v (fun y => d.hat v V y.val)
          (fun x => (((ω x : ℂ)^n)⁻¹)⁻¹) (1-(-(n : ℂ)*s))) := by
        simp_rw [hpt]; rw [integral_const_mul,mellin_eq_integral]
    _ = ((m (n : Kv) : ℂ) / (n : ℂ)) * (K * (γ₁ * d.mellin v (fun u => V u.val)
          (fun x => ((ω x : ℂ)^n)⁻¹) (-(n : ℂ)*s))) := by rw [hγ V hV]
    _ = _ := by
        rw [hM2]
        simp only [K,c₀,hω1,Complex.cpow_neg]
        field_simp

theorem integrable_classInd_of_integrable (d0 : (Kv)ˣ) {f : Weight v} (hf : Integrable f μ) :
    Integrable (classInd n v d0 f) μ := by
  let S := (fun c : (Kv)ˣ => d0⁻¹ * c) ⁻¹' ((powMonoidHom n : (Kv)ˣ →* (Kv)ˣ).range : Set (Kv)ˣ)
  have hS : MeasurableSet S := (measurable_const_mul d0⁻¹) (isOpen_powers v).measurableSet
  have e : classInd n v d0 f = S.indicator f := by
    funext c
    simp only [classInd,indicator,S,mem_preimage,SetLike.mem_coe,MonoidHom.mem_range,powMonoidHom_apply]
    congr 1
    apply propext
    constructor
    · rintro ⟨u,rfl⟩; exact ⟨u,by simp⟩
    · rintro ⟨u,hu⟩; exact ⟨u,by rw [hu]; simp⟩
  rw [e]; exact hf.indicator hS

theorem zeta_dualWeight (W : Weight v) (hw : TestWeight v W) (β : (LocalField F v)ˣ)
    (support : ∀ x, W x ≠ 0 → ∃ u : (LocalField F v)ˣ, x = β * u ^ n)
    (ω : (LocalField F v)ˣ →* Circle) (hω : Continuous ω) (s : ℂ)
    (lo : -(1/(n : ℝ)) < s.re) (hi : s.re < 0) :
    let η : Weight v := fun x => (ω x : ℂ) * d.symbol v β x
    ∃ γ₁ γ₂ : ℂ, d.TateEquation v (fun x => ((ω x : ℂ)^n)⁻¹) (-(n : ℂ)*s) γ₁ ∧
      d.TateEquation v η (1+s) γ₂ ∧
      d.mellin v (d.dualWeight v W) (fun x => ω x) s =
        (Real.sqrt (modulus F v (n : LocalField F v)) : ℂ)⁻¹ * η (-1) * γ₁ * γ₂ *
          d.mellin v W (fun x => (ω x : ℂ)⁻¹) (-s) := by
  intro η
  have hωc : Continuous fun x => (ω x : ℂ) := continuous_subtype_val.comp hω
  have hω0 (x : (Kv)ˣ) : (ω x : ℂ) ≠ 0 := Circle.coe_ne_zero _
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
  have hns : -1 < (n : ℝ) * s.re := by
    have := mul_lt_mul_of_pos_left lo hn0
    rwa [show (n : ℝ) * -(1/(n : ℝ)) = -1 by field_simp] at this
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast NeZero.one_le
  -- the two Tate constants
  obtain ⟨γ₁,T1,B1⟩ := d.exists_tateEquation v (fun x => ((ω x : ℂ)^n)⁻¹)
    (fun x y => by simp only [map_mul,Circle.coe_mul,mul_pow,mul_inv]) ((hωc.pow n).inv₀ fun x => pow_ne_zero _ (hω0 x))
    (fun x => by simp) (z := -(n : ℂ)*s) (by simp; nlinarith) (by simp; nlinarith)
  obtain ⟨γ₂,T2,B2⟩ := d.exists_tateEquation v η
    (fun x y => by simp only [η,map_mul,Circle.coe_mul,symbol_mul_right]; ring)
    (hωc.mul ((d.continuous_symbol v).comp (continuous_const.prodMk continuous_id)))
    (fun x => by simp [η,d.norm_symbol]) (z := 1+s) (by simp; nlinarith) (by simp; linarith)
  refine ⟨γ₁,γ₂,T1,T2,?_⟩
  let : Fintype (PowerClass n v) := @Fintype.ofFinite _ (finite_power_classes v)
  let Hh := d.hat v (extWeight v (invWeight v W))
  have hHb : Bruhat v Hh := d.hat_bruhat v (d.extWeight_bruhat v (testWeight_invWeight v hw))
  let Fw : Weight v := fun c => d.dualWeight v W c * (ω c : ℂ) * ((m c.val : ℝ) : ℂ)^s
  let G : Weight v := fun y => Hh y.val * ((ω y : ℂ) * d.symbol v β y)⁻¹ * ((m y.val : ℝ) : ℂ)^(-s)
  have CI := fun d0 => d.class_identity v hw support ω hω lo hi γ₁ B1 d0
  have hη0 (x : (Kv)ˣ) : η x ≠ 0 := mul_ne_zero (hω0 x) (d.symbol_ne_zero v β x)
  have hηc : Continuous η := hωc.mul ((d.continuous_symbol v).comp (continuous_const.prodMk continuous_id))
  have hG : Integrable G μ :=
    d.integrable_mellin_bruhat v hHb (χ := fun y => (η y)⁻¹) (hηc.inv₀ hη0) (fun x => by simp [η,d.norm_symbol])
      (by simp; linarith) (by simp; nlinarith)
  let e : PowerClass n v ≃ PowerClass n v :=
    (Equiv.mulLeft (QuotientGroup.mk (-1) : PowerClass n v)).trans (Equiv.inv _)
  have hr (C : PowerClass n v) : (QuotientGroup.mk (-C.out)⁻¹ : PowerClass n v) = e C := by
    simp only [e,Equiv.trans_apply,Equiv.coe_mulLeft,Equiv.inv_apply]
    rw [QuotientGroup.mk_inv,show -C.out = (-1) * C.out by simp,QuotientGroup.mk_mul,QuotientGroup.out_eq']
  have step8 : d.mellin v (fun u => extWeight v (invWeight v W) u.val) η (1+s) =
      d.symbol v β (-1) * d.mellin v W (fun x => (ω x : ℂ)⁻¹) (-s) := by
    unfold mellin
    rw [← d.lineIntegral_const_mul]
    have e1 : (fun u : (Kv)ˣ => extWeight v (invWeight v W) u.val * η u * ((m u.val : ℝ) : ℂ)^(1+s)) =
        fun u => (fun u => W u * η u⁻¹ * ((m u⁻¹.val : ℝ) : ℂ)^s) u⁻¹ := by
      funext u
      have hm : ((m u.val : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (modulus_ne_zero v u)
      simp only [extWeight_unit,invWeight,inv_inv]
      rw [Complex.cpow_add _ _ hm,Complex.cpow_one]
      field_simp
    rw [e1]
    refine (d.lineIntegral_inv v (fun u => W u * η u⁻¹ * ((m u⁻¹.val : ℝ) : ℂ)^s)).trans ?_
    congr 1; funext u
    by_cases h0 : W u = 0
    · simp [h0]
    obtain ⟨t,ht⟩ := support u h0
    have hsu : d.symbol v β u = d.symbol v β (-1) := by
      rw [ht,symbol_mul_right,symbol_pow_right,mul_one,(d.symbol_self v β).1]
    have hsq := (d.symbol_self v β).2
    have hsi : (d.symbol v β (-1))⁻¹ = d.symbol v β (-1) := by
      exact inv_eq_of_mul_eq_one_right (by rw [← sq,hsq])
    have hmi : ((m u⁻¹.val : ℝ) : ℂ)^s = ((m u.val : ℝ) : ℂ)^(-s) := by
      have := cpow_modulus_mul v u u⁻¹ s
      rw [mul_inv_cancel,Units.val_one] at this
      have h1 : m (1 : Kv) = 1 := by cases v <;> simp [modulus]
      rw [h1,Complex.ofReal_one,Complex.one_cpow] at this
      rw [Complex.cpow_neg]; exact eq_inv_of_mul_eq_one_right this.symm
    simp only [η,map_inv,Circle.coe_inv,symbol_inv_right,hsu,hmi]
    rw [hsi]; ring
  have step7 : d.mellin v (fun y => Hh y.val) (fun x => (η x)⁻¹) (-s) =
      γ₂ * d.mellin v (fun u => extWeight v (invWeight v W) u.val) η (1+s) := by
    have := B2 (extWeight v (invWeight v W)) (d.extWeight_bruhat v (testWeight_invWeight v hw))
    rwa [show 1 - (1+s) = -s by ring] at this
  have hω2 : ((ω (-1) : ℂ))⁻¹ = (ω (-1) : ℂ) := by
    apply inv_eq_of_mul_eq_one_right
    rw [← Circle.coe_mul,← map_mul,neg_one_mul,neg_neg,map_one,Circle.coe_one]
  calc d.mellin v (d.dualWeight v W) (fun x => ω x) s = ∫ c, Fw c ∂μ := mellin_eq_integral ..
    _ = ∑ C : PowerClass n v, ∫ c, classInd n v C.out Fw c ∂μ :=
        d.integral_sum_classes v (fun C => C.out) (Equiv.refl _) (fun C => QuotientGroup.out_eq' C) Fw
          (fun C => (CI C.out).1)
    _ = ∑ C : PowerClass n v, (Real.sqrt (m (n : Kv)) : ℂ)⁻¹ * ((ω (-1) : ℂ))⁻¹ * γ₁ *
          ∫ y, classInd n v (-C.out)⁻¹ G y ∂μ := Finset.sum_congr rfl fun C _ => (CI C.out).2
    _ = (Real.sqrt (m (n : Kv)) : ℂ)⁻¹ * ((ω (-1) : ℂ))⁻¹ * γ₁ * ∫ y, G y ∂μ := by
        rw [← Finset.mul_sum,d.integral_sum_classes v (fun C => (-C.out)⁻¹) e hr G
          (fun C => d.integrable_classInd_of_integrable v _ hG)]
    _ = (Real.sqrt (m (n : Kv)) : ℂ)⁻¹ * ((ω (-1) : ℂ))⁻¹ * γ₁ *
          d.mellin v (fun y => Hh y.val) (fun x => (η x)⁻¹) (-s) := by rw [mellin_eq_integral]
    _ = _ := by
        rw [step7,step8,hω2]
        simp only [η]
        ring

end MetaplecticPoisson.Datum
