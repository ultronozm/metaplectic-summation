import MetaplecticSummation.Gauss.Setup
import MetaplecticSummation.MultiplicativeMeasure

/-! Character Gauss integrals on the unit group of a finite completion. -/

noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField MeasureTheory CompactlySupported
open scoped ComplexConjugate
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

def unitGauss (p : Prime F) (θ : Weight (.inr p : Place F)) (α : LocalField F (.inr p)) :=
  d.lineIntegral (.inr p) fun x => if ‖(x : LocalField F (.inr p))‖ = 1 then
    θ x * d.character.localValue F (.inr p) (α*x) else 0

theorem charWeight_unit_mul {p : Prime F} (χ : UnitChar p) (u : integralUnits p)
    (x : (LocalField F (.inr p))ˣ) :
    charWeight χ (u.val*x) = (χ u : ℂ) * charWeight χ x := by
  by_cases hx : x ∈ integralUnits p
  · have hux := (integralUnits p).mul_mem u.property hx
    simp only [charWeight,dif_pos hux,dif_pos hx]
    exact (congrArg ((↑) : Circle → ℂ) (χ.map_mul u ⟨x,hx⟩)).trans (Circle.coe_mul _ _)
  · have hux : u.val*x ∉ integralUnits p := fun hm => hx
           (((integralUnits p).mul_mem_cancel_left u.property).mp hm)
    simp only [charWeight,dif_neg hx,dif_neg hux,mul_zero]

omit [NeZero n] in
/-- Multiplication of the Gauss frequency by a local unit contributes the
inverse value of the character. -/
theorem unitGauss_unit_mul (p : Prime F) (χ : UnitChar p) (u : integralUnits p)
    (α : LocalField F (.inr p)) :
    d.unitGauss p (charWeight χ) (u.val.val*α) = conj (χ u : ℂ) * d.unitGauss p (charWeight χ) α := by
  let v : Place F := .inr p
  let g := fun x : (LocalField F v)ˣ => if ‖x.val‖ = 1 then
    charWeight χ x * d.character.localValue F v ((u.val.val*α)*x.val) else 0
  have hu : ‖u.val.val‖ = 1 := u.property
  change d.lineIntegral v g = _
  rw [← d.lineIntegral_mul v u.val⁻¹ g]
  unfold unitGauss
  rw [← d.lineIntegral_const_mul]
  congr 1
  funext x
  have hnorm : ‖(u.val⁻¹*x).val‖ = ‖x.val‖ := by
    rw [Units.val_mul,Units.val_inv_eq_inv_val,norm_mul,norm_inv,hu,inv_one,one_mul]
  have phase : u.val.val*α*(u.val⁻¹*x).val = α*x.val := by
    rw [Units.val_mul,Units.val_inv_eq_inv_val]
    field_simp
  have char := charWeight_unit_mul χ u⁻¹ x
  simpa only [Subgroup.coe_inv, map_inv, Circle.coe_inv_eq_conj] using
    (show g (u.val⁻¹*x) = ((χ u⁻¹ : Circle) : ℂ) *
      (if ‖x.val‖ = 1 then charWeight χ x * d.character.localValue F v (α*x.val) else 0) by
      simp only [g,hnorm,phase,Subgroup.coe_inv] at char ⊢
      split_ifs <;> simp only [char,mul_assoc,mul_zero])

omit [NeZero n] in
/-- On the unit sphere the multiplicative measure agrees with the additive
measure used for the Gauss integral in the paper. -/
theorem unitGauss_additive (p : Prime F) (θ : Weight (.inr p : Place F)) (α : LocalField F (.inr p)) :
    d.unitGauss p θ α = ∫ y, (if hy : y ≠ 0 then
      (if ‖y‖ = 1 then θ (Units.mk0 y hy) * d.character.localValue F (.inr p) (α*y) else 0) else 0)
      ∂selfDual F d.character (.inr p) := by
  unfold unitGauss lineIntegral
  apply integral_congr_ae
  filter_upwards with y
  by_cases hy : y = 0
  · simp [hy]
  · simp only [dif_pos hy,Units.val_mk0,modulus]
    by_cases hu : ‖y‖ = 1 <;> simp [hu]

omit [NeZero n] in
/-- A nontrivial character value on a unit fixing the additive phase forces
the Gauss integral to vanish. -/
theorem unitGauss_zero_of_unit (p : Prime F) (hψ : d.UnramifiedAt (.inr p))
    (χ : UnitChar p) (α : LocalField F (.inr p)) (u : integralUnits p)
    (hu : χ u ≠ 1) (hphase : ‖(u.val.val-1)*α‖ ≤ 1) :
    d.unitGauss p (charWeight χ) α = 0 := by
  let v : Place F := .inr p
  have same : d.unitGauss p (charWeight χ) (u.val.val*α) = d.unitGauss p (charWeight χ) α := by
    unfold unitGauss
    congr 1
    funext x
    split_ifs with hx
    · have hp := (hψ ((u.val.val-1)*α)).mpr hphase x.val hx.le
      rw [show u.val.val*α*x.val = (u.val.val-1)*α*x.val + α*x.val by ring,
        d.character.localValue_add, hp,one_mul]
    · rfl
  rw [d.unitGauss_unit_mul] at same
  have hne : conj (χ u : ℂ) ≠ 1 := by
    intro hz
    apply hu
    apply Subtype.ext
    simpa using congrArg (starRingEnd ℂ) hz
  by_contra hn
  exact hne ((mul_eq_right₀ hn).mp same)

omit [NeZero n] in
/-- Below the conductor shell, a principal unit fixes the additive phase
and detects the character. Level zero tests the whole unit group. -/
theorem unitGauss_zero_below_conductor (p : Prime F) (hψ : d.UnramifiedAt (.inr p))
    (χ : UnitChar p) {e k : ℕ} (cond : IsLeast {j | trivialAtLevel χ j} e)
    (hk : k < e) (α : LocalField F (.inr p)) (hα : ‖α‖ ≤ (p.asIdeal.absNorm : ℝ)^k) :
    d.unitGauss p (charWeight χ) α = 0 := by
  letI : IsUltrametricDist (LocalField F (.inr p)) := inferInstanceAs (IsUltrametricDist (p.adicCompletion F))
  let q : ℝ := p.asIdeal.absNorm
  have hq : 0 < q := by dsimp [q]; exact_mod_cast (Nat.zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm p))
  have hnt : ¬ trivialAtLevel χ k := fun he => hk.not_ge (cond.2 he)
  unfold trivialAtLevel at hnt
  push Not at hnt
  obtain ⟨u,hlevel,hu⟩ := hnt
  apply d.unitGauss_zero_of_unit p hψ χ α u hu
  have hd : ‖u.val.val-1‖ ≤ (q^k)⁻¹ := by
    rcases hlevel with rfl | hd
    · have hum : ‖u.val.val‖ = 1 := u.property
      simpa [sub_eq_add_neg,hum] using (IsUltrametricDist.norm_add_le_max u.val.val (-1))
    · exact hd
  rw [norm_mul]
  exact (mul_le_mul hd hα (norm_nonneg _) (inv_nonneg.mpr (pow_nonneg hq.le k))).trans_eq
    (inv_mul_cancel₀ (pow_ne_zero k hq.ne'))

def unitCharField {p : Prime F} (χ : UnitChar p) (y : LocalField F (.inr p)) : ℂ :=
  if hy : y ≠ 0 then charWeight χ (Units.mk0 y hy) else 0

omit [NeZero n] in
theorem unitGauss_hat (p : Prime F) (χ : UnitChar p) (α : LocalField F (.inr p)) :
    d.unitGauss p (charWeight χ) α = d.hat (.inr p) (unitCharField χ) α := by
  rw [d.unitGauss_additive]
  unfold hat
  apply integral_congr_ae
  filter_upwards with y
  by_cases hy : y = 0
  · simp [unitCharField,hy]
  · by_cases hu : ‖y‖ = 1
    · simp [unitCharField,hy,hu,mul_comm]
    · have hn : Units.mk0 y hy ∉ integralUnits p := hu
      simp [unitCharField,hy,hu,charWeight,hn]

private theorem unitCharField_period {p : Prime F} (χ : UnitChar p) {e : ℕ} (he : 0 < e)
    (hc : trivialAtLevel χ e) (z : LocalField F (.inr p))
    (hz : ‖z‖ ≤ ((p.asIdeal.absNorm : ℝ)^e)⁻¹) (x : LocalField F (.inr p)) :
    unitCharField χ (x+z) = unitCharField χ x := by
  letI : IsUltrametricDist (LocalField F (.inr p)) := inferInstanceAs (IsUltrametricDist (p.adicCompletion F))
  let q : ℝ := p.asIdeal.absNorm
  have hq : 1 < (p.asIdeal.absNorm : ℝ) := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm p
  have hz1 := hz.trans_lt (inv_lt_one_of_one_lt₀ (one_lt_pow₀ hq he.ne'))
  have stays (a b : LocalField F (.inr p)) (ha : ‖a‖ = 1) (hb : ‖b‖ < 1) : ‖a+b‖ = 1 := by
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ha ▸ hb.ne'), ha, max_eq_left hb.le]
  have zero (y : LocalField F (.inr p)) (hy : ‖y‖ ≠ 1) : unitCharField χ y = 0 := by
    unfold unitCharField
    split_ifs with hn
    · exact dif_neg (show Units.mk0 y hn ∉ integralUnits p from hy)
    · rfl
  by_cases hx : ‖x‖ = 1
  · have hsum := stays x z hx hz1
    have hn : x ≠ 0 := fun h => by simp [h] at hx
    have hsn : x+z ≠ 0 := fun h => by simp [h] at hsum
    let X := Units.mk0 x hn
    let Y := Units.mk0 (x+z) hsn
    let u : integralUnits p := ⟨Y/X,by change ‖(x+z)/x‖ = 1; rw [norm_div,hsum,hx,div_one]⟩
    have hu : χ u = 1 := by
      apply hc u (Or.inr ?_)
      change ‖(x+z)/x-1‖ ≤ _
      rw [show (x+z)/x-1 = z/x by field_simp; ring, norm_div,hx,div_one]
      exact hz
    have hval : u.val*X = Y := div_mul_cancel _ _
    simpa only [hval,hu,Circle.coe_one,one_mul,unitCharField,dif_pos hsn,dif_pos hn,X,Y] using
      charWeight_unit_mul χ u X
  · have hy : ‖x+z‖ ≠ 1 := fun h => hx (by simpa using stays (x+z) (-z) h (by simpa using hz1))
    rw [zero _ hy,zero _ hx]

omit [NeZero n] in
/-- Above the conductor shell, an additive period of the extended character
acts nontrivially on the Fourier phase. -/
theorem unitGauss_zero_above_conductor (p : Prime F) (hψ : d.UnramifiedAt (.inr p))
    (χ : UnitChar p) {e : ℕ} (he : 0 < e) (hc : trivialAtLevel χ e)
    (α : LocalField F (.inr p)) (hα : (p.asIdeal.absNorm : ℝ)^e < ‖α‖) :
    d.unitGauss p (charWeight χ) α = 0 := by
  let v : Place F := .inr p
  let dx := selfDual F d.character v
  letI : dx.IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  let q : ℝ := p.asIdeal.absNorm
  have hq : 0 < (p.asIdeal.absNorm : ℝ) := by exact_mod_cast (Nat.zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm p))
  obtain ⟨π,hπ⟩ : ∃ π : (LocalField F (.inr p))ˣ, ‖π.val‖ = q⁻¹ := FinitePlace.exists_norm_uniformizer p
  have hπe : ‖π.val^e‖ = (q^e)⁻¹ := by rw [norm_pow,hπ,inv_pow]
  have hlarge : ¬ ‖α*π.val^e‖ ≤ 1 := by
    rw [norm_mul,hπe,← div_eq_mul_inv,div_le_one (pow_pos hq e)]
    exact hα.not_ge
  have hn := (hψ (α*π.val^e)).not.mpr hlarge
  push Not at hn
  obtain ⟨y,hy,hyψ⟩ := hn
  let z := π.val^e*y
  have hz : ‖z‖ ≤ (q^e)⁻¹ := by
    rw [norm_mul,hπe]
    exact mul_le_of_le_one_right (inv_nonneg.mpr (pow_nonneg hq.le e)) hy
  have hphase : d.character.localValue F v (α*z) ≠ 1 := by simpa only [z,mul_assoc] using hyψ
  let g (t : LocalField F v) := unitCharField χ t * d.character.localValue F v (α*t)
  have period (x : LocalField F v) : g (x+z) = g x * d.character.localValue F v (α*z) := by
    simp only [g,unitCharField_period χ he hc z hz,mul_add,d.character.localValue_add,mul_assoc]
  have hi := integral_add_right_eq_self (μ := dx) g z
  simp_rw [period] at hi
  rw [integral_mul_const] at hi
  rw [d.unitGauss_hat]
  by_contra hn
  exact hphase ((mul_eq_left₀ hn).mp hi)

omit [NeZero n] in
/-- A ramified unit character has Gauss transform supported on the shell
of absolute value q to its conductor exponent. -/
theorem unitGauss_conductor_support (p : Prime F) (hψ : d.UnramifiedAt (.inr p))
    (χ : UnitChar p) {e : ℕ} (he : 0 < e) (cond : IsLeast {j | trivialAtLevel χ j} e)
    (α : LocalField F (.inr p)) (hoff : ‖α‖ ≠ (p.asIdeal.absNorm : ℝ)^e) :
    d.unitGauss p (charWeight χ) α = 0 := by
  rcases lt_or_gt_of_ne hoff with hlo | hhi
  · apply d.unitGauss_zero_below_conductor p hψ χ cond (Nat.sub_lt he (by decide : 0 < 1)) α
    have hq : 1 < (p.asIdeal.absNorm : ℝ) := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm p
    by_cases hz : α = 0
    · simp [hz,pow_nonneg (zero_le_one.trans hq.le)]
    obtain ⟨j,hj⟩ := norm_zpow_residue_card p (Units.mk0 α hz)
    change ‖α‖ = _ at hj
    rw [hj,← zpow_natCast] at hlo ⊢
    apply (zpow_le_zpow_iff_right₀ hq).mpr
    have hlt := (zpow_lt_zpow_iff_right₀ hq).mp hlo
    omega
  · exact d.unitGauss_zero_above_conductor p hψ χ he cond.1 α hhi

private theorem norm_unitCharField {p : Prime F} (χ : UnitChar p) (x : LocalField F (.inr p)) :
    ‖unitCharField χ x‖ = if ‖x‖ = 1 then 1 else 0 := by
  by_cases hx : x = 0
  · simp [unitCharField,hx]
  · by_cases hu : ‖x‖ = 1
    · have hmem : Units.mk0 x hx ∈ integralUnits p := hu
      simp [unitCharField,charWeight,hx,hu,hmem]
    · have hmem : Units.mk0 x hx ∉ integralUnits p := hu
      simp [unitCharField,charWeight,hx,hu,hmem]

private theorem unitCharField_test {p : Prime F} (χ : UnitChar p) {e : ℕ} (he : 0 < e)
    (hc : trivialAtLevel χ e) : Continuous (unitCharField χ) ∧ HasCompactSupport (unitCharField χ) := by
  let K := LocalField F (.inr p)
  letI : NontriviallyNormedField (p.adicCompletion F) := FinitePlace.nontriviallyNormedCompletion p
  letI : ProperSpace K := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace (p.adicCompletion F)
  have hq : 0 < (p.asIdeal.absNorm : ℝ) := by exact_mod_cast (Nat.zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm p))
  constructor
  · apply IsLocallyConstant.continuous
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    filter_upwards [Metric.ball_mem_nhds x (inv_pos.mpr (pow_pos hq e))] with y hy
    have h := unitCharField_period χ he hc (y-x) (le_of_lt (by simpa [Metric.mem_ball,dist_eq_norm] using hy)) x
    simpa using h
  · apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : K) 1)
    intro x hx
    have hn := norm_ne_zero_iff.mpr hx
    rw [norm_unitCharField] at hn
    have hu : ‖x‖ = 1 := by_contra fun h => hn (if_neg h)
    simp [Metric.mem_closedBall,dist_zero_right,hu]

omit [NeZero n] in
/-- Parseval and unit covariance give the squared absolute value of a primitive
Gauss integral at every frequency on its conductor shell. -/
theorem unitGauss_conductor_norm_sq (p : Prime F) (hψ : d.UnramifiedAt (.inr p))
    (χ : UnitChar p) {e : ℕ} (he : 0 < e) (cond : IsLeast {j | trivialAtLevel χ j} e)
    (a : (LocalField F (.inr p))ˣ) (ha : ‖a.val‖ = (p.asIdeal.absNorm : ℝ)^e) :
    ‖d.unitGauss p (charWeight χ) a.val‖^2 = ((p.asIdeal.absNorm : ℝ)^e)⁻¹ := by
  let v : Place F := .inr p
  let K := LocalField F v
  let dx := selfDual F d.character v
  letI : dx.IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  let f : C_c(K, ℂ) := ⟨⟨unitCharField χ,(unitCharField_test χ he cond.1).1⟩,(unitCharField_test χ he cond.1).2⟩
  let G := d.unitGauss p (charWeight χ)
  have hat (y : K) : d.hat v f y = G y := (d.unitGauss_hat p χ y).symm
  have shell (x : K) : ‖G (a.val*x)‖ = ‖G a.val‖ * ‖f x‖ := by
    change _ = _ * ‖unitCharField χ x‖
    rw [norm_unitCharField]
    by_cases hx : ‖x‖ = 1
    · have hn : x ≠ 0 := fun h => by simp [h] at hx
      let u : integralUnits p := ⟨Units.mk0 x hn,hx⟩
      have H := d.unitGauss_unit_mul p χ u a.val
      change G (x*a.val) = _ at H
      rw [if_pos hx,mul_one,mul_comm a.val,H,norm_mul]
      simp [G]
    · have hmul : ‖a.val*x‖ ≠ (p.asIdeal.absNorm : ℝ)^e := by
        rw [norm_mul,← ha]
        exact fun h => hx ((mul_eq_left₀ (norm_ne_zero_iff.mpr a.ne_zero)).mp h)
      rw [if_neg hx,mul_zero,show G (a.val*x) = 0 from d.unitGauss_conductor_support p hψ χ he cond _ hmul,norm_zero]
  let mass (x : K) := ‖f x‖^2
  have hpos : 0 < ∫ x, mass x ∂dx := by
    have hc : Continuous mass := f.continuous.norm.pow 2
    have hs : HasCompactSupport mass := by
      simp only [mass,pow_two]
      exact f.hasCompactSupport.norm.mul_right
    apply integral_pos_of_integrable_nonneg_nonzero hc (hc.integrable_of_hasCompactSupport hs) (fun x => sq_nonneg _) (x := 1)
    change ‖unitCharField χ 1‖^2 ≠ 0
    simp [norm_unitCharField]
  have parseval := d.hat_parseval v f f
  simp_rw [hat,← Complex.normSq_eq_conj_mul_self,← Complex.sq_norm] at parseval
  let A (x : K) : ℂ := (‖G x‖^2 : ℝ)
  let I : ℂ := ∫ x, (mass x : ℂ) ∂dx
  have hI : I ≠ 0 := by
    dsimp only [I]
    rw [integral_complex_ofReal]
    exact Complex.ofReal_ne_zero.mpr hpos.ne'
  have mul := d.integral_local_mul v a A
  dsimp only at mul
  have eval (x : K) : A (a.val*x) = ((‖G a.val‖^2 : ℝ) : ℂ) * (mass x : ℂ) := by
    simp only [A,mass,shell,mul_pow,Complex.ofReal_mul]
  simp_rw [eval] at mul
  rw [integral_const_mul,show (∫ x, A x ∂dx) = I from parseval] at mul
  change ((‖G a.val‖^2 : ℝ) : ℂ) * I = I / (‖a.val‖ : ℂ) at mul
  rw [div_eq_inv_mul,ha] at mul
  exact Complex.ofReal_injective (by simpa only [Complex.ofReal_inv] using (mul_right_cancel₀ hI mul))

/-- Inverting the inner Jacquet variable turns the kernel into the Gauss
integral of the conjugate character times the Hilbert symbol. -/
theorem kernelIntegral_charWeight (p : Prime F) (hp : p.asIdeal.absNorm.Coprime n)
    (χ : UnitChar p) (c : (LocalField F (.inr p))ˣ) (t : LocalField F (.inr p)) :
    d.kernelIntegral (.inr p) (charWeight χ) c t =
      d.unitGauss p (fun x => conj (charWeight χ x) * d.symbol (.inr p) c x) (-t^n/c.val) := by
  let v : Place F := .inr p
  unfold kernelIntegral unitGauss
  rw [← d.lineIntegral_inv]
  congr 1
  funext x
  dsimp only
  by_cases hx : x ∈ integralUnits p
  · have hxi := (integralUnits p).inv_mem hx
    have char : charWeight χ x⁻¹ = conj (charWeight χ x) := by
      let u : integralUnits p := ⟨x,hx⟩
      simp only [charWeight,dif_pos hx,dif_pos hxi]
      exact (congrArg ((↑) : Circle → ℂ) (χ.map_inv u)).trans (Circle.coe_inv_eq_conj _)
    have hsym : d.symbol v x⁻¹ (-c) = d.symbol v c x := by
      apply congrArg Units.val
      change d.unitPairing v x⁻¹ (-c) = d.unitPairing v c x
      have sk : d.unitPairing v x (-c) = (d.unitPairing v (-c) x)⁻¹ :=
        (d.lineSymbol v (d.finite_steinberg p)).skew x (-c)
      rw [map_inv,MonoidHom.inv_apply,sk,inv_inv,
        show -c = (-1)*c by simp,map_mul,MonoidHom.mul_apply,
        d.unitPairing_tame_units p hp (-1) x (by simp) hx,one_mul]
    have phase : -(t^n)/(c.val*x⁻¹.val) = -(t^n)/c.val*x.val := by
      rw [Units.val_inv_eq_inv_val]
      field_simp
    rw [if_pos (show ‖x.val‖ = 1 from hx),char,hsym,phase]
  · have hxi : x⁻¹ ∉ integralUnits p := by simpa using hx
    simp [charWeight,hxi,show ‖x.val‖ ≠ 1 from hx]

/-- The integral formula in the twisted-reduction lemma. -/
theorem dual_charWeight_integral (p : Prime F) (hp : p.asIdeal.absNorm.Coprime n)
    (χ : UnitChar p) (c : (LocalField F (.inr p))ˣ) :
    d.dualWeight (.inr p) (charWeight χ) c =
      ∫ t, d.character.localValue F (.inr p) t *
        d.unitGauss p (fun x => conj (charWeight χ x) * d.symbol (.inr p) c x) (-t^n/c.val)
        ∂(selfDual F d.character (.inr p)) := by
  have hm : modulus F (.inr p) (n : LocalField F (.inr p)) = 1 := FinitePlace.norm_degree_of_tame p hp
  simp only [dualWeight,hm,Real.sqrt_one,
    Complex.ofReal_one,inv_one,one_mul,d.kernelIntegral_charWeight p hp]

end MetaplecticPoisson.Datum
