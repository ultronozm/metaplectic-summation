import MetaplecticSummation.UnitGauss

/-! Evaluation of the local transform of a ramified unit character. -/

noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField MeasureTheory
open scoped ComplexConjugate
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

def hilbertUnitChar (p : Prime F) (t : (p.adicCompletion F)ˣ) : UnitChar p where
  toFun u := ⟨d.symbol (.inr p) t u.val, mem_sphere_zero_iff_norm.mpr (d.norm_symbol (.inr p) t u.val)⟩
  map_one' := Subtype.ext (congrArg Units.val ((d.unitPairing (.inr p) t).map_one))
  map_mul' x y := Subtype.ext (congrArg Units.val ((d.unitPairing (.inr p) t).map_mul x.val y.val))

theorem continuous_hilbertUnitChar (p : Prime F) (t : (p.adicCompletion F)ˣ) :
    Continuous (d.hilbertUnitChar p t) :=
  ((d.continuous_symbol (.inr p)).comp (continuous_const.prodMk continuous_subtype_val)).subtype_mk _

theorem hilbertUnitChar_pow (p : Prime F) (t : (p.adicCompletion F)ˣ) : (d.hilbertUnitChar p t)^n = 1 := by
  ext u
  exact congrArg Units.val (d.unitPairing_pow (.inr p) t u.val)

private def dualUnitChar (p : Prime F) (χ : UnitChar p) (c : (LocalField F (.inr p))ˣ) :=
  χ⁻¹ * d.hilbertUnitChar p c

private theorem dualUnitChar_pow (p : Prime F) (χ : UnitChar p) (c : (LocalField F (.inr p))ˣ) :
    (d.dualUnitChar p χ c)^n = (χ^n)⁻¹ := by
  erw [dualUnitChar,mul_pow,d.hilbertUnitChar_pow p c,mul_one,inv_pow]

private theorem charWeight_dualUnitChar (p : Prime F) (χ : UnitChar p) (c : (LocalField F (.inr p))ˣ) :
    charWeight (d.dualUnitChar p χ c) = fun x => conj (charWeight χ x) * d.symbol (.inr p) c x := by
  funext x
  by_cases hx : x ∈ integralUnits p
  · simp only [charWeight,dif_pos hx,dualUnitChar,MonoidHom.mul_apply,MonoidHom.inv_apply,Circle.coe_mul,
      Circle.coe_inv_eq_conj]
    rfl
  · simp only [charWeight,dif_neg hx,map_zero,zero_mul]

/-- Multiplication of the conjugate character by the tame Hilbert symbol
preserves the conductor exponent of the ramified n-th power. -/
private theorem dualUnitChar_conductor (p : Prime F) (hp : p.asIdeal.absNorm.Coprime n)
    (χ : UnitChar p) (c : (LocalField F (.inr p))ˣ) {e : ℕ} (he : 0 < e)
    (cond : IsLeast {j | trivialAtLevel (χ^n) j} e) :
    IsLeast {j | trivialAtLevel (d.dualUnitChar p χ c) j} e := by
  constructor
  · intro u hu
    have hb := hu.resolve_left he.ne'
    have hq : 1 < (p.asIdeal.absNorm : ℝ) := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm p
    obtain ⟨z,hz,hclose⟩ : ∃ z : (LocalField F (.inr p))ˣ, z^n = u.val ∧ ‖z.val-1‖ = ‖u.val.val-1‖ := FinitePlace.principal_unit_pow_norm p hp u.val
      (hb.trans_lt (inv_lt_one_of_one_lt₀ (one_lt_pow₀ hq he.ne')))
    have hnorm : ‖z.val‖ = 1 := by
      apply (pow_left_inj₀ (norm_nonneg _) zero_le_one (NeZero.ne n)).mp
      have h := congrArg (fun t : (LocalField F (.inr p))ˣ => ‖t.val‖) hz
      simpa only [Units.val_pow_eq_pow_val,norm_pow,show ‖u.val.val‖ = 1 from u.property,one_pow] using h
    let Z : integralUnits p := ⟨z,hnorm⟩
    have hZu : Z^n = u := Subtype.ext hz
    have hχ := cond.1 Z (Or.inr (hclose.trans_le hb))
    have hχu : χ u = 1 := by rw [← hZu,map_pow]; exact hχ
    have hsym : d.hilbertUnitChar p c u = 1 := by
      apply Subtype.ext
      change (d.unitPairing (.inr p) c u.val).val = _
      rw [← hz,map_pow,d.unitPairing_pow]
      rfl
    simp only [dualUnitChar,MonoidHom.mul_apply,MonoidHom.inv_apply,hχu,hsym,inv_one,mul_one]
  · intro k hk
    apply cond.2
    intro u hu
    have h := congrArg (fun θ : UnitChar p => θ u) (d.dualUnitChar_pow p χ c)
    simp only [MonoidHom.pow_apply,MonoidHom.inv_apply,hk u hu,one_pow] at h
    simpa only [MonoidHom.pow_apply,inv_eq_one] using h.symm

private theorem gauss_shell_evaluation (p : Prime F) (hp : p.asIdeal.absNorm.Coprime n)
    (hψ : d.UnramifiedAt (.inr p)) (χ : UnitChar p) {e : ℕ} (he : 0 < e)
    (cond : IsLeast {j | trivialAtLevel (χ^n) j} e) (c t : (LocalField F (.inr p))ˣ)
    (ht : ‖-t.val^n/c.val‖ = (p.asIdeal.absNorm : ℝ)^e) :
    d.dualWeight (.inr p) (charWeight χ) c =
      (‖t.val‖ : ℂ) * d.unitGauss p (charWeight (χ^n)) t.val *
        d.unitGauss p (charWeight (d.dualUnitChar p χ c)) (-t.val^n/c.val) := by
  let v : Place F := .inr p
  let ρ := d.dualUnitChar p χ c
  let G := d.unitGauss p (charWeight ρ)
  let α := -t.val^n/c.val
  let ψ := d.character.localValue F v
  let dx := selfDual F d.character v
  have hc := d.dualUnitChar_conductor p hp χ c he cond
  have shell (x : LocalField F v) : G (x^n*α) = unitCharField (χ^n) x * G α := by
    by_cases hx : ‖x‖ = 1
    · have hn : x ≠ 0 := fun h => by simp [h] at hx
      let u : integralUnits p := ⟨Units.mk0 x hn,hx⟩
      have hρ := congrArg (fun θ : UnitChar p => θ u) (d.dualUnitChar_pow p χ c)
      change ρ u ^ n = ((χ^n) u)⁻¹ at hρ
      have hchar : conj (ρ (u^n) : ℂ) = unitCharField (χ^n) x := by
        rw [map_pow,hρ,Circle.coe_inv_eq_conj,starRingEnd_self_apply]
        simp only [unitCharField,dif_pos hn,charWeight,dif_pos (show Units.mk0 x hn ∈ integralUnits p from hx)]
        rfl
      exact (d.unitGauss_unit_mul p ρ (u^n) α).trans (congrArg (· * G α) hchar)
    · have hα : ‖x^n*α‖ ≠ (p.asIdeal.absNorm : ℝ)^e := by
        rw [norm_mul,norm_pow,← ht]
        have ha : α ≠ 0 := div_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ t.ne_zero)) c.ne_zero
        exact fun h => hx ((pow_eq_one_iff_of_nonneg (norm_nonneg x) (NeZero.ne n)).mp
          ((mul_eq_right₀ (norm_ne_zero_iff.mpr ha)).mp h))
      have hzero : unitCharField (χ^n) x = 0 := by
        by_cases hn : x = 0
        · simp [unitCharField,hn]
        · simp only [unitCharField,dif_pos hn,charWeight,dif_neg (show Units.mk0 x hn ∉ integralUnits p from hx)]
      rw [hzero,zero_mul]
      exact d.unitGauss_conductor_support p hψ ρ he hc _ hα
  let g (y : LocalField F v) := ψ y * G (-y^n/c.val)
  have arg (x : LocalField F v) : -(t.val*x)^n/c.val = x^n*α := by simp only [α,mul_pow]; ring
  have mul := d.integral_local_mul v t g
  dsimp only at mul
  have eval (x : LocalField F v) : g (t.val*x) = (unitCharField (χ^n) x * ψ (t.val*x)) * G α := by
    dsimp only [g]
    rw [arg,shell]; ring
  simp_rw [eval] at mul
  rw [integral_mul_const] at mul
  have ht0 : (‖t.val‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr t.ne_zero)
  have hh := (eq_div_iff ht0).mp mul
  rw [d.dual_charWeight_integral p hp,← d.charWeight_dualUnitChar]
  change (∫ y, g y ∂dx) = (‖t.val‖ : ℂ) * d.unitGauss p (charWeight (χ^n)) t.val * G α
  rw [← hh, d.unitGauss_hat]
  unfold hat
  change (_ * G α) * _ = _ * _ * G α
  ring

theorem twistedVector (p : Prime F) (hp : p.asIdeal.absNorm.Coprime n) (hψ : d.UnramifiedAt (.inr p))
    (χ : UnitChar p) (hχ : Continuous χ) (e : ℕ) (he : 0 < e)
    (cond : IsLeast {k | trivialAtLevel (χ^n) k} e) (c : (LocalField F (.inr p))ˣ) :
    let q : ℝ := p.asIdeal.absNorm
    let V := d.dualWeight (.inr p) (charWeight χ) c
    (‖(c : LocalField F (.inr p))‖ ≠ q ^ ((n-1)*e) → V = 0) ∧
    (‖(c : LocalField F (.inr p))‖ = q ^ ((n-1)*e) →
      ‖V‖ = 1 ∧ ∀ t : (LocalField F (.inr p))ˣ, ‖(t : LocalField F (.inr p))‖ = q ^ e →
        V = (q : ℂ)^e * d.unitGauss p (charWeight (χ ^ n)) t *
          d.unitGauss p (fun x => conj (charWeight χ x) * d.symbol (.inr p) c x)
            (-((t : LocalField F (.inr p)) ^ n) / c)) := by
  let v : Place F := .inr p
  clear hχ
  let q : ℝ := p.asIdeal.absNorm
  let R := q ^ e
  let ρ := d.dualUnitChar p χ c
  let V := d.dualWeight v (charWeight χ) c
  let G := d.unitGauss p (charWeight ρ)
  have hq : 0 < q := by dsimp [q]; exact_mod_cast (Nat.zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm p))
  have hR : 0 < R := pow_pos hq e
  have hexp : q^((n-1)*e) = R^(n-1) := by rw [Nat.mul_comm (n-1),pow_mul]
  have hpow : R*R^(n-1) = R^n := by rw [← pow_succ',Nat.sub_add_cancel (NeZero.pos n)]
  have hcpos := norm_pos_iff.mpr c.ne_zero
  have shell (x : LocalField F v) : ‖-x^n/c.val‖ = R ↔ ‖x‖^n = R*‖c.val‖ := by
    rw [norm_div,norm_neg,norm_pow,div_eq_iff hcpos.ne']
  have hρ := d.dualUnitChar_conductor p hp χ c he cond
  dsimp only
  change (‖c.val‖ ≠ q^((n-1)*e) → V = 0) ∧ (‖c.val‖ = q^((n-1)*e) → _)
  rw [hexp]
  constructor
  · intro off
    by_cases hit : ∃ t : (LocalField F v)ˣ, ‖-t.val^n/c.val‖ = R
    · obtain ⟨t,ht⟩ := hit
      have ht' : ‖t.val‖ ≠ R := by
        intro h
        have hn := (shell t.val).mp ht
        rw [h,← hpow] at hn
        exact off (mul_left_cancel₀ hR.ne' hn.symm)
      exact (d.gauss_shell_evaluation p hp hψ χ he cond c t ht).trans (by
        rw [d.unitGauss_conductor_support p hψ (χ^n) he cond _ ht',mul_zero,zero_mul])
    · change d.dualWeight v _ c = 0
      rw [d.dual_charWeight_integral p hp,← d.charWeight_dualUnitChar]
      apply integral_eq_zero_of_ae
      filter_upwards with y
      have none : ‖-y^n/c.val‖ ≠ R := by
        by_cases hy : y = 0
        · simp [hy,zero_pow (NeZero.ne n),hR.ne'.symm]
        · exact fun hy' => hit ⟨Units.mk0 y hy,hy'⟩
      rw [d.unitGauss_conductor_support p hψ ρ he hρ _ none,mul_zero]
      rfl
  · intro hc
    have eqn (t : (LocalField F v)ˣ) (ht : ‖t.val‖ = R) :
        V = (R : ℂ) * d.unitGauss p (charWeight (χ^n)) t.val * G (-t.val^n/c.val) := by
      have ha := (shell t.val).mpr (by rw [ht,hc,hpow])
      exact (d.gauss_shell_evaluation p hp hψ χ he cond c t ha).trans (by rw [ht])
    constructor
    · obtain ⟨π,hπ⟩ : ∃ π : (LocalField F v)ˣ, ‖π.val‖ = q⁻¹ := FinitePlace.exists_norm_uniformizer p
      let t := π⁻¹^e
      have ht : ‖t.val‖ = R := by simp only [t,R,Units.val_pow_eq_pow_val,norm_pow,Units.val_inv_eq_inv_val,norm_inv,hπ,inv_inv]
      let a := Units.mk0 (-t.val^n/c.val) (div_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ t.ne_zero)) c.ne_zero)
      have ha : ‖a.val‖ = R := (shell t.val).mpr (by rw [ht,hc,hpow])
      have h1 := d.unitGauss_conductor_norm_sq p hψ (χ^n) he cond t ht
      have h2 := d.unitGauss_conductor_norm_sq p hψ ρ he hρ a ha
      change ‖G (-t.val^n/c.val)‖^2 = R⁻¹ at h2
      change ‖d.unitGauss p (charWeight (χ^n)) t.val‖^2 = R⁻¹ at h1
      change ‖V‖ = 1
      apply (pow_left_inj₀ (norm_nonneg _) zero_le_one (by decide : 2 ≠ 0)).mp
      rw [eqn t ht,norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg hR.le,
        mul_pow,mul_pow,h1,h2,one_pow]
      field_simp
    · intro t ht
      rw [← d.charWeight_dualUnitChar]
      simpa only [R,Complex.ofReal_pow,q] using eqn t ht

end MetaplecticPoisson.Datum
