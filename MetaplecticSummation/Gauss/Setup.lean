import MetaplecticSummation.SArithmetic

noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField IsDedekindDomain MeasureTheory
open scoped ComplexConjugate
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [hn : NeZero n] (d : Datum F n)

def UnramifiedAt (v : Place F) : Prop :=
  ∀ x : LocalField F v, (∀ y : LocalField F v, ‖y‖ ≤ 1 →
    d.character.localValue F v (x * y) = 1) ↔ ‖x‖ ≤ 1

structure ClassicalSetting (S : Finset (Place F)) : Prop where
  good : d.GoodOutside S
  unramified : ∀ p : Prime F, Sum.inr p ∉ S → d.UnramifiedAt (.inr p)
  principal : IsPrincipalIdealRing (SIntegers S)

def integralUnits (p : Prime F) : Subgroup (LocalField F (.inr p))ˣ where
  carrier := {u | ‖(u : LocalField F (.inr p))‖ = 1}
  one_mem' := norm_one
  mul_mem' := by intro a b ha hb; change ‖(a : LocalField F (.inr p)) * b‖ = 1; rw [norm_mul, ha, hb, one_mul]
  inv_mem' := by
    intro a ha
    change ‖((a⁻¹ : (LocalField F (.inr p))ˣ) : LocalField F (.inr p))‖ = 1
    rw [Units.val_inv_eq_inv_val, norm_inv, ha, inv_one]

abbrev UnitChar (p : Prime F) := integralUnits p →* Circle

def charWeight {p : Prime F} (χ : UnitChar p) : Weight (.inr p : Place F) := by
  classical exact fun x => if h : x ∈ integralUnits p then ((χ ⟨x,h⟩ : Circle) : ℂ) else 0

/-- Level zero tests the full unit group. At positive level k this tests
the principal units congruent to one modulo the kth power of the prime. -/
def trivialAtLevel {p : Prime F} (χ : UnitChar p) (k : ℕ) : Prop :=
  ∀ u : integralUnits p, (k = 0 ∨ ‖((u.val : LocalField F (.inr p)) - 1)‖ ≤
    ((p.asIdeal.absNorm : ℝ) ^ k)⁻¹) → χ u = 1

structure Twist (S : Finset (Place F)) (f : NonzeroInteger S) where
  primes : Finset (Prime F)
  outside : ∀ p ∈ primes, Sum.inr p ∉ S
  character : (p : primes) → UnitChar p.val
  continuous_char : ∀ p, Continuous (character p)
  exponent : primes → ℕ
  positive : ∀ p, 0 < exponent p
  conductor : ∀ p, IsLeast {k | trivialAtLevel (character p ^ n) k} (exponent p)
  generator : ∀ p : primes, ‖diagonal F (.inr p.val) (fieldUnit f)‖ =
    ((p.val.asIdeal.absNorm : ℝ) ^ exponent p)⁻¹
  unit_elsewhere : ∀ p : Prime F, Sum.inr p ∉ S → p ∉ primes →
    ‖diagonal F (.inr p) (fieldUnit f)‖ = 1
  empty_modulus : primes = ∅ → fieldUnit f = 1

def twistValue {S : Finset (Place F)} {f : NonzeroInteger S} (T : Twist (n := n) S f) (c : Fˣ) :=
  ∏ p : T.primes, charWeight (T.character p) (atPlace (.inr p.val) c)

def epsilon {S : Finset (Place F)} {f : NonzeroInteger S} (T : Twist (n := n) S f) (b : Fˣ) :=
  ∏ p : T.primes, d.dualWeight (.inr p.val) (charWeight (T.character p))
    (atPlace _ (b * fieldUnit f ^ (n-1))⁻¹)

omit hn in
theorem exists_scaled (b : Fˣ) : ∃ ψ : Character F, ∀ x,
    ψ.toChar x = d.character.toChar (algebraMap F (Adeles F) (b : F) * x) := by
  let χ := d.character.toChar.mulShift (algebraMap F (Adeles F) (b : F))
  refine ⟨⟨χ, d.character.continuous_toChar.comp (continuous_const.mul continuous_id), ?_, ?_⟩,
    fun _ => rfl⟩
  · obtain ⟨x, hx⟩ := d.character.nontrivial
    refine ⟨algebraMap F (Adeles F) (↑b⁻¹ : F) * x, ?_⟩
    simpa only [χ, AddChar.mulShift_apply, ← mul_assoc, ← map_mul, Units.mul_inv, map_one,
      one_mul] using hx
  · intro a
    exact (congrArg d.character.toChar (map_mul _ (b : F) a).symm).trans
      (d.character.trivial_diagonal _)

def scaled (b : Fˣ) : Datum F n := { d with character := (d.exists_scaled b).choose }

def sWeight {S : Finset (Place F)} (W : Weights S) (c : Fˣ) :=
  ∏ v : S, W v (atPlace v.val c)

def sDual {S : Finset (Place F)} (W : Weights S) (c : Fˣ) :=
  ∏ v : S, d.dualWeight v.val (W v) (atPlace v.val c)

omit hn in
theorem scaled_localValue (b : Fˣ) (v : Place F) (x : LocalField F v) :
    (d.scaled b).character.localValue F v x = d.character.localValue F v (diagonal F v b * x) := by
  unfold Character.localValue
  rw [show (d.scaled b).character.toChar (singleAdele F v x) = _ from
    (d.exists_scaled b).choose_spec (singleAdele F v x)]
  congr 2
  classical
  cases v with
  | inl w =>
    apply Prod.ext
    · funext u
      change algebraMap F u.Completion (b : F) * Pi.single w x u = Pi.single w (_ * x) u
      by_cases h : u = w
      · subst u; simp only [Pi.single_eq_same]; rfl
      · simp only [Pi.single_eq_of_ne h, mul_zero]
    · exact mul_zero _
  | inr p =>
    apply Prod.ext (mul_zero _)
    exact (RestrictedProduct.mul_single _ p x (algebraMap F (Adeles F) (b : F)).2).symm

omit hn in
/-- The annihilator of the integers for the scaled character is the
inverse image of the original annihilator under multiplication by b. -/
theorem scaled_conductor (b : Fˣ) (v : Place F) (h : d.UnramifiedAt v)
    (x : LocalField F v) :
    (∀ y : LocalField F v, ‖y‖ ≤ 1 → (d.scaled b).character.localValue F v (x*y) = 1) ↔
      ‖x * diagonal F v b‖ ≤ 1 := by
  simp only [d.scaled_localValue, ← mul_assoc]
  simpa only [mul_comm x (diagonal F v b)] using h (diagonal F v b * x)

omit hn in
theorem scaled_good {S : Finset (Place F)} (h : d.ClassicalSetting S) (b : NonzeroInteger S) :
    (d.scaled (fieldUnit b)).GoodOutside S := by
  refine ⟨h.good.1, h.good.2.1, fun p hp => ⟨(h.good.2.2 p hp).1, fun x hx => ?_⟩⟩
  rw [d.scaled_localValue]
  apply (h.good.2.2 p hp).2
  rw [norm_mul]
  exact mul_le_one₀ (integer_norm_le_one b.val p hp) (norm_nonneg _) hx

def mainTerm {S : Finset (Place F)} (h : d.ClassicalSetting S) (b : NonzeroInteger S)
    (W : Weights S) : ℂ :=
  let db := d.scaled (fieldUnit b)
  let ρ := (db.lineSummation S (d.scaled_good h b)).exists.choose
  (Real.sqrt (sNorm S (fieldUnit b)) : ℂ) * ∑ᶠ β, ρ β * db.moment W β

end MetaplecticPoisson.Datum
