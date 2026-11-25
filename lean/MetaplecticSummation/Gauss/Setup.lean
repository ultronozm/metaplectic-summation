import MetaplecticSummation.SArithmetic

noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField IsDedekindDomain MeasureTheory
open scoped ComplexConjugate
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [hn : NeZero n] (d : Datum F n)

structure ClassicalSetting (S : Finset (Place F)) : Prop where
  good : d.GoodOutside S
  unramified : ∀ p : Prime F, Sum.inr p ∉ S → d.UnramifiedAt (.inr p)
  principal : IsPrincipalIdealRing (SIntegers S)

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

def sWeight {S : Finset (Place F)} (W : Weights S) (c : Fˣ) :=
  ∏ v : S, W v (atPlace v.val c)

def sDual {S : Finset (Place F)} (W : Weights S) (c : Fˣ) :=
  ∏ v : S, d.dualWeight v.val (W v) (atPlace v.val c)

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
