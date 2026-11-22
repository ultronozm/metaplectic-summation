import MetaplecticSummation.Jacquet
import Mathlib.RingTheory.DedekindDomain.SInteger
import Mathlib.RingTheory.UniqueFactorizationDomain.Finite

noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField IsDedekindDomain MeasureTheory
open scoped ComplexConjugate
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [hn : NeZero n] (d : Datum F n)

abbrev Prime (F : Type) [Field F] [NumberField F] := HeightOneSpectrum (𝓞 F)
abbrev SIntegers (S : Finset (Place F)) := ({p : Prime F | Sum.inr p ∈ S}.integer F)
abbrev NonzeroInteger (S : Finset (Place F)) := {c : SIntegers S // c ≠ 0}

def fieldUnit {S : Finset (Place F)} (c : NonzeroInteger S) : Fˣ :=
  Units.mk0 (c.val : F) (fun h => c.property (Subtype.ext h))

def sNorm (S : Finset (Place F)) (x : F) := ∏ v ∈ S, modulus F v (diagonal F v x)
def sPsi (S : Finset (Place F)) (x : F) := ∏ v ∈ S, d.character.localValue F v (diagonal F v x)
def sSymbol (S : Finset (Place F)) (a b : Fˣ) := ∏ v ∈ S, d.symbol v (atPlace v a) (atPlace v b)

def residue (S : Finset (Place F)) (a c : F) : ℂ := by
  classical
  exact ∏ᶠ p : Prime F, if Sum.inr p ∉ S ∧ ‖diagonal F (.inr p) c‖ < 1 then
    if h : a ≠ 0 ∧ c ≠ 0 ∧ ‖diagonal F (.inr p) a‖ = 1 then
      d.symbol (.inr p) (atPlace _ (Units.mk0 c h.2.1)) (atPlace _ (Units.mk0 a h.1))
    else 0 else 1

theorem finite_residues (S : Finset (Place F)) (c : NonzeroInteger S) :
    Finite (SIntegers S ⧸ Ideal.span {c.val}) := by sorry

include hn in
theorem finite_power_divisors (S : Finset (Place F)) [IsPrincipalIdealRing (SIntegers S)]
    (c : NonzeroInteger S) :
    Set.Finite {t : Associates (SIntegers S) | t ^ n ∣ Associates.mk c.val} := by
  classical
  let a := Associates.mk c.val
  have ha : a ≠ 0 := by simpa [a] using c.property
  letI := Fintype.ofFinite (Associates (SIntegers S))ˣ
  let s : Set (Associates (SIntegers S)) := {t | t ∣ a}
  letI : Fintype s := UniqueFactorizationMonoid.fintypeSubtypeDvd a ha
  exact s.toFinite.subset (fun t ht => (dvd_pow_self t (NeZero.ne n)).trans ht)

/-- A unit residue class modulo (c) is evaluated on an S-integer representative.
For a unit modulus the product defining the residue symbol is empty. -/
def gauss (S : Finset (Place F)) (b c : SIntegers S) : ℂ :=
  ∑ᶠ u : (SIntegers S ⧸ Ideal.span {c})ˣ,
    let a : SIntegers S := Quotient.out (u : SIntegers S ⧸ Ideal.span {c})
    d.residue S a c * d.sPsi S ((b : F) * a / c)

theorem gauss_lift_independent {S : Finset (Place F)} (hS : d.GoodOutside S)
    (b : SIntegers S) (c : NonzeroInteger S) (u : (SIntegers S ⧸ Ideal.span {c.val})ˣ)
    (a a' : SIntegers S) (ha : Ideal.Quotient.mk _ a = u.val)
    (ha' : Ideal.Quotient.mk _ a' = u.val) :
    d.residue S a c.val * d.sPsi S ((b : F) * a / c.val) =
    d.residue S a' c.val * d.sPsi S ((b : F) * a' / c.val) := by sorry

theorem gauss_unit_power {S : Finset (Place F)} (hS : d.GoodOutside S)
    (b : SIntegers S) (c : NonzeroInteger S) (u : (SIntegers S)ˣ) :
    d.gauss S b ((u : SIntegers S)^n * c.val) = d.gauss S b c.val := by sorry

def normalizedGauss (S : Finset (Place F)) (b c : SIntegers S) : ℂ := by
  classical
  exact (sNorm S c : ℂ)⁻¹ * ∑ᶠ t : Associates (SIntegers S),
    let a : SIntegers S := Quotient.out t
    if h : a ^ n ∣ c then
      (sNorm S a : ℂ) ^ (n-1) * d.gauss S b h.choose else 0

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

theorem exists_scaled (b : Fˣ) : ∃ ψ : Character F, ∀ x,
    ψ.toChar x = d.character.toChar (algebraMap F (Adeles F) (b : F) * x) := by sorry

def scaled (b : Fˣ) : Datum F n := { d with character := (d.exists_scaled b).choose }

def sWeight {S : Finset (Place F)} (W : Weights S) (c : Fˣ) :=
  ∏ v : S, W v (atPlace v.val c)

def sDual {S : Finset (Place F)} (W : Weights S) (c : Fˣ) :=
  ∏ v : S, d.dualWeight v.val (W v) (atPlace v.val c)

theorem scaled_good {S : Finset (Place F)} (h : d.ClassicalSetting S) (b : NonzeroInteger S) :
    (d.scaled (fieldUnit b)).GoodOutside S := by sorry

def mainTerm {S : Finset (Place F)} (h : d.ClassicalSetting S) (b : NonzeroInteger S)
    (W : Weights S) : ℂ :=
  let db := d.scaled (fieldUnit b)
  let ρ := (db.lineSummation S (d.scaled_good h b)).exists.choose
  (Real.sqrt (sNorm S (fieldUnit b)) : ℂ) * ∑ᶠ β, ρ β * db.moment W β

/-- The untwisted S-integer formula preceding Theorem 10.34. -/
theorem untwistedGaussSummation {S : Finset (Place F)} (h : d.ClassicalSetting S)
    (W : Weights S) (hW : Admissible W) :
    let ρ := (d.lineSummation S h.good).exists.choose
    (∑' c : NonzeroInteger S, sWeight W (fieldUnit c) * d.normalizedGauss S 1 c.val) =
      (∑' c : NonzeroInteger S, d.sDual W (fieldUnit c) * d.normalizedGauss S 1 c.val) +
        ∑ᶠ β, ρ β * d.moment W β := by sorry

/-- Theorem 10.34. The primes of the conductor determine whether the main term occurs. -/
theorem twistedGaussSummation {S : Finset (Place F)} (h : d.ClassicalSetting S)
    (f b : NonzeroInteger S) (T : Twist (n := n) S f) (coprime : IsCoprime b.val f.val)
    (W : Weights S) (hW : Admissible W) :
    ‖d.epsilon T (fieldUnit b)‖ = 1 ∧
    (∑' c : NonzeroInteger S, sWeight W (fieldUnit c) * twistValue T (fieldUnit c) *
      d.normalizedGauss S b.val c.val) =
    d.epsilon T (fieldUnit b) * (∑' c : NonzeroInteger S,
      d.sDual (fun v x => W v x * d.symbol v.val x (atPlace _ (fieldUnit b)))
        (fieldUnit c / (fieldUnit b * fieldUnit f ^ (n-1))) *
      conj (twistValue T (fieldUnit c)) * d.residue S (fieldUnit c) (fieldUnit f) *
      d.residue S (fieldUnit f) (fieldUnit c) * d.normalizedGauss S b.val c.val) +
      (if T.primes.card = 0 then d.mainTerm h b W else 0) := by sorry

/-- Every embedding sends the two square roots of unity to the same signs. -/
def quadraticDatum : Datum F 2 := by
  let e := (Classical.arbitrary (InfinitePlace F)).embedding
  exact { root := -1
          primitive := IsPrimitiveRoot.neg_one 0 (by decide)
          embedding := (Units.map e.toMonoidHom).comp (rootsOfUnity 2 F).subtype
          injective := (Units.map_injective e.injective).comp Subtype.val_injective
          character := d.character }

/-- Corollary 10.40. The quadratic datum uses the same number field;
the quadratic Hilbert symbol has a unique complex embedding. -/
theorem quadraticDual {S : Finset (Place F)} (hS : d.ClassicalSetting S)
    (odd : Odd n)
    (awayTwo : ∀ p : Prime F, Sum.inr p ∉ S → Odd p.asIdeal.absNorm)
    (h : NonzeroInteger S) (nonunit : ¬ IsUnit h.val) (squarefree : Squarefree h.val) :
    ∃ ε : ℂ, ‖ε‖ = 1 ∧ ∀ W : Weights S, Admissible W →
      (∑' c : NonzeroInteger S, sWeight W (fieldUnit c) * d.quadraticDatum.residue S (fieldUnit c) (fieldUnit h) *
        d.residue S (fieldUnit c) (fieldUnit h) ^ 2 * d.normalizedGauss S 1 c.val) =
      ε * ∑' c : NonzeroInteger S, d.sDual W (fieldUnit c / fieldUnit h ^ (n-1)) *
        d.sSymbol S (fieldUnit h) (fieldUnit c) * d.quadraticDatum.residue S (fieldUnit c) (fieldUnit h) *
        d.normalizedGauss S 1 c.val := by sorry

/-- In degree three the twist on the left of Corollary 10.40 is the
sextic residue symbol for the compatible embedding of μ₆. -/
theorem sextic_to_quadratic (a : Datum F 3) (six : Datum F 6)
    (compatible : ∀ z : Mu F 3,
      six.embedding ⟨z.val, rootsOfUnity_le_of_dvd (by decide : 3 ∣ 6) z.property⟩ = a.embedding z)
    {S : Finset (Place F)} (hS : a.ClassicalSetting S)
    (awayTwo : ∀ p : Prime F, Sum.inr p ∉ S → Odd p.asIdeal.absNorm)
    (h : NonzeroInteger S) (nonunit : ¬ IsUnit h.val) (squarefree : Squarefree h.val) :
    ∃ ε : ℂ, ‖ε‖ = 1 ∧ ∀ W : Weights S, Admissible W →
      (∑' c : NonzeroInteger S, sWeight W (fieldUnit c) * six.residue S (fieldUnit c) (fieldUnit h) *
        a.normalizedGauss S 1 c.val) =
      ε * ∑' c : NonzeroInteger S, a.sDual W (fieldUnit c / fieldUnit h ^ 2) *
        a.sSymbol S (fieldUnit h) (fieldUnit c) * a.quadraticDatum.residue S (fieldUnit c) (fieldUnit h) *
        a.normalizedGauss S 1 c.val := by sorry

end MetaplecticPoisson.Datum
