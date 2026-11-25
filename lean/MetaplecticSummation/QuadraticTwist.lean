import MetaplecticSummation.TwistedSummation
import MetaplecticSummation.ResidueReciprocity
import MetaplecticSummation.TamePowers

/-! The primitive unit characters used in Corollary 10.40 at the primes of a squarefree modulus. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField
open scoped ComplexConjugate
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

/-- Restriction of the Hilbert character of t to the local integer units. -/
private theorem twist_pow (b : Datum F 2) (odd : Odd n) (p : Prime F) (t : (p.adicCompletion F)ˣ) :
    (b.hilbertUnitChar p t * (d.hilbertUnitChar p t)^2)^n = b.hilbertUnitChar p t := by
  rw [mul_pow,pow_right_comm,hilbertUnitChar_pow,one_pow,mul_one]
  obtain ⟨k,hk⟩ := odd
  rw [hk,pow_succ,pow_mul,b.hilbertUnitChar_pow,one_pow,one_mul]

private theorem quadratic_level_one (b : Datum F 2) (p : Prime F) (hp : Odd p.asIdeal.absNorm)
    (t : (p.adicCompletion F)ˣ) (ht : ‖t.val‖ = (p.asIdeal.absNorm : ℝ)⁻¹) :
    IsLeast {k | trivialAtLevel (b.hilbertUnitChar p t) k} 1 := by
  have hq : 1 < (p.asIdeal.absNorm : ℝ) := by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm p
  constructor
  · intro u hu
    obtain ⟨z,hz⟩ := FinitePlace.principal_unit_pow p hp.coprime_two_right u.val
      ((hu.resolve_left (by decide)).trans_lt (by simpa using inv_lt_one_of_one_lt₀ hq))
    apply Subtype.ext
    change b.symbol (.inr p) t u.val = 1
    rw [← hz]
    exact congrArg Units.val (((b.unitPairing (.inr p) t).map_pow z 2).trans (b.unitPairing_pow (.inr p) t z))
  · intro k hk
    by_contra h
    have hz : k = 0 := by omega
    subst k
    obtain ⟨z,he⟩ := b.norm_power_of_trivial_on_units p hp.coprime_two_right t (by
      intro u hu
      exact congrArg (fun y : Circle => (y : ℂ)) (hk ⟨u,hu⟩ (by simp)))
    obtain ⟨j,hj⟩ := norm_zpow_residue_card p z
    rw [ht,hj] at he
    have hpow : (p.asIdeal.absNorm : ℝ)^(-1 : ℤ) = (p.asIdeal.absNorm : ℝ)^(j*2) := by
      simpa only [zpow_neg_one,zpow_mul,zpow_ofNat] using he
    have := (zpow_right_inj₀ (zero_lt_one.trans hq) hq.ne').mp hpow
    omega

/-- The character ηκ² has conductor exponent one after raising to the odd cover degree. -/
def quadraticTwist (b : Datum F 2) {S : Finset (Place F)} (setting : d.ClassicalSetting S) (odd : Odd n)
    (awayTwo : ∀ p : Prime F, Sum.inr p ∉ S → Odd p.asIdeal.absNorm)
    (h : NonzeroInteger S) (hn : ¬ IsUnit h.val) (hs : Squarefree h.val) : Twist (n := n) S h := by
  letI := setting.principal
  let t (p : Prime F) := atPlace (.inr p) (fieldUnit h)
  have hgen (p : modulusPrimes h) : ‖(t p.val).val‖ = (p.val.asIdeal.absNorm : ℝ)⁻¹ := by
    rw [show ‖(t p.val).val‖ = _ from norm_primeOrder p.val ((mem_modulusPrimes h p.val).mp p.property).1 h,
      primeOrder_squarefree h hs p,pow_one]
  exact
    { primes := modulusPrimes h
      outside := fun p hp => ((mem_modulusPrimes h p).mp hp).1
      character := fun p => b.hilbertUnitChar p.val (t p.val) * (d.hilbertUnitChar p.val (t p.val))^2
      continuous_char := fun p => (b.continuous_hilbertUnitChar _ _).mul ((d.continuous_hilbertUnitChar _ _).pow 2)
      exponent := fun _ => 1
      positive := fun _ => Nat.one_pos
      conductor := fun p => by
        erw [d.twist_pow b odd p.val (t p.val)]
        exact quadratic_level_one b _ (awayTwo _ ((mem_modulusPrimes h p.val).mp p.property).1) _ (hgen p)
      generator := fun p => by simpa only [pow_one] using! hgen p
      unit_elsewhere := fun p hp he => by
        change ‖diagonal F (.inr p) (h.val : F)‖ = 1
        rw [norm_primeOrder p hp h,primeOrder_eq_zero_of_not_mem h p hp he,pow_zero]
      empty_modulus := fun he => ((modulusPrimes_nonempty_of_nonunit h hn).ne_empty he).elim }

section
variable (b : Datum F 2) {S : Finset (Place F)} (setting : d.ClassicalSetting S) (odd : Odd n)
  (awayTwo : ∀ p : Prime F, Sum.inr p ∉ S → Odd p.asIdeal.absNorm)
  (h : NonzeroInteger S) (hn : ¬ IsUnit h.val) (hs : Squarefree h.val)
local notation "T" => d.quadraticTwist b setting odd awayTwo h hn hs

theorem quadraticTwist_nonempty : (T).primes.Nonempty :=
  modulusPrimes_nonempty_of_nonunit h hn

theorem quadraticTwist_value (c : Fˣ) :
    twistValue T c = b.residue S c (fieldUnit h) * (d.residue S c (fieldUnit h))^2 := by
  rw [twistValue,b.residue_on_modulus_primes,d.residue_on_modulus_primes,← Finset.prod_pow,← Finset.prod_mul_distrib]
  rw [← Finset.prod_attach (modulusPrimes h)]
  apply Finset.prod_congr rfl
  intro p _
  by_cases hu : ‖diagonal F (.inr p.val) (c : F)‖ = 1
  · rw [if_pos hu,if_pos hu,charWeight,dif_pos (show atPlace (.inr p.val) c ∈ integralUnits p.val from hu)]
    rfl
  · rw [if_neg hu,if_neg hu,charWeight,dif_neg (show atPlace (.inr p.val) c ∉ integralUnits p.val from hu)]
    simp

/-- The two residue factors in the dual summand cancel the cubic or higher odd-order
part of the twist and leave the quadratic character and the S-Hilbert factor. -/
theorem quadraticTwist_dual_value (c : NonzeroInteger S) :
    conj (twistValue T (fieldUnit c)) * d.residue S (fieldUnit c) (fieldUnit h) *
        d.residue S (fieldUnit h) (fieldUnit c) =
      d.sSymbol S (fieldUnit h) (fieldUnit c) * b.residue S (fieldUnit c) (fieldUnit h) := by
  rw [d.quadraticTwist_value b setting odd awayTwo h hn hs,d.residue_reciprocity setting.good h c]
  let Q := b.residue S (fieldUnit c) (fieldUnit h)
  let A := d.residue S (fieldUnit c) (fieldUnit h)
  let H := d.sSymbol S (fieldUnit h) (fieldUnit c)
  change conj (Q * A^2) * A * (H * A) = H * Q
  have qpow := b.residue_pow_degree (fieldUnit c) h
  have apow := d.residue_pow_degree (fieldUnit c) h
  by_cases hu : ∀ p ∈ modulusPrimes h, ‖diagonal F (.inr p) (fieldUnit c : F)‖ = 1
  · have hq : Q^2 = 1 := qpow.trans (if_pos hu)
    have ha : ‖A‖ = 1 := Complex.norm_eq_one_of_pow_eq_one (apow.trans (if_pos hu)) (NeZero.ne n)
    have inv : A * conj A = 1 := by rw [Complex.mul_conj',ha]; norm_num
    have hreal : conj Q = Q := by rcases sq_eq_one_iff.mp hq with e | e <;> simp [e]
    rw [map_mul,map_pow,hreal]
    linear_combination (norm := ring1) H * Q * (A * conj A + 1) * inv
  · have hq : Q = 0 := eq_zero_of_pow_eq_zero (qpow.trans (if_neg hu))
    simp [hq]
end

end MetaplecticPoisson.Datum
