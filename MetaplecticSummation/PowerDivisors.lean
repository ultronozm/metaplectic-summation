import MetaplecticSummation.ResidueCRT

/-! Power divisors of an S-integer in terms of its valuations outside S. -/

noncomputable section
namespace MetaplecticPoisson.Datum

open NumberField IsDedekindDomain WithZero
open Classical
variable {F : Type} [Field F] [NumberField F] {S : Finset (Place F)}

/-- Divisibility of nonzero S-integers is tested at the places outside S. -/
theorem integer_dvd_iff_valuation_le (a b : SIntegers S) (ha : a ≠ 0) :
    a ∣ b ↔ ∀ (p : Prime F), Sum.inr p ∉ S → p.valuation F (b : F) ≤ p.valuation F (a : F) := by
  constructor
  · rintro ⟨k,rfl⟩ p hp
    change p.valuation F ((a : F) * k) ≤ p.valuation F (a : F)
    rw [map_mul]
    exact mul_le_of_le_one_right zero_le (k.property p hp)
  · intro h
    have ha' : (a : F) ≠ 0 := fun he => ha (Subtype.ext he)
    have hi : (b : F) / a ∈ SIntegers S := by
      intro p hp
      rw [map_div₀, div_le_one₀ ((map_ne_zero _).mpr ha' |> bot_lt_iff_ne_bot.mpr)]
      exact h p hp
    exact ⟨⟨_,hi⟩, Subtype.ext (by change (b : F) = a * ((b : F)/a); field_simp)⟩

/-- The exponent of p in the principal ideal of a nonzero S-integer, for p outside S. -/
def primeOrder (p : Prime F) (a : SIntegers S) : ℕ := (-(p.valuation F (a : F)).log).toNat

theorem valuation_primeOrder (p : Prime F) (hp : Sum.inr p ∉ S) (a : NonzeroInteger S) :
    p.valuation F (a.val : F) = exp (-(primeOrder p a.val : ℤ)) := by
  have hn : p.valuation F (a.val : F) ≠ 0 := (map_ne_zero (p.valuation F)).mpr (fieldUnit a).ne_zero
  have hl := a.val.property p hp
  rw [← exp_log hn, ← exp_zero] at hl
  have he := exp_le_exp.mp hl
  rw [primeOrder, Int.toNat_of_nonneg (neg_nonneg.mpr he), neg_neg, exp_log hn]

theorem norm_primeOrder (p : Prime F) (hp : Sum.inr p ∉ S) (a : NonzeroInteger S) :
    ‖diagonal F (.inr p) (a.val : F)‖ = ((p.asIdeal.absNorm : ℝ)⁻¹) ^ primeOrder p a.val := by
  change ‖algebraMap F (p.adicCompletion F) (a.val : F)‖ = _
  have hv : Valued.v (algebraMap F (p.adicCompletion F) (a.val : F)) = p.valuation F (a.val : F) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' p _
  rw [NumberField.FinitePlace.norm_def, hv,
    valuation_primeOrder p hp a, WithZeroMulInt.toNNReal_neg_apply _ (exp_ne_zero (a := _))]
  change (↑((p.asIdeal.absNorm : NNReal) ^ (-(primeOrder p a.val : ℤ))) : ℝ) = _
  simp

private def primeIdealOutside (p : Prime F) (hp : Sum.inr p ∉ S) : Ideal (SIntegers S) where
  carrier := {a | p.valuation F (a : F) < 1}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    exact ((p.valuation F).map_add_le (le_max_left _ _) (le_max_right _ _)).trans_lt (max_lt ha hb)
  smul_mem' := by
    intro a b hb
    change p.valuation F ((a : F) * b) < 1
    rw [map_mul]
    exact (mul_le_of_le_one_left' (a.property p hp)).trans_lt hb

/-- A principal generator at p has valuation one there (in additive notation)
and is a unit at every other prime outside S. -/
theorem exists_prime_generator [IsPrincipalIdealRing (SIntegers S)]
    (p : Prime F) (hp : Sum.inr p ∉ S) :
    ∃ t : NonzeroInteger S, p.valuation F (t.val : F) = exp (-1 : ℤ) ∧
      ∀ q : Prime F, Sum.inr q ∉ S → q ≠ p → q.valuation F (t.val : F) = 1 := by
  let I := primeIdealOutside p hp
  let t := Submodule.IsPrincipal.generator I
  have ht : t ∈ I := by
    rw [← Ideal.span_singleton_generator I]
    exact Ideal.mem_span_singleton_self _
  have hd (a : SIntegers S) (ha : p.valuation F (a : F) < 1) : t ∣ a :=
    Ideal.mem_span_singleton.mp (Ideal.span_singleton_generator I ▸ (show a ∈ I from ha))
  have hlt : p.valuation F (t : F) < 1 := ht
  obtain ⟨r,hr⟩ := p.valuation_exists_uniformizer' F
  let a := algebraMap (𝓞 F) (SIntegers S) r
  have he : p.valuation F (a : F) = exp (-1 : ℤ) := hr
  have hrlt : exp (-1 : ℤ) < 1 := exp_lt_exp.mpr (show (-1 : ℤ) < 0 by decide)
  have hta := hd a (he ▸ hrlt)
  have ht0 : t ≠ 0 := by
    rintro hz
    have ha := zero_dvd_iff.mp (hz ▸ hta)
    exact exp_ne_zero (a := (-1 : ℤ)) (he.symm.trans (by simp [ha]))
  have hle := (integer_dvd_iff_valuation_le t a ht0).mp hta p hp
  rw [he] at hle
  refine ⟨⟨t,ht0⟩, le_antisymm ?_ hle, ?_⟩
  · rw [valuation_primeOrder p hp ⟨t,ht0⟩] at hlt ⊢
    exact exp_le_exp.mpr (by have := exp_lt_exp.mp (show _ < exp (0 : ℤ) from hlt); omega)
  · intro q hq hqp
    have hnot : ¬ p.asIdeal ≤ q.asIdeal :=
      fun h => hqp (HeightOneSpectrum.ext (p.isMaximal.eq_of_le q.isPrime.ne_top h)).symm
    obtain ⟨z,hz,hzq⟩ := Set.not_subset.mp hnot
    let a' := algebraMap (𝓞 F) (SIntegers S) z
    have ha' : p.valuation F (a' : F) < 1 := (p.valuation_lt_one_iff_mem (K := F) z).mpr hz
    have hunit : q.valuation F (a' : F) = 1 := (q.valuation_eq_one_iff_notMem (K := F)).mpr hzq
    exact le_antisymm (t.property q hq)
      (hunit ▸ (integer_dvd_iff_valuation_le t a' ht0).mp (hd a' ha') q hq)

theorem pow_dvd_iff_primeOrder (a c : NonzeroInteger S) (n : ℕ) :
    a.val ^ n ∣ c.val ↔ ∀ p : Prime F, Sum.inr p ∉ S →
      primeOrder p a.val * n ≤ primeOrder p c.val := by
  rw [integer_dvd_iff_valuation_le _ _ (pow_ne_zero _ a.property)]
  apply forall_congr'
  intro p
  apply forall_congr'
  intro hp
  change p.valuation F (c.val : F) ≤ p.valuation F ((a.val : F) ^ n) ↔ _
  rw [map_pow, valuation_primeOrder p hp a, valuation_primeOrder p hp c,
    ← exp_nsmul, exp_le_exp, nsmul_eq_mul]
  rw [mul_neg, neg_le_neg_iff, mul_comm]
  exact_mod_cast Iff.rfl

theorem associated_iff_primeOrder (a b : NonzeroInteger S) :
    Associated a.val b.val ↔ ∀ p : Prime F, Sum.inr p ∉ S → primeOrder p a.val = primeOrder p b.val := by
  have hd (x y : NonzeroInteger S) : x.val ∣ y.val ↔
      ∀ p : Prime F, Sum.inr p ∉ S → primeOrder p x.val ≤ primeOrder p y.val := by
    simpa only [pow_one,mul_one] using pow_dvd_iff_primeOrder x y 1
  rw [← dvd_dvd_iff_associated, hd, hd]
  exact ⟨fun ⟨h₁,h₂⟩ p hp => le_antisymm (h₁ p hp) (h₂ p hp),
    fun h => ⟨fun p hp => (h p hp).le,fun p hp => (h p hp).ge⟩⟩

theorem primeOrder_eq_zero_of_not_mem (c : NonzeroInteger S) (p : Prime F)
    (hp : Sum.inr p ∉ S) (hc : p ∉ modulusPrimes c) : primeOrder p c.val = 0 := by
  by_contra hn
  apply hc
  refine (mem_modulusPrimes c p).mpr ⟨hp,?_⟩
  rw [norm_primeOrder p hp c]
  have hq : 1 < (p.asIdeal.absNorm : ℝ) := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm p
  exact pow_lt_one₀ (by positivity) (inv_lt_one_of_one_lt₀ hq) hn

/-- Over a principal ring of S-integers, an orthogonal power class with
integral-unit representatives outside S is detected at the places of S. -/
theorem eq_one_of_orthogonal_of_principal_sIntegers {n : ℕ} [NeZero n] (d : Datum F n)
    [IsPrincipalIdealRing (SIntegers S)] (x : AdelicPowerClass n F) (hx : x ∈ d.rationalOrthogonal)
    (hS : ∀ v ∈ S, adelicClassAt n v x = 1) (hinf : ∀ w : InfinitePlace F, Sum.inl w ∈ S)
    (ht : ∀ p : Prime F, Sum.inr p ∉ S → p.asIdeal.absNorm.Coprime n)
    (hu : ∀ p : Prime F, Sum.inr p ∉ S →
      ∃ u : (LocalField F (.inr p))ˣ, ‖u.val‖ = 1 ∧ QuotientGroup.mk u = adelicClassAt n (.inr p) x) :
    x = 1 := by
  apply d.eq_one_of_orthogonal_of_unit_outside S x hx hS hinf ht hu
  intro p hp
  obtain ⟨t,htp,htq⟩ := exists_prime_generator p hp
  refine ⟨fieldUnit t, ?_, fun q hq hne => ?_⟩
  · change ‖diagonal F (.inr p) (t.val : F)‖ = _
    rw [norm_primeOrder p hp t]
    simp [primeOrder,htp]
  · change ‖diagonal F (.inr q) (t.val : F)‖ = _
    rw [norm_primeOrder q hq t]
    simp [primeOrder,htq q hq hne]

section PID
variable [IsPrincipalIdealRing (SIntegers S)] (c : NonzeroInteger S)

abbrev DivisorExponents (n : ℕ) := (p : modulusPrimes c) → Fin (primeOrder p.val c.val / n + 1)

def primeGenerator (p : Prime F) (hp : Sum.inr p ∉ S) := (exists_prime_generator p hp).choose

omit [IsPrincipalIdealRing (SIntegers S)] in
/-- A nonunit modulus has a prime divisor outside S. -/
theorem modulusPrimes_nonempty_of_nonunit (hn : ¬ IsUnit c.val) : (modulusPrimes c).Nonempty := by
  by_contra he
  apply hn
  apply isUnit_iff_dvd_one.mpr
  apply (integer_dvd_iff_valuation_le c.val 1 c.property).mpr
  intro p hp
  have h := primeOrder_eq_zero_of_not_mem c p hp (fun h => he ⟨p,h⟩)
  rw [valuation_primeOrder p hp c,h]
  simp

/-- Every prime in a squarefree modulus has valuation exponent one. -/
theorem primeOrder_squarefree (h : Squarefree c.val) (p : modulusPrimes c) :
    primeOrder p.val c.val = 1 := by
  obtain ⟨hp,hl⟩ := (mem_modulusPrimes c p.val).mp p.property
  have hpos : primeOrder p.val c.val ≠ 0 := by
    intro hz
    rw [norm_primeOrder p.val hp c,hz,pow_zero] at hl
    exact hl.false
  by_contra hne
  have htwo : 2 ≤ primeOrder p.val c.val := by omega
  obtain ⟨t,ht,ht'⟩ := exists_prime_generator p.val hp
  have hd : t.val * t.val ∣ c.val := by
    apply (integer_dvd_iff_valuation_le _ _ (mul_ne_zero t.property t.property)).mpr
    intro q hq
    change q.valuation F (c.val : F) ≤ q.valuation F ((t.val : F)*(t.val : F))
    rw [map_mul]
    by_cases he : q = p.val
    · subst q
      rw [valuation_primeOrder p.val hp c, ht, ← exp_add, exp_le_exp]
      omega
    · rw [ht' q hq he,one_mul]
      exact c.val.property q hq
  have htunit := h t.val hd
  have hl' := (integer_dvd_iff_valuation_le t.val 1 t.property).mp htunit.dvd p.val hp
  rw [ht,Subalgebra.coe_one,map_one] at hl'
  change (1 : WithZero (Multiplicative ℤ)) ≤ exp (-1 : ℤ) at hl'
  exact (exp_lt_exp.mpr (show (-1 : ℤ) < 0 by decide)).not_ge hl'

/-- A representative for the divisor with the given finite tuple of prime exponents. -/
def divisorMonomial (k : modulusPrimes c → ℕ) : NonzeroInteger S :=
  ⟨∏ p : modulusPrimes c,
    (primeGenerator p.val ((mem_modulusPrimes c p.val).mp p.property).1).val ^ k p,
    Finset.prod_ne_zero_iff.mpr fun _ _ => pow_ne_zero _ (primeGenerator _ _).property⟩

theorem primeOrder_divisorMonomial (k : modulusPrimes c → ℕ) (q : Prime F) (hq : Sum.inr q ∉ S) :
    primeOrder q (divisorMonomial c k).val = if h : q ∈ modulusPrimes c then k ⟨q,h⟩ else 0 := by
  let e := (q.valuation F).toMonoidWithZeroHom.toMonoidHom.comp (algebraMap (SIntegers S) F).toMonoidHom
  let t (p : modulusPrimes c) := primeGenerator p.val ((mem_modulusPrimes c p.val).mp p.property).1
  have he (p : modulusPrimes c) (hn : p.val ≠ q) : e (t p).val = 1 :=
    (exists_prime_generator p.val ((mem_modulusPrimes c p.val).mp p.property).1).choose_spec.2 q hq (Ne.symm hn)
  have hv := valuation_primeOrder q hq (divisorMonomial c k)
  change e (∏ p : modulusPrimes c, (t p).val ^ k p) = _ at hv
  rw [map_prod] at hv
  simp_rw [map_pow] at hv
  by_cases h : q ∈ modulusPrimes c
  · let j : modulusPrimes c := ⟨q,h⟩
    rw [Finset.prod_eq_single j (fun i _ hij => by
      rw [he i (fun hx => hij (Subtype.ext hx)),one_pow]) (by simp),
      show e (t j).val = exp (-1 : ℤ) from (exists_prime_generator q hq).choose_spec.1,
      ← exp_nsmul] at hv
    have hg := exp_injective hv
    simp only [dif_pos h]
    change primeOrder q (divisorMonomial c k).val = k j
    simpa using (congrArg Int.toNat (congrArg Neg.neg hg.symm))
  · rw [Finset.prod_eq_one (fun p _ => by
      rw [he p (fun hx => h (hx ▸ p.property)),one_pow])] at hv
    have hg := exp_injective (show exp (0 : ℤ) = _ from hv)
    simp only [dif_neg h]
    omega

theorem divisorMonomial_pow_dvd {n : ℕ} [NeZero n] (k : DivisorExponents c n) :
    (divisorMonomial c (fun p => (k p).val)).val ^ n ∣ c.val := by
  apply (pow_dvd_iff_primeOrder _ _ n).mpr
  intro p hp
  rw [primeOrder_divisorMonomial c _ p hp]
  split_ifs with h
  · exact (Nat.le_div_iff_mul_le (NeZero.pos n)).mp (Nat.le_of_lt_succ (k ⟨p,h⟩).isLt)
  · simp

/-- Tuples of local exponents bounded by v(c)/n enumerate the global n-th
power divisors of c up to multiplication by S-units. -/
def powerDivisorEquiv (n : ℕ) [NeZero n] :
    DivisorExponents c n ≃ {t : Associates (SIntegers S) // t^n ∣ Associates.mk c.val} := by
  let m (k : DivisorExponents c n) := divisorMonomial c (fun p => (k p).val)
  let f (k : DivisorExponents c n) : {t : Associates (SIntegers S) // t^n ∣ Associates.mk c.val} :=
    ⟨Associates.mk (m k).val, by rw [← Associates.mk_pow,Associates.mk_dvd_mk]; exact divisorMonomial_pow_dvd c k⟩
  refine Equiv.ofBijective f ⟨?_,?_⟩
  · intro j k hj
    have he : Associated (m j).val (m k).val :=
      Associates.mk_eq_mk_iff_associated.mp (congrArg Subtype.val hj)
    funext p
    apply Fin.ext
    have ho := (associated_iff_primeOrder _ _).mp he p.val ((mem_modulusPrimes c p.val).mp p.property).1
    dsimp only [m] at ho
    rwa [primeOrder_divisorMonomial c _ p.val ((mem_modulusPrimes c p.val).mp p.property).1,
      primeOrder_divisorMonomial c _ p.val ((mem_modulusPrimes c p.val).mp p.property).1, dif_pos p.property, dif_pos p.property] at ho
  · rintro ⟨t,ht⟩
    obtain ⟨a,rfl⟩ := Associates.mk_surjective t
    rw [← Associates.mk_pow,Associates.mk_dvd_mk] at ht
    have ha : a ≠ 0 := fun hz => c.property (zero_dvd_iff.mp (by simpa [hz,zero_pow (NeZero.ne n)] using ht))
    let a' : NonzeroInteger S := ⟨a,ha⟩
    have bound := (pow_dvd_iff_primeOrder a' c n).mp ht
    let k (p : modulusPrimes c) : Fin (primeOrder p.val c.val / n + 1) :=
      ⟨primeOrder p.val a, Nat.lt_succ_of_le ((Nat.le_div_iff_mul_le (NeZero.pos n)).mpr
        (bound p.val ((mem_modulusPrimes c p.val).mp p.property).1))⟩
    refine ⟨k, Subtype.ext (Associates.mk_eq_mk_iff_associated.mpr ((associated_iff_primeOrder (m k) a').mpr ?_))⟩
    intro p hp
    rw [show primeOrder p (m k).val = _ from primeOrder_divisorMonomial c _ p hp]
    split_ifs with h
    · rfl
    · have hb := bound p hp
      rw [primeOrder_eq_zero_of_not_mem c p hp h] at hb
      exact ((mul_eq_zero.mp (Nat.eq_zero_of_le_zero hb)).resolve_right (NeZero.ne n)).symm

end PID
end MetaplecticPoisson.Datum
