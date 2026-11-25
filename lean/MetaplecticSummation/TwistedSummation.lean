import MetaplecticSummation.TwistedWeights

/-! Adelic line summation with a finite set of ramified unit-character components. -/

noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n]
variable {S : Finset (Place F)} {f : NonzeroInteger S}

namespace Twist
variable (T : Twist (n := n) S f)

/-- Places of the original test weight together with the primes of the twist. -/
def places := S ∪ T.primes.image (Sum.inr : Prime F → Place F)

omit [NeZero n] in
theorem finite_mem_places (p : Prime F) : Sum.inr p ∈ T.places ↔ Sum.inr p ∈ S ∨ p ∈ T.primes := by
  simp [places]

omit [NeZero n] in
theorem infinite_mem_places (w : InfinitePlace F) : Sum.inl w ∈ T.places ↔ Sum.inl w ∈ S := by
  simp [places]

omit [NeZero n] in
theorem good_places {d : Datum F n} (h : d.GoodOutside S) : d.GoodOutside T.places :=
  ⟨h.1.mono Finset.subset_union_left,fun w => (T.infinite_mem_places w).mpr (h.2.1 w),
    fun p hp => h.2.2 p (fun hs => hp ((T.finite_mem_places p).mpr (Or.inl hs)))⟩

def weights (W : Weights S) : Weights T.places
  | ⟨.inl w,hw⟩ => W ⟨.inl w,(T.infinite_mem_places w).mp hw⟩
  | ⟨.inr p,hp⟩ => if h : Sum.inr p ∈ S then W ⟨_,h⟩ else
      charWeight (T.character ⟨p,((T.finite_mem_places p).mp hp).resolve_left h⟩)

omit [NeZero n] in
theorem weights_at_prime (W : Weights S) (p : T.primes) :
    T.weights W ⟨.inr p.val,(T.finite_mem_places p.val).mpr (Or.inr p.property)⟩ =
      charWeight (T.character p) := dif_neg (T.outside p.val p.property)

theorem admissible_weights (W : Weights S) (hW : Admissible W) : Admissible (T.weights W) := by
  rintro ⟨w | p,hp⟩
  · exact hW _
  · by_cases hs : Sum.inr p ∈ S
    · simpa only [weights,dif_pos hs] using hW ⟨.inr p,hs⟩
    · let i : T.primes := ⟨p,((T.finite_mem_places p).mp hp).resolve_left hs⟩
      rw [weights,dif_neg hs]
      exact charWeight_test p (T.character i) (T.continuous_char i) (T.exponent i) (T.conductor i).1

end Twist

/-- With a nonempty conductor the adelic line identity at S ∪ T has no
power-class main term. Both its series converge absolutely. -/
theorem twisted_lineSummation (d : Datum F n) (h : d.ClassicalSetting S)
    (b : NonzeroInteger S) (T : Twist (n := n) S f) (hT : T.primes.Nonempty)
    (W : Weights S) (hW : Admissible W) :
    let db := d.scaled (fieldUnit b)
    let V := T.weights W
    Summable (fun c => ‖db.globalWeight V false c‖) ∧
      Summable (fun c => ‖db.globalWeight V true c‖) ∧
      (∑' c, db.globalWeight V false c) = ∑' c, db.globalWeight V true c := by
  let db := d.scaled (fieldUnit b)
  let L := db.lineSummation T.places (T.good_places (d.scaled_good h b))
  obtain ⟨hp₁,hp₂,hs⟩ := L.exists.choose_spec (T.weights W) (T.admissible_weights W hW)
  refine ⟨hp₁,hp₂,?_⟩
  obtain ⟨p,hp⟩ := hT
  let i : T.primes := ⟨p,hp⟩
  have hz (β : Classes n T.places) : db.moment (T.weights W) β = 0 :=
    db.moment_eq_zero_of_twistedComponent (T.weights W) p ((T.finite_mem_places p).mpr (Or.inr hp))
      (T.character i) (T.exponent i) (T.positive i) (T.conductor i) (T.weights_at_prime W i) β
  simpa only [hz,mul_zero,finsum_zero,add_zero] using hs

omit [NeZero n] in
/-- The primes of the twist are exactly the primes of the conductor modulus outside S. -/
theorem Twist.primes_eq_modulusPrimes (T : Twist (n := n) S f) : T.primes = modulusPrimes f := by
  ext p
  rw [mem_modulusPrimes]
  constructor
  · intro hp
    let i : T.primes := ⟨p,hp⟩
    have hq : 1 < (p.asIdeal.absNorm : ℝ) := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm p
    exact ⟨T.outside p hp,(T.generator i).trans_lt (inv_lt_one_of_one_lt₀ (one_lt_pow₀ hq (T.positive i).ne'))⟩
  · rintro ⟨hp,hl⟩
    exact by_contra fun ht => hl.ne (T.unit_elsewhere p hp ht)

/-- At the conductor primes the product of transformed weights contributes ε,
the conjugate twist, and the residue symbol with denominator f. -/
theorem conductor_product (d : Datum F n) (h : d.ClassicalSetting S) (b : NonzeroInteger S)
    (T : Twist (n := n) S f) (hb : IsCoprime b.val f.val) (c : Fˣ) :
    (∏ p : T.primes, (d.scaled (fieldUnit b)).dualWeight (.inr p.val) (charWeight (T.character p))
      (atPlace _ (c/(fieldUnit b^n * fieldUnit f^(n-1))))) =
    d.epsilon T (fieldUnit b) * (starRingEnd ℂ) (twistValue T c) * d.residue S c (fieldUnit f) := by
  let H (p : T.primes) := d.symbol (.inr p.val) (atPlace _ (fieldUnit f)) (atPlace _ c)
  have eqProd :
      (∏ p : T.primes, (d.scaled (fieldUnit b)).dualWeight (.inr p.val) (charWeight (T.character p))
        (atPlace _ (c/(fieldUnit b^n * fieldUnit f^(n-1))))) =
      d.epsilon T (fieldUnit b) * (starRingEnd ℂ) (twistValue T c) * ∏ p : T.primes, H p := by
    unfold epsilon twistValue
    rw [map_prod,← Finset.prod_mul_distrib,← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p _
    simpa only [atPlace,map_div,map_mul,map_pow,map_inv,H] using
      d.dual_conductor_factor h f b T hb p (atPlace (.inr p.val) c)
  rw [eqProd]
  by_cases ht : twistValue T c = 0
  · simp [ht]
  congr 1
  symm
  unfold residue
  rw [finprod_eq_prod_of_mulSupport_subset (s := T.primes) _ (by
    intro p hp
    by_contra hn
    exact hp (if_neg fun hh => hn (T.primes_eq_modulusPrimes ▸ (mem_modulusPrimes f p).mpr hh)))]
  rw [← Finset.prod_attach T.primes]
  apply Finset.prod_congr rfl
  intro p _
  have hf : Sum.inr p.val ∉ S ∧ ‖diagonal F (.inr p.val) (fieldUnit f : F)‖ < 1 :=
    (mem_modulusPrimes f p.val).mp (T.primes_eq_modulusPrimes ▸ p.property)
  have hc : ‖diagonal F (.inr p.val) (c : F)‖ = 1 := by
    by_contra hnu
    apply ht
    apply Finset.prod_eq_zero (Finset.mem_univ p)
    exact dif_neg (show atPlace (.inr p.val) c ∉ integralUnits p.val from hnu)
  rw [if_pos hf,dif_pos ⟨c.ne_zero,(fieldUnit f).ne_zero,hc⟩]
  change d.symbol (.inr p.val) (atPlace _ (Units.mk0 _ _)) (atPlace _ (Units.mk0 _ _)) = H p
  rw [show Units.mk0 (c : F) c.ne_zero = c from Units.ext rfl]
  rfl

end MetaplecticPoisson.Datum
