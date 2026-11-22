import MetaplecticSummation.ResidueCRT

/-! Reciprocity of power residue symbols in the normalization of §10. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField IsDedekindDomain Set
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

/-- A residue symbol is a root of unity on units modulo the modulus and zero otherwise. -/
theorem residue_pow_degree {S : Finset (Place F)} (c : Fˣ) (h : NonzeroInteger S) :
    (d.residue S c (fieldUnit h))^n = if ∀ p ∈ modulusPrimes h, ‖diagonal F (.inr p) (c : F)‖ = 1 then 1 else 0 := by
  rw [d.residue_on_modulus_primes]
  split_ifs with hu
  · rw [← Finset.prod_pow]
    apply Finset.prod_eq_one
    intro p hp
    rw [if_pos (hu p hp)]
    exact congrArg Units.val (d.unitPairing_pow (.inr p) (atPlace _ (fieldUnit h)) (atPlace _ c))
  · push_neg at hu
    obtain ⟨p,hp,hu⟩ := hu
    rw [Finset.prod_eq_zero hp (if_neg hu),zero_pow (NeZero.ne n)]

set_option maxHeartbeats 800000 in
/-- Interchanging two nonzero integral arguments inserts the product of the
Hilbert symbols at S. Both sides vanish if the arguments share a prime outside S. -/
theorem residue_reciprocity {S : Finset (Place F)} (hS : d.GoodOutside S) (a b : NonzeroInteger S) :
    d.residue S (fieldUnit a) (fieldUnit b) =
      d.sSymbol S (fieldUnit a) (fieldUnit b) * d.residue S (fieldUnit b) (fieldUnit a) := by
  let U := modulusPrimes a ∪ modulusPrimes b
  let H (v : Place F) := d.symbol v (atPlace v (fieldUnit a)) (atPlace v (fieldUnit b))
  let R (x y : NonzeroInteger S) (p : Prime F) :=
    if p ∈ modulusPrimes y then
      if ‖diagonal F (.inr p) (fieldUnit x : F)‖ = 1 then
        d.symbol (.inr p) (atPlace _ (fieldUnit y)) (atPlace _ (fieldUnit x)) else 0 else 1
  have prod (x y : NonzeroInteger S) (hy : modulusPrimes y ⊆ U) :
      d.residue S (fieldUnit x) (fieldUnit y) = ∏ p ∈ U, R x y p := by
    rw [d.residue_on_modulus_primes]
    calc
      _ = ∏ p ∈ modulusPrimes y, R x y p := Finset.prod_congr rfl fun p hp => by simp only [R,if_pos hp]
      _ = _ := Finset.prod_subset hy fun p _ hp => if_neg hp
  have unit (x : NonzeroInteger S) (p : Prime F) (hp : Sum.inr p ∉ S) (hx : p ∉ modulusPrimes x) :
      ‖diagonal F (.inr p) (fieldUnit x : F)‖ = 1 :=
    (integer_norm_le_one x.val p hp).eq_of_not_lt fun hl => hx ((mem_modulusPrimes x p).mpr ⟨hp,hl⟩)
  have outside (p : Prime F) (hp : p ∈ U) : Sum.inr p ∉ S := by
    rcases Finset.mem_union.mp hp with h | h
    · exact ((mem_modulusPrimes a p).mp h).1
    · exact ((mem_modulusPrimes b p).mp h).1
  have localEq (p : Prime F) (hp : p ∈ U) : R a b p * H (.inr p) = R b a p := by
    by_cases ha : p ∈ modulusPrimes a
    · have ha' := ((mem_modulusPrimes a p).mp ha).2.ne
      by_cases hb : p ∈ modulusPrimes b
      · have hb' := ((mem_modulusPrimes b p).mp hb).2.ne
        simp [R,ha,hb,ha',hb',fieldUnit]
      · simp only [R,if_pos ha,if_neg hb,if_pos (unit b p (outside p hp) hb),one_mul,H]
    · have hb := (Finset.mem_union.mp hp).resolve_left ha
      simp only [R,if_neg ha,if_pos hb,if_pos (unit a p (outside p hp) ha)]
      let e := (Units.coeHom ℂ).comp d.embedding
      have hs := (congrArg e (d.family_spec.skew (.inr p) (atPlace _ (fieldUnit b)) (atPlace _ (fieldUnit a)))).trans e.map_one
      rw [map_mul] at hs
      exact hs
  let I := U.image (Sum.inr : Prime F → Place F)
  have hdis : Disjoint S I := by
    apply Finset.disjoint_left.mpr
    rintro v hv hi
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hi
    exact outside p hp hv
  have hsup : Function.mulSupport H ⊆ ((S ∪ I : Finset (Place F)) : Set (Place F)) := by
    intro v hv
    by_contra hn
    have hs : v ∉ S := fun h => hn (Finset.mem_union_left _ h)
    obtain w | p := v
    · exact hs (hS.2.1 w)
    · have hU : p ∉ U := fun hp => hn (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hp))
      have ha := unit a p hs (fun h => hU (Finset.mem_union_left _ h))
      have hb := unit b p hs (fun h => hU (Finset.mem_union_right _ h))
      have he := d.unitPairing_tame_units p (hS.2.2 p hs).1 (atPlace _ (fieldUnit a)) (atPlace _ (fieldUnit b)) ha hb
      exact hv (congrArg (fun z : ℂˣ => z.val) he)
  have hrec := (d.symbol_reciprocity (fieldUnit a) (fieldUnit b)).2
  change ∏ᶠ v, H v = 1 at hrec
  rw [finprod_eq_prod_of_mulSupport_subset _ hsup,Finset.prod_union hdis,Finset.prod_image
    (fun _ _ _ _ h => Sum.inr.inj h)] at hrec
  have factor : (∏ p ∈ U, R a b p) * (∏ p ∈ U, H (.inr p)) = ∏ p ∈ U, R b a p := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl localEq
  rw [prod a b Finset.subset_union_right,prod b a Finset.subset_union_left,← factor]
  change _ = (∏ v ∈ S, H v) * _
  rw [mul_left_comm,hrec,mul_one]

end MetaplecticPoisson.Datum
