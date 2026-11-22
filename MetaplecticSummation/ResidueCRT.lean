import MetaplecticSummation.LocalGauss

/-! The Chinese remainder decomposition of the S-integer residue ring
into the local rings occurring in the Gauss sum. -/

noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField IsDedekindDomain Filter Set
open Classical
variable {F : Type} [Field F] [NumberField F]

/-- The finite primes outside S dividing the nonzero modulus c. -/
def modulusPrimes {S : Finset (Place F)} (c : NonzeroInteger S) : Finset (Prime F) :=
  ((eventually_cofinite.mp (eventually_diagonal_norm_one (fieldUnit c).ne_zero)).toFinset).filter
    fun p => Sum.inr p ∉ S

theorem mem_modulusPrimes {S : Finset (Place F)} (c : NonzeroInteger S) (p : Prime F) :
    p ∈ modulusPrimes c ↔ Sum.inr p ∉ S ∧ ‖diagonal F (.inr p) c.val‖ < 1 := by
  simp only [modulusPrimes,Finset.mem_filter,Set.Finite.mem_toFinset,Set.mem_setOf_eq]
  change (‖diagonal F (.inr p) c.val‖ ≠ 1 ∧ _) ↔ _
  exact ⟨fun ⟨hne, hp⟩ => ⟨hp,lt_of_le_of_ne (integer_norm_le_one c.val p hp) hne⟩,
    fun ⟨hp,hl⟩ => ⟨hl.ne,hp⟩⟩

def toLocalInteger {S : Finset (Place F)} (p : Prime F) (hp : Sum.inr p ∉ S) :
    SIntegers S →+* p.adicCompletionIntegers F where
  toFun a := ⟨diagonal F (.inr p) a,(mem_localIntegers_iff p _).mpr (integer_norm_le_one a p hp)⟩
  map_zero' := Subtype.ext (map_zero _)
  map_one' := Subtype.ext (map_one _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

variable {S : Finset (Place F)} (c : NonzeroInteger S)

abbrev localModulus (p : modulusPrimes c) :=
  toLocalInteger p.val ((mem_modulusPrimes c p.val).mp p.property).1 c.val

abbrev LocalResidue (p : modulusPrimes c) :=
  p.val.adicCompletionIntegers F ⧸ Ideal.span {localModulus c p}

def localReduction (p : modulusPrimes c) : SIntegers S →+* LocalResidue c p :=
  (Ideal.Quotient.mk _).comp (toLocalInteger p.val ((mem_modulusPrimes c p.val).mp p.property).1)

theorem localReduction_eq_iff (p : modulusPrimes c) (a b : SIntegers S) :
    localReduction c p a = localReduction c p b ↔
      diagonal F (.inr p.val) (((a : F)-b)/c.val) ∈ p.val.adicCompletionIntegers F := by
  let e := toLocalInteger p.val ((mem_modulusPrimes c p.val).mp p.property).1
  have hc : (e c.val : p.val.adicCompletion F) ≠ 0 :=
    (map_ne_zero (diagonal F (.inr p.val))).mpr (fieldUnit c).ne_zero
  rw [map_div₀,map_sub]
  exact localResidues_eq_iff p.val (e c.val) (e a) (e b) hc

/-- Simultaneous reduction at the prime powers dividing c. -/
def residueReduction : (SIntegers S ⧸ Ideal.span {c.val}) →+* ((p : modulusPrimes c) → LocalResidue c p) :=
  let f := RingHom.pi fun p => localReduction c p
  Ideal.Quotient.lift _ f (by
    intro x hx
    obtain ⟨k,rfl⟩ := Ideal.mem_span_singleton.mp hx
    apply funext
    intro p
    change localReduction c p (c.val*k) = 0
    rw [map_mul, show localReduction c p c.val = 0 from
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self (localModulus c p)),zero_mul])

@[simp] theorem residueReduction_mk (a : SIntegers S) (p : modulusPrimes c) :
    residueReduction c (Ideal.Quotient.mk _ a) p = localReduction c p a := rfl

theorem residueReduction_injective : Function.Injective (residueReduction c) := by
  intro a b hab
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b,rfl⟩ := Ideal.Quotient.mk_surjective b
  let k := ((a : F)-b)/c.val
  have hk : k ∈ SIntegers S := by
    intro p hp
    apply (diagonal_norm_le_one_iff k p).mp
    by_cases h : p ∈ modulusPrimes c
    · exact (mem_localIntegers_iff p _).mp ((localReduction_eq_iff c ⟨p,h⟩ a b).mp (congrFun hab ⟨p,h⟩))
    · have hn : ‖diagonal F (.inr p) c.val‖ = 1 :=
        le_antisymm (integer_norm_le_one c.val p hp) (le_of_not_gt fun hl => h ((mem_modulusPrimes c p).mpr ⟨hp,hl⟩))
      rw [show k = ((a-b : SIntegers S) : F) / c.val from rfl,map_div₀,norm_div,hn,div_one]
      exact integer_norm_le_one (a-b) p hp
  apply Ideal.Quotient.eq.mpr
  apply Ideal.mem_span_singleton.mpr
  refine ⟨⟨k,hk⟩,Subtype.ext ?_⟩
  change (a : F)-b = (c.val : F)*(((a : F)-b)/c.val)
  have hc : (c.val : F) ≠ 0 := (fieldUnit c).ne_zero
  field_simp

theorem residueReduction_surjective : Function.Surjective (residueReduction c) := by
  classical
  intro y
  let T := modulusPrimes c
  let z (p : T) : p.val.adicCompletionIntegers F := Quotient.out (y p)
  let e (p : Prime F) : F →+* p.adicCompletion F := diagonal F (.inr p)
  let x (p : Prime F) : p.adicCompletion F :=
    if h : p ∈ T then ((z ⟨p,h⟩ : p.adicCompletionIntegers F) : p.adicCompletion F) / e p c.val else 0
  let A : FiniteAdeleRing (𝓞 F) F := ⟨x,(Finset.eventually_cofinite_notMem T).mono fun p hp => by
    rw [show x p = 0 from dif_neg hp]
    exact (p.adicCompletionIntegers F).zero_mem⟩
  obtain ⟨k,hk⟩ := AdeleLattice.exists_sub_mem_integralFiniteAdeles A
  have hnear (p : Prime F) : x p - e p k ∈ p.adicCompletionIntegers F := hk p
  have hc (p : Prime F) : e p c.val ≠ 0 := (map_ne_zero _).mpr (fieldUnit c).ne_zero
  have hdiff (p : Prime F) (hp : p ∈ T) :
      ((z ⟨p,hp⟩ : p.adicCompletionIntegers F) : p.adicCompletion F) - e p ((c.val : F)*k) =
        e p c.val * (x p - e p k) := by
    rw [map_mul]
    change _ - (e p c.val : p.adicCompletion F) * e p k = (e p c.val : p.adicCompletion F) * _
    simp only [x,dif_pos hp,mul_sub]
    field_simp [hc p]
  have ha : (c.val : F)*k ∈ SIntegers S := by
    intro p hp
    apply (diagonal_norm_le_one_iff _ p).mp
    apply (mem_localIntegers_iff p _).mp
    change e p ((c.val : F)*k) ∈ (p.adicCompletionIntegers F).toSubring
    have hcO : e p c.val ∈ p.adicCompletionIntegers F := (toLocalInteger p hp c.val).property
    by_cases h : p ∈ T
    · have hh := (p.adicCompletionIntegers F).toSubring.mul_mem hcO (hnear p)
      rw [← hdiff p h] at hh
      simpa only [sub_sub_cancel] using (p.adicCompletionIntegers F).toSubring.sub_mem (z ⟨p,h⟩).property hh
    · have hh := hnear p
      rw [show x p = 0 by simp [x,h],zero_sub] at hh
      rw [map_mul]
      exact (p.adicCompletionIntegers F).toSubring.mul_mem hcO ((p.adicCompletionIntegers F).toSubring.neg_mem_iff.mp hh)
  let a : SIntegers S := ⟨_,ha⟩
  refine ⟨Ideal.Quotient.mk _ a,funext fun p => ?_⟩
  have hq : Ideal.Quotient.mk _ (z p) = y p := Quotient.out_eq _
  apply Eq.trans _ hq
  let ep := toLocalInteger p.val ((mem_modulusPrimes c p.val).mp p.property).1
  apply (localResidues_eq_iff p.val (ep c.val) (ep a) (z p) (hc p.val)).mpr
  have he : ((ep a : p.val.adicCompletion F) - (z p : p.val.adicCompletion F)) / (ep c.val : p.val.adicCompletion F) =
      -(x p.val - e p.val k) := by
    change (e p.val ((c.val : F)*k) - _) / (e p.val c.val : p.val.adicCompletion F) = _
    apply (div_eq_iff (hc p.val)).mpr
    linear_combination -(hdiff p.val p.property)
  rw [he]
  exact (p.val.adicCompletionIntegers F).toSubring.neg_mem (hnear p.val)

def residueCRT : (SIntegers S ⧸ Ideal.span {c.val}) ≃+* ((p : modulusPrimes c) → LocalResidue c p) :=
  RingEquiv.ofBijective (residueReduction c) ⟨residueReduction_injective c,residueReduction_surjective c⟩

section Character
variable {n : ℕ} [NeZero n] (d : Datum F n)

omit [NeZero n] in
/-- The phase at S for a/c is the product of the negative local phases
at the finite primes dividing c. -/
theorem sPsi_fraction (hS : d.GoodOutside S) (a : SIntegers S) :
    d.sPsi S ((a : F)/c.val) = ∏ p : modulusPrimes c,
      d.character.localValue F (.inr p.val) (-(diagonal F (.inr p.val) ((a : F)/c.val))) := by
  let x := (a : F)/c.val
  let χ (v : Place F) := d.character.localValue F v (diagonal F v x)
  let T := modulusPrimes c
  let i : Prime F ↪ Place F := ⟨Sum.inr, Sum.inr_injective⟩
  have hdis : Disjoint S (T.map i) := by
    rw [Finset.disjoint_left]
    rintro _ hv hw
    obtain ⟨p,hp,rfl⟩ := Finset.mem_map.mp hw
    exact ((mem_modulusPrimes c p).mp hp).1 hv
  have htriv : ∀ v ∉ S ∪ T.map i, χ v = 1 := by
    rintro (w|p) hv
    · exact (hv (Finset.mem_union_left _ (hS.2.1 w))).elim
    · have hp : Sum.inr p ∉ S := fun h => hv (Finset.mem_union_left _ h)
      have hT : p ∉ T := fun h => hv (Finset.mem_union_right _ (Finset.mem_map.mpr ⟨p,h,rfl⟩))
      have hu : ‖diagonal F (.inr p) c.val‖ = 1 := le_antisymm (integer_norm_le_one c.val p hp)
        (le_of_not_gt fun hl => hT ((mem_modulusPrimes c p).mpr ⟨hp,hl⟩))
      apply (hS.2.2 p hp).2
      rw [show x = (a : F)/c.val from rfl,map_div₀,norm_div,hu,div_one]
      exact integer_norm_le_one a p hp
  have hprod : HasProd χ (1 : ℂ) := by
    have he (v : Place F) : component (algebraMap F (Adeles F) x) v = diagonal F v x := by cases v <;> rfl
    simpa only [χ, he, d.character.trivial_diagonal,Circle.coe_one] using
      hasProd_localValue d.character (algebraMap F (Adeles F) x)
  have hm := (hasProd_prod_of_ne_finset_one htriv).unique hprod
  rw [Finset.prod_union hdis,Finset.prod_map,← Finset.prod_attach T (fun p => χ (i p))] at hm
  let neg (p : T) := d.character.localValue F (.inr p.val) (-(diagonal F (.inr p.val) x))
  have hinv : (∏ p : T, χ (.inr p.val)) * ∏ p : T, neg p = 1 := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro p _
    rw [show χ (.inr p.val) * neg p = _ from
      (d.character.localValue_add (.inr p.val) (diagonal F (.inr p.val) x) _).symm,add_neg_cancel]
    exact d.character.localValue_zero _
  change (∏ v ∈ S, χ v) = ∏ p : T, neg p
  calc
    _ = (∏ v ∈ S, χ v) * ((∏ p : T, χ (.inr p.val)) * ∏ p : T, neg p) := by rw [hinv,mul_one]
    _ = _ := by rw [← mul_assoc,show (∏ v ∈ S, χ v) * (∏ p : T, χ (.inr p.val)) = 1 from hm,one_mul]

end Character
end MetaplecticPoisson.Datum
