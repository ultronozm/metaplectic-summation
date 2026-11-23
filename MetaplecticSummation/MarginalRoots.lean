import MetaplecticSummation.MarginalDifference
import Mathlib.Algebra.Polynomial.Splits

/-! The factorization over roots in the proof of the reverse marginal identity. -/

noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField MeasureTheory Filter Polynomial
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

/-- The difference integral extended by zero at the exceptional parameter. -/
def differenceIntegral (v : Place F) (f : LocalField F v → ℂ) (a : (LocalField F v)ˣ)
    (t : LocalField F v) : ℂ :=
  if ht : t ≠ 0 then d.lineIntegral v (d.marginalDifference v f a (Units.mk0 t ht)) else 0

private theorem sub_pow_factorization {K : Type*} [Field K] {ζ a : K} (hζ : IsPrimitiveRoot ζ n)
    (ha : a ≠ 0) (hr : ∃ r : K, r^n = a) (t : K) :
    t^n-a = ∏ r ∈ nthRootsFinset n a, (t-r) := by
  have hs : (X^n-C a).Splits := splits_iff_card_roots.mpr (by
    rw [← nthRoots,hζ.card_nthRoots,if_pos hr,natDegree_X_pow_sub_C])
  have he := hs.eval_eq_prod_roots_of_monic (monic_X_pow_sub_C _ (NeZero.ne n)) t
  rw [eval_sub,eval_pow,eval_X,eval_C,← nthRoots] at he
  rw [nthRootsFinset_def,← Multiset.toFinset_eq (hζ.nthRoots_nodup ha)]
  exact he

/-- When a is an n-th power, its Hilbert character is trivial and the
multiplicative difference integral is additive on products of units. -/
private def differenceHom (v : Place F) (f : LocalField F v → ℂ) (r : (LocalField F v)ˣ)
    (hi : ∀ b, d.LineIntegrable v (d.marginalDifference v f (r^n) b)) :
    (LocalField F v)ˣ →* Multiplicative ℂ where
  toFun b := Multiplicative.ofAdd (d.lineIntegral v (d.marginalDifference v f (r^n) b))
  map_one' := by
    change d.lineIntegral v _ = 0
    simp [lineIntegral,marginalDifference]
  map_mul' b c := by
    change d.lineIntegral v (d.marginalDifference v f (r^n) (b*c)) = _ + _
    have hs : d.symbol v c (r^n) = 1 := by
      change (d.unitPairing v c (r^n)).val = 1
      rw [map_pow,d.unitPairing_pow,Units.val_one]
    have he := d.marginalDifference_cocycle v f (r^n) b c (hi _) (hi _)
    dsimp only at he
    rw [hs,one_mul] at he
    exact sub_eq_iff_eq_add.mp he

/-- Appendix A's decomposition into linear factors, off the finite set of roots. -/
theorem differenceIntegral_roots (v : Place F) (f : LocalField F v → ℂ) (a : (LocalField F v)ˣ)
    (ha : ∃ r : (LocalField F v)ˣ, r^n = a)
    (hi : ∀ b, d.LineIntegrable v (d.marginalDifference v f a b))
    (t : LocalField F v) (ht : t^n ≠ a.val) :
    d.differenceIntegral v f a (t^n-a.val) =
      ∑ r ∈ nthRootsFinset n a.val, d.differenceIntegral v f a (t-r) := by
  obtain ⟨r,rfl⟩ := ha
  let R := nthRootsFinset n (r^n).val
  let L := d.differenceHom v f r hi
  have hne (z : R) : t - z.val ≠ 0 := sub_ne_zero.mpr fun h =>
    ht (h ▸ (mem_nthRootsFinset (NeZero.pos n) _).mp z.property)
  let w (z : R) := Units.mk0 (t-z.val) (hne z)
  have hp : Units.mk0 (t^n-(r^n).val) (sub_ne_zero.mpr ht) = ∏ z : R, w z := by
    apply Units.ext
    rw [Units.val_mk0,Units.coe_prod]
    change _ = ∏ z ∈ R.attach, (t-z.val)
    rw [Finset.prod_attach]
    exact sub_pow_factorization (d.primitive.map_of_injective (diagonal F v).injective)
      (r^n).ne_zero ⟨r.val,(Units.val_pow_eq_pow_val _ _).symm⟩ t
  have he := congrArg Multiplicative.toAdd ((congrArg L hp).trans (map_prod L _ _))
  rw [toAdd_prod] at he
  rw [← Finset.sum_attach R]
  simp only [differenceIntegral,dif_pos (sub_ne_zero.mpr ht),dif_pos (hne _)]
  exact he

/-- The finitely many deleted roots have additive measure zero. The factorization
therefore holds inside the tested integral, even when the test meets a root. -/
theorem integral_difference_roots (v : Place F) (f h : LocalField F v → ℂ) (a : (LocalField F v)ˣ)
    (ha : ∃ r : (LocalField F v)ˣ, r^n = a)
    (hi : ∀ b, d.LineIntegrable v (d.marginalDifference v f a b))
    (hh : ∀ r ∈ nthRootsFinset n a.val, Integrable (fun t => h t * d.differenceIntegral v f a (t-r))
      (selfDual F d.character v)) :
    (∫ t, h t * d.differenceIntegral v f a (t^n-a.val) ∂(selfDual F d.character v)) =
      ∑ r ∈ nthRootsFinset n a.val, ∫ t, h t * d.differenceIntegral v f a (t-r) ∂(selfDual F d.character v) := by
  let dx := selfDual F d.character v
  letI : NullSingletonClass dx := d.selfDual_nullSingleton v
  rw [← integral_finsetSum _ hh]
  apply integral_congr_ae
  filter_upwards [(nthRootsFinset n a.val).finite_toSet.countable.ae_notMem dx] with t ht
  have hn : t^n ≠ a.val := fun he => ht ((mem_nthRootsFinset (NeZero.pos n) _).mpr he)
  exact (congrArg (h t * ·) (d.differenceIntegral_roots v f a ha hi t hn)).trans (Finset.mul_sum ..)

/-- For a nonpower with nontrivial symbol character, the difference integral
vanishes at every polynomial argument and the root sum is empty. -/
theorem differenceIntegral_nonpower (v : Place F) (f : LocalField F v → ℂ)
    (a : (LocalField F v)ˣ) (hp : ¬ ∃ b, b^n = a)
    (hi : ∀ c, d.LineIntegrable v (d.marginalDifference v f a c))
    (hχ : ∃ u, d.symbol v u a ≠ 1) :
    nthRootsFinset n a.val = ∅ ∧ ∀ t : LocalField F v, d.differenceIntegral v f a (t^n-a.val) = 0 := by
  have hn (t : LocalField F v) : t^n ≠ a.val := by
    intro ht
    have ht₀ : t ≠ 0 := fun h => a.ne_zero (by simpa [h,zero_pow (NeZero.ne n)] using ht.symm)
    exact hp ⟨Units.mk0 t ht₀, Units.ext ht⟩
  constructor
  · exact Finset.eq_empty_iff_forall_notMem.mpr fun t ht =>
      hn t ((mem_nthRootsFinset (NeZero.pos n) _).mp ht)
  · intro t
    rw [differenceIntegral,dif_pos (sub_ne_zero.mpr (hn t))]
    exact d.marginalDifference_vanishes v f a _ hi hχ t (sub_add_cancel _ _)

end MetaplecticPoisson.Datum
