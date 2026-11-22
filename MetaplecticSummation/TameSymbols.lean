import MetaplecticSummation.LocalGluing
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Topology.Algebra.Module.Compact

/-! Tame principal units and the Steinberg relation at finite places (§2). -/

noncomputable section
namespace MetaplecticPoisson.FinitePlace
open NumberField IsDedekindDomain IsLocalRing Polynomial
open scoped Pointwise
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (p : HeightOneSpectrum (𝓞 F))

/-- Completeness for powers of the maximal ideal follows by intersecting nested
closed cosets in the compact ring of integers. -/
private instance : IsAdicComplete (maximalIdeal (p.adicCompletionIntegers F)) (p.adicCompletionIntegers F) where
  prec' f hf := by
    let O := p.adicCompletionIntegers F
    let S k : Set O := f k +ᵥ ((maximalIdeal O ^ k : Ideal O) : Set O)
    have hS k : S (k + 1) ⊆ S k := by
      apply (Set.vadd_set_subset_vadd_set_iff.mpr (Ideal.pow_le_pow_right k.le_succ)).trans
      simpa [S] using (hf k.le_succ).symm
    have h k : IsClosed (S k) := (IsNoetherianRing.isClosed_ideal (maximalIdeal O ^ k)).vadd (f k)
    obtain ⟨a, ha⟩ := (h 0).isCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S hS
      (by simp [S]) h
    refine ⟨a, fun k => ?_⟩
    obtain ⟨z, hz, rfl⟩ := Set.mem_iInter.mp ha k
    simpa [SModEq.sub_mem] using hz

/-- Property 2(f). Every principal unit is an n-th power when the residue
characteristic is prime to n. -/
theorem principal_unit_pow (hp : p.asIdeal.absNorm.Coprime n) (u : (p.adicCompletion F)ˣ)
    (hu : ‖u.val - 1‖ < 1) : ∃ z : (p.adicCompletion F)ˣ, z ^ n = u := by
  let O := p.adicCompletionIntegers F
  let k := ResidueField O
  have hi : Valued.v (u.val - 1) < 1 := Valued.toNormedField.norm_lt_one_iff.mp hu
  have hunit : u.val ∈ O := by
    change Valued.v u.val ≤ 1
    have he : u.val = (u.val - 1) + 1 := by ring
    calc
      Valued.v u.val = Valued.v ((u.val-1)+1) := congrArg Valued.v he
      _ ≤ max _ _ := Valuation.map_add _ _ _
      _ ≤ 1 := max_le hi.le (map_one _).le
  let a : O := ⟨u.val, hunit⟩
  let f : O[X] := X^n - C a
  have heval : f.eval 1 ∈ maximalIdeal O := by
    simp only [f, eval_sub, eval_pow, eval_X, one_pow, eval_C]
    rw [mem_maximalIdeal, mem_nonunits_iff, HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    exact (Valuation.map_sub_swap Valued.v 1 u.val ▸ hi).ne
  have hq : (p.asIdeal.absNorm : k) = 0 := by
    letI : Fintype k := Fintype.ofFinite k
    rw [← natCard_residueField_adicCompletionIntegers p, Nat.card_eq_fintype_card]
    exact Nat.cast_card_eq_zero k
  have hn : (n : k) ≠ 0 := (ne_zero_or_ne_zero_of_nat_coprime (A := k) hp).resolve_left (not_not.mpr hq)
  have hd : IsUnit (Ideal.Quotient.mk (maximalIdeal O) (f.derivative.eval 1)) := by
    simp [f, derivative_X_pow]
    exact isUnit_iff_ne_zero.mpr hn
  obtain ⟨x, hx, _⟩ := HenselianRing.is_henselian f (monic_X_pow_sub_C a (NeZero.ne n)) 1 heval hd
  have hx' : x^n = a := sub_eq_zero.mp (by simpa [f, Polynomial.IsRoot] using hx)
  have hpow : x.val ^ n = u.val := congrArg Subtype.val hx'
  have hx₀ : x.val ≠ 0 := fun hz => u.ne_zero (by simpa [hz, zero_pow (NeZero.ne n)] using hpow.symm)
  exact ⟨Units.mk0 _ hx₀, Units.ext hpow⟩

end MetaplecticPoisson.FinitePlace

namespace MetaplecticPoisson.Datum
open NumberField IsDedekindDomain
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

/-- The Steinberg relation at every place of residue characteristic prime to n. -/
theorem tame_steinberg (p : HeightOneSpectrum (𝓞 F)) (hp : p.asIdeal.absNorm.Coprime n)
    (a b : (p.adicCompletion F)ˣ) (hab : a.val + b.val = 1) :
    d.unitPairing (.inr p) a b = 1 := by
  let H : (p.adicCompletion F)ˣ →* (p.adicCompletion F)ˣ →* ℂˣ := d.unitPairing (.inr p)
  have hpow (x y : (p.adicCompletion F)ˣ) : H x y ^ n = 1 := d.unitPairing_pow (.inr p) x y
  change H a b = 1
  have right (x u : (p.adicCompletion F)ˣ) (hu : ‖u.val - 1‖ < 1) :
      H x u = 1 := by
    obtain ⟨z, rfl⟩ := FinitePlace.principal_unit_pow p hp u hu
    rw [map_pow, hpow]
  by_cases ha : ‖a.val‖ < 1
  · apply right
    simpa [show b.val - 1 = -a.val by linear_combination hab] using ha
  by_cases hb : ‖b.val‖ < 1
  · have h : ‖a.val - 1‖ < 1 := by
      simpa [show a.val - 1 = -b.val by linear_combination hab] using hb
    obtain ⟨z, rfl⟩ := FinitePlace.principal_unit_pow p hp a h
    rw [map_pow, MonoidHom.pow_apply, hpow]
  by_cases hbig : 1 < ‖a.val‖
  · let u := -b / a
    have hu : u.val - 1 = -(a.val)⁻¹ := by
      simp only [u, Units.val_div_eq_div_val, Units.val_neg]
      field_simp
      linear_combination -hab
    have h := right a u (by simpa [hu] using (inv_lt_one_of_one_lt₀ hbig))
    have he : b = (-a)*u := by
      apply Units.ext
      simp only [u, Units.val_mul, Units.val_div_eq_div_val, Units.val_neg]
      field_simp
    calc
      H a b = H a ((-a)*u) := congrArg _ he
      _ = 1 := by rw [map_mul, show H a (-a) = 1 from d.unitPairing_neg_self (.inr p) a, h, one_mul]
  have ha₁ := le_antisymm (le_of_not_gt hbig) (le_of_not_gt ha)
  apply d.unitPairing_tame_units p hp a b ha₁
  apply le_antisymm _ (le_of_not_gt hb)
  apply Valued.toNormedField.norm_le_one_iff.mpr
  rw [show b.val = 1-a.val by linear_combination hab]
  exact (Valuation.map_sub _ _ _).trans (max_le (map_one _).le
    (Valued.toNormedField.norm_le_one_iff.mp ha₁.le))

theorem tame_radon_glues (p : HeightOneSpectrum (𝓞 F)) (hp : p.asIdeal.absNorm.Coprime n)
    {f : Charts (LocalField F (.inr p))} (hf : Glues (d.symbol (.inr p)) f)
    (t : LocalField F (.inr p)) :
    Glues (d.symbol (.inr p)) (radon n (d.symbol (.inr p)) (modulus F (.inr p))
      (selfDual F d.character (.inr p)) f t) :=
  d.finite_radon_glues p (d.tame_steinberg p hp) hf t

end MetaplecticPoisson.Datum
