import MetaplecticSummation.HilbertData
import MetaplecticSummation.FinitePlaceNorm
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-! Tame reduction distinguishes the normalized values in the global roots of unity. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField IsDedekindDomain IsLocalRing
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n]
variable (p : HeightOneSpectrum (𝓞 F))
local notation "K" => p.adicCompletion F
local notation "O" => p.adicCompletionIntegers F
local notation "k" => ResidueField O
local notation "q" => p.asIdeal.absNorm

theorem norm_one_of_power {x : K} (hx : x^n = 1) : ‖x‖ = 1 := by
  have h : ‖x‖^n = (1 : ℝ)^n := by simp [← norm_pow,hx]
  exact (pow_left_inj₀ (norm_nonneg _) zero_le_one (NeZero.ne n)).mp h

/-- Reduction of a primitive root stays primitive when n is invertible in
the residue field, by reduction of the n-th cyclotomic polynomial. -/
theorem tame_primitive_lift {ζ₀ : F} (hζ₀ : IsPrimitiveRoot ζ₀ n) (hp : p.asIdeal.absNorm.Coprime n) :
    ∃ z : O, IsPrimitiveRoot z n ∧ IsPrimitiveRoot (IsLocalRing.residue O z) n := by
  letI : Fintype k := Fintype.ofFinite k
  have hcard : Fintype.card k = p.asIdeal.absNorm := by
    rw [← Nat.card_eq_fintype_card,FinitePlace.natCard_residueField_adicCompletionIntegers]
  have hq : (p.asIdeal.absNorm : k) = 0 := hcard ▸ Nat.cast_card_eq_zero k
  letI : NeZero (n : k) := ⟨(ne_zero_or_ne_zero_of_nat_coprime (A := k) hp).resolve_left (not_not.mpr hq)⟩
  let ζ : K := diagonal F (.inr p) ζ₀
  have hζ : IsPrimitiveRoot ζ n := hζ₀.map_of_injective (diagonal F (.inr p)).injective
  let z : O := ⟨ζ,(mem_localIntegers_iff p _).mpr (norm_one_of_power p hζ.pow_eq_one).le⟩
  have hz : IsPrimitiveRoot z n := IsPrimitiveRoot.of_map_of_injective (f := (p.adicCompletionIntegers F).subtype) hζ Subtype.val_injective
  have hr : IsPrimitiveRoot (IsLocalRing.residue O z) n := by
    apply Polynomial.isRoot_cyclotomic_iff.mp
    change Polynomial.eval _ _ = 0
    rw [Polynomial.cyclotomic.eval_apply,(show Polynomial.eval z (Polynomial.cyclotomic n O) = 0 from hz.isRoot_cyclotomic (NeZero.pos n)),map_zero]
  exact ⟨z,hz,hr⟩

theorem residue_eq_iff_norm_sub_lt (a b : O) :
    IsLocalRing.residue O a = IsLocalRing.residue O b ↔ ‖(a : K) - b‖ < 1 := by
  rw [← sub_eq_zero,← map_sub,residue_eq_zero_iff,mem_maximalIdeal,mem_nonunits_iff,
    localInteger_isUnit_iff]
  exact ne_iff_lt_iff_le.mpr ((mem_localIntegers_iff p _).mp (a-b).property)

/-- Reduction modulo a tame finite prime distinguishes n-th roots of unity. -/
theorem tame_root_reduction_injective_of_primitive {ζ : F} (hζ : IsPrimitiveRoot ζ n)
    (hp : p.asIdeal.absNorm.Coprime n) {x y : O}
    (hx : x^n = 1) (hy : y^n = 1) (h : IsLocalRing.residue O x = IsLocalRing.residue O y) : x = y := by
  obtain ⟨z,hz,hr⟩ := tame_primitive_lift p hζ hp
  obtain ⟨i,hi,ei⟩ := hz.eq_pow_of_pow_eq_one hx
  obtain ⟨j,hj,ej⟩ := hz.eq_pow_of_pow_eq_one hy
  rw [← ei,← ej,map_pow,map_pow] at h
  exact ei.symm.trans ((congrArg (fun l : ℕ => z^l) (hr.pow_inj hi hj h)).trans ej)

omit [NeZero n] in
private theorem root_local_pow (z : Mu F n) :
    (diagonal F (.inr p) (z.val : F))^n = 1 := by
  rw [← map_pow,show (z.val : F)^n = 1 from congrArg Units.val z.property,map_one]

def rootInteger (z : Mu F n) : O :=
  ⟨diagonal F (.inr p) (z.val : F), (mem_localIntegers_iff p _).mpr (by
    have hp : ‖diagonal F (.inr p) (z.val : F)‖^n = (1 : ℝ)^n := by
      rw [← norm_pow,root_local_pow,norm_one,one_pow]
    exact ((pow_left_inj₀ (norm_nonneg _) zero_le_one (NeZero.ne n)).mp hp).le)⟩

theorem rootInteger_pow (z : Mu F n) : rootInteger p z ^ n = 1 :=
  Subtype.ext (root_local_pow p z)

/-- Tame normalization fixes the root of unity itself on a uniformizer and a unit. -/
theorem tame_uniformizer_value_unique {ζ : F} (hζ : IsPrimitiveRoot ζ n)
    {H J : SymbolFamily F n} (hH : IsHilbertFamily F n H) (hJ : IsHilbertFamily F n J)
    (hp : Nat.Coprime q n) (π u : Kˣ) (hπ : ‖π.val‖ = (q : ℝ)⁻¹) (hu : ‖u.val‖ = 1) :
    H (.inr p) π u = J (.inr p) π u := by
  let U : O := ⟨u.val,(mem_localIntegers_iff p _).mpr hu.le⟩
  have red {P : SymbolFamily F n} (hP : IsHilbertFamily F n P) :
      IsLocalRing.residue O (rootInteger p (P (.inr p) π u)) =
        IsLocalRing.residue O (U^((q-1)/n)) :=
    (residue_eq_iff_norm_sub_lt p _ _).mpr (hP.tame_uniformizer p hp π u hπ hu)
  have he := tame_root_reduction_injective_of_primitive p hζ hp (rootInteger_pow p _)
    (rootInteger_pow p _) ((red hH).trans (red hJ).symm)
  apply Subtype.ext
  apply Units.ext
  exact (diagonal F (.inr p)).injective (congrArg Subtype.val he)

end MetaplecticPoisson.Datum
