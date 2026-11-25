import ClassFieldTheory.AlgebraicNumberTheory.Idele.FinitePrime
import ClassFieldTheory.AlgebraicNumberTheory.Idele.NormOneCompact
import ClassFieldTheory.AlgebraicNumberTheory.Idele.PositiveArchimedeanSection

/-! Compact idele representatives for the split torus in Proposition B.6. -/
noncomputable section
namespace MetaplecticPoisson
open Set NumberField Topology
open scoped Pointwise NNReal
variable (F : Type) [Field F] [NumberField F]
local notation "J" => IdeleGroup F
local notation "modulusJ" => (IdeleGroup.absoluteNorm (K := F))
local notation "principal" => IdeleGroup.principalIdele F
private theorem normOne_representative (a : J) (ha : a ∈ IdeleGroup.normOneSubgroup (K := F)) :
    ∃ t : Fˣ, ∃ b ∈ IdeleGroup.compactNormOneClassCover (K := F), a = principal t * b := by
  have h := (IdeleClassGroup.mk_mem_normOneSubgroup_iff a).mpr ha
  change _ ∈ (IdeleClassGroup.normOneSubgroup (K := F) : Set (IdeleClassGroup F)) at h
  rw [← IdeleClassGroup.image_compactNormOneClassCover] at h
  obtain ⟨b,hb,he⟩ := h
  have hdiv : a / b ∈ IdeleGroup.principalSubgroup F := QuotientGroup.eq_iff_div_mem.mp he.symm
  obtain ⟨t,ht⟩ := hdiv
  exact ⟨t,b,hb,by rw [ht,div_mul_cancel]⟩

private theorem compact_positive_interval (R : ℝ≥0ˣ) : IsCompact (Icc (1 : ℝ≥0ˣ) R) := by
  apply Units.isEmbedding_val₀.isCompact_iff.mpr
  have eqn : (Units.val : ℝ≥0ˣ → ℝ≥0) '' Icc 1 R = Icc 1 R.val := by
    ext t
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact hu
    · intro ht
      have hpos : t ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1)
      exact ⟨Units.mk0 t hpos, ht, rfl⟩
  rw [eqn]
  exact isCompact_Icc

/-- Compact torus representatives modulo principal ideles and powers of an expanding idele.
The positive archimedean section sends a parameter to an idele of inverse absolute norm. -/
theorem exists_compact_idele_representatives (z : J) (hz : 1 < (modulusJ z)⁻¹) :
    ∃ C : Set J, IsCompact C ∧ ∀ a : J, ∃ t : Fˣ, ∃ k : ℤ, ∃ c ∈ C,
      a = principal t * z^k * c ∧
      1 ≤ (modulusJ a)⁻¹ / ((modulusJ z)⁻¹)^k ∧ (modulusJ a)⁻¹ / ((modulusJ z)⁻¹)^k < (modulusJ z)⁻¹ := by
  let R := (modulusJ z)⁻¹
  let S := IdeleGroup.positiveArchimedeanSection F
  let B := IdeleGroup.compactNormOneClassCover (K := F)
  refine ⟨B * (S '' Icc 1 R), IdeleGroup.isCompact_compactNormOneClassCover.mul
    ((compact_positive_interval R).image IdeleGroup.continuous_positiveArchimedeanSection), ?_⟩
  intro a
  obtain ⟨k, hk, _⟩ := existsUnique_zpow_near_of_one_lt' hz (modulusJ a)⁻¹
  let b := a / z^k
  have eb : (modulusJ b)⁻¹ = (modulusJ a)⁻¹ / R^k := by
    simp only [b, R, map_div, map_zpow, inv_div', inv_zpow]
  let b₁ := IdeleGroup.positiveArchimedeanNormOneCorrection F b
  obtain ⟨t,c,hc,he⟩ := normOne_representative F b₁ b₁.property
  have hs : (modulusJ b)⁻¹ ∈ Icc 1 R := eb ▸ ⟨hk.1,hk.2.le⟩
  refine ⟨t,k,c * S (modulusJ b)⁻¹, ⟨c,hc,_,⟨_,hs,rfl⟩,rfl⟩,?_,hk⟩
  have decomp : b = principal t * c * S (modulusJ b)⁻¹ := by
    rw [map_inv]
    exact (IdeleGroup.eq_positiveArchimedeanNormOneCorrection_mul_section_inv b).trans
      (congrArg (· * (S (modulusJ b))⁻¹) he)
  calc
    a = b * z^k := (div_mul_cancel _ _).symm
    _ = (principal t * c * S (modulusJ b)⁻¹) * z^k := congrArg (· * z^k) decomp
    _ = _ := by ac_rfl

/-- The cusp idele has inverse uniformizer at the chosen place and one elsewhere. -/
def cuspIdele (w : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) : J := (IdeleGroup.finitePrimeIdele w)⁻¹

theorem cuspIdele_module (w : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) : (modulusJ (cuspIdele F w))⁻¹ = FiniteIdeleGroup.primeNorm w := by
  rw [cuspIdele, map_inv, inv_inv, IdeleGroup.absoluteNorm_apply]
  rw [show (IdeleGroup.finitePrimeIdele w).1 = 1 from rfl, map_one, inv_one, mul_one,
    FiniteIdeleGroup.absoluteNorm_eq_fractionalIdealAbsoluteNorm]
  change FractionalIdealGroup.absoluteNorm (IdeleGroup.fractionalIdeal (IdeleGroup.finitePrimeIdele w)) = _
  rw [IdeleGroup.fractionalIdeal_finitePrimeIdele, FractionalIdealGroup.absoluteNorm_prime]

theorem cuspIdele_expands (w : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) : 1 < (modulusJ (cuspIdele F w))⁻¹ := by
  rw [cuspIdele_module]
  change (1 : ℝ≥0) < (w.asIdeal.absNorm : ℝ≥0)
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm w

end MetaplecticPoisson
