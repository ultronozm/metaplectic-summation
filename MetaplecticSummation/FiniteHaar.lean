import MetaplecticSummation.Arithmetic
import MetaplecticSummation.LineMeasures
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.NumberTheory.LocalField.Basic

/-! Haar scaling on a finite completion. The residue-field comparison and the count
of cosets follow GroundTheory.GlobalFields.LocalAtPlace and TateThesis.FiniteAdeleScaling.
The computation below takes place on the local additive group. -/

noncomputable section
namespace MetaplecticPoisson.FinitePlace
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum MeasureTheory Measure
open scoped Pointwise NNReal ENNReal WithZero

section Residue

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

theorem algebraMap_mem_maximalIdeal_adicCompletionIntegers_iff (r : R) :
    algebraMap R (v.adicCompletionIntegers K) r ∈
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ↔ r ∈ v.asIdeal := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    adicCompletionIntegers.isUnit_iff_valued_eq_one, algebraMap_adicCompletionIntegers_apply,
    valuedAdicCompletion_eq_valuation', valuation_eq_one_iff_notMem, not_not]

theorem exists_algebraMap_sub_mem_maximalIdeal (x : v.adicCompletionIntegers K) :
    ∃ r : R, x - algebraMap R (v.adicCompletionIntegers K) r ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by

  have hnhds : {y : v.adicCompletion K | Valued.v (y - (x : v.adicCompletion K)) < 1} ∈
      nhds (x : v.adicCompletion K) :=
    Valued.mem_nhds.2 ⟨1, fun y hy ↦ by
      simpa [Valuation.restrict_lt_one_iff] using hy⟩
  obtain ⟨k, hk⟩ := (denseRange_algebraMap (K := K) v).mem_nhds hnhds
  have hk' : Valued.v ((x : v.adicCompletion K) - (k : v.adicCompletion K)) < 1 := by
    rw [Valuation.map_sub_swap]; exact hk

  have hk1 : v.valuation K k ≤ 1 := by
    rw [← valuedAdicCompletion_eq_valuation']
    have : (k : v.adicCompletion K) = (x : v.adicCompletion K) -
        ((x : v.adicCompletion K) - (k : v.adicCompletion K)) := by ring
    rw [this]
    exact (Valuation.map_sub _ _ _).trans (max_le x.2 hk'.le)
  obtain ⟨r, hr⟩ := exists_valuation_sub_lt_of_integer v hk1 1
  refine ⟨r, ?_⟩
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    adicCompletionIntegers.isUnit_iff_valued_eq_one]
  refine ne_of_lt ?_
  have hr' : Valued.v (algebraMap K (v.adicCompletion K) (k - algebraMap R K r)) < 1 := by
    rw [Valuation.map_sub_swap] at hr
    have := valuedAdicCompletion_eq_valuation' (R := R) v (k - algebraMap R K r)
    exact this.trans_lt (by simpa using hr)
  have : ((x - algebraMap R (v.adicCompletionIntegers K) r : v.adicCompletionIntegers K) :
      v.adicCompletion K) = ((x : v.adicCompletion K) - (k : v.adicCompletion K)) +
        algebraMap K (v.adicCompletion K) (k - algebraMap R K r) := by
    rw [map_sub]
    simp [algebraMap_adicCompletion]
  rw [this]
  exact Valuation.map_add_lt _ hk' hr'

noncomputable def toResidueFieldAdicCompletionIntegers :
    R →+* IsLocalRing.ResidueField (v.adicCompletionIntegers K) :=
  (IsLocalRing.residue _).comp (algebraMap R (v.adicCompletionIntegers K))

theorem ker_toResidueFieldAdicCompletionIntegers :
    RingHom.ker (toResidueFieldAdicCompletionIntegers (K := K) v) = v.asIdeal := by
  ext r
  rw [RingHom.mem_ker, toResidueFieldAdicCompletionIntegers, RingHom.comp_apply,
    IsLocalRing.residue_eq_zero_iff, algebraMap_mem_maximalIdeal_adicCompletionIntegers_iff]

theorem toResidueFieldAdicCompletionIntegers_surjective :
    Function.Surjective (toResidueFieldAdicCompletionIntegers (K := K) v) := by
  intro y
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨r, hr⟩ := exists_algebraMap_sub_mem_maximalIdeal v x
  exact ⟨r, (Ideal.Quotient.eq.2 hr).symm⟩

noncomputable def residueFieldEquiv :
    (R ⧸ v.asIdeal) ≃+* IsLocalRing.ResidueField (v.adicCompletionIntegers K) :=
  (Ideal.quotEquivOfEq (ker_toResidueFieldAdicCompletionIntegers v).symm).trans
    (RingHom.quotientKerEquivOfSurjective (toResidueFieldAdicCompletionIntegers_surjective v))

@[simp]
theorem residueFieldEquiv_mk (r : R) :
    residueFieldEquiv (K := K) v (Ideal.Quotient.mk v.asIdeal r) =
      IsLocalRing.residue _ (algebraMap R (v.adicCompletionIntegers K) r) :=
  rfl

end Residue

section NumberField

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

instance : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) :=
  haveI := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  Finite.of_equiv _ (residueFieldEquiv v).toEquiv

theorem natCard_residueField_adicCompletionIntegers :
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) =
      Ideal.absNorm v.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (residueFieldEquiv v).toEquiv).symm

end NumberField

section Topology

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem isOpen_adicCompletionIntegers :
    IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
  Valued.isOpen_valuationSubring _

theorem isClosed_adicCompletionIntegers :
    IsClosed (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
  (Valued.isClopen_integer (v.adicCompletion K)).isClosed

theorem isCompact_adicCompletionIntegers :
    IsCompact (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
  have : CompleteSpace (Valued.integer (v.adicCompletion K)) :=
    (isClosed_adicCompletionIntegers v).completeSpace_coe
  have : IsDiscreteValuationRing (Valued.integer (v.adicCompletion K)) :=
    inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers K))
  have : Finite (Valued.ResidueField (v.adicCompletion K)) :=
    inferInstanceAs (Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)))
  have h : CompactSpace (Valued.integer (v.adicCompletion K)) :=
    Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.2
      ⟨inferInstance, inferInstance, inferInstance⟩
  exact isCompact_iff_compactSpace.2 h

instance : CompactSpace (v.adicCompletionIntegers K) :=
  isCompact_iff_compactSpace.1 (isCompact_adicCompletionIntegers v)

instance : LocallyCompactSpace (v.adicCompletion K) :=
  (isCompact_adicCompletionIntegers v).locallyCompactSpace_of_mem_nhds_of_addGroup
    ((isOpen_adicCompletionIntegers v).mem_nhds (v.adicCompletionIntegers K).zero_mem)

end Topology

theorem measure_eq_card_mul_measure_ker {A Q : Type*} [AddGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] [MeasurableSpace A] [BorelSpace A] (μ : Measure A)
    [μ.IsAddLeftInvariant] (L : AddSubgroup A) [AddGroup Q] [Finite Q] (φ : L →+ Q)
    (hφ : Function.Surjective φ) (hker : IsOpen ((φ.ker.map L.subtype : AddSubgroup A) : Set A)) :
    μ L = Nat.card Q * μ (φ.ker.map L.subtype) := by
  classical
  have := Fintype.ofFinite Q
  set N : Set A := ((φ.ker.map L.subtype : AddSubgroup A) : Set A) with hN
  have hmemN : ∀ y : A, y ∈ N ↔ ∃ h : y ∈ L, φ ⟨y, h⟩ = 0 := by
    intro y
    simp only [hN, AddSubgroup.coe_map, AddSubgroup.coe_subtype, Set.mem_image, SetLike.mem_coe,
      AddMonoidHom.mem_ker]
    constructor
    · rintro ⟨⟨z, hz⟩, h0, rfl⟩
      exact ⟨hz, h0⟩
    · rintro ⟨h, h0⟩
      exact ⟨⟨y, h⟩, h0, rfl⟩
  let t : Q → L := Function.surjInv hφ
  have ht : ∀ q, φ (t q) = q := Function.surjInv_eq hφ
  have hU : (L : Set A) = ⋃ q, ((t q : L) : A) +ᵥ N := by
    ext y
    simp only [SetLike.mem_coe, Set.mem_iUnion, Set.mem_vadd_set, vadd_eq_add]
    constructor
    · intro hy
      refine ⟨φ ⟨y, hy⟩, -(t (φ ⟨y, hy⟩) : A) + y, (hmemN _).2 ⟨L.add_mem (L.neg_mem (t _).2) hy, ?_⟩,
        add_neg_cancel_left _ _⟩
      have : (⟨-(t (φ ⟨y, hy⟩) : A) + y, L.add_mem (L.neg_mem (t _).2) hy⟩ : L) =
          -t (φ ⟨y, hy⟩) + ⟨y, hy⟩ := rfl
      rw [this, map_add, map_neg, ht, neg_add_cancel]
    · rintro ⟨q, n, hn, rfl⟩
      obtain ⟨hnL, -⟩ := (hmemN n).1 hn
      exact L.add_mem (t q).2 hnL
  have hdisj : Pairwise (Function.onFun Disjoint fun q ↦ ((t q : L) : A) +ᵥ N) := by
    intro q q' hqq'
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨n, hn, rfl⟩ ⟨n', hn', h⟩
    obtain ⟨hnL, hn0⟩ := (hmemN n).1 hn
    obtain ⟨hnL', hn0'⟩ := (hmemN n').1 hn'
    apply hqq'
    have h' : (t q' : L) + ⟨n', hnL'⟩ = t q + ⟨n, hnL⟩ := Subtype.ext h
    have := congrArg φ h'
    rwa [map_add, map_add, hn0, hn0', add_zero, add_zero, ht, ht, eq_comm] at this
  rw [hU, measure_iUnion hdisj fun q ↦ (hker.vadd _).measurableSet, tsum_fintype]
  simp only [measure_vadd, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private theorem norm_uniformizer {π : v.adicCompletionIntegers K} (hπ : Irreducible π) :
    ‖(π : v.adicCompletion K)‖₊ = (v.asIdeal.absNorm : ℝ≥0)⁻¹ := by
  have hu := Valuation.isUniformizer_of_maximalIdeal_eq_span
    (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)
    ((IsDiscreteValuationRing.irreducible_iff_uniformizer π).1 hπ)
  have hv : Valued.v (π : v.adicCompletion K) = WithZero.exp (-1 : ℤ) := by
    rw [hu.val, Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
      (valuedAdicCompletion_surjective K v)]
    rfl
  apply NNReal.eq
  rw [coe_nnnorm, NumberField.FinitePlace.norm_def, hv]
  rw [WithZeroMulInt.toNNReal_neg_apply _ (WithZero.exp_ne_zero (a := (-1 : ℤ)))]
  change (↑((v.asIdeal.absNorm : ℝ≥0) ^ (-1 : ℤ)) : ℝ) = _
  simp

private theorem uniformizer_smul_integers {π : v.adicCompletionIntegers K} (hπ : Irreducible π)
    (h₀ : (π : v.adicCompletion K) ≠ 0) :
    Units.mk0 (π : v.adicCompletion K) h₀ • (v.adicCompletionIntegers K : Set (v.adicCompletion K)) =
      ((((IsLocalRing.residue (v.adicCompletionIntegers K)).toAddMonoidHom.ker).map
        (v.adicCompletionIntegers K).toAddSubgroup.subtype : AddSubgroup _) : Set _) := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    let w : v.adicCompletionIntegers K := π * ⟨z, hz⟩
    refine ⟨w, ?_, rfl⟩
    change IsLocalRing.residue _ w = 0
    rw [IsLocalRing.residue_eq_zero_iff, (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ]
    exact Ideal.mem_span_singleton.mpr (dvd_mul_right _ _)
  · rintro ⟨z, hz, rfl⟩
    change IsLocalRing.residue (v.adicCompletionIntegers K) z = 0 at hz
    rw [IsLocalRing.residue_eq_zero_iff, (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ,
      Ideal.mem_span_singleton] at hz
    obtain ⟨w, hw⟩ := hz
    exact ⟨w.val, w.property, (congrArg Subtype.val hw).symm⟩

/-- Scaling the ring of integers by a uniformizer gives the kernel of reduction.
Its index is the cardinality of the residue field. -/
private theorem haarChar_uniformizer {π : v.adicCompletionIntegers K} (hπ : Irreducible π)
    (h₀ : (π : v.adicCompletion K) ≠ 0) :
    distribHaarChar (v.adicCompletion K) (Units.mk0 _ h₀) = (v.asIdeal.absNorm : ℝ≥0)⁻¹ := by
  letI := borel (v.adicCompletion K)
  letI : BorelSpace (v.adicCompletion K) := ⟨rfl⟩
  let μ := (addHaar : Measure (v.adicCompletion K))
  let O := v.adicCompletionIntegers K
  have ho := isOpen_adicCompletionIntegers v
  have hk := uniformizer_smul_integers v hπ h₀
  have hc := measure_eq_card_mul_measure_ker μ O.toAddSubgroup
    (IsLocalRing.residue O).toAddMonoidHom (fun q => IsLocalRing.residue_surjective (R := O) q) (by rw [← hk]; exact ho.smul _)
  rw [natCard_residueField_adicCompletionIntegers] at hc
  have hq : (v.asIdeal.absNorm : ℝ≥0) ≠ 0 := NumberField.HeightOneSpectrum.absNorm_ne_zero v
  apply distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ)
    (ho.measure_pos μ ⟨0, O.zero_mem⟩).ne' (isCompact_adicCompletionIntegers v).measure_ne_top
  rw [hk]
  change _ = _ * μ (O.toAddSubgroup : Set _)
  rw [hc, ENNReal.coe_inv hq, ENNReal.coe_natCast, ← mul_assoc,
    ENNReal.inv_mul_cancel (by exact_mod_cast hq) (ENNReal.natCast_ne_top _), one_mul]

private theorem haarChar_norm_one (u : (v.adicCompletion K)ˣ) (hu : ‖u.val‖ = 1) :
    distribHaarChar (v.adicCompletion K) u = 1 := by
  letI := borel (v.adicCompletion K)
  letI : BorelSpace (v.adicCompletion K) := ⟨rfl⟩
  let μ := (addHaar : Measure (v.adicCompletion K))
  let O := v.adicCompletionIntegers K
  have hmem (x : v.adicCompletion K) : x ∈ O ↔ ‖x‖ ≤ 1  :=
    (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 K) K v).trans (Valued.toNormedField.norm_le_one_iff (x := x)).symm
  have same : u • (O : Set (v.adicCompletion K)) = O := by
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    change u⁻¹ • x ∈ O ↔ x ∈ O
    rw [hmem, hmem, Units.smul_def, smul_eq_mul,
      norm_mul, Units.val_inv_eq_inv_val, norm_inv, hu, inv_one, one_mul]
  apply distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ)
    ((isOpen_adicCompletionIntegers v).measure_pos μ ⟨0, O.zero_mem⟩).ne'
    (isCompact_adicCompletionIntegers v).measure_ne_top
  simpa only [ENNReal.coe_one, one_mul] using congrArg μ same

/-- The normalized adic norm is the modulus of multiplication on additive Haar measure. -/
theorem haarChar_eq_nnnorm (z : (v.adicCompletion K)ˣ) :
    distribHaarChar (v.adicCompletion K) z = ‖z.val‖₊ := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers K)
  have h₀ : (π : v.adicCompletion K) ≠ 0 := fun h => hπ.ne_zero (Subtype.ext h)
  have hint (a : (v.adicCompletion K)ˣ) (ha : a.val ∈ v.adicCompletionIntegers K) :
      distribHaarChar (v.adicCompletion K) a = ‖a.val‖₊ := by
    have hne : (⟨a, ha⟩ : v.adicCompletionIntegers K) ≠ 0 := fun h => a.ne_zero (congrArg Subtype.val h)
    obtain ⟨k, u, hku⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne hπ
    let b := Units.map (v.adicCompletionIntegers K).subtype.toMonoidHom u
    have he : a = b * Units.mk0 _ h₀ ^ k := Units.ext (congrArg Subtype.val hku)
    have hv := (adicCompletionIntegers.isUnit_iff_valued_eq_one (K := K) (v := v)).mp u.isUnit
    have hb : ‖b.val‖ = 1 :=
      le_antisymm (Valued.toNormedField.norm_le_one_iff.mpr hv.le)
        (Valued.toNormedField.one_le_norm_iff.mpr hv.ge)
    have hb' : ‖b.val‖₊ = 1 := NNReal.eq hb
    rw [he, map_mul, map_pow, haarChar_norm_one v b hb, haarChar_uniformizer v hπ h₀,
      Units.val_mul, nnnorm_mul, hb', Units.val_pow_eq_pow_val, nnnorm_pow, Units.val_mk0,
      norm_uniformizer v hπ]
  rcases (v.adicCompletionIntegers K).mem_or_inv_mem z.val with hz | hz
  · exact hint z hz
  · have h := hint z⁻¹ (by rwa [Units.val_inv_eq_inv_val])
    rwa [map_inv, Units.val_inv_eq_inv_val, nnnorm_inv, inv_inj] at h

/-- The additive group has no isolated points. An inverse uniformizer has norm q. -/
abbrev nontriviallyNormedCompletion : NontriviallyNormedField (v.adicCompletion K) where
  non_trivial := by
    obtain ⟨π, hp⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers K)
    refine ⟨(π : v.adicCompletion K)⁻¹, ?_⟩
    have h := congrArg NNReal.toReal (norm_uniformizer v hp)
    rw [norm_inv, show ‖(π : v.adicCompletion K)‖ = (v.asIdeal.absNorm : ℝ)⁻¹ from h, inv_inv]
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v

end MetaplecticPoisson.FinitePlace
