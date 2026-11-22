import MetaplecticSummation.Arithmetic
import MetaplecticSummation.LineMeasures
import MetaplecticSummation.FiniteCompletionTopology

/-! Haar scaling on a finite completion. The count of cosets follows
GroundTheory.GlobalFields.TateThesis.FiniteAdeleScaling.
The computation below takes place on the local additive group. -/

noncomputable section
namespace MetaplecticPoisson.FinitePlace
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum MeasureTheory Measure
open scoped Pointwise NNReal ENNReal WithZero

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

theorem exists_norm_uniformizer :
    ∃ π : (v.adicCompletion K)ˣ, ‖π.val‖ = (v.asIdeal.absNorm : ℝ)⁻¹ := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers K)
  have hn : (π : v.adicCompletion K) ≠ 0 := fun h => hπ.ne_zero (Subtype.ext h)
  exact ⟨Units.mk0 _ hn, congrArg NNReal.toReal (norm_uniformizer v hπ)⟩

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


namespace MetaplecticPoisson.Datum
open NumberField IsDedekindDomain
variable {F : Type} [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F))
local notation "K" => p.adicCompletion F
local notation "O" => p.adicCompletionIntegers F

theorem mem_localIntegers_iff (x : K) : x ∈ O ↔ ‖x‖ ≤ 1 :=
  (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F p).trans
    Valued.toNormedField.norm_le_one_iff.symm

theorem localInteger_isUnit_iff (a : O) : IsUnit a ↔ ‖(a : K)‖ = 1 := by
  constructor
  · rintro ⟨u,rfl⟩
    have h : (u.val : K) * (u⁻¹.val : K) = 1 := congrArg Subtype.val u.val_inv
    have hprod : ‖(u.val : K)‖ * ‖(u⁻¹.val : K)‖ = 1 := by rw [← norm_mul,h,norm_one]
    apply le_antisymm ((mem_localIntegers_iff p _).mp u.val.property)
    exact hprod ▸ mul_le_of_le_one_right (norm_nonneg _) ((mem_localIntegers_iff p _).mp u⁻¹.val.property)
  · intro h
    have hn : (a : K) ≠ 0 := norm_ne_zero_iff.mp (h ▸ one_ne_zero)
    let b : O := ⟨(a : K)⁻¹,(mem_localIntegers_iff p _).mpr (by rw [norm_inv,h,inv_one])⟩
    exact ⟨⟨a,b,Subtype.ext (mul_inv_cancel₀ hn),Subtype.ext (inv_mul_cancel₀ hn)⟩,rfl⟩

end MetaplecticPoisson.Datum
