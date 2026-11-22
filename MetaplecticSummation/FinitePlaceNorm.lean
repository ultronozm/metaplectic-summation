import MetaplecticSummation.FiniteCompletionTopology

/-! The normalized absolute value of a uniformizer at a finite place. -/
noncomputable section
namespace MetaplecticPoisson.FinitePlace
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NNReal WithZero
variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem norm_uniformizer {π : v.adicCompletionIntegers K} (hπ : Irreducible π) :
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

/-- The additive group has no isolated points. An inverse uniformizer has norm q. -/
abbrev nontriviallyNormedCompletion : NontriviallyNormedField (v.adicCompletion K) where
  non_trivial := by
    obtain ⟨π, hp⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers K)
    refine ⟨(π : v.adicCompletion K)⁻¹, ?_⟩
    have h := congrArg NNReal.toReal (norm_uniformizer v hp)
    rw [norm_inv, show ‖(π : v.adicCompletion K)‖ = (v.asIdeal.absNorm : ℝ)⁻¹ from h, inv_inv]
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v

end MetaplecticPoisson.FinitePlace
