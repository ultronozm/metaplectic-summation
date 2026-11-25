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

open WithZero

theorem integral_norm_power (p : HeightOneSpectrum (𝓞 F)) (t : (p.adicCompletion F)ˣ) (ht : ‖t.val‖ ≤ 1) :
    ∃ k : ℕ, ‖t.val‖ = ((p.asIdeal.absNorm : ℝ)^k)⁻¹ := by
  have hv : Valued.v t.val ≠ 0 := Valued.v.ne_zero_iff.mpr t.ne_zero
  have hle := Valued.toNormedField.norm_le_one_iff.mp ht
  rw [← exp_log hv,← exp_zero] at hle
  let k := (-(Valued.v t.val).log).toNat
  have h : Valued.v t.val = exp (-(k : ℤ)) := by
    simp only [k,Int.toNat_of_nonneg (neg_nonneg.mpr (exp_le_exp.mp hle)),neg_neg,exp_log hv]
  refine ⟨k,?_⟩
  rw [NumberField.FinitePlace.norm_def,h,WithZeroMulInt.toNNReal_neg_apply _ (exp_ne_zero (a := _))]
  change (↑((p.asIdeal.absNorm : NNReal) ^ (-(k : ℤ))) : ℝ) = _
  simp

/-- Every nonzero absolute value in the local field is an integral power of q. -/
theorem norm_zpow_residue_card (p : HeightOneSpectrum (𝓞 F)) (a : (p.adicCompletion F)ˣ) :
    ∃ j : ℤ, ‖a.val‖ = (p.asIdeal.absNorm : ℝ)^j := by
  by_cases h : ‖a.val‖ ≤ 1
  · obtain ⟨k,hk⟩ := integral_norm_power p a h
    exact ⟨-(k : ℤ),by simpa only [zpow_neg,zpow_natCast] using hk⟩
  · have hi : ‖a⁻¹.val‖ ≤ 1 := by
      rw [Units.val_inv_eq_inv_val,norm_inv]
      exact inv_le_one_of_one_le₀ (le_of_not_ge h)
    obtain ⟨k,hk⟩ := integral_norm_power p a⁻¹ hi
    exact ⟨k,by simpa only [Units.val_inv_eq_inv_val,norm_inv,inv_inj,zpow_natCast] using hk⟩

end MetaplecticPoisson.Datum
