import ClassFieldTheory.LocalClassFieldTheory.Kummer.MathlibHilbertPairing
import ClassFieldTheory.LocalClassFieldTheory.Kummer.PowerResidueTameFormula

open scoped ValuativeRel
open LocalFieldTheory LocalFieldTheory.IsNonarchimedeanLocalField
open LocalClassFieldTheory.Kummer KummerTheory
noncomputable section

/-- The inverse of the public pairing, on a positive uniformizer then a unit,
is the unique lift used in the paper. -/
theorem inverse_uniformizer_unit (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ+) (hn : ValuativeRel.valuation K ((n : ℕ) : K) = 1)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (π : Kˣ) (u : 𝒪[K]ˣ)
    (hπ : valuationMap K (Additive.ofMul π) = -1) :
    (ClassFieldTheory.localHilbertSymbol K n (natCast_ne_zero_of_valuation_eq_one K n hn) hmu
      π (integerUnitsToFieldUnits K u))⁻¹ =
      nthRootsSubgroupEquivRootsOfUnity K (n : ℕ) (localTamePowerResidueSymbol K n hn hmu u) := by
  rw [← ClassFieldTheory.localHilbertSymbol_skew]
  unfold ClassFieldTheory.localHilbertSymbol
  rw [localHilbertSymbol_tame_formula, hπ, neg_neg, zpow_one]

#print axioms inverse_uniformizer_unit
