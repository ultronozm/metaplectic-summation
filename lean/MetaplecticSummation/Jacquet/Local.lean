import MetaplecticSummation.Jacquet.ArchLift

noncomputable section
namespace MetaplecticPoisson
namespace Datum

open MeasureTheory Filter NumberField IsDedekindDomain
open scoped ContDiff Topology
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [hn : NeZero n] (d : Datum F n)

def kernelIntegral (v : Place F) (W : Weight v) (c : (LocalField F v)ˣ) (t : LocalField F v) :=
  d.lineIntegral v fun x => W x * d.symbol v x (-c) *
    d.character.localValue F v (-(t ^ n) / ((c : LocalField F v) * x))

/-- Proposition 10.8 at λ = 1, used for compactly supported test weights. -/
def dualWeight (v : Place F) (W : Weight v) (c : (LocalField F v)ˣ) : ℂ :=
  (Real.sqrt (modulus F v (n : LocalField F v)) : ℂ)⁻¹ *
    ∫ t, d.character.localValue F v t * d.kernelIntegral v W c t ∂(selfDual F d.character v)

theorem exists_jacquetLift_auxiliary (v : Place F) : ∃ β, d.IsJacquetLiftAuxiliary v β := by
  cases v with
  | inl w => exact d.arch_exists_jacquetLift_auxiliary w
  | inr p => exact d.finite_exists_jacquetLift_auxiliary p

theorem jacquet_test_lift (v : Place F) (W : Weight v) (h : TestWeight v W) :
    ∃ Φ : d.schwartz v, Φ.val ∈ d.testSet v ∧ d.jacquet v Φ = W := by
  obtain ⟨β,hβ,ht⟩ := d.exists_jacquetLift_auxiliary v
  exact d.jacquetLift_evaluation v W β hβ (ht W h)

end Datum
end MetaplecticPoisson
