import MetaplecticSummation.HaarNormalization
import Mathlib.NumberTheory.NumberField.AdeleRing
import MetaplecticSummation.FiniteCompletionTopology
import Mathlib.Analysis.Complex.Circle
import Mathlib.Algebra.Group.AddChar
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Number-field completions, adelic characters and uniqueness of the self-dual measure. -/
noncomputable section
namespace MetaplecticPoisson
open NumberField IsDedekindDomain Filter MeasureTheory
open scoped Topology

variable (F : Type) [Field F] [NumberField F]
abbrev Place := InfinitePlace F ⊕ HeightOneSpectrum (𝓞 F)

def LocalField : Place F → Type
  | .inl w => w.Completion
  | .inr p => p.adicCompletion F

instance localNormedField (v : Place F) : NormedField (LocalField F v) := by
  cases v with
  | inl w => exact inferInstanceAs (NormedField w.Completion)
  | inr p => exact inferInstanceAs (NormedField (p.adicCompletion F))

instance (v : Place F) : MeasurableSpace (LocalField F v) := borel _
instance (v : Place F) : BorelSpace (LocalField F v) := ⟨rfl⟩

def diagonal (v : Place F) : F →+* LocalField F v := by
  cases v with
  | inl w => exact algebraMap F w.Completion
  | inr p => exact FinitePlace.embedding p

def modulus (v : Place F) (x : LocalField F v) : ℝ :=
  match v with
  | .inl w => ‖x‖ ^ w.mult
  | .inr _ => ‖x‖

abbrev Adeles := AdeleRing (𝓞 F) F

structure Character where
  toChar : AddChar (Adeles F) Circle
  continuous_toChar : Continuous toChar
  nontrivial : ∃ a, toChar a ≠ 1
  trivial_diagonal : ∀ x : F, toChar (algebraMap F (Adeles F) x) = 1

def singleAdele (v : Place F) : LocalField F v → Adeles F := by
  classical
  cases v with
  | inl w => exact fun x => (Pi.single w x, 0)
  | inr p => exact fun x => (0, RestrictedProduct.single (fun q : HeightOneSpectrum (𝓞 F) => q.adicCompletionIntegers F) p x)

def Character.localValue (ψ : Character F) (v : Place F) (x : LocalField F v) : ℂ :=
  ψ.toChar (singleAdele F v x)

/-- Plancherel on continuous compactly supported functions fixes the scalar of Haar measure. -/
def IsSelfDual (ψ : Character F) (v : Place F) (dx : Measure (LocalField F v)) : Prop :=
  dx.IsAddHaarMeasure ∧ KernelPlancherel (fun x y => ψ.localValue F v (x*y)) dx

theorem IsSelfDual.unique {ψ : Character F} {v : Place F} {μ ν : Measure (LocalField F v)}
    (hμ : IsSelfDual F ψ v μ) (hν : IsSelfDual F ψ v ν) : μ = ν := by
  letI : LocallyCompactSpace (LocalField F v) := by
    cases v with
    | inl w => exact inferInstanceAs (LocallyCompactSpace w.Completion)
    | inr p => exact inferInstanceAs (LocallyCompactSpace (p.adicCompletion F))
  letI : TopologicalSpace.SeparableSpace (LocalField F v) := by
    cases v with
    | inl w =>
      letI : SecondCountableTopology (LocalField F (.inl w)) :=
        (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
      infer_instance
    | inr p =>
      letI : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
      exact TopologicalSpace.SeparableSpace.of_denseRange _ (HeightOneSpectrum.denseRange_algebraMap (K := F) p)
  letI : μ.IsAddHaarMeasure := hμ.1
  letI : ν.IsAddHaarMeasure := hν.1
  exact haar_eq_of_plancherel (fun x y => ψ.localValue F v (x*y)) ν μ hν.2 hμ.2

end MetaplecticPoisson
