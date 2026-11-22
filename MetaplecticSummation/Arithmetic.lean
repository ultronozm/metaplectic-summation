import MetaplecticSummation.HaarNormalization
import Mathlib.NumberTheory.NumberField.AdeleRing
import MetaplecticSummation.FiniteCompletionTopology
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.Analysis.Complex.Circle
import Mathlib.Algebra.Group.AddChar
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Number-field inputs and normalizations for §9. The statements of local class
field theory and of self-dual Haar normalization are isolated below. -/
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

theorem exists_selfDual (ψ : Character F) (v : Place F) :
    ∃ dx, IsSelfDual F ψ v dx := by sorry

theorem existsUnique_selfDual (ψ : Character F) (v : Place F) :
    ∃! dx, IsSelfDual F ψ v dx := by
  obtain ⟨μ,hμ⟩ := exists_selfDual F ψ v
  exact ⟨μ, hμ, fun _ hν => IsSelfDual.unique F hν hμ⟩

def selfDual (ψ : Character F) (v : Place F) := (existsUnique_selfDual F ψ v).exists.choose

abbrev Mu (n : ℕ) := rootsOfUnity n F
abbrev SymbolFamily (n : ℕ) := (v : Place F) → (LocalField F v)ˣ → (LocalField F v)ˣ → Mu F n

/-- Reciprocity and the tame convention determine the family, including at
wild and infinite places, by weak approximation. The convention is
{uniformizer,u} reducing to u^((q-1)/n). -/
structure IsHilbertFamily (n : ℕ) (H : SymbolFamily F n) : Prop where
  continuous_pair : ∀ v, Continuous (fun a : (LocalField F v)ˣ × (LocalField F v)ˣ =>
    diagonal F v (((H v a.1 a.2 : Fˣ) : F)))
  mul_left : ∀ v a b c, H v (a*b) c = H v a c * H v b c
  mul_right : ∀ v a b c, H v a (b*c) = H v a b * H v a c
  skew : ∀ v a b, H v a b * H v b a = 1
  neg_self : ∀ v a, H v a (-a) = 1
  tame_units : ∀ (p : HeightOneSpectrum (𝓞 F)), p.asIdeal.absNorm.Coprime n →
    ∀ a b : (LocalField F (.inr p))ˣ, ‖(a : LocalField F (.inr p))‖ = 1 →
      ‖(b : LocalField F (.inr p))‖ = 1 → H (.inr p) a b = 1
  tame_uniformizer : ∀ (p : HeightOneSpectrum (𝓞 F)), p.asIdeal.absNorm.Coprime n →
    ∀ π u : (LocalField F (.inr p))ˣ, ‖(π : LocalField F (.inr p))‖ = (p.asIdeal.absNorm : ℝ)⁻¹ →
      ‖(u : LocalField F (.inr p))‖ = 1 →
      ‖diagonal F (.inr p) (((H (.inr p) π u : Fˣ) : F)) -
        (u : LocalField F (.inr p)) ^ ((p.asIdeal.absNorm - 1) / n)‖ < 1
  unramified : ∀ a b : Fˣ, ∀ᶠ v in cofinite,
    H v (Units.map (diagonal F v) a) (Units.map (diagonal F v) b) = 1
  reciprocity : ∀ a b : Fˣ,
    (∏ᶠ v, H v (Units.map (diagonal F v) a) (Units.map (diagonal F v) b)) = 1

theorem existsUnique_hilbert (n : ℕ) [NeZero n] {ζ : F} (hζ : IsPrimitiveRoot ζ n) :
    ∃! H, IsHilbertFamily F n H := by sorry

def hilbert {n : ℕ} [NeZero n] {ζ : F} (hζ : IsPrimitiveRoot ζ n)
    (ε : Mu F n →* ℂˣ) (v : Place F) (a b : (LocalField F v)ˣ) : ℂ :=
  ε ((existsUnique_hilbert F n hζ).exists.choose v a b)

/-- Choices fixed throughout the number-field Poisson formula. -/
structure Datum (n : ℕ) where
  root : F
  primitive : IsPrimitiveRoot root n
  embedding : Mu F n →* ℂˣ
  injective : Function.Injective embedding
  character : Character F

end MetaplecticPoisson
