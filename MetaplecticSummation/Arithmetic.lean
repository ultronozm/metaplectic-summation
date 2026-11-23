import MetaplecticSummation.Hilbert.Family
import MetaplecticSummation.HilbertUniqueness
import MetaplecticSummation.ArchimedeanSelfDual
import MetaplecticSummation.FinitePlancherel
import MetaplecticSummation.FinitePlaceNorm
import MetaplecticSummation.FiniteLocalCharacter
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots

/-! Local measure and Hilbert-symbol normalizations for §9. -/
noncomputable section
namespace MetaplecticPoisson
open NumberField IsDedekindDomain Filter MeasureTheory
open scoped Topology
variable (F : Type) [Field F] [NumberField F]

/-- Self-dual Haar normalization at a finite place. -/
theorem exists_finite_selfDual (ψ : Character F) (p : HeightOneSpectrum (𝓞 F)) :
    ∃ μ, IsSelfDual F ψ (.inr p) μ := by
  letI : NontriviallyNormedField (p.adicCompletion F) := FinitePlace.nontriviallyNormedCompletion p
  letI : ProperSpace (p.adicCompletion F) := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace _
  letI : MeasurableSpace (p.adicCompletion F) := borel _
  letI : BorelSpace (p.adicCompletion F) := ⟨rfl⟩
  let χ : AddChar (p.adicCompletion F) ℂ :=
    ⟨ψ.localValue F (.inr p), ψ.localValue_zero (.inr p), ψ.localValue_add (.inr p)⟩
  have hl : IsLocallyConstant χ := ψ.locallyConstant_finiteValue p
  have hn : ∃ z, χ z ≠ 1 := ψ.nontrivial_finiteValue p
  obtain ⟨μ,hμ,hV⟩ := exists_haar_dual_ball_volumes χ hl hn
  letI := hμ
  exact ⟨μ,hμ,kernelPlancherel_of_dualBallVolumes μ χ hl.continuous (ψ.norm_localValue (.inr p)) hn hV⟩

theorem exists_selfDual (ψ : Character F) (v : Place F) :
    ∃ dx, IsSelfDual F ψ v dx := by
  cases v with
  | inl w => exact exists_arch_selfDual ψ w
  | inr p => exact exists_finite_selfDual F ψ p

theorem existsUnique_selfDual (ψ : Character F) (v : Place F) :
    ∃! dx, IsSelfDual F ψ v dx := by
  obtain ⟨μ,hμ⟩ := exists_selfDual F ψ v
  exact ⟨μ, hμ, fun _ hν => IsSelfDual.unique F hν hμ⟩

def selfDual (ψ : Character F) (v : Place F) := (existsUnique_selfDual F ψ v).exists.choose

theorem existsUnique_hilbert (n : ℕ) [NeZero n] {ζ : F} (hζ : IsPrimitiveRoot ζ n) :
    ∃! H, IsHilbertFamily F n H := by
  let m : ℕ+ := ⟨n, NeZero.pos n⟩
  exact ⟨Hilbert.family m hζ, Hilbert.family_spec m hζ,
    fun _ h => IsHilbertFamily.unique hζ h (Hilbert.family_spec m hζ)⟩

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
