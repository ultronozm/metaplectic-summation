import MetaplecticSummation.Arithmetic
import MetaplecticSummation.Core
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.LocallyConstant.Basic

noncomputable section
namespace MetaplecticPoisson
open NumberField IsDedekindDomain Filter MeasureTheory
open scoped Topology ContDiff
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n]

section Charts
variable {K : Type} [Field K]

/-- Total extensions used only on the corresponding open chart. -/
def xChart (f : Charts K) (p : K × K) : ℂ := by
  classical exact if h : p.1 ≠ 0 then f.1 (Units.mk0 p.1 h) p.2 else 0

def yChart (f : Charts K) (p : K × K) : ℂ := by
  classical exact if h : p.2 ≠ 0 then f.2 p.1 (Units.mk0 p.2 h) else 0

def finiteTest [TopologicalSpace K] (f : Charts K) : Prop :=
  IsLocallyConstant (fun p : Kˣ × K => f.1 p.1 p.2) ∧
  IsLocallyConstant (fun p : K × Kˣ => f.2 p.1 p.2) ∧
  ∃ C : Set (K × K), IsCompact C ∧ (0 : K × K) ∉ C ∧
    ∀ p ∉ C, xChart f p = 0 ∧ yChart f p = 0

/-- In real coordinates the chart is smooth, and each derivative decays to
all orders at both ends. Taking every N allows the ordinary Euclidean norm
also at a complex place (where the normalized modulus is the norm squared). -/
def rapidChart {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : Set E) (f : E → ℂ) : Prop :=
  ContDiffOn ℝ ∞ f U ∧ ∀ k N : ℕ, ∃ C : ℝ, ∀ x ∈ U,
    ‖iteratedFDeriv ℝ k f x‖ ≤ C * min (‖x‖ ^ N) ((‖x‖ ^ N)⁻¹)

def archTest {L : Type} [NormedField L] [NormedAlgebra ℝ L]
    (e : K ≃+* L) (f : Charts K) : Prop :=
  rapidChart {p : L × L | p.1 ≠ 0} (fun p => xChart f (e.symm p.1, e.symm p.2)) ∧
  rapidChart {p : L × L | p.2 ≠ 0} (fun p => yChart f (e.symm p.1, e.symm p.2))
end Charts

namespace Datum
variable (d : Datum F n)

def symbol (v : Place F) := hilbert F d.primitive d.embedding v

def testSet (v : Place F) : Set (Charts (LocalField F v)) :=
  {f | Glues (d.symbol v) f ∧ (by
    classical
    cases v with
    | inr p => exact finiteTest f
    | inl w =>
      by_cases h : w.IsReal
      · exact archTest (InfinitePlace.Completion.ringEquivRealOfIsReal h) f
      · exact archTest (InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (InfinitePlace.not_isReal_iff_isComplex.mp h)) f)}

def integralTransform (v : Place F) :=
  transform n (d.character.localValue F v) (d.symbol v) (modulus F v) (selfDual F d.character v)

/-- The algebraic sum of the test functions and their integral transforms (§4). -/
def schwartz (v : Place F) : Submodule ℂ (Charts (LocalField F v)) :=
  Submodule.span ℂ (d.testSet v ∪ d.integralTransform v '' d.testSet v)

theorem exists_fourier (v : Place F) :
    ∃ L : d.schwartz v →ₗ[ℂ] d.schwartz v, ∀ f, (L f).val = d.integralTransform v f := by sorry

def fourier (v : Place F) := (d.exists_fourier v).choose

theorem fourier_apply (v : Place F) (f : d.schwartz v) :
    (d.fourier v f).val = d.integralTransform v f :=
  (d.exists_fourier v).choose_spec f

/-- The basic vector on the shell with radius q^(-nk) has weight q^((n-1)k).
On that shell the chart of the larger coordinate is the primitive chart. -/
def basicCharts (p : HeightOneSpectrum (𝓞 F)) : Charts (LocalField F (.inr p)) := by
  classical
  let q := p.asIdeal.absNorm
  let weight (r : ℝ) : ℂ := ∑' k : ℕ,
    if r = ((q : ℝ) ^ (n*k))⁻¹ then (q : ℂ) ^ ((n-1)*k) else 0
  let X (x : (LocalField F (.inr p))ˣ) (y : LocalField F (.inr p)) :=
    weight (max ‖(x : LocalField F (.inr p))‖ ‖y‖) *
      (if ‖y‖ ≤ ‖(x : LocalField F (.inr p))‖ then 1 else
        if h : y ≠ 0 then d.symbol (.inr p) x (Units.mk0 y h) else 0)
  let Y (x : LocalField F (.inr p)) (y : (LocalField F (.inr p))ˣ) :=
    weight (max ‖x‖ ‖(y : LocalField F (.inr p))‖) *
      (if ‖x‖ ≤ ‖(y : LocalField F (.inr p))‖ then 1 else
        if h : x ≠ 0 then d.symbol (.inr p) y (Units.mk0 x h) else 0)
  exact (X, Y)

theorem basic_mem (p : HeightOneSpectrum (𝓞 F)) (hp : p.asIdeal.absNorm.Coprime n) :
    d.basicCharts p ∈ d.schwartz (.inr p) := by sorry

/-- An arbitrary reference vector suffices at the finitely many exceptional
places, since every pure tensor may vary there. We choose zero. -/
def basic : (v : Place F) → d.schwartz v
  | .inl _ => 0
  | .inr p => if h : p.asIdeal.absNorm.Coprime n then ⟨_, d.basic_mem p h⟩ else 0

theorem eventually_fourier_basic :
    ∀ᶠ v in cofinite, d.fourier v (d.basic v) = d.basic v := by sorry

end Datum
end MetaplecticPoisson
