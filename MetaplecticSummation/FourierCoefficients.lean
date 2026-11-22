import MetaplecticSummation.Jacquet
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField IsDedekindDomain MeasureTheory Filter
open scoped Topology
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

def marginal (v : Place F) (Φ : d.schwartz v) (c : (LocalField F v)ˣ) :=
  ∫ y, Φ.val.1 c y ∂(selfDual F d.character v)

def axis (v : Place F) (Φ : d.schwartz v) (y : (LocalField F v)ˣ) := Φ.val.2 0 y

def Bruhat (v : Place F) (g : LocalField F v → ℂ) : Prop := by
  classical
  cases v with
  | inr p => exact IsLocallyConstant g ∧ HasCompactSupport g
  | inl w =>
    by_cases h : w.IsReal
    · exact ∃ f : SchwartzMap ℝ ℂ, ∀ x, g x = f (InfinitePlace.Completion.ringEquivRealOfIsReal h x)
    · exact ∃ f : SchwartzMap ℂ ℂ, ∀ x, g x = f (InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (InfinitePlace.not_isReal_iff_isComplex.mp h) x)

def hat (v : Place F) (g : LocalField F v → ℂ) (u : LocalField F v) :=
  ∫ t, g t * d.character.localValue F v (u*t) ∂(selfDual F d.character v)

/-- The two marginal identities of Appendix A, on the full Schwartz space. -/
theorem marginal_fourier (v : Place F) (Φ : d.schwartz v) (x y : (LocalField F v)ˣ) :
    let N : ℂ := modulus F v (n : LocalField F v)
    let k : ℂ := (Real.sqrt (modulus F v (n : LocalField F v)))⁻¹
    ∃ ν σ : LocalField F v → ℂ, Bruhat v ν ∧ Bruhat v σ ∧
      (∀ u : (LocalField F v)ˣ,
        ν u = d.symbol v (-1) y / (modulus F v y : ℂ) * d.marginal v Φ (u^n/y) ∧
        σ u = N / (modulus F v x : ℂ) * (modulus F v u : ℂ)^(n-1) * d.axis v Φ (-(u^n)/x)) ∧
      (∀ u : (LocalField F v)ˣ,
        d.axis v (d.fourier v Φ) (u^n*y) = k * (modulus F v u : ℂ)^(1-(n : ℤ)) * d.hat v ν u ∧
        d.marginal v (d.fourier v Φ) (u^n*x) = k * d.hat v σ u) := by sorry

abbrev AdeleQuotient (F : Type) [Field F] [NumberField F] :=
  Adeles F ⧸ AdeleRing.principalSubgroup (𝓞 F) F

local instance : MeasurableSpace (AdeleQuotient F) := borel _
theorem exists_quotient_measure :
    ∃! μ : Measure (AdeleQuotient F), μ.IsAddHaarMeasure ∧ IsProbabilityMeasure μ := by sorry

def component (u : Adeles F) (v : Place F) : LocalField F v :=
  match v with
  | .inl w => u.1 w
  | .inr p => u.2 p

/-- The theta series at an upper unipotent translate, written in the common rational chart. -/
def translatedTheta (Φ : ∀ v, d.schwartz v) (u : Adeles F) : ℂ :=
  ∑' p : RationalPoint F, ∏ᶠ v,
    let z := diagonalPoint p v
    if p.val.1 ≠ 0 then xChart (Φ v) (z.1, z.2 + component u v * z.1) else yChart (Φ v) z

def coefficient (Φ : ∀ v, d.schwartz v) (a : F) : ℂ :=
  ∫ q : AdeleQuotient F, d.translatedTheta Φ q.out *
    (d.character.toChar (-(algebraMap F (Adeles F) a * q.out)) : ℂ)
    ∂(exists_quotient_measure (F := F)).exists.choose

def constantTerm (Φ : ∀ v, d.schwartz v) :=
  (∑' y : Fˣ, ∏ᶠ v, d.axis v (Φ v) (atPlace v y)) +
    ∑' x : Fˣ, ∏ᶠ v, d.marginal v (Φ v) (atPlace v x)

theorem unfolding (Φ : ∀ v, d.schwartz v) (h : ∀ᶠ v in cofinite, Φ v = d.basic v) :
    d.coefficient Φ 0 = d.constantTerm Φ ∧
    Summable (fun c : Fˣ => ‖∏ᶠ v, d.jacquet v (Φ v) (atPlace v c)‖) ∧
    d.coefficient Φ 1 = ∑' c : Fˣ, ∏ᶠ v, d.jacquet v (Φ v) (atPlace v c) := by sorry

abbrev GlobalClass (n : ℕ) (F : Type) [Field F] := Fˣ ⧸ (powMonoidHom n : Fˣ →* Fˣ).range

/-- Appendix B's Poisson formula on multiplicative power classes. -/
theorem powerClass_poisson (β : (v : Place F) → PowerClass n v → ℂ)
    (hβ : ∀ᶠ p : HeightOneSpectrum (𝓞 F) in cofinite, ∀ c, β (.inr p) c =
      if ∃ u : (LocalField F (.inr p))ˣ, ‖(u : LocalField F (.inr p))‖ = 1 ∧
        QuotientGroup.mk u = c then 1 else 0) :
    let eval := fun (v : Place F) (x : GlobalClass n F) =>
      (QuotientGroup.mk (atPlace v x.out) : PowerClass n v)
    let dual := fun (v : Place F) (y : PowerClass n v) =>
      (n : ℂ)⁻¹ * ∑ᶠ c : PowerClass n v, d.symbol v c.out y.out * β v c
    (∑' x : GlobalClass n F, ∏ᶠ v, β v (eval v x)) =
      ∑' y : GlobalClass n F, ∏ᶠ v, dual v (eval v y) := by sorry

def axisBoundary (Φ : ∀ v, d.schwartz v) :=
  (n : ℂ)⁻¹ * ∑ᶠ y : GlobalClass n F, ∏ᶠ v,
    (d.leading v (Φ v)).2 0 (atPlace v y.out)

theorem constantTerm_identity (Φ : ∀ v, d.schwartz v) (h : ∀ᶠ v in cofinite, Φ v = d.basic v) :
    let dual := fun v => d.fourier v (Φ v)
    d.constantTerm Φ + d.axisBoundary Φ = d.constantTerm dual + d.axisBoundary dual := by sorry

end MetaplecticPoisson.Datum
