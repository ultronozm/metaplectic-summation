import MetaplecticSummation.Poisson

noncomputable section
namespace MetaplecticPoisson
namespace Datum

open MeasureTheory Filter NumberField IsDedekindDomain
open scoped ContDiff Topology
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [hn : NeZero n] (d : Datum F n)

abbrev Weight (v : Place F) := (LocalField F v)ˣ → ℂ

def jacquet (v : Place F) (Φ : d.schwartz v) (c : (LocalField F v)ˣ) : ℂ :=
  ∫ y, Φ.val.1 c y * d.character.localValue F v (-y / (c : LocalField F v))
    ∂(selfDual F d.character v)

def lineIntegral (v : Place F) (f : Weight v) : ℂ := by
  classical
  exact ∫ x, if h : x ≠ 0 then f (Units.mk0 x h) / (modulus F v x : ℂ) else 0
    ∂(selfDual F d.character v)

def archSmooth {K L : Type} [Field K] [NormedField L] [NormedAlgebra ℝ L]
    (e : K ≃+* L) (W : Kˣ → ℂ) : Prop := by
  classical
  exact ContDiffOn ℝ ∞ (fun x => if h : e.symm x ≠ 0 then W (Units.mk0 _ h) else 0) {0}ᶜ

def TestWeight (v : Place F) (W : Weight v) : Prop :=
  HasCompactSupport W ∧ (by
    classical
    cases v with
    | inr p => exact IsLocallyConstant W
    | inl w =>
      by_cases h : w.IsReal
      · exact archSmooth (InfinitePlace.Completion.ringEquivRealOfIsReal h) W
      · exact archSmooth (InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (InfinitePlace.not_isReal_iff_isComplex.mp h)) W)

def kernelIntegral (v : Place F) (W : Weight v) (c : (LocalField F v)ˣ) (t : LocalField F v) :=
  d.lineIntegral v fun x => W x * d.symbol v x (-c) *
    d.character.localValue F v (-(t ^ n) / ((c : LocalField F v) * x))

/-- Proposition 10.8 at λ = 1, used for compactly supported test weights. -/
def dualWeight (v : Place F) (W : Weight v) (c : (LocalField F v)ˣ) : ℂ :=
  (Real.sqrt (modulus F v (n : LocalField F v)) : ℂ)⁻¹ *
    ∫ t, d.character.localValue F v t * d.kernelIntegral v W c t ∂(selfDual F d.character v)

theorem jacquet_test_lift (v : Place F) (W : Weight v) (h : TestWeight v W) :
    ∃ Φ : d.schwartz v, Φ.val ∈ d.testSet v ∧ d.jacquet v Φ = W := by sorry

theorem jacquet_fourier_test (v : Place F) (Φ : d.schwartz v) (h : TestWeight v (d.jacquet v Φ)) :
    d.jacquet v (d.fourier v Φ) = d.dualWeight v (d.jacquet v Φ) := by sorry

theorem root_fourier (v : Place F) (W : Weight v) (h : TestWeight v W)
    (c lam : (LocalField F v)ˣ) :
    d.dualWeight v W (c * lam ^ n) =
      (Real.sqrt (modulus F v (n : LocalField F v)) : ℂ)⁻¹ * (modulus F v lam : ℂ) *
        ∫ t, d.kernelIntegral v W c t * d.character.localValue F v (t * lam)
          ∂(selfDual F d.character v) := by sorry

def GoodOutside (S : Finset (Place F)) : Prop :=
  S.Nonempty ∧ (∀ w, Sum.inl w ∈ S) ∧ ∀ p : HeightOneSpectrum (𝓞 F), Sum.inr p ∉ S →
    p.asIdeal.absNorm.Coprime n ∧ ∀ x : LocalField F (.inr p), ‖x‖ ≤ 1 →
      d.character.localValue F (.inr p) x = 1

abbrev Weights (S : Finset (Place F)) := (v : S) → Weight v.val
abbrev Admissible {S : Finset (Place F)} (W : Weights S) := ∀ v, TestWeight v.val (W v)
abbrev PowerClass (n : ℕ) (v : Place F) := (LocalField F v)ˣ ⧸ (powMonoidHom n :
  (LocalField F v)ˣ →* (LocalField F v)ˣ).range
abbrev Classes (n : ℕ) (S : Finset (Place F)) := (v : S) → PowerClass n v.val

include hn in
theorem finite_power_classes (v : Place F) : Finite (PowerClass n v) := by sorry

def moment {S : Finset (Place F)} (W : Weights S) (β : Classes n S) : ℂ := by
  classical
  exact ∏ v : S, d.lineIntegral v.val fun x =>
    if (QuotientGroup.mk x : PowerClass n v.val) = β v then
      W v x * ((modulus F v.val x ^ (1 / (n : ℝ)) : ℝ) : ℂ) else 0

def globalWeight {S : Finset (Place F)} (W : Weights S) (dual : Bool) (c : Fˣ) : ℂ := by
  classical
  exact ∏ᶠ v, if hv : v ∈ S then
    (if dual then d.dualWeight v (W ⟨v,hv⟩) else W ⟨v,hv⟩) (atPlace v c)
    else d.jacquet v (if dual then d.fourier v (d.basic v) else d.basic v) (atPlace v c)

/-- The constants are chosen once for all test weights. -/
def LineFormula (S : Finset (Place F)) (ρ : Classes n S → ℂ) : Prop :=
  ∀ W : Weights S, Admissible W →
    Summable (fun c => ‖d.globalWeight W false c‖) ∧
    Summable (fun c => ‖d.globalWeight W true c‖) ∧
    (∑' c, d.globalWeight W false c) = (∑' c, d.globalWeight W true c) +
      ∑ᶠ β, ρ β * d.moment W β

theorem lineSummation (S : Finset (Place F)) (hS : d.GoodOutside S) :
    ∃! ρ, d.LineFormula S ρ := by sorry

theorem line_degree_one (a : Datum F 1) (S : Finset (Place F)) (hS : a.GoodOutside S) :
    a.LineFormula S (fun _ => 0) := by sorry

end Datum
end MetaplecticPoisson
