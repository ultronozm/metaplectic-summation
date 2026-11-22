import MetaplecticSummation.Gauss
import MetaplecticSummation.Inversion
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField MeasureTheory
open scoped ComplexConjugate
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

def jacquetSpace (v : Place F) := Set.range (d.jacquet v)

theorem jacquet_transform_descends (v : Place F) (Φ Ψ : d.schwartz v)
    (h : d.jacquet v Φ = d.jacquet v Ψ) :
    d.jacquet v (d.fourier v Φ) = d.jacquet v (d.fourier v Ψ) := by sorry

theorem jacquet_inversion (v : Place F) (Φ : d.schwartz v) (c : (LocalField F v)ˣ) :
    let e : (LocalField F v)ˣ := (-1) ^ (n+1)
    d.jacquet v (d.fourier v (d.fourier v Φ)) c = d.symbol v (-c) e * d.jacquet v Φ (e*c) := by
  let e : (LocalField F v)ˣ := (-1) ^ (n+1)
  have he : e*e = 1 := by rw [← mul_pow]; simp
  have hval : e.val*e.val = 1 := congrArg Units.val he
  have hm : modulus F v e.val = 1 := by
    cases v <;> simp [modulus,e,Units.val_pow_eq_pow_val]
  have hs : d.symbol v c e * d.symbol v (-1) e = d.symbol v (-c) e := by
    change ((d.unitPairing v c e).val) * ((d.unitPairing v (-1) e).val) = _
    rw [show -c = c * (-1) by simp, ← d.coe_unitPairing, map_mul]
    rfl
  let f (y : LocalField F v) := Φ.val.1 (e*c) (y/e.val) * d.character.localValue F v (-y/c.val)
  have ht := d.integral_local_mul v e f
  dsimp only at ht
  rw [hm,Complex.ofReal_one,div_one] at ht
  have hphase (y : LocalField F v) : -(e.val*y)/c.val = -y/(e*c).val := by
    rw [Units.val_mul]
    field_simp
    linear_combination -y * hval
  have eval (y : LocalField F v) : f (e.val*y) = Φ.val.1 (e*c) y *
      d.character.localValue F v (-y/(e*c).val) := by
    simp only [f,hphase,mul_div_cancel_left₀ _ e.ne_zero]
  simp_rw [eval] at ht
  change d.jacquet v (d.fourier v (d.fourier v Φ)) c = d.symbol v (-c) e * d.jacquet v Φ (e*c)
  unfold jacquet
  rw [d.schwartz_fourier_square v Φ]
  change (∫ y, (d.symbol v c e * d.symbol v (-1) e * Φ.val.1 (e*c) (y/e.val)) *
    d.character.localValue F v (-y/c.val) ∂_) = _
  rw [hs]
  simp_rw [mul_assoc (d.symbol v (-c) e)]
  rw [integral_const_mul]
  exact congrArg (d.symbol v (-c) e * ·) ht.symm

def mellin (v : Place F) (W ω : Weight v) (s : ℂ) :=
  d.lineIntegral v fun x => W x * ω x * (modulus F v x : ℂ) ^ s

/-- Tate's normalization on the open strip. Smooth compact tests supported
away from zero suffice to determine the scalar at each point of the strip. -/
def TateEquation (v : Place F) (ω : Weight v) (s γ : ℂ) : Prop :=
  ∀ g : Weight v, TestWeight v g →
    let ĝ : Weight v := fun y => d.lineIntegral v fun x =>
      (modulus F v x : ℂ) * g x * d.character.localValue F v ((x : LocalField F v) * y)
    d.mellin v ĝ (fun x => (ω x)⁻¹) (1-s) = γ * d.mellin v g ω s

/-- Proposition 10.20, with both gamma factors specified by Tate's equation. -/
theorem mellin_dual (v : Place F) (W : Weight v) (hw : TestWeight v W) (β : (LocalField F v)ˣ)
    (support : ∀ x, W x ≠ 0 → ∃ u : (LocalField F v)ˣ, x = β * u ^ n)
    (ω : (LocalField F v)ˣ →* Circle) (hω : Continuous ω) (s : ℂ)
    (lo : -(1/(n : ℝ)) < s.re) (hi : s.re < 0) :
    let η : Weight v := fun x => (ω x : ℂ) * d.symbol v β x
    ∃ γ₁ γ₂ : ℂ, d.TateEquation v (fun x => ((ω x : ℂ)^n)⁻¹) (-(n : ℂ)*s) γ₁ ∧
      d.TateEquation v η (1+s) γ₂ ∧
      d.mellin v (d.dualWeight v W) (fun x => ω x) s =
        (Real.sqrt (modulus F v (n : LocalField F v)) : ℂ)⁻¹ * η (-1) * γ₁ * γ₂ *
          d.mellin v W (fun x => (ω x : ℂ)⁻¹) (-s) := by sorry

/-- Proposition 10.27, with valuations written as powers of the residue cardinality. -/
theorem untwistedVector (p : Prime F) (hp : p.asIdeal.absNorm.Coprime n) (hψ : d.UnramifiedAt (.inr p))
    (a c : (LocalField F (.inr p))ˣ) (i j : ℤ)
    (ha : ‖(a : LocalField F (.inr p))‖ = (p.asIdeal.absNorm : ℝ)^(-i))
    (hc : ‖(c : LocalField F (.inr p))‖ = (p.asIdeal.absNorm : ℝ)^(-j)) :
    let v : Place F := .inr p
    let q : ℝ := p.asIdeal.absNorm
    let W : Weight v := fun x => if ‖(x : LocalField F v)‖ = 1 then d.symbol v a x else 0
    let shell := fun U : Set (LocalField F v) =>
      ∫ t in U, d.character.localValue F v t ∂(selfDual F d.character v)
    (i ≡ j [ZMOD n] → d.dualWeight v W c =
      (1 - (q : ℂ)⁻¹) * shell {t | ‖t‖ ^ n ≤ ‖(c : LocalField F v)‖} -
      (q : ℂ)⁻¹ * shell {t | ‖t‖ ^ n = q * ‖(c : LocalField F v)‖}) ∧
    (¬ i ≡ j [ZMOD n] →
      (¬ (n : ℤ) ∣ j-1 → d.dualWeight v W c = 0) ∧
      ∀ k : ℤ, j = n*k+1 → ∀ t : (LocalField F v)ˣ, ‖(t : LocalField F v)‖ = q^(-k) →
        d.dualWeight v W c = d.unitGauss p (fun x => d.symbol v (c/a) x)
          (-((t : LocalField F v)^n) / c) * shell {y | ‖y‖ = q^(-k)}) := by sorry

def powerAverage (v : Place F) (f : Charts (LocalField F v)) : Charts (LocalField F v) :=
  let avg := fun g : Weight v => d.lineIntegral v fun x =>
    if ∃ u : (LocalField F v)ˣ, x = u^n then (modulus F v x ^ (1+1/(n : ℝ)) : ℝ) * g x else 0
  (fun x y => avg fun a => (dilateCharts a f).1 x y,
   fun x y => avg fun a => (dilateCharts a f).2 x y)

def intertwiner (v : Place F) (f : Charts (LocalField F v)) :=
  radon n (d.symbol v) (modulus F v) (selfDual F d.character v) f 1

theorem leading_fourier_test (v : Place F) (Φ : d.schwartz v) (h : Φ.val ∈ d.testSet v) :
    d.leading v (d.fourier v Φ) =
      ((n : ℂ) / ((modulus F v (n : LocalField F v) ^ (3/2 : ℝ) : ℝ) : ℂ)) •
        d.intertwiner v (d.powerAverage v Φ.val) := by sorry

theorem finite_boundary_image (p : Prime F) (g : Charts (LocalField F (.inr p))) :
    let v : Place F := .inr p
    g ∈ LinearMap.range (d.leading v) ↔ ∃ f : Charts (LocalField F v),
      Glues (d.symbol v) f ∧ IsLocallyConstant (fun z : (LocalField F v)ˣ × LocalField F v => f.1 z.1 z.2) ∧
      IsLocallyConstant (fun z : LocalField F v × (LocalField F v)ˣ => f.2 z.1 z.2) ∧
      (∀ u : (LocalField F v)ˣ, dilateCharts (u^n) f =
        ((modulus F v (u^n : (LocalField F v)ˣ) ^ (-1-1/(n : ℝ)) : ℝ) : ℂ) • f) ∧
      g = d.intertwiner v f := by sorry

end MetaplecticPoisson.Datum
