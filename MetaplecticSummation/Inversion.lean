import MetaplecticSummation.Schwartz
import MetaplecticSummation.Shears
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField IsDedekindDomain Filter MeasureTheory
open scoped Topology Matrix ENNReal
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)
variable (v : Place F)
abbrev Operators := d.schwartz v ≃ₗ[ℂ] d.schwartz v

def IsUpper (u : LocalField F v) (g : d.Operators v) : Prop :=
  ∀ Φ, (∀ x y, (g Φ).val.1 x y = Φ.val.1 x (y + u * x)) ∧
    ∀ y, (g Φ).val.2 0 y = Φ.val.2 0 y

def IsLower (u : LocalField F v) (g : d.Operators v) : Prop :=
  ∀ Φ, (∀ x y, (g Φ).val.2 x y = Φ.val.2 (x + u * y) y) ∧
    ∀ x, (g Φ).val.1 x 0 = Φ.val.1 x 0

theorem exists_upper (u : LocalField F v) : ∃! g, d.IsUpper v u g := by sorry
theorem exists_lower (u : LocalField F v) : ∃! g, d.IsLower v u g := by sorry

def IsCentralScalar (g : d.Operators v) : Prop :=
  ∃ z : Mu F n, ∀ Φ, g Φ = ((d.embedding z : ℂˣ) : ℂ) • Φ

/-- The image of the local cover acting on Schwartz functions, generated as in §5. -/
def cover : Subgroup (d.Operators v) := Subgroup.closure
  {g | d.IsCentralScalar v g ∨ (∃ u, d.IsUpper v u g) ∨ ∃ u, d.IsLower v u g}

theorem kubota_projection :
    ∃ π : d.cover v →* Matrix.SpecialLinearGroup (Fin 2) (LocalField F v),
      Function.Surjective π ∧
      (∀ g, π g = 1 ↔ d.IsCentralScalar v g.val) ∧
      (∀ g u, d.IsUpper v u g.val → (π g).val = !![1,u;0,1]) ∧
      (∀ g u, d.IsLower v u g.val → (π g).val = !![1,0;u,1]) := by sorry

def torusCharts (a : (LocalField F v)ˣ) (Φ : Charts (LocalField F v)) : Charts (LocalField F v) :=
  (fun x y => d.symbol v x a * d.symbol v (-1) a * Φ.1 (a*x) (y/a),
   fun x y => d.symbol v a y * Φ.2 (a*x) (y/a))

def mass (Φ : d.schwartz v) : ℝ≥0∞ :=
  let dx := selfDual F d.character v
  ∫⁻ p, ‖xChart Φ p‖ₑ ^ 2 ∂(dx.prod dx)

/-- Theorem 7.1, in the chart model, with §5's lift of the diagonal matrix. -/
theorem schwartz_inversion :
    Function.Bijective (d.fourier v) ∧
    (∀ Φ, (d.fourier v (d.fourier v Φ)).val = d.torusCharts v ((-1) ^ (n+1)) Φ.val) ∧
    (∀ (g : d.cover v) Φ, d.fourier v (g.val Φ) = g.val (d.fourier v Φ)) ∧
    (∀ Φ, d.mass v Φ < ⊤ ∧ d.mass v (d.fourier v Φ) = d.mass v Φ) := by sorry

theorem finite_germs (p : HeightOneSpectrum (𝓞 F)) (Φ : d.schwartz (.inr p)) :
    (d.leading (.inr p) Φ = 0 ↔ Φ.val ∈ d.testSet (.inr p)) ∧
    (∃ C : Set (LocalField F (.inr p) × LocalField F (.inr p)), IsCompact C ∧
      ∀ z ∉ C, xChart Φ z = 0 ∧ yChart Φ z = 0) ∧
    ∀ᶠ z in 𝓝 (0 : LocalField F (.inr p) × LocalField F (.inr p)),
      xChart Φ z = xChart (d.leading (.inr p) Φ) z ∧
      yChart Φ z = yChart (d.leading (.inr p) Φ) z := by sorry

/-- Section 4's root kernel in the X chart. The deleted axis and the
zero-determinant line have measure zero and are assigned value zero. -/
def rootKernel (x' : (LocalField F v)ˣ) (y' : LocalField F v)
    (z : LocalField F v × LocalField F v) : ℂ := by
  classical
  let det := z.1 * y' - z.2 * x'
  exact if h : z.1 ≠ 0 ∧ det ≠ 0 then
    d.symbol v (Units.mk0 _ h.1) (-x') *
      ((modulus F v (n : LocalField F v) ^ (-(3/2 : ℝ)) : ℝ) : ℂ) *
      ∑ᶠ t : {t : LocalField F v // t^n = det},
        d.character.localValue F v t.val * ((modulus F v t.val : ℂ) ^ (1 - (n : ℤ)))
    else 0

theorem fourier_root_kernel (Φ : d.schwartz v) (x' : (LocalField F v)ˣ) (y' : LocalField F v) :
    let dx := selfDual F d.character v
    let integrand := fun z => xChart Φ z * d.rootKernel v x' y' z
    Integrable integrand (dx.prod dx) ∧
      (d.fourier v Φ).val.1 x' y' = ∫ z, integrand z ∂(dx.prod dx) := by sorry

end MetaplecticPoisson.Datum
