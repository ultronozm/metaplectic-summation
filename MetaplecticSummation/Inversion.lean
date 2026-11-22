import MetaplecticSummation.FiniteGerms
import MetaplecticSummation.FiniteInversion

noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField IsDedekindDomain Filter MeasureTheory
open scoped Topology Matrix ENNReal
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)
variable (v : Place F)
def mass (Φ : d.schwartz v) : ℝ≥0∞ :=
  let dx := selfDual F d.character v
  ∫⁻ p, ‖xChart Φ p‖ₑ ^ 2 ∂(dx.prod dx)

/-- Ordinary Fourier inversion at frequency one for the chosen archimedean
character and its self-dual measure. -/
theorem hat_hat_arch_one (w : InfinitePlace F) (f : LocalField F (.inl w) → ℂ)
    (hf : Bruhat (.inl w) f) : d.hat (.inl w) (d.hat (.inl w) f) 1 = f (-1) := by sorry

theorem schwartz_fourier_square (Φ : d.schwartz v) :
    (d.fourier v (d.fourier v Φ)).val = d.torusCharts v ((-1) ^ (n+1)) Φ.val := by
  cases v with
  | inl w => exact d.fourier_square_of_ordinary_inversion _ (d.hat_hat_arch_one w) Φ
  | inr p => exact d.finite_fourier_square p Φ

/-- Finiteness and invariance of the squared norm in Theorem 7.1. -/
theorem fourier_mass (Φ : d.schwartz v) :
    d.mass v Φ < ⊤ ∧ d.mass v (d.fourier v Φ) = d.mass v Φ := by sorry

/-- Theorem 7.1, in the chart model, with §5's lift of the diagonal matrix. -/
theorem schwartz_inversion :
    Function.Bijective (d.fourier v) ∧
    (∀ Φ, (d.fourier v (d.fourier v Φ)).val = d.torusCharts v ((-1) ^ (n+1)) Φ.val) ∧
    (∀ (g : d.cover v) Φ, d.fourier v (g.val Φ) = g.val (d.fourier v Φ)) ∧
    (∀ Φ, d.mass v Φ < ⊤ ∧ d.mass v (d.fourier v Φ) = d.mass v Φ) :=
  ⟨d.fourier_bijective_of_square v (d.schwartz_fourier_square v),
    d.schwartz_fourier_square v, d.fourier_equivariant v, d.fourier_mass v⟩

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
