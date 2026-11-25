import MetaplecticSummation.Marginals.Regularity

noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField IsDedekindDomain MeasureTheory Filter
open scoped Topology
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

/-- Schwartz regularity of both marginal kernels and the converse Fourier identity
on the full local Schwartz space (Appendix A). -/
theorem schwartz_marginal_kernels (v : Place F) (Φ : d.schwartz v) (x y : (LocalField F v)ˣ) :
    Bruhat v (d.axisLine v Φ y) ∧ Bruhat v (d.axisDensity v Φ x) ∧
    ∀ u : (LocalField F v)ˣ, d.marginal v (d.fourier v Φ) (u^n*x) =
      (Real.sqrt (modulus F v (n : LocalField F v)) : ℂ)⁻¹ * d.hat v (d.axisDensity v Φ x) u :=
  ⟨d.axisLine_bruhat v Φ y,d.axisDensity_bruhat v Φ x,d.reverse_marginal v Φ x⟩

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
        d.marginal v (d.fourier v Φ) (u^n*x) = k * d.hat v σ u) := by
  dsimp only
  obtain ⟨hν,hσ,hrev⟩ := d.schwartz_marginal_kernels v Φ x y
  exact ⟨_,_,hν,hσ,fun t => ⟨d.axisLine_unit v Φ y t,d.axisDensity_unit v Φ x t⟩,
    fun u => ⟨d.axis_fourier v Φ y u,hrev u⟩⟩

end MetaplecticPoisson.Datum
