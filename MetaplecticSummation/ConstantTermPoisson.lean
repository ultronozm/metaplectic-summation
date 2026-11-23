import MetaplecticSummation.FourierCoefficients
import MetaplecticSummation.AdelicFourierIntegrals

/-! The two applications of additive Poisson summation in Proposition B.4. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField IsDedekindDomain MeasureTheory Filter
open scoped Topology
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

private theorem tsum_zero_add_units (a : F → ℂ) (ha : Summable a) :
    (∑' x : F, a x) = a 0 + ∑' u : Fˣ, a u.val := by
  let S : Finset F := {0}
  let e : Fˣ ≃ ((S : Set F)ᶜ : Set F) := unitsEquivNeZero.trans (Equiv.subtypeEquivRight fun x => by simp [S])
  rw [← ha.sum_add_tsum_compl (s := S)]
  rw [show ∑ t ∈ S, a t = a 0 from Finset.sum_singleton _ _,← e.tsum_eq (fun x => a x.val)]
  rfl

/-- The first additive Poisson identity in B.4, for each rational power-class representative. -/
theorem axisLine_poisson (Φ : ∀ v, d.schwartz v) (hΦ : ∀ᶠ v in cofinite, Φ v = d.basic v) (y : Fˣ) :
    (∏ᶠ v, d.axisLine v (Φ v) (atPlace v y) 0) +
      (∑' t : Fˣ, ∏ᶠ v, d.marginal v (Φ v) (atPlace v (t^n/y))) =
    (∏ᶠ v, (d.leading v (d.fourier v (Φ v))).2 0 (atPlace v y)) +
      ∑' t : Fˣ, ∏ᶠ v, d.axis v (d.fourier v (Φ v)) (atPlace v (t^n*y)) := by
  let f := fun v => d.axisLine v (Φ v) (atPlace v y)
  have hf (v) : Bruhat v (f v) := d.axisLine_bruhat v _ _
  obtain ⟨ha,hb,eqn⟩ := d.additivePoisson_tensor f hf (d.eventually_axisLine_basic Φ hΦ y)
  rw [tsum_zero_add_units _ ha.of_norm,tsum_zero_add_units _ hb.of_norm] at eqn
  simp only [map_zero] at eqn
  change (∏ᶠ v, f v 0) + (∑' t : Fˣ, ∏ᶠ v, f v (atPlace v t)) =
    (∏ᶠ v, d.hat v (f v) 0) + ∑' t : Fˣ, ∏ᶠ v, d.hat v (f v) (atPlace v t) at eqn
  simpa only [f,d.axisLine_product,d.axisLine_hat_zero_product Φ y (fun v => Bruhat.integrable d (hf v)),
    d.axisLine_hat_product] using eqn

/-- The second additive Poisson identity in B.4, for each rational power-class representative. -/
theorem axisDensity_poisson (Φ : ∀ v, d.schwartz v) (hΦ : ∀ᶠ v in cofinite, Φ v = d.basic v) (x : Fˣ) :
    (∏ᶠ v, (d.leading v (Φ v)).2 0 (atPlace v (-1/x))) +
      (∑' t : Fˣ, ∏ᶠ v, d.axis v (Φ v) (atPlace v (-(t^n)/x))) =
    (∏ᶠ v, d.hat v (d.axisDensity v (Φ v) (atPlace v x)) 0) +
      ∑' t : Fˣ, ∏ᶠ v, d.marginal v (d.fourier v (Φ v)) (atPlace v (t^n*x)) := by
  let f := fun v => d.axisDensity v (Φ v) (atPlace v x)
  obtain ⟨ha,hb,eqn⟩ := d.additivePoisson_tensor f (fun v => d.axisDensity_bruhat v _ _) (d.eventually_axisDensity_basic Φ hΦ x)
  rw [tsum_zero_add_units _ ha.of_norm,tsum_zero_add_units _ hb.of_norm] at eqn
  simp only [map_zero] at eqn
  change (∏ᶠ v, f v 0) + (∑' t : Fˣ, ∏ᶠ v, f v (atPlace v t)) =
    (∏ᶠ v, d.hat v (f v) 0) + ∑' t : Fˣ, ∏ᶠ v, d.hat v (f v) (atPlace v t) at eqn
  simpa only [f,d.axisDensity_zero_product,d.axisDensity_product,d.axisDensity_hat_product] using eqn

end MetaplecticPoisson.Datum
