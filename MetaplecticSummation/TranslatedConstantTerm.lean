import MetaplecticSummation.ConstantTermPoisson

/-! The translated constant terms in the proof of Proposition B.6. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField Filter
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

/-- A local zero of the leading term kills the adelic boundary on a pure tensor. -/
theorem axisBoundary_eq_zero_of_local (Φ : ∀ v, d.schwartz v) (hΦ : ∀ᶠ v in cofinite, Φ v = d.basic v)
    (w : Place F) (hw : d.leading w (Φ w) = 0) : d.axisBoundary Φ = 0 := by
  unfold axisBoundary
  rw [finsum_eq_zero_of_forall_eq_zero,mul_zero]
  intro c
  let a : Fˣ := -1/c.out
  have h := d.axisDensity_zero_product Φ a
  dsimp only [a] at h
  rw [div_div_cancel] at h
  rw [← h]
  refine finprod_eq_zero (fun v => d.axisDensity v (Φ v) (atPlace v a) 0) w ?_ ?_
  · rw [d.axisDensity_zero,hw]
    exact mul_zero _
  · suffices H : ∀ᶠ v in cofinite, d.axisDensity v (Φ v) (atPlace v a) 0 = 1 from eventually_cofinite.mp H
    apply eventually_place_of_finite
    filter_upwards [d.eventually_axisDensity_basic Φ hΦ a] with p hp
    simpa only [norm_zero,zero_le_one,ite_true] using hp 0

/-- For every restricted translate by the local covering groups, the two
unipotent constant coefficients agree under the local vanishing hypotheses of B.6. -/
theorem translated_constant_coefficients_eq (Φ : ∀ v, d.schwartz v) (g : ∀ v, d.cover v)
    (hg : ∀ᶠ v in cofinite, (g v).val (Φ v) = d.basic v) (v w : Place F)
    (hv : d.leading v (Φ v) = 0) (hw : d.leading w (d.fourier w (Φ w)) = 0) :
    d.coefficient (fun q => (g q).val (Φ q)) 0 =
      d.coefficient (fun q => (g q).val (d.fourier q (Φ q))) 0 := by
  let Ψ := fun q => (g q).val (Φ q)
  let dual := fun q => d.fourier q (Ψ q)
  have hd : ∀ᶠ q in cofinite, dual q = d.basic q := by
    filter_upwards [hg,d.eventually_fourier_basic] with q h h'
    exact (congrArg (d.fourier q) h).trans h'
  have he : dual = fun q => (g q).val (d.fourier q (Φ q)) := funext fun q => d.fourier_equivariant q _ _
  have h₁ := d.axisBoundary_eq_zero_of_local Ψ hg v ((d.leading_cover_zero_iff v _ _).mpr hv)
  have h₂ : d.leading w (dual w) = 0 := by
    rw [he]
    exact (d.leading_cover_zero_iff w _ _).mpr hw
  have eqn := d.constantTerm_identity Ψ hg
  change d.constantTerm Ψ + d.axisBoundary Ψ = d.constantTerm dual + d.axisBoundary dual at eqn
  rw [h₁,d.axisBoundary_eq_zero_of_local dual hd w h₂,add_zero,add_zero] at eqn
  rw [← he]
  exact (d.unfolding Ψ hg).1.trans (eqn.trans (d.unfolding dual hd).1.symm)

end MetaplecticPoisson.Datum
