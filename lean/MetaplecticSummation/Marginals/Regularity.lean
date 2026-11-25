import MetaplecticSummation.TransformedMarginals
import MetaplecticSummation.RadonDecay

/-! Schwartz regularity of the Radon marginal at all number-field places. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField MeasureTheory
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

private theorem arch_bruhat_reflect (w : InfinitePlace F) {f : w.Completion → ℂ}
    (hf : Bruhat (.inl w) f) : Bruhat (.inl w) (fun t => f (-t)) := by
  have go {L : Type} [NormedField L] [NormedAlgebra ℝ L] (e : w.Completion ≃+* L)
      (G : SchwartzMap L ℂ) (hG : ∀ t, f t = G (e t)) :
      ∃ T : SchwartzMap L ℂ, ∀ t, f (-t) = T (e t) := by
    refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.neg ℝ) G,fun t => ?_⟩
    rw [hG,map_neg]
    rfl
  dsimp only [Bruhat] at hf ⊢
  split at hf <;> rename_i hw
  · rw [dif_pos hw]
    obtain ⟨G,hG⟩ := hf
    exact go _ G hG
  · rw [dif_neg hw]
    obtain ⟨G,hG⟩ := hf
    exact go _ G hG

/-- Both for wild finite places and for archimedean places, the Radon
marginal is Schwartz–Bruhat for every local Schwartz section. -/
theorem axisLine_bruhat (v : Place F) (Φ : d.schwartz v) (y : (LocalField F v)ˣ) :
    Bruhat v (d.axisLine v Φ y) := by
  cases v with
  | inr p => exact d.finite_axisLine_bruhat p Φ y
  | inl w =>
    let v : Place F := .inl w
    let K := LocalField F v
    let dx := selfDual F d.character v
    let ν := d.axisLine v Φ y
    have hR := (d.schwartz_radon_rapid v Φ).2
    have hc : Continuous ν := hR.1.comp
      (f := fun t : K => (((0 : K),y),t)) (continuous_const.prodMk continuous_id)
    have hi : Integrable ν dx := hR.integrable dx (d.integrable_local_inv_cube v) (0,y)
    let x := -1/y
    have hx : -1/x = y := div_div_cancel _ _
    let Ψ := d.fourier v Φ
    have eqn := d.axisDensity_transform_eq_hat v Φ Ψ (d.fourier_apply v Φ) x (hx ▸ hi)
    rw [hx] at eqn
    let N := modulus F v (n : K)
    have hn : (n : K) ≠ 0 := by
      simpa only [map_natCast,map_zero] using (diagonal F v).injective.ne (Nat.cast_ne_zero.mpr (NeZero.ne n) : (n:F) ≠ 0)
    have hN : 0 < N := pow_pos (norm_pos_iff.mpr hn) _
    let c := (N : ℂ) / (modulus F v x.val : ℂ) * (Real.sqrt N : ℂ)⁻¹
    have hc₀ : c ≠ 0 := mul_ne_zero
      (div_ne_zero (Complex.ofReal_ne_zero.mpr hN.ne') (Complex.ofReal_ne_zero.mpr (modulus_ne_zero v x)))
      (inv_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos_of_pos hN).ne'))
    have hh : d.hat v ν = fun t => c⁻¹ * d.axisDensity v Ψ x t := by
      funext t
      rw [eqn]
      exact (inv_mul_cancel_left₀ hc₀ _).symm
    have hhat : Bruhat v (d.hat v ν) := hh ▸ Bruhat.const_mul v (d.axisDensity_bruhat v Ψ x) _
    have href := d.arch_hat_bruhat w hhat
    rw [d.arch_hat_hat_of_integrable w hc hi (hhat.integrable d)] at href
    simpa only [neg_neg] using arch_bruhat_reflect w href

end MetaplecticPoisson.Datum
