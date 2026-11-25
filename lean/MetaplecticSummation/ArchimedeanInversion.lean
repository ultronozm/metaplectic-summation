import MetaplecticSummation.LocalParseval
import MetaplecticSummation.ArchimedeanFourierDecay
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! Ordinary Fourier inversion for the chosen additive character and self-dual
measure at every archimedean place. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField MeasureTheory Set CompactlySupported
open scoped ContDiff
variable {F : Type} [Field F] [NumberField F] {n : ℕ} (d : Datum F n) (w : InfinitePlace F)
local notation "vᵥ" => (Sum.inl w : Place F)
local notation "K" => LocalField F vᵥ
local notation "dxᵥ" => selfDual F d.character vᵥ

private theorem integrable_hat_in_coordinates {L : Type} [NormedField L] [NormedAlgebra ℝ L]
    (e : w.Completion ≃+* L) (he : Isometry e) {f : K → ℂ} (hi : Integrable f dxᵥ)
    (g : SchwartzMap L ℂ) (hg : ∀ x, f x = g (e x)) : Integrable (d.hat vᵥ f) dxᵥ := by
  obtain ⟨C,hC,H⟩ := d.hat_decay_of_schwartz_slices w e he (SchwartzSliceFamily.const e g hg)
    (fun _ => hi) {()} isCompact_singleton 3
  let M := ∫ t, ‖f t‖ ∂dxᵥ
  have hM : 0 ≤ M := integral_nonneg (fun t => norm_nonneg _)
  apply ((d.arch_integrable_inv_cube w).const_mul (max C (8*M))).mono'
    (d.continuous_hat _ hi).aestronglyMeasurable (.of_forall (fun y => ?_))
  change ‖d.hat vᵥ f y‖ ≤ max C (8*M) * ((1+‖y‖)^3)⁻¹
  rw [← div_eq_mul_inv,le_div_iff₀ (by positivity)]
  rcases le_total 1 ‖y‖ with hy | hy
  · exact (H () (mem_singleton _) y hy).trans (le_max_left ..)
  · have h : ‖d.hat vᵥ f y‖ ≤ M := by
      simpa only [hat,norm_mul,d.character.norm_localValue,mul_one,M] using
        norm_integral_le_integral_norm (μ := dxᵥ) (fun t => f t * d.character.localValue F vᵥ (y*t))
    have hy' : (1+‖y‖)^3 ≤ (2:ℝ)^3 := pow_le_pow_left₀ (by positivity) (by linarith) _
    exact (mul_le_mul h hy' (by positivity) hM).trans ((by ring_nf : M*2^3 = 8*M).le.trans (le_max_right ..))

/-- Smooth compactly supported real test functions in archimedean coordinates
distinguish continuous complex functions on the completion. -/
private theorem arch_separating_tests {L : Type} [NormedField L] [NormedAlgebra ℝ L]
    [FiniteDimensional ℝ L] [MeasurableSpace L] [BorelSpace L] [SecondCountableTopology L]
    (e : w.Completion ≃+* L) (he : Isometry e) (a b : K → ℂ) (ha : Continuous a) (hb : Continuous b)
    (H : ∀ p : C_c(K, ℂ), Integrable (d.hat vᵥ p) dxᵥ →
      (∫ x, p x * a x ∂dxᵥ) = ∫ x, p x * b x ∂dxᵥ) : a = b := by
  letI : (dxᵥ).IsAddHaarMeasure := (existsUnique_selfDual F d.character vᵥ).exists.choose_spec.1
  let i : K ≃ᵢ L := ⟨e.toEquiv,he⟩
  let ν := (dxᵥ).map i
  letI : ν.IsAddHaarMeasure := e.toAddEquiv.isAddHaarMeasure_map dxᵥ he.continuous i.symm.continuous
  have ca : Continuous (a ∘ i.symm) := ha.comp i.symm.continuous
  have cb : Continuous (b ∘ i.symm) := hb.comp i.symm.continuous
  have eqn : a ∘ i.symm = b ∘ i.symm := by
    apply (ca.ae_eq_iff_eq (μ := ν) cb).mp
    apply ae_eq_of_integral_contDiff_smul_eq ca.locallyIntegrable cb.locallyIntegrable
    intro φ hd hk
    let φc (x : L) : ℂ := φ x
    have hdc : ContDiff ℝ ∞ φc := Complex.ofRealCLM.contDiff.comp hd
    have hkc : HasCompactSupport φc := hk.comp_left Complex.ofReal_zero
    let p : C_c(K,ℂ) :=
      { toFun := fun x => φc (e x)
        continuous_toFun := hdc.continuous.comp he.continuous
        hasCompactSupport' := hkc.comp_homeomorph i.toHomeomorph }
    have hp := d.integrable_hat_in_coordinates w e he (f := p) p.integrable (hkc.toSchwartzMap hdc) (fun _ => rfl)
    have pull (z : K → ℂ) : (∫ t, φ t • (z ∘ i.symm) t ∂ν) = ∫ x, p x * z x ∂dxᵥ := by
      rw [show ν = (dxᵥ).map i.toHomeomorph.toMeasurableEquiv from rfl, integral_map_equiv]
      apply integral_congr_ae
      filter_upwards with x
      change φ (i x) • z (i.symm (i x)) = (φ (i x) : ℂ) * z x
      rw [i.symm_apply_apply,Complex.real_smul]
    rw [pull,pull,H p hp]
  funext x
  simpa only [Function.comp_apply,i.symm_apply_apply] using congrFun eqn (i x)

/-- Fourier inversion for a continuous integrable function with integrable transform,
with respect to the chosen self-dual measure. -/
theorem arch_hat_hat_of_integrable {f : K → ℂ} (hf : Continuous f) (hi : Integrable f dxᵥ)
    (hi' : Integrable (d.hat vᵥ f) dxᵥ) : d.hat vᵥ (d.hat vᵥ f) = fun x => f (-x) := by
  letI : SecondCountableTopology K := (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  letI : LocallyCompactSpace K := inferInstanceAs (LocallyCompactSpace w.Completion)
  letI : (dxᵥ).IsAddHaarMeasure := (existsUnique_selfDual F d.character vᵥ).exists.choose_spec.1
  apply d.hat_hat_of_separating_tests _ _ hf hi hi'
  by_cases hw : w.IsReal
  · exact d.arch_separating_tests w (InfinitePlace.Completion.ringEquivRealOfIsReal hw)
      (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw)
  · exact d.arch_separating_tests w (InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (InfinitePlace.not_isReal_iff_isComplex.mp hw)) (InfinitePlace.Completion.isometry_extensionEmbedding w)

/-- Pointwise Fourier inversion at every frequency for a Schwartz function at a real or complex place. -/
theorem arch_hat_hat (f : K → ℂ) (hf : Bruhat vᵥ f) : d.hat vᵥ (d.hat vᵥ f) = fun x => f (-x) := by
  have hi := Bruhat.integrable d hf
  have go {L : Type} [NormedField L] [NormedAlgebra ℝ L] (e : w.Completion ≃+* L)
      (he : Isometry e) (g : SchwartzMap L ℂ) (hg : ∀ x, f x = g (e x)) :
      d.hat vᵥ (d.hat vᵥ f) = fun x => f (-x) :=
    d.arch_hat_hat_of_integrable w ((g.continuous.comp he.continuous).congr (fun x => (hg x).symm)) hi
      (d.integrable_hat_in_coordinates w e he hi g hg)
  dsimp only [Bruhat] at hf
  split at hf
  · obtain ⟨g,hg⟩ := hf
    exact go _ (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal _) g hg
  · obtain ⟨g,hg⟩ := hf
    exact go _ (InfinitePlace.Completion.isometry_extensionEmbedding w) g hg

end MetaplecticPoisson.Datum
