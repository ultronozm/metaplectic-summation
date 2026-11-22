import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Complex.Basic

/-! Bilinear pairing for the ordinary Fourier integral over a normed field. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open MeasureTheory

def fourierIntegral {K : Type*} [NormedField K] [MeasurableSpace K]
    (μ : Measure K) (ψ : K → ℂ) (f : K → ℂ) (u : K) := ∫ t, f t * ψ (u*t) ∂μ

/-- The bilinear Fourier identity, by absolute convergence of the joint integral. -/
theorem fourierIntegral_swap {K : Type*} [NormedField K] [MeasurableSpace K] [BorelSpace K]
    [SecondCountableTopology K] (μ : Measure K) [SFinite μ] {ψ f g : K → ℂ} (hψ : Continuous ψ) (hnorm : ∀ z, ‖ψ z‖ = 1)
    (hf : Continuous f) (hg : Continuous g) (hfi : Integrable f μ) (hgi : Integrable g μ) :
    (∫ x, fourierIntegral μ ψ f x * g x ∂μ) = ∫ t, f t * fourierIntegral μ ψ g t ∂μ := by
  let H (x t : K) := f t * ψ (x*t) * g x
  have hi : Integrable (Function.uncurry H) (μ.prod μ) := by
    apply (hgi.norm.mul_prod hfi.norm).mono
    · exact ((hf.comp continuous_snd).mul (hψ.comp (continuous_fst.mul continuous_snd)) |>.mul
        (hg.comp continuous_fst)).aestronglyMeasurable
    · filter_upwards with z
      simp [Function.uncurry,H,norm_mul,hnorm,mul_comm]
  calc
    _ = ∫ x, ∫ t, H x t ∂μ ∂μ := by simp only [H,fourierIntegral,integral_mul_const]
    _ = ∫ t, ∫ x, H x t ∂μ ∂μ := integral_integral_swap hi
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with t
      unfold fourierIntegral
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      dsimp [H]
      rw [mul_comm x t]
      ring

end MetaplecticPoisson.Datum
