import MetaplecticSummation.SchwartzSliceFamily
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Differentiation of the fiber integrals in the archimedean Radon charts. -/
noncomputable section
namespace MetaplecticPoisson
open MeasureTheory Set Filter
open scoped Topology ContDiff

variable {X E : Type} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure X} {g : X → E → ℂ}

/-- An integrable majorant at each order permits every real derivative to pass under
the fiber integral. The measure on the fiber need not be finite. -/
theorem smooth_fiber_integral
    (hs : ∀ x, ContDiff ℝ ∞ (g x))
    (hm : ∀ k t, AEStronglyMeasurable (fun x => iteratedFDeriv ℝ k (g x) t) μ)
    (hb : ∀ k, ∃ b : X → ℝ, Integrable b μ ∧ ∀ x t, ‖iteratedFDeriv ℝ k (g x) t‖ ≤ b x) :
    ContDiff ℝ ∞ (fun t => ∫ x, g x t ∂μ) ∧
    ∀ k, iteratedFDeriv ℝ k (fun t => ∫ x, g x t ∂μ) =
      fun t => ∫ x, iteratedFDeriv ℝ k (g x) t ∂μ := by
  have hi (k : ℕ) (t : E) : Integrable (fun x => iteratedFDeriv ℝ k (g x) t) μ := by
    obtain ⟨b, hbi, h⟩ := hb k
    exact hbi.mono' (hm k t) (.of_forall (fun x => h x t))
  have hd (k : ℕ) (t : E) :
      HasFDerivAt (fun u => ∫ x, iteratedFDeriv ℝ k (g x) u ∂μ)
        (∫ x, fderiv ℝ (iteratedFDeriv ℝ k (g x)) t ∂μ) t := by
    obtain ⟨b, hbi, h⟩ := hb (k+1)
    let c := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k+1) => E) ℂ
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le (s := univ) Filter.univ_mem
      (.of_forall (hm k)) (hi k t) (bound := b)
    · have H := c.continuous.comp_aestronglyMeasurable (hm (k+1) t)
      simpa only [iteratedFDeriv_succ_eq_comp_left, Function.comp_def, c,
        LinearIsometryEquiv.apply_symm_apply] using H
    · exact .of_forall (fun x t _ => by simpa only [iteratedFDeriv_succ_eq_comp_left,
        Function.comp_apply, LinearIsometryEquiv.norm_map] using h x t)
    · exact hbi
    · exact .of_forall (fun x u _ => ((hs x).differentiable_iteratedFDeriv
        (show (k : WithTop ℕ∞) < ∞ by exact_mod_cast ENat.coe_lt_top k) u).hasFDerivAt)
  have eqn (k : ℕ) : iteratedFDeriv ℝ k (fun t => ∫ x, g x t ∂μ) =
      fun t => ∫ x, iteratedFDeriv ℝ k (g x) t ∂μ := by
    induction k with
    | zero =>
      funext t
      simp_rw [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
      exact ((continuousMultilinearCurryFin0 ℝ E ℂ).symm.toContinuousLinearEquiv.integral_comp_comm _).symm
    | succ k ih =>
      funext t
      simp_rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, ih, (hd k t).fderiv]
      exact (ContinuousLinearEquiv.integral_comp_comm (𝕜 := ℝ) (E := E →L[ℝ] (E [×k]→L[ℝ] ℂ))
        (F := E [×(k+1)]→L[ℝ] ℂ) ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k+1) => E) ℂ).symm.toContinuousLinearEquiv)
        (fun x => fderiv ℝ (iteratedFDeriv ℝ k (g x)) t) (μ := μ)).symm
  refine ⟨contDiff_of_differentiable_iteratedFDeriv (fun k _ => ?_), eqn⟩
  rw [eqn]
  exact fun t => (hd k t).differentiableAt

/-- Uniform integrable majorants for the weighted fiber derivatives give a bounded
Schwartz family after integration, including for compact sets containing the zero parameter. -/
theorem SchwartzSliceFamily.of_integral
    {P K L : Type} [TopologicalSpace P] [NormedField K] [NormedField L] [NormedAlgebra ℝ L]
    (e : K ≃+* L) (G : P → X → L → ℂ)
    (hs : ∀ q x, ContDiff ℝ ∞ (G q x))
    (hm : ∀ q k t, AEStronglyMeasurable (fun x => iteratedFDeriv ℝ k (G q x) t) μ)
    (hb : ∀ T : Set P, IsCompact T → ∀ k N : ℕ, ∃ b : X → ℝ, Integrable b μ ∧
      ∀ q ∈ T, ∀ x t, ‖iteratedFDeriv ℝ k (G q x) t‖ * (1+‖t‖)^N ≤ b x) :
    SchwartzSliceFamily e (fun q t => ∫ x, G q x (e t) ∂μ) := by
  let R (q : P) (t : L) := ∫ x, G q x t ∂μ
  have dif (q : P) := smooth_fiber_integral (μ := μ) (hs q) (hm q) (by
    intro k
    obtain ⟨b,hi,h⟩ := hb {q} isCompact_singleton k 0
    exact ⟨b,hi,fun x t => by simpa using h q (mem_singleton q) x t⟩)
  have bound (T : Set P) (hT : IsCompact T) (k N : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ T, ∀ t,
      ‖iteratedFDeriv ℝ k (R q) t‖ * (1+‖t‖)^N ≤ C := by
    obtain ⟨b,hi,H⟩ := hb T hT k N
    refine ⟨max 0 (∫ x, b x ∂μ),le_max_left ..,fun q hq t => ?_⟩
    have hi' : Integrable (fun x => ‖iteratedFDeriv ℝ k (G q x) t‖ * (1+‖t‖)^N) μ := by
      refine hi.mono' (((hm q k t).norm).mul aestronglyMeasurable_const) (.of_forall (fun x => ?_))
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact H q hq x t
    change ‖iteratedFDeriv ℝ k (fun u => ∫ x, G q x u ∂μ) t‖ * _ ≤ _
    rw [(dif q).2 k]
    calc
      _ ≤ (∫ x, ‖iteratedFDeriv ℝ k (G q x) t‖ ∂μ) * (1+‖t‖)^N :=
        mul_le_mul_of_nonneg_right (norm_integral_le_integral_norm _) (by positivity)
      _ = _ := (integral_mul_const _ _).symm
      _ ≤ _ := (integral_mono hi' hi (fun x => H q hq x t)).trans (le_max_right ..)
  let S (q : P) : SchwartzMap L ℂ :=
    { toFun := R q
      smooth' := (dif q).1
      decay' := by
        intro N k
        obtain ⟨C,_,h⟩ := bound {q} isCompact_singleton k N
        refine ⟨C, fun t => ?_⟩
        rw [mul_comm]
        exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg t)
          (by linarith : ‖t‖ ≤ 1+‖t‖) N) (norm_nonneg _)).trans (h q (mem_singleton q) t) }
  exact ⟨S, fun _ _ => rfl, bound⟩

end MetaplecticPoisson
