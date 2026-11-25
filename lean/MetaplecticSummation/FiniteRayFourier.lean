import MetaplecticSummation.FiniteLeading
import MetaplecticSummation.CharacterNontrivial
import MetaplecticSummation.FiniteLocalCharacter

/-! One-dimensional Fourier transforms of bounded families of Schwartz–Bruhat
functions over a finite completion, as used in §§4 and 8. -/

noncomputable section
namespace MetaplecticPoisson
open Filter Set MeasureTheory Metric
open scoped Topology ENNReal
open Classical

namespace SmoothFiniteFamily
variable {P K : Type*} [TopologicalSpace P] [WeaklyLocallyCompactSpace P] [NormedField K]
    [ProperSpace K] [MeasurableSpace K] [BorelSpace K]

/-- Fourier transformation in the field variable preserves the finite-place
Schwartz–Bruhat bounds uniformly on each compact set of parameters. -/
theorem fourier {g : P → K → ℂ} (hg : SmoothFiniteFamily g) (dx : Measure K) [dx.IsAddHaarMeasure]
    {ψ : K → ℂ} (hc : IsLocallyConstant ψ) (ha : ∀ x y, ψ (x+y) = ψ x * ψ y)
    (hn : ∃ x, ψ x ≠ 1) : SmoothFiniteFamily (fun p u => ∫ t, g p t * ψ (u*t) ∂dx) := by
  apply smoothFiniteFamily_of_support
  · let G (w : (P × K) × K) := g w.1.1 w.2 * ψ (w.1.2*w.2)
    have hG : IsLocallyConstant G :=
      (hg.1.comp_continuous ((continuous_fst.comp continuous_fst).prodMk continuous_snd)).mul
        (hc.comp_continuous ((continuous_snd.comp continuous_fst).mul continuous_snd))
    have hs (q : P × K) : ∃ C : Set K, IsCompact C ∧ ∀ᶠ w in 𝓝 q, ∀ t ∉ C, G (w,t) = 0 := by
      obtain ⟨T,hT,hq⟩ := exists_compact_mem_nhds q.1
      obtain ⟨C,hC,hvan⟩ := (hg.2 T hT).2.1
      refine ⟨C,hC,?_⟩
      filter_upwards [(continuous_fst.tendsto q).eventually hq] with w hw t ht
      dsimp [G]
      rw [hvan _ hw _ ht,zero_mul]
    exact (locallyConstant_slices_of_localSupport hG hs).comp (fun s => ∫ t, s t ∂dx)
  · intro T hT
    obtain ⟨b,hb⟩ := hn
    obtain ⟨r,hr,hper⟩ := Metric.mem_nhds_iff.mp ((hg.2 T hT).2.2)
    refine ⟨closedBall 0 (‖b‖/r),isCompact_closedBall _ _,?_⟩
    intro p hp u hu
    have hlt : ‖b‖/r < ‖u‖ := by simpa [mem_closedBall,dist_zero_right] using hu
    have hu₀ : u ≠ 0 := norm_pos_iff.mp ((div_nonneg (norm_nonneg b) hr.le).trans_lt hlt)
    let h := b/u
    have hh : h ∈ ball 0 r := by
      rw [mem_ball_zero_iff,norm_div, div_lt_iff₀ (norm_pos_iff.mpr hu₀)]
      simpa [mul_comm] using (div_lt_iff₀ hr).mp hlt
    let f (t : K) := g p t * ψ (u*t)
    have he (t : K) : f (t+h) = f t * ψ b := by
      dsimp [f]
      rw [hper hh p hp t,mul_add,ha,show u*h = b by dsimp [h]; field_simp, mul_assoc]
    have hi := integral_add_right_eq_self (μ := dx) f h
    simp_rw [he] at hi
    rw [integral_mul_const] at hi
    exact by_contra fun hne => hb ((mul_eq_left₀ hne).mp hi)

end SmoothFiniteFamily

end MetaplecticPoisson
