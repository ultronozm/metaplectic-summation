import MetaplecticSummation.AdelicAnnihilator
import Mathlib.Analysis.Normed.Field.Ultra

/-! Local constancy and nontriviality of the finite components of an adelic character. -/
noncomputable section
namespace MetaplecticPoisson
open Filter Set MeasureTheory Metric
open scoped Topology ENNReal
open Classical

/-- A continuous circle-valued additive character on an ultrametric field
has open kernel: every positive integral multiple stays in the same ball at zero. -/
theorem locallyConstant_addChar {K : Type*} [NormedField K] [IsUltrametricDist K]
    (χ : AddChar K Circle) (hc : Continuous χ) : IsLocallyConstant χ := by
  have h1 : (1 : Circle) ∈ Circle.centeredArc (Real.pi / 2) := by
    rw [Circle.mem_centeredArc (by linarith [Real.pi_pos])]
    simp [Real.pi_pos]
  have he : ∀ᶠ x in 𝓝 (0 : K), χ x ∈ Circle.centeredArc (Real.pi / 2) :=
    (hc.tendsto 0).eventually ((Circle.isOpen_centeredArc _).mem_nhds (by simpa using h1))
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp he
  have hk (x : K) (hx : ‖x‖ < r) : χ x = 1 := by
    apply Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two
    intro n _
    rw [← χ.map_nsmul_eq_pow]
    apply hball
    rw [mem_ball_zero_iff, nsmul_eq_mul, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one K n)).trans_lt hx
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  filter_upwards [Metric.ball_mem_nhds x hr] with y hy
  have h := χ.map_add_eq_mul (y-x) x
  simpa [hk _ (show ‖y-x‖ < r by simpa [mem_ball,dist_eq_norm] using hy)] using h

namespace Character
open NumberField IsDedekindDomain
variable {F : Type} [Field F] [NumberField F] (χ : Character F)

theorem locallyConstant_finiteValue (p : HeightOneSpectrum (𝓞 F)) :
    IsLocallyConstant (χ.localValue F (.inr p)) := by
  let v : Place F := .inr p
  let ψ : AddChar (p.adicCompletion F) Circle :=
    χ.toChar.compAddMonoidHom
      { toFun := singleAdele F v
        map_zero' := singleAdele_zero v
        map_add' := singleAdele_add v }
  exact (locallyConstant_addChar ψ (χ.continuous_toChar.comp (continuous_singleAdele v))).comp Subtype.val

theorem nontrivial_finiteValue (p : HeightOneSpectrum (𝓞 F)) :
    ∃ x, χ.localValue F (.inr p) x ≠ 1 := χ.nontrivial_localValue (.inr p)

end Character

end MetaplecticPoisson
