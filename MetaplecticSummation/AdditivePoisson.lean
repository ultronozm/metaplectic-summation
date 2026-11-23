import GroundTheory.GlobalFields.TateThesis.AdelePoisson
import MetaplecticSummation.Places

/-! The additive adelic Poisson theorem used twice in Proposition B.4. -/
noncomputable section
namespace MetaplecticPoisson.Character
variable {F : Type} [Field F] [NumberField F]

/-- A nontrivial continuous additive character trivial on the number field
has a unique nonzero rational trace parameter. -/
theorem existsUnique_trace_parameter (ψ : Character F) :
    ∃! b : Fˣ, ∀ x : Adeles F, ψ.toChar x =
      GroundTheory.Global.adelicChar F (algebraMap F (Adeles F) b.val * x) := by
  obtain ⟨b,hb,hu⟩ := GroundTheory.Global.existsUnique_eq_adelicChar_mul ψ.toChar
    ψ.continuous_toChar ψ.trivial_diagonal
  have hne : b ≠ 0 := by
    rintro rfl
    obtain ⟨x,hx⟩ := ψ.nontrivial
    exact hx (by simpa using hb x)
  exact ⟨Units.mk0 b hne,hb,fun a ha => Units.ext (hu a.val ha)⟩

open MeasureTheory GroundTheory.Global
/-- Adelic Poisson for any nontrivial continuous additive character trivial on
the number field. Both diagonal sums converge absolutely. -/
theorem adelic_poisson (ψ : Character F) {f : Adeles F → ℂ} (hf : f ∈ schwartzBruhat F) :
    let dual := fun y : F => ∫ x, f x * (ψ.toChar (x * algebraMap F (Adeles F) y) : ℂ) ∂adeleMeasure F
    Summable (fun y : F => ‖f (algebraMap F (Adeles F) y)‖) ∧
      Summable (fun y => ‖dual y‖) ∧
      (∑' y : F, f (algebraMap F (Adeles F) y)) = ∑' y, dual y := by
  obtain ⟨b,hb,_⟩ := ψ.existsUnique_trace_parameter
  let e := Equiv.mulLeft₀ b.val b.ne_zero
  let g (t : F) := adelicFourier F f (algebraMap F (Adeles F) t)
  have he (y : F) : (∫ x, f x * (ψ.toChar (x * algebraMap F (Adeles F) y) : ℂ) ∂adeleMeasure F) = g (e y) := by
    change _ = ∫ x, f x * (adelicChar F (x * algebraMap F (Adeles F) (b.val*y)) : ℂ) ∂adeleMeasure F
    apply integral_congr_ae
    filter_upwards with x
    rw [hb,(algebraMap F (Adeles F)).map_mul,mul_left_comm (algebraMap F (Adeles F) b.val) x]
  dsimp only
  simp_rw [he]
  refine ⟨summable_norm_algebraMap_of_mem_schwartzBruhat hf,?_,?_⟩
  · exact (summable_norm_algebraMap_of_mem_schwartzBruhat (adelicFourier_mem_schwartzBruhat hf)).comp_injective e.injective
  · exact (tsum_algebraMap_eq_tsum_adelicFourier hf).trans (e.tsum_eq g).symm

end MetaplecticPoisson.Character
