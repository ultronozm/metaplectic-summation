import MetaplecticSummation.Cusp.ThetaGrowth
import MetaplecticSummation.TranslatedConstantTerm

/-! Decay of the theta difference from uniform off-axis decay and vanishing of its mean. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField Filter MeasureTheory Set
open scoped Matrix MatrixGroups
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

theorem upperLift_projects (u : Adeles F) : d.LiftsAdelicMatrix (adelicUpper F u) (d.upperLift u) := by
  intro v
  apply Subtype.ext
  rw [show (d.coverProjection v (d.upperLift u v)).val = _ from
    (d.kubota_projection v).choose_spec.2.2.1 _ _ (d.upperLift_isUpper u v)]
  change _ = (adelicUpper F u).val.map (componentHom v)
  rw [show (adelicUpper F u).val = _ from upperTransvection_matrix u]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [show component u v = componentHom v u from rfl]

private def axisSum (Φ : ∀ v, d.schwartz v) : ℂ :=
  ∑' p : RationalPoint F, if p.val.1 = 0 then d.translatedValue Φ 0 p else 0

private theorem norm_sub_axisSum (Φ : ∀ v, d.schwartz v) (hf : ∀ᶠ v in cofinite, Φ v = d.basic v) (s : Adeles F) :
    ‖d.quotientIntegrand Φ 0 (QuotientAddGroup.mk s) - d.axisSum Φ‖ ≤
      ∑' p : RationalPoint F, if p.val.1 = 0 then 0 else ‖d.translatedValue Φ s p‖ := by
  let f := d.translatedValue Φ s
  let T : Set (RationalPoint F) := {p | p.val.1 = 0}
  have hf' : Summable f := (d.summable_translatedValue Φ hf s).of_norm
  have he : d.axisSum Φ = ∑' p, T.indicator f p := by
    apply tsum_congr
    intro p
    by_cases hx : p.val.1 = 0 <;> simp [T,f,Set.indicator,translatedValue,hx]
  rw [d.quotientIntegrand_mk,he]
  simp only [map_zero,zero_mul,neg_zero,AddChar.map_zero_eq_one,Circle.coe_one,mul_one]
  change ‖(∑' p, f p) - _‖ ≤ _
  rw [← hf'.tsum_sub (hf'.indicator T)]
  refine (norm_tsum_le_tsum_norm (hf'.sub (hf'.indicator T)).norm).trans_eq ?_
  apply tsum_congr
  intro p
  by_cases hx : p.val.1 = 0 <;> simp [T,f,Set.indicator,hx]

private theorem centered_bound {X : Type} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
    {H : X → ℂ} (hi : Integrable H μ) (hz : ∫ x, H x ∂μ = 0)
    (J : ℂ) (C : ℝ) (hb : ∀ x, ‖H x-J‖ ≤ C) (x : X) : ‖H x‖ ≤ 2*C := by
  have hJ := norm_integral_le_of_norm_le_const (μ := μ) (.of_forall hb)
  rw [integral_sub hi (integrable_const J),hz,integral_const] at hJ
  simp at hJ
  calc
    ‖H x‖ = ‖(H x-J)+J‖ := by rw [sub_add_cancel]
    _ ≤ ‖H x-J‖+‖J‖ := norm_add_le ..
    _ ≤ 2*C := by linarith [hb x]

local instance : MeasurableSpace (AdeleQuotient F) := borel _
local instance : BorelSpace (AdeleQuotient F) := ⟨rfl⟩

/-- Lemma B.9 for any restricted lift of a cusp representative. -/
theorem cusp_thetaDifference_decay (Φ : ∀ v, d.schwartz v) (hf : ∀ᶠ v in cofinite, Φ v = d.basic v)
    (v₁ v₂ : Place F) (h₁ : d.leading v₁ (Φ v₁) = 0) (h₂ : d.leading v₂ (d.fourier v₂ (Φ v₂)) = 0)
    (w : Prime F) (K : Set (AdelicSL F)) (hK : IsCompact K) (R : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (u : Adeles F) (k : ℕ), ∀ ω ∈ K, ∀ g : ∀ v, d.cover v, ∀ hg : d.IsRestrictedCover g,
      d.LiftsAdelicMatrix (adelicUpper F u * ideleDiagonal F (cuspIdele F w)^k * ω) g →
      ‖d.thetaDifference (d.coverAction g hg (d.pure Φ hf))‖ ≤ M*(w.asIdeal.absNorm : ℝ)^(-R*k) := by
  let N := ⌈R⌉₊
  let Ψ := fun v => d.fourier v (Φ v)
  have hΨ : ∀ᶠ v in cofinite, Ψ v = d.basic v := (hf.and d.eventually_fourier_basic).mono fun _ h => h.1 ▸ h.2
  obtain ⟨A,hA,bA⟩ := d.cusp_offAxis_decay Φ hf w K hK N
  obtain ⟨B,hB,bB⟩ := d.cusp_offAxis_decay Ψ hΨ w K hK N
  refine ⟨2*(A+B),by positivity,fun u k ω hω g hg hm => ?_⟩
  let q : ℝ := w.asIdeal.absNorm
  let g₀ := fun v => (d.upperLift u v)⁻¹ * g v
  have hg₀ : d.IsRestrictedCover g₀ := ((d.upperLift_restricted u).and hg).mono fun p h =>
    (d.integralCover p).mul_mem ((d.integralCover p).inv_mem h.1) h.2
  let gs := fun s v => d.upperLift s v * g₀ v
  have hgs (s) : d.IsRestrictedCover (gs s) := ((d.upperLift_restricted s).and hg₀).mono fun p h =>
    (d.integralCover p).mul_mem h.1 h.2
  have ms (s) : d.LiftsAdelicMatrix (adelicUpper F s * ideleDiagonal F (cuspIdele F w)^k * ω) (gs s) := by
    intro v
    dsimp only [gs,g₀]
    rw [map_mul,map_mul,map_inv,d.upperLift_projects u v,d.upperLift_projects s v,hm v]
    simp only [map_mul,mul_assoc,inv_mul_cancel_left]
  let trans := fun (f : ∀ v, d.schwartz v) v => (g₀ v).val (f v)
  have basic (f) (h : ∀ᶠ v in cofinite, f v = d.basic v) : ∀ᶠ v in cofinite, trans f v = d.basic v :=
    (h.and (d.restrictedCover_fixes_basic hg₀)).mono fun _ e => e.1 ▸ e.2
  have value (f) (h : ∀ᶠ v in cofinite, f v = d.basic v) (s p) : d.translatedValue (trans f) s p =
      d.evaluation (d.coverAction (gs s) (hgs s) (d.pure f h)) p := by
    rw [d.coverAction_pure]
    exact d.translatedValue_eq_upper s _ (d.upperLift_isUpper s) (trans f) _ p
  let H := fun x => d.quotientIntegrand (trans Φ) 0 x - d.quotientIntegrand (trans Ψ) 0 x
  let J := d.axisSum (trans Φ) - d.axisSum (trans Ψ)
  let μ := (exists_quotient_measure (F := F)).exists.choose
  let : IsProbabilityMeasure μ := (exists_quotient_measure (F := F)).exists.choose_spec.2
  have hi : Integrable H μ := (d.coefficient_eq_slope_integrals _ (basic Φ hf) 0).1.sub
    (d.coefficient_eq_slope_integrals _ (basic Ψ hΨ) 0).1
  have hz : ∫ x, H x ∂μ = 0 := d.translated_constantTerm_difference Φ g₀ (basic Φ hf) v₁ v₂ h₁ h₂
  have bound (x) : ‖H x - J‖ ≤ (A+B)*(q^(N*k))⁻¹ := by
    induction x using QuotientAddGroup.induction_on with
    | _ s =>
      have single (f) (h : ∀ᶠ v in cofinite, f v = d.basic v) :=
        d.norm_sub_axisSum (trans f) (basic f h) s
      have eA := single Φ hf
      have eB := single Ψ hΨ
      simp only [value Φ hf] at eA
      simp only [value Ψ hΨ] at eB
      dsimp only [H,J]
      rw [sub_sub_sub_comm,add_mul]
      exact (norm_sub_le ..).trans (add_le_add (eA.trans (bA s k ω hω _ (hgs s) (ms s)))
        (eB.trans (bB s k ω hω _ (hgs s) (ms s))))
  have hu := centered_bound hi hz J _ bound (QuotientAddGroup.mk u)
  have e : H (QuotientAddGroup.mk u) = d.thetaDifference (d.coverAction g hg (d.pure Φ hf)) := by
    have dual : trans Ψ = fun v => d.fourier v (trans Φ v) := funext fun v => (d.fourier_equivariant v _ _).symm
    dsimp only [H]
    rw [dual,d.quotient_thetaDifference_mk _ (basic Φ hf),d.coverAction_pure,d.coverAction_pure]
    apply congrArg d.thetaDifference
    congr 1
    funext v
    change ((d.upperLift u v * ((d.upperLift u v)⁻¹ * g v)).val (Φ v)) = _
    rw [mul_inv_cancel_left]
  rw [e,← mul_assoc] at hu
  refine hu.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  have hq : 1 ≤ q := by dsimp [q]; exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm w).le
  rw [← Real.rpow_natCast,← Real.rpow_neg (zero_le_one.trans hq)]
  apply Real.rpow_le_rpow_of_exponent_le hq
  push_cast
  nlinarith [Nat.le_ceil R, Nat.cast_nonneg (α := ℝ) k]

end MetaplecticPoisson.Datum
