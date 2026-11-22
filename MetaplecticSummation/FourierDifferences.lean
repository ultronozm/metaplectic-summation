import MetaplecticSummation.CharacterNontrivial
import MetaplecticSummation.FiniteLeading
import Mathlib.Algebra.Group.ForwardDiff

/-! Fourier decay from integral bounds for forward differences of the Radon
slices. Translation works with the actual local additive character. -/
noncomputable section
namespace MetaplecticPoisson
open Metric
open scoped ContDiff
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem smooth_fwdDiff {f : E → ℂ} (hf : ContDiff ℝ ∞ f) (h : E) (j : ℕ) :
    ContDiff ℝ ∞ ((fwdDiff h)^[j] f) := by
  induction j with
  | zero => exact hf
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact (ih.comp (contDiff_id.add contDiff_const)).sub ih

/-- Repeated application of the mean value inequality bounds a forward
difference by the derivative of matching order on a ball about the base point. -/
theorem norm_fwdDiff_iter_le {f : E → ℂ} (hf : ContDiff ℝ ∞ f) (h z : E) (j : ℕ) {M : ℝ}
    (hM : ∀ y ∈ closedBall z (j*‖h‖), ‖iteratedFDeriv ℝ j f y‖ ≤ M) :
    ‖(fwdDiff h)^[j] f z‖ ≤ M*‖h‖^j := by
  have H (i : ℕ) : ∀ k x, (∀ y ∈ closedBall x (i*‖h‖), ‖iteratedFDeriv ℝ (k+i) f y‖ ≤ M) →
      ‖iteratedFDeriv ℝ k ((fwdDiff h)^[i] f) x‖ ≤ M*‖h‖^i := by
    induction i with
    | zero =>
      intro k x hs
      simpa using hs x (by simp)
    | succ i ih =>
      intro k x hs
      let G := (fwdDiff h)^[i] f
      have hG : ContDiff ℝ ∞ G := smooth_fwdDiff hf h i
      have hk : (k : WithTop ℕ∞) < ∞ := by exact_mod_cast ENat.coe_lt_top k
      have hd : Differentiable ℝ (iteratedFDeriv ℝ k G) := hG.differentiable_iteratedFDeriv hk
      have hb (a : E) (ha : a ∈ closedBall x ‖h‖) : ‖fderiv ℝ (iteratedFDeriv ℝ k G) a‖ ≤ M*‖h‖^i := by
        rw [norm_fderiv_iteratedFDeriv]
        apply ih (k+1) a
        intro y hy
        have hy' : y ∈ closedBall x ((i+1 : ℕ)*‖h‖) := by
          rw [mem_closedBall] at hy ha ⊢
          exact (dist_triangle y a x).trans ((add_le_add hy ha).trans_eq (by push_cast; ring))
        rw [show k+1+i = k+(i+1) by omega]
        exact hs y hy'
      have he := (convex_closedBall x ‖h‖).norm_image_sub_le_of_norm_fderiv_le (fun a _ => hd a) hb
        (mem_closedBall_self (norm_nonneg _)) (show x+h ∈ closedBall x ‖h‖ by simp [mem_closedBall,dist_eq_norm])
      rw [Function.iterate_succ_apply']
      change ‖iteratedFDeriv ℝ k ((fun t => G (t+h)) - G) x‖ ≤ _
      have hh : ContDiff ℝ k (fun t => G (t+h)) := (hG.comp (contDiff_id.add contDiff_const)).of_le hk.le
      rw [iteratedFDeriv_sub_apply hh.contDiffAt (hG.of_le hk.le).contDiffAt,iteratedFDeriv_comp_add_right]
      simpa only [add_sub_cancel_left,pow_succ,mul_assoc] using he
  have hbound := H j 0 z
  have atOrder (k : ℕ) (e : k = j) : ∀ y ∈ closedBall z (j*‖h‖), ‖iteratedFDeriv ℝ k f y‖ ≤ M := e ▸ hM
  simpa only [norm_iteratedFDeriv_zero] using hbound (atOrder (0+j) (Nat.zero_add j))

/-- The weight in an integrable order-three majorant survives bounded
translations of the variable in an iterated difference. -/
theorem fwdDiff_decay {f : E → ℂ} (hf : ContDiff ℝ ∞ f) {j : ℕ} {C A : ℝ}
    (H : ∀ y, ‖iteratedFDeriv ℝ j f y‖*(1+‖y‖)^3 ≤ C)
    (z h : E) (ha : ‖h‖ ≤ A) :
    ‖(fwdDiff h)^[j] f z‖ ≤ C*(1+j*A)^3*‖h‖^j*((1+‖z‖)^3)⁻¹ := by
  let M := C*(1+j*A)^3/((1+‖z‖)^3)
  have bound (y : E) (hy : y ∈ closedBall z (j*‖h‖)) : ‖iteratedFDeriv ℝ j f y‖ ≤ M := by
    have hD : 0 ≤ (j:ℝ)*A := mul_nonneg (Nat.cast_nonneg _) ((norm_nonneg _).trans ha)
    have hdist := (mem_closedBall.mp hy).trans (mul_le_mul_of_nonneg_left ha (Nat.cast_nonneg _))
    have ht := norm_sub_norm_le z y
    rw [← dist_eq_norm,dist_comm z y] at ht
    have hz : 1+‖z‖ ≤ (1+‖y‖)*(1+j*A) := by nlinarith [mul_nonneg (norm_nonneg y) hD]
    apply (le_div_iff₀ (by positivity : 0 < (1+‖z‖)^3)).mpr
    calc
      _ ≤ ‖iteratedFDeriv ℝ j f y‖*((1+‖y‖)*(1+j*A))^3 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hz _) (norm_nonneg _)
      _ ≤ _ := by rw [mul_pow,← mul_assoc]; exact mul_le_mul_of_nonneg_right (H y) (by positivity)
  exact (norm_fwdDiff_iter_le hf h z j bound).trans_eq (by dsimp [M]; ring)

end
end MetaplecticPoisson

namespace MetaplecticPoisson.Datum
open MeasureTheory
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)
variable (v : Place F)
local notation "K" => LocalField F v
local notation "dxᵥ" => selfDual F d.character v

omit [NeZero n] in
theorem integrable_phase {g : K → ℂ} (hg : Integrable g dxᵥ) (u : K) :
    Integrable (fun t => g t * d.character.localValue F v (u*t)) dxᵥ := by
  apply hg.norm.mono' (hg.aestronglyMeasurable.mul (((d.character.continuous_localValue v).comp
    (continuous_const.mul continuous_id)).aestronglyMeasurable))
  exact .of_forall fun t => by simp

omit [NeZero n] in
private theorem integrable_translate {g : K → ℂ} (hg : Integrable g dxᵥ) (h : K) :
    Integrable (fun t => g (t+h)) dxᵥ := by
  letI : (dxᵥ).IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  exact (measurePreserving_add_right dxᵥ h).integrable_comp_of_integrable hg

omit [NeZero n] in
/-- Translation of the slice multiplies the Fourier integral by the inverse phase. -/
theorem hat_translate (g : K → ℂ) (h u : K) :
    d.hat v (fun t => g (t+h)) u = d.character.localValue F v (-(u*h)) * d.hat v g u := by
  letI : (dxᵥ).IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  let ψ := d.character.localValue F v
  have H := integral_add_right_eq_self (μ := dxᵥ) (fun t : K => g t * ψ (u*(t-h))) h
  simp only [add_sub_cancel_right] at H
  change (∫ t, g (t+h)*ψ (u*t) ∂dxᵥ) = ψ (-(u*h)) * ∫ t, g t*ψ (u*t) ∂dxᵥ
  rw [H,← integral_const_mul]
  apply integral_congr_ae
  exact .of_forall fun t => by
    change g t * d.character.localValue F v (u*(t-h)) = d.character.localValue F v (-(u*h)) * (g t * d.character.localValue F v (u*t))
    rw [mul_sub,sub_eq_add_neg,d.character.localValue_add]
    ring

omit [NeZero n] in
theorem hat_iterated_fwdDiff {g : K → ℂ} (hg : Integrable g dxᵥ) (h u : K) (j : ℕ) :
    Integrable ((fwdDiff h)^[j] g) dxᵥ ∧ d.hat v ((fwdDiff h)^[j] g) u =
      (d.character.localValue F v (-(u*h))-1)^j * d.hat v g u := by
  induction j with
  | zero => exact ⟨hg,by simp⟩
  | succ j ih =>
    let G := (fwdDiff h)^[j] g
    have H := d.integrable_translate v ih.1 h
    rw [Function.iterate_succ_apply']
    refine ⟨H.sub ih.1,?_⟩
    have e : d.hat v (fwdDiff h G) u = d.hat v (fun t => G (t+h)) u - d.hat v G u := by
      simp only [hat,fwdDiff,sub_mul]
      exact integral_sub (d.integrable_phase v H u) (d.integrable_phase v ih.1 u)
    change d.hat v (fwdDiff h G) u = _
    rw [e,d.hat_translate,show d.hat v G u = _ from ih.2,pow_succ]
    ring

omit [NeZero n] in
/-- A uniform L¹ bound of order j for forward differences gives the
high-frequency bound of the same order for the family of Fourier integrals.
The step a/u keeps the character multiplier independent of u. -/
theorem hat_decay_of_fwdDiff {P : Type*} (g : P → K → ℂ) (T : Set P)
    (hi : ∀ q ∈ T, Integrable (g q) dxᵥ) (j : ℕ)
    (hD : ∀ a : K, ∃ B : ℝ, 0 ≤ B ∧ ∀ q ∈ T, ∀ u : K, 1 ≤ ‖u‖ →
      (∫ t, ‖(fwdDiff (a/u))^[j] (g q) t‖ ∂dxᵥ) ≤ B*‖a/u‖^j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ T, ∀ u : K, 1 ≤ ‖u‖ → ‖d.hat v (g q) u‖*(1+‖u‖)^j ≤ C := by
  obtain ⟨b,hb⟩ := d.character.nontrivial_localValue v
  let a := -b
  let k := d.character.localValue F v b - 1
  have hk : 0 < ‖k‖^j := pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hb)) _
  obtain ⟨B,hB,H⟩ := hD a
  refine ⟨B*(‖a‖*2)^j/‖k‖^j,by positivity,?_⟩
  intro q hq u hu
  have hpos := zero_lt_one.trans_le hu
  have hstep : -(u*(a/u)) = b := by dsimp [a]; field_simp [norm_pos_iff.mp hpos]
  let G := (fwdDiff (a/u))^[j] (g q)
  have h := (d.hat_iterated_fwdDiff v (hi q hq) (a/u) u j).2
  rw [hstep] at h
  have hnorm : ‖k‖^j*‖d.hat v (g q) u‖ ≤ B*‖a/u‖^j := by
    rw [← norm_pow,← norm_mul,← h]
    apply (norm_integral_le_integral_norm _).trans
    simpa only [norm_mul,d.character.norm_localValue,mul_one] using H q hq u hu
  rw [le_div_iff₀ hk]
  have hd := mul_le_mul_of_nonneg_right hnorm (pow_nonneg (show 0 ≤ 2*‖u‖ by positivity) j)
  calc
    _ ≤ (‖k‖^j*‖d.hat v (g q) u‖)*(2*‖u‖)^j := by
      rw [mul_right_comm,mul_comm ‖d.hat v (g q) u‖]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) _) (by positivity)
    _ ≤ _ := hd.trans_eq (by rw [mul_assoc,← mul_pow,norm_div]; congr 2; field_simp [hpos.ne'])
end MetaplecticPoisson.Datum
