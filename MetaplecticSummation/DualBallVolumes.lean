import MetaplecticSummation.FourierOrthogonality
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.Analysis.Normed.Field.Ultra
import Mathlib.Topology.LocallyConstant.Basic

/-! Haar normalization by the volumes of a ball and its character annihilator. -/
noncomputable section
namespace MetaplecticPoisson
open MeasureTheory MeasureTheory.Measure Metric Set Filter
open scoped Topology Pointwise NNReal ENNReal
open Classical
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K]
    [MeasurableSpace K] [BorelSpace K]

/-- Reciprocal volumes of principal fractional ideals and their annihilators. -/
def DualBallVolumes (ψ : K → ℂ) (μ : Measure K) : Prop :=
  ∀ a : Kˣ, let B := closedBall (0:K) ‖a.val‖
    μ.real B * μ.real {x : K | ∀ y ∈ B, ψ (x*y) = 1} = 1

def closedBallSubgroup (R : ℝ) (hR : 0 ≤ R) : AddSubgroup K where
  carrier := closedBall 0 R
  zero_mem' := by simp [hR]
  add_mem' := by
    intro a b ha hb
    rw [mem_closedBall,dist_zero_right] at ha hb ⊢
    exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  neg_mem' := by intro a ha; simpa only [mem_closedBall,dist_zero_right,norm_neg] using ha

theorem dualBallVolumes_of_plancherel (μ : Measure K) [μ.IsAddHaarMeasure] {ψ : K → ℂ}
    (hc : Continuous ψ) (ha : ∀ x y, ψ (x+y) = ψ x * ψ y)
    (hP : KernelPlancherel (fun x y => ψ (x*y)) μ) : DualBallVolumes ψ μ := by
  intro a
  let O := closedBallSubgroup (K := K) ‖a.val‖ (norm_nonneg _)
  let D := {x : K | ∀ y ∈ O, ψ (x*y) = 1}
  have hd : IsClosed D := by
    dsimp only [D]
    simp only [setOf_forall]
    exact isClosed_iInter (fun y => isClosed_iInter (fun _ =>
      isClosed_eq (hc.comp (continuous_id.mul_const y)) continuous_const))
  exact Datum.volume_mul_annihilator O D hd.measurableSet
    (IsUltrametricDist.isClopen_closedBall _ (norm_ne_zero_iff.mpr a.ne_zero)) (isCompact_closedBall _ _)
    μ ψ ha (fun _ => Iff.rfl) hP

/-- A Haar measure normalizing the volumes of every principal fractional
ideal and its annihilator. -/
theorem exists_haar_dual_ball_volumes (ψ : AddChar K ℂ) (hc : IsLocallyConstant ψ)
    (hn : ∃ z, ψ z ≠ 1) :
    ∃ μ : Measure K, μ.IsAddHaarMeasure ∧ DualBallVolumes ψ μ := by
  let O := closedBall (0:K) 1
  let D := {x : K | ∀ y ∈ O, ψ (x*y) = 1}
  have hd : IsClosed D := by
    dsimp only [D]
    simp only [setOf_forall]
    exact isClosed_iInter (fun y => isClosed_iInter (fun _ => isClosed_eq
      (hc.continuous.comp (continuous_id.mul_const y)) continuous_const))
  obtain ⟨z,hz⟩ := hn
  have compactD : IsCompact D := (isCompact_closedBall 0 ‖z‖).of_isClosed_subset hd (by
    intro x hx
    rw [mem_closedBall_zero_iff]
    by_contra! h
    have h₀ := norm_pos_iff.mp ((norm_nonneg _).trans_lt h)
    have hdiv : z/x ∈ O := mem_closedBall_zero_iff.mpr (by rw [norm_div,div_le_one (norm_pos_iff.mpr h₀)]; exact h.le)
    exact hz (by simpa only [mul_div_cancel₀ _ h₀] using hx _ hdiv))
  have near : D ∈ 𝓝 0 := by
    obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hc.eventually_eq 0)
    apply mem_of_superset (ball_mem_nhds (0:K) hr)
    intro x hx y hy
    exact (hball (mem_ball_zero_iff.mpr ((norm_mul x y).le.trans_lt
      ((mul_le_of_le_one_right (norm_nonneg _) (mem_closedBall_zero_iff.mp hy)).trans_lt
        (mem_ball_zero_iff.mp hx))))).trans ψ.map_zero_eq_one
  let ν := (addHaar : Measure K)
  have ho : 0 < ν.real O := ENNReal.toReal_pos
    (measure_pos_of_mem_nhds ν (closedBall_mem_nhds (0:K) zero_lt_one)).ne' (isCompact_closedBall _ _).measure_ne_top
  have hp : 0 < ν.real D := ENNReal.toReal_pos (measure_pos_of_mem_nhds ν near).ne' compactD.measure_ne_top
  let r : ℝ≥0 := ⟨(Real.sqrt (ν.real O*ν.real D))⁻¹,(inv_pos.mpr (Real.sqrt_pos.mpr (mul_pos ho hp))).le⟩
  have hr : r ≠ 0 := (show 0 < r from inv_pos.mpr (Real.sqrt_pos.mpr (mul_pos ho hp))).ne'
  let μ := r • ν
  letI : μ.IsAddHaarMeasure := Measure.IsAddHaarMeasure.nnreal_smul ν hr
  have normalized : μ.real O * μ.real D = 1 := by
    simp only [μ,measureReal_nnreal_smul_apply]
    change (Real.sqrt (ν.real O*ν.real D))⁻¹ * ν.real O *
      ((Real.sqrt (ν.real O*ν.real D))⁻¹ * ν.real D) = 1
    rw [show (Real.sqrt (ν.real O*ν.real D))⁻¹ * ν.real O *
      ((Real.sqrt (ν.real O*ν.real D))⁻¹ * ν.real D) =
      ((Real.sqrt (ν.real O*ν.real D))^2)⁻¹*(ν.real O*ν.real D) by ring]
    rw [Real.sq_sqrt (mul_pos ho hp).le,inv_mul_cancel₀ (mul_pos ho hp).ne']
  have scale (t : Kˣ) (S : Set K) : μ.real (t • S) = (distribHaarChar K t : ℝ)*μ.real S := by
    rw [measureReal_def,← distribHaarChar_mul,ENNReal.toReal_mul]
    rfl
  refine ⟨μ,inferInstance,fun a => ?_⟩
  have ball : closedBall (0:K) ‖a.val‖ = a • O := by
    ext y
    rw [mem_smul_set_iff_inv_smul_mem]
    simp only [O,mem_closedBall_zero_iff,Units.smul_def,smul_eq_mul,Units.val_inv_eq_inv_val,
      ← div_eq_inv_mul,norm_div,div_le_one (norm_pos_iff.mpr a.ne_zero)]
  have dual : {x : K | ∀ y ∈ a • O, ψ (x*y) = 1} = a⁻¹ • D := by
    ext x
    rw [mem_smul_set_iff_inv_smul_mem,inv_inv]
    change (∀ y ∈ a • O, ψ (x*y) = 1) ↔ ∀ y ∈ O, ψ ((a.val*x)*y) = 1
    constructor
    · intro h y hy
      exact (by simpa only [Units.smul_def,smul_eq_mul,mul_left_comm,mul_assoc] using h _ (smul_mem_smul_set (a := a) hy))
    · rintro h _ ⟨y,hy,rfl⟩
      simpa only [Units.smul_def,smul_eq_mul,mul_left_comm,mul_assoc] using h y hy
  dsimp only
  rw [ball,dual,scale,scale,map_inv,NNReal.coe_inv]
  have hp₀ : (distribHaarChar K a : ℝ) ≠ 0 := (show 0 < (distribHaarChar K a : ℝ) from distribHaarChar_pos).ne'
  field_simp [hp₀]
  exact normalized

end MetaplecticPoisson
