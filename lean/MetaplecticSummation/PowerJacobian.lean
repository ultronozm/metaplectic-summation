import MetaplecticSummation.PowerSubgroup
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Algebra.Ring.GeomSum

/-! The local Jacobian of the power map in the non-archimedean root-sum formula. -/

noncomputable section
namespace MetaplecticPoisson
open Filter Set Metric
open scoped Topology
open Classical
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-- At every noncritical point, the power map sends every sufficiently small
closed ball bijectively to the ball scaled by the norm of its derivative.
This includes residue characteristics dividing n. -/
theorem power_local_balls (n : ℕ) (hn : (n : K) ≠ 0) (a : K) (ha : a ≠ 0) :
    let J (x : K) := ‖(n : K)*x^(n-1)‖
    ∃ r > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ ≤ r →
      BijOn (fun x : K => x^n) (closedBall a δ) (closedBall (a^n) (J a * δ)) ∧
        ∀ x ∈ closedBall a δ, J x = J a := by
  let J (x : K) := ‖(n : K)*x^(n-1)‖
  let P (z : K × K) := ∑ i ∈ Finset.range n, z.1^i * z.2^(n-1-i)
  have hdiag (x : K) : P (x,x) = (n : K)*x^(n-1) := by
    unfold P
    calc
      _ = ∑ _i ∈ Finset.range n, x^(n-1) := Finset.sum_congr rfl (fun i hi => by
        rw [← pow_add,show i + (n-1-i) = n-1 by have := Finset.mem_range.mp hi; omega])
      _ = _ := by simp
  have hJ : 0 < J a := norm_pos_iff.mpr (mul_ne_zero hn (pow_ne_zero _ ha))
  have hcont : Continuous P := by unfold P; fun_prop
  have hev : ∀ᶠ z in 𝓝 (a,a), ‖P z‖ = J a := by
    filter_upwards [hcont.continuousAt.eventually (ball_mem_nhds (P (a,a)) hJ)] with z hz
    rw [dist_eq_norm,sub_eq_add_neg] at hz
    have h := IsUltrametricDist.norm_eq_of_add_norm_lt_max (x := P z) (y := -P (a,a))
      (hz.trans_le (by simp [J,hdiag]))
    simpa [J,hdiag] using h
  obtain ⟨r,hr,hu⟩ := Metric.mem_nhds_iff.mp hev
  have hnorm {x y : K} (hx : x ∈ ball a r) (hy : y ∈ ball a r) : ‖P (x,y)‖ = J a :=
    hu (show (x,y) ∈ ball (a,a) r by simpa [Metric.mem_ball,Prod.dist_eq] using And.intro hx hy)
  have hdist {x y : K} (hx : x ∈ ball a r) (hy : y ∈ ball a r) :
      dist (x^n) (y^n) = J a * dist x y := by
    rw [dist_eq_norm,dist_eq_norm,← (Commute.all x y).geom_sum₂_mul n,norm_mul]
    exact congrArg (· * ‖x-y‖) (hnorm hx hy)
  have hopen : (fun x : K => x^n) '' ball a r ∈ 𝓝 (a^n) := by
    rw [← (hasStrictDerivAt_pow n a).map_nhds_eq (mul_ne_zero hn (pow_ne_zero _ ha))]
    exact image_mem_map (ball_mem_nhds a hr)
  obtain ⟨R,hR,himage⟩ := Metric.mem_nhds_iff.mp hopen
  refine ⟨min (r/2) (R/2 / J a),lt_min (half_pos hr) (div_pos (half_pos hR) hJ),fun δ _ hδ => ?_⟩
  have hδr : δ < r := (hδ.trans (min_le_left _ _)).trans_lt (half_lt_self hr)
  have hδR : J a * δ < R := by
    have h := (le_div_iff₀ hJ).mp (hδ.trans (min_le_right _ _))
    rw [mul_comm] at h
    exact h.trans_lt (half_lt_self hR)
  have small := closedBall_subset_ball (x := a) hδr
  have center := mem_ball_self (x := a) hr
  constructor
  · refine ⟨?_,?_,?_⟩
    · intro x hx
      rw [mem_closedBall,hdist (small hx) center]
      exact mul_le_mul_of_nonneg_left hx hJ.le
    · intro x hx y hy he
      have h := hdist (small hx) (small hy)
      change x^n = y^n at he
      rw [he,dist_self] at h
      exact dist_eq_zero.mp ((mul_eq_zero.mp h.symm).resolve_left hJ.ne')
    · intro y hy
      obtain ⟨x,hx,rfl⟩ := himage (closedBall_subset_ball hδR hy)
      refine ⟨x,?_,rfl⟩
      change dist (x^n) (a^n) ≤ J a * δ at hy
      rw [hdist hx center] at hy
      exact (le_of_mul_le_mul_left hy hJ)
  · intro x hx
    simpa only [hdiag,J] using hnorm (small hx) (small hx)

end MetaplecticPoisson
