import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv

/-! Openness of the subgroup of n-th powers (§2(e)). -/

namespace MetaplecticPoisson
open Filter Set
open scoped Topology
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]

/-- The nonzero n-th powers form an open subset of the field, also in positive
characteristic whenever the characteristic does not divide n. -/
theorem isOpen_nonzero_powers (n : ℕ) (hn : (n : K) ≠ 0) :
    IsOpen (range fun u : Kˣ => u.val ^ n) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨u, rfl⟩
  have hd := hasStrictDerivAt_pow n u.val
  rw [← hd.map_nhds_eq (mul_ne_zero hn (pow_ne_zero _ u.ne_zero))]
  change ∀ᶠ x in 𝓝 u.val, x ^ n ∈ range (fun u : Kˣ => u.val ^ n)
  filter_upwards [eventually_ne_nhds u.ne_zero] with x hx
  exact ⟨Units.mk0 x hx, rfl⟩

theorem isOpen_unit_powers (n : ℕ) (hn : (n : K) ≠ 0) : IsOpen (range fun u : Kˣ => u ^ n) := by
  have h : range (fun u : Kˣ => u ^ n) = Units.val ⁻¹' range (fun u : Kˣ => u.val ^ n) := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨u, rfl⟩
    · rintro ⟨u, hu⟩
      exact ⟨u, Units.ext hu⟩
  rw [h]
  exact (isOpen_nonzero_powers n hn).preimage Units.continuous_val

open Metric
open Classical

omit [CompleteSpace K] in
/-- A compact subset of the dominant-coordinate chart meets every power ray
in that cone. The normalized dominant coordinate has norm between 1 and B. -/
theorem compact_ray_shell {n : ℕ} [ProperSpace K] (hn : n ≠ 0) :
    ∃ (T : Set (Kˣ × K)) (B : ℝ), IsCompact T ∧ 0 < B ∧
    ∀ (a : Kˣ) (b : K), ‖b‖ ≤ ‖a.val‖ → ∃ (q : Kˣ × K) (u : Kˣ), q ∈ T ∧
      (u^n*q.1,u.val^n*q.2) = (a,b) ∧ ‖u.val‖^n ≤ ‖a.val‖ ∧ ‖a.val‖ ≤ B * ‖u.val‖^n := by
  obtain ⟨c,hc⟩ := NormedField.exists_one_lt_norm K
  let B := ‖c‖^n
  have hB : 1 < B := one_lt_pow₀ hc hn
  let A := closedBall (0:K) B ∩ {x : K | 1 ≤ ‖x‖}
  have hA : IsCompact A := (isCompact_closedBall _ _).inter_right (isClosed_le continuous_const continuous_norm)
  have hA' := Units.isEmbedding_val₀.isInducing.isCompact_preimage' hA (by
    intro x hx
    have hnz : x ≠ 0 := by
      rintro rfl
      exact (not_le_of_gt zero_lt_one) (by simpa using hx.2)
    exact ⟨Units.mk0 x hnz,rfl⟩)
  refine ⟨_ ×ˢ closedBall 0 B,B,hA'.prod (isCompact_closedBall _ _),zero_lt_one.trans hB,?_⟩
  intro a b hab
  obtain ⟨j,hj₁,hj₂⟩ := exists_mem_Ico_zpow (norm_pos_iff.mpr a.ne_zero) hB
  let u := (Units.mk0 c (norm_pos_iff.mp (zero_lt_one.trans hc))) ^ j
  have hu : ‖u.val‖^n = B^j := by
    simp only [u,Units.val_zpow_eq_zpow_val,Units.val_mk0,norm_zpow,B]
    rw [← zpow_natCast, ← zpow_natCast (‖c‖), ← zpow_mul, ← zpow_mul, mul_comm]
  have hval : ‖a.val‖ ≤ B * ‖u.val‖^n := by
    rw [hu,mul_comm,← zpow_add_one₀ (ne_of_gt (zero_lt_one.trans hB))]
    exact hj₂.le
  have hpos : 0 < ‖u.val‖^n := pow_pos (norm_pos_iff.mpr u.ne_zero) _
  let q : Kˣ × K := (a/u^n,b/u.val^n)
  have hq : ‖q.1.val‖ = ‖a.val‖ / ‖u.val‖^n := by simp [q,norm_div,norm_pow]
  refine ⟨q,u,⟨⟨?_,?_⟩,?_⟩,?_,hu ▸ hj₁,hval⟩
  · change q.1.val ∈ closedBall 0 B
    simpa [mem_closedBall,dist_zero_right,hq] using (div_le_iff₀ hpos).mpr hval
  · change 1 ≤ ‖q.1.val‖
    rw [hq,one_le_div hpos,hu]
    exact hj₁
  · simpa [q,mem_closedBall,dist_zero_right,norm_div,norm_pow] using (div_le_iff₀ hpos).mpr (hab.trans hval)
  · dsimp [q]
    ext <;> simp [field]

/-- The quotient by n-th powers is finite over a proper complete normed
field when the exponent is nonzero in the field. -/
theorem finite_unit_power_quotient [ProperSpace K] (n : ℕ) (hn : (n : K) ≠ 0) :
    Finite (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) := by
  let H := (powMonoidHom n : Kˣ →* Kˣ).range
  let π := QuotientGroup.mk' H
  letI : DiscreteTopology (Kˣ ⧸ H) := QuotientGroup.discreteTopology (isOpen_unit_powers n hn)
  obtain ⟨T, B, hT, _, h⟩ := compact_ray_shell (K := K) (n := n) (by rintro rfl; simp at hn)
  have him : (fun q : Kˣ × K => π q.1) '' T = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective H y
    obtain ⟨q, u, hq, he, _, _⟩ := h a 0 (by simp)
    refine ⟨q,hq,?_⟩
    have hh : π (u^n) = 1 := (QuotientGroup.eq_one_iff _).mpr ⟨u,rfl⟩
    change π q.1 = π a
    calc
      π q.1 = π (u^n) * π q.1 := by rw [hh]; exact (one_mul (π q.1)).symm
      _ = π a := (π.map_mul _ _).symm.trans (congrArg π (congrArg Prod.fst he))
  have hc := hT.image ((QuotientGroup.continuous_mk (N := H)).comp continuous_fst)
  letI : CompactSpace (Kˣ ⧸ H) := ⟨him ▸ hc⟩
  exact finite_of_compact_of_discrete

end MetaplecticPoisson
