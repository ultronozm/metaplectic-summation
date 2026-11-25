import MetaplecticSummation.PowerJacobian
import MetaplecticSummation.RayFourier
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-! Integration over the fibers of the power map on a finite completion. -/

noncomputable section
namespace MetaplecticPoisson
open Set Metric MeasureTheory Filter NumberField IsDedekindDomain Polynomial
open scoped Topology
open Classical

/-- A compact set covered by prescribed ultrametric balls is covered by
finitely many pairwise disjoint balls from the same family. -/
private theorem disjoint_closedBall_cover {K : Type*} [MetricSpace K] [IsUltrametricDist K]
    {s : Set K} (hs : IsCompact s) (radius : s → ℝ) (hr : ∀ x, 0 < radius x) :
    ∃ T : Finset (Set K), (∀ B ∈ T, ∃ x : s, B = closedBall x.val (radius x)) ∧
      (∀ B ∈ T, ∀ C ∈ T, B ≠ C → Disjoint B C) ∧ s ⊆ ⋃ B ∈ T, B := by
  let ballAt (x : s) := closedBall x.val (radius x)
  obtain ⟨U,hU⟩ := hs.elim_nhds_subcover' (fun x hx => ballAt ⟨x,hx⟩)
    (fun x hx => closedBall_mem_nhds x (hr ⟨x,hx⟩))
  let S := U.image ballAt
  let T := S.filter (Maximal (· ∈ S))
  have origin {B : Set K} (hb : B ∈ S) : ∃ x : s, B = ballAt x := by
    obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hb
    exact ⟨x,rfl⟩
  refine ⟨T,fun B hB => origin (Finset.mem_filter.mp hB).1,?_,?_⟩
  · intro B hB C hC hne
    obtain ⟨hb,mb⟩ := Finset.mem_filter.mp hB
    obtain ⟨hc,mc⟩ := Finset.mem_filter.mp hC
    obtain ⟨x,rfl⟩ := origin hb
    obtain ⟨y,rfl⟩ := origin hc
    rcases IsUltrametricDist.closedBall_subset_trichotomy x.val y.val (radius x) (radius y) with h|h|h
    · exact (hne (Subset.antisymm h (mb.2 hc h))).elim
    · exact (hne (Subset.antisymm (mc.2 hb h) h)).elim
    · exact h
  · intro z hz
    obtain ⟨x,hx,hzx⟩ := mem_iUnion₂.mp (hU hz)
    obtain ⟨B,hsub,hmax⟩ := S.exists_le_maximal (Finset.mem_image.mpr ⟨x,hx,rfl⟩ : ballAt x ∈ S)
    exact mem_iUnion₂.mpr ⟨B,Finset.mem_filter.mpr ⟨hmax.1,hmax⟩,hsub hzx⟩

private theorem sum_indicator_roots {K : Type*} [Field K] {n : ℕ} (hn : 0 < n)
    {B C : Set K} (h : BijOn (fun x : K => x^n) B C) (c : ℂ) (y : K) :
    ∑ x ∈ nthRootsFinset n y, B.indicator (fun _ => c) x = C.indicator (fun _ => c) y := by
  by_cases hy : y ∈ C
  · obtain ⟨a,ha,rfl⟩ := h.surjOn hy
    rw [indicator_of_mem hy,Finset.sum_eq_single_of_mem a ((mem_nthRootsFinset hn _).mpr rfl),
      indicator_of_mem ha]
    intro b hb hba
    exact indicator_of_notMem (fun hB => hba (h.injOn hB ha ((mem_nthRootsFinset hn _).mp hb))) _
  · rw [indicator_of_notMem hy]
    apply Finset.sum_eq_zero
    intro a ha
    exact indicator_of_notMem (fun hB => hy (((mem_nthRootsFinset hn _).mp ha) ▸ h.mapsTo hB)) _

namespace Datum
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)
private instance finiteProper (p : HeightOneSpectrum (𝓞 F)) : ProperSpace (LocalField F (.inr p)) := by
  letI : NontriviallyNormedField (p.adicCompletion F) := FinitePlace.nontriviallyNormedCompletion p
  exact .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace (p.adicCompletion F)

omit [NeZero n] in
private theorem integral_scaled_ball (p : HeightOneSpectrum (𝓞 F)) (a b : LocalField F (.inr p))
    (k : (LocalField F (.inr p))ˣ) (r : ℝ) (c : ℂ) :
    let dx := selfDual F d.character (.inr p)
    (∫ y, (closedBall b (‖k.val‖*r)).indicator (fun _ => c) y ∂dx) =
      (‖k.val‖ : ℂ) * ∫ x, (closedBall a r).indicator (fun _ => c) x ∂dx := by
  let v : Place F := .inr p
  let K := LocalField F v
  let dx := selfDual F d.character v
  letI : dx.IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  let f := (closedBall b (‖k.val‖*r)).indicator (fun _ => c)
  have h (x : K) : f (k.val*(x-a)+b) = (closedBall a r).indicator (fun _ => c) x := by
    have e : k.val*(x-a)+b ∈ closedBall b (‖k.val‖*r) ↔ x ∈ closedBall a r := by
      simp only [mem_closedBall,dist_eq_norm,add_sub_cancel_right,norm_mul]
      exact mul_le_mul_iff_right₀ (norm_pos_iff.mpr k.ne_zero)
    simp [f,Set.indicator_apply,e]
  have hmul := d.integral_local_mul v k (fun t => f (t+b))
  change (∫ x, f (k.val*x+b) ∂dx) = (∫ x, f (x+b) ∂dx) / (‖k.val‖ : ℂ) at hmul
  rw [integral_add_right_eq_self] at hmul
  have he := integral_add_right_eq_self (μ := dx) (fun x => f (k.val*x+b)) (-a)
  change (∫ y, f y ∂dx) = _
  have hk : (‖k.val‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr k.ne_zero
  rw [← (eq_div_iff hk).mp hmul,← he,mul_comm]
  simp only [← sub_eq_add_neg,h]
  rfl

/-- Integrating a sum over the distinct n-th roots amounts to multiplying the
test function by the norm of the derivative of the power map. -/
theorem finite_power_area (p : HeightOneSpectrum (𝓞 F)) {g : LocalField F (.inr p) → ℂ}
    (hl : IsLocallyConstant g) (hc : HasCompactSupport g) (h₀ : g 0 = 0) :
    let dx := selfDual F d.character (.inr p)
    (∫ y, ∑ x ∈ nthRootsFinset n y, g x ∂dx) =
      ∫ x, (‖(n : LocalField F (.inr p))*x^(n-1)‖ : ℂ) * g x ∂dx := by
  let K := LocalField F (.inr p)
  letI : NontriviallyNormedField (p.adicCompletion F) := FinitePlace.nontriviallyNormedCompletion p
  letI : CharZero K := charZero_of_injective_ringHom (algebraMap F (p.adicCompletion F)).injective
  letI : IsUltrametricDist K := inferInstanceAs (IsUltrametricDist (p.adicCompletion F))
  let dx := selfDual F d.character (.inr p)
  letI : dx.IsAddHaarMeasure := (existsUnique_selfDual F d.character (.inr p)).exists.choose_spec.1
  let deriv (x : K) := (n : K)*x^(n-1)
  have hn : (n : K) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  let s := Function.support g
  have hclosed : IsClosed s := (hl.isOpen_fiber 0).isClosed_compl
  have hs : IsCompact s := by
    change IsCompact (closure s) at hc
    rwa [hclosed.closure_eq] at hc
  have nonzero (a : s) : a.val ≠ 0 := fun h => a.property (h ▸ h₀)
  have localData (a : s) : ∃ r > (0 : ℝ),
      BijOn (fun x : K => x^n) (closedBall a.val r) (closedBall (a.val^n) (‖deriv a.val‖*r)) ∧
      ∀ x ∈ closedBall a.val r, g x = g a.val ∧ ‖deriv x‖ = ‖deriv a.val‖ := by
    obtain ⟨R,hR,hp⟩ := power_local_balls (K := p.adicCompletion F) n hn a.val (nonzero a)
    obtain ⟨t,ht,hf⟩ := Metric.mem_nhds_iff.mp (hl.eventually_eq a.val)
    let r := min R (t/2)
    have hr : 0 < r := lt_min hR (half_pos ht)
    obtain ⟨hb,hj⟩ := hp r hr (min_le_left _ _)
    exact ⟨r,hr,hb,fun x hx => ⟨hf (closedBall_subset_ball ((min_le_right R (t/2)).trans_lt
      (half_lt_self ht)) hx),hj x hx⟩⟩
  choose rad hrad hbij hconst using localData
  obtain ⟨T,hT,hdis,hcover⟩ := disjoint_closedBall_cover (K := K) hs rad hrad
  choose center hball using fun i : T => hT i.val i.property
  let A (i : T) := (center i).val
  let k (i : T) : Kˣ := Units.mk0 (deriv (A i)) (mul_ne_zero hn (pow_ne_zero _ (nonzero _)))
  let C (i : T) := closedBall ((A i)^n) (‖(k i).val‖*rad (center i))
  let f (i : T) := i.val.indicator (fun _ => g (A i))
  let out (i : T) := (C i).indicator (fun _ => g (A i))
  have he (x : K) : g x = ∑ i, f i x := by
    by_cases hx : ∃ i : T, x ∈ i.val
    · obtain ⟨i,hi⟩ := hx
      rw [Finset.sum_eq_single i]
      · unfold f
        rw [indicator_of_mem hi]
        exact (hconst (center i) x (hball i ▸ hi)).1
      · intro j _ hji
        exact indicator_of_notMem (fun hj =>
          Set.disjoint_left.mp (hdis _ j.property _ i.property (fun h => hji (Subtype.ext h))) hj hi) _
      · simp
    · have hz : x ∉ s := fun ha => by
        obtain ⟨B,hB,hxB⟩ := mem_iUnion₂.mp (hcover ha)
        exact hx ⟨⟨B,hB⟩,hxB⟩
      rw [Function.notMem_support.mp hz,Finset.sum_eq_zero (fun i _ =>
        indicator_of_notMem (fun hi => hx ⟨i,hi⟩) _)]
  have hout (y : K) : (∑ x ∈ nthRootsFinset n y, g x) = ∑ i, out i y := by
    simp_rw [he]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => sum_indicator_roots (NeZero.pos n)
      (hball i ▸ hbij (center i) : BijOn (fun x : K => x^n) i.val (C i)) _ y
  have hin (x : K) : (‖deriv x‖ : ℂ)*g x = ∑ i, (‖(k i).val‖ : ℂ)*f i x := by
    rw [he,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hx : x ∈ i.val
    · rw [(hconst (center i) x (hball i ▸ hx)).2]
      rfl
    · simp [f,indicator_of_notMem hx]
  have intBall (a : K) (r : ℝ) (c : ℂ) :
      Integrable ((closedBall a r).indicator (fun _ => c)) dx :=
    (integrableOn_const (isCompact_closedBall a r).measure_ne_top).integrable_indicator
      isClosed_closedBall.measurableSet
  have hfi (i : T) : Integrable (f i) dx := by
    unfold f
    rw [hball i]
    exact intBall _ _ _
  change (∫ y, ∑ x ∈ nthRootsFinset n y, g x ∂dx) = ∫ x, (‖deriv x‖ : ℂ)*g x ∂dx
  apply (integral_congr_ae (μ := dx) (Eventually.of_forall hout)).trans
  apply Eq.trans _ (integral_congr_ae (μ := dx) (Eventually.of_forall hin)).symm
  rw [integral_finsetSum _ (fun i _ => intBall _ _ _ : ∀ i ∈ Finset.univ, Integrable (out i) dx),
    integral_finsetSum _ (fun i _ => (hfi i).const_mul _)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_const_mul]
  change (∫ y, (C i).indicator (fun _ => g (A i)) y ∂dx) =
    (‖(k i).val‖ : ℂ) * ∫ x, i.val.indicator (fun _ => g (A i)) x ∂dx
  rw [hball i]
  exact d.integral_scaled_ball p _ _ _ _ _

end Datum
end MetaplecticPoisson
