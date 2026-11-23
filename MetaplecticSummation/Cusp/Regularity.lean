import MetaplecticSummation.Cusp.Orbit
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-! Regularity in the unfolding from products of pairs of rational evaluations. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField Filter Set MeasureTheory
open scoped Topology ComplexConjugate
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)
local instance regularitySchwartzAddGroup : AddCommGroup d.Schwartz := Module.addCommMonoidToAddCommGroup ℂ

/-- A locally summably bounded family with continuous pairwise products has a
continuous absolute sum value and continuous products with its conjugate series. -/
private theorem continuous_theta_products {T I : Type*} [TopologicalSpace T] [WeaklyLocallyCompactSpace T]
    (f : T → I → ℂ) (h : ∀ i j, Continuous (fun x => f x i * conj (f x j)))
    (major : ∀ K : Set T, IsCompact K → ∃ b : I → ℝ, Summable b ∧ ∀ x ∈ K, ∀ i, ‖f x i‖ ≤ b i) :
    Continuous (fun x => ‖∑' i, f x i‖) ∧ ∀ i, Continuous (fun x => f x i * conj (∑' j, f x j)) := by
  let Ξ := fun x => ∑' i, f x i
  let A := fun i x => f x i * conj (Ξ x)
  have sumA (i x) : (∑' j, f x i * conj (f x j)) = A i x := by
    rw [tsum_mul_left,← Complex.conj_tsum]
  have localEst (x : T) : ∃ K ∈ 𝓝 x, (∀ i, ContinuousOn (A i) K) ∧
      ContinuousOn (fun x => ‖Ξ x‖) K := by
    obtain ⟨K,hK,hx⟩ := exists_compact_mem_nhds x
    obtain ⟨b,hb,bound⟩ := major K hK
    have h₀ (i) : 0 ≤ b i := (norm_nonneg _).trans (bound x (mem_of_mem_nhds hx) i)
    have hc (i) : ContinuousOn (A i) K := by
      change ContinuousOn (fun y => A i y) K
      simp_rw [← sumA]
      apply continuousOn_tsum (fun j => (h i j).continuousOn) (hb.mul_left (b i))
      intro j y hy
      rw [norm_mul,RCLike.norm_conj]
      exact mul_le_mul (bound y hy i) (bound y hy j) (norm_nonneg _) (h₀ i)
    have hsum : ContinuousOn (fun y => (∑' i, A i y)) K := by
      apply continuousOn_tsum hc (hb.mul_right (∑' j, b j))
      intro i y hy
      dsimp only [A,Ξ]
      rw [norm_mul,RCLike.norm_conj]
      have summ := hb.of_nonneg_of_le (fun j => norm_nonneg (f y j)) (bound y hy)
      exact mul_le_mul (bound y hy i) ((norm_tsum_le_tsum_norm summ).trans (summ.tsum_le_tsum (bound y hy) hb))
        (norm_nonneg _) (h₀ i)
    have realPart (y) : Real.sqrt (∑' i, A i y).re = ‖Ξ y‖ := by
      dsimp only [A]
      rw [tsum_mul_right,show (∑' i, f y i) = Ξ y from rfl,Complex.mul_conj,
        Complex.ofReal_re,Complex.normSq_eq_norm_sq,Real.sqrt_sq (norm_nonneg _)]
    refine ⟨K,hx,hc,?_⟩
    exact ((Real.continuous_sqrt.comp Complex.continuous_re).comp_continuousOn hsum).congr
      (fun y _ => (realPart y).symm)
  constructor
  · apply continuous_iff_continuousAt.mpr
    intro x
    obtain ⟨K,hK,_,hc⟩ := localEst x
    exact (hc x (mem_of_mem_nhds hK)).continuousAt hK
  · intro i
    apply continuous_iff_continuousAt.mpr
    intro x
    obtain ⟨K,hK,hc,_⟩ := localEst x
    exact (hc i x (mem_of_mem_nhds hK)).continuousAt hK

/-- The two regularity inputs for B.6 reduce to continuity of products of two
individual evaluations. The individual evaluations may depend on the chosen lift. -/
theorem thetaDifference_eq_zero_of_continuous_evaluation_products (Φ : ∀ v, d.schwartz v)
    (hf : ∀ᶠ v in cofinite, Φ v = d.basic v)
    (v t : Place F) (hv : d.leading v (Φ v) = 0) (ht : d.leading t (d.fourier t (Φ t)) = 0)
    (w : Prime F) (hc : ∀ p q : RationalPoint F, Continuous (fun m : AdelicSL F =>
      let f := d.liftedAction (d.pure Φ hf - d.adelicFourier (d.pure Φ hf)) m
      d.evaluation f p * conj (d.evaluation f q))) : d.thetaDifference (d.pure Φ hf) = 0 := by
  let φ := d.pure Φ hf
  let Δ := φ-d.adelicFourier φ
  let f := fun (m : AdelicSL F) => d.evaluation (d.liftedAction Δ m)
  let Ψ := fun v => d.fourier v (Φ v)
  have hΨ : ∀ᶠ v in cofinite, Ψ v = d.basic v := (hf.and d.eventually_fourier_basic).mono fun _ h => h.1 ▸ h.2
  have major (K : Set (AdelicSL F)) (hK : IsCompact K) : ∃ b : RationalPoint F → ℝ,
      Summable b ∧ ∀ x ∈ K, ∀ i, ‖f x i‖ ≤ b i := by
    obtain ⟨b,hb,e⟩ := d.compact_theta_majorant Φ hf hK
    obtain ⟨b',hb',e'⟩ := d.compact_theta_majorant Ψ hΨ hK
    refine ⟨_,hb.add hb',fun m hm p => ?_⟩
    obtain ⟨hg,pg⟩ := (d.exists_restricted_lift m).choose_spec
    dsimp only [f,Δ,φ,liftedAction]
    rw [map_sub,map_sub,Pi.sub_apply,d.adelicFourier_pure]
    exact (norm_sub_le ..).trans (add_le_add (e m hm _ hg pg p) (e' m hm _ hg pg p))
  obtain ⟨hn,ha⟩ := continuous_theta_products f hc major
  apply d.thetaDifference_eq_zero_of_quotient_regularity Φ hf v t hv ht w
  · apply continuous_coinduced_dom.mpr
    refine hn.congr fun m => ?_
    change ‖d.theta (d.coverAction _ _ (φ-d.adelicFourier φ))‖ = ‖d.thetaDifference (d.liftedAction φ m)‖
    rw [map_sub,map_sub,← d.coverAction_fourier]
    rfl
  · intro U hU
    exact (ha (verticalPoint F)).measurable hU

end MetaplecticPoisson.Datum
