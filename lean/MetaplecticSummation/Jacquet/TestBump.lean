import MetaplecticSummation.Jacquet.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Topology.LocallyConstant.Algebra

/-! Compact test weights supported in an arbitrary open subset of the local units. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open MeasureTheory NumberField Filter Set Metric
open scoped Topology ContDiff
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n]

private theorem arch_bump {K E : Type} [NormedField K] [NormedField E] [NormedAlgebra ℝ E]
    [FiniteDimensional ℝ E] (e : K ≃+* E) (he : Isometry e)
    {U : Set Kˣ} (hU : IsOpen U) (a : Kˣ) (ha : a ∈ U) :
    ∃ g : Kˣ → ℝ, Continuous g ∧ HasCompactSupport g ∧ (∀ x, 0 ≤ g x) ∧ g a = 1 ∧
      (∀ x ∉ U, g x = 0) ∧ ∀ z : ℂ, archSmooth e (fun x => z * (g x : ℂ)) := by
  let i : K ≃ᵢ E := ⟨e.toEquiv,he⟩
  let j : Kˣ → E := fun x => i x.val
  have hj : Topology.IsOpenEmbedding j := i.toHomeomorph.isOpenEmbedding.comp
    (show Topology.IsOpenEmbedding (Units.val : Kˣ → K) from
      (IsOpen.isOpenEmbedding_subtypeVal isOpen_compl_singleton).comp unitsHomeomorphNeZero.isOpenEmbedding)
  obtain ⟨b,hsub,hk,hd,hb,h1⟩ := exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞))
    ((hj.isOpenMap U hU).mem_nhds (mem_image_of_mem j ha))
  refine ⟨b ∘ j,hd.continuous.comp hj.continuous,?_,fun x => (hb ⟨_,rfl⟩).1,h1,?_,?_⟩
  · exact HasCompactSupport.intro (hj.isInducing.isCompact_preimage' hk
      (hsub.trans (image_subset_range ..))) (fun x hx => (image_eq_zero_of_notMem_tsupport (f := b) (x := j x) hx))
  · intro x hx
    change b (j x) = 0
    apply image_eq_zero_of_notMem_tsupport
    exact fun h => hx (by obtain ⟨y,hy,heq⟩ := hsub h; exact hj.injective heq ▸ hy)
  · intro z
    apply ((contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hd)).contDiffOn :
      ContDiffOn ℝ ∞ (fun t => z * (b t : ℂ)) {0}ᶜ).congr
    intro t ht
    have ht' : e.symm t ≠ 0 := (map_ne_zero e.symm).mpr ht
    simp only [dif_pos ht',Function.comp_apply,j,Units.val_mk0]
    exact congrArg (fun s => z * (b s : ℂ)) (e.apply_symm_apply t)

private theorem finite_bump {K : Type} [NormedField K] [ProperSpace K] [IsUltrametricDist K]
    {U : Set Kˣ} (hU : IsOpen U) (a : Kˣ) (ha : a ∈ U) :
    ∃ g : Kˣ → ℝ, Continuous g ∧ HasCompactSupport g ∧ (∀ x, 0 ≤ g x) ∧ g a = 1 ∧
      (∀ x ∉ U, g x = 0) ∧ ∀ z : ℂ, IsLocallyConstant (fun x => z * (g x : ℂ)) := by
  have hj : Topology.IsOpenEmbedding (Units.val : Kˣ → K) :=
    (IsOpen.isOpenEmbedding_subtypeVal isOpen_compl_singleton).comp unitsHomeomorphNeZero.isOpenEmbedding
  obtain ⟨r,hr,hs⟩ := Metric.mem_nhds_iff.mp ((hj.isOpenMap U hU).mem_nhds (mem_image_of_mem Units.val ha))
  let B : Set K := closedBall (a.val : K) (r/2)
  have hcl : IsClopen B := IsUltrametricDist.isClopen_closedBall _ (half_pos hr).ne'
  have sub : B ⊆ Units.val '' U := (closedBall_subset_ball (half_lt_self hr)).trans hs
  let C := (Units.val : Kˣ → K) ⁻¹' B
  have hc : IsClopen C := hcl.preimage hj.continuous
  have hk : IsCompact C := hj.isInducing.isCompact_preimage' (isCompact_closedBall _ _) (sub.trans (image_subset_range ..))
  let g := C.indicator (fun _ => (1 : ℝ))
  have lg : IsLocallyConstant g := (LocallyConstant.charFn ℝ hc).isLocallyConstant
  have kg : HasCompactSupport g := HasCompactSupport.intro hk (fun _ h => indicator_of_notMem h _)
  refine ⟨g,lg.continuous,kg,fun x => indicator_nonneg (fun _ _ => zero_le_one) x,?_,?_,?_⟩
  · exact indicator_of_mem (show a ∈ C from mem_closedBall_self (half_pos hr).le) _
  · intro x hx
    apply indicator_of_notMem
    intro h
    obtain ⟨y,hy,e⟩ := sub h
    exact hx (Units.ext e ▸ hy)
  · intro z
    exact lg.comp (fun t => z * (t : ℂ))

theorem exists_test_bump (v : Place F) {U : Set (LocalField F v)ˣ} (hU : IsOpen U)
    (a : (LocalField F v)ˣ) (ha : a ∈ U) :
    ∃ g : (LocalField F v)ˣ → ℝ, Continuous g ∧ HasCompactSupport g ∧ (∀ x, 0 ≤ g x) ∧ g a = 1 ∧
      (∀ x ∉ U, g x = 0) ∧ ∀ z : ℂ, TestWeight v (fun x => z * (g x : ℂ)) := by
  cases v with
  | inl w =>
    by_cases hw : w.IsReal
    · obtain ⟨g,hc,hk,hp,hg,hs,hd⟩ := arch_bump (InfinitePlace.Completion.ringEquivRealOfIsReal hw)
        (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw) hU a ha
      exact ⟨g,hc,hk,hp,hg,hs,fun z => ⟨(hk.comp_left Complex.ofReal_zero).mul_left,
        by dsimp only; rw [dif_pos hw]; exact hd z⟩⟩
    · let h := InfinitePlace.not_isReal_iff_isComplex.mp hw
      obtain ⟨g,hc,hk,hp,hg,hs,hd⟩ := arch_bump (InfinitePlace.Completion.ringEquivComplexOfIsComplex h)
        (InfinitePlace.Completion.isometry_extensionEmbedding w) hU a ha
      exact ⟨g,hc,hk,hp,hg,hs,fun z => ⟨(hk.comp_left Complex.ofReal_zero).mul_left,
        by dsimp only; rw [dif_neg hw]; exact hd z⟩⟩
  | inr p =>
    let K := p.adicCompletion F
    letI : NontriviallyNormedField K := FinitePlace.nontriviallyNormedCompletion p
    letI : ProperSpace K := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace _
    obtain ⟨g,hc,hk,hp,hg,hs,hd⟩ := finite_bump (K := p.adicCompletion F) hU a ha
    exact ⟨g,hc,hk,hp,hg,hs,fun z => ⟨(hk.comp_left Complex.ofReal_zero).mul_left,hd z⟩⟩

end MetaplecticPoisson.Datum
