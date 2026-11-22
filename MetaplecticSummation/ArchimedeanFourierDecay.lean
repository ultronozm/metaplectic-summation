import MetaplecticSummation.ArchimedeanLeading
import MetaplecticSummation.FourierDifferences
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-! The Fourier transform of a bounded family of archimedean Radon slices in §4. -/
noncomputable section
namespace MetaplecticPoisson
open NumberField MeasureTheory Set
open scoped ContDiff

/-- A chart family consists of Schwartz functions in the line variable,
with each derivative bounded in every polynomial weight on compact parameter sets. -/
def SchwartzSliceFamily {P K L : Type} [TopologicalSpace P] [NormedField K]
    [NormedField L] [NormedAlgebra ℝ L] (e : K ≃+* L) (R : P → K → ℂ) : Prop :=
  ∃ G : P → SchwartzMap L ℂ, (∀ q t, R q t = G q (e t)) ∧
    ∀ T : Set P, IsCompact T → ∀ k N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ T, ∀ y : L,
      ‖iteratedFDeriv ℝ k (G q) y‖ * (1+‖y‖)^N ≤ C

private theorem fwdDiff_pullback {K L : Type} [Field K] [Field L] (e : K ≃+* L)
    {f : K → ℂ} {g : L → ℂ} (H : ∀ t, f t = g (e t)) (h : K) (j : ℕ) (t : K) :
    (fwdDiff h)^[j] f t = (fwdDiff (e h))^[j] g (e t) := by
  induction j generalizing t with
  | zero => exact H t
  | succ j ih => simp only [Function.iterate_succ_apply',fwdDiff,ih,map_add]

namespace Datum
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

omit [NeZero n] in
/-- For the chosen local character and self-dual measure, Fourier integrals of
a bounded Schwartz family decay to every order, uniformly on compact parameter sets. -/
theorem hat_decay_of_schwartz_slices (w : InfinitePlace F) {P L : Type} [TopologicalSpace P]
    [NormedField L] [NormedAlgebra ℝ L] (e : w.Completion ≃+* L) (he : Isometry e)
    {R : P → LocalField F (.inl w) → ℂ} (hR : SchwartzSliceFamily e R)
    (hi : ∀ q, Integrable (R q) (selfDual F d.character (.inl w))) (T : Set P) (hT : IsCompact T) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ T, ∀ u : LocalField F (.inl w), 1 ≤ ‖u‖ →
      ‖d.hat (.inl w) (R q) u‖ * (1+‖u‖)^j ≤ C := by
  obtain ⟨G,hG,H⟩ := hR
  obtain ⟨M,hM,hD⟩ := H T hT j 3
  apply d.hat_decay_of_fwdDiff _ R T (fun q _ => hi q) j
  intro a
  let D := M*(1+j*‖a‖)^3
  let μ := selfDual F d.character (.inl w)
  let V := ∫ t : LocalField F (.inl w), ((1+‖t‖)^3)⁻¹ ∂μ
  have hd : 0 ≤ D := by dsimp [D]; positivity
  have hv : 0 ≤ V := integral_nonneg (fun _ => by positivity)
  refine ⟨D*V,mul_nonneg hd hv,?_⟩
  intro q hq u hu
  let h := a/u
  have hh : ‖h‖ ≤ ‖a‖ := by rw [show ‖h‖ = ‖a‖/‖u‖ from norm_div ..]; exact div_le_self (norm_nonneg _) hu
  have bound (t : LocalField F (.inl w)) : ‖(fwdDiff h)^[j] (R q) t‖ ≤ D*‖h‖^j*((1+‖t‖)^3)⁻¹ := by
    apply (congrArg norm (fwdDiff_pullback e (hG q) h j t)).trans_le
    have hstep : ‖e h‖ ≤ ‖a‖ := (he.norm_map_of_map_zero e.map_zero h).trans_le hh
    have ht := fwdDiff_decay ((G q).smooth ⊤) (hD q hq) (e t) (e h) hstep
    simpa only [D,he.norm_map_of_map_zero e.map_zero] using! ht
  have hi' := (d.hat_iterated_fwdDiff (.inl w) (hi q) h u j).1.norm
  have hle := integral_mono hi' ((d.arch_integrable_inv_cube w).const_mul (D*‖h‖^j)) bound
  apply hle.trans_eq
  rw [integral_const_mul]
  change D*‖h‖^j*V = D*V*‖h‖^j
  ring

/-- The slice assertion of Lemma 4.2(iii) at a real or complex place. -/
theorem arch_radon_schwartz_slices (w : InfinitePlace F) {f : Charts w.Completion} (hf : f ∈ d.testSet (.inl w))
    {L : Type} [NormedField L] [NormedAlgebra ℝ L] (e : w.Completion ≃+* L) (he : Isometry e) :
    let v : Place F := .inl w
    let R := radon n (d.symbol v) (modulus F v) (selfDual F d.character v) f
    SchwartzSliceFamily e (fun (q : w.Completionˣ × w.Completion) t => (R t).1 q.1 q.2) ∧
    SchwartzSliceFamily e (fun (q : w.Completionˣ × w.Completion) t => (R t).2 q.2 q.1) := by sorry

/-- Uniform high-frequency decay of the ordinary one-dimensional Fourier integrals
of both Radon charts. -/
theorem arch_radon_hat_decay (w : InfinitePlace F) {f : Charts w.Completion} (hf : f ∈ d.testSet (.inl w))
    (T : Set (w.Completionˣ × w.Completion)) (hT : IsCompact T) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ T, ∀ u : w.Completion, 1 ≤ ‖u‖ →
      ‖d.archRadonHat w f q u‖ * (1+‖u‖)^j ≤ C := by
  have go {L : Type} [NormedField L] [NormedAlgebra ℝ L] (e : w.Completion ≃+* L) (he : Isometry e) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ T, ∀ u : w.Completion, 1 ≤ ‖u‖ →
        ‖d.archRadonHat w f q u‖ * (1+‖u‖)^j ≤ C := by
    obtain ⟨hx,hy⟩ := d.arch_radon_schwartz_slices w hf e he
    obtain ⟨ix,iy⟩ := d.arch_test_integrable_slices w hf
    obtain ⟨A,hA,X⟩ := d.hat_decay_of_schwartz_slices w e he hx (fun q => ix q.1 q.2) T hT j
    obtain ⟨B,_,Y⟩ := d.hat_decay_of_schwartz_slices w e he hy (fun q => iy q.2 q.1) T hT j
    refine ⟨max A B,hA.trans (le_max_left ..),fun q hq u hu => ?_⟩
    rw [Prod.norm_def,max_mul_of_nonneg _ _ (by positivity)]
    exact max_le_max (X q hq u hu) (Y q hq u hu)
  by_cases hw : w.IsReal
  · exact go (InfinitePlace.Completion.ringEquivRealOfIsReal hw) (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw)
  · exact go (InfinitePlace.Completion.ringEquivComplexOfIsComplex (InfinitePlace.not_isReal_iff_isComplex.mp hw))
      (InfinitePlace.Completion.isometry_extensionEmbedding w)

end Datum
end MetaplecticPoisson
