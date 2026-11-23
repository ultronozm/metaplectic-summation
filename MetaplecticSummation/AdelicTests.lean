import MetaplecticSummation.SchwartzTensor
import MetaplecticSummation.AdditivePoisson
import MetaplecticSummation.FiniteAdelicTests
import MetaplecticSummation.Marginals.Regularity

/-! The mixed real and complex tensors used by both applications of additive Poisson in B.4. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace MetaplecticPoisson.Datum
open GroundTheory.Global NumberField IsDedekindDomain Filter MeasureTheory
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open Classical
variable {F : Type} [Field F] [NumberField F]
local notation "P" => HeightOneSpectrum (𝓞 F)

theorem exists_infiniteSchwartzTensor (f : (w : InfinitePlace F) → w.Completion → ℂ)
    (hf : ∀ w, Bruhat (.inl w) (f w)) :
    ∃ φ : SchwartzMap (mixedEmbedding.mixedSpace F) ℂ,
      ∀ x : InfiniteAdeleRing F, φ (homeomorphMixedSpace F x) = ∏ w, f w (x w) := by
  let R := {w : InfinitePlace F // w.IsReal}
  let C := {w : InfinitePlace F // w.IsComplex}
  have hr (w : R) : ∃ g : SchwartzMap ℝ ℂ, ∀ t, f w.val t = g (extensionEmbeddingOfIsReal w.property t) := by
    have hw := hf w.val
    simp only [Bruhat,dite_eq_left w.property] at hw
    obtain ⟨g,hg⟩ := hw
    exact ⟨g,fun t => (hg t).trans (congrArg g (ringEquivRealOfIsReal_apply w.property t))⟩
  have hc (w : C) : ∃ g : SchwartzMap ℂ ℂ, ∀ t, f w.val t = g (extensionEmbedding w.val t) := by
    have hw := hf w.val
    simp only [Bruhat,dite_eq_right (not_isReal_iff_isComplex.mpr w.property)] at hw
    obtain ⟨g,hg⟩ := hw
    exact ⟨g,fun t => (hg t).trans (congrArg g (ringEquivComplexOfIsComplex_apply w.property t))⟩
  choose r hr using hr
  choose c hc using hc
  obtain ⟨φ,hφ⟩ := exists_schwartz_tensor r
  obtain ⟨γ,hγ⟩ := exists_schwartz_tensor c
  refine ⟨schwartzProduct φ γ,fun x => ?_⟩
  change φ _ * γ _ = _
  rw [hφ,hγ,← Fintype.prod_subtype_mul_prod_subtype (fun w : InfinitePlace F => w.IsReal)]
  congr 1
  · exact Finset.prod_congr rfl (fun w _ => (hr w (x w)).symm)
  · exact Fintype.prod_equiv (Equiv.subtypeEquivRight fun w : InfinitePlace F => not_isReal_iff_isComplex.symm)
      _ _ (fun w => (hc w (x w)).symm)

/-- The product over the infinite places times the restricted product over finite places. -/
def adelicTensor (f : (v : Place F) → LocalField F v → ℂ) (x : Adeles F) : ℂ :=
  (∏ w, f (.inl w) (x.1 w)) * ∏ᶠ p : P, f (.inr p) (x.2 p)

/-- Membership of a restricted tensor of all local tests in the adelic Poisson test space. -/
theorem adelicTensor_mem_schwartzBruhat (f : (v : Place F) → LocalField F v → ℂ)
    (hf : ∀ v, Bruhat v (f v))
    (h : ∀ᶠ p : P in cofinite, ∀ t, f (.inr p) t = if ‖t‖ ≤ 1 then 1 else 0) :
    adelicTensor f ∈ schwartzBruhat F := by
  obtain ⟨φ,hφ⟩ := exists_infiniteSchwartzTensor (fun w => f (.inl w)) (fun w => hf (.inl w))
  have hg := finiteTensor_mem_schwartzBruhat (fun p => f (.inr p)) (fun p => hf (.inr p)) h
  convert schwartzBruhatTensor_mem φ hg using 1
  funext x
  exact congrArg (· * _) (hφ x.1).symm

variable {n : ℕ} [NeZero n] (d : Datum F n)

theorem adelicTensor_axisLine (Φ : ∀ v, d.schwartz v) (hΦ : ∀ᶠ v in cofinite, Φ v = d.basic v) (y : Fˣ) :
    adelicTensor (fun v => d.axisLine v (Φ v) (atPlace v y)) ∈ schwartzBruhat F :=
  adelicTensor_mem_schwartzBruhat (fun v => d.axisLine v (Φ v) (atPlace v y)) (fun v => d.axisLine_bruhat v _ _) (d.eventually_axisLine_basic Φ hΦ y)

theorem adelicTensor_axisDensity (Φ : ∀ v, d.schwartz v) (hΦ : ∀ᶠ v in cofinite, Φ v = d.basic v) (y : Fˣ) :
    adelicTensor (fun v => d.axisDensity v (Φ v) (atPlace v y)) ∈ schwartzBruhat F :=
  adelicTensor_mem_schwartzBruhat (fun v => d.axisDensity v (Φ v) (atPlace v y)) (fun v => d.axisDensity_bruhat v _ _) (d.eventually_axisDensity_basic Φ hΦ y)

end MetaplecticPoisson.Datum
