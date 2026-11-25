import MetaplecticSummation.SmoothFiniteLines
import MetaplecticSummation.LocalCharacters

/-! Absolute convergence and smoothness of Definition 4.4 on finite-place
test functions. -/

noncomputable section
namespace MetaplecticPoisson
open MeasureTheory Filter Set
open scoped Topology

namespace SmoothFiniteFamily
variable {P K : Type*} [TopologicalSpace P] [NormedField K] {g : P → K → ℂ}

theorem locallyConstant [WeaklyLocallyCompactSpace P] (hg : SmoothFiniteFamily g) :
    IsLocallyConstant g := by
  apply locallyConstant_slices_of_localSupport (G := Function.uncurry g) hg.1
  intro p
  obtain ⟨T,hT,hp⟩ := exists_compact_mem_nhds p
  obtain ⟨C,hC,ho⟩ := (hg.2 T hT).2.1
  exact ⟨C,hC,mem_of_superset hp fun q hq => ho q hq⟩

theorem integrable_weight [MeasurableSpace K] [BorelSpace K] (hg : SmoothFiniteFamily g)
    (dx : Measure K) [IsFiniteMeasureOnCompacts dx] {ψ : K → ℂ} (hc : Continuous ψ) (p : P) :
    Integrable (fun t => ψ t * g p t) dx := by
  have hl : IsLocallyConstant (g p) := hg.1.comp_continuous (continuous_const.prodMk continuous_id)
  obtain ⟨C,hC,ho⟩ := (hg.2 {p} isCompact_singleton).2.1
  exact (hc.mul hl.continuous).integrable_of_hasCompactSupport (HasCompactSupport.intro hC
    (fun x hx => by change ψ x * g p x = 0; rw [ho p rfl x hx, mul_zero]))

end SmoothFiniteFamily

namespace Datum
open NumberField IsDedekindDomain
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

/-- The outer integrals of Definition 4.4 converge absolutely for every test
function at a finite place. -/
theorem integrable_finiteTest_transform (p : HeightOneSpectrum (𝓞 F)) {f : Charts (LocalField F (.inr p))}
    (hf : f ∈ d.testSet (.inr p)) :
    let v : Place F := .inr p
    let dx := selfDual F d.character v
    let R := radon n (d.symbol v) (modulus F v) dx f
    (∀ q : (LocalField F v)ˣ × LocalField F v,
      Integrable (fun t => d.character.localValue F v t * (R t).1 q.1 q.2) dx) ∧
    (∀ q : LocalField F v × (LocalField F v)ˣ,
      Integrable (fun t => d.character.localValue F v t * (R t).2 q.1 q.2) dx) := by
  let v : Place F := .inr p
  let dx := selfDual F d.character v
  letI : dx.IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  obtain ⟨hx,hy⟩ := d.smooth_finiteTest_lines p hf
  exact ⟨hx.integrable_weight dx (d.character.continuous_localValue v),
    hy.integrable_weight dx (d.character.continuous_localValue v)⟩

/-- Smoothness in Proposition 4.5 for test sections at finite places. -/
theorem locallyConstant_finiteTest_transform (p : HeightOneSpectrum (𝓞 F)) {f : Charts (LocalField F (.inr p))}
    (hf : f ∈ d.testSet (.inr p)) :
    let v : Place F := .inr p
    let g := d.integralTransform v f
    (IsLocallyConstant fun q : (LocalField F v)ˣ × LocalField F v => g.1 q.1 q.2) ∧
    (IsLocallyConstant fun q : LocalField F v × (LocalField F v)ˣ => g.2 q.1 q.2) := by
  let v : Place F := .inr p
  letI : LocallyCompactSpace (LocalField F v) := inferInstanceAs (LocallyCompactSpace (p.adicCompletion F))
  letI : LocallyCompactSpace {x : LocalField F v // x ≠ 0} :=
    (isOpen_ne_fun continuous_id (continuous_const (y := (0 : LocalField F v)))).locallyCompactSpace
  letI : LocallyCompactSpace (LocalField F v)ˣ := unitsHomeomorphNeZero.isOpenEmbedding.locallyCompactSpace
  let L (g : LocalField F v → ℂ) : ℂ := (Real.sqrt (modulus F v (n : LocalField F v)) : ℂ)⁻¹ *
    ∫ t, d.character.localValue F v t * g t ∂selfDual F d.character v
  obtain ⟨hx,hy⟩ := d.smooth_finiteTest_lines p hf
  exact ⟨hx.locallyConstant.comp L, hy.locallyConstant.comp L⟩

/-- Both charts of every finite-place Schwartz section are locally constant. -/
theorem locallyConstant_finite_schwartz (p : HeightOneSpectrum (𝓞 F)) (f : d.schwartz (.inr p)) :
    let K := LocalField F (.inr p)
    (IsLocallyConstant fun q : Kˣ × K => f.val.1 q.1 q.2) ∧
    (IsLocallyConstant fun q : K × Kˣ => f.val.2 q.1 q.2) := by
  let K := LocalField F (.inr p)
  let smooth (g : Charts K) := (IsLocallyConstant fun q : Kˣ × K => g.1 q.1 q.2) ∧
    (IsLocallyConstant fun q : K × Kˣ => g.2 q.1 q.2)
  refine Submodule.span_induction (p := fun g _ => smooth g) ?_ ?_ ?_ ?_ f.property
  · rintro g (hg | ⟨h,hh,rfl⟩)
    · have ht : finiteTest g := hg.2
      exact ⟨ht.1,ht.2.1⟩
    · exact d.locallyConstant_finiteTest_transform p hh
  · exact ⟨IsLocallyConstant.const 0,IsLocallyConstant.const 0⟩
  · rintro g h _ _ ⟨gx,gy⟩ ⟨hx,hy⟩
    exact ⟨gx.comp₂ hx (· + ·),gy.comp₂ hy (· + ·)⟩
  · rintro c g _ ⟨gx,gy⟩
    exact ⟨gx.comp (c * ·),gy.comp (c * ·)⟩

end Datum
end MetaplecticPoisson
