import MetaplecticSummation.ArchimedeanLines
import MetaplecticSummation.FiniteHaar

/-! Gluing of the Radon integrals and of sections in the Schwartz space. -/

noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField IsDedekindDomain MeasureTheory
open scoped Topology
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

/-- Finite-place compatibility in Lemma 4.2(ii). The remaining arithmetic input
is the Steinberg relation for the chosen family of Hilbert symbols. -/
theorem finite_radon_glues (p : HeightOneSpectrum (𝓞 F))
    (hS : ∀ a b : (LocalField F (.inr p))ˣ, a.val + b.val = 1 → d.unitPairing (.inr p) a b = 1)
    {f : Charts (LocalField F (.inr p))} (hf : Glues (d.symbol (.inr p)) f)
    (t : LocalField F (.inr p)) :
    Glues (d.symbol (.inr p)) (radon n (d.symbol (.inr p)) (modulus F (.inr p))
      (selfDual F d.character (.inr p)) f t) := by
  let dx := selfDual F d.character (.inr p)
  letI : LocallyCompactSpace (LocalField F (.inr p)) := inferInstanceAs (LocallyCompactSpace (p.adicCompletion F))
  letI : NontriviallyNormedField (LocalField F (.inr p)) := FinitePlace.nontriviallyNormedCompletion p
  letI : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  letI : TopologicalSpace.SeparableSpace (LocalField F (.inr p)) :=
    TopologicalSpace.SeparableSpace.of_denseRange _ (HeightOneSpectrum.denseRange_algebraMap (K := F) p)
  letI : dx.IsAddHaarMeasure := (existsUnique_selfDual F d.character (.inr p)).exists.choose_spec.1
  letI : (𝓝[≠] (0 : LocalField F (.inr p))).NeBot := NormedField.nhdsNE_neBot _
  letI : NullSingletonClass dx := Measure.IsAddHaarMeasure.nullSingletonClass dx
  apply (d.lineSymbol (.inr p) hS).radon_glues dx (NeZero.ne n) _ _ hf t
  intro u
  exact (congrArg NNReal.toReal (FinitePlace.haarChar_eq_nnnorm p u)).symm

/-- A span of genuine test functions and genuine transforms consists of genuine sections. -/
theorem schwartz_glues_of_transform (v : Place F)
    (h : ∀ f ∈ d.testSet v, Glues (d.symbol v) (d.integralTransform v f))
    (Φ : d.schwartz v) : Glues (d.symbol v) Φ.val := by
  refine Submodule.span_induction (p := fun f _ => Glues (d.symbol v) f) ?_ ?_ ?_ ?_ Φ.property
  · intro f hf
    rcases hf with hf | ⟨g, hg, rfl⟩
    · exact hf.1
    · exact h g hg
  · intro a b; simp
  · intro f g _ _ hf hg a b
    change f.1 a b + g.1 a b = _ * (f.2 a b + g.2 a b)
    rw [hf, hg, mul_add]
  · intro c f _ hf a b
    change c * f.1 a b = _ * (c * f.2 a b)
    rw [hf]; ring

theorem arch_schwartz_glues (w : InfinitePlace F) (Φ : d.schwartz (.inl w)) :
    Glues (d.symbol (.inl w)) Φ.val :=
  d.schwartz_glues_of_transform _ (fun _ hf => d.arch_transform_glues w hf.1) Φ

theorem finite_schwartz_glues (p : HeightOneSpectrum (𝓞 F))
    (hS : ∀ a b : (LocalField F (.inr p))ˣ, a.val + b.val = 1 → d.unitPairing (.inr p) a b = 1)
    (Φ : d.schwartz (.inr p)) : Glues (d.symbol (.inr p)) Φ.val :=
  d.schwartz_glues_of_transform _ (fun f hf =>
    transform_glues_of_radon_glues _ _ _ _ _ f (d.finite_radon_glues p hS hf.1)) Φ

end MetaplecticPoisson.Datum
