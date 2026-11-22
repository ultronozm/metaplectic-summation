import MetaplecticSummation.FiniteLeading

noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField IsDedekindDomain Filter
open scoped Topology
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

theorem exists_leading_arch (w : InfinitePlace F) :
    let v : Place F := .inl w
    ∃ b : d.schwartz v →ₗ[ℂ] Charts (LocalField F v), ∀ f : d.schwartz v,
      IsLeadingTerm n (modulus F v) f (b f) := by sorry

theorem exists_leading (v : Place F) :
    ∃ b : d.schwartz v →ₗ[ℂ] Charts (LocalField F v), ∀ f : d.schwartz v,
      IsLeadingTerm n (modulus F v) f (b f) := by
  cases v with
  | inl w => exact d.exists_leading_arch w
  | inr p => exact d.exists_leading_finite p

def leading (v : Place F) := (d.exists_leading v).choose

theorem leading_spec (v : Place F) (f : d.schwartz v) :
    IsLeadingTerm n (modulus F v) f (d.leading v f) :=
  (d.exists_leading v).choose_spec f

/-- At a finite place the canonical leading term of a test section vanishes. -/
theorem leading_finiteTest_eq_zero (p : HeightOneSpectrum (𝓞 F)) (f : d.schwartz (.inr p))
    (hf : f.val ∈ d.testSet (.inr p)) : d.leading (.inr p) f = 0 := by
  letI : NontriviallyNormedField (LocalField F (.inr p)) := FinitePlace.nontriviallyNormedCompletion p
  letI : NeBot (comap (fun u : (LocalField F (.inr p))ˣ => u.val) (𝓝 0)) := units_neBot_at_zero
  exact (d.leading_spec _ f).unique (finiteTest_zero_leading n (NeZero.ne n) _ hf.2)

/-- On the integral transform of a test section the canonical finite-place
leading term is the integral of its Radon slices at frequency zero. -/
theorem leading_finiteTest_transform (p : HeightOneSpectrum (𝓞 F)) {f : Charts (LocalField F (.inr p))}
    (hf : f ∈ d.testSet (.inr p)) :
    d.leading (.inr p) ⟨d.integralTransform (.inr p) f,
      Submodule.subset_span (Or.inr ⟨f,hf,rfl⟩)⟩ = d.radonLeading (.inr p) f := by
  letI : NontriviallyNormedField (LocalField F (.inr p)) := FinitePlace.nontriviallyNormedCompletion p
  letI : NeBot (comap (fun u : (LocalField F (.inr p))ˣ => u.val) (𝓝 0)) := units_neBot_at_zero
  exact (d.leading_spec _ _).unique (d.finiteTest_transform_leading p hf)

end MetaplecticPoisson.Datum
