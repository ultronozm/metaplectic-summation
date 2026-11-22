import MetaplecticSummation.Places

/-! Restriction of the adelic additive character to one completion. The
finite-place continuity argument uses the restricted-product inclusion as
in GroundTheory.GlobalFields.TateThesis.AdelicCharLocal. -/

noncomputable section
namespace MetaplecticPoisson
open NumberField IsDedekindDomain Filter
open scoped RestrictedProduct
variable {F : Type} [Field F] [NumberField F]

theorem continuous_singleAdele (v : Place F) : Continuous (singleAdele F v) := by
  classical
  cases v with
  | inl w =>
    exact (continuous_single (A := fun u : InfinitePlace F => u.Completion) w).prodMk continuous_const
  | inr p =>
    have hS : cofinite ≤ principal ({p}ᶜ : Set (HeightOneSpectrum (𝓞 F))) := by simp
    let g : p.adicCompletion F → Πʳ q : HeightOneSpectrum (𝓞 F),
        [q.adicCompletion F, q.adicCompletionIntegers F]_[principal {p}ᶜ] := fun x =>
      ⟨Pi.single p x, eventually_principal.mpr fun q hq => by
        rw [Pi.single_eq_of_ne hq x]
        exact zero_mem _⟩
    have hg : Continuous g := RestrictedProduct.continuous_rng_of_principal.mpr (continuous_single p)
    exact continuous_const.prodMk ((RestrictedProduct.continuous_inclusion hS).comp hg)

theorem singleAdele_add (v : Place F) (x y : LocalField F v) :
    singleAdele F v (x+y) = singleAdele F v x + singleAdele F v y := by
  classical
  cases v with
  | inl w =>
    exact Prod.ext (Pi.single_add (f := fun u : InfinitePlace F => u.Completion) w x y)
      (zero_add _).symm
  | inr p =>
    exact Prod.ext (zero_add _).symm (Subtype.ext
      (Pi.single_add (f := fun u : HeightOneSpectrum (𝓞 F) => u.adicCompletion F) p x y))

@[simp] theorem singleAdele_zero (v : Place F) : singleAdele F v 0 = 0 := by
  simpa using (singleAdele_add v 0 0).symm

theorem Character.continuous_localValue (ψ : Character F) (v : Place F) :
    Continuous (ψ.localValue F v) :=
  continuous_subtype_val.comp (ψ.continuous_toChar.comp (continuous_singleAdele v))

@[simp] theorem Character.localValue_zero (ψ : Character F) (v : Place F) :
    ψ.localValue F v 0 = 1 := by simp [Character.localValue]

theorem Character.localValue_add (ψ : Character F) (v : Place F) (x y : LocalField F v) :
    ψ.localValue F v (x+y) = ψ.localValue F v x * ψ.localValue F v y := by
  simp [Character.localValue, singleAdele_add, AddChar.map_add_eq_mul]

@[simp] theorem Character.norm_localValue (ψ : Character F) (v : Place F) (x : LocalField F v) :
    ‖ψ.localValue F v x‖ = 1 := Circle.norm_coe _

end MetaplecticPoisson
