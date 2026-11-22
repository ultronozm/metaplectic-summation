import MetaplecticSummation.LocalCharacters

noncomputable section
namespace MetaplecticPoisson.Datum
open Classical
open NumberField IsDedekindDomain Filter
open scoped RestrictedProduct Topology
variable {F : Type} [Field F] [NumberField F]

def component (u : Adeles F) (v : Place F) : LocalField F v :=
  match v with
  | .inl w => u.1 w
  | .inr p => u.2 p

def componentHom (v : Place F) : Adeles F →+* LocalField F v where
  toFun u := component u v
  map_one' := by cases v <;> rfl
  map_zero' := by cases v <;> rfl
  map_add' _ _ := by cases v <;> rfl
  map_mul' _ _ := by cases v <;> rfl

private theorem component_single (x : Adeles F) (i v : Place F) :
    component (singleAdele F i (component x i)) v =
      if i = v then component x v else 0 := by
  classical
  rcases i with i|i <;> rcases v with v|v
  · by_cases h : i = v
    · subst v; simp [component,singleAdele]
    · simp [component,singleAdele,h]; rfl
  · exact rfl
  · exact rfl
  · by_cases h : i = v
    · subst v; rw [if_pos rfl]; exact Pi.single_eq_same (M := fun p : HeightOneSpectrum (𝓞 F) => p.adicCompletion F) i (x.2 i)
    · rw [if_neg (fun he => h (Sum.inr.inj he))]; exact Pi.single_eq_of_ne (Ne.symm h) _

/-- An adele is the convergent sum of its single-place components. -/
theorem hasSum_singleAdele (x : Adeles F) :
    HasSum (fun v => singleAdele F v (component x v)) x := by
  classical
  let P (s : Finset (Place F)) := ∑ i ∈ s, singleAdele F i (component x i)
  have hc (s : Finset (Place F)) (v : Place F) :
      component (P s) v = if v ∈ s then component x v else 0 := by
    change componentHom v (∑ i ∈ s, _) = _
    simp only [map_sum, componentHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,component_single]
    simp
  have ht (v : Place F) : Tendsto (fun s => component (P s) v) atTop (𝓝 (component x v)) := by
    apply tendsto_nhds_of_eventually_eq
    filter_upwards [eventually_ge_atTop ({v} : Finset (Place F))] with s hs
    rw [hc, if_pos (hs (Finset.mem_singleton_self v))]
  change Tendsto P atTop (𝓝 x)
  apply Filter.Tendsto.prodMk_nhds (tendsto_pi_nhds.mpr (fun w => ht (.inl w)))
  let U := {p : HeightOneSpectrum (𝓞 F) | x.2 p ∈ p.adicCompletionIntegers F}
  let stage := Πʳ p : HeightOneSpectrum (𝓞 F), [p.adicCompletion F, p.adicCompletionIntegers F]_[principal U]
  let z : stage := ⟨x.2.1, eventually_principal.mpr (fun _ h => h)⟩
  let trunc (s : Finset (Place F)) : stage := ⟨(P s).2.1, eventually_principal.mpr (by
    intro p hp
    change component (P s) (.inr p) ∈ p.adicCompletionIntegers F
    rw [hc]
    split_ifs
    · exact hp
    · exact zero_mem _)⟩
  have hs : Tendsto trunc atTop (𝓝 z) :=
    RestrictedProduct.isEmbedding_coe_of_principal.tendsto_nhds_iff.mpr
      (tendsto_pi_nhds.mpr (fun p => ht (.inr p)))
  exact ((RestrictedProduct.continuous_inclusion (le_principal_iff.mpr x.2.2)).tendsto z).comp hs

/-- Factorization of a continuous adelic character over all places, in
the topology of unconditional products. -/
theorem hasProd_localValue (ψ : Character F) (x : Adeles F) :
    HasProd (fun v => ψ.localValue F v (component x v)) (ψ.toChar x : ℂ) := by
  classical
  have ht := ((continuous_subtype_val.comp ψ.continuous_toChar).tendsto x).comp
    (hasSum_singleAdele x)
  have he (s : Finset (Place F)) :
      (ψ.toChar (∑ v ∈ s, singleAdele F v (component x v)) : ℂ) =
      ∏ v ∈ s, ψ.localValue F v (component x v) := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert v s hv ih =>
      simp only [Finset.sum_insert hv, Finset.prod_insert hv, AddChar.map_add_eq_mul,
        Circle.coe_mul, ih, Character.localValue]
  exact ht.congr he

end MetaplecticPoisson.Datum
