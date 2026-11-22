import MetaplecticSummation.LocalCharacters
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

noncomputable section
namespace MetaplecticPoisson.Datum
open Classical
open NumberField IsDedekindDomain Filter
open scoped RestrictedProduct Topology
variable {F : Type} [Field F] [NumberField F]

theorem eventually_place_of_finite {P : Place F → Prop}
    (h : ∀ᶠ w in cofinite, P (.inr w)) : ∀ᶠ v in cofinite, P v := by
  apply eventually_cofinite.mpr
  apply ((Set.finite_range (Sum.inl : InfinitePlace F → Place F)).union
    ((eventually_cofinite.mp h).image Sum.inr)).subset
  rintro (w | w) hw
  · exact Or.inl ⟨w,rfl⟩
  · exact Or.inr ⟨w,hw,rfl⟩

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

theorem component_single_self (v : Place F) (x : LocalField F v) :
    component (singleAdele F v x) v = x := by
  cases v with
  | inl w => exact Pi.single_eq_same w x
  | inr p => exact Pi.single_eq_same (M := fun q : HeightOneSpectrum (𝓞 F) => q.adicCompletion F) p x

theorem singleAdele_mul (v : Place F) (x : LocalField F v) (a : Adeles F) :
    singleAdele F v x * a = singleAdele F v (x * component a v) := by
  cases v with
  | inl w =>
    change w.Completion at x
    apply Prod.ext _ (zero_mul _)
    funext j
    change Pi.single w x j * a.1 j = Pi.single w (x*a.1 w) j
    by_cases hj : j = w
    · subst j; simp only [Pi.single_eq_same]
    · simp only [Pi.single_eq_of_ne hj,zero_mul]
  | inr p => exact Prod.ext (zero_mul _) (RestrictedProduct.single_mul _ p x a.2).symm

theorem continuous_component (v : Place F) : Continuous (fun a : Adeles F => component a v) := by
  cases v with
  | inl w => exact (continuous_apply w).comp continuous_fst
  | inr p => exact (RestrictedProduct.continuous_eval p).comp continuous_snd

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

/-- A continuous adelic character is trivial on the entire local integer ring
at all but finitely many finite places. -/
theorem eventually_trivial_on_integers (ψ : Character F) :
    ∀ᶠ p : HeightOneSpectrum (𝓞 F) in cofinite, ∀ x : LocalField F (.inr p), ‖x‖ ≤ 1 →
      ψ.localValue F (.inr p) x = 1 := by
  let χ (p : HeightOneSpectrum (𝓞 F)) : AddChar (p.adicCompletionIntegers F) Circle :=
    { toFun := fun x => ψ.toChar (singleAdele F (.inr p) x.val)
      map_zero_eq_one' := (congrArg ψ.toChar (singleAdele_zero (F := F) (.inr p))).trans ψ.toChar.map_zero_eq_one
      map_add_eq_mul' := fun x y => by
        change ψ.toChar (singleAdele F (.inr p) (x.val+y.val)) = _
        exact (congrArg ψ.toChar (singleAdele_add (F := F) (.inr p) x.val y.val)).trans (ψ.toChar.map_add_eq_mul _ _) }
  let U := Circle.centeredArc (Real.pi / 2)
  have hU : U ∈ 𝓝 (1 : Circle) := (Circle.isOpen_centeredArc _).mem_nhds
    ⟨0, by simpa using half_pos Real.pi_pos, Circle.exp_zero⟩
  have eventuallyArc (z : (p : HeightOneSpectrum (𝓞 F)) → p.adicCompletionIntegers F) :
      ∀ᶠ p in cofinite, χ p (z p) ∈ U := by
    let a : Adeles F := (0, ⟨fun p => (z p).val, .of_forall (fun p => (z p).property)⟩)
    have hin : Tendsto (Sum.inr : HeightOneSpectrum (𝓞 F) → Place F) cofinite cofinite :=
      Function.Injective.tendsto_cofinite Sum.inr_injective
    have ht := (hasSum_singleAdele a).summable.tendsto_cofinite_zero.comp hin
    have hc := (ψ.continuous_toChar.tendsto 0).comp ht
    rw [AddChar.map_zero_eq_one] at hc
    exact hc hU
  let bad (p : HeightOneSpectrum (𝓞 F)) := ∃ x, χ p x ∉ U
  let z (p : HeightOneSpectrum (𝓞 F)) := if h : bad p then h.choose else 0
  filter_upwards [eventuallyArc z] with p hp
  have hall (x : p.adicCompletionIntegers F) : χ p x ∈ U := by
    by_contra hx
    have h : bad p := ⟨x,hx⟩
    exact h.choose_spec (by simpa only [z, dif_pos h] using hp)
  intro x hx
  have mem (u : p.adicCompletion F) (hu : ‖u‖ ≤ 1) : u ∈ p.adicCompletionIntegers F :=
    Valued.toNormedField.norm_le_one_iff.mp hu
  let a : p.adicCompletionIntegers F := ⟨x, mem x hx⟩
  have hχ : χ p a = 1 := Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two
    (fun k _ => by rw [← AddChar.map_nsmul_eq_pow]; exact hall (k • a))
  exact congrArg (fun t : Circle => (t : ℂ)) hχ

end MetaplecticPoisson.Datum
