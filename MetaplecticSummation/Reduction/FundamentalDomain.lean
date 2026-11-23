import MetaplecticSummation.RationalOrbits
import GroundTheory.GlobalFields.TateThesis.AdeleMeasure
import Mathlib.Topology.Covering.Quotient
import Mathlib.MeasureTheory.Measure.Haar.Quotient

/-! Discreteness of rational matrices and a Borel fundamental domain for adelic SL₂. -/
noncomputable section
namespace MetaplecticPoisson
open NumberField IsDedekindDomain Set MeasureTheory Topology
open scoped MatrixGroups Pointwise
open Classical
variable (F : Type) [Field F] [NumberField F]
abbrev AdelicSL := SL(2, Adeles F)
abbrev rationalSLMap : SL(2,F) →* AdelicSL F := Matrix.SpecialLinearGroup.map (algebraMap F (Adeles F))
abbrev rationalSL := (rationalSLMap F).range

theorem sigmaCompactAdeles : SigmaCompactSpace (Adeles F) := by
  let := GroundTheory.Global.countable_numberField F
  obtain ⟨C,hC,h⟩ := GroundTheory.Global.exists_isCompact_forall_exists_sub_mem F
  let D : Set (Adeles F) := C ×ˢ (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set _)
  have hc : IsCompact D := hC.prod (GroundTheory.Global.isCompact_integralFiniteAdeles F)
  let S (t : F) : Set (Adeles F) := (fun x => x + algebraMap F (Adeles F) t) '' D
  have cov : (⋃ t, S t) = univ := eq_univ_of_forall fun x => by
    obtain ⟨t,ht⟩ := h x
    exact mem_iUnion.mpr ⟨t,_,ht,sub_add_cancel _ _⟩
  apply isSigmaCompact_univ_iff.mp
  rw [← cov]
  exact isSigmaCompact_iUnion _ fun t => (hc.image (continuous_add_const _)).isSigmaCompact

instance : SigmaCompactSpace (AdelicSL F) := by
  let := sigmaCompactAdeles F
  let : SigmaCompactSpace (Matrix (Fin 2) (Fin 2) (Adeles F)) := inferInstanceAs (SigmaCompactSpace (Fin 2 → Fin 2 → Adeles F))
  exact Matrix.SpecialLinearGroup.isClosedEmbedding_val.sigmaCompactSpace
instance : LocallyCompactSpace (AdelicSL F) := by
  let : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) (Adeles F)) := inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → Adeles F))
  exact Matrix.SpecialLinearGroup.isClosedEmbedding_val.locallyCompactSpace
instance : MeasurableSpace (AdelicSL F) := borel _
instance : BorelSpace (AdelicSL F) := ⟨rfl⟩

theorem rationalSLMap_injective : Function.Injective (rationalSLMap F) := by
  intro A B h
  apply Subtype.ext
  ext i j
  exact (algebraMap F (Adeles F)).injective (congrArg (fun g : AdelicSL F => g.val i j) h)

instance : Countable SL(2,F) := by
  let := GroundTheory.Global.countable_numberField F
  let : Countable (Matrix (Fin 2) (Fin 2) F) := inferInstanceAs (Countable (Fin 2 → Fin 2 → F))
  exact (Subtype.val_injective (p := fun A : Matrix (Fin 2) (Fin 2) F => A.det = 1)).countable

instance : Countable (rationalSL F) := (rationalSLMap F).rangeRestrict_surjective.countable

instance : DiscreteTopology (rationalSL F) := by
  let P := AdeleRing.principalSubgroup (𝓞 F) F
  let : DiscreteTopology P := GroundTheory.Global.discreteTopology_principalSubgroup F
  have entries (g : rationalSL F) (i j : Fin 2) : g.val.val i j ∈ P := by
    obtain ⟨g,A,rfl⟩ := g
    exact ⟨A.val i j,rfl⟩
  let e (g : rationalSL F) (i j : Fin 2) : P := ⟨g.val.val i j,entries g i j⟩
  apply DiscreteTopology.of_continuous_injective (f := e)
  · apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    apply Continuous.subtype_mk
    change Continuous (fun g : rationalSL F => g.val.val i j)
    fun_prop
  · intro a b h
    exact Subtype.ext (Subtype.ext (funext fun i => funext fun j => congrArg Subtype.val (congrFun (congrFun h i) j)))

/-- A discrete subgroup acting on the left of a Lindelöf group has a Borel domain
that meets every orbit in exactly one point. -/
theorem exists_rightCoset_domain {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LindelofSpace G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G) [DiscreteTopology H] :
    ∃ D : Set G, MeasurableSet D ∧ ∀ x : G, ∃! h : H, h.val*x ∈ D := by
  let Q := Quotient (QuotientGroup.rightRel H)
  let π : G → Q := Quotient.mk _
  have hπ : IsQuotientMap π := isQuotientMap_quotient_mk'
  have hdisc : IsDiscrete (H : Set G) := SetLike.isDiscrete_iff_discreteTopology.mpr inferInstance
  have loc := (hπ.isQuotientCoveringMap_of_subgroup H hdisc (fun {_ _} => Quotient.eq''.trans QuotientGroup.rightRel_apply)).isLocalHomeomorph
  choose e hx he using loc
  have hcov : (univ : Set G) ⊆ ⋃ x, (e x).source := fun x _ => mem_iUnion.mpr ⟨x,hx x⟩
  obtain ⟨T,hT,hcov⟩ := isLindelof_univ.elim_countable_subcover _ (fun x => (e x).open_source) hcov
  have cover (x : G) : ∃ t ∈ T, x ∈ (e t).source := by simpa only [mem_iUnion,exists_prop] using hcov (mem_univ x)
  obtain ⟨t,ht,_⟩ := cover 1
  obtain ⟨k,hk⟩ := hT.exists_eq_range ⟨t,ht⟩
  let U (i : ℕ) := (e (k i)).target
  let V := disjointed U
  have hits (x : G) : ∃ i, π x ∈ V i := by
    obtain ⟨s,hs,hx⟩ := cover x
    obtain ⟨i,rfl⟩ := hk ▸ hs
    apply mem_iUnion.mp
    rw [show (⋃ i, V i) = ⋃ i, U i from iUnion_disjointed]
    exact mem_iUnion.mpr ⟨i,by rw [he]; exact (e (k i)).map_source hx⟩
  let D := ⋃ i, (e (k i)).source ∩ π ⁻¹' V i
  let : MeasurableSpace Q := borel _
  let : BorelSpace Q := ⟨rfl⟩
  refine ⟨D,MeasurableSet.iUnion (fun i => (e (k i)).open_source.measurableSet.inter
    (hπ.continuous.measurable ((MeasurableSet.disjointed (fun j => (e (k j)).open_target.measurableSet)) i))),?_⟩
  intro x
  obtain ⟨i,hi⟩ := hits x
  have hu : π x ∈ (e (k i)).target := disjointed_le U i hi
  let y := (e (k i)).symm (π x)
  have hy : y ∈ (e (k i)).source := (e (k i)).map_target hu
  have eqn : π y = π x := (congrFun (he (k i)) y).trans ((e (k i)).right_inv hu)
  have hom : y*x⁻¹ ∈ H := QuotientGroup.rightRel_apply.mp (Quotient.exact eqn.symm)
  let h : H := ⟨y*x⁻¹,hom⟩
  have act : h.val*x = y := inv_mul_cancel_right _ _
  refine ⟨h,?_,?_⟩
  · change h.val*x ∈ D
    rw [act]
    exact mem_iUnion.mpr ⟨i,hy,(show π y ∈ V i from eqn.symm ▸ hi)⟩
  intro s hs
  have hsπ : π (s.val*x) = π x := Quotient.sound (QuotientGroup.rightRel_apply.mpr (by simp))
  obtain ⟨j,hj,hj'⟩ := mem_iUnion.mp hs
  have hij : i = j := by
    by_contra hn
    exact Set.disjoint_left.mp (disjoint_disjointed U hn) hi (hsπ ▸ hj')
  subst j
  have equal : s.val*x = y := (e (k i)).injOn hj hy (by rw [← he]; exact hsπ.trans eqn.symm)
  exact Subtype.ext (mul_right_cancel (equal.trans act.symm))

/-- A Borel fundamental set for the rational left action on adelic SL₂. -/
theorem exists_rationalSL_domain :
    ∃ D : Set (AdelicSL F), MeasurableSet D ∧ ∀ x, ∃! γ : SL(2,F), rationalSLMap F γ * x ∈ D := by
  obtain ⟨D,hD,hs⟩ := exists_rightCoset_domain (rationalSL F)
  refine ⟨D,hD,fun x => ?_⟩
  obtain ⟨⟨_,γ,rfl⟩,hit,uniq⟩ := hs x
  exact ⟨γ,hit,fun g hg => rationalSLMap_injective F (congrArg Subtype.val (uniq ((rationalSLMap F).rangeRestrict g) hg))⟩

end MetaplecticPoisson
