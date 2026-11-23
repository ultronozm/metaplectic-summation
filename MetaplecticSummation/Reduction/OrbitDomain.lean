import MetaplecticSummation.Reduction.FundamentalDomain

/-! A fundamental set for the rational unipotent obtained by translating a fundamental set for SL₂(F). -/
noncomputable section
namespace MetaplecticPoisson
open MeasureTheory Set Topology NumberField
open scoped MatrixGroups Pointwise
open Classical
variable (F : Type) [Field F] [NumberField F]
local notation "G" => AdelicSL F
local notation "Γ" => SL(2,F)
local notation "ι" => rationalSLMap F
abbrev RationalCosets := Quotient (QuotientGroup.rightRel (upperUnipotent F))

def rationalSLDomain : Set G := (exists_rationalSL_domain F).choose
theorem measurableSet_rationalSLDomain : MeasurableSet (rationalSLDomain F) :=
  (exists_rationalSL_domain F).choose_spec.1
theorem rationalSLDomain_unique (x : G) : ∃! γ : Γ, ι γ * x ∈ rationalSLDomain F :=
  (exists_rationalSL_domain F).choose_spec.2 x

def unipotentDomainPiece (q : RationalCosets F) : Set G := ι q.out • rationalSLDomain F
def rationalUnipotentDomain : Set G := ⋃ q, unipotentDomainPiece F q

theorem measurableSet_unipotentDomainPiece (q : RationalCosets F) : MeasurableSet (unipotentDomainPiece F q) :=
  (measurableSet_rationalSLDomain F).const_smul _

theorem measurableSet_rationalUnipotentDomain : MeasurableSet (rationalUnipotentDomain F) :=
  MeasurableSet.iUnion (measurableSet_unipotentDomainPiece F)

private theorem mem_piece (q : RationalCosets F) (x : G) :
    x ∈ unipotentDomainPiece F q ↔ ι q.out⁻¹ * x ∈ rationalSLDomain F := by
  rw [unipotentDomainPiece,mem_smul_set_iff_inv_smul_mem,map_inv]
  rfl

theorem disjoint_unipotentDomainPiece : Pairwise (Function.onFun Disjoint (unipotentDomainPiece F)) := by
  intro a b h
  apply disjoint_left.mpr
  intro x ha hb
  have eqn := (rationalSLDomain_unique F x).unique ((mem_piece F a x).mp ha) ((mem_piece F b x).mp hb)
  exact h ((Quotient.out_eq a).symm.trans ((congrArg (Quotient.mk _) (inv_injective eqn)).trans (Quotient.out_eq b)))

theorem rationalUnipotentDomain_unique (x : G) :
    ∃! h : upperUnipotent F, ι h.val * x ∈ rationalUnipotentDomain F := by
  obtain ⟨γ,hγ,uniq⟩ := rationalSLDomain_unique F x
  let q : RationalCosets F := Quotient.mk _ γ⁻¹
  have rel : q.out * γ ∈ upperUnipotent F := by
    have eqn : (Quotient.mk _ γ⁻¹ : RationalCosets F) = Quotient.mk _ q.out := (Quotient.out_eq q).symm
    simpa using QuotientGroup.rightRel_apply.mp (Quotient.exact eqn)
  refine ⟨⟨q.out*γ,rel⟩,?_,?_⟩
  · apply mem_iUnion.mpr
    refine ⟨q,(mem_piece F _ _).mpr ?_⟩
    simpa only [map_mul,map_inv,← mul_assoc,inv_mul_cancel,one_mul] using hγ
  · intro h hh
    obtain ⟨p,hp⟩ := mem_iUnion.mp hh
    have E : p.out⁻¹*h.val = γ := uniq _ (by
      simpa only [map_mul,map_inv,mul_assoc] using (mem_piece F p _).mp hp)
    have hpq : p = q := by
      apply (Quotient.out_eq p).symm.trans
      apply Quotient.sound
      apply QuotientGroup.rightRel_apply.mpr
      change γ⁻¹*p.out⁻¹ ∈ upperUnipotent F
      rw [← E,mul_inv_rev,inv_inv,mul_inv_cancel_right]
      exact h⁻¹.property
    subst p
    apply Subtype.ext
    change h.val = q.out*γ
    rw [← E,mul_inv_cancel_left]

abbrev rationalUnipotents := (upperUnipotent F).map (rationalSLMap F)

instance : Countable (rationalUnipotents F) :=
  ((upperUnipotent F).equivMapOfInjective (rationalSLMap F) (rationalSLMap_injective F)).surjective.countable

theorem isFundamentalDomain_rationalSL (μ : Measure G) :
    IsFundamentalDomain (rationalSL F) (rationalSLDomain F) μ := by
  apply IsFundamentalDomain.mk' (measurableSet_rationalSLDomain F).nullMeasurableSet
  intro x
  obtain ⟨γ, hγ, hu⟩ := rationalSLDomain_unique F x
  refine ⟨(rationalSLMap F).rangeRestrict γ, hγ, ?_⟩
  rintro ⟨_, g, rfl⟩ hg
  exact congrArg (rationalSLMap F).rangeRestrict (hu g hg)

theorem isFundamentalDomain_rationalUnipotents (μ : Measure G) :
    IsFundamentalDomain (rationalUnipotents F) (rationalUnipotentDomain F) μ := by
  apply IsFundamentalDomain.mk' (measurableSet_rationalUnipotentDomain F).nullMeasurableSet
  intro x
  obtain ⟨h, hh, hu⟩ := rationalUnipotentDomain_unique F x
  let i := (upperUnipotent F).equivMapOfInjective (rationalSLMap F) (rationalSLMap_injective F)
  exact ⟨i h, hh, fun a ha => by
    obtain ⟨b, rfl⟩ := i.surjective a
    exact congrArg i (hu b ha)⟩

private theorem projection_mul {H : Subgroup G} (h : H) (x : G) :
    Quotient.mk (QuotientGroup.rightRel H) (h.val * x) = Quotient.mk _ x := by
  apply Quotient.sound
  exact QuotientGroup.rightRel_apply.mpr (by simp)

/-- The quotient measure is independent of the fundamental domain for the rational subgroup. -/
theorem rightCoset_map_restrict_eq {H : Subgroup G} [Countable H] {μ : Measure G}
    [μ.IsMulLeftInvariant] {s t : Set G} (hs : IsFundamentalDomain H s μ)
    (ht : IsFundamentalDomain H t μ) :
    (μ.restrict s).map (Quotient.mk (QuotientGroup.rightRel H)) =
      (μ.restrict t).map (Quotient.mk (QuotientGroup.rightRel H)) := by
  ext A hA
  have hm := measurable_quotient_mk'' hA
  rw [Measure.map_apply measurable_quotient_mk'' hA, Measure.map_apply measurable_quotient_mk'' hA,
    Measure.restrict_apply hm, Measure.restrict_apply hm]
  apply hs.measure_set_eq ht hm
  intro h
  ext x
  change (Quotient.mk (QuotientGroup.rightRel H) (h.val * x) ∈ A) ↔ _
  rw [projection_mul]
  rfl

end MetaplecticPoisson
