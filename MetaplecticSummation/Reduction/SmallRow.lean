import MetaplecticSummation.Reduction.AdelicIwasawa
import MetaplecticSummation.Reduction.SecondCountable

/-! A uniform small rational row from the covolume-one adelic lattice. -/

noncomputable section
namespace MetaplecticPoisson
open Set NumberField IsDedekindDomain MeasureTheory GroundTheory.Global
open scoped MatrixGroups Pointwise ENNReal
open Classical
variable (F : Type) [Field F] [NumberField F]
local notation "A" => Adeles F
local notation "μ" => adeleMeasure F
local notation "D" => fundamentalSet F
local notation "ι" => (algebraMap F A)
local notation "L" => AdeleRing.principalSubgroup (𝓞 F) F
local notation "Λ" => AddSubgroup.prod L L
local notation "I" => integralFiniteAdeles (𝓞 F) F

private def rationalPair (q : F × F) : Λ :=
  ⟨(ι q.1,ι q.2),⟨q.1,rfl⟩,⟨q.2,rfl⟩⟩

private theorem rationalPair_surjective : Function.Surjective (rationalPair F) := by
  intro g
  obtain ⟨v,hv⟩ := g.property.1
  obtain ⟨w,hw⟩ := g.property.2
  exact ⟨(v,w),Subtype.ext (Prod.ext hv hw)⟩

private theorem fundamentalSquare :
    IsAddFundamentalDomain Λ (D ×ˢ D) ((μ).prod μ) := by
  have unique (x : A) : ∃! g : L, g.val+x ∈ D := by
    obtain ⟨a,ha,hu⟩ := existsUnique_sub_mem_fundamentalSet F x
    refine ⟨⟨ι (-a),-a,rfl⟩, ?_, ?_⟩
    · simpa [map_neg,sub_eq_add_neg,add_comm] using ha
    · rintro ⟨_,b,rfl⟩ hb
      have eqn : -b = a := hu _ (by simpa [map_neg,sub_neg_eq_add,add_comm] using hb)
      exact Subtype.ext (congrArg ι (by rw [← eqn,neg_neg]))
  apply IsAddFundamentalDomain.mk' ((measurableSet_fundamentalSet F).prod (measurableSet_fundamentalSet F)).nullMeasurableSet
  intro x
  obtain ⟨a,ha,ua⟩ := unique x.1
  obtain ⟨b,hb,ub⟩ := unique x.2
  refine ⟨⟨(a.val,b.val),a.property,b.property⟩,⟨ha,hb⟩,?_⟩
  intro g hg
  exact Subtype.ext (Prod.ext (congrArg Subtype.val (ua ⟨_,g.property.1⟩ hg.1))
    (congrArg Subtype.val (ub ⟨_,g.property.2⟩ hg.2)))

private theorem exists_compact_box :
    ∃ B : Set A, IsCompact B ∧ 1 < μ B ∧ ∀ x ∈ B, x.2 ∈ I := by
  let C : Set A := closure (fundamentalSetInfinite F) ×ˢ (I : Set _)
  have hC : IsCompact C := (isCompact_closure_fundamentalSetInfinite F).prod (isCompact_integralFiniteAdeles F)
  have hDC : D ⊆ C := fun x hx => ⟨subset_closure hx.1,hx.2⟩
  let B := C ∪ ((1:A) +ᵥ C)
  refine ⟨B,hC.union (hC.image (continuous_const_add _)),?_,?_⟩
  · have disj : Disjoint D ((1:A) +ᵥ D) := by
      apply Set.disjoint_left.mpr
      rintro x hx ⟨y,hy,rfl⟩
      have hu := existsUnique_sub_mem_fundamentalSet F (1+y)
      have eqn : (0 : F) = 1 := hu.unique (by simpa using hx) (by simpa [add_comm] using hy)
      exact zero_ne_one eqn
    have hmeas : MeasurableSet ((1:A) +ᵥ D) := (measurableSet_fundamentalSet F).const_vadd _
    have hsub : D ∪ ((1:A) +ᵥ D) ⊆ B := union_subset_union hDC (Set.image_mono hDC)
    apply lt_of_lt_of_le _ (measure_mono hsub)
    rw [measure_union disj hmeas,measure_vadd,adeleMeasure_fundamentalSet]
    norm_num
  · rintro x (hx | ⟨y,hy,rfl⟩)
    · exact hx.2
    · exact (I).add_mem (I).one_mem hy.2

/-- Row multiplication by an adelic upper triangular determinant-one matrix. -/
def triangularRow (u : A) (a : Aˣ) : A × A →+ A × A where
  toFun x := (a.val*x.1,(a⁻¹).val*(u*x.1+x.2))
  map_zero' := by simp
  map_add' x y := by
    apply Prod.ext <;> simp [mul_add]
    ring

theorem measurePreserving_triangularRow (u : A) (a : Aˣ) :
    MeasurePreserving (triangularRow F u a) ((μ).prod μ) ((μ).prod μ) := by
  let shear (x : A × A) := (x.1,u*x.1+x.2)
  have hs : MeasurePreserving shear ((μ).prod μ) ((μ).prod μ) :=
    (MeasurePreserving.id μ).skew_product
      (show Measurable (fun x : A × A => u*x.1+x.2) by fun_prop)
      (ae_of_all _ fun x => (measurePreserving_add_left μ (u*x)).map_eq)
  have hm : MeasurePreserving (Prod.map (fun x : A => a • x) (fun y : A => a⁻¹ • y)) ((μ).prod μ) ((μ).prod μ) := by
    refine ⟨(continuous_const_smul a).measurable.prodMap (continuous_const_smul a⁻¹).measurable,?_⟩
    rw [← Measure.map_prod_map _ _ (continuous_const_smul a).measurable (continuous_const_smul a⁻¹).measurable,
      map_smul_adeleMeasure,map_smul_adeleMeasure, Measure.prod_smul_left,Measure.prod_smul_right,smul_smul,
      ← ENNReal.ofReal_mul (inv_nonneg.mpr (IdeleGroup.ideleModule F a).property.le),map_inv,Positive.coe_inv,inv_inv,inv_mul_cancel₀,ENNReal.ofReal_one,one_smul]
    exact (IdeleGroup.ideleModule F a).property.ne'
  exact hm.comp hs

/-- A fixed compact archimedean box with integral finite components contains
the image of a nonzero rational row under every adelic upper triangular matrix of determinant one. -/
theorem exists_uniform_small_row :
    ∃ C : Set A, IsCompact C ∧ (∀ x ∈ C, x.2 ∈ I) ∧ ∀ (u : A) (a : Aˣ),
      ∃ v : F × F, v ≠ 0 ∧ triangularRow F u a (ι v.1,ι v.2) ∈ C ×ˢ C := by
  obtain ⟨B,hB,hvol,hint⟩ := exists_compact_box F
  have compact : IsCompact (B - B) := by
    have eqn : B - B = (fun z : A × A => z.1-z.2) '' (B ×ˢ B) := by
      ext
      simp [Set.mem_sub]
    rw [eqn]
    exact (hB.prod hB).image continuous_sub
  refine ⟨B - B,compact,?_,?_⟩
  · rintro _ ⟨x,hx,y,hy,rfl⟩
    exact (I).sub_mem (hint x hx) (hint y hy)
  intro u a
  let := countable_numberField F
  let : Countable Λ := (rationalPair_surjective F).countable
  let T := triangularRow F u a
  have hp := measurePreserving_triangularRow F u a
  have hm := hB.measurableSet.prod hB.measurableSet
  have hv : ((μ).prod μ) (D ×ˢ D) < ((μ).prod μ) (T ⁻¹' (B ×ˢ B)) := by
    rw [hp.measure_preimage hm.nullMeasurableSet,Measure.prod_prod,Measure.prod_prod,adeleMeasure_fundamentalSet,one_mul]
    exact one_lt_mul_of_lt_of_le hvol hvol.le
  obtain ⟨x,hx,y,hy,γ,hγ,he⟩ := (fundamentalSquare F).exists_ne_zero_vadd_eq ((hp.measurable hm).nullMeasurableSet) hv
  obtain ⟨⟨v,w⟩,rfl⟩ := rationalPair_surjective F γ
  refine ⟨(v,w),fun eqn => hγ (by rw [eqn]; apply Subtype.ext; exact Prod.ext (map_zero ι) (map_zero ι)),?_⟩
  have eqn : T (ι v,ι w) = T y - T x := by
    rw [← map_sub]
    apply congrArg T
    change (ι v,ι w) + x = y at he
    exact eq_sub_of_add_eq he
  change T (ι v,ι w) ∈ _
  rw [eqn]
  exact ⟨Set.sub_mem_sub hy.1 hx.1,Set.sub_mem_sub hy.2 hx.2⟩

end MetaplecticPoisson
