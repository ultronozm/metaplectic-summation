import MetaplecticSummation.FiniteHaar
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.FundamentalDomain

/-! The additive adelic lattice and its compact quotient. The approximation,
archimedean lattice, and fundamental-domain proofs are adapted from
GroundTheory.GlobalFields.Adele.{Approximation, IntegersLattice, Discrete, Compact}
and the extracted ExistsValuationSubLeOne proof used there. -/

noncomputable section
namespace MetaplecticPoisson.AdeleLattice

section Finite
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped RestrictedProduct

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]

theorem exists_valuation_sub_le_one (S : Finset (HeightOneSpectrum R))
    (x : HeightOneSpectrum R → K) :
    ∃ k : K, (∀ v ∈ S, v.valuation K (k - x v) ≤ 1) ∧ (∀ v ∉ S, v.valuation K k ≤ 1) := by
  classical
  obtain ⟨⟨d, hdm⟩, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors R) S x
  simp only at hd
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hdm
  have hdK : algebraMap R K d ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hdm
  have hr : ∀ v, ∃ r : R, v ∈ S → algebraMap R K r = algebraMap R K d * x v := by
    intro v
    by_cases hv : v ∈ S
    · obtain ⟨r, hr⟩ := hd v hv
      exact ⟨r, fun _ => by rw [hr, Algebra.smul_def]⟩
    · exact ⟨0, fun h => absurd h hv⟩
  choose r hr using hr
  have hI : Ideal.span {d} ≠ (0 : Ideal R) := by
    simpa using hd0
  let T : Finset (IsDedekindDomain.HeightOneSpectrum R) := S ∪ (Ideal.finite_factors hI).toFinset
  let e : IsDedekindDomain.HeightOneSpectrum R → ℕ := fun v =>
    (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {d} : Ideal R)).factors
  have he : ∀ v : IsDedekindDomain.HeightOneSpectrum R,
      v.intValuation d = WithZero.exp (-(e v : ℤ)) := fun v => v.intValuation_if_neg hd0
  have he0 : ∀ v, v ∉ T → e v = 0 := by
    intro v hv
    have hmem : d ∉ v.asIdeal := by
      intro h
      apply hv
      simp only [T, Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      exact Or.inr (Ideal.dvd_span_singleton.2 h)
    have h1 := IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.2 hmem
    rw [he, ← WithZero.exp_zero, WithZero.exp_inj] at h1
    omega
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := T)
    (fun v : IsDedekindDomain.HeightOneSpectrum R => v.asIdeal) e
    (fun v _ => v.prime)
    (fun v _ w _ hvw h => hvw (IsDedekindDomain.HeightOneSpectrum.ext h))
    (fun v => if v.1 ∈ S then r v.1 else 0)
  have key : ∀ (v : IsDedekindDomain.HeightOneSpectrum R) (a : R), a ∈ v.asIdeal ^ e v →
      v.valuation K (algebraMap R K a / algebraMap R K d) ≤ 1 := by
    intro v a ha
    rw [map_div₀, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, he]
    exact div_le_one_of_le₀ ((v.intValuation_le_pow_iff_mem a (e v)).2 ha) zero_le
  refine ⟨algebraMap R K y / algebraMap R K d, fun v hv => ?_, fun v hv => ?_⟩
  · have hvT : v ∈ T := Finset.mem_union_left _ hv
    have h1 := hy v hvT
    simp only [hv, if_true] at h1
    have h2 := key v _ h1
    have h3 : algebraMap R K (y - r v) / algebraMap R K d =
        algebraMap R K y / algebraMap R K d - x v := by
      rw [map_sub, hr v hv]
      field_simp
    rwa [h3] at h2
  · apply key
    by_cases hvT : v ∈ T
    · have h1 := hy v hvT
      simpa [hv] using h1
    · simp [he0 v hvT]

def integralFiniteAdeles (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] : Subring (FiniteAdeleRing R K) where
  carrier := {a | ∀ v : HeightOneSpectrum R, a v ∈ v.adicCompletionIntegers K}
  mul_mem' ha hb v := Subring.mul_mem _ (ha v) (hb v)
  one_mem' _ := Subring.one_mem _
  add_mem' ha hb v := Subring.add_mem _ (ha v) (hb v)
  zero_mem' _ := Subring.zero_mem _
  neg_mem' ha v := Subring.neg_mem _ (ha v)

theorem mem_integralFiniteAdeles {a : FiniteAdeleRing R K} :
    a ∈ integralFiniteAdeles R K ↔ ∀ v : HeightOneSpectrum R, a v ∈ v.adicCompletionIntegers K :=
  Iff.rfl

theorem isOpen_integralFiniteAdeles :
    IsOpen (integralFiniteAdeles R K : Set (FiniteAdeleRing R K)) :=
  RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum R => v.adicCompletion K)
    (A := fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
    (fun _ => Valued.isOpen_valuationSubring _)

theorem coe_mem_adicCompletionIntegers_iff (v : HeightOneSpectrum R) (k : K) :
    (k : v.adicCompletion K) ∈ v.adicCompletionIntegers K ↔ v.valuation K k ≤ 1 := by
  rw [mem_adicCompletionIntegers, valuedAdicCompletion_eq_valuation']

theorem exists_sub_mem_integralFiniteAdeles (a : FiniteAdeleRing R K) :
    ∃ k : K, a - algebraMap K (FiniteAdeleRing R K) k ∈ integralFiniteAdeles R K := by
  classical
  have hS : {v : HeightOneSpectrum R | a v ∉ v.adicCompletionIntegers K}.Finite :=
    Filter.eventually_cofinite.mp a.2
  have hx : ∀ v : HeightOneSpectrum R, ∃ z : K,
      a v - (z : v.adicCompletion K) ∈ v.adicCompletionIntegers K := by
    intro v
    have hU : IsOpen {w : v.adicCompletion K | a v - w ∈ v.adicCompletionIntegers K} :=
      (Valued.isOpen_valuationSubring (v.adicCompletion K)).preimage
        (continuous_const.sub continuous_id)
    obtain ⟨z, hz⟩ := (denseRange_algebraMap (K := K) v).exists_mem_open hU
      ⟨a v, by simp⟩
    exact ⟨z, hz⟩
  choose x hx using hx
  obtain ⟨k, hkS, hkn⟩ := exists_valuation_sub_le_one hS.toFinset x
  refine ⟨k, fun v => ?_⟩
  change a v - (k : v.adicCompletion K) ∈ v.adicCompletionIntegers K
  by_cases hv : v ∈ hS.toFinset
  · have h1 := (coe_mem_adicCompletionIntegers_iff v (k - x v)).mpr (hkS v hv)
    have h2 : a v - (k : v.adicCompletion K) =
        (a v - (x v : v.adicCompletion K)) - ((k - x v : K) : v.adicCompletion K) := by
      have hc : ∀ z : K, (z : v.adicCompletion K) = algebraMap K (v.adicCompletion K) z :=
        fun z => by simp [algebraMap_adicCompletion]
      rw [hc, hc, hc, map_sub]
      ring
    rw [h2]
    exact Subring.sub_mem _ (hx v) h1
  · have hav : a v ∈ v.adicCompletionIntegers K := by
      simpa using hv
    exact Subring.sub_mem _ hav ((coe_mem_adicCompletionIntegers_iff v k).mpr (hkn v hv))

end Finite

section Infinite
open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion

theorem discreteTopology_of_isOpen_of_forall_mem {G : Type*} [AddGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] (H : AddSubgroup G) (U : Set G) (hU : IsOpen U) (h0 : (0 : G) ∈ U)
    (hH : ∀ x ∈ H, x ∈ U → x = 0) : DiscreteTopology H := by
  rw [discreteTopology_iff_isOpen_singleton_zero]
  convert hU.preimage continuous_subtype_val
  ext ⟨x, hx⟩
  simp only [Set.mem_singleton_iff, Set.mem_preimage]
  constructor
  · intro h
    have hx0 : x = 0 := by simpa using congrArg Subtype.val h
    rw [hx0]
    exact h0
  · intro h
    exact Subtype.ext (hH x hx h)

variable (K : Type*) [Field K]

open scoped Classical in

noncomputable def homeomorphMixedSpace : (InfiniteAdeleRing K) ≃ₜ mixedEmbedding.mixedSpace K :=
  (Homeomorph.piEquivPiSubtypeProd (fun v : InfinitePlace K => IsReal v)
      (fun v => v.Completion)).trans
    (Homeomorph.prodCongr
      (Homeomorph.piCongrRight fun v => (isometryEquivRealOfIsReal v.2).toHomeomorph)
      ((Homeomorph.piCongrRight fun v =>
          (isometryEquivComplexOfIsComplex (not_isReal_iff_isComplex.1 v.2)).toHomeomorph).trans
        (Homeomorph.piCongrLeft (Y := fun _ => ℂ)
          (Equiv.subtypeEquivRight fun _ => not_isReal_iff_isComplex))))

theorem homeomorphMixedSpace_apply (x : (InfiniteAdeleRing K)) :
    homeomorphMixedSpace K x = InfiniteAdeleRing.ringEquiv_mixedSpace K x := rfl

theorem homeomorphMixedSpace_algebraMap (k : K) :
    homeomorphMixedSpace K (algebraMap K (InfiniteAdeleRing K) k) = mixedEmbedding K k := by
  rw [homeomorphMixedSpace_apply, InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]

theorem homeomorphMixedSpace_sub (x y : (InfiniteAdeleRing K)) :
    homeomorphMixedSpace K (x - y) = homeomorphMixedSpace K x - homeomorphMixedSpace K y := by
  simp only [homeomorphMixedSpace_apply, map_sub]

variable [NumberField K]

theorem eq_zero_of_forall_infinitePlace_lt_one (z : 𝓞 K) (h : ∀ w : InfinitePlace K, w z < 1) :
    z = 0 := by
  by_contra hz
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
  exact (one_le_of_lt_one hz fun w' _ => h w').not_gt (h w)

omit [NumberField K] in
theorem norm_algebraMap_apply (k : K) (w : InfinitePlace K) :
    ‖algebraMap K (InfiniteAdeleRing K) k w‖ = w k := by
  simp [InfiniteAdeleRing.algebraMap_apply, WithAbs.norm_toAbs_eq]
  rfl

open scoped Classical

noncomputable def fundamentalSetInfinite : Set (InfiniteAdeleRing K) :=
  homeomorphMixedSpace K ⁻¹' ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis K)

theorem isCompact_closure_fundamentalSetInfinite :
    IsCompact (closure (fundamentalSetInfinite K)) := by
  rw [fundamentalSetInfinite, ← Homeomorph.preimage_closure, Homeomorph.isCompact_preimage]
  exact (ZSpan.fundamentalDomain_isBounded _).isCompact_closure

theorem existsUnique_sub_mem_fundamentalSetInfinite (x : (InfiniteAdeleRing K)) :
    ∃! z : 𝓞 K, x - algebraMap (𝓞 K) (InfiniteAdeleRing K) z ∈ fundamentalSetInfinite K := by
  set b := mixedEmbedding.latticeBasis K
  have hmem : ∀ z : 𝓞 K, mixedEmbedding K (z : K) ∈ Submodule.span ℤ (Set.range b) := by
    intro z
    rw [mixedEmbedding.mem_span_latticeBasis]
    exact ⟨z, rfl⟩
  have himg : ∀ z : 𝓞 K, homeomorphMixedSpace K (x - algebraMap (𝓞 K) (InfiniteAdeleRing K) z) =
      homeomorphMixedSpace K x - mixedEmbedding K (z : K) := by
    intro z
    rw [homeomorphMixedSpace_sub, IsScalarTower.algebraMap_apply (𝓞 K) K (InfiniteAdeleRing K),
      homeomorphMixedSpace_algebraMap]
  have hinj : Function.Injective fun z : 𝓞 K => mixedEmbedding K (z : K) :=
    (mixedEmbedding K).injective.comp RingOfIntegers.coe_injective
  obtain ⟨z, hz⟩ : ∃ z : 𝓞 K, mixedEmbedding K (z : K) =
      (ZSpan.floor b (homeomorphMixedSpace K x) : mixedEmbedding.mixedSpace K) := by
    have := (ZSpan.floor b (homeomorphMixedSpace K x)).2
    rw [mixedEmbedding.mem_span_latticeBasis] at this
    obtain ⟨z, hz⟩ := this
    exact ⟨z, hz⟩
  refine ⟨z, ?_, fun z' hz' => ?_⟩
  · change homeomorphMixedSpace K (x - algebraMap (𝓞 K) (InfiniteAdeleRing K) z) ∈ ZSpan.fundamentalDomain b
    rw [himg, hz]
    exact ZSpan.fract_mem_fundamentalDomain b _
  · replace hz' : homeomorphMixedSpace K (x - algebraMap (𝓞 K) (InfiniteAdeleRing K) z') ∈
        ZSpan.fundamentalDomain b := hz'
    rw [himg] at hz'
    have h1 : homeomorphMixedSpace K x - mixedEmbedding K (z : K) ∈ ZSpan.fundamentalDomain b := by
      rw [hz]
      exact ZSpan.fract_mem_fundamentalDomain b _
    rw [← ZSpan.fract_eq_self] at h1 hz'
    have heq : ZSpan.fract b (homeomorphMixedSpace K x - mixedEmbedding K (z' : K)) =
        ZSpan.fract b (homeomorphMixedSpace K x - mixedEmbedding K (z : K)) := by
      rw [ZSpan.fract_eq_fract]
      have : -(homeomorphMixedSpace K x - mixedEmbedding K (z' : K)) +
          (homeomorphMixedSpace K x - mixedEmbedding K (z : K)) =
          mixedEmbedding K (z' : K) - mixedEmbedding K (z : K) := by abel
      rw [this]
      exact Submodule.sub_mem _ (hmem z') (hmem z)
    rw [hz', h1] at heq
    exact hinj (sub_right_injective heq)

end Infinite

open NumberField IsDedekindDomain

variable (K : Type*) [Field K] [NumberField K]
open scoped RestrictedProduct

local instance : T2Space (AdeleRing (𝓞 K) K) := by
  letI : T2Space (FiniteAdeleRing (𝓞 K) K) := inferInstanceAs (T2Space
    (Πʳ v : HeightOneSpectrum (𝓞 K), [v.adicCompletion K, v.adicCompletionIntegers K]))
  letI : T2Space (InfiniteAdeleRing K) := inferInstanceAs (T2Space ((v : InfinitePlace K) → v.Completion))
  exact inferInstanceAs (T2Space (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K))

theorem exists_eq_of_forall_mem_adicCompletionIntegers (k : K)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), (k : v.adicCompletion K) ∈ v.adicCompletionIntegers K) :
    ∃ z : 𝓞 K, (z : K) = k := by
  have hv : ∀ v : HeightOneSpectrum (𝓞 K), v.valuation K k ≤ 1 := fun v =>
    (coe_mem_adicCompletionIntegers_iff v k).mp (h v)
  obtain ⟨z, hz⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K k hv
  exact ⟨z, hz⟩

theorem algebraMap_integers_mem_integralFiniteAdeles (z : 𝓞 K) :
    algebraMap K (FiniteAdeleRing (𝓞 K) K) (z : K) ∈ integralFiniteAdeles (𝓞 K) K := fun v =>
  (coe_mem_adicCompletionIntegers_iff v (z : K)).mpr (HeightOneSpectrum.valuation_le_one v z)

theorem discreteTopology_principalSubgroup :
    DiscreteTopology (AdeleRing.principalSubgroup (𝓞 K) K) := by
  refine discreteTopology_of_isOpen_of_forall_mem _
    ({x : (InfiniteAdeleRing K) | ∀ w, ‖x w‖ < 1} ×ˢ (integralFiniteAdeles (𝓞 K) K : Set (FiniteAdeleRing (𝓞 K) K)))
    ?_ ⟨fun w => by
      show ‖(0 : (InfiniteAdeleRing K)) w‖ < 1
      rw [show (0 : (InfiniteAdeleRing K)) w = 0 from rfl, norm_zero]; exact one_pos,
      Subring.zero_mem _⟩ ?_
  · refine IsOpen.prod ?_ isOpen_integralFiniteAdeles
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun w =>
      isOpen_lt (continuous_apply (A := fun w : InfinitePlace K => w.Completion) w).norm
        continuous_const
  · rintro _ ⟨k, rfl⟩ ⟨hinf, hf⟩
    obtain ⟨z, rfl⟩ := exists_eq_of_forall_mem_adicCompletionIntegers K k hf
    have hz : ∀ w : InfinitePlace K, w z < 1 := fun w => by
      have := hinf w
      rwa [show (algebraMap K (AdeleRing (𝓞 K) K) (z : K)).1 = algebraMap K (InfiniteAdeleRing K) (z : K) from rfl,
        norm_algebraMap_apply] at this
    rw [eq_zero_of_forall_infinitePlace_lt_one K z hz]
    simp

theorem isClosed_principalSubgroup :
    IsClosed (AdeleRing.principalSubgroup (𝓞 K) K : Set (AdeleRing (𝓞 K) K)) :=
  haveI := discreteTopology_principalSubgroup K
  AddSubgroup.isClosed_of_discrete

noncomputable def fundamentalSet : Set (AdeleRing (𝓞 K) K) :=
  fundamentalSetInfinite K ×ˢ (integralFiniteAdeles (𝓞 K) K : Set (FiniteAdeleRing (𝓞 K) K))

theorem existsUnique_sub_mem_fundamentalSet (x : (AdeleRing (𝓞 K) K)) :
    ∃! k : K, x - algebraMap K (AdeleRing (𝓞 K) K) k ∈ fundamentalSet K := by
  obtain ⟨k₁, hk₁⟩ := exists_sub_mem_integralFiniteAdeles x.2
  obtain ⟨z, hz, -⟩ := existsUnique_sub_mem_fundamentalSetInfinite K (x.1 - algebraMap K (InfiniteAdeleRing K) k₁)
  refine ⟨k₁ + z, ⟨?_, ?_⟩, fun k hk => ?_⟩
  · change x.1 - algebraMap K (InfiniteAdeleRing K) (k₁ + z) ∈ _
    rw [map_add, ← sub_sub, ← IsScalarTower.algebraMap_apply]
    exact hz
  · change x.2 - algebraMap K (FiniteAdeleRing (𝓞 K) K) (k₁ + z) ∈ _
    rw [map_add, ← sub_sub]
    exact Subring.sub_mem _ hk₁ (algebraMap_integers_mem_integralFiniteAdeles K z)
  · obtain ⟨hkinf, hkf⟩ := hk
    change x.1 - algebraMap K (InfiniteAdeleRing K) k ∈ fundamentalSetInfinite K at hkinf
    change x.2 - algebraMap K (FiniteAdeleRing (𝓞 K) K) k ∈ integralFiniteAdeles (𝓞 K) K at hkf

    have hdiff : algebraMap K (FiniteAdeleRing (𝓞 K) K) (k - (k₁ + z)) ∈
        integralFiniteAdeles (𝓞 K) K := by
      have h2 := Subring.sub_mem _ (Subring.sub_mem _ hk₁ hkf)
        (algebraMap_integers_mem_integralFiniteAdeles K z)
      convert h2 using 1
      simp only [map_sub, map_add]
      abel
    obtain ⟨u, hu⟩ := exists_eq_of_forall_mem_adicCompletionIntegers K _ hdiff
    have h1 : z + u = z := by
      refine (existsUnique_sub_mem_fundamentalSetInfinite K (x.1 - algebraMap K (InfiniteAdeleRing K) k₁)).unique
        ?_ hz
      convert hkinf using 1
      have hu' : algebraMap (𝓞 K) K u = k - (k₁ + algebraMap (𝓞 K) K z) := hu
      rw [IsScalarTower.algebraMap_apply (𝓞 K) K (InfiniteAdeleRing K), map_add, hu']
      simp only [map_sub, map_add]
      abel
    have hu0 : u = 0 := by simpa using h1
    rw [hu0] at hu
    have : k - (k₁ + z) = 0 := by rw [← hu]; simp
    exact sub_eq_zero.mp this


/-- The finite integral conditions and the archimedean parallelotope give an
additive fundamental domain for the Borel action of the principal adeles. -/
theorem isAddFundamentalDomain [MeasurableSpace (AdeleRing (𝓞 K) K)]
    [OpensMeasurableSpace (AdeleRing (𝓞 K) K)] (μ : MeasureTheory.Measure (AdeleRing (𝓞 K) K)) :
    MeasureTheory.IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 K) K) (fundamentalSet K) μ := by
  classical
  have hc : Continuous (fun x : AdeleRing (𝓞 K) K => homeomorphMixedSpace K x.1) :=
    (homeomorphMixedSpace K).continuous.comp continuous_fst
  have hi : IsOpen (Prod.snd ⁻¹' (integralFiniteAdeles (𝓞 K) K : Set (FiniteAdeleRing (𝓞 K) K)) :
      Set (AdeleRing (𝓞 K) K)) := isOpen_integralFiniteAdeles.preimage continuous_snd
  have hm : MeasurableSet (fundamentalSet K) := by
    change MeasurableSet (((fun x : AdeleRing (𝓞 K) K => homeomorphMixedSpace K x.1) ⁻¹'
      ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis K)) ∩ (Prod.snd ⁻¹' _))
    exact ((ZSpan.fundamentalDomain_measurableSet (mixedEmbedding.latticeBasis K)).preimage hc.measurable).inter hi.measurableSet
  apply MeasureTheory.IsAddFundamentalDomain.mk' hm.nullMeasurableSet
  intro x
  obtain ⟨k,hk,huniq⟩ := existsUnique_sub_mem_fundamentalSet K x
  refine ⟨⟨algebraMap K _ (-k), -k, rfl⟩,?_,?_⟩
  · change algebraMap K _ (-k) + x ∈ _
    simpa only [map_neg,sub_eq_neg_add] using hk
  · rintro ⟨_, t, rfl⟩ ht
    have h : -t = k := huniq (-t) (by
      change algebraMap K _ t + x ∈ _ at ht
      simpa only [map_neg,sub_neg_eq_add,add_comm] using ht)
    exact Subtype.ext (congrArg (algebraMap K _) (neg_eq_iff_eq_neg.mp h))

theorem exists_isCompact_forall_exists_sub_mem :
    ∃ C : Set (InfiniteAdeleRing K), IsCompact C ∧ ∀ x : (AdeleRing (𝓞 K) K), ∃ k : K, x - algebraMap K (AdeleRing (𝓞 K) K) k ∈
      C ×ˢ (integralFiniteAdeles (𝓞 K) K : Set (FiniteAdeleRing (𝓞 K) K)) := by
  refine ⟨closure (fundamentalSetInfinite K), isCompact_closure_fundamentalSetInfinite K,
    fun x => ?_⟩
  obtain ⟨k, ⟨hinf, hf⟩, -⟩ := existsUnique_sub_mem_fundamentalSet K x
  exact ⟨k, subset_closure hinf, hf⟩

theorem isCompact_integralFiniteAdeles :
    IsCompact (integralFiniteAdeles (𝓞 K) K : Set (FiniteAdeleRing (𝓞 K) K)) := by
  have : ∀ v : HeightOneSpectrum (𝓞 K),
      CompactSpace ((v.adicCompletionIntegers K : Set (v.adicCompletion K))) := fun v =>
    isCompact_iff_compactSpace.1 (FinitePlace.isCompact_adicCompletionIntegers v)
  have hcont := (RestrictedProduct.isEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
    (A := fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
    (𝓕 := Filter.cofinite)).continuous
  have h := isCompact_range hcont
  rw [RestrictedProduct.range_structureMap] at h
  exact h

abbrev Quotient : Type _ := (AdeleRing (𝓞 K) K) ⧸ AdeleRing.principalSubgroup (𝓞 K) K

instance : IsClosed (AdeleRing.principalSubgroup (𝓞 K) K : Set (AdeleRing (𝓞 K) K)) :=
  isClosed_principalSubgroup K

instance compactSpace_adeleQuotient : CompactSpace (Quotient K) := by
  obtain ⟨C, hC, hx⟩ := exists_isCompact_forall_exists_sub_mem K
  have hD : IsCompact (C ×ˢ (integralFiniteAdeles (𝓞 K) K : Set (FiniteAdeleRing (𝓞 K) K)) :
      Set (AdeleRing (𝓞 K) K)) := hC.prod (isCompact_integralFiniteAdeles K)
  refine ⟨?_⟩
  convert hD.image (QuotientAddGroup.continuous_mk (N := AdeleRing.principalSubgroup (𝓞 K) K))
  refine (Set.eq_univ_of_forall fun q => ?_).symm
  induction q using QuotientAddGroup.induction_on with
  | H x =>
    obtain ⟨k, hk⟩ := hx x
    refine ⟨x - algebraMap K (AdeleRing (𝓞 K) K) k, hk, ?_⟩
    rw [QuotientAddGroup.eq]
    exact ⟨k, by simp⟩

instance t2Space_adeleQuotient : T2Space (Quotient K) := inferInstance


end MetaplecticPoisson.AdeleLattice
