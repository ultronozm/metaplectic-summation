import MetaplecticSummation.TamePowerClassFourier
import ClassFieldTheory.AlgebraicNumberTheory.Idele.SufficientlyLarge
import ClassFieldTheory.AlgebraicNumberTheory.Idele.SinglePlace

/-! A finite set of places detecting the orthogonal complement on integral-unit classes. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField IsDedekindDomain Filter
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

/-- A rational uniformizer at p that is a unit away from p and the fixed
finite support for the ideal class group. -/
theorem rational_uniformizer_off_support (p : HeightOneSpectrum (𝓞 F))
    (hp : p ∉ IdeleGroup.sufficientlyLargeFiniteSet (K := F)) :
    ∃ a : Fˣ, ‖(atPlace (.inr p) a).val‖ = (p.asIdeal.absNorm : ℝ)⁻¹ ∧
      ∀ q ∉ IdeleGroup.sufficientlyLargeFiniteSet (K := F), q ≠ p → ‖(atPlace (.inr q) a).val‖ = 1 := by
  obtain ⟨π,hπ⟩ := FinitePlace.exists_norm_uniformizer p
  let S := IdeleGroup.sufficientlyLargeFiniteSet (K := F)
  let t := IdeleGroup.finitePlaceIdele p π
  have ht : t ∈ IdeleGroup.supportedAt (K := F) (S : Set _) ⊔ IdeleGroup.principalSubgroup F := by
    rw [IdeleGroup.supportedAt_sup_principalSubgroup_eq_top]
    exact Subgroup.mem_top t
  obtain ⟨u,hu,_,⟨a,rfl⟩,he⟩ := Subgroup.mem_sup_of_normal_right.mp ht
  have H (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ S) :
      ‖(atPlace (.inr q) a).val‖ = ‖(IdeleGroup.finiteComponent q t).val‖ := by
    have huq := (IdeleGroup.mem_supportedAt_iff _ u).mp hu q hq
    let b := IdeleGroup.finiteComponent q u
    have hle (x : (q.adicCompletion F)ˣ) (h : x ∈ (q.adicCompletionIntegers F).units) :
        ‖x.val‖ ≤ 1 :=
      Valued.toNormedField.norm_le_one_iff.mpr ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F q).mp h.1)
    have hi := hle b⁻¹ ((q.adicCompletionIntegers F).units.inv_mem huq)
    rw [Units.val_inv_eq_inv_val,norm_inv,inv_le_one₀ (norm_pos_iff.mpr b.ne_zero)] at hi
    have hb := le_antisymm (hle b huq) hi
    have eqn := congrArg (fun z => ‖(IdeleGroup.finiteComponent q z).val‖) he
    rw [map_mul,Units.val_mul,norm_mul] at eqn
    change ‖b.val‖ * ‖(atPlace (.inr q) a).val‖ = _ at eqn
    rwa [hb,one_mul] at eqn
  refine ⟨a,(H p hp).trans ?_,fun q hq hne => (H q hq).trans ?_⟩
  · rw [show IdeleGroup.finiteComponent p t = π from IdeleGroup.finitePlaceIdele_finiteComponent_same p π]
    exact hπ
  · rw [show IdeleGroup.finiteComponent q t = 1 from IdeleGroup.finitePlaceIdele_finiteComponent_of_ne p q π hne]
    exact norm_one

/-- Every number field has a fixed finite support S₀ such that the restriction
to S detects orthogonal classes represented by integral units away from S,
for every finite S containing S₀. -/
theorem exists_finite_support_detecting_orthogonal :
    ∃ S₀ : Finset (Place F), ∀ S : Finset (Place F), S₀ ⊆ S →
      ∀ x : AdelicPowerClass n F, x ∈ d.rationalOrthogonal →
        (∀ v ∈ S, adelicClassAt n v x = 1) →
        (∀ p : HeightOneSpectrum (𝓞 F), Sum.inr p ∉ S →
          ∃ u : (LocalField F (.inr p))ˣ, ‖u.val‖ = 1 ∧ QuotientGroup.mk u = adelicClassAt n (.inr p) x) →
        x = 1 := by
  let wild := (eventually_cofinite.mp (eventually_tame (F := F) (n := n))).toFinset
  let T := IdeleGroup.sufficientlyLargeFiniteSet (K := F)
  refine ⟨Finset.univ.disjSum (T ∪ wild),?_⟩
  intro S hS x hx hloc hu
  have away (p : HeightOneSpectrum (𝓞 F)) (hp : Sum.inr p ∉ S) : p ∉ T ∪ wild :=
    fun h => hp (hS (Finset.inr_mem_disjSum.mpr h))
  apply d.eq_one_of_orthogonal_of_unit_outside S x hx hloc
  · intro w
    exact hS (Finset.inl_mem_disjSum.mpr (Finset.mem_univ w))
  · intro p hp
    have H : p ∉ wild := fun h => away p hp (Finset.mem_union_right _ h)
    simpa [wild] using H
  · exact hu
  · intro p hp
    obtain ⟨a,ha,hq⟩ := rational_uniformizer_off_support p (fun h => away p hp (Finset.mem_union_left _ h))
    exact ⟨a,ha,fun q hqs => hq q (fun h => away q hqs (Finset.mem_union_left _ h))⟩

/-- Restriction of an adelic class to its components on S. -/
def restrictPowerClass (S : Finset (Place F)) :
    AdelicPowerClass n F →* (v : S) → PowerClass n v.val :=
  MonoidHom.pi fun v => adelicClassAt n v.val

/-- Pair the components over S and multiply their values. -/
def supportPairing (S : Finset (Place F)) :
    ((v : S) → PowerClass n v.val) →* ((v : S) → PowerClass n v.val) →* ℂˣ :=
  MonoidHom.mk' (fun a => MonoidHom.mk' (fun b => ∏ v : S, d.localClassPairing v.val (a v) (b v)) (by
    intro b c
    simp only [Pi.mul_apply,map_mul,Finset.prod_mul_distrib])) (by
    intro a b
    apply MonoidHom.ext
    intro c
    change (∏ v : S, d.localClassPairing v.val (a v * b v) (c v)) = _
    simp only [map_mul,MonoidHom.mul_apply,Finset.prod_mul_distrib]
    rfl)

/-- Image on S of rational units having valuation zero at all finite places outside S. -/
def sUnitClassImage (n : ℕ) (S : Finset (Place F)) : Subgroup ((v : S) → PowerClass n v.val) :=
  let U : Subgroup Fˣ := ⨅ (p : HeightOneSpectrum (𝓞 F)) (_ : Sum.inr p ∉ S),
    (integralUnits p).comap (Units.map (diagonal F (.inr p)).toMonoidHom)
  U.map (((restrictPowerClass S).comp (rationalClassMap n F)).comp (QuotientGroup.mk' _))

/-- If two classes are represented by units outside S, their product
pairing is determined on S, provided S contains the infinite and wild places. -/
theorem adelicClassPairing_eq_supportPairing (S : Finset (Place F))
    (hinf : ∀ w : InfinitePlace F, Sum.inl w ∈ S)
    (ht : ∀ p : HeightOneSpectrum (𝓞 F), Sum.inr p ∉ S → p.asIdeal.absNorm.Coprime n)
    (x y : AdelicPowerClass n F)
    (hx : ∀ p : HeightOneSpectrum (𝓞 F), Sum.inr p ∉ S → adelicClassAt n (.inr p) x ∈ integralUnitClasses p n)
    (hy : ∀ p : HeightOneSpectrum (𝓞 F), Sum.inr p ∉ S → adelicClassAt n (.inr p) y ∈ integralUnitClasses p n) :
    d.adelicClassPairing x y = d.supportPairing S (restrictPowerClass S x) (restrictPowerClass S y) := by
  let f (v : Place F) := d.localClassPairing v (adelicClassAt n v x) (adelicClassAt n v y)
  have he : d.adelicClassPairing x y = ∏ᶠ v, f v := by
    dsimp only [f]
    induction x using QuotientGroup.induction_on with | _ a => _
    induction y using QuotientGroup.induction_on with | _ b => rfl
  rw [he,finprod_eq_prod_of_mulSupport_subset (s := S) _ (by
    intro v hv
    by_contra h
    cases v with
    | inl w => exact h (hinf w)
    | inr p => exact hv ((d.integralUnitClasses_orthogonal p (ht p h) _).mpr (hy p h) _ (hx p h))),
    ← Finset.prod_attach]
  rfl

/-- Restriction of an orthogonal class integral away from S annihilates
the S-unit image for the finite product of local pairings. -/
theorem orthogonal_restrict_sUnits (S : Finset (Place F)) (x : AdelicPowerClass n F)
    (hx : x ∈ d.rationalOrthogonal) (hinf : ∀ w : InfinitePlace F, Sum.inl w ∈ S)
    (ht : ∀ p : HeightOneSpectrum (𝓞 F), Sum.inr p ∉ S → p.asIdeal.absNorm.Coprime n)
    (hu : ∀ p : HeightOneSpectrum (𝓞 F), Sum.inr p ∉ S → adelicClassAt n (.inr p) x ∈ integralUnitClasses p n)
    (a : (v : S) → PowerClass n v.val) (ha : a ∈ sUnitClassImage n S) :
    d.supportPairing S a (restrictPowerClass S x) = 1 := by
  obtain ⟨b,hb,rfl⟩ := ha
  let y := rationalClassMap n F (QuotientGroup.mk b)
  have hy (p : HeightOneSpectrum (𝓞 F)) (hp : Sum.inr p ∉ S) :
      adelicClassAt n (.inr p) y ∈ integralUnitClasses p n :=
    ⟨atPlace (.inr p) b,Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hb p) hp,rfl⟩
  exact (d.adelicClassPairing_eq_supportPairing S hinf ht y x hy hu).symm.trans
    (Subgroup.mem_iInf.mp hx (QuotientGroup.mk b))

/-- The finite product pairing detects a class by testing one component at a time. -/
theorem supportPairing_left_kernel (S : Finset (Place F)) (a : (v : S) → PowerClass n v.val)
    (h : ∀ b, d.supportPairing S a b = 1) : a = 1 := by
  funext j
  apply d.localClassPairing_right_kernel
  intro c
  let b := Function.update (1 : (v : S) → PowerClass n v.val) j c
  have H := h b
  change (∏ v : S, d.localClassPairing v.val (a v) (b v)) = 1 at H
  rw [Finset.prod_eq_single j] at H
  · rw [d.localClassPairing_skew]
    simpa only [b,Function.update_self,inv_eq_one] using H
  · intro i _ hi
    simp only [b,Function.update_of_ne hi,Pi.one_apply,map_one]
  · simp

section FiniteOrthogonal
variable {G : Type*} [CommGroup G] [Fintype G]

private theorem card_mul_card_orthogonal (B : G →* G →* ℂˣ) (H : Subgroup G)
    (hn : ∀ a, (∀ b, B a b = 1) → a = 1) :
    Nat.card H * Nat.card (⨅ a : H, (B a.val).ker : Subgroup G) = Nat.card G := by
  let P := ⨅ a : H, (B a.val).ker
  let χ (a b : G) := (B a b : ℂ)
  have col (b : G) : (∑ a : H, χ a.val b) = if b ∈ P then (Nat.card H : ℂ) else 0 := by
    let f := ((Units.coeHom ℂ).comp (B.flip b)).comp H.subtype
    have he : f = 1 ↔ b ∈ P := by
      constructor
      · intro hf
        exact Subgroup.mem_iInf.mpr fun a => Units.ext (DFunLike.congr_fun hf a)
      · intro hb
        exact MonoidHom.ext fun a => congrArg Units.val (show B a.val b = 1 from Subgroup.mem_iInf.mp hb a)
    by_cases hb : b ∈ P
    · change (∑ a : H, f a) = _
      simp [he.mpr hb,hb,Nat.card_eq_fintype_card]
    · exact (sum_hom_units_eq_zero f (mt he.mp hb)).trans (if_neg hb).symm
  have row (a : H) : (∑ b : G, χ a.val b) = if a = 1 then (Nat.card G : ℂ) else 0 := by
    by_cases ha : a = 1
    · simp [ha,χ,Nat.card_eq_fintype_card]
    · rw [if_neg ha]
      let f := (Units.coeHom ℂ).comp (B a.val)
      apply sum_hom_units_eq_zero f
      intro hf
      exact ha (Subtype.ext (hn a.val fun b => Units.ext (DFunLike.congr_fun hf b)))
  let w (b : G) := if b ∈ P then (Nat.card H : ℂ) else 0
  have hw : (∑ b : G, w b) = (Nat.card H : ℂ) * (Nat.card P : ℂ) := by
    rw [← Fintype.sum_subtype_add_sum_subtype (· ∈ P)]
    have hw₁ (a : P) : w a.val = Nat.card H := if_pos a.property
    have hw₀ (a : {x : G // x ∉ P}) : w a.val = 0 := if_neg a.property
    simp [hw₁,hw₀,Nat.card_eq_fintype_card,mul_comm]
  have eqn : (Nat.card H : ℂ) * (Nat.card P : ℂ) = (Nat.card G : ℂ) := calc
    _ = ∑ b : G, ∑ a : H, χ a.val b := by simp only [col]; exact hw.symm
    _ = ∑ a : H, ∑ b : G, χ a.val b := Finset.sum_comm
    _ = _ := by simp [row]
  exact_mod_cast eqn
end FiniteOrthogonal

/-- For the product over S, isotropy and the square-cardinality identity
suffice to prove that a subgroup equals its annihilator. -/
theorem supportPairing_self_orthogonal_of_card (S : Finset (Place F))
    (H : Subgroup ((v : S) → PowerClass n v.val))
    (hi : ∀ a ∈ H, ∀ b ∈ H, d.supportPairing S a b = 1)
    (hc : Nat.card H ^ 2 = Nat.card ((v : S) → PowerClass n v.val)) :
    H = ⨅ a : H, (d.supportPairing S a.val).ker := by
  let (i : S) := finite_power_classes (n := n) i.val
  letI := Fintype.ofFinite ((v : S) → PowerClass n v.val)
  have Hc := card_mul_card_orthogonal (G := (v : S) → PowerClass n v.val) (d.supportPairing S) H (d.supportPairing_left_kernel S)
  rw [← hc,pow_two] at Hc
  have hpos : 0 < Nat.card H := Nat.card_pos
  exact Subgroup.eq_of_le_of_card_ge (fun b hb => Subgroup.mem_iInf.mpr fun a => hi a.val a.property b hb)
    (Nat.eq_of_mul_eq_mul_left hpos Hc).le

omit [NeZero n] in
theorem sUnit_mem_away (S : Finset (Place F)) (b : Fˣ)
    (hb : b ∈ ⨅ (p : HeightOneSpectrum (𝓞 F)) (_ : Sum.inr p ∉ S),
      (integralUnits p).comap (Units.map (diagonal F (.inr p)).toMonoidHom))
    (p : HeightOneSpectrum (𝓞 F)) (hp : Sum.inr p ∉ S) :
    adelicClassAt n (.inr p) (rationalClassMap n F (QuotientGroup.mk b)) ∈ integralUnitClasses p n :=
  ⟨atPlace (.inr p) b,Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hb p) hp,rfl⟩

/-- On a support satisfying the square-cardinality formula, the local images
of S-units form their own annihilator. -/
theorem sUnitClassImage_eq_orthogonal (S : Finset (Place F))
    (hi : ∀ w : InfinitePlace F, Sum.inl w ∈ S)
    (ht : ∀ p : HeightOneSpectrum (𝓞 F), Sum.inr p ∉ S → p.asIdeal.absNorm.Coprime n)
    (hc : Nat.card (sUnitClassImage n S)^2 = Nat.card ((v : S) → PowerClass n v.val)) :
    sUnitClassImage n S = ⨅ a : sUnitClassImage n S, (d.supportPairing S a.val).ker := by
  have iso (a) (ha : a ∈ sUnitClassImage n S) (b) (hb : b ∈ sUnitClassImage n S) :
      d.supportPairing S a b = 1 := by
    obtain ⟨c,hc,rfl⟩ := hb
    let y := rationalClassMap n F (QuotientGroup.mk c)
    exact d.orthogonal_restrict_sUnits S y (d.rationalClass_le_orthogonal ⟨_,rfl⟩) hi ht
      (sUnit_mem_away S c hc) a ha
  exact d.supportPairing_self_orthogonal_of_card S (sUnitClassImage n S) iso hc

/-- The adelic annihilator equality follows from the square-cardinality
identity for the S-unit image on a cofinal system of finite sets of places. -/
theorem rationalOrthogonal_eq_of_sUnit_card
    (hcard : ∀ T : Finset (Place F), ∃ S : Finset (Place F), T ⊆ S ∧
      Nat.card (sUnitClassImage n S)^2 = Nat.card ((v : S) → PowerClass n v.val)) :
    d.rationalOrthogonal = (rationalClassMap n F).range := by
  apply le_antisymm _ d.rationalClass_le_orthogonal
  intro x hx
  obtain ⟨S₀,h₀⟩ := d.exists_finite_support_detecting_orthogonal
  have hu₀ : ∀ᶠ p : HeightOneSpectrum (𝓞 F) in cofinite,
      adelicClassAt n (.inr p) x ∈ integralUnitClasses p n := by
    induction x using QuotientGroup.induction_on with | _ a => _
    exact (eventually_unit_component a).mono fun p hp => ⟨Units.map (componentHom (.inr p)).toMonoidHom a,hp,rfl⟩
  have hgood := (eventually_tame (F := F) (n := n)).and hu₀
  let bad := (eventually_cofinite.mp hgood).toFinset
  obtain ⟨S,hS,hc⟩ := hcard (S₀ ∪ Finset.univ.disjSum bad)
  have hbase : S₀ ⊆ S := fun _ h => hS (Finset.mem_union_left _ h)
  have hi (w : InfinitePlace F) : Sum.inl w ∈ S :=
    hS (Finset.mem_union_right _ (Finset.inl_mem_disjSum.mpr (Finset.mem_univ w)))
  have hg (p : HeightOneSpectrum (𝓞 F)) (hp : Sum.inr p ∉ S) :
      p.asIdeal.absNorm.Coprime n ∧ adelicClassAt n (.inr p) x ∈ integralUnitClasses p n := by
    have H : p ∉ bad := fun h => hp (hS (Finset.mem_union_right _ (Finset.inr_mem_disjSum.mpr h)))
    simpa [bad] using H
  have ht := fun p hp => (hg p hp).1
  have hu := fun p hp => (hg p hp).2
  have H := d.sUnitClassImage_eq_orthogonal S hi ht hc
  have hloc : restrictPowerClass S x ∈ sUnitClassImage n S := by
    rw [H]
    exact Subgroup.mem_iInf.mpr fun a => d.orthogonal_restrict_sUnits S x hx hi ht hu a.val a.property
  obtain ⟨b,hb,he⟩ := hloc
  let y := rationalClassMap n F (QuotientGroup.mk b)
  have hxy : x/y = 1 := by
    apply h₀ S hbase (x/y) (d.rationalOrthogonal.div_mem hx (d.rationalClass_le_orthogonal ⟨_,rfl⟩))
    · intro v hv
      rw [map_div,div_eq_one]
      exact (congrFun he (⟨v,hv⟩ : S)).symm
    · intro p hp
      rw [map_div]
      exact (integralUnitClasses p n).div_mem (hu p hp) (sUnit_mem_away S b hb p hp)
  exact ⟨QuotientGroup.mk b,(div_eq_one.mp hxy).symm⟩

end MetaplecticPoisson.Datum
