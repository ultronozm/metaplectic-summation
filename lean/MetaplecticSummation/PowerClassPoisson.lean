import MetaplecticSummation.Hilbert.GlobalRadical

/-! Multiplicative Poisson summation on power classes (Lemma B.3). -/
noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField IsDedekindDomain Filter
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)
private abbrev localize (v : Place F) (x : GlobalClass n F) :=
  adelicClassAt n v (rationalClassMap n F x)

private theorem localize_rep (v : Place F) (x : GlobalClass n F) :
    localize v x = QuotientGroup.mk (atPlace v x.out) := by
  have he (b : Fˣ) : localize v (QuotientGroup.mk b : GlobalClass n F) = QuotientGroup.mk (atPlace v b) := by
    cases v <;> rfl
  exact (congrArg (localize v) (Quotient.out_eq x)).symm.trans (he x.out)

private theorem supportPairing_skew (S : Finset (Place F)) (a b : (v : S) → PowerClass n v.val) :
    d.supportPairing S a b = (d.supportPairing S b a)⁻¹ := by
  change (∏ i : S, d.localClassPairing i.val (a i) (b i)) = (∏ i : S, d.localClassPairing i.val (b i) (a i))⁻¹
  rw [← Finset.prod_inv_distrib]
  exact Finset.prod_congr rfl fun i _ => d.localClassPairing_skew _ _ _

private theorem finite_support_poisson (S : Finset (Place F))
    (β : (v : Place F) → PowerClass n v → ℂ) (H : Subgroup ((v : S) → PowerClass n v.val))
    (hself : H = ⨅ a : H, (d.supportPairing S a.val).ker) (hcard : Nat.card H = n^S.card) :
    (∑ᶠ a : H, ∏ i : S, β i.val (a.val i)) =
      ∑ᶠ a : H, ∏ i : S, d.powerClassTransform i.val (β i.val) (a.val i) := by
  let (i : S) := finite_power_classes (n := n) i.val
  letI (i : S) := Fintype.ofFinite (PowerClass n i.val)
  let G := (i : S) → PowerClass n i.val
  let B := d.supportPairing S
  let f (a : G) := ∏ i : S, β i.val (a i)
  let k := (n : ℂ)⁻¹ ^ S.card
  have expand (a : G) : (∏ i : S, d.powerClassTransform i.val (β i.val) (a i)) =
      k * ∑ c : G, (B c a : ℂ) * f c := by
    simp only [powerClassTransform,finsum_eq_sum_of_fintype,Finset.prod_mul_distrib,Finset.prod_const,
      Finset.card_univ,Fintype.card_coe,Fintype.prod_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro c _
    change (∏ i : S, (Units.coeHom ℂ) _) * _ = (Units.coeHom ℂ) (∏ i : S, _) * _
    rw [map_prod]
  have orth (c : G) : (∑ a : H, (B c a.val : ℂ)) = if c ∈ H then (Nat.card H : ℂ) else 0 := by
    let χ := ((Units.coeHom ℂ).comp (B c)).comp H.subtype
    have he : χ = 1 ↔ c ∈ H := by
      constructor
      · intro h
        rw [hself]
        apply Subgroup.mem_iInf.mpr
        intro a
        change d.supportPairing S a.val c = 1
        rw [d.supportPairing_skew,inv_eq_one]
        exact Units.ext (DFunLike.congr_fun h a)
      · intro hc
        have hc' : c ∈ ⨅ a : H, (B a.val).ker := hself ▸ hc
        apply MonoidHom.ext
        intro a
        have e : B a.val c = 1 := Subgroup.mem_iInf.mp hc' a
        exact congrArg Units.val ((d.supportPairing_skew S c a.val).trans (by rw [show d.supportPairing S a.val c = 1 from e,inv_one]))
    by_cases hc : c ∈ H
    · change (∑ a : H, χ a) = _
      simp [he.mpr hc,hc,Nat.card_eq_fintype_card]
    · exact (sum_hom_units_eq_zero χ (mt he.mp hc)).trans (if_neg hc).symm
  have count : (∑ c : G, (if c ∈ H then (Nat.card H : ℂ) else 0) * f c) =
      (Nat.card H : ℂ) * ∑ c : H, f c.val := by
    rw [← Fintype.sum_subtype_add_sum_subtype (· ∈ H),Finset.mul_sum]
    have good (c : H) : (if c.val ∈ H then (Nat.card H : ℂ) else 0) = Nat.card H := if_pos c.property
    have bad (c : {c : G // c ∉ H}) : (if c.val ∈ H then (Nat.card H : ℂ) else 0) = 0 := if_neg c.property
    simp only [good,bad,zero_mul,Finset.sum_const_zero,add_zero]
  have norm : k * (Nat.card H : ℂ) = 1 := by
    rw [hcard,Nat.cast_pow]
    change (n : ℂ)⁻¹ ^ S.card * (n : ℂ)^S.card = 1
    rw [← mul_pow,inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne n)),one_pow]
  rw [finsum_eq_sum_of_fintype,finsum_eq_sum_of_fintype]
  symm
  calc
    _ = k * ∑ c : G, (∑ a : H, (B c a.val : ℂ)) * f c := by
      simp_rw [expand]
      rw [← Finset.mul_sum,Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ = k * ((Nat.card H : ℂ) * ∑ c : H, f c.val) := by simp only [orth,count]
    _ = _ := by rw [← mul_assoc,norm,one_mul]

private theorem adelic_sum_eq_sUnit_sum (S : Finset (Place F)) (β : (v : Place F) → PowerClass n v → ℂ)
    (hi : ∀ w : InfinitePlace F, Sum.inl w ∈ S)
    (ht : ∀ p : HeightOneSpectrum (𝓞 F), Sum.inr p ∉ S → p.asIdeal.absNorm.Coprime n)
    (hβ : ∀ p : HeightOneSpectrum (𝓞 F), Sum.inr p ∉ S → β (.inr p) = unitClassTest p n)
    (hself : sUnitClassImage n S = ⨅ a : sUnitClassImage n S, (d.supportPairing S a.val).ker)
    (hdet : ∀ x : AdelicPowerClass n F, x ∈ d.rationalOrthogonal → (∀ v ∈ S, adelicClassAt n v x = 1) →
      (∀ p : HeightOneSpectrum (𝓞 F), Sum.inr p ∉ S → adelicClassAt n (.inr p) x ∈ integralUnitClasses p n) → x = 1) :
    Function.HasFiniteSupport (fun a : GlobalClass n F => ∏ᶠ v, β v (localize v a)) ∧
    (∑' a : GlobalClass n F, ∏ᶠ v, β v (localize v a)) =
      ∑ᶠ c : sUnitClassImage n S, ∏ i : S, β i.val (c.val i) := by
  let A : Set (GlobalClass n F) := {a | ∀ p : HeightOneSpectrum (𝓞 F), Sum.inr p ∉ S →
    localize (.inr p) a ∈ integralUnitClasses p n}
  let H := sUnitClassImage n S
  let r (a : GlobalClass n F) := restrictPowerClass S (rationalClassMap n F a)
  have hr (a : A) : r a.val ∈ H := by
    change r a.val ∈ sUnitClassImage n S
    rw [hself]
    exact Subgroup.mem_iInf.mpr fun b => d.orthogonal_restrict_sUnits S (rationalClassMap n F a.val)
      (d.rationalClass_le_orthogonal ⟨_,rfl⟩) hi ht a.property b.val b.property
  let g (a : A) : H := ⟨r a.val,hr a⟩
  have inj : Function.Injective g := by
    intro a b hab
    apply Subtype.ext
    apply d.rationalClassMap_injective
    apply div_eq_one.mp
    apply hdet
    · exact d.rationalOrthogonal.div_mem (d.rationalClass_le_orthogonal ⟨_,rfl⟩)
        (d.rationalClass_le_orthogonal ⟨_,rfl⟩)
    · intro v hv
      rw [map_div,div_eq_one]
      exact congrArg (fun c : H => c.val (⟨v,hv⟩ : S)) hab
    · intro p hp
      rw [map_div]
      exact (integralUnitClasses p n).div_mem (a.property p hp) (b.property p hp)
  have surj : Function.Surjective g := by
    rintro ⟨c,b,hb,rfl⟩
    exact ⟨⟨QuotientGroup.mk b,sUnit_mem_away S b hb⟩,rfl⟩
  let e := Equiv.ofBijective g ⟨inj,surj⟩
  let ψ (a : GlobalClass n F) v := β v (localize v a)
  have supp (a : GlobalClass n F) : Function.HasFiniteMulSupport (ψ a) := by
    apply eventually_cofinite.mp
    apply eventually_place_of_finite
    have away : ∀ᶠ p : HeightOneSpectrum (𝓞 F) in cofinite, Sum.inr p ∉ S :=
      (S.toRight.eventually_cofinite_notMem).mono fun _ hp h => hp (Finset.mem_toRight.mpr h)
    filter_upwards [away,eventually_diagonal_norm_one a.out.ne_zero] with p hp hnorm
    change β (.inr p) (localize (.inr p) a) = 1
    rw [hβ p hp,localize_rep]
    exact if_pos ⟨atPlace (.inr p) a.out,hnorm,rfl⟩
  have hz : Function.support (fun a : GlobalClass n F => ∏ᶠ v, ψ a v) ⊆ A := by
    intro a ha p hp
    by_contra hn
    apply ha
    apply finprod_eq_zero _ (.inr p) _ (supp a)
    change β (.inr p) (localize (.inr p) a) = 0
    rw [hβ p hp]
    exact if_neg hn
  let Φ (c : H) := ∏ i : S, β i.val (c.val i)
  have term (a : A) : (∏ᶠ v, ψ a.val v) = Φ (e a) := by
    rw [finprod_eq_prod_of_mulSupport_subset (s := S) _ (by
      intro v hv
      by_contra h
      cases v with
      | inl w => exact h (hi w)
      | inr p =>
        apply hv
        change β (.inr p) (localize (.inr p) a.val) = 1
        rw [hβ p h]
        exact if_pos (a.property p h)),← Finset.prod_attach]
    rfl
  let (i : S) := finite_power_classes (n := n) i.val
  letI := Fintype.ofFinite H
  letI : Fintype A := Fintype.ofEquiv H e.symm
  refine ⟨A.toFinite.subset hz,?_⟩
  calc
    _ = ∑' a : A, ∏ᶠ v, ψ a.val v := (tsum_subtype_eq_of_support_subset hz).symm
    _ = ∑' a : A, Φ (e a) := tsum_congr term
    _ = ∑' c : H, Φ c := e.tsum_eq Φ
    _ = _ := by rw [tsum_fintype,finsum_eq_sum_of_fintype]

private theorem powerClass_poisson_aux (β : (v : Place F) → PowerClass n v → ℂ)
    (hβ : ∀ᶠ p : HeightOneSpectrum (𝓞 F) in cofinite, β (.inr p) = unitClassTest p n) :
    Function.HasFiniteSupport (fun a : GlobalClass n F => ∏ᶠ v, β v (localize v a)) ∧
    Function.HasFiniteSupport (fun a : GlobalClass n F => ∏ᶠ v, d.powerClassTransform v (β v) (localize v a)) ∧
    (∑' a : GlobalClass n F, ∏ᶠ v, β v (localize v a)) =
      ∑' a : GlobalClass n F, ∏ᶠ v, d.powerClassTransform v (β v) (localize v a) := by
  obtain ⟨S₀,h₀⟩ := d.exists_finite_support_detecting_orthogonal
  have good := (eventually_tame (F := F) (n := n)).and hβ
  let bad := (eventually_cofinite.mp good).toFinset
  obtain ⟨S,hs,horder,hc⟩ := d.exists_support_sUnit_card (S₀ ∪ Finset.univ.disjSum bad)
  have det := h₀ S (fun _ h => hs (Finset.mem_union_left _ h))
  have hi (w : InfinitePlace F) : Sum.inl w ∈ S := hs (Finset.mem_union_right _ (Finset.inl_mem_disjSum.mpr (Finset.mem_univ w)))
  have hg (p : HeightOneSpectrum (𝓞 F)) (hp : Sum.inr p ∉ S) :
      p.asIdeal.absNorm.Coprime n ∧ β (.inr p) = unitClassTest p n := by
    have hh : p ∉ bad := fun h => hp (hs (Finset.mem_union_right _ (Finset.inr_mem_disjSum.mpr h)))
    simpa [bad] using hh
  have ht := fun p hp => (hg p hp).1
  have Hu := fun p hp => (hg p hp).2
  have H := d.sUnitClassImage_eq_orthogonal S hi ht hc
  obtain ⟨hβfin,hβsum⟩ := d.adelic_sum_eq_sUnit_sum S β hi ht Hu H det
  obtain ⟨hdualfin,hdualsum⟩ := d.adelic_sum_eq_sUnit_sum S (fun v => d.powerClassTransform v (β v)) hi ht
    (fun p hp => by rw [Hu p hp,d.powerClassTransform_unitClassTest p (ht p hp)]) H det
  exact ⟨hβfin,hdualfin,hβsum.trans ((d.finite_support_poisson S β _ H horder).trans hdualsum.symm)⟩

/-- Both summands in Lemma B.3 have finite support on the rational power classes. -/
theorem powerClass_poisson_finite_support (β : (v : Place F) → PowerClass n v → ℂ)
    (hβ : ∀ᶠ p : HeightOneSpectrum (𝓞 F) in cofinite, β (.inr p) = unitClassTest p n) :
    let ev := fun (v : Place F) (x : GlobalClass n F) => (QuotientGroup.mk (atPlace v x.out) : PowerClass n v)
    Function.HasFiniteSupport (fun a : GlobalClass n F => ∏ᶠ v, β v (ev v a)) ∧
      Function.HasFiniteSupport (fun a : GlobalClass n F => ∏ᶠ v, d.powerClassTransform v (β v) (ev v a)) := by
  obtain ⟨h,h',_⟩ := d.powerClass_poisson_aux β hβ
  simpa only [localize_rep] using And.intro h h'

/-- Appendix B's Poisson formula on multiplicative power classes. -/
theorem powerClass_poisson (β : (v : Place F) → PowerClass n v → ℂ)
    (hβ : ∀ᶠ p : HeightOneSpectrum (𝓞 F) in cofinite, ∀ c, β (.inr p) c =
      if ∃ u : (LocalField F (.inr p))ˣ, ‖(u : LocalField F (.inr p))‖ = 1 ∧
        QuotientGroup.mk u = c then 1 else 0) :
    let eval := fun (v : Place F) (x : GlobalClass n F) =>
      (QuotientGroup.mk (atPlace v x.out) : PowerClass n v)
    let dual := fun (v : Place F) (y : PowerClass n v) =>
      (n : ℂ)⁻¹ * ∑ᶠ c : PowerClass n v, d.symbol v c.out y.out * β v c
    (∑' x : GlobalClass n F, ∏ᶠ v, β v (eval v x)) =
      ∑' y : GlobalClass n F, ∏ᶠ v, dual v (eval v y) := by
  have hu : ∀ᶠ p : HeightOneSpectrum (𝓞 F) in cofinite, β (.inr p) = unitClassTest p n := by
    filter_upwards [hβ] with p hp
    funext c
    exact hp c
  simpa only [localize_rep,powerClassTransform_representatives] using (d.powerClass_poisson_aux β hu).2.2

end MetaplecticPoisson.Datum
