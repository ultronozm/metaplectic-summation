import MetaplecticSummation.PowerClassSupport
import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.SUnitKummerNormCore

/-! The annihilator of the rational power classes in Appendix B, Lemma B.3. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField IsDedekindDomain GlobalClassFieldTheory.ClassFieldAxiom
open GlobalClassFieldTheory.GlobalClassFields KummerTheory
open Classical
variable {F : Type} [Field F] [NumberField F]
private abbrev PrimeSet (F : Type) [Field F] := Finset (HeightOneSpectrum (𝓞 F))

private def allInfinite (T : PrimeSet F) : Finset (Place F) := Finset.univ.disjSum T

private theorem norm_rational_unit_iff (p : HeightOneSpectrum (𝓞 F)) (a : Fˣ) :
    ‖(atPlace (.inr p) a).val‖ = 1 ↔ p.valuation F a.val = 1 := by
  change ‖algebraMap F (p.adicCompletion F) a.val‖ = 1 ↔ _
  rw [Valued.toNormedField.norm_eq_one_iff]
  exact Iff.of_eq (congrArg (· = 1) (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' p a.val))

private def localizeSUnit (m : ℕ+) (T : PrimeSet F) :
    SUnitGroup (K := F) (T ∪ ∅) →* ((v : allInfinite T) → PowerClass (m : ℕ) v.val) :=
  (((restrictPowerClass (n := (m : ℕ)) (allInfinite T)).comp (rationalClassMap (m : ℕ) F)).comp (QuotientGroup.mk' _)).comp
    (SUnitGroup (K := F) (T ∪ ∅)).subtype

private theorem localizeSUnit_apply (m : ℕ+) (T : PrimeSet F) (b : SUnitGroup (K := F) (T ∪ ∅))
    (v : allInfinite T) : localizeSUnit m T b v = QuotientGroup.mk (atPlace v.val b.val) := by
  obtain ⟨w|p,h⟩ := v <;> rfl

private theorem localizeSUnit_range (m : ℕ+) (T : PrimeSet F) :
    (localizeSUnit m T).range = sUnitClassImage (m : ℕ) (allInfinite T) := by
  ext f
  constructor
  · rintro ⟨b,rfl⟩
    refine ⟨b.val,Subgroup.mem_iInf.mpr fun p => Subgroup.mem_iInf.mpr fun hp => ?_,rfl⟩
    apply (norm_rational_unit_iff p b.val).mpr
    apply (mem_SUnitGroup_iff _ _).mp b.property
    simpa [allInfinite] using hp
  · rintro ⟨b,hb,rfl⟩
    refine ⟨⟨b,(mem_SUnitGroup_iff _ _).mpr fun p hp => ?_⟩,rfl⟩
    apply (norm_rational_unit_iff p b).mp
    apply Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hb p)
    simpa [allInfinite] using hp

private theorem localizeSUnit_ker (m : ℕ+) (T : PrimeSet F) :
    (localizeSUnit m T).ker = sUnitPrincipalIdelePowerSubgroup (K := F) m T ∅ := by
  ext b
  change localizeSUnit m T b = 1 ↔
    IdeleGroup.principalIdele F b.val ∈ idelePowerLocalUnitSubgroup (K := F) m T ∅
  rw [mem_idelePowerLocalUnitSubgroup_iff]
  have hinf (w : InfinitePlace F) : IdeleGroup.infiniteComponent w (IdeleGroup.principalIdele F b.val) =
      atPlace (.inl w) b.val := rfl
  have hfin (p : HeightOneSpectrum (𝓞 F)) : IdeleGroup.finiteComponent p (IdeleGroup.principalIdele F b.val) =
      atPlace (.inr p) b.val := rfl
  constructor
  · intro h
    have he (v : allInfinite T) : atPlace v.val b.val ∈ (powMonoidHom (m : ℕ) : (LocalField F v.val)ˣ →* _).range :=
      (QuotientGroup.eq_one_iff _).mp ((localizeSUnit_apply m T b v).symm.trans (congrFun h v))
    refine ⟨?_,?_,?_⟩
    · intro w
      obtain ⟨r,hr⟩ := he ⟨.inl w,Finset.inl_mem_disjSum.mpr (Finset.mem_univ w)⟩
      exact ⟨r,hr⟩
    · intro p hp
      obtain ⟨r,hr⟩ := he ⟨.inr p,Finset.inr_mem_disjSum.mpr hp⟩
      exact ⟨r,hr⟩
    · have hs := (principalIdele_mem_supportedAt_iff_sUnit (L := F) (T ∪ ∅) b.val).mpr b.property
      intro p hnot
      have hbad : p ∉ T ∪ (∅ : PrimeSet F) := by simpa using hnot
      exact ((IdeleGroup.mem_supportedAt_iff (K := F) (↑(T ∪ (∅ : PrimeSet F))) (IdeleGroup.principalIdele F b.val)).mp hs) p hbad
  · rintro ⟨hi,hp,_⟩
    funext v
    rw [localizeSUnit_apply]
    apply (QuotientGroup.eq_one_iff _).mpr
    obtain ⟨w|p,h⟩ := v
    · exact hinf w ▸ hi w
    · exact hfin p ▸ hp p (by simpa [allInfinite] using h)

private def supportClassesEquiv (m : ℕ+) (T : PrimeSet F) :
    ((v : allInfinite T) → PowerClass (m : ℕ) v.val) ≃
      ((w : InfinitePlace F) → PowerClass (m : ℕ) (.inl w)) × ((p : T) → PowerClass (m : ℕ) (.inr p.val)) where
  toFun f := (fun w => f ⟨.inl w,by simp [allInfinite]⟩, fun p => f ⟨.inr p.val,by simpa [allInfinite] using p.property⟩)
  invFun f v := match v with
    | ⟨.inl w,_⟩ => f.1 w
    | ⟨.inr p,h⟩ => f.2 ⟨p,by simpa [allInfinite] using h⟩
  left_inv f := funext fun ⟨w,h⟩ => by cases w <;> rfl
  right_inv _ := rfl

/-- On Yamaguchi's enlarged Kummer norm support the S-unit image has
square order equal to the order of the full product of local classes. -/
theorem card_sUnitClassImage_on_kummerSupport {n : ℕ} [NeZero n] (d : Datum F n) (T : PrimeSet F) :
    let m : ℕ+ := ⟨n,NeZero.pos n⟩
    let S := allInfinite (sUnitKummerNormSupport (K := F) m T)
    Nat.card (sUnitClassImage n S) = n^S.card ∧
      Nat.card (sUnitClassImage n S)^2 = Nat.card ((v : S) → PowerClass n v.val) := by
  let m : ℕ+ := ⟨n,NeZero.pos n⟩
  let U := sUnitKummerNormSupport (K := F) m T
  have hm : (primitiveRoots n F).Nonempty := ⟨d.root,(mem_primitiveRoots m.pos).mpr d.primitive⟩
  have hd (p : HeightOneSpectrum (𝓞 F)) (hp : p.asIdeal ∣ Ideal.span {(n : 𝓞 F)}) : p ∈ U :=
    mem_sUnitKummerNormSupport_of_asIdeal_dvd_natCast (K := F) m T hp
  have hl := supportedAt_sUnitKummerNormSupport_sup_principalSubgroup_eq_top (K := F) m T
  have hlarge : IdeleGroup.supportedAt (K := F) ((U : Set _) ∪ (↑(∅ : PrimeSet F) : Set (HeightOneSpectrum (𝓞 F)))) ⊔ IdeleGroup.principalSubgroup F = ⊤ := by simpa [U] using hl
  let q := n ^ totalPlaceCard (K := F) U
  have hq : 0 < q := pow_pos (NeZero.pos n) _
  have hi := card_ideleClassPowerLocalUnitQuotient_on_kummerNormSupport (K := F) m hm T
  have hex := card_sUnitPrincipalQuotient_mul_card_ideleClassQuotient_eq_power_two_totalPlaceCard
    (K := F) m hm U ∅ hd hlarge
  have hp : (n : ℕ)^(2 * totalPlaceCard (K := F) U) = q * q := by simp [q,two_mul,pow_add]
  rw [hi] at hex
  have hN := Nat.eq_of_mul_eq_mul_right hq (hex.trans hp)
  have HR := Nat.card_congr (QuotientGroup.quotientKerEquivRange (G := SUnitGroup (K := F) (U ∪ ∅))
    (H := (v : allInfinite U) → PowerClass (m : ℕ) v.val) (localizeSUnit m U)).toEquiv
  rw [localizeSUnit_ker,localizeSUnit_range] at HR
  have hc : Nat.card (sUnitClassImage n (allInfinite U)) = q := HR.symm.trans hN
  have hprod := card_supportedIdeleQuotient_eq_localPowerClasses (K := F) m U ∅
  have htot := card_supportedIdeleQuotient_eq_power_two_totalPlaceCard (K := F) m hm U ∅ hd
  refine ⟨hc.trans (by simp [q,allInfinite,totalPlaceCard,U,m]),?_⟩
  change Nat.card (sUnitClassImage n (allInfinite U)) ^ 2 = _
  rw [hc,pow_two]
  exact hp.symm.trans (htot.symm.trans (hprod.trans (Nat.card_congr (supportClassesEquiv m U)).symm))

/-- Cofinal finite sets with the cardinalities needed for finite Poisson summation. -/
theorem exists_support_sUnit_card {n : ℕ} [NeZero n] (d : Datum F n) (T : Finset (Place F)) :
    ∃ S : Finset (Place F), T ⊆ S ∧ Nat.card (sUnitClassImage n S) = n^S.card ∧
      Nat.card (sUnitClassImage n S)^2 = Nat.card ((v : S) → PowerClass n v.val) := by
  let m : ℕ+ := ⟨n,NeZero.pos n⟩
  refine ⟨allInfinite (sUnitKummerNormSupport (K := F) m T.toRight),?_,d.card_sUnitClassImage_on_kummerSupport T.toRight⟩
  intro v hv
  cases v with
  | inl w => simp [allInfinite]
  | inr p => exact Finset.inr_mem_disjSum.mpr (subset_sUnitKummerNormSupport m _ (Finset.mem_toRight.mpr hv))

/-- The diagonal rational power classes in the ideles modulo powers equal
their orthogonal complement under the normalized Hilbert pairing. -/
theorem rationalOrthogonal_eq {n : ℕ} [NeZero n] (d : Datum F n) :
    d.rationalOrthogonal = (rationalClassMap n F).range := by
  apply d.rationalOrthogonal_eq_of_sUnit_card
  intro T
  obtain ⟨S,hS,_,hc⟩ := d.exists_support_sUnit_card T
  exact ⟨S,hS,hc⟩

/-- A rational unit whose class becomes trivial adelically was already an
n-th power in the number field. -/
theorem rationalClassMap_injective {n : ℕ} [NeZero n] (d : Datum F n) :
    Function.Injective (rationalClassMap n F) := by
  have H (x : GlobalClass n F) (hx : rationalClassMap n F x = 1) : x = 1 := by
    induction x using QuotientGroup.induction_on with | _ b => _
    let m : ℕ+ := ⟨n,NeZero.pos n⟩
    let T := chosenUnitFiniteSupport (K := F) b
    let U := sUnitKummerNormSupport (K := F) m T
    have hm : (primitiveRoots n F).Nonempty := ⟨d.root,(mem_primitiveRoots m.pos).mpr d.primitive⟩
    have hb : b ∈ SUnitGroup (K := F) (U ∪ ∅) := by
      apply (mem_SUnitGroup_iff _ _).mpr
      intro p hp
      apply (mem_SUnitGroup_iff _ _).mp (mem_sUnitGroup_chosenUnitFiniteSupport b) p
      exact fun ht => hp (Finset.mem_union_left _ (subset_sUnitKummerNormSupport m T ht))
    let u : SUnitGroup (K := F) (U ∪ ∅) := ⟨b,hb⟩
    have hker : u ∈ (localizeSUnit m U).ker := by
      change restrictPowerClass (allInfinite U) (rationalClassMap n F (QuotientGroup.mk b)) = 1
      rw [hx,map_one]
    rw [localizeSUnit_ker] at hker
    change b ∈ principalIdelePowerLocalUnitSubgroup (K := F) m U ∅ at hker
    rw [principalIdelePowerLocalUnitSubgroup_eq_sUnitNthPowers_on_kummerNormSupport m hm T] at hker
    exact (QuotientGroup.eq_one_iff _).mpr ((mem_sUnitNthPowersInField_iff m U b).mp hker).2
  intro a b h
  exact div_eq_one.mp (H (a/b) (by rw [map_div,h,div_self']))

end MetaplecticPoisson.Datum
