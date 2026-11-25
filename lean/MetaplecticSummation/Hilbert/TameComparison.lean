import MetaplecticSummation.Hilbert.FinitePairing
import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.PowerResidueReciprocity
import ClassFieldTheory.LocalClassFieldTheory.Kummer.PowerResidueTameFormula

noncomputable section
open scoped NumberField ValuativeRel WithZero NNReal
open NumberField IsDedekindDomain GlobalClassFieldTheory.Reciprocity
open LocalFieldTheory LocalFieldTheory.IsNonarchimedeanLocalField
open LocalClassFieldTheory.Kummer KummerTheory ClassFieldTheory MetaplecticPoisson
namespace MetaplecticPoisson.Hilbert

variable {F : Type} [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F))
local notation "C" => AbsoluteValue.Completion (NumberField.HeightOneSpectrum.adicAbv F p)
local notation "D" => IsDedekindDomain.HeightOneSpectrum.adicCompletion F p
local instance : ValuativeRel C := finitePlaceLocalArtinCompletionValuativeRel p
local instance : IsNonarchimedeanLocalField C := finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField p
local instance : IsUltrametricDist C := finitePlaceArtinCompletionIsUltrametricDist _
  (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv F p)

private theorem valuation_eq_iff_norm_eq (x y : C) :
    ValuativeRel.valuation C x = ValuativeRel.valuation C y ↔ ‖x‖ = ‖y‖ := by
  rw [← (ValuativeRel.valuation C).veq_iff_eq]
  change (‖x‖ ≤ ‖y‖ ∧ ‖y‖ ≤ ‖x‖) ↔ _
  exact le_antisymm_iff.symm

private theorem valuation_lt_iff_norm_lt (x y : C) :
    ValuativeRel.valuation C x < ValuativeRel.valuation C y ↔ ‖x‖ < ‖y‖ := by
  rw [← (ValuativeRel.valuation C).vlt_iff_lt]
  change (¬ ‖y‖ ≤ ‖x‖) ↔ _
  exact not_le

/-- Every uniformizer of the paper's norm has exponent -1 in the source
completion of the coherent Hilbert pairing. -/
theorem valuationMap_of_uniformizer_norm (π : Cˣ) (hπ : ‖π.val‖ = (p.asIdeal.absNorm : ℝ)⁻¹) :
    valuationMap C (Additive.ofMul π) = -1 := by
  let data := chosenFinitePlaceCompletionIntegralUniformizer p
  let π₀ := uniformizerFieldUnit C data.completionInteger data.completionInteger_isUniformizer
  have hnorm : ‖π₀.val‖ = (p.asIdeal.absNorm : ℝ)⁻¹ := by
    change ‖(data.completionInteger : C)‖ = _
    rw [data.coe_completionInteger]
    have h := AbsoluteValue.completionAbsoluteValue_coe (NumberField.HeightOneSpectrum.adicAbv F p) (data.integer : F)
    change ‖algebraMap F C (data.integer : F)‖ = NumberField.HeightOneSpectrum.adicAbv F p (data.integer : F) at h
    rw [h,
      NumberField.HeightOneSpectrum.adicAbv_def,HeightOneSpectrum.valuation_of_algebraMap,
      data.intValuation_eq_exp_neg_one,WithZeroMulInt.toNNReal_neg_apply _ (WithZero.exp_ne_zero (a := (-1 : ℤ)))]
    change (↑((p.asIdeal.absNorm : ℝ≥0) ^ (-1 : ℤ)) : ℝ) = _
    simp
  have hv := (valuation_eq_iff_norm_eq p π.val π₀.val).2 (hπ.trans hnorm.symm)
  have he : valuationMap C (Additive.ofMul π) = valuationMap C (Additive.ofMul π₀) := by
    rw [valuationMap_apply,valuationMap_apply]
    unfold IsNonarchimedeanLocalField.v
    congr 2
    exact congrArg (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt C) hv
  exact he.trans (valuationMap_uniformizerFieldUnit C _ _)

private theorem residueCard : Nat.card 𝓀[C] = p.asIdeal.absNorm := by
  rw [← Nat.card_congr (finitePlacePrimeResidueEquivLocalResidue F p).toEquiv]
  rfl

private theorem degree_valuation (n : ℕ+) (hp : p.asIdeal.absNorm.Coprime (n : ℕ)) :
    ValuativeRel.valuation C ((n : ℕ) : C) = 1 := by
  apply finitePlace_natCast_valuation_eq_one_of_not_mem_exponent
  rw [mem_powerResidueExponentFinitePlaces_iff,powerResidueExponentIdeal,Ideal.dvd_span_singleton]
  intro h
  let k := 𝓞 F ⧸ p.asIdeal
  letI : Field k := Ideal.Quotient.field p.asIdeal
  letI : Fintype k := Fintype.ofFinite _
  have hcard : Fintype.card k = p.asIdeal.absNorm := (Nat.card_eq_fintype_card (α := k)).symm
  have hq : (p.asIdeal.absNorm : k) = 0 := hcard ▸ Nat.cast_card_eq_zero k
  have hn := (ne_zero_or_ne_zero_of_nat_coprime (A := k) hp).resolve_left (not_not.mpr hq)
  exact hn (by simpa only [map_natCast] using (Ideal.Quotient.eq_zero_iff_mem.mpr h))

private theorem integerUnit_of_norm_one (u : Cˣ) (hu : ‖u.val‖ = 1) :
    ∃ U : 𝒪[C]ˣ, integerUnitsToFieldUnits C U = u := by
  apply (integerUnitsToFieldUnits_mem_range_iff_valuationMap_eq_zero C u).mpr
  have hv := (valuation_eq_iff_norm_eq p u.val 1).mpr (hu.trans norm_one.symm)
  rw [map_one] at hv
  rw [valuationMap_apply]
  simp [IsNonarchimedeanLocalField.v,hv]
  rfl

private theorem tameLift_norm (n : ℕ+) (hn : ValuativeRel.valuation C ((n : ℕ) : C) = 1)
    (hmu : (primitiveRoots (n : ℕ) C).Nonempty) (U : 𝒪[C]ˣ) :
    let z := localTamePowerResidueSymbol C n hn hmu U
    ‖(z.val : C) - (integerUnitsToFieldUnits C U : C) ^ ((p.asIdeal.absNorm - 1) / (n : ℕ))‖ < 1 := by
  let z := localTamePowerResidueSymbol C n hn hmu U
  let Z := nthRootIntegerUnit C n z
  let j := (p.asIdeal.absNorm - 1) / (n : ℕ)
  letI : Fintype 𝓀[C] := Fintype.ofFinite _
  have he := congrArg (fun z : rootsOfUnity (n : ℕ) 𝓀[C] => (z.val : 𝓀[C]))
    (localNthRootsReductionEquiv_localTamePowerResidueSymbol C n hn hmu U)
  change IsLocalRing.residue 𝒪[C] Z.val =
    IsLocalRing.residue 𝒪[C] U.val ^ ((Fintype.card 𝓀[C] - 1) / (n : ℕ)) at he
  rw [← Nat.card_eq_fintype_card,residueCard p] at he
  have hr : IsLocalRing.residue 𝒪[C] (Z.val - U.val ^ j) = 0 := by
    rw [map_sub,map_pow,sub_eq_zero]
    exact he
  have hv := (Valuation.mem_maximalIdeal_iff C (ValuativeRel.valuation C)).mp
    ((IsLocalRing.residue_eq_zero_iff _).mp hr)
  rw [← (ValuativeRel.valuation C).map_one] at hv
  exact ((valuation_lt_iff_norm_lt p _ _).mp hv).trans_le (norm_one.le)


private abbrev compEquiv := (relativeFinitePlaceCompletionAlgEquiv p).toRingEquiv

private theorem norm_compEquiv (x : C) : ‖compEquiv p x‖ = ‖x‖ :=
  relativeFinitePlaceCompletionRingEquiv_norm p x

variable (n : ℕ+) {ζ : F} (hζ : IsPrimitiveRoot ζ (n : ℕ))

include hζ in
private theorem source_hasRoots : (primitiveRoots (n : ℕ) C).Nonempty :=
  ⟨algebraMap F C ζ,(mem_primitiveRoots n.pos).2
    (hζ.map_of_injective (algebraMap F C).injective)⟩

private theorem finiteValue_image (a b : Cˣ)
    (hn : ((n : ℕ) : C) ≠ 0) (hm : (primitiveRoots (n : ℕ) C).Nonempty) :
    algebraMap F D ((finiteValue n hζ p (Units.mapEquiv (compEquiv p).toMulEquiv a)
      (Units.mapEquiv (compEquiv p).toMulEquiv b)).val : F) =
    compEquiv p (((ClassFieldTheory.localHilbertSymbol C n hn hm a b)⁻¹).val : C) := by
  let hF : (primitiveRoots (n : ℕ) F).Nonempty := ⟨ζ,(mem_primitiveRoots n.pos).2 hζ⟩
  let e := compEquiv p
  let eCD := rootsOfUnityEquivOfRingEquiv e n hm
  let A := Units.mapEquiv e.toMulEquiv a
  let B := Units.mapEquiv e.toMulEquiv b
  let z := finitePlaceAdicHilbertPairingFamily F n hF p (powerClass D n A) (powerClass D n B)
  have hz : z = eCD (ClassFieldTheory.localHilbertSymbol C n hn hm a b) := by
    change hilbertPairingOfRingEquiv e n hm (ClassFieldTheory.localHilbertPairing C n hn hm)
      (powerClass D n A) (powerClass D n B) = _
    rw [hilbertPairingOfRingEquiv_apply,powerClassGroupEquivOfRingEquiv_symm_powerClass,
      powerClassGroupEquivOfRingEquiv_symm_powerClass]
    simp only [A,B,MulEquiv.symm_apply_apply,ClassFieldTheory.localHilbertPairing_powerClass]
    rfl
  letI : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  have h := rootsOfUnityEquivOfPrimitiveRoots_symm_apply (algebraMap F D).injective hF z⁻¹
  refine h.trans ?_
  rw [hz,← eCD.map_inv]
  rfl

/-- Tame uniformizer normalization for the actual transported global
family, on arbitrary units of the adic completion. -/
theorem finiteValue_tame_uniformizer (hp : p.asIdeal.absNorm.Coprime (n : ℕ))
    (π u : Dˣ) (hπ : ‖π.val‖ = (p.asIdeal.absNorm : ℝ)⁻¹) (hu : ‖u.val‖ = 1) :
    ‖algebraMap F D ((finiteValue n hζ p π u).val : F) -
      u.val ^ ((p.asIdeal.absNorm - 1) / (n : ℕ))‖ < 1 := by
  let e := compEquiv p
  obtain ⟨x,rfl⟩ := (Units.mapEquiv e.toMulEquiv).surjective π
  obtain ⟨y,rfl⟩ := (Units.mapEquiv e.toMulEquiv).surjective u
  have hx := (norm_compEquiv p x.val).symm.trans hπ
  have hy := (norm_compEquiv p y.val).symm.trans hu
  obtain ⟨U,hU⟩ := integerUnit_of_norm_one p y hy
  let hn := degree_valuation p n hp
  let hm := source_hasRoots p n hζ
  let hn₀ := natCast_ne_zero_of_valuation_eq_one C n hn
  rw [finiteValue_image p n hζ x y hn₀ hm]
  change ‖e _ - e y.val ^ _‖ < 1
  rw [← map_pow,← map_sub,norm_compEquiv,← hU]
  rw [← ClassFieldTheory.localHilbertSymbol_skew]
  unfold ClassFieldTheory.localHilbertSymbol
  rw [localHilbertSymbol_tame_formula C n hn hm U x,valuationMap_of_uniformizer_norm p x hx,neg_neg,zpow_one]
  exact tameLift_norm p n hn hm U



private theorem finiteValue_eq_one_of_source (a b : Cˣ)
    (hn : ((n : ℕ) : C) ≠ 0) (hm : (primitiveRoots (n : ℕ) C).Nonempty)
    (h : LocalClassFieldTheory.Kummer.localHilbertSymbol C n hn hm a b = 1) :
    finiteValue n hζ p (Units.mapEquiv (compEquiv p).toMulEquiv a)
      (Units.mapEquiv (compEquiv p).toMulEquiv b) = 1 := by
  apply Subtype.ext
  apply Units.ext
  apply (algebraMap F D).injective
  rw [finiteValue_image p n hζ a b hn hm]
  have hone : ClassFieldTheory.localHilbertSymbol C n hn hm a b = 1 :=
    (congrArg (nthRootsSubgroupEquivRootsOfUnity C (n : ℕ)) h).trans (map_one _)
  rw [hone,inv_one]
  exact (compEquiv p).map_one.trans (algebraMap F D).map_one.symm

/-- Tame unit–unit normalization, including nonrational local units. -/
theorem finiteValue_tame_units (hp : p.asIdeal.absNorm.Coprime (n : ℕ)) (a b : Dˣ)
    (ha : ‖a.val‖ = 1) (hb : ‖b.val‖ = 1) : finiteValue n hζ p a b = 1 := by
  let e := compEquiv p
  obtain ⟨x,rfl⟩ := (Units.mapEquiv e.toMulEquiv).surjective a
  obtain ⟨y,rfl⟩ := (Units.mapEquiv e.toMulEquiv).surjective b
  obtain ⟨U,hU⟩ := integerUnit_of_norm_one p x ((norm_compEquiv p x.val).symm.trans ha)
  obtain ⟨V,hV⟩ := integerUnit_of_norm_one p y ((norm_compEquiv p y.val).symm.trans hb)
  let hn := degree_valuation p n hp
  let hm := source_hasRoots p n hζ
  apply finiteValue_eq_one_of_source p n hζ x y (natCast_ne_zero_of_valuation_eq_one C n hn) hm
  rw [← hU,← hV]
  exact localHilbertSymbol_integerUnit_integerUnit_eq_one C n hn hm U V

/-- The relation on a unit and its negative also holds at wild places. -/
theorem finiteValue_neg_self (a : Dˣ) : finiteValue n hζ p a (-a) = 1 := by
  let e := compEquiv p
  obtain ⟨x,rfl⟩ := (Units.mapEquiv e.toMulEquiv).surjective a
  have neg : -(Units.mapEquiv e.toMulEquiv x) = Units.mapEquiv e.toMulEquiv (-x) :=
    Units.ext (e.map_neg x.val).symm
  rw [neg]
  letI : CharZero C := charZero_of_injective_algebraMap (algebraMap F C).injective
  have hn : ((n : ℕ) : C) ≠ 0 := Nat.cast_ne_zero.mpr n.ne_zero
  exact finiteValue_eq_one_of_source p n hζ x (-x) hn (source_hasRoots p n hζ)
    (localHilbertSymbol_neg_self C n hn (source_hasRoots p n hζ) x)


end MetaplecticPoisson.Hilbert
