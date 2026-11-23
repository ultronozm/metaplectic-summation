import MetaplecticSummation.PowerClassFourier

/-! The unramified test in the multiplicative Poisson formula of Appendix B. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open Classical NumberField IsDedekindDomain
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)
variable (p : HeightOneSpectrum (𝓞 F))
local notation "v" => (Sum.inr p : Place F)
local notation "G" => PowerClass n v

/-- The image of the integral units in the local power classes. -/
def integralUnitClasses (n : ℕ) : Subgroup (PowerClass n v) :=
  (integralUnits p).map (QuotientGroup.mk' (powMonoidHom n : (LocalField F v)ˣ →* _).range)

/-- The tame integral unit classes form their own annihilator. -/
theorem integralUnitClasses_orthogonal (ht : p.asIdeal.absNorm.Coprime n) (c : G) :
    (∀ a ∈ integralUnitClasses p n, d.localClassPairing v a c = 1) ↔ c ∈ integralUnitClasses p n := by
  constructor
  · induction c using QuotientGroup.induction_on with | _ c => _
    intro h
    obtain ⟨t,htn⟩ : ∃ t : (LocalField F v)ˣ, ‖c.val‖ = ‖t.val‖^n := d.norm_power_of_trivial_on_units p ht c (by
      intro u hu
      have he := h (QuotientGroup.mk u) ⟨u,hu,rfl⟩
      rw [d.localClassPairing_skew,inv_eq_one] at he
      exact congrArg Units.val he)
    refine ⟨c/t^n,?_,?_⟩
    · change ‖(c/t^n).val‖ = 1
      rw [Units.val_div_eq_div_val,Units.val_pow_eq_pow_val,norm_div,norm_pow,htn,div_self]
      exact pow_ne_zero n (norm_ne_zero_iff.mpr t.ne_zero)
    · change QuotientGroup.mk' _ (c/t^n) = _
      rw [map_div,show (QuotientGroup.mk' _ (t^n) : G) = 1 from (QuotientGroup.eq_one_iff _).mpr ⟨t,rfl⟩,div_one]
      rfl
  · rintro ⟨b,hb,rfl⟩ _ ⟨a,ha,rfl⟩
    exact d.unitPairing_tame_units p ht a b ha hb

/-- Characteristic function of the image of the integral units. -/
def unitClassTest (n : ℕ) (c : PowerClass n v) : ℂ :=
  if c ∈ integralUnitClasses p n then 1 else 0

private theorem powerClassTransform_unit_multiple (ht : p.asIdeal.absNorm.Coprime n) (y : G) :
    d.powerClassTransform v (unitClassTest p n) y =
      ((n : ℂ)⁻¹ * Nat.card (integralUnitClasses p n)) * unitClassTest p n y := by
  let := finite_power_classes (n := n) v
  letI := Fintype.ofFinite G
  let H := integralUnitClasses p n
  let χ := ((Units.coeHom ℂ).comp ((d.localClassPairing v).flip y)).comp H.subtype
  have hh : χ = 1 ↔ y ∈ H := by
    rw [← d.integralUnitClasses_orthogonal p ht]
    constructor
    · intro h a ha
      exact Units.ext (DFunLike.congr_fun h (⟨a,ha⟩ : H))
    · intro h
      exact MonoidHom.ext fun a => congrArg Units.val (h a a.property)
  let f (a : G) := (d.localClassPairing v a y : ℂ) * unitClassTest p n a
  have hs := (Fintype.sum_subtype_add_sum_subtype (· ∈ H) f).symm
  have hy : (∑ a : G, f a) = ∑ a : H, χ a := by
    rw [hs]
    have h₁ (a : H) : f a.val = χ a := by
      change _ * (if a.val ∈ H then 1 else 0) = _
      rw [if_pos a.property,mul_one]
      rfl
    have h₀ (a : {a : G // a ∉ H}) : f a.val = 0 := by
      change _ * (if a.val ∈ H then 1 else 0) = _
      rw [if_neg a.property,mul_zero]
    simp only [h₁,h₀,Finset.sum_const_zero,add_zero]
  rw [powerClassTransform,finsum_eq_sum_of_fintype]
  change _ * (∑ a : G, f a) = _
  rw [hy,sum_hom_units χ]
  by_cases h : y ∈ H
  · simp [hh.mpr h,unitClassTest,show y ∈ integralUnitClasses p n from h,Nat.card_eq_fintype_card,H]
  · simp [mt hh.mp h,unitClassTest,show y ∉ integralUnitClasses p n from h]

/-- The tame local factor of Lemma B.3 is fixed by the paper's transform. -/
theorem powerClassTransform_unitClassTest (ht : p.asIdeal.absNorm.Coprime n) :
    d.powerClassTransform v (unitClassTest p n) = unitClassTest p n := by
  let A := Nat.card (integralUnitClasses p n)
  let k : ℂ := (n : ℂ)⁻¹ * A
  have h : d.powerClassTransform v (unitClassTest p n) = fun y => k * unitClassTest p n y :=
    funext (d.powerClassTransform_unit_multiple p ht)
  have h₁ : unitClassTest p n 1 = 1 := if_pos (integralUnitClasses p n).one_mem
  have hmod : modulus F v (n : LocalField F v) = 1 := FinitePlace.norm_degree_of_tame p ht
  have H := d.modulus_mul_powerClassTransform_square v (unitClassTest p n) 1
  rw [hmod,Complex.ofReal_one,one_mul,h,d.powerClassTransform_const_mul,h] at H
  change k * (k * unitClassTest p n 1) = unitClassTest p n 1 at H
  rw [h₁,mul_one] at H
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hc : (A : ℂ)^2 = (n : ℂ)^2 := by
    dsimp [k] at H
    field_simp at H
    linear_combination H
  have e : A = n := by
    have ha : A^2 = n^2 := by exact_mod_cast hc
    exact Nat.pow_left_injective (by decide : 2 ≠ 0) ha
  have hk : k = 1 := by simp [k,e,hn]
  rw [h,hk]
  simp

/-- The local transforms preserve the restricted-product condition on the
test family in the global power-class Poisson formula. -/
theorem eventually_powerClassTransform_unitClassTest (β : (w : Place F) → PowerClass n w → ℂ)
    (hβ : ∀ᶠ q : HeightOneSpectrum (𝓞 F) in Filter.cofinite, β (.inr q) = unitClassTest q n) :
    ∀ᶠ q : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      d.powerClassTransform (.inr q) (β (.inr q)) = unitClassTest q n := by
  filter_upwards [hβ,eventually_tame (F := F) (n := n)] with q he ht
  rw [he,d.powerClassTransform_unitClassTest q ht]

end MetaplecticPoisson.Datum
