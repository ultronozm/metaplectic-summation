import MetaplecticSummation.PowerHaar

/-! Sums over the n-th roots of the integration variable. Under the power map the
multiplicative Haar measure pushes forward to a multiple of its restriction to the
open subgroup of powers. The root sum is continuous there, because the power map is
proper onto that subgroup, and its integral is the normalized modulus of n times the
integral of the summand. The additive form gives the change of variables z = τⁿ. -/

noncomputable section
open MeasureTheory Set Filter Polynomial
open scoped Topology ENNReal NNReal
open Classical
namespace MetaplecticPoisson

section Core
variable {K : Type*} [NormedField K] [ProperSpace K] [MeasurableSpace K] [BorelSpace K]
  {n : ℕ} [NeZero n]

omit [ProperSpace K] [MeasurableSpace K] [BorelSpace K] in
/-- The n-th roots of an n-th power are its multiples by the n-th roots of one. -/
theorem nthRootsFinset_pow_eq_image' (u : Kˣ) :
    nthRootsFinset n (u.val^n) = (nthRootsFinset n (1 : K)).image (· * u.val) := by
  ext r
  simp only [mem_nthRootsFinset (NeZero.pos n),Finset.mem_image]
  constructor
  · intro hr
    refine ⟨r * u.val⁻¹,?_,by field_simp [u.ne_zero]⟩
    rw [mul_pow,hr,inv_pow,mul_inv_cancel₀ (pow_ne_zero _ u.ne_zero)]
  · rintro ⟨ζ,hζ,rfl⟩
    rw [mul_pow,hζ,one_mul]

omit [MeasurableSpace K] [BorelSpace K] in
/-- A sum over the n-th roots of a unit vanishes off the subgroup of powers and
is continuous on it. -/
theorem rootSum_continuousOn {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [ContinuousAdd E]
    (hP : IsOpen ((powMonoidHom n : Kˣ →* Kˣ).range : Set Kˣ)) {g : K → E} (hg : ContinuousOn g {0}ᶜ) :
    ContinuousOn (fun z : Kˣ => ∑ r ∈ nthRootsFinset n z.val, g r)
        ((powMonoidHom n : Kˣ →* Kˣ).range : Set Kˣ) ∧
      ∀ z ∉ ((powMonoidHom n : Kˣ →* Kˣ).range : Set Kˣ), ∑ r ∈ nthRootsFinset n z.val, g r = 0 := by
  let P := (powMonoidHom n : Kˣ →* Kˣ).range
  let R := nthRootsFinset n (1 : K)
  have hR (ζ : K) (hζ : ζ ∈ R) : ζ ≠ 0 := by
    intro h
    rw [mem_nthRootsFinset (NeZero.pos n),h,zero_pow (NeZero.ne n)] at hζ
    exact zero_ne_one hζ
  have hpow (u : Kˣ) : ∑ r ∈ nthRootsFinset n (u^n).val, g r = ∑ ζ ∈ R, g (ζ * u.val) := by
    rw [Units.val_pow_eq_pow_val,nthRootsFinset_pow_eq_image' u,Finset.sum_image]
    intro a _ b _ hab
    exact mul_right_cancel₀ u.ne_zero hab
  let : LocallyCompactSpace P := hP.locallyCompactSpace
  constructor
  · let f := (powMonoidHom n : Kˣ →* Kˣ).rangeRestrict
    have hfc : Continuous f := (continuous_id.pow n : Continuous (fun x : Kˣ => x^n)).subtype_mk _
    have hq : Topology.IsQuotientMap f := by
      have hp : IsProperMap f := isProperMap_iff_tendsto_cocompact.mpr
        ⟨hfc,unitPower_proper n (NeZero.ne n)⟩
      exact hp.isClosedMap.isQuotientMap hfc (MonoidHom.rangeRestrict_surjective _)
    have hsum_cont : Continuous (fun u : Kˣ => ∑ ζ ∈ R, g (ζ * u.val)) := by
      refine continuous_finsetSum _ fun ζ hζ => ?_
      exact hg.comp_continuous (continuous_const.mul Units.continuous_val)
        (fun u => mul_ne_zero (hR ζ hζ) u.ne_zero)
    rw [continuousOn_iff_continuous_domRestrict]
    apply hq.continuous_iff.mpr
    convert hsum_cont using 1
    funext u
    exact hpow u
  · intro z hz
    apply Finset.sum_eq_zero
    intro r hr
    exfalso
    rw [mem_nthRootsFinset (NeZero.pos n)] at hr
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [zero_pow (NeZero.ne n)] at hr
      exact z.ne_zero hr.symm
    exact hz ⟨Units.mk0 r hr0,Units.ext (by simpa using hr)⟩

variable (ν : Measure Kˣ) [ν.IsMulLeftInvariant] (c : ℝ≥0)
  (hmap : ν.map (fun x : Kˣ => x^n) = c • ν.restrict ((powMonoidHom n : Kˣ →* Kˣ).range : Set Kˣ))
  (hcard : (nthRootsFinset n (1 : K)).card = n)
  (hP : IsOpen ((powMonoidHom n : Kˣ →* Kˣ).range : Set Kˣ))
include hmap hcard hP

/-- The Lebesgue form of the root-sum formula. -/
theorem lintegral_rootSum {g : K → ℝ≥0∞} (hg : ContinuousOn g {0}ᶜ) :
    c * ∫⁻ z, ∑ r ∈ nthRootsFinset n z.val, g r ∂ν = n * ∫⁻ u, g u.val ∂ν := by
  let P := (powMonoidHom n : Kˣ →* Kˣ).range
  let G (z : Kˣ) := ∑ r ∈ nthRootsFinset n z.val, g r
  obtain ⟨hGc,hG0⟩ := rootSum_continuousOn hP hg
  have hGm : Measurable G := by
    have he : (P : Set Kˣ).piecewise G 0 = G := by
      funext z
      by_cases hz : z ∈ (P : Set Kˣ)
      · simp [hz]
      · simp [hz,G,hG0 z hz]
    rw [← he]
    exact hGc.measurable_piecewise continuousOn_const hP.measurableSet
  let R := nthRootsFinset n (1 : K)
  have hR (ζ : K) (hζ : ζ ∈ R) : ζ ≠ 0 := by
    intro h
    rw [mem_nthRootsFinset (NeZero.pos n),h,zero_pow (NeZero.ne n)] at hζ
    exact zero_ne_one hζ
  have hpow (u : Kˣ) : G (u^n) = ∑ ζ ∈ R, g (ζ * u.val) := by
    simp only [G,Units.val_pow_eq_pow_val]
    rw [nthRootsFinset_pow_eq_image' u,Finset.sum_image]
    intro a _ b _ hab
    exact mul_right_cancel₀ u.ne_zero hab
  have gm : Measurable (fun u : Kˣ => g u.val) :=
    (hg.comp_continuous Units.continuous_val (fun u => u.ne_zero)).measurable
  have key := lintegral_map (μ := ν) hGm (continuous_pow n).measurable
  rw [hmap,lintegral_smul_measure] at key
  have hres : (∫⁻ z in (P : Set Kˣ), G z ∂ν) = ∫⁻ z, G z ∂ν := by
    rw [← lintegral_indicator hP.measurableSet]
    congr 1; funext z
    by_cases hz : z ∈ (P : Set Kˣ)
    · rw [indicator_of_mem hz]
    · rw [indicator_of_notMem hz]; exact (hG0 z hz).symm
  rw [hres] at key
  rw [ENNReal.smul_def,smul_eq_mul] at key
  change c * ∫⁻ z, G z ∂ν = _
  rw [key]
  simp_rw [hpow]
  rw [lintegral_finsetSum R (f := fun ζ (u : Kˣ) => g (ζ * u.val)) (fun ζ hζ =>
    (hg.comp_continuous (continuous_const.mul Units.continuous_val)
      (fun u => mul_ne_zero (hR ζ hζ) u.ne_zero)).measurable)]
  have hrot (ζ : K) (hζ : ζ ∈ R) : (∫⁻ u, g (ζ * u.val) ∂ν) = ∫⁻ u, g u.val ∂ν := by
    simpa only [Units.val_mul,Units.val_mk0] using
      lintegral_mul_left_eq_self (fun u : Kˣ => g u.val) (Units.mk0 ζ (hR ζ hζ))
  rw [Finset.sum_congr rfl hrot,Finset.sum_const,hcard,nsmul_eq_mul]

/-- The Bochner form of the root-sum formula, with integrability of the root sum. -/
theorem integral_rootSum (hc : 0 < c) {Θ : K → ℂ} (hΘ : ContinuousOn Θ {0}ᶜ)
    (hi : Integrable (fun u : Kˣ => Θ u.val) ν) :
    Integrable (fun z : Kˣ => ∑ r ∈ nthRootsFinset n z.val, Θ r) ν ∧
      ((c : ℝ) : ℂ) * ∫ z, ∑ r ∈ nthRootsFinset n z.val, Θ r ∂ν = n * ∫ u, Θ u.val ∂ν := by
  let P := (powMonoidHom n : Kˣ →* Kˣ).range
  let G (z : Kˣ) := ∑ r ∈ nthRootsFinset n z.val, Θ r
  obtain ⟨hGc,hG0⟩ := rootSum_continuousOn hP hΘ
  have hGm : Measurable G := by
    have he : (P : Set Kˣ).piecewise G 0 = G := by
      funext z
      by_cases hz : z ∈ (P : Set Kˣ)
      · simp [hz]
      · simp only [Set.piecewise_eq_of_notMem _ _ _ hz,Pi.zero_apply]; exact (hG0 z hz).symm
    rw [← he]
    exact hGc.measurable_piecewise continuousOn_const hP.measurableSet
  have hnorm : ContinuousOn (fun r : K => ‖Θ r‖ₑ) {0}ᶜ := hΘ.enorm
  have hlin := lintegral_rootSum ν c hmap hcard hP hnorm
  have hint : Integrable G ν := by
    refine ⟨hGm.aestronglyMeasurable,?_⟩
    have hle : (∫⁻ z, ‖G z‖ₑ ∂ν) ≤ ∫⁻ z, ∑ r ∈ nthRootsFinset n z.val, ‖Θ r‖ₑ ∂ν :=
      lintegral_mono fun z => enorm_sum_le _ _
    have hfin : (∫⁻ z, ∑ r ∈ nthRootsFinset n z.val, ‖Θ r‖ₑ ∂ν) < ∞ := by
      have hc0 : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc.ne'
      have h2 : (c : ℝ≥0∞) * ∫⁻ z, ∑ r ∈ nthRootsFinset n z.val, ‖Θ r‖ₑ ∂ν < ∞ := by
        rw [hlin]; exact ENNReal.mul_lt_top (by simp) hi.2
      exact (ENNReal.mul_lt_top_iff.mp h2).elim (fun h => h.2)
        (fun h => h.elim (fun h' => absurd h' hc0) (fun h' => by rw [h']; exact ENNReal.zero_lt_top))
    exact hle.trans_lt hfin
  refine ⟨hint,?_⟩
  let R := nthRootsFinset n (1 : K)
  have hR (ζ : K) (hζ : ζ ∈ R) : ζ ≠ 0 := by
    intro h
    rw [mem_nthRootsFinset (NeZero.pos n),h,zero_pow (NeZero.ne n)] at hζ
    exact zero_ne_one hζ
  have hpow (u : Kˣ) : G (u^n) = ∑ ζ ∈ R, Θ (ζ * u.val) := by
    simp only [G,Units.val_pow_eq_pow_val]
    rw [nthRootsFinset_pow_eq_image' u,Finset.sum_image]
    intro a _ b _ hab
    exact mul_right_cancel₀ u.ne_zero hab
  have key := integral_map (φ := fun x : Kˣ => x^n) (μ := ν) (continuous_pow n).aemeasurable
    hGm.aestronglyMeasurable
  rw [hmap,integral_smul_nnreal_measure] at key
  have hres : (∫ z, G z ∂ν.restrict (P : Set Kˣ)) = ∫ z, G z ∂ν :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hG0
  have hrot (ζ : K) (hζ : ζ ∈ R) : (∫ u, Θ (ζ * u.val) ∂ν) = ∫ u, Θ u.val ∂ν :=
    integral_mul_left_eq_self (fun u : Kˣ => Θ u.val) (Units.mk0 ζ (hR ζ hζ))
  have hsum : (∫ u, G (u^n) ∂ν) = n * ∫ u, Θ u.val ∂ν := by
    simp_rw [hpow]
    rw [integral_finsetSum _ (fun ζ hζ => by
      simpa only [Units.val_mul,Units.val_mk0] using
        (hi.comp_mul_left (Units.mk0 ζ (hR ζ hζ))))]
    rw [Finset.sum_congr rfl hrot,Finset.sum_const,hcard,nsmul_eq_mul]
  rw [hres,hsum,NNReal.smul_def,Complex.real_smul] at key
  exact key

end Core

namespace Datum
open NumberField
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n) (v : Place F)
local notation "Kv" => LocalField F v

private theorem place_proper : ProperSpace Kv := by
  cases v with
  | inl w =>
    let : LocallyCompactSpace (LocalField F (.inl w)) := inferInstanceAs (LocallyCompactSpace w.Completion)
    let := archNontriviallyNormedCompletion w
    exact .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace (LocalField F (.inl w))
  | inr p =>
    let := FinitePlace.nontriviallyNormedCompletion p
    exact .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace (p.adicCompletion F)

private theorem place_powers_open : IsOpen ((powMonoidHom n : Kvˣ →* Kvˣ).range : Set Kvˣ) := by
  cases v with
  | inl w =>
    let : NontriviallyNormedField w.Completion := { (inferInstance : NormedField w.Completion) with
      non_trivial := (archNontriviallyNormedCompletion w).non_trivial }
    let : CharZero w.Completion := charZero_of_injective_ringHom (algebraMap F w.Completion).injective
    exact isOpen_unit_powers (K := w.Completion) n (Nat.cast_ne_zero.mpr (NeZero.ne n))
  | inr p =>
    let := FinitePlace.nontriviallyNormedCompletion p
    let : CharZero (p.adicCompletion F) := charZero_of_injective_ringHom (diagonal F (.inr p)).injective
    exact isOpen_unit_powers (K := p.adicCompletion F) n (Nat.cast_ne_zero.mpr (NeZero.ne n))

/-- Summing over the n-th roots of the integration variable multiplies the integral
over the units by the normalized modulus of n, at every place. -/
theorem lineIntegral_rootSum (Θ : Kv → ℂ) (hc : ContinuousOn Θ {0}ᶜ)
    (hi : Integrable (fun u : Kvˣ => Θ u.val) (d.lineMeasure v)) :
    Integrable (fun z : Kvˣ => ∑ r ∈ nthRootsFinset n z.val, Θ r) (d.lineMeasure v) ∧
    (∫ z : Kvˣ, ∑ r ∈ nthRootsFinset n z.val, Θ r ∂(d.lineMeasure v)) =
      (modulus F v (n : Kv) : ℂ) * ∫ u : Kvˣ, Θ u.val ∂(d.lineMeasure v) := by
  let := place_proper (F := F) v
  have hP := place_powers_open (F := F) (n := n) v
  have hnK : (n : Kv) ≠ 0 := by
    have hnz := (diagonal F v).injective.ne (Nat.cast_ne_zero.mpr (NeZero.ne n) : (n:F) ≠ 0)
    simpa only [map_natCast,map_zero] using hnz
  have hmap := d.map_lineMeasure_pow v
  have hcard : (nthRootsFinset n (1 : Kv)).card = n :=
    (d.primitive.map_of_injective (diagonal F v).injective).card_nthRootsFinset
  have hmn : 0 < modulus F v (n : Kv) := by
    cases v <;> simp [modulus,norm_pos_iff.mpr hnK,pow_pos]
  let c := ((n : ℝ) / modulus F v (n : Kv)).toNNReal
  have hcpos : 0 < c := Real.toNNReal_pos.mpr (div_pos (by exact_mod_cast NeZero.pos n) hmn)
  obtain ⟨hint,key⟩ := integral_rootSum (d.lineMeasure v) c hmap hcard hP hcpos hc hi
  refine ⟨hint,?_⟩
  have hc' : ((c : ℝ) : ℂ) = (n : ℂ) / (modulus F v (n : Kv) : ℂ) := by
    simp only [c]; rw [Real.coe_toNNReal _ (by positivity)]; push_cast; rfl
  rw [hc'] at key
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hm0 : (modulus F v (n : Kv) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hmn.ne'
  field_simp at key
  linear_combination key

local notation "dx" => selfDual F d.character v

/-- Change of variables z = τⁿ for the additive self-dual measure at every place. -/
theorem integral_pow_change {g h : Kv → ℂ} (hg : ContinuousOn g {0}ᶜ) (hh : ContinuousOn h {0}ᶜ)
    (hi : Integrable (fun τ => h (τ^n) * g τ) dx) :
    Integrable (fun z => h z * ∑ τ ∈ nthRootsFinset n z, g τ * (modulus F v τ : ℂ)^(1-(n:ℤ))) dx ∧
    (∫ z, h z * ∑ τ ∈ nthRootsFinset n z, g τ * (modulus F v τ : ℂ)^(1-(n:ℤ)) ∂dx) =
      (modulus F v (n : Kv) : ℂ) * ∫ τ, h (τ^n) * g τ ∂dx := by
  let m := modulus F v
  have hm (x : Kv) (hx : x ≠ 0) : 0 < m x := by cases v <;> simp [m,modulus,norm_pos_iff.mpr hx,pow_pos]
  have mpow (x : Kv) : m (x^n) = m x ^ n := by cases v <;> simp [m,modulus,norm_pow,← pow_mul,mul_comm]
  have mc : Continuous m := by
    show Continuous (modulus F v)
    cases v with
    | inl w => exact continuous_norm.pow _
    | inr p => exact continuous_norm
  let Θ (τ : Kv) : ℂ := (m τ : ℂ) * (h (τ^n) * g τ)
  have hΘc : ContinuousOn Θ {0}ᶜ := by
    refine (Complex.continuous_ofReal.comp mc).continuousOn.mul ((hh.comp (continuous_pow n).continuousOn ?_).mul hg)
    intro τ hτ; exact pow_ne_zero n hτ
  have hΘi : Integrable (fun u : Kvˣ => Θ u.val) (d.lineMeasure v) := by
    have := (d.lineMeasure_modulus v (fun τ => h (τ^n) * g τ)).1.mpr hi
    refine this.congr (.of_forall fun u => ?_)
    simp only [Θ,Complex.real_smul]
    rfl
  obtain ⟨hint,heq⟩ := d.lineIntegral_rootSum v Θ hΘc hΘi
  have hpt (z : Kvˣ) : (m z.val : ℂ) * (h z.val * ∑ τ ∈ nthRootsFinset n z.val, g τ * (m τ : ℂ)^(1-(n:ℤ))) =
      ∑ τ ∈ nthRootsFinset n z.val, Θ τ := by
    rw [Finset.mul_sum,Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ hτ => ?_
    have hτn := (mem_nthRootsFinset (NeZero.pos n) _).mp hτ
    have hτ0 : τ ≠ 0 := by rintro rfl; rw [zero_pow (NeZero.ne n)] at hτn; exact z.ne_zero hτn.symm
    have hmτ : (m τ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hm τ hτ0).ne'
    have hz : (m z.val : ℂ) = (m τ : ℂ)^n := by rw [← hτn,mpow]; push_cast; rfl
    simp only [Θ,hτn,hz]
    rw [show (1 : ℤ) - n = -((n:ℤ) - 1) by ring,zpow_neg,show ((n:ℤ) - 1) = ((n-1 : ℕ) : ℤ) by
      rw [Nat.cast_sub (NeZero.one_le)]; rfl,zpow_natCast]
    have e : (m τ : ℂ)^n = (m τ : ℂ) * (m τ : ℂ)^(n-1) := by
      rw [← pow_succ',Nat.sub_add_cancel (NeZero.one_le)]
    rw [e]
    field_simp
  have hF := d.lineMeasure_modulus v
    (fun z => h z * ∑ τ ∈ nthRootsFinset n z, g τ * (m τ : ℂ)^(1-(n:ℤ)))
  dsimp only at hF
  have hcongr : (fun u : Kvˣ => m u.val • (h u.val * ∑ τ ∈ nthRootsFinset n u.val, g τ * (m τ : ℂ)^(1-(n:ℤ)))) =
      fun u => ∑ τ ∈ nthRootsFinset n u.val, Θ τ := by
    funext u; rw [Complex.real_smul]; exact hpt u
  rw [hcongr] at hF
  refine ⟨hF.1.mp hint,?_⟩
  rw [← hF.2,heq,← (d.lineMeasure_modulus v (fun τ => h (τ^n) * g τ)).2]
  congr 1

end Datum
end MetaplecticPoisson
