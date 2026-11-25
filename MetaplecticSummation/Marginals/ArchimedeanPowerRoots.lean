import MetaplecticSummation.PowerHaar
import MetaplecticSummation.Marginals.Basic
import MetaplecticSummation.RadonConvergence

/-! Change of variables by the power map at real and complex places. Summing a
function over the n-th roots of the integration variable multiplies its
multiplicative integral by the normalized modulus of n. The root sum is continuous
on the open subgroup of powers, because the power map is proper onto it. -/

noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField MeasureTheory Set Filter Polynomial
open scoped Topology
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n) (w : InfinitePlace F)
local notation "v" => (Sum.inl w : Place F)
local notation "K" => LocalField F v

omit [NumberField F] [NeZero n] in
/-- The n-th roots of an n-th power are its multiples by the n-th roots of one. -/
theorem nthRootsFinset_pow_eq_image {L : Type*} [Field L] (hn : 0 < n) (u : Lˣ) :
    nthRootsFinset n (u.val^n) = (nthRootsFinset n (1 : L)).image (· * u.val) := by
  ext r
  simp only [mem_nthRootsFinset hn,Finset.mem_image]
  constructor
  · intro hr
    refine ⟨r * u.val⁻¹,?_,by field_simp [u.ne_zero]⟩
    rw [mul_pow,hr,inv_pow,mul_inv_cancel₀ (pow_ne_zero _ u.ne_zero)]
  · rintro ⟨ζ,hζ,rfl⟩
    rw [mul_pow,hζ,one_mul]

omit [NeZero n] in
include d in
/-- At an infinite place there are exactly n roots of one. -/
theorem arch_card_roots_one : (nthRootsFinset n (1 : K)).card = n :=
  (d.primitive.map_of_injective (diagonal F v).injective).card_nthRootsFinset

/-- Summing over the n-th roots of the integration variable multiplies the integral
over the units by the normalized modulus of n, at every infinite place. -/
theorem arch_lineIntegral_root_sum (Θ : K → ℂ) (hc : ContinuousOn Θ {0}ᶜ)
    (hi : Integrable (fun u : Kˣ => Θ u.val) (d.lineMeasure v)) :
    (∫ z : Kˣ, ∑ r ∈ nthRootsFinset n z.val, Θ r ∂(d.lineMeasure v)) =
      (modulus F v (n : K) : ℂ) * ∫ u : Kˣ, Θ u.val ∂(d.lineMeasure v) := by
  let ν := d.lineMeasure v
  let : LocallyCompactSpace K := inferInstanceAs (LocallyCompactSpace w.Completion)
  let : NontriviallyNormedField K := archNontriviallyNormedCompletion w
  let : ProperSpace K := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace _
  let : CharZero K := charZero_of_injective_ringHom (algebraMap F w.Completion).injective
  let P := (powMonoidHom n : Kˣ →* Kˣ).range
  have hP : IsOpen (P : Set Kˣ) := by
    rw [MonoidHom.coe_range]
    exact isOpen_unit_powers n (Nat.cast_ne_zero.mpr (NeZero.ne n))
  let : LocallyCompactSpace P := hP.locallyCompactSpace
  let G (z : Kˣ) := ∑ r ∈ nthRootsFinset n z.val, Θ r
  let R := nthRootsFinset n (1 : K)
  have hpow (u : Kˣ) : G (u^n) = ∑ ζ ∈ R, Θ (ζ * u.val) := by
    simp only [G,Units.val_pow_eq_pow_val]
    rw [nthRootsFinset_pow_eq_image (NeZero.pos n) u,Finset.sum_image]
    intro a _ b _ hab
    exact mul_right_cancel₀ u.ne_zero hab
  have hR (ζ : K) (hζ : ζ ∈ R) : ζ ≠ 0 := by
    intro h
    rw [mem_nthRootsFinset (NeZero.pos n),h,zero_pow (NeZero.ne n)] at hζ
    exact zero_ne_one hζ
  have hGP (z : Kˣ) (hz : z ∉ (P : Set Kˣ)) : G z = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    exfalso
    rw [mem_nthRootsFinset (NeZero.pos n)] at hr
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [zero_pow (NeZero.ne n)] at hr
      exact z.ne_zero hr.symm
    exact hz ⟨Units.mk0 r hr0,Units.ext (by simpa using hr)⟩
  -- Continuity of the root sum on the open subgroup of powers.
  let f := (powMonoidHom n : Kˣ →* Kˣ).rangeRestrict
  have hfc : Continuous f := (continuous_id.pow n : Continuous (fun x : Kˣ => x^n)).subtype_mk _
  have hq : Topology.IsQuotientMap f := by
    have hp : IsProperMap f := isProperMap_iff_tendsto_cocompact.mpr
      ⟨hfc,unitPower_proper n (NeZero.ne n)⟩
    exact hp.isClosedMap.isQuotientMap hfc (MonoidHom.rangeRestrict_surjective _)
  have hsum_cont : Continuous (fun u : Kˣ => ∑ ζ ∈ R, Θ (ζ * u.val)) := by
    refine continuous_finsetSum _ fun ζ hζ => ?_
    exact hc.comp_continuous (continuous_const.mul Units.continuous_val)
      (fun u => mul_ne_zero (hR ζ hζ) u.ne_zero)
  have hGc : ContinuousOn G (P : Set Kˣ) := by
    rw [continuousOn_iff_continuous_domRestrict]
    apply hq.continuous_iff.mpr
    convert hsum_cont using 1
    funext u
    exact hpow u
  have hmap := d.arch_map_lineMeasure_pow w
  dsimp only at hmap
  let c := ((n : ℝ) / modulus F v (n : K)).toNNReal
  have hmn : 0 < modulus F v (n : K) := by
    have hnz := (diagonal F v).injective.ne (Nat.cast_ne_zero.mpr (NeZero.ne n) : (n:F) ≠ 0)
    simp only [map_natCast,map_zero] at hnz
    simp [modulus,norm_pos_iff.mpr hnz,pow_pos]
  have hcpos : (c : ℝ) = n / modulus F v (n : K) := Real.coe_toNNReal _ (by positivity)
  have hGm : AEStronglyMeasurable G (ν.map (fun x : Kˣ => x^n)) := by
    rw [hmap]
    exact (hGc.aestronglyMeasurable hP.measurableSet).smul_measure c
  have key := integral_map (φ := fun x : Kˣ => x^n) (μ := ν) (continuous_pow n).aemeasurable hGm
  rw [hmap,integral_smul_nnreal_measure] at key
  have hres : (∫ z, G z ∂ν.restrict (P : Set Kˣ)) = ∫ z, G z ∂ν :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hGP
  have hrot (ζ : K) (hζ : ζ ∈ R) : (∫ u, Θ (ζ * u.val) ∂ν) = ∫ u, Θ u.val ∂ν :=
    integral_mul_left_eq_self (fun u : Kˣ => Θ u.val) (Units.mk0 ζ (hR ζ hζ))
  have hsum : (∫ u, G (u^n) ∂ν) = n * ∫ u, Θ u.val ∂ν := by
    simp_rw [hpow]
    rw [integral_finsetSum _ (fun ζ hζ => by
      simpa only [Units.val_mul,Units.val_mk0] using
        (hi.comp_mul_left (Units.mk0 ζ (hR ζ hζ))))]
    rw [Finset.sum_congr rfl hrot,Finset.sum_const,arch_card_roots_one d w,nsmul_eq_mul]
  rw [hres,hsum,NNReal.smul_def,hcpos,Complex.real_smul] at key
  change (∫ z, G z ∂ν) = _
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hm0 : (modulus F v (n : K) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hmn.ne'
  have hq : ((n : ℝ) / modulus F v (n : K) : ℝ) ≠ 0 := div_ne_zero (by exact_mod_cast NeZero.ne n) hmn.ne'
  apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hq)
  rw [key]
  push_cast
  field_simp
  rfl

local notation "dx" => selfDual F d.character v

/-- The change of variables y = −rⁿ/s turns the sum over the n-th roots of −sy
into an integral against the axis density, at every infinite place. -/
theorem arch_axis_root_change (Φ : d.schwartz v) (s : Kˣ) {k : K → ℂ} (hk : Continuous k)
    (hσk : Integrable (fun r => d.axisDensity v Φ s r * k r) dx) :
    (∫ y, (if hy : y ≠ 0 then d.axis v Φ (Units.mk0 y hy) else 0) *
        ∑ r ∈ nthRootsFinset n (-(s.val*y)), k r ∂dx) =
      ∫ r, d.axisDensity v Φ s r * k r ∂dx := by
  let ν := d.lineMeasure v
  let m := modulus F v
  have hm (x : K) (hx : x ≠ 0) : 0 < m x := by simp [m,modulus,norm_pos_iff.mpr hx,pow_pos]
  have mmul (x y : K) : m (x*y) = m x * m y := by simp [m,modulus,norm_mul,mul_pow]
  have mpow (x : K) : m (x^n) = m x ^ n := by simp [m,modulus,norm_pow,← pow_mul,mul_comm]
  let A (y : K) := if hy : y ≠ 0 then d.axis v Φ (Units.mk0 y hy) else 0
  have hA : ContinuousOn A {0}ᶜ := by
    intro y hy
    have hy' : y ≠ 0 := hy
    let : NontriviallyNormedField K := archNontriviallyNormedCompletion w
    have hc : ContinuousAt (fun y : K => Φ.val.2 0 (liftUnit y)) y := by
      exact ((d.continuous_schwartz_charts v Φ).2.comp (continuous_const.prodMk continuous_id)).continuousAt.comp
        (liftUnit_continuousAt hy')
    refine (hc.congr ?_).continuousWithinAt
    filter_upwards [isOpen_ne.mem_nhds hy'] with z hz
    have hz' : z ≠ 0 := hz
    simp only [A,ne_eq,hz',not_false_eq_true,dite_true,axis]
    have hl : liftUnit z = Units.mk0 z hz' := Units.ext (liftUnit_val (by simpa using hz'))
    rw [hl]
  let Θ (r : K) : ℂ := ((m r)^n / m s.val : ℝ) * A (-(r^n)/s.val) * k r
  have hΘc : ContinuousOn Θ {0}ᶜ := by
    refine ((Complex.continuous_ofReal.comp_continuousOn ?_).mul (hA.comp ?_ ?_)).mul hk.continuousOn
    · exact ((continuous_norm.pow w.mult).pow n).continuousOn.div_const _
    · exact (by fun_prop : Continuous fun r : K => -(r^n)/s.val).continuousOn
    · intro r hr
      have hr' : r ≠ 0 := hr
      simpa [s.ne_zero] using pow_ne_zero n hr'
  have hΘσ (u : Kˣ) : (m n : ℂ) * Θ u.val = m u.val • (d.axisDensity v Φ s u.val * k u.val) := by
    rw [d.axisDensity_unit,Complex.real_smul]
    have hv : (-(u^n)/s).val = -(u.val^n)/s.val := by simp
    have hAv : A (-(u.val^n)/s.val) = d.axis v Φ (-(u^n)/s) := by
      simp only [A,ne_eq,(-(u^n)/s).ne_zero,← hv,not_false_eq_true,dite_true]
      congr 1
      exact Units.ext rfl
    simp only [Θ,hAv]
    have hu := hm u.val u.ne_zero
    have e : (m u.val : ℂ)^n = (m u.val) * (m u.val)^(n-1) := by
      rw [← pow_succ',Nat.sub_add_cancel (NeZero.one_le)]
    push_cast
    rw [e]
    field_simp
    ring
  have hΘi : Integrable (fun u : Kˣ => Θ u.val) ν := by
    have h := ((d.lineMeasure_modulus v (fun r => d.axisDensity v Φ s r * k r)).1.mpr hσk).const_mul
      ((m n : ℂ)⁻¹)
    refine h.congr (.of_forall fun u => ?_)
    have hn : (m n : ℂ) ≠ 0 := by
      have := hΘσ u
      intro h0
      have hnz := (diagonal F v).injective.ne (Nat.cast_ne_zero.mpr (NeZero.ne n) : (n:F) ≠ 0)
      simp only [map_natCast,map_zero] at hnz
      exact (hm _ hnz).ne' (by exact_mod_cast h0)
    simp only
    rw [← hΘσ u,← mul_assoc,inv_mul_cancel₀ hn,one_mul]
  -- Left side as a multiplicative integral, rotated by -s.
  have hL := (d.lineMeasure_modulus v (fun y => A y * ∑ r ∈ nthRootsFinset n (-(s.val*y)), k r)).2
  dsimp only at hL
  rw [← hL]
  rw [← integral_mul_left_eq_self _ (-s)⁻¹]
  have hpt (z : Kˣ) : m ((-s)⁻¹*z).val • (A ((-s)⁻¹*z).val * ∑ r ∈ nthRootsFinset n (-(s.val*((-s)⁻¹*z).val)), k r) =
      ∑ r ∈ nthRootsFinset n z.val, Θ r := by
    have hz : -(s.val*((-s)⁻¹*z).val) = z.val := by
      simp only [Units.val_mul,Units.val_inv_eq_inv_val,Units.val_neg]; field_simp [s.ne_zero]
    rw [hz,Complex.real_smul,Finset.mul_sum,Finset.mul_sum]
    refine Finset.sum_congr rfl fun r hr => ?_
    have hr' := (mem_nthRootsFinset (NeZero.pos n) _).mp hr
    have hy : ((-s)⁻¹*z).val = -(r^n)/s.val := by
      simp only [Units.val_mul,Units.val_inv_eq_inv_val,Units.val_neg,hr']; field_simp [s.ne_zero]
    have hmz : m ((-s)⁻¹*z).val = m r ^ n / m s.val := by
      rw [hy,show -(r^n)/s.val = r^n * (-s.val)⁻¹ by field_simp,mmul,mpow,div_eq_mul_inv]
      congr 1
      simp [m,modulus,norm_inv,inv_pow]
    rw [hmz,hy]
    simp only [Θ]
    push_cast
    ring
  trans ∫ z : Kˣ, ∑ r ∈ nthRootsFinset n z.val, Θ r ∂ν
  · exact integral_congr_ae (.of_forall hpt)
  rw [d.arch_lineIntegral_root_sum w Θ hΘc hΘi,← integral_const_mul]
  rw [← (d.lineMeasure_modulus v (fun r => d.axisDensity v Φ s r * k r)).2]
  exact integral_congr_ae (.of_forall hΘσ)

end MetaplecticPoisson.Datum
