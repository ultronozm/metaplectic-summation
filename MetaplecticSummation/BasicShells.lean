import MetaplecticSummation.BasicShears
import MetaplecticSummation.ConductorMeasure
import MetaplecticSummation.TamePowers

/-! The vertical marginal of the explicit tame basic charts on all valuation shells. -/

noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField IsDedekindDomain MeasureTheory Set
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n) (p : Prime F)
local notation "v" => (Sum.inr p : Place F)
local notation "K" => LocalField F v
local notation "q" => (p.asIdeal.absNorm : ℝ)
local notation "dx" => selfDual F d.character v
private abbrev radius (j : ℕ) := (q^(n*j))⁻¹
private abbrev weight (j : ℕ) := (p.asIdeal.absNorm : ℂ)^((n-1)*j)
local notation "R" => radius (n := n) p
local notation "W" => weight (n := n) p

private theorem radius_anti : StrictAnti R := by
  have hq : 1 < q := by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm p
  intro i j hij
  exact (inv_lt_inv₀ (pow_pos (zero_lt_one.trans hq) _) (pow_pos (zero_lt_one.trans hq) _)).mpr
    ((pow_lt_pow_right₀ hq) (Nat.mul_lt_mul_of_pos_left hij (NeZero.pos n)))

omit [NeZero n] in
private theorem norm_uniformizer_layer (π : Kˣ) (hπ : ‖π.val‖ = q⁻¹) (j : ℕ) :
    ‖(π^j).val‖^n = R j := by
  rw [Units.val_pow_eq_pow_val,norm_pow,← pow_mul,Nat.mul_comm j n,hπ,inv_pow]

/-- Outside the integral power shells the vertical marginal vanishes. -/
theorem basic_marginal_off_shell (hp : p.asIdeal.absNorm.Coprime n) (x : Kˣ)
    (hx : ∀ j : ℕ, ‖x.val‖ ≠ R j) : (∫ y, (d.basicCharts p).1 x y ∂dx) = 0 := by
  by_cases hbig : 1 < ‖x.val‖
  · apply integral_eq_zero_of_ae
    filter_upwards with y
    have he j : max ‖x.val‖ ‖y‖ ≠ R j := by
      apply ne_of_gt
      have h₀ : R 0 = 1 := by simp [radius]
      exact ((h₀ ▸ (radius_anti (n := n) p).antitone (Nat.zero_le j)).trans_lt hbig).trans_le (le_max_left _ _)
    simp only [radius] at he
    simp [basicCharts,he]
  have hpow : ¬ ∃ t : Kˣ, ‖x.val‖ = ‖t.val‖^n := by
    rintro ⟨t,ht⟩
    have ht' : ‖t.val‖ ≤ 1 := by
      by_contra! hh
      exact hbig (ht ▸ one_lt_pow₀ hh (NeZero.ne n))
    obtain ⟨j,hj⟩ := integral_norm_power p t ht'
    apply hx j
    change ‖t.val‖ = (q^j)⁻¹ at hj
    rw [ht,hj,inv_pow,← pow_mul,Nat.mul_comm j n]
  obtain ⟨u,hu,hs⟩ : ∃ u : Kˣ, ‖u.val‖ = 1 ∧ d.symbol v x u ≠ 1 := by
    by_contra! h
    exact hpow (d.norm_power_of_trivial_on_units p hp x h)
  let f := (d.basicCharts p).1 x
  have he (y : K) : f (u.val*y) = d.symbol v x u * f y := by
    have hn : ‖u.val*y‖ = ‖y‖ := by rw [norm_mul,hu,one_mul]
    by_cases h : ‖y‖ ≤ ‖x.val‖
    · simp only [f,basicCharts,hn,if_pos h,max_eq_left h]
      change (∑' j, if ‖x.val‖ = R j then W j else 0) * 1 = _
      simp [hx]
    · have hy : y ≠ 0 := by rintro rfl; exact h (by simp)
      let Y := Units.mk0 y hy
      have hm : d.symbol v x (u*Y) = d.symbol v x u * d.symbol v x Y := by
        change (d.unitPairing v x (u*Y)).val = _
        rw [map_mul,Units.val_mul,d.coe_unitPairing,d.coe_unitPairing]
      simp only [f,basicCharts,hn,if_neg h,dif_pos (mul_ne_zero u.ne_zero hy),dif_pos hy]
      rw [show Units.mk0 (u.val*y) (mul_ne_zero u.ne_zero hy) = u*Y from Units.ext rfl,hm,mul_left_comm]
  have hm := d.integral_local_mul v u f
  change (∫ y, f (u.val*y) ∂dx) = _ / (‖u.val‖ : ℂ) at hm
  simp only [he,integral_const_mul,hu,Complex.ofReal_one,div_one] at hm
  exact (mul_left_eq_self₀.mp hm).resolve_left hs

/-- On a power shell the two Hilbert-symbol arguments have valuation divisible
by n wherever the outer part of the basic chart contributes. -/
private theorem basic_slice_on_shell (hp : p.asIdeal.absNorm.Coprime n) (π x : Kˣ)
    (hπ : ‖π.val‖ = q⁻¹) (k : ℕ) (hx : ‖x.val‖ = R k) (y : K) :
    (d.basicCharts p).1 x y =
      (∑ j ∈ Finset.range k, if ‖y‖ = R j then W j else 0) +
      (if ‖y‖ ≤ R k then W k else 0) := by
  let r := max ‖x.val‖ ‖y‖
  let phase : ℂ := if ‖y‖ ≤ ‖x.val‖ then 1 else
    if hy : y ≠ 0 then d.symbol v x (Units.mk0 y hy) else 0
  change (∑' j, if r = R j then W j else 0) * phase = _
  have ha := radius_anti (n := n) p
  have hcut j (hj : j ∉ Finset.range (k+1)) : r ≠ R j :=
    ne_of_gt ((ha (by simpa using hj : k < j)).trans_le (hx ▸ le_max_left _ _))
  rw [tsum_eq_sum (s := Finset.range (k+1)) (fun j hj => if_neg (hcut j hj)),Finset.sum_mul,Finset.sum_range_succ]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    have hlt : ‖x.val‖ < R j := hx ▸ ha (Finset.mem_range.mp hj)
    have iff' : r = R j ↔ ‖y‖ = R j := by
      by_cases h : ‖y‖ ≤ ‖x.val‖
      · simp [r,max_eq_left h,hlt.ne,(h.trans_lt hlt).ne]
      · simp [r,max_eq_right (le_of_not_ge h)]
    rw [if_congr iff' rfl rfl]
    split_ifs with hy
    · have hn : y ≠ 0 := norm_pos_iff.mp ((norm_nonneg _).trans_lt (hy ▸ hlt))
      have hphase := d.symbol_one_of_norm_powers p hp x (Units.mk0 y hn) (π^k) (π^j)
        (hx.trans (norm_uniformizer_layer p π hπ k).symm) (hy.trans (norm_uniformizer_layer p π hπ j).symm)
      simp [phase,show ¬ ‖y‖ ≤ ‖x.val‖ from (hy ▸ hlt).not_ge,hn,hphase]
    · simp
  · have iff' : r = R k ↔ ‖y‖ ≤ ‖x.val‖ := hx ▸ max_eq_left_iff
    by_cases h : ‖y‖ ≤ ‖x.val‖
    · simp [iff'.mpr h,phase,h,← hx]
    · rw [if_neg (mt iff'.mp h),zero_mul,if_neg (hx ▸ h)]

private theorem lt_unit_iff (a : K) : ‖a‖ < 1 ↔ ‖a‖ ≤ q⁻¹ := by
  have hq : 1 < q := by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm p
  refine ⟨fun h => ?_, fun h => h.trans_lt (inv_lt_one_of_one_lt₀ hq)⟩
  by_cases ha : a = 0
  · simp [ha]
  obtain ⟨j,hj⟩ := integral_norm_power p (Units.mk0 a ha) h.le
  change ‖a‖ = (q^j)⁻¹ at hj
  cases j with
  | zero => simp [hj] at h
  | succ j =>
    rw [hj]
    apply (inv_le_inv₀ (pow_pos (zero_lt_one.trans hq) _) (zero_lt_one.trans hq)).mpr
    simpa using (pow_le_pow_right₀ hq.le (Nat.succ_le_succ (Nat.zero_le j)))

def ballValue (r : ℝ) (y : K) : ℂ := if ‖y‖ ≤ r then 1 else 0

omit [NeZero n] in
theorem ball_integrable (r : ℝ) : Integrable (ballValue p r) dx := by
  letI : ProperSpace K := by
    letI := FinitePlace.nontriviallyNormedCompletion p
    exact .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace (p.adicCompletion F)
  letI : (dx).IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  let B := Metric.closedBall (0 : K) r
  have he : ballValue p r = B.indicator (fun _ => (1 : ℂ)) := by
    funext y
    simp [ballValue,B,indicator,Metric.mem_closedBall,dist_zero_right]
  rw [he]
  exact (integrableOn_const (isCompact_closedBall (0 : K) r).measure_lt_top.ne).integrable_indicator
    Metric.isClosed_closedBall.measurableSet

omit [NeZero n] in
private theorem ball_integral (hψ : d.UnramifiedAt v) (t : Kˣ) :
    (∫ y, ballValue p ‖t.val‖ y ∂dx) = (‖t.val‖ : ℂ) := by
  have he (y : K) : ballValue p 1 (t⁻¹.val*y) = ballValue p ‖t.val‖ y := by
    simp only [ballValue,Units.val_inv_eq_inv_val,← div_eq_inv_mul,norm_div,
      div_le_one (norm_pos_iff.mpr t.ne_zero)]
  have h₁ : (∫ y, ballValue p 1 y ∂dx) = 1 := by
    let B := {y : K | ‖y‖ ≤ 1}
    have hB : MeasurableSet B := (isClosed_le continuous_norm continuous_const).measurableSet
    change (∫ y, B.indicator (fun _ => (1 : ℂ)) y ∂dx) = 1
    rw [integral_indicator hB,integral_const,measureReal_restrict_apply_univ,Complex.real_smul]
    simp only [B,d.selfDual_volume_unramified p hψ,Complex.ofReal_one,mul_one]
  have h := d.integral_local_mul v t⁻¹ (ballValue p 1)
  change _ = _ / (‖t⁻¹.val‖ : ℂ) at h
  simp_rw [he] at h
  simpa only [h₁,Units.val_inv_eq_inv_val,norm_inv,Complex.ofReal_inv,div_inv_eq_mul,one_mul] using h

omit [NeZero n] in
private theorem sphere_integral (hψ : d.UnramifiedAt v) (π t : Kˣ) (hπ : ‖π.val‖ = q⁻¹) :
    let s := fun y : K => if ‖y‖ = ‖t.val‖ then (1:ℂ) else 0
    Integrable s dx ∧ (∫ y, s y ∂dx) = (‖t.val‖ : ℂ) * (1-(q : ℂ)⁻¹) := by
  let s (y : K) : ℂ := if ‖y‖ = ‖t.val‖ then 1 else 0
  have he : s = fun y => ballValue p ‖t.val‖ y - ballValue p ‖(π*t).val‖ y := by
    funext y
    have hlt : ‖y‖ < ‖t.val‖ ↔ ‖y‖ ≤ ‖(π*t).val‖ := by
      have h := lt_unit_iff p (y/t.val)
      rwa [norm_div,div_lt_one (norm_pos_iff.mpr t.ne_zero),div_le_iff₀ (norm_pos_iff.mpr t.ne_zero),
        ← hπ,← norm_mul] at h
    rcases lt_trichotomy ‖y‖ ‖t.val‖ with h | h | h
    · simp only [s,ballValue,if_neg h.ne,if_pos h.le,if_pos (hlt.mp h),sub_self]
    · simp only [s,ballValue,if_pos h,if_pos h.le,if_neg (hlt.not.mp h.not_lt),sub_zero]
    · simp only [s,ballValue,if_neg h.ne',if_neg h.not_ge,if_neg (hlt.not.mp h.not_gt),sub_self]
  change Integrable s dx ∧ (∫ y, s y ∂dx) = _
  rw [he]
  have ht := d.ball_integrable p ‖t.val‖
  have hπt := d.ball_integrable p ‖(π*t).val‖
  refine ⟨ht.sub hπt,?_⟩
  rw [integral_sub ht hπt,d.ball_integral p hψ,d.ball_integral p hψ,Units.val_mul,norm_mul,hπ,
    Complex.ofReal_mul,Complex.ofReal_inv]
  ring

/-- Appendix A's basic-vector marginal, with the unramified self-dual
normalization. It applies directly to the raw basic charts. -/
theorem basicCharts_marginal (hp : p.asIdeal.absNorm.Coprime n) (hψ : d.UnramifiedAt v) (x : Kˣ) :
    (∫ y, (d.basicCharts p).1 x y ∂dx) =
      if ∃ k : ℕ, ‖x.val‖ = ((p.asIdeal.absNorm : ℝ)^(n*k))⁻¹ then 1 else 0 := by
  by_cases hx : ∃ k : ℕ, ‖x.val‖ = R k
  · rw [if_pos hx]
    obtain ⟨k,hx⟩ := hx
    obtain ⟨π,hπ⟩ : ∃ π : Kˣ, ‖π.val‖ = q⁻¹ := FinitePlace.exists_norm_uniformizer p
    have hr (j : ℕ) : ‖(π^(n*j)).val‖ = R j := by
      rw [Units.val_pow_eq_pow_val,norm_pow,hπ,inv_pow]
    let s (j : ℕ) (y : K) : ℂ := if ‖y‖ = R j then 1 else 0
    have hs (j : ℕ) : Integrable (s j) dx ∧ (∫ y, s j y ∂dx) = (R j : ℂ) * (1-(q : ℂ)⁻¹) := by
      simpa only [hr,s] using d.sphere_integral p hψ π (π^(n*j)) hπ
    have hb : (∫ y, ballValue p (R k) y ∂dx) = (R k : ℂ) := by
      simpa only [hr] using d.ball_integral p hψ (π^(n*k))
    have he (y : K) : (d.basicCharts p).1 x y =
        (∑ j ∈ Finset.range k, W j * s j y) + W k * ballValue p (R k) y := by
      rw [d.basic_slice_on_shell p hp π x hπ k hx]
      simp only [s,ballValue,mul_ite,mul_one,mul_zero]
    have hw (j : ℕ) : W j * (R j : ℂ) = ((q : ℂ)^j)⁻¹ := by
      have hq₀ : (p.asIdeal.absNorm : ℂ) ≠ 0 := by
        exact_mod_cast (Nat.zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm p)).ne'
      have hexp : n*j = (n-1)*j+j := by
        conv_lhs => rw [← Nat.sub_add_cancel (NeZero.pos n),Nat.add_mul,Nat.one_mul]
      simp only [radius,weight,Complex.ofReal_inv,Complex.ofReal_pow,Complex.ofReal_natCast]
      rw [hexp,pow_add,mul_inv_rev]
      field_simp
    have hg (j : ℕ) := (hs j).1.const_mul (W j)
    simp_rw [he]
    rw [integral_add (integrable_finsetSum _ (fun j _ => hg j)) ((d.ball_integrable p _).const_mul _),
      integral_finsetSum _ (fun j _ => hg j),integral_const_mul,hb,hw]
    simp_rw [integral_const_mul,fun j => (hs j).2,← mul_assoc,hw]
    clear hx hb he
    induction k with
    | zero => simp
    | succ j ih =>
      rw [Finset.sum_range_succ,pow_succ,mul_inv_rev]
      linear_combination ih
  · rw [if_neg hx]
    exact d.basic_marginal_off_shell p hp x (not_exists.mp hx)

end MetaplecticPoisson.Datum
