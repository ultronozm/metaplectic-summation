import MetaplecticSummation.RamifiedGauss
import MetaplecticSummation.TamePowers

/-! Unit-character transforms when the n-th power of the character is trivial. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField MeasureTheory Set
open scoped ComplexConjugate
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n) (p : Prime F)
section
local notation "v" => (Sum.inr p : Place F)
local notation "K" => LocalField F v
local notation "q" => (p.asIdeal.absNorm : ℝ)
local notation "dx" => selfDual F d.character v
local notation "ψ" => d.character.localValue F v

omit [NeZero n] in
private theorem unitGauss_congr {θ η : Weight v} (h : ∀ x : Kˣ, ‖x.val‖ = 1 → θ x = η x) (α : K) :
    d.unitGauss p θ α = d.unitGauss p η α := by
  unfold unitGauss
  congr 1
  funext x
  split_ifs with hx
  · rw [h x hx]
  · rfl

omit [NeZero n] in
/-- The Fourier integral of the trivial unit character takes the three
Ramanujan values for an unramified additive character. -/
theorem unitGauss_trivial (hψ : d.UnramifiedAt v) (α : K) :
    d.unitGauss p (fun _ => 1) α =
      (if ‖α‖ ≤ 1 then 1-(q : ℂ)⁻¹ else 0) - (if ‖α‖ = q then (q : ℂ)⁻¹ else 0) := by
  obtain ⟨π,hπ⟩ : ∃ π : Kˣ, ‖π.val‖ = q⁻¹ := FinitePlace.exists_norm_uniformizer p
  have hq : 1 < q := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm p
  have hq₀ := zero_lt_one.trans hq
  have diff := sphereValue_eq_sub p π 1 hπ
  simp only [Units.val_one,norm_one,mul_one] at diff
  rw [d.unitGauss_additive]
  have he (y : K) : (if hy : y ≠ 0 then
      (if ‖y‖ = 1 then (fun _ : Kˣ => (1:ℂ)) (Units.mk0 y hy) * ψ (α*y) else 0) else 0) =
      ballValue p ‖(1 : Kˣ).val‖ y * ψ (α*y) - ballValue p ‖π.val‖ y * ψ (α*y) := by
    rw [← sub_mul,Units.val_one,norm_one,← congrFun diff y]
    by_cases hy : y = 0 <;> simp [hy,ite_mul]
  simp_rw [he]
  rw [integral_sub (d.integrable_phase v (d.ball_integrable p _) α) (d.integrable_phase v (d.ball_integrable p _) α),
    d.ball_character_integral p hψ 1,d.ball_character_integral p hψ π]
  simp only [Units.val_one,mul_one,norm_one,Complex.ofReal_one,norm_mul,hπ,Complex.ofReal_inv]
  simp only [← div_eq_mul_inv,div_le_one hq₀]
  by_cases hi : ‖α‖ ≤ 1
  · simp [hi,hi.trans hq.le,(hi.trans_lt hq).ne]
  · by_cases heq : ‖α‖ = q
    · simp [heq,hq.not_ge]
    · have hgt : ¬ ‖α‖ ≤ q := by
        intro hl
        have hh := (finite_norm_lt_one_iff p (α*π.val)).mp (by
          rw [norm_mul,hπ,← div_eq_mul_inv,div_lt_one hq₀]
          exact lt_of_le_of_ne hl heq)
        rw [norm_mul,hπ] at hh
        exact hi ((mul_le_iff_le_one_left (inv_pos.mpr hq₀)).mp hh)
      simp [hi,heq,hgt]

private theorem hilbertUnitChar_one_iff (hp : p.asIdeal.absNorm.Coprime n)
    (a c : Kˣ) (i j : ℤ) (ha : ‖a.val‖ = q^(-i)) (hc : ‖c.val‖ = q^(-j)) :
    d.hilbertUnitChar p (c/a) = 1 ↔ i ≡ j [ZMOD n] := by
  have hq : 1 < q := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm p
  have hq₀ := zero_lt_one.trans hq
  have hratio : ‖(c/a).val‖ = q^(i-j) := by
    rw [Units.val_div_eq_div_val,norm_div,hc,ha,← zpow_sub₀ hq₀.ne']
    congr 1
    omega
  constructor
  · intro h
    obtain ⟨z,hz⟩ : ∃ z : Kˣ, ‖(c/a).val‖ = ‖z.val‖^n := d.norm_power_of_trivial_on_units p hp (c/a) (fun u hu =>
      congrArg (fun θ : UnitChar p => (θ ⟨u,hu⟩ : ℂ)) h)
    obtain ⟨k,hk⟩ : ∃ k : ℤ, ‖z.val‖ = q^k := norm_zpow_residue_card p z
    rw [hratio,hk,← zpow_natCast,← zpow_mul] at hz
    have he := (zpow_right_inj₀ hq₀ hq.ne').mp hz
    apply Int.modEq_iff_dvd.mpr
    exact ⟨-k,by rw [mul_neg,mul_comm (n : ℤ)]; omega⟩
  · intro h
    obtain ⟨k,hk⟩ := Int.modEq_iff_dvd.mp h
    obtain ⟨π,hπ⟩ : ∃ π : Kˣ, ‖π.val‖ = q⁻¹ := FinitePlace.exists_norm_uniformizer p
    let t : Kˣ := π^k
    have ht : ‖(t^n).val‖ = q^(i-j) := by
      rw [Units.val_pow_eq_pow_val,norm_pow,show ‖t.val‖ = q^(-k) by simp [t,Units.val_zpow_eq_zpow_val,hπ],
        ← zpow_natCast,← zpow_mul]
      congr 1
      linear_combination hk
    let w := (c/a)/t^n
    have hw : ‖w.val‖ = 1 := by
      rw [show w.val = (c/a).val/(t^n).val from Units.val_div_eq_div_val ..,norm_div,ht,hratio,div_self (zpow_ne_zero _ hq₀.ne')]
    apply MonoidHom.ext
    intro u
    apply Subtype.ext
    change (d.unitPairing v (c/a) u.val).val = 1
    have he : c/a = w*t^n := (div_mul_cancel _ _).symm
    rw [he,map_mul,map_pow,MonoidHom.mul_apply,MonoidHom.pow_apply,d.unitPairing_pow,
      d.unitPairing_tame_units p hp w u.val hw u.property,mul_one]
    rfl

private theorem hilbertUnitChar_level_one (hp : p.asIdeal.absNorm.Coprime n) (z : Kˣ)
    (hz : d.hilbertUnitChar p z ≠ 1) : IsLeast {k | trivialAtLevel (d.hilbertUnitChar p z) k} 1 := by
  constructor
  · intro u hu
    have hq : 1 < q := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm p
    obtain ⟨t,ht⟩ : ∃ t : Kˣ, t^n = u.val := FinitePlace.principal_unit_pow p hp u.val
      ((hu.resolve_left (by decide)).trans_lt (by simpa using inv_lt_one_of_one_lt₀ hq))
    apply Subtype.ext
    change (d.unitPairing v z u.val).val = 1
    rw [← ht,map_pow,d.unitPairing_pow]
    rfl
  · intro k hk
    by_contra! h
    have he : k = 0 := by omega
    subst k
    exact hz (MonoidHom.ext fun u => hk u (Or.inl rfl))

private theorem hilbertWeight_dual_integral (hp : p.asIdeal.absNorm.Coprime n) (a c : Kˣ) :
    d.dualWeight v (fun x => if ‖x.val‖ = 1 then d.symbol v a x else 0) c =
      ∫ y, ψ y * d.unitGauss p (charWeight (d.hilbertUnitChar p (c/a))) (-y^n/c.val) ∂dx := by
  have hw : (fun x : Kˣ => if ‖x.val‖ = 1 then d.symbol v a x else 0) = charWeight (d.hilbertUnitChar p a) := by
    funext x
    by_cases hx : x ∈ integralUnits p
    · rw [if_pos (show ‖x.val‖ = 1 from hx)]
      rw [charWeight,dif_pos hx]
      rfl
    · rw [if_neg (show ‖x.val‖ ≠ 1 from hx)]
      rw [charWeight,dif_neg hx]
  rw [hw,d.dual_charWeight_integral p hp]
  apply integral_congr_ae
  filter_upwards with y
  apply congrArg (ψ y * ·)
  apply d.unitGauss_congr
  intro x hx
  have hu : x ∈ integralUnits p := hx
  let u : integralUnits p := ⟨x,hu⟩
  change conj (charWeight (d.hilbertUnitChar p a) x) * _ = charWeight (d.hilbertUnitChar p (c/a)) x
  simp only [charWeight,dif_pos hu]
  rw [← Circle.coe_inv_eq_conj,Circle.coe_inv]
  change ((d.unitPairing v a x).val)⁻¹ * (d.unitPairing v c x).val = (d.unitPairing v (c/a) x).val
  rw [map_div,MonoidHom.div_apply,Units.val_div_eq_div_val,div_eq_inv_mul]

private theorem phase_integrableOn (U : Set K) (r : ℝ) (hU : ∀ x ∈ U, ‖x‖^n ≤ r) :
    IntegrableOn (ψ) U dx := by
  letI : ProperSpace K := by
    letI := FinitePlace.nontriviallyNormedCompletion p
    exact .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace (p.adicCompletion F)
  letI : (dx).IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  apply ((d.character.continuous_localValue v).continuousOn.integrableOn_compact
    (isCompact_closedBall (0 : K) (max 1 r))).mono_set
  intro x hx
  rw [Metric.mem_closedBall,dist_zero_right]
  by_cases h : ‖x‖ ≤ 1
  · exact h.trans (le_max_left ..)
  · have he := pow_le_pow_right₀ (le_of_not_ge h) (show 1 ≤ n from NeZero.pos n)
    rw [pow_one] at he
    exact (he.trans (hU x hx)).trans (le_max_right ..)

private theorem hilbertWeight_same_class (hp : p.asIdeal.absNorm.Coprime n) (hψ : d.UnramifiedAt v)
    (a c : Kˣ) (hχ : d.hilbertUnitChar p (c/a) = 1) :
    d.dualWeight v (fun x => if ‖x.val‖ = 1 then d.symbol v a x else 0) c =
      (1-(q : ℂ)⁻¹) * (∫ y in {y : K | ‖y‖^n ≤ ‖c.val‖}, ψ y ∂dx) -
      (q : ℂ)⁻¹ * ∫ y in {y : K | ‖y‖^n = q*‖c.val‖}, ψ y ∂dx := by
  let A := {y : K | ‖y‖^n ≤ ‖c.val‖}
  let B := {y : K | ‖y‖^n = q*‖c.val‖}
  have hA : MeasurableSet A := (isClosed_le (continuous_norm.pow n) continuous_const).measurableSet
  have hB : MeasurableSet B := (isClosed_eq (continuous_norm.pow n) continuous_const).measurableSet
  have hiA := (d.phase_integrableOn p A _ (fun _ h => h)).integrable_indicator hA
  have hiB := (d.phase_integrableOn p B _ (fun _ h => h.le)).integrable_indicator hB
  rw [d.hilbertWeight_dual_integral p hp,hχ]
  have hg (y : K) : d.unitGauss p (charWeight 1) (-y^n/c.val) =
      (if y ∈ A then 1-(q : ℂ)⁻¹ else 0) - (if y ∈ B then (q : ℂ)⁻¹ else 0) := by
    rw [d.unitGauss_congr p (η := fun _ => 1) (by
      intro x hx
      simp [charWeight,show x ∈ integralUnits p from hx]),d.unitGauss_trivial p hψ]
    simp only [A,B,mem_setOf_eq,norm_div,norm_neg,norm_pow,div_le_one (norm_pos_iff.mpr c.ne_zero),
      div_eq_iff (norm_ne_zero_iff.mpr c.ne_zero)]
  have eval (y : K) : ψ y * d.unitGauss p (charWeight 1) (-y^n/c.val) =
      (1-(q : ℂ)⁻¹)*A.indicator (ψ) y - (q : ℂ)⁻¹*B.indicator (ψ) y := by
    rw [hg]
    by_cases ha : y ∈ A <;> by_cases hb : y ∈ B <;> simp [ha,hb,indicator] <;> ring
  simp_rw [eval]
  rw [integral_sub (hiA.const_mul _) (hiB.const_mul _),integral_const_mul,integral_const_mul,
    integral_indicator hA,integral_indicator hB]

private theorem hilbertWeight_other_class (hp : p.asIdeal.absNorm.Coprime n) (hψ : d.UnramifiedAt v)
    (a c : Kˣ) (j : ℤ) (hc : ‖c.val‖ = q^(-j)) (hχ : d.hilbertUnitChar p (c/a) ≠ 1) :
    let W : Weight v := fun x => if ‖x.val‖ = 1 then d.symbol v a x else 0
    (¬ (n : ℤ) ∣ j-1 → d.dualWeight v W c = 0) ∧
    ∀ k : ℤ, j = n*k+1 → ∀ t : Kˣ, ‖t.val‖ = q^(-k) →
      d.dualWeight v W c = d.unitGauss p (fun x => d.symbol v (c/a) x) (-t.val^n/c.val) *
        ∫ y in {y : K | ‖y‖ = q^(-k)}, ψ y ∂dx := by
  let θ := d.hilbertUnitChar p (c/a)
  let G := d.unitGauss p (charWeight θ)
  let α (y : K) := -y^n/c.val
  let V := d.dualWeight v (fun x : Kˣ => if ‖x.val‖ = 1 then d.symbol v a x else 0) c
  have heval : V = ∫ y, ψ y * G (α y) ∂dx := d.hilbertWeight_dual_integral p hp a c
  have hq : 1 < q := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm p
  have hq₀ := zero_lt_one.trans hq
  have cond := d.hilbertUnitChar_level_one p hp (c/a) hχ
  have zero (y : K) (hy : ‖α y‖ ≠ q) : G (α y) = 0 :=
    d.unitGauss_conductor_support p hψ θ (by decide : 0 < 1) cond (α y) (by simpa only [pow_one] using hy)
  have expn (y : Kˣ) (m : ℤ) (hm : ‖y.val‖ = q^m) :
      ‖α y.val‖ = q^(m*n+j) := by
    dsimp only [α]
    rw [norm_div,norm_neg,norm_pow,hm,hc,← zpow_natCast,← zpow_mul,← zpow_sub₀ hq₀.ne',sub_neg_eq_add]
  have index (y : K) (hit : ‖α y‖ = q) : ∃ m : ℤ, ‖y‖ = q^m ∧ m*n+j = 1 := by
    have hy : y ≠ 0 := by
      rintro rfl
      simp [α,zero_pow (NeZero.ne n),hq₀.ne'.symm] at hit
    obtain ⟨m,hm⟩ : ∃ m : ℤ, ‖y‖ = q^m := norm_zpow_residue_card p (Units.mk0 y hy)
    refine ⟨m,hm,(zpow_right_inj₀ hq₀ hq.ne').mp ?_⟩
    simpa only [zpow_one] using (expn (Units.mk0 y hy) m hm).symm.trans hit
  constructor
  · intro hdiv
    change V = 0
    rw [heval]
    apply integral_eq_zero_of_ae
    filter_upwards with y
    rw [zero y (fun hit => hdiv (by
      obtain ⟨m,_,hm⟩ := index y hit
      exact ⟨-m,by rw [mul_neg,mul_comm (n : ℤ)]; omega⟩)),mul_zero]
    rfl
  · intro k hj t ht
    let U := {y : K | ‖y‖ = q^(-k)}
    have hU : MeasurableSet U := (isClosed_eq continuous_norm continuous_const).measurableSet
    have off (y : K) (hy : y ∉ U) : G (α y) = 0 := by
      apply zero
      intro hit
      obtain ⟨m,hm,h⟩ := index y hit
      have hmk : m = -k := by
        apply mul_right_cancel₀ (show (n : ℤ) ≠ 0 by exact_mod_cast NeZero.ne n)
        linear_combination h - hj
      exact hy (hm.trans (by rw [hmk]))
    have on (y : K) (hy : y ∈ U) : G (α y) = G (α t.val) := by
      have hyt : ‖y‖ = ‖t.val‖ := hy.trans ht.symm
      have hyn : y ≠ 0 := norm_ne_zero_iff.mp (hyt ▸ norm_ne_zero_iff.mpr t.ne_zero)
      let u : integralUnits p := ⟨(Units.mk0 y hyn)/t,by
        change ‖((Units.mk0 y hyn)/t).val‖ = 1
        rw [Units.val_div_eq_div_val,Units.val_mk0,norm_div,hyt,div_self (norm_ne_zero_iff.mpr t.ne_zero)]⟩
      have harg : α y = (u^n).val.val * α t.val := by
        simp only [α,Subgroup.coe_pow,Units.val_pow_eq_pow_val,u,Units.val_div_eq_div_val,Units.val_mk0,div_pow]
        field_simp
      have hθ : θ (u^n) = 1 := by
        rw [map_pow,← MonoidHom.pow_apply,show θ^n = 1 from d.hilbertUnitChar_pow p (c/a)]
        rfl
      exact harg ▸ (d.unitGauss_unit_mul p θ (u^n) (α t.val)).trans (by simp [G,hθ])
    have he (y : K) : ψ y * G (α y) = G (α t.val) * U.indicator (ψ) y := by
      by_cases hy : y ∈ U
      · rw [on y hy,indicator_of_mem hy,mul_comm]
      · rw [off y hy,indicator_of_notMem hy,mul_zero,mul_zero]
    have hsym : G (α t.val) = d.unitGauss p (fun x => d.symbol v (c/a) x) (α t.val) := by
      apply d.unitGauss_congr
      intro x hx
      simp only [charWeight,dif_pos (show x ∈ integralUnits p from hx)]
      rfl
    change V = _ * _
    rw [heval]
    simp_rw [he]
    rw [integral_const_mul,integral_indicator hU,hsym]

end

/-- Proposition 10.27, with valuations written as powers of the residue cardinality. -/
theorem untwistedVector (p : Prime F) (hp : p.asIdeal.absNorm.Coprime n) (hψ : d.UnramifiedAt (.inr p))
    (a c : (LocalField F (.inr p))ˣ) (i j : ℤ)
    (ha : ‖(a : LocalField F (.inr p))‖ = (p.asIdeal.absNorm : ℝ)^(-i))
    (hc : ‖(c : LocalField F (.inr p))‖ = (p.asIdeal.absNorm : ℝ)^(-j)) :
    let v : Place F := .inr p
    let q : ℝ := p.asIdeal.absNorm
    let W : Weight v := fun x => if ‖(x : LocalField F v)‖ = 1 then d.symbol v a x else 0
    let shell := fun U : Set (LocalField F v) =>
      ∫ t in U, d.character.localValue F v t ∂(selfDual F d.character v)
    (i ≡ j [ZMOD n] → d.dualWeight v W c =
      (1 - (q : ℂ)⁻¹) * shell {t | ‖t‖ ^ n ≤ ‖(c : LocalField F v)‖} -
      (q : ℂ)⁻¹ * shell {t | ‖t‖ ^ n = q * ‖(c : LocalField F v)‖}) ∧
    (¬ i ≡ j [ZMOD n] →
      (¬ (n : ℤ) ∣ j-1 → d.dualWeight v W c = 0) ∧
      ∀ k : ℤ, j = n*k+1 → ∀ t : (LocalField F v)ˣ, ‖(t : LocalField F v)‖ = q^(-k) →
        d.dualWeight v W c = d.unitGauss p (fun x => d.symbol v (c/a) x)
          (-((t : LocalField F v)^n) / c) * shell {y | ‖y‖ = q^(-k)}) := by
  have test := d.hilbertUnitChar_one_iff p hp a c i j ha hc
  exact ⟨fun h => d.hilbertWeight_same_class p hp hψ a c (test.mpr h),
    fun h => d.hilbertWeight_other_class p hp hψ a c j hc (fun he => h (test.mp he))⟩

end MetaplecticPoisson.Datum
