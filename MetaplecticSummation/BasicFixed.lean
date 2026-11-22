import MetaplecticSummation.BasicShells
import MetaplecticSummation.Marginals

/-! Fourier invariance of the explicit unramified basic vector, Proposition 6.3(i). -/

noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField IsDedekindDomain MeasureTheory Filter
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n) (p : Prime F)
local notation "v" => (Sum.inr p : Place F)
local notation "K" => LocalField F v
local notation "q" => (p.asIdeal.absNorm : ℝ)
local notation "dx" => selfDual F d.character v
local notation "ψ" => d.character.localValue F v
private abbrev shell (k : ℕ) := (q^(n*k))⁻¹
local notation "R" => shell (n := n) p
private abbrev value (k : ℕ) := (p.asIdeal.absNorm : ℂ)^((n-1)*k)
local notation "W" => value (n := n) p

omit [NeZero n] in
private theorem integral_ball_character (hψ : d.UnramifiedAt v) (b : Kˣ) :
    (∫ t, ψ t * (if ‖t‖ ≤ ‖b.val‖ then (1:ℂ) else 0) ∂dx) =
      if ‖b.val‖ ≤ 1 then (‖b.val‖ : ℂ) else 0 := by
  let g (t : K) := ψ t * (if ‖t‖ ≤ ‖b.val‖ then (1:ℂ) else 0)
  have he (t : K) : g (b.val*t) = (if ‖t‖ ≤ 1 then 1 else 0) * ψ (t*b.val) := by
    have iff' : ‖b.val*t‖ ≤ ‖b.val‖ ↔ ‖t‖ ≤ 1 := by
      rw [norm_mul]
      simp [norm_pos_iff.mpr b.ne_zero]
    unfold g
    rw [if_congr iff' rfl rfl,mul_comm b.val t,mul_comm]
  have h := d.integral_local_mul v b g
  simp_rw [he,d.integral_unitBall_character p hψ] at h
  change _ = (∫ y, g y ∂dx) / (‖b.val‖ : ℂ) at h
  have hh := (eq_div_iff (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr b.ne_zero))).mp h
  simpa only [ite_mul,one_mul,zero_mul] using hh.symm

private theorem shell_inj {i j : ℕ} : R i = R j ↔ i = j := by
  have hq : 1 < q := by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm p
  simp only [shell,inv_inj,pow_right_inj₀ (zero_lt_one.trans hq) hq.ne',Nat.mul_right_inj (NeZero.ne n)]

private theorem axis_basic_value (y : Kˣ) : (d.basicCharts p).2 0 y =
    ∑' j, if ‖y.val‖ = R j then W j else 0 := by simp [basicCharts,shell,value]

omit [NeZero n] in
private theorem norm_ratio_shell (t y π : Kˣ) (hπ : ‖π.val‖ = q⁻¹) (j : ℕ) :
    ‖(t^n/y).val‖ = R j ↔ ‖y.val‖ = ‖(t/π^j).val‖^n := by
  have hπ' : ‖(π^j).val‖^n = R j := by
    rw [Units.val_pow_eq_pow_val,norm_pow,← pow_mul,Nat.mul_comm j n,hπ,inv_pow]
  rw [Units.val_div_eq_div_val,Units.val_pow_eq_pow_val,norm_div,norm_pow,← hπ',Units.val_div_eq_div_val,
    norm_div,div_pow,div_eq_iff (norm_ne_zero_iff.mpr y.ne_zero),eq_div_iff (pow_ne_zero _ (norm_ne_zero_iff.mpr (π^j).ne_zero))]
  exact ⟨fun h => (mul_comm ..).trans h.symm,fun h => h.symm.trans (mul_comm ..)⟩

private theorem ratio_in_shell_iff (t y b : Kˣ) (hy : ‖y.val‖ = ‖b.val‖^n) :
    (∃ j, ‖(t^n/y).val‖ = R j) ↔ ‖t.val‖ ≤ ‖b.val‖ := by
  have ht : ‖(t^n/y).val‖ = ‖(t/b).val‖^n := by
    simp only [Units.val_div_eq_div_val,Units.val_pow_eq_pow_val,norm_div,norm_pow,hy,div_pow]
  have hr (j : ℕ) : R j = ((q^j)⁻¹)^n := by rw [inv_pow,← pow_mul,Nat.mul_comm j n]
  simp_rw [ht,hr]
  have hq : 1 < q := by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm p
  have iff' : ‖(t/b).val‖ ≤ 1 ↔ ‖t.val‖ ≤ ‖b.val‖ := by
    rw [Units.val_div_eq_div_val,norm_div,div_le_one (norm_pos_iff.mpr b.ne_zero)]
  constructor
  · rintro ⟨j,hj⟩
    apply iff'.mp
    have h := (pow_left_inj₀ (norm_nonneg _) (inv_nonneg.mpr (pow_nonneg (zero_lt_one.trans hq).le _)) (NeZero.ne n)).mp hj
    exact h.le.trans (inv_le_one_of_one_le₀ (one_le_pow₀ hq.le))
  · intro h
    obtain ⟨j,hj⟩ := integral_norm_power p (t/b) (iff'.mpr h)
    exact ⟨j,congrArg (·^n) hj⟩

/-- Proposition 6.3(i), the unramified fixed-vector formula for the defining integral,
independent of any construction of the Fourier endomorphism or basic-vector membership. -/
theorem basicCharts_fourier_fixed (hp : p.asIdeal.absNorm.Coprime n) (hψ : d.UnramifiedAt v) :
    d.integralTransform v (d.basicCharts p) = d.basicCharts p := by
  apply (d.transform_basic_eq_iff_axis p hp).mpr
  intro y
  let f := d.basicCharts p
  let L (t : K) := (radon n (d.symbol v) (modulus F v) dx f t).2 0 y
  have hl (t : Kˣ) : L t.val = d.symbol v (-1) y / (‖y.val‖ : ℂ) *
      (if ∃ k, ‖(t^n/y).val‖ = R k then 1 else 0) := by
    rw [show L t.val = _ from d.radon_axis_unit v f (d.basicCharts_glues p hp) y t,
      d.basicCharts_marginal p hp hψ]
    rfl
  have hn : ‖(n : K)‖ = 1 := FinitePlace.norm_degree_of_tame p hp
  letI : NullSingletonClass (dx) := d.selfDual_nullSingleton v
  change (↑(Real.sqrt ‖(n : K)‖) : ℂ)⁻¹ * (∫ t, ψ t * L t ∂dx) = _
  rw [hn,Real.sqrt_one,Complex.ofReal_one,inv_one,one_mul,d.axis_basic_value]
  by_cases hy : ∃ b : Kˣ, ‖y.val‖ = ‖b.val‖^n
  · obtain ⟨b,hb⟩ := hy
    have hs : d.symbol v (-1) y = 1 :=
      d.symbol_one_of_norm_powers p hp (-1) y 1 b (by simp) hb
    have he : (∫ t, ψ t * L t ∂dx) = (∫ t, ψ t * (if ‖t‖ ≤ ‖b.val‖ then (1:ℂ) else 0) ∂dx) / (‖y.val‖ : ℂ) := by
      rw [← integral_div]
      apply integral_congr_ae
      filter_upwards [(dx).ae_ne 0] with t ht
      have h := hl (Units.mk0 t ht)
      rw [hs,if_congr (ratio_in_shell_iff p _ y b hb) rfl rfl] at h
      simp only [Units.val_mk0] at h
      rw [h]
      simp only [div_eq_mul_inv]
      ac_rfl
    rw [he,d.integral_ball_character p hψ]
    by_cases hi : ‖b.val‖ ≤ 1
    · obtain ⟨k,hk⟩ := integral_norm_power p b hi
      change ‖b.val‖ = (q^k)⁻¹ at hk
      have hky : ‖y.val‖ = R k := by rw [hb,hk,inv_pow,← pow_mul,Nat.mul_comm k n]
      rw [if_pos hi,tsum_eq_single k (fun j hj => if_neg (fun h => hj ((shell_inj p).mp (h.symm.trans hky)))) ,
        if_pos hky,hb,hk]
      have hq₀ : (p.asIdeal.absNorm : ℂ) ≠ 0 := by exact_mod_cast (Nat.zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm p)).ne'
      have hnk : k*n = (n-1)*k + k := by
        rw [Nat.mul_comm k n]
        conv_lhs => rw [← Nat.sub_add_cancel (NeZero.pos n),Nat.add_mul,Nat.one_mul]
      simp only [Complex.ofReal_pow,Complex.ofReal_inv,Complex.ofReal_natCast,value,inv_pow,← pow_mul,hnk,
        pow_add,div_inv_eq_mul]
      field_simp
      push_cast
      ring
    · have hbig : 1 < ‖y.val‖ := hb ▸ one_lt_pow₀ (lt_of_not_ge hi) (NeZero.ne n)
      have hq : 1 < q := by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm p
      have hn' (j : ℕ) : ‖y.val‖ ≠ R j := ne_of_gt ((inv_le_one_of_one_le₀ (one_le_pow₀ hq.le)).trans_lt hbig)
      simp [if_neg hi,hn']
  · obtain ⟨π,hπ⟩ : ∃ π : Kˣ, ‖π.val‖ = q⁻¹ := FinitePlace.exists_norm_uniformizer p
    have hzero (t : Kˣ) : L t.val = 0 := by
      have hh : ¬ ∃ k, ‖(t^n/y).val‖ = R k := by
        rintro ⟨k,hk⟩
        exact hy ⟨t/π^k,(norm_ratio_shell p t y π hπ k).mp hk⟩
      rw [hl,if_neg hh,mul_zero]
    have hh (j : ℕ) : ‖y.val‖ ≠ R j := by
      intro he
      apply hy
      exact ⟨π^j,by rw [he,Units.val_pow_eq_pow_val,norm_pow,← pow_mul,Nat.mul_comm j n,hπ,inv_pow]⟩
    simp only [if_neg (hh _),tsum_zero]
    apply integral_eq_zero_of_ae
    filter_upwards [(dx).ae_ne 0] with t ht
    exact mul_eq_zero_of_right _ (hzero (Units.mk0 t ht))

end MetaplecticPoisson.Datum
