import MetaplecticSummation.BasicFixed
import MetaplecticSummation.TransformScaling

/-! The transform of the basic vector for an arbitrary finite conductor (Corollary 6.5). -/

noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField IsDedekindDomain MeasureTheory Filter
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n) (p : Prime F)
local notation "v" => (Sum.inr p : Place F)
local notation "K" => LocalField F v

private theorem rational_same_norm (b : Kˣ) : ∃ a : Fˣ, ‖(atPlace v a).val‖ = ‖b.val‖ := by
  let β : p.adicCompletion F := b.val
  have hβ : 0 < ‖β‖ := norm_pos_iff.mpr b.ne_zero
  obtain ⟨a,ha⟩ := (HeightOneSpectrum.denseRange_algebraMap («K» := F) p).mem_nhds (Metric.ball_mem_nhds β hβ)
  let z := algebraMap F (p.adicCompletion F) a
  change dist z β < ‖β‖ at ha
  rw [dist_eq_norm] at ha
  have he : ‖z‖ = ‖β‖ := calc
    ‖z‖ = ‖(z-β)+β‖ := by rw [sub_add_cancel]
    _ = ‖β‖ := (IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm ha.ne).trans (max_eq_right ha.le)
  have ha₀ : a ≠ 0 := by
    intro h
    simp [z,h] at he
    exact hβ.ne' he.symm
  exact ⟨Units.mk0 a ha₀,he⟩

private theorem basic_power_dilate_eq (a b : Kˣ) (hb : ‖a.val‖ = ‖b.val‖) :
    dilateCharts (a^n) (d.basicCharts p) = dilateCharts (b^n) (d.basicCharts p) := by
  let f := d.basicCharts p
  have hx (x : Kˣ) (y : K) : f.1 (a^n*x) (a.val^n*y) = f.1 (b^n*x) (b.val^n*y) := by
    let H := d.unitPairing v
    have hs (u Y : Kˣ) : d.symbol v (u^n*x) (u^n*Y) = d.symbol v x Y := by
      change (H (u^n*x) (u^n*Y)).val = _
      have ht (r s : Kˣ) : (H r s)^n = 1 := d.unitPairing_pow v r s
      simp only [map_mul,map_pow,MonoidHom.mul_apply,MonoidHom.pow_apply,ht,one_mul]
      rfl
    simp only [f,basicCharts,Units.val_mul,Units.val_pow_eq_pow_val,norm_mul,norm_pow,hb]
    by_cases hy : y = 0
    · simp [hy]
    · let Y := Units.mk0 y hy
      have pair (u : Kˣ) : Units.mk0 (u.val^n*y) (mul_ne_zero (pow_ne_zero _ u.ne_zero) hy) = u^n*Y := Units.ext rfl
      simp only [dif_pos (mul_ne_zero (pow_ne_zero _ a.ne_zero) hy),
        dif_pos (mul_ne_zero (pow_ne_zero _ b.ne_zero) hy),pair,hs]
  apply Prod.ext
  · exact funext fun x => funext fun y => hx x y
  · funext x y
    change f.2 (a.val^n*x) (a^n*y) = f.2 (b.val^n*x) (b^n*y)
    have swap (X : Kˣ) (Y : K) : f.2 Y X = f.1 X Y := by simp only [f,basicCharts,max_comm ‖Y‖ ‖X.val‖]
    exact (swap _ _).trans ((hx y x).trans (swap _ _).symm)

omit [NeZero n] in
private theorem scaled_unramified_of_conductor (b : Kˣ)
    (conductor : ∀ x : K, (∀ y : K, ‖y‖ ≤ 1 → d.character.localValue F v (x*y) = 1) ↔ ‖x*b.val‖ ≤ 1)
    (a : Fˣ) (ha : ‖(atPlace v a).val‖ = ‖b.val‖) : (d.scaled a⁻¹).UnramifiedAt v := by
  let A := atPlace v a
  intro x
  simp_rw [d.scaled_localValue,← mul_assoc,conductor,norm_mul]
  change ‖A⁻¹.val‖ * ‖x‖ * ‖b.val‖ ≤ 1 ↔ _
  rw [Units.val_inv_eq_inv_val,norm_inv,show ‖A.val‖ = ‖b.val‖ from ha,mul_right_comm,
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr b.ne_zero),one_mul]

omit [NeZero n] in
/-- At each finite place one can normalize the character by a global scalar. -/
theorem exists_unramified_scaling : ∃ a : Fˣ, (d.scaled a).UnramifiedAt v := by
  obtain ⟨b,hb⟩ := d.exists_finite_conductor p
  obtain ⟨a,ha⟩ := rational_same_norm p b
  exact ⟨a⁻¹,d.scaled_unramified_of_conductor p b hb a ha⟩

/-- Corollary 6.5 in both charts. The conductor parameter is local. -/
theorem basicCharts_fourier_conductor (hp : p.asIdeal.absNorm.Coprime n) (b : Kˣ)
    (conductor : ∀ x : K, (∀ y : K, ‖y‖ ≤ 1 → d.character.localValue F v (x*y) = 1) ↔ ‖x*b.val‖ ≤ 1) :
    d.integralTransform v (d.basicCharts p) =
      (‖b.val‖ : ℂ)^n • dilateCharts (b^n) (d.basicCharts p) := by
  obtain ⟨a,ha⟩ := rational_same_norm p b
  let A := atPlace v a
  have hAi : atPlace v a⁻¹ = A⁻¹ := map_inv _ _
  have hψ := d.scaled_unramified_of_conductor p b conductor a ha
  let f := d.basicCharts p
  let T := d.integralTransform v f
  have h := (d.scaled a⁻¹).basicCharts_fourier_fixed p hp hψ
  change (d.scaled a⁻¹).integralTransform v f = f at h
  rw [d.integralTransform_scaled] at h
  change (‖(atPlace v a⁻¹).val‖ : ℂ)^n • dilateCharts ((atPlace v a⁻¹)^n) T = f at h
  rw [hAi,Units.val_inv_eq_inv_val,norm_inv,Complex.ofReal_inv,inv_pow,
    inv_smul_eq_iff₀ (pow_ne_zero n (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr A.ne_zero)))] at h
  rw [← d.basic_power_dilate_eq p A b ha,← ha]
  change T = (‖A.val‖ : ℂ)^n • dilateCharts (A^n) f
  have h' := congrArg (dilateCharts (A^n)) h
  simp only [dilateCharts,Prod.smul_fst,Prod.smul_snd,Pi.smul_apply,smul_eq_mul,Units.val_pow_eq_pow_val,
    Units.val_inv_eq_inv_val,← mul_assoc,inv_pow,inv_mul_cancel₀ (pow_ne_zero _ A.ne_zero),inv_mul_cancel,
    one_mul,Prod.mk.eta] at h'
  exact h'

/-- The change of conductor in the basic Jacquet integral, directly on the explicit charts. -/
theorem basicCharts_jacquet_dual (hp : p.asIdeal.absNorm.Coprime n) (b : Kˣ)
    (conductor : ∀ x : K, (∀ y : K, ‖y‖ ≤ 1 → d.character.localValue F v (x*y) = 1) ↔ ‖x*b.val‖ ≤ 1)
    (c : Kˣ) :
    (∫ y, (d.integralTransform v (d.basicCharts p)).1 c y * d.character.localValue F v (-y/c.val)
      ∂selfDual F d.character v) = ∫ y, (d.basicCharts p).1 (b^n*c) y *
        d.character.localValue F v (-y/(b^n*c).val) ∂selfDual F d.character v := by
  let B := b^n
  let f := d.basicCharts p
  let g (y : K) := f.1 (B*c) y * d.character.localValue F v (-y/(B*c).val)
  have hB : B.val ≠ 0 := B.ne_zero
  have hphase (y : K) : -(B.val*y)/(B*c).val = -y/c.val := by
    rw [Units.val_mul]
    field_simp
  have he := d.integral_local_mul v B g
  simp only [g,hphase] at he
  have hm : (modulus F v B.val : ℂ) = (‖b.val‖ : ℂ)^n := by
    change (‖(b^n).val‖ : ℂ) = _
    rw [Units.val_pow_eq_pow_val,norm_pow,Complex.ofReal_pow]
  rw [hm] at he
  rw [d.basicCharts_fourier_conductor p hp b conductor]
  change (∫ y, ((‖b.val‖ : ℂ)^n * f.1 (B*c) (B.val*y)) *
    d.character.localValue F v (-y/c.val) ∂selfDual F d.character v) = _
  simp_rw [mul_assoc]
  rw [integral_const_mul,he,mul_div_cancel₀ _ (pow_ne_zero n (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr b.ne_zero)))]

end MetaplecticPoisson.Datum
