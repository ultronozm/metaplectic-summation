import MetaplecticSummation.Jacquet.ArchWeak

/-! Corollary 10.4 at real and complex places: the pointwise bound
W(c) ≪ min(|c|^{1/n}, |c|^{-A}) for every Jacquet weight.

Following the paper, |W(c)| = |JΞ(c)| is at most ∫ |Ξ_X(c, y)| dy for the third shear
difference Ξ. After the substitution y = cz, the chart growth bound (4.2) handles |c| ≥ 1 and
the part of the line near the axis. On the rest of the line, the bound of order three on the
far vertical cone (`ShearVerticalBound`) applies, as in the proof of Lemma 10.3. -/

noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField MeasureTheory Set Filter
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n) (w : InfinitePlace F)
local notation "v" => (Sum.inl w : Place F)
local notation "K" => LocalField F v
local notation "dx" => selfDual F d.character v
local notation "m" => modulus F v

/-- Substitution y = c z in a real integral over the local field. -/
theorem integral_real_local_mul (c : Kˣ) (f : K → ℝ) :
    ∫ y, f y ∂dx = m c.val * ∫ z, f (c.val * z) ∂dx := by
  have h := d.integral_local_mul v c (fun y => (f y : ℂ))
  dsimp only at h
  rw [integral_complex_ofReal,integral_complex_ofReal] at h
  have hm : (m c.val : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (modulus_ne_zero v c)
  have h' : ((m c.val * ∫ z, f (c.val * z) ∂dx : ℝ) : ℂ) = ((∫ y, f y ∂dx : ℝ) : ℂ) := by
    push_cast; rw [h]; field_simp
  exact_mod_cast h'.symm

theorem modulus_mul_arch (x y : K) : m (x * y) = m x * m y := by
  simp [modulus,norm_mul,mul_pow]

/-- Corollary 10.4 at a real or complex place: every Jacquet weight satisfies
W(c) ≪ min(|c|^{1/n}, |c|^{-A}) for each A. -/
theorem jacquet_decay_arch (Φ : d.schwartz v) (A : ℕ) :
    ∃ C : ℝ, ∀ c : Kˣ, ‖d.jacquet v Φ c‖ ≤ C * min ((m c.val)^(1/(n:ℝ))) ((m c.val)^(-(A:ℝ))) := by
  obtain ⟨u,hu⟩ := d.character.nontrivial_localValue v
  obtain ⟨g,hg⟩ := (d.exists_upper v u).exists
  set Ξ := (d.jacquetDifference v u g)^[3] Φ with hΞ
  have hJ : d.jacquet v Ξ = d.jacquet v Φ := (d.jacquet_difference_iterate v u hu hg 3 Φ).1
  obtain ⟨C₀,B,hB,hSV⟩ := d.shearVerticalBound_arch w u hg Φ
  obtain ⟨Cg,hCg0,hCg⟩ := d.schwartz_chart_growth v Ξ (A+3) (by omega)
  set γ := growthExponent n
  have hγ0 : 0 ≤ γ := growthExponent_nonneg n
  have hn0 : (0:ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
  have hγ1 : 1 - γ = 1/(n:ℝ) := by
    simp only [γ,growthExponent]
    rw [Nat.cast_sub (NeZero.one_le : 1 ≤ n)]; field_simp; ring
  let C₁ := max C₀ 1
  have hC₁ : 1 ≤ C₁ := le_max_right _ _
  have hmpos (x : K) (hx : x ≠ 0) : 0 < m x := by simp [modulus,norm_pos_iff.mpr hx,pow_pos]
  have hm0 (x : K) : 0 ≤ m x := by simp only [modulus]; positivity
  have hX (c : Kˣ) (y : K) : xChart Ξ.val (c.val, y) = Ξ.val.1 c y := by
    simp [xChart,c.ne_zero]
  have hint := d.arch_integrable_inv_cube w
  let V := ∫ z : K, ((1+‖z‖)^3)⁻¹ ∂dx
  have hV : 0 ≤ V := integral_nonneg fun _ => by positivity
  -- the growth bound at a point (c, y)
  have grow (c : Kˣ) (y : K) : ‖Ξ.val.1 c y‖ ≤
      Cg * min ((max (m c.val) (m y))^(-γ)) ((max (m c.val) (m y))^(-((A+3 : ℕ) : ℝ))) := by
    have h := (hCg (c.val, y) (by simp [c.ne_zero])).1
    rwa [hX] at h
  -- pointwise bound after y = c z, small |c|
  let κ := Cg * (1+C₁)^3 + 8*B
  have small (c : Kˣ) (hc : m c.val < 1) (z : K) :
      ‖Ξ.val.1 c (c.val * z)‖ ≤ (m c.val)^(-γ) * κ * ((1+‖z‖)^3)⁻¹ := by
    have hmc := hmpos c.val c.ne_zero
    have hpow : 0 < (m c.val)^(-γ) := Real.rpow_pos_of_pos hmc _
    have hz3 : 0 < (1+‖z‖)^3 := by positivity
    rw [← mul_le_mul_iff_left₀ hz3,mul_assoc ((m c.val)^(-γ) * κ),inv_mul_cancel₀ hz3.ne',mul_one]
    by_cases hz : ‖z‖ ≤ C₁
    · have h1 := grow c (c.val * z)
      have h2 : (max (m c.val) (m (c.val * z)))^(-γ) ≤ (m c.val)^(-γ) :=
        Real.rpow_le_rpow_of_nonpos hmc (le_max_left _ _) (by linarith)
      have h3 : ‖Ξ.val.1 c (c.val * z)‖ ≤ Cg * (m c.val)^(-γ) :=
        h1.trans (mul_le_mul_of_nonneg_left ((min_le_left _ _).trans h2) hCg0)
      have h4 : (1+‖z‖)^3 ≤ (1+C₁)^3 := pow_le_pow_left₀ (by positivity) (by linarith) 3
      calc ‖Ξ.val.1 c (c.val * z)‖ * (1+‖z‖)^3 ≤ Cg * (m c.val)^(-γ) * (1+C₁)^3 :=
            mul_le_mul h3 h4 (by positivity) (by positivity)
        _ ≤ (m c.val)^(-γ) * κ := by
            simp only [κ]; nlinarith [mul_nonneg hpow.le hB]
    · have hz' : C₁ < ‖z‖ := lt_of_not_ge hz
      have hz1 : 1 < ‖z‖ := lt_of_le_of_lt hC₁ hz'
      have hcz : C₀ * ‖c.val‖ ≤ ‖c.val * z‖ := by
        rw [norm_mul,mul_comm ‖c.val‖]
        exact mul_le_mul_of_nonneg_right ((le_max_left _ _).trans hz'.le) (norm_nonneg _)
      have h1 := hSV c (c.val * z) hc hcz
      have hcn : 0 < ‖c.val‖ := norm_pos_iff.mpr c.ne_zero
      have h2 : (‖c.val‖ / ‖c.val * z‖)^3 * (1+‖z‖)^3 ≤ 8 := by
        rw [norm_mul,div_mul_cancel_left₀ hcn.ne',inv_pow,inv_mul_le_iff₀ (by positivity)]
        have : 1 + ‖z‖ ≤ 2 * ‖z‖ := by linarith
        calc (1+‖z‖)^3 ≤ (2*‖z‖)^3 := pow_le_pow_left₀ (by positivity) this 3
          _ = ‖z‖^3 * 8 := by ring
      calc ‖Ξ.val.1 c (c.val * z)‖ * (1+‖z‖)^3
          ≤ B * (m c.val)^(-γ) * (‖c.val‖ / ‖c.val * z‖)^3 * (1+‖z‖)^3 :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ ≤ B * (m c.val)^(-γ) * 8 := by
            rw [mul_assoc (B * (m c.val)^(-γ))]; exact mul_le_mul_of_nonneg_left h2 (by positivity)
        _ ≤ (m c.val)^(-γ) * κ := by
            simp only [κ]; nlinarith [mul_nonneg hpow.le (mul_nonneg hCg0 (by positivity : (0:ℝ) ≤ (1+C₁)^3))]
  -- large |c|
  have large (c : Kˣ) (hc : 1 ≤ m c.val) (z : K) :
      ‖Ξ.val.1 c (c.val * z)‖ ≤ ((m c.val)^(A+3))⁻¹ * (8 * Cg) * ((1+‖z‖)^3)⁻¹ := by
    have hmc : 0 < m c.val := by linarith
    set s := max 1 (m z)
    have hs1 : 1 ≤ s := le_max_left _ _
    have hr : m c.val * s ≤ max (m c.val) (m (c.val * z)) := by
      rw [modulus_mul_arch]
      rcases le_total (m z) 1 with h|h
      · rw [show s = 1 from max_eq_left h,mul_one]; exact le_max_left _ _
      · rw [show s = m z from max_eq_right h]; exact le_max_right _ _
    have h1 := (grow c (c.val * z)).trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hCg0)
    rw [Real.rpow_neg (by positivity),Real.rpow_natCast] at h1
    have h2 : ((max (m c.val) (m (c.val * z)))^(A+3))⁻¹ ≤ ((m c.val * s)^(A+3))⁻¹ :=
      inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hr _)
    have hsz : 1 + ‖z‖ ≤ 2 * s := by
      rcases le_total ‖z‖ 1 with h|h
      · linarith
      · have : ‖z‖ ≤ m z := by
          simp only [modulus]; exact le_self_pow₀ h (InfinitePlace.mult_ne_zero (w := w))
        linarith [le_max_right 1 (m z)]
    have h3 : (s^(A+3))⁻¹ ≤ 8 * ((1+‖z‖)^3)⁻¹ := by
      rw [← div_eq_mul_inv,le_div_iff₀ (by positivity),inv_mul_le_iff₀ (by positivity)]
      calc (1+‖z‖)^3 ≤ (2*s)^3 := pow_le_pow_left₀ (by positivity) hsz 3
        _ = 8 * s^3 := by ring
        _ ≤ 8 * s^(A+3) := by gcongr; omega
        _ = s^(A+3) * 8 := by ring
    calc ‖Ξ.val.1 c (c.val * z)‖ ≤ Cg * ((m c.val * s)^(A+3))⁻¹ := h1.trans (mul_le_mul_of_nonneg_left h2 hCg0)
      _ = Cg * ((m c.val)^(A+3))⁻¹ * (s^(A+3))⁻¹ := by rw [mul_pow,mul_inv]; ring
      _ ≤ Cg * ((m c.val)^(A+3))⁻¹ * (8 * ((1+‖z‖)^3)⁻¹) := by gcongr
      _ = _ := by ring
  have hκ : 0 ≤ κ := by positivity
  refine ⟨max (κ * V) (8 * Cg * V),fun c => ?_⟩
  rw [← hJ]
  have hmc := hmpos c.val c.ne_zero
  have hJb : ‖d.jacquet v Ξ c‖ ≤ m c.val * ∫ z, ‖Ξ.val.1 c (c.val * z)‖ ∂dx := by
    rw [← d.integral_real_local_mul w c (fun y => ‖Ξ.val.1 c y‖)]
    unfold jacquet
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr 1; funext y; rw [norm_mul,d.character.norm_localValue,mul_one]
  have hmin0 : 0 ≤ min ((m c.val)^(1/(n:ℝ))) ((m c.val)^(-(A:ℝ))) :=
    le_min (Real.rpow_nonneg hmc.le _) (Real.rpow_nonneg hmc.le _)
  by_cases hc : m c.val < 1
  · have hI : ∫ z, ‖Ξ.val.1 c (c.val * z)‖ ∂dx ≤ (m c.val)^(-γ) * κ * V := by
      rw [← integral_const_mul]
      exact integral_mono_of_nonneg (.of_forall fun _ => norm_nonneg _) (hint.const_mul _)
        (.of_forall (small c hc))
    have hmin : min ((m c.val)^(1/(n:ℝ))) ((m c.val)^(-(A:ℝ))) = (m c.val)^(1/(n:ℝ)) := by
      refine min_eq_left ((Real.rpow_le_one hmc.le hc.le (by positivity)).trans ?_)
      exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hmc hc.le (by simp)
    rw [hmin]
    calc ‖d.jacquet v Ξ c‖ ≤ m c.val * ((m c.val)^(-γ) * κ * V) :=
          hJb.trans (mul_le_mul_of_nonneg_left hI hmc.le)
      _ = (m c.val)^(1 + -γ) * (κ * V) := by rw [Real.rpow_add hmc,Real.rpow_one]; ring
      _ = (κ * V) * (m c.val)^(1/(n:ℝ)) := by rw [← sub_eq_add_neg,hγ1]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hmc.le _)
  · have hc1 : 1 ≤ m c.val := le_of_not_gt hc
    have hI : ∫ z, ‖Ξ.val.1 c (c.val * z)‖ ∂dx ≤ ((m c.val)^(A+3))⁻¹ * (8 * Cg) * V := by
      rw [← integral_const_mul]
      exact integral_mono_of_nonneg (.of_forall fun _ => norm_nonneg _) (hint.const_mul _)
        (.of_forall (large c hc1))
    have hmin : min ((m c.val)^(1/(n:ℝ))) ((m c.val)^(-(A:ℝ))) = (m c.val)^(-(A:ℝ)) := by
      refine min_eq_right ((Real.rpow_le_one_of_one_le_of_nonpos hc1 (by simp)).trans ?_)
      exact Real.one_le_rpow hc1 (by positivity)
    rw [hmin,Real.rpow_neg hmc.le,Real.rpow_natCast]
    have hpow : m c.val * ((m c.val)^(A+3))⁻¹ ≤ ((m c.val)^A)⁻¹ := by
      rw [← div_eq_mul_inv,div_le_iff₀ (by positivity),pow_add,inv_mul_eq_div]
      rw [le_div_iff₀ (by positivity)]
      have : m c.val ≤ (m c.val)^3 := le_self_pow₀ hc1 (by norm_num)
      nlinarith [pow_pos hmc A]
    calc ‖d.jacquet v Ξ c‖ ≤ m c.val * (((m c.val)^(A+3))⁻¹ * (8 * Cg) * V) :=
          hJb.trans (mul_le_mul_of_nonneg_left hI hmc.le)
      _ = (m c.val * ((m c.val)^(A+3))⁻¹) * (8 * Cg * V) := by ring
      _ ≤ ((m c.val)^A)⁻¹ * (8 * Cg * V) := mul_le_mul_of_nonneg_right hpow (by positivity)
      _ ≤ _ := by rw [mul_comm]; exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

end MetaplecticPoisson.Datum
