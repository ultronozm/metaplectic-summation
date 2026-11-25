import MetaplecticSummation.RootKernel

/-! Estimates for the Plancherel part of Theorem 7.1. Every local Schwartz section is
square integrable, and its product with the root kernel and a second section is
absolutely integrable on the product of two planes. The integral of the chart bound
against |[v,w]|^(-1+1/n) over v is at most a constant over the chart radius of w plus
a constant, by the weighted bound in one variable after an affine change. A symbol
identity gives the adjoint relation of the root kernel. -/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
open Classical
namespace MetaplecticPoisson
/-- The symbol identity behind the adjoint relation of the root kernel. -/
theorem LineSymbol.kernel_symbol {K : Type*} [Field K] {n : ℕ} (H : LineSymbol K n) (w v : Kˣ) :
    H.pairing w (-((-1)^(n+1)*v)) * H.pairing v (-w) =
      H.pairing ((-1)^(n+1)*v) ((-1)^(n+1)) * H.pairing (-1) ((-1)^(n+1)) := by
  have hneg : -((-1 : Kˣ)^(n+1)) = (-1)^n := by rw [pow_succ]; simp
  have e1 : H.pairing w (-((-1)^(n+1)*v)) = H.pairing w v := by
    rw [show -((-1 : Kˣ)^(n+1)*v) = (-((-1)^(n+1))) * v by simp,hneg,map_mul,H.pow_right,one_mul]
  have e2 : H.pairing v (-w) = H.pairing v (-1) * (H.pairing w v)⁻¹ := by
    rw [show -w = (-1 : Kˣ) * w by simp,map_mul,H.skew v w]
  have e3 : H.pairing ((-1 : Kˣ)^(n+1)*v) ((-1)^(n+1)) * H.pairing (-1) ((-1)^(n+1)) =
      H.pairing v ((-1)^(n+1)) := by
    rw [map_mul,MonoidHom.mul_apply,mul_comm (H.pairing ((-1)^(n+1)) _),mul_assoc,← MonoidHom.mul_apply,
      ← map_mul,show (-1 : Kˣ)^(n+1) * (-1) = (-1)^n by rw [pow_succ]; simp,H.pow_left,mul_one]
  have e4 : H.pairing v ((-1 : Kˣ)^(n+1)) = H.pairing v (-1) := by
    rw [pow_succ,map_mul,H.pow_right,one_mul]
  rw [e1,e2,e3,e4,mul_comm (H.pairing v (-1)),← mul_assoc,mul_inv_cancel,one_mul]

end MetaplecticPoisson

namespace MetaplecticPoisson.Datum
open NumberField
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n) (v : Place F)
local notation "Kv" => LocalField F v
local notation "dx" => selfDual F d.character v
local notation "m" => modulus F v

omit [NeZero n] in
theorem card_nthRootsFinset_le' (a : Kv) : (Polynomial.nthRootsFinset n a).card ≤ n := by
  classical
  unfold Polynomial.nthRootsFinset
  exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots n a)

/-- Each root τ of a nonzero determinant D contributes |D|^(-γ). -/
theorem rootSum_norm_le (D : Kv) (hD : D ≠ 0) :
    ‖∑ τ ∈ Polynomial.nthRootsFinset n D, d.character.localValue F v τ * (m τ : ℂ)^(1-(n:ℤ))‖ ≤
      n * (m D)^(-growthExponent n) := by
  have hm0 (z : Kv) : 0 ≤ m z := by cases v <;> simp [modulus,pow_nonneg]
  have mpow (x : Kv) : m (x^n) = m x ^ n := by cases v <;> simp [modulus,norm_pow,← pow_mul,mul_comm]
  have hmpos (z : Kv) (hz : z ≠ 0) : 0 < m z := by cases v <;> simp [modulus,norm_pos_iff.mpr hz,pow_pos]
  refine (norm_sum_le _ _).trans ?_
  have hterm (τ : Kv) (hτ : τ ∈ Polynomial.nthRootsFinset n D) :
      ‖d.character.localValue F v τ * (m τ : ℂ)^(1-(n:ℤ))‖ = (m D)^(-growthExponent n) := by
    have hτn := (Polynomial.mem_nthRootsFinset (NeZero.pos n) _).mp hτ
    have hτ0 : τ ≠ 0 := by rintro rfl; rw [zero_pow (NeZero.ne n)] at hτn; exact hD hτn.symm
    have hτp := hmpos τ hτ0
    rw [norm_mul,d.character.norm_localValue,one_mul,norm_zpow,Complex.norm_real,
      Real.norm_of_nonneg hτp.le,← hτn,mpow]
    rw [← Real.rpow_intCast,← Real.rpow_natCast,← Real.rpow_mul hτp.le]
    congr 1
    simp only [growthExponent]
    rw [Nat.cast_sub (NeZero.one_le : 1 ≤ n)]
    push_cast
    field_simp [show (n:ℝ) ≠ 0 by exact_mod_cast NeZero.ne n]
    ring
  rw [Finset.sum_congr rfl hterm,Finset.sum_const,nsmul_eq_mul]
  gcongr
  · exact Real.rpow_nonneg (hm0 _) _
  · exact_mod_cast card_nthRootsFinset_le' v D

omit [NeZero n] in
/-- Affine change of variables for nonnegative functions. -/
theorem lintegral_affine_local (f : Kv → ℝ≥0∞) (k : Kvˣ) (b : Kv) :
    (∫⁻ z, f (k.val*z+b) ∂dx) = ENNReal.ofReal (m k.val)⁻¹ * ∫⁻ z, f z ∂dx := by
  let : (dx).IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  let e := MeasurableEquiv.smul (α := Kv) k
  have h := e.measurableEmbedding.lintegral_map (μ := dx) (fun t => f (t+b))
  change (∫⁻ t, f (t+b) ∂Measure.map (fun t => k.val*t) dx) = ∫⁻ z, f (k.val*z+b) ∂dx at h
  rw [← h,d.map_local_mul,lintegral_smul_measure,lintegral_add_right_eq_self]
  rw [ENNReal.smul_def,smul_eq_mul,ENNReal.ofReal,Real.toNNReal_inv,ENNReal.coe_inv]
  have hk : 0 < m k.val := by cases v <;> simp [modulus,norm_pos_iff.mpr k.ne_zero,pow_pos]
  exact (Real.toNNReal_pos.mpr hk).ne'

omit [NeZero n] in
private theorem modulus_rpow_le_weight (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ : γ ≤ 2) (u : Kv) :
    (m u)^(-γ) ≤ min ((m u)^(-γ)) ((m u)^(-(2:ℝ))) + 1 := by
  have hm0 : 0 ≤ m u := by cases v <;> simp [modulus,pow_nonneg]
  rcases eq_or_lt_of_le hm0 with h|h
  · rw [← h]
    rcases eq_or_lt_of_le hγ0 with hg|hg
    · rw [← hg]; simp
    · rw [Real.zero_rpow (by linarith),Real.zero_rpow (by norm_num)]
      norm_num
  rcases le_total (m u) 1 with h1|h1
  · rw [min_eq_left (Real.rpow_le_rpow_of_exponent_ge h h1 (by linarith))]
    linarith
  · have : (m u)^(-γ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith)
    linarith [le_min (Real.rpow_nonneg hm0 (-γ)) (Real.rpow_nonneg hm0 (-(2:ℝ)))]

omit [NeZero n] in
/-- A bounded function against a power of an affine form, in one variable. -/
theorem lintegral_affine_weight (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ : γ ≤ 2)
    {φ : Kv → ℝ≥0∞} (hφ : Measurable φ) {M : ℝ≥0∞} (hM : ∀ s, φ s ≤ M) (k : Kvˣ) (b : Kv) :
    (∫⁻ s, φ s * ENNReal.ofReal ((m (k.val*s+b))^(-γ)) ∂dx) ≤
      M * (ENNReal.ofReal (m k.val)⁻¹ *
        ∫⁻ u, ENNReal.ofReal (min ((m u)^(-γ)) ((m u)^(-(2:ℝ)))) ∂dx) + ∫⁻ s, φ s ∂dx := by
  let W (u : Kv) := ENNReal.ofReal (min ((m u)^(-γ)) ((m u)^(-(2:ℝ))))
  have hmc : Continuous m := by
    show Continuous (modulus F v)
    cases v with
    | inl w => exact continuous_norm.pow _
    | inr p => exact continuous_norm
  have hWm : Measurable W := ENNReal.measurable_ofReal.comp
    ((hmc.measurable.pow_const _).min (hmc.measurable.pow_const _))
  have hpt (s : Kv) : φ s * ENNReal.ofReal ((m (k.val*s+b))^(-γ)) ≤ M * W (k.val*s+b) + φ s := by
    have h := modulus_rpow_le_weight (F := F) v γ hγ0 hγ (k.val*s+b)
    calc φ s * ENNReal.ofReal ((m (k.val*s+b))^(-γ))
        ≤ φ s * (W (k.val*s+b) + 1) := by
          gcongr
          rw [← ENNReal.ofReal_one,← ENNReal.ofReal_add (le_min (Real.rpow_nonneg (by cases v <;> simp [modulus,pow_nonneg]) _)
            (Real.rpow_nonneg (by cases v <;> simp [modulus,pow_nonneg]) _)) zero_le_one]
          exact ENNReal.ofReal_le_ofReal h
      _ = φ s * W (k.val*s+b) + φ s := by rw [mul_add,mul_one]
      _ ≤ M * W (k.val*s+b) + φ s := by gcongr; exact hM s
  refine (lintegral_mono hpt).trans ?_
  have hWk : Measurable (fun s : Kv => W (k.val*s+b)) := hWm.comp (by fun_prop)
  rw [lintegral_add_right _ hφ,lintegral_const_mul M hWk,d.lintegral_affine_local v W k b]

omit [NeZero n] in
/-- The two-variable estimate behind the interchange of integrals in Theorem 7.1(iii). -/
theorem lintegral_kernel_bound (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ : γ ≤ 2) (x' : Kvˣ) (y' : Kv) :
    let fr := fun z : Kv × Kv => min ((max (m z.1) (m z.2))^(-γ)) ((max (m z.1) (m z.2))^(-(4:ℝ)))
    let Fr := fun s : Kv => min ((m s)^(-γ)) ((m s)^(-(4:ℝ)))
    let I := ∫⁻ u, ENNReal.ofReal (min ((m u)^(-γ)) ((m u)^(-(2:ℝ)))) ∂dx
    (∫⁻ z, ENNReal.ofReal (fr z) * ENNReal.ofReal ((m (z.1*y' - z.2*x'.val))^(-γ)) ∂((dx).prod dx)) ≤
      (∫⁻ s, ENNReal.ofReal (Fr s) ∂dx) * I * ENNReal.ofReal (max (m x'.val) (m y'))⁻¹ +
        ∫⁻ z, ENNReal.ofReal (fr z) ∂((dx).prod dx) := by
  intro fr Fr I
  let : (dx).IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  let : NullSingletonClass dx := d.selfDual_nullSingleton v
  have hm0 (z : Kv) : 0 ≤ m z := by cases v <;> simp [modulus,pow_nonneg]
  have hmpos (z : Kv) (hz : z ≠ 0) : 0 < m z := by cases v <;> simp [modulus,norm_pos_iff.mpr hz,pow_pos]
  have mneg (a : Kv) : m (-a) = m a := by cases v <;> simp [modulus]
  have hmc : Continuous m := by
    show Continuous (modulus F v)
    cases v with
    | inl w => exact continuous_norm.pow _
    | inr p => exact continuous_norm
  have hfrm : Measurable fr := by
    have h := (hmc.comp continuous_fst).max (hmc.comp continuous_snd)
    exact (h.measurable.pow_const _).min (h.measurable.pow_const _)
  have hKm : Measurable (fun z : Kv × Kv => (m (z.1*y' - z.2*x'.val))^(-γ)) :=
    ((hmc.comp (by fun_prop : Continuous fun z : Kv × Kv => z.1*y' - z.2*x'.val)).measurable.pow_const _)
  have hint_m : Measurable (fun z : Kv × Kv => ENNReal.ofReal (fr z) * ENNReal.ofReal ((m (z.1*y' - z.2*x'.val))^(-γ))) :=
    (ENNReal.measurable_ofReal.comp hfrm).mul (ENNReal.measurable_ofReal.comp hKm)
  have anti (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) : min (b^(-γ)) (b^(-(4:ℝ))) ≤ min (a^(-γ)) (a^(-(4:ℝ))) :=
    min_le_min (Real.rpow_le_rpow_of_nonpos ha hab (by linarith)) (Real.rpow_le_rpow_of_nonpos ha hab (by norm_num))
  have hB : (∫⁻ z, ENNReal.ofReal (fr z) ∂((dx).prod dx)) =
      ∫⁻ x, ∫⁻ y, ENNReal.ofReal (fr (x,y)) ∂dx ∂dx :=
    lintegral_prod _ (ENNReal.measurable_ofReal.comp hfrm).aemeasurable
  have hBs : (∫⁻ z, ENNReal.ofReal (fr z) ∂((dx).prod dx)) =
      ∫⁻ y, ∫⁻ x, ENNReal.ofReal (fr (x,y)) ∂dx ∂dx :=
    lintegral_prod_symm _ (ENNReal.measurable_ofReal.comp hfrm).aemeasurable
  -- the bound with the first coefficient
  have caseA : (∫⁻ z, ENNReal.ofReal (fr z) * ENNReal.ofReal ((m (z.1*y' - z.2*x'.val))^(-γ)) ∂((dx).prod dx)) ≤
      (∫⁻ s, ENNReal.ofReal (Fr s) ∂dx) * I * ENNReal.ofReal (m x'.val)⁻¹ +
        ∫⁻ z, ENNReal.ofReal (fr z) ∂((dx).prod dx) := by
    rw [lintegral_prod _ hint_m.aemeasurable,hB]
    calc (∫⁻ x, ∫⁻ y, ENNReal.ofReal (fr (x,y)) * ENNReal.ofReal ((m (x*y' - y*x'.val))^(-γ)) ∂dx ∂dx)
        ≤ ∫⁻ x, (ENNReal.ofReal (Fr x) * (ENNReal.ofReal (m x'.val)⁻¹ * I) +
            ∫⁻ y, ENNReal.ofReal (fr (x,y)) ∂dx) ∂dx := by
          apply lintegral_mono_ae
          filter_upwards [(dx).ae_ne 0] with x hx
          have h := d.lintegral_affine_weight v γ hγ0 hγ (φ := fun y => ENNReal.ofReal (fr (x,y)))
            ((ENNReal.measurable_ofReal.comp hfrm).comp (measurable_const.prodMk measurable_id))
            (M := ENNReal.ofReal (Fr x))
            (fun y => ENNReal.ofReal_le_ofReal (anti _ _ (hmpos x hx) (le_max_left _ _))) (-x') (x*y')
          simp only [Units.val_neg,mneg] at h
          convert h using 3
          congr 3; ring
        _ = _ := by
          have hFm : Measurable (fun x => ENNReal.ofReal (Fr x)) :=
            ENNReal.measurable_ofReal.comp ((hmc.measurable.pow_const _).min (hmc.measurable.pow_const _))
          rw [lintegral_add_left (hFm.mul_const _),lintegral_mul_const _ hFm]
          ring
  have hFm : Measurable (fun x => ENNReal.ofReal (Fr x)) :=
    ENNReal.measurable_ofReal.comp ((hmc.measurable.pow_const _).min (hmc.measurable.pow_const _))
  rcases le_total (m y') (m x'.val) with hle|hle
  · rwa [max_eq_left hle]
  have hy' : y' ≠ 0 := by
    intro h; rw [h] at hle
    have := hmpos _ x'.ne_zero
    have h0 : m (0:Kv) = 0 := by cases v <;> simp [modulus]
    linarith
  rw [max_eq_right hle]
  let Y' := Units.mk0 y' hy'
  rw [lintegral_prod_symm _ hint_m.aemeasurable,hBs]
  calc (∫⁻ y, ∫⁻ x, ENNReal.ofReal (fr (x,y)) * ENNReal.ofReal ((m (x*y' - y*x'.val))^(-γ)) ∂dx ∂dx)
      ≤ ∫⁻ y, (ENNReal.ofReal (Fr y) * (ENNReal.ofReal (m y')⁻¹ * I) +
          ∫⁻ x, ENNReal.ofReal (fr (x,y)) ∂dx) ∂dx := by
        apply lintegral_mono_ae
        filter_upwards [(dx).ae_ne 0] with y hy
        have h := d.lintegral_affine_weight v γ hγ0 hγ (φ := fun x => ENNReal.ofReal (fr (x,y)))
          ((ENNReal.measurable_ofReal.comp hfrm).comp (measurable_id.prodMk measurable_const))
          (M := ENNReal.ofReal (Fr y))
          (fun x => ENNReal.ofReal_le_ofReal (anti _ _ (hmpos y hy) (le_max_right _ _))) Y' (-(y*x'.val))
        simp only [Y',Units.val_mk0] at h
        convert h using 3
        congr 3; ring
    _ = _ := by
        rw [lintegral_add_left (hFm.mul_const _),lintegral_mul_const _ hFm]
        ring

omit [NeZero n] in
/-- Two-sided powers of the chart radius are integrable on the plane when the
exponent at the origin is below two. -/
theorem lintegral_radius_finite {γ' : ℝ} (h0 : 0 ≤ γ') (h2 : γ' < 2) :
    (∫⁻ z, ENNReal.ofReal (min ((max (m z.1) (m z.2))^(-γ')) ((max (m z.1) (m z.2))^(-(4:ℝ))))
      ∂((dx).prod dx)) < ∞ := by
  let : (dx).IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  let : NullSingletonClass dx := d.selfDual_nullSingleton v
  have hmpos (z : Kv) (hz : z ≠ 0) : 0 < m z := by cases v <;> simp [modulus,norm_pos_iff.mpr hz,pow_pos]
  let β := γ'/2
  let A (s : Kv) := min ((m s)^(-(γ'-β))) ((m s)^(-(2:ℝ)))
  let B (s : Kv) := min ((m s)^(-β)) ((m s)^(-(2:ℝ)))
  have hA : Integrable A dx := d.integrable_modulus_two_sided v (by simp only [β]; linarith)
    (by simp only [β]; linarith) (by norm_num)
  have hB : Integrable B dx := d.integrable_modulus_two_sided v (by simp only [β]; linarith)
    (by simp only [β]; linarith) (by norm_num)
  calc _ ≤ ∫⁻ z, ENNReal.ofReal (A z.1) * ENNReal.ofReal (B z.2) ∂((dx).prod dx) := by
        apply lintegral_mono_ae
        filter_upwards [Measure.quasiMeasurePreserving_fst.ae ((dx).ae_ne 0),
          Measure.quasiMeasurePreserving_snd.ae ((dx).ae_ne 0)] with z h1 h2
        rw [← ENNReal.ofReal_mul (le_min (Real.rpow_nonneg (hmpos _ h1).le _) (Real.rpow_nonneg (hmpos _ h1).le _))]
        exact ENNReal.ofReal_le_ofReal (min_max_rpow_le (hmpos _ h1) (hmpos _ h2) (by simp only [β]; linarith)
          (by simp only [β]; linarith) (by linarith))
    _ = (∫⁻ s, ENNReal.ofReal (A s) ∂dx) * ∫⁻ s, ENNReal.ofReal (B s) ∂dx :=
        lintegral_prod_mul (ENNReal.measurable_ofReal.comp_aemeasurable hA.aemeasurable)
          (ENNReal.measurable_ofReal.comp_aemeasurable hB.aemeasurable)
    _ < ∞ := ENNReal.mul_lt_top hA.lintegral_lt_top hB.lintegral_lt_top

/-- The chart bound (4.2) in terms of the chart radius, everywhere on the plane. -/
theorem xChart_radius_bound (Φ : d.schwartz v) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Kv × Kv, ‖xChart Φ.val z‖ ≤
      C * min ((max (m z.1) (m z.2))^(-growthExponent n)) ((max (m z.1) (m z.2))^(-(4:ℝ))) := by
  obtain ⟨C,hC,H⟩ := d.schwartz_chart_growth v Φ 4 (by decide)
  refine ⟨C,hC,fun z => ?_⟩
  by_cases hz : z = 0
  · have hm0 (a : Kv) : 0 ≤ m a := by cases v <;> simp [modulus,pow_nonneg]
    simp only [hz,xChart,Prod.fst_zero,ne_eq,not_true_eq_false,dite_false,norm_zero]
    exact mul_nonneg hC (le_min (Real.rpow_nonneg (le_max_of_le_left (hm0 _)) _)
      (Real.rpow_nonneg (le_max_of_le_left (hm0 _)) _))
  · simpa using (H z hz).1

/-- Theorem 7.1(iii), finiteness: every local Schwartz section is square integrable. -/
theorem lintegral_xChart_sq_lt_top (Φ : d.schwartz v) :
    (∫⁻ z, ‖xChart Φ.val z‖ₑ^2 ∂((dx).prod dx)) < ∞ := by
  obtain ⟨C,hC,H⟩ := d.xChart_radius_bound v Φ
  let γ := growthExponent n
  have hγ0 : 0 ≤ γ := growthExponent_nonneg n
  have hγ1 : γ < 1 := by
    simp only [γ,growthExponent]
    rw [div_lt_one (by exact_mod_cast NeZero.pos n)]
    exact_mod_cast Nat.sub_lt (NeZero.pos n) one_pos
  have hm0 (a : Kv) : 0 ≤ m a := by cases v <;> simp [modulus,pow_nonneg]
  have hfin := d.lintegral_radius_finite v (γ' := 2*γ) (by positivity) (by linarith)
  calc (∫⁻ z, ‖xChart Φ.val z‖ₑ^2 ∂((dx).prod dx))
      ≤ ∫⁻ z, ENNReal.ofReal (C^2) * ENNReal.ofReal (min ((max (m z.1) (m z.2))^(-(2*γ)))
          ((max (m z.1) (m z.2))^(-(4:ℝ)))) ∂((dx).prod dx) := by
        apply lintegral_mono
        intro z
        dsimp only
        set r := max (m z.1) (m z.2)
        have hr0 : 0 ≤ r := le_max_of_le_left (hm0 _)
        rw [← ENNReal.ofReal_mul (by positivity),← ofReal_norm,← ENNReal.ofReal_pow (norm_nonneg _)]
        apply ENNReal.ofReal_le_ofReal
        have h1 := H z
        have hmin0 : 0 ≤ min (r^(-γ)) (r^(-(4:ℝ))) := le_min (Real.rpow_nonneg hr0 _) (Real.rpow_nonneg hr0 _)
        calc ‖xChart Φ.val z‖^2 ≤ (C * min (r^(-γ)) (r^(-(4:ℝ))))^2 :=
              pow_le_pow_left₀ (norm_nonneg _) h1 2
          _ = C^2 * (min (r^(-γ)) (r^(-(4:ℝ))))^2 := by ring
          _ ≤ C^2 * min (r^(-(2*γ))) (r^(-(4:ℝ))) := by
              gcongr
              rcases eq_or_lt_of_le hr0 with h|h
              · rw [← h]
                rcases eq_or_lt_of_le hγ0 with hg|hg
                · rw [← hg]; simp
                · rw [Real.zero_rpow (by linarith),Real.zero_rpow (by norm_num)]
                  simp only [min_self,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow]
                  exact le_min (Real.rpow_nonneg le_rfl _) le_rfl
              rcases le_total r 1 with h1|h1
              · rw [min_eq_left (Real.rpow_le_rpow_of_exponent_ge h h1 (by linarith)),
                  min_eq_left (Real.rpow_le_rpow_of_exponent_ge h h1 (by linarith)),
                  ← Real.rpow_natCast,← Real.rpow_mul h.le]
                norm_num; ring_nf; exact le_rfl
              · rw [min_eq_right (Real.rpow_le_rpow_of_exponent_le h1 (by linarith)),
                  min_eq_right (Real.rpow_le_rpow_of_exponent_le h1 (by linarith)),
                  ← Real.rpow_natCast,← Real.rpow_mul h.le]
                exact Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
    _ < ∞ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

end MetaplecticPoisson.Datum
