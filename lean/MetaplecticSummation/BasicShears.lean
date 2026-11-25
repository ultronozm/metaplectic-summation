import MetaplecticSummation.SmoothFiniteLines

/-! Integral unipotent invariance of the tame basic vector (§6). -/

noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField IsDedekindDomain
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)
variable (p : HeightOneSpectrum (𝓞 F))
local notation "v" => (Sum.inr p : Place F)

local notation "K" => LocalField F v
local instance : IsUltrametricDist K := inferInstanceAs (IsUltrametricDist (p.adicCompletion F))

private abbrev radialWeight (r : ℝ) : ℂ := ∑' k : ℕ,
  if r = ((p.asIdeal.absNorm : ℝ)^(n*k))⁻¹ then (p.asIdeal.absNorm : ℂ)^((n-1)*k) else 0

/-- Multiplying either argument by an n-th power leaves the symbol unchanged. -/
theorem symbol_div_powers (x y s t : Kˣ) :
    d.symbol v (x/s^n) (y/t^n) = d.symbol v x y := by
  let H := d.unitPairing v
  have h (a b : Kˣ) : H a b ^ n = 1 := d.unitPairing_pow v a b
  apply congrArg Units.val
  change H (x/s^n) (y/t^n) = H x y
  simp only [map_div,map_pow,MonoidHom.div_apply,MonoidHom.pow_apply,h,div_one]

/-- Two elements whose valuations are multiples of the cover degree pair trivially at a tame place. -/
theorem symbol_one_of_norm_powers (hp : p.asIdeal.absNorm.Coprime n) (x y s t : Kˣ)
    (hx : ‖x.val‖ = ‖s.val‖^n) (hy : ‖y.val‖ = ‖t.val‖^n) : d.symbol v x y = 1 := by
  have h (a b : Kˣ) (ha : ‖a.val‖ = ‖b.val‖^n) : ‖(a/b^n).val‖ = 1 := by
    rw [Units.val_div_eq_div_val,Units.val_pow_eq_pow_val,norm_div,norm_pow,ha]
    exact div_self (pow_ne_zero _ (norm_ne_zero_iff.mpr b.ne_zero))
  rw [← d.symbol_div_powers p x y s t]
  exact congrArg Units.val (d.unitPairing_tame_units p hp _ _ (h x s hx) (h y t hy))

private theorem basic_X_shear (hp : p.asIdeal.absNorm.Coprime n) (u : K) (hu : ‖u‖ ≤ 1)
    (x : Kˣ) (y : K) : (d.basicCharts p).1 x (y+u*x.val) = (d.basicCharts p).1 x y := by
  have hux : ‖u*x.val‖ ≤ ‖x.val‖ := by
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) hu
  by_cases h : ‖y‖ ≤ ‖x.val‖
  · have h' := (IsUltrametricDist.norm_add_le_max y (u*x.val)).trans (max_le h hux)
    simp [basicCharts,h,h']
  · have hxy := lt_of_not_ge h
    have h' : ‖y+u*x.val‖ = ‖y‖ := by
      rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (hux.trans_lt hxy).ne',max_eq_left (hux.trans hxy.le)]
    have hy : y ≠ 0 := fun he => h (by simp [he])
    have hw : y+u*x.val ≠ 0 := norm_ne_zero_iff.mp (h' ▸ norm_ne_zero_iff.mpr hy)
    let Y := Units.mk0 y hy
    let W := Units.mk0 (y+u*x.val) hw
    have hsub : (W/Y).val - 1 = u*x.val/y := by
      simp only [W,Y,Units.val_div_eq_div_val,Units.val_mk0]
      field_simp
      ring
    have hprincipal : ‖(W/Y).val - 1‖ < 1 := by
      rw [hsub,norm_div,div_lt_one (norm_pos_iff.mpr hy)]
      exact hux.trans_lt hxy
    obtain ⟨z,hz⟩ : ∃ z : Kˣ, z^n = W/Y := FinitePlace.principal_unit_pow p hp _ hprincipal
    have hs : d.unitPairing v x W = d.unitPairing v x Y := by
      rw [show W = z^n*Y by rw [hz,div_mul_cancel],map_mul,map_pow,d.unitPairing_pow,one_mul]
    simp only [basicCharts,h',if_neg h,dif_pos hw,dif_pos hy]
    exact congrArg (_ * ·) (congrArg Units.val hs)

theorem basic_swap (x : Kˣ) (y : K) : (d.basicCharts p).2 y x = (d.basicCharts p).1 x y := by
  simp only [basicCharts,max_comm ‖y‖ ‖x.val‖]

/-- Gluing of the explicit basic vector, directly from its two chart formulas. -/
theorem basicCharts_glues (hp : p.asIdeal.absNorm.Coprime n) : Glues (d.symbol v) (d.basicCharts p) := by
  intro x y
  rw [d.basic_swap]
  let w := radialWeight (n := n) p (max ‖x.val‖ ‖y.val‖)
  change w * (if ‖y.val‖ ≤ ‖x.val‖ then 1 else _) =
    d.symbol v x y * (radialWeight (n := n) p (max ‖y.val‖ ‖x.val‖) * _)
  rw [max_comm ‖y.val‖ ‖x.val‖]
  rcases lt_trichotomy ‖x.val‖ ‖y.val‖ with h | h | h
  · simp only [if_neg h.not_ge,if_pos h.le,dif_pos y.ne_zero,Units.mk0_val,mul_one]
    exact mul_comm ..
  · simp only [if_pos h.le,if_pos h.ge,mul_one]
    by_cases hw : w = 0
    · change w = _ * w
      rw [hw,mul_zero]
    obtain ⟨k,hk⟩ : ∃ k : ℕ, ‖x.val‖ = ((p.asIdeal.absNorm : ℝ)^(n*k))⁻¹ := by
      by_contra! hn
      apply hw
      simp [w,radialWeight,max_eq_left h.ge,hn]
    obtain ⟨π,hπ⟩ := FinitePlace.exists_norm_uniformizer p
    have ht : ‖x.val‖ = ‖(π^k).val‖^n := by
      rw [Units.val_pow_eq_pow_val,norm_pow,← pow_mul,Nat.mul_comm k n,hπ,inv_pow,hk]
    rw [d.symbol_one_of_norm_powers p hp x y (π^k) (π^k) ht (h ▸ ht),one_mul]
  · have hs := (d.lineSymbol v (d.tame_steinberg p hp)).skew x y
    have he : d.symbol v x y = (d.symbol v y x)⁻¹ := by
      change (d.unitPairing v x y).val = (d.unitPairing v y x).val⁻¹
      change d.unitPairing v x y = (d.unitPairing v y x)⁻¹ at hs
      rw [hs,Units.val_inv_eq_inv_val]
    simp only [if_pos h.le,if_neg h.not_ge,dif_pos x.ne_zero,Units.mk0_val,mul_one]
    rw [he,mul_left_comm,inv_mul_cancel₀ (show d.symbol v y x ≠ 0 from (d.unitPairing v y x).ne_zero),mul_one]

/-- Both integral shears fix the explicit basic charts. The assertion precedes
the proof that the basic vector belongs to the Schwartz space. -/
theorem basicCharts_shear (hp : p.asIdeal.absNorm.Coprime n) (u : K) (hu : ‖u‖ ≤ 1) :
    upperShear (d.symbol v) u (d.basicCharts p) = d.basicCharts p ∧
    lowerShear (d.symbol v) u (d.basicCharts p) = d.basicCharts p := by
  have hx := d.basic_X_shear p hp u hu
  have hy (x : K) (y : Kˣ) : (d.basicCharts p).2 (x+u*y.val) y = (d.basicCharts p).2 x y := by
    simpa only [d.basic_swap] using hx y x
  have gl := d.basicCharts_glues p hp
  constructor
  · apply Prod.ext (funext fun x => funext (hx x))
    funext x y
    by_cases h : x = 0
    · simp [upperShear,h]
    · simp only [upperShear,dif_pos h]
      let X := Units.mk0 x h
      change (d.basicCharts p).1 X (y.val+u*X.val) / d.symbol v X y = (d.basicCharts p).2 X.val y
      rw [hx,gl,mul_div_cancel_left₀ _ (show d.symbol v X y ≠ 0 from (d.unitPairing v X y).ne_zero)]
  · apply Prod.ext _ (funext fun x => funext (hy x))
    funext x y
    by_cases h : y = 0
    · simp [lowerShear,h]
    · simp only [lowerShear,dif_pos h]
      let Y := Units.mk0 y h
      change d.symbol v x Y * (d.basicCharts p).2 (x.val+u*Y.val) Y = (d.basicCharts p).1 x Y.val
      rw [hy,← gl]

/-- Two genuine sections invariant in their primary charts under integral
upper and lower shears agree everywhere if they agree on the vertical axis. -/
theorem eq_of_integral_shears_of_axis {f g : Charts K} (hf : Glues (d.symbol v) f)
    (hg : Glues (d.symbol v) g)
    (upper : ∀ (u : K), ‖u‖ ≤ 1 → ∀ x y, f.1 x (y+u*x.val) - g.1 x (y+u*x.val) = f.1 x y - g.1 x y)
    (lower : ∀ (u : K), ‖u‖ ≤ 1 → ∀ x y, f.2 (x+u*y.val) y - g.2 (x+u*y.val) y = f.2 x y - g.2 x y)
    (axis : ∀ y, f.2 0 y = g.2 0 y) : f = g := by
  have small (x : K) (y : Kˣ) (h : ‖x‖ ≤ ‖y.val‖) : f.2 x y = g.2 x y := by
    have hu : ‖-x/y.val‖ ≤ 1 := by rwa [norm_div,norm_neg,div_le_one (norm_pos_iff.mpr y.ne_zero)]
    have e := lower (-x/y.val) hu x y
    rw [div_mul_cancel₀ _ y.ne_zero,add_neg_cancel,axis,sub_self] at e
    exact sub_eq_zero.mp e.symm
  have X (x : Kˣ) (y : K) : f.1 x y = g.1 x y := by
    by_cases h : ‖x.val‖ ≤ ‖y‖
    · have hy : y ≠ 0 := by
        intro hy
        simp [hy,x.ne_zero] at h
      let Y := Units.mk0 y hy
      exact (hf x Y).trans ((congrArg (d.symbol v x Y * ·) (small x.val Y h)).trans (hg x Y).symm)
    · let u := (x.val-y)/x.val
      have hu : ‖u‖ ≤ 1 := by
        rw [show u = (x.val-y)/x.val from rfl,norm_div,div_le_one (norm_pos_iff.mpr x.ne_zero),sub_eq_add_neg]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le le_rfl (by simpa using (le_of_not_ge h)))
      have hux : y+u*x.val = x.val := by simp [u,div_mul_cancel₀ _ x.ne_zero]
      have e := upper u hu x y
      rw [hux,hf x x,hg x x,small x.val x le_rfl,sub_self] at e
      exact sub_eq_zero.mp e.symm
  refine Prod.ext (funext fun x => funext (X x)) ?_
  funext x y
  by_cases h : x = 0
  · simpa only [h] using axis y
  · let A := Units.mk0 x h
    apply mul_left_cancel₀ (show d.symbol v A y ≠ 0 from (d.unitPairing v A y).ne_zero)
    exact (hf A y).symm.trans ((X A y.val).trans (hg A y))

/-- The fixed-vector assertion for the raw integral is equivalent to its
restriction to the vertical axis, before proving basic-vector membership. -/
theorem transform_basic_eq_iff_axis (hp : p.asIdeal.absNorm.Coprime n) :
    d.integralTransform v (d.basicCharts p) = d.basicCharts p ↔
      ∀ y, (d.integralTransform v (d.basicCharts p)).2 0 y = (d.basicCharts p).2 0 y := by
  let f := d.basicCharts p
  let h := d.symbol v
  let T := d.integralTransform v
  constructor
  · intro he y
    rw [he]
  · intro axis
    apply d.eq_of_integral_shears_of_axis p (d.integralTransform_glues v (d.basicCharts_glues p hp))
      (d.basicCharts_glues p hp) _ _ axis
    · intro u hu x y
      have he : upperShear h u f = f := (d.basicCharts_shear p hp u hu).1
      have hT := transform_upper h n (modulus F v) (selfDual F d.character v)
        (d.character.localValue F v) u f x y
      change (T (upperShear h u f)).1 x y = (T f).1 x (y+u*x.val) at hT
      rw [he] at hT
      exact congrArg₂ (· - ·) hT.symm (congrArg (fun z : Charts K => z.1 x y) he)
    · intro u hu x y
      have he : lowerShear h u f = f := (d.basicCharts_shear p hp u hu).2
      have hT := transform_lower h n (modulus F v) (selfDual F d.character v)
        (d.character.localValue F v) u f x y
      change (T (lowerShear h u f)).2 x y = (T f).2 (x+u*y.val) y at hT
      rw [he] at hT
      exact congrArg₂ (· - ·) hT.symm (congrArg (fun z : Charts K => z.2 x y) he)

end MetaplecticPoisson.Datum
