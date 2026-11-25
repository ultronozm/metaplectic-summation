import MetaplecticSummation.Dilations
import MetaplecticSummation.Jacquet.Local
import MetaplecticSummation.LineMoments
import MetaplecticSummation.Jacquet.LeadingKernel

/-! The power average of a test lift and the leading term of its transform. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open MeasureTheory
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

def powerAverage (v : Place F) (f : Charts (LocalField F v)) : Charts (LocalField F v) :=
  let avg := fun g : Weight v => d.lineIntegral v fun x =>
    if ∃ u : (LocalField F v)ˣ, x = u^n then (modulus F v x ^ (1+1/(n : ℝ)) : ℝ) * g x else 0
  (fun x y => avg fun a => (dilateCharts a f).1 x y,
   fun x y => avg fun a => (dilateCharts a f).2 x y)

/-- The X-chart of the power average of a Jacquet lift, in terms of the weighted
moment on the power class of its first coordinate (equation `eq:lift-average`). -/
theorem powerAverage_jacquetLift (v : Place F) (W : Weight v) (β : LocalField F v → ℂ)
    (x : (LocalField F v)ˣ) (y : LocalField F v) :
    (d.powerAverage v (d.jacquetLift v W β)).1 x y =
      β (y / x.val) / ((modulus F v x.val ^ (1 + 1 / (n : ℝ)) : ℝ) : ℂ) *
        d.lineIntegral v (fun t =>
          if (QuotientGroup.mk t : PowerClass n v) = QuotientGroup.mk x then
            W t * ((modulus F v t.val ^ (1 / (n : ℝ)) : ℝ) : ℂ) else 0) := by
  let m (u : (LocalField F v)ˣ) := modulus F v u.val
  have pos (u : (LocalField F v)ˣ) : 0 < m u := by
    cases v <;> simp [m,modulus,norm_pos_iff,u.ne_zero,pow_pos (norm_pos_iff.mpr u.ne_zero)]
  let s := 1 / (n : ℝ)
  let g (t : (LocalField F v)ˣ) : ℂ :=
    if (QuotientGroup.mk t : PowerClass n v) = QuotientGroup.mk x then W t * (m t ^ s : ℝ) else 0
  let b := β (y / x.val) / ((m x ^ (1 + s) : ℝ) : ℂ)
  unfold powerAverage
  dsimp only
  change _ = b * d.lineIntegral v g
  rw [← d.lineIntegral_mul v x g,← d.lineIntegral_const_mul]
  congr 1
  funext a
  have coset : (QuotientGroup.mk (x*a) : PowerClass n v) = QuotientGroup.mk x ↔
      ∃ u : (LocalField F v)ˣ, a = u^n := by
    rw [QuotientGroup.eq_iff_div_mem,mul_comm x a,mul_div_cancel_right]
    exact ⟨fun ⟨u,hu⟩ => ⟨u,hu.symm⟩,fun ⟨u,hu⟩ => ⟨u,hu.symm⟩⟩
  change (if ∃ u : (LocalField F v)ˣ, a = u^n then
    ((m a ^ (1+s) : ℝ) : ℂ) * jacquetLiftX v W β (a*x) (a.val*y) else 0) = b * g (x*a)
  simp only [g,coset]
  split_ifs
  · have hm : m (a*x) = m a * m x := by cases v <;> simp [m,modulus,norm_mul,mul_pow]
    have ratio : a.val*y / (a*x).val = y / x.val := by rw [Units.val_mul]; field_simp
    rw [jacquetLiftX,ratio,mul_comm x a]
    change ((m a ^ (1+s) : ℝ) : ℂ) * ((m (a*x) : ℂ)⁻¹ * W (a*x) * β (y/x.val)) =
      β (y/x.val) / ((m x ^ (1+s) : ℝ) : ℂ) * (W (a*x) * ((m (a*x)^s : ℝ) : ℂ))
    rw [hm,Real.mul_rpow (pos a).le (pos x).le,Real.rpow_add (pos a),Real.rpow_add (pos x)]
    simp only [Real.rpow_one,Complex.ofReal_mul]
    field_simp [Complex.ofReal_ne_zero.mpr (pos a).ne', Complex.ofReal_ne_zero.mpr (pos x).ne',
      Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (pos x) s).ne']
  · exact (mul_zero _).symm

theorem powerAverage_glues (v : Place F) {f : Charts (LocalField F v)} (hf : Glues (d.symbol v) f) :
    Glues (d.symbol v) (d.powerAverage v f) := by
  intro x y
  unfold powerAverage
  dsimp only
  rw [← d.lineIntegral_const_mul]
  congr 1
  funext a
  split_ifs with ha
  · obtain ⟨u,rfl⟩ := ha
    rw [d.dilateCharts_glues v u hf x y]
    ring
  · rw [mul_zero]

/-- Vanishing of all the power-class moments kills the average in both charts. -/
theorem powerAverage_jacquetLift_eq_zero (v : Place F) (W : Weight v) (β : LocalField F v → ℂ)
    (h : ∀ c : PowerClass n v, d.lineIntegral v (fun t =>
      if (QuotientGroup.mk t : PowerClass n v) = c then
        W t * ((modulus F v t.val ^ (1 / (n : ℝ)) : ℝ) : ℂ) else 0) = 0) :
    d.powerAverage v (d.jacquetLift v W β) = 0 := by
  let f := d.jacquetLift v W β
  have hx (x : (LocalField F v)ˣ) (y : LocalField F v) : (d.powerAverage v f).1 x y = 0 := by
    dsimp only [f]
    rw [d.powerAverage_jacquetLift,h,mul_zero]
  refine Prod.ext (funext fun x => funext fun y => hx x y) (funext fun x => funext fun y => ?_)
  by_cases hn : x = 0
  · subst x
    simp [powerAverage,dilateCharts,jacquetLift,lineIntegral]
  · let x' := Units.mk0 x hn
    have eqn := d.powerAverage_glues v (d.jacquetLift_glues v W β) x' y
    rw [hx] at eqn
    exact (mul_eq_zero.mp eqn.symm).resolve_left (d.unitPairing v x' y).ne_zero

def intertwiner (v : Place F) (f : Charts (LocalField F v)) :=
  radon n (d.symbol v) (modulus F v) (selfDual F d.character v) f 1

variable (v : Place F)
local notation "K" => LocalField F v

/-- Dilating the input of the intertwiner by an n-th power recovers the
Radon slice at its root, with its additive Jacobian. -/
theorem intertwiner_dilate_power (f : Charts K) (u : Kˣ) :
    d.intertwiner v (dilateCharts (u^n) f) =
      (modulus F v (u^n).val : ℂ)⁻¹ •
        radon n (d.symbol v) (modulus F v) (selfDual F d.character v) f u.val := by
  let A := u^n
  let R := radon n (d.symbol v) (modulus F v) (selfDual F d.character v) f
  let m : ℂ := modulus F v u.val
  have hm : m ≠ 0 := Complex.ofReal_ne_zero.mpr (modulus_ne_zero v u)
  have modpow (u b : Kˣ) : modulus F v (u.val^n * b.val) = modulus F v u.val ^ n * modulus F v b.val := by
    cases v <;> simp [modulus,norm_mul,norm_pow,mul_pow,← pow_mul,Nat.mul_comm n]
  have hA : (modulus F v A.val : ℂ) = m^n := by
    cases v <;> simp [A,m,modulus,norm_pow,← pow_mul,Nat.mul_comm n]
  let H := d.lineSymbol v (by cases v with
    | inl w => exact d.arch_steinberg w
    | inr p => exact d.finite_steinberg p)
  have ray := H.radon_pow_ray _ modpow (selfDual F d.character v) f u 1
  have rev : dilateCharts A⁻¹ (R 1) = m^n • R u.val := by
    apply Prod.ext
    · funext a b
      have h := ray.1 (A⁻¹*a) (A⁻¹.val*b)
      change (R (u.val*1)).1 (A*(A⁻¹*a)) (A.val*(A⁻¹.val*b)) = _ / m^n at h
      simp only [mul_one,mul_inv_cancel_left,Units.val_inv_eq_inv_val,mul_inv_cancel_left₀ A.ne_zero] at h
      simp only [dilateCharts,Units.val_inv_eq_inv_val,Prod.smul_fst,Pi.smul_apply,smul_eq_mul]
      exact ((eq_div_iff (pow_ne_zero n hm)).mp h).symm.trans (mul_comm ..)
    · funext a b
      have h := ray.2 (A⁻¹.val*a) (A⁻¹*b)
      change (R (u.val*1)).2 (A.val*(A⁻¹.val*a)) (A*(A⁻¹*b)) = _ / m^n at h
      simp only [mul_one,mul_inv_cancel_left,Units.val_inv_eq_inv_val,mul_inv_cancel_left₀ A.ne_zero] at h
      simp only [dilateCharts,Units.val_inv_eq_inv_val,Prod.smul_snd,Pi.smul_apply,smul_eq_mul]
      exact ((eq_div_iff (pow_ne_zero n hm)).mp h).symm.trans (mul_comm ..)
  refine (d.radon_dilateCharts v u f 1).trans ?_
  change ((modulus F v A.val : ℂ)^2)⁻¹ • dilateCharts A⁻¹ (R 1) = (modulus F v A.val : ℂ)⁻¹ • R u.val
  rw [rev,smul_smul,hA]
  congr 1
  field_simp

omit [NeZero n] in
/-- Dilation of the power average by an n-th power acts by the
homogeneity character of the principal series in §8. -/
theorem powerAverage_homogeneous (f : Charts K) (u : Kˣ) :
    dilateCharts (u^n) (d.powerAverage v f) =
      ((modulus F v (u^n).val ^ (-1-1/(n : ℝ)) : ℝ) : ℂ) • d.powerAverage v f := by
  let A := u^n
  let e := 1+1/(n:ℝ)
  let m (a : Kˣ) := modulus F v a.val
  have pos (a : Kˣ) : 0 < m a := by
    cases v <;> simp [m,modulus,norm_pos_iff,a.ne_zero,pow_pos (norm_pos_iff.mpr a.ne_zero)]
  have hm (a : Kˣ) : m (A*a) = m A * m a := by cases v <;> simp [m,modulus,norm_mul,mul_pow]
  have coset (a : Kˣ) : (∃ t : Kˣ, A*a=t^n) ↔ ∃ t : Kˣ, a=t^n := by
    constructor
    · rintro ⟨t,ht⟩
      exact ⟨t/u,by rw [div_pow,← ht]; exact (mul_div_cancel_left A a).symm⟩
    · rintro ⟨t,rfl⟩
      exact ⟨u*t,(mul_pow ..).symm⟩
  let avg (g : Kˣ → ℂ) := d.lineIntegral v fun a =>
    if ∃ t : Kˣ, a=t^n then ((m a^e : ℝ) : ℂ) * g a else 0
  have scale (g : Kˣ → ℂ) : avg (fun a => g (A*a)) = (((m A)^(-e) : ℝ) : ℂ) * avg g := by
    unfold avg
    rw [← d.lineIntegral_mul v A (fun a => if ∃ t : Kˣ, a=t^n then ((m a^e : ℝ) : ℂ) * g a else 0),
      ← d.lineIntegral_const_mul]
    congr 1
    funext a
    rw [coset]
    split_ifs <;> simp [hm,Real.mul_rpow (pos A).le (pos a).le,Real.rpow_neg (pos A).le,
      Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (pos A) e).ne',mul_assoc]
  have hex : -1-1/(n:ℝ) = -e := by dsimp [e]; ring
  rw [hex]
  apply Prod.ext <;> funext x y
  · simpa only [avg,powerAverage,dilateCharts,Units.val_mul,mul_assoc,mul_comm A _,mul_comm A.val _,e,m,A,
      Prod.smul_fst,Pi.smul_apply,smul_eq_mul] using scale (fun a => (dilateCharts a f).1 x y)
  · simpa only [avg,powerAverage,dilateCharts,Units.val_mul,mul_assoc,mul_comm A _,mul_comm A.val _,e,m,A,
      Prod.smul_snd,Pi.smul_apply,smul_eq_mul] using scale (fun a => (dilateCharts a f).2 x y)

theorem leading_fourier_test (Φ : d.schwartz v) (h : Φ.val ∈ d.testSet v) :
    d.leading v (d.fourier v Φ) =
      ((n : ℂ) / ((modulus F v (n : LocalField F v) ^ (3/2 : ℝ) : ℝ) : ℂ)) •
        d.intertwiner v (d.powerAverage v Φ.val) := by
  have he : d.fourier v Φ =
      ⟨d.integralTransform v Φ.val,Submodule.subset_span (Or.inr ⟨_,h,rfl⟩)⟩ :=
    Subtype.ext (d.fourier_apply v Φ)
  have hl : d.leading v (d.fourier v Φ) = d.radonLeading v Φ.val := by
    rw [he]
    cases v with
    | inl w => exact d.leading_archTest_transform w h
    | inr p => exact d.leading_finiteTest_transform p h
  rw [hl]
  let m := modulus F v (n : K)
  have hn : (n : K) ≠ 0 := by
    simpa only [map_natCast,map_zero] using
      (diagonal F v).injective.ne (Nat.cast_ne_zero.mpr (NeZero.ne n) : (n:F) ≠ 0)
  have hp : 0 < m := by cases v <;> simp [m,modulus,norm_pos_iff,hn,pow_pos (norm_pos_iff.mpr hn)]
  let k : ℂ := (m : ℂ)/(n : ℂ)
  have hscale : ((n:ℂ)/((m^(3/2:ℝ) : ℝ) : ℂ))*k = (Real.sqrt m : ℂ)⁻¹ := by
    rw [show (3/2:ℝ) = 1+1/2 by norm_num,Real.rpow_add hp,Real.rpow_one,← Real.sqrt_eq_rpow,Complex.ofReal_mul]
    dsimp only [k]
    field_simp [Complex.ofReal_ne_zero.mpr hp.ne',Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hp).ne',
      (Nat.cast_ne_zero.mpr (NeZero.ne n) : (n:ℂ) ≠ 0)]
  have inv (c t x : Kˣ) : d.symbol v (t^n*x) c = d.symbol v x c := by
    change ((d.unitPairing v (t^n*x) c : ℂˣ) : ℂ) = _
    rw [map_mul,map_pow,MonoidHom.mul_apply,MonoidHom.pow_apply,d.unitPairing_pow,one_mul]
    rfl
  have symcont (c : Kˣ) : Continuous (fun x => d.symbol v x c) :=
    (d.continuous_symbol v).comp (continuous_id.prodMk continuous_const)
  obtain ⟨hX,hY⟩ := d.test_rapidLineCharts v h
  let dx := selfDual F d.character v
  let R := radon n (d.symbol v) (modulus F v) dx Φ.val
  let A := d.intertwiner v (d.powerAverage v Φ.val)
  have combine (u z : ℂ) (hz : u = k*z) :
      (Real.sqrt m : ℂ)⁻¹*z = ((n:ℂ)/((m^(3/2:ℝ) : ℝ) : ℂ))*u := by rw [hz,← mul_assoc,hscale]
  apply Prod.ext
  · funext c b
    change (Real.sqrt m : ℂ)⁻¹*(∫ t, (R t).1 c b ∂dx) = _ * A.1 c b
    apply combine
    have H := d.leadingLine_average v hX c b (-1) (by simp) (fun x => d.symbol v x (-c))
      (symcont _) (fun x => d.norm_symbol v x _) (inv _)
    have HH := congrArg (fun z : ℂ => z/(modulus F v c.val : ℂ)) H
    simpa only [leadingLine,neg_one_mul,← sub_eq_add_neg,powerAverage,dilateCharts,
      A,intertwiner,R,radon,integral_div,mul_div_assoc,dx,k,m] using HH
  · funext b c
    change (Real.sqrt m : ℂ)⁻¹*(∫ t, (R t).2 b c ∂dx) = _ * A.2 b c
    apply combine
    have H := d.leadingLine_average v hY c b 1 (by simp)
      (fun x => d.symbol v x c * d.symbol v (-1) c) ((symcont c).mul continuous_const)
      (fun x => by simp) (fun t x => by rw [inv])
    have HH := congrArg (fun z : ℂ => z/(modulus F v c.val : ℂ)) H
    simpa only [leadingLine,one_mul,mul_comm b _,mul_assoc,powerAverage,dilateCharts,
      A,intertwiner,R,radon,integral_div,mul_div_assoc,dx,k,m] using HH

end MetaplecticPoisson.Datum
