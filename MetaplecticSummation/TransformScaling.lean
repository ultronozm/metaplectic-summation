import MetaplecticSummation.CharacterScaling

/-! Change of additive character in the defining metaplectic integral. -/

noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField MeasureTheory
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

theorem integralTransform_scaled (v : Place F) (b : Fˣ) (f : Charts (LocalField F v)) :
    (d.scaled b).integralTransform v f = (modulus F v (atPlace v b).val : ℂ)^n •
      dilateCharts ((atPlace v b)^n) (d.integralTransform v f) := by
  let u := atPlace v b
  let m : ℂ := modulus F v u.val
  let r := NNReal.sqrt (modulus F v u.val).toNNReal
  let c : ℂ := (Real.sqrt (modulus F v (n : LocalField F v)))⁻¹
  let dx := selfDual F d.character v
  let ψ := d.character.localValue F v
  let R := radon n (d.symbol v) (modulus F v) dx f
  let T := d.integralTransform v f
  have hm : 0 ≤ modulus F v u.val := by cases v <;> simp [modulus,pow_nonneg]
  have hr : (r : ℂ)*(r : ℂ) = m := by
    have hr' : (r : ℝ)*(r : ℝ) = modulus F v u.val := by
      rw [← NNReal.coe_mul,show r*r = _ from NNReal.mul_self_sqrt _,Real.coe_toNNReal _ hm]
    change ((r : ℝ) : ℂ) * ((r : ℝ) : ℂ) = ((modulus F v u.val : ℝ) : ℂ)
    rw [← Complex.ofReal_mul,hr']
  have hR (t : LocalField F v) : radon n (d.symbol v) (modulus F v) (r • dx) f t = (r : ℂ) • R t := by
    ext a z <;> simp only [R,radon,integral_smul_nnreal_measure,NNReal.smul_def,Complex.real_smul,
      Prod.smul_fst,Prod.smul_snd,Pi.smul_apply,smul_eq_mul,mul_div_assoc]
  have eqn (s : LocalField F v → ℂ) (z : ℂ)
      (h : m^(n-1)*z = c * ∫ t, s t * ψ (u.val*t) ∂dx) :
      c * (∫ t, ψ (u.val*t) * ((r:ℂ)*s t) ∂(r • dx)) = m^n*z := by
    have he : m^n = m*m^(n-1) := by rw [← pow_succ',Nat.sub_add_cancel (NeZero.pos n)]
    simp_rw [mul_left_comm (ψ _) (r:ℂ),mul_comm (ψ _) (s _)]
    rw [integral_smul_nnreal_measure,NNReal.smul_def,Complex.real_smul,integral_const_mul,
      ← mul_assoc (r : ℂ),hr,he,mul_assoc m,h]
    ring
  have h := d.transform_pow_ray v f u
  change (∀ a z, m^(n-1)*(T.1 (u^n*a) (u.val^n*z)) = _) ∧
    (∀ z a, m^(n-1)*(T.2 (u.val^n*z) (u^n*a)) = _) at h
  have hd : selfDual F (d.scaled b).character v = r • dx := d.selfDual_scaled v b
  change transform n _ (d.symbol v) _ _ f = m^n • dilateCharts (u^n) T
  rw [hd]
  apply Prod.ext
  · funext a z
    change c*(∫ t, _ * (radon n (d.symbol v) (modulus F v) (r • dx) f t).1 a z ∂(r • dx)) = _
    simp_rw [d.scaled_localValue,hR]
    exact eqn (fun t => (R t).1 a z) _ (h.1 a z)
  · funext z a
    change c*(∫ t, _ * (radon n (d.symbol v) (modulus F v) (r • dx) f t).2 z a ∂(r • dx)) = _
    simp_rw [d.scaled_localValue,hR]
    exact eqn (fun t => (R t).2 z a) _ (h.2 z a)

end MetaplecticPoisson.Datum
