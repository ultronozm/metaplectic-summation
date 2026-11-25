import MetaplecticSummation.Gauss.Setup

/-! Self-dual measure and the dual weight under a change of additive character. -/

noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField MeasureTheory
open scoped ENNReal NNReal
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

omit [NeZero n] in
theorem lineIntegral_scaled (v : Place F) (b : Fˣ) (W : Weight v) :
    (d.scaled b).lineIntegral v W =
      (NNReal.sqrt (modulus F v (diagonal F v b)).toNNReal : ℂ) * d.lineIntegral v W := by
  unfold lineIntegral
  rw [d.selfDual_scaled,integral_smul_nnreal_measure,NNReal.smul_def,Complex.real_smul]

theorem dualWeight_const_mul (v : Place F) (z : ℂ) (W : Weight v) (c : (LocalField F v)ˣ) :
    d.dualWeight v (fun x => z * W x) c = z * d.dualWeight v W c := by
  have kernel (t : LocalField F v) :
      d.kernelIntegral v (fun x => z * W x) c t = z * d.kernelIntegral v W c t := by
    unfold kernelIntegral
    simp_rw [mul_assoc z,d.lineIntegral_const_mul]
  unfold dualWeight
  simp_rw [kernel,mul_left_comm (d.character.localValue F v _) z]
  rw [integral_const_mul]
  ring

theorem dual_dilation (v : Place F) (W : Weight v) (_hw : TestWeight v W)
    (X c : (LocalField F v)ˣ) :
    d.dualWeight v (fun x => W (x/X)) c =
      d.symbol v X (-c) * d.dualWeight v (fun x => W x / d.symbol v x X) (X*c) := by
  let W' : Weight v := fun x => W x / d.symbol v x X
  let z := d.symbol v X (-c)
  have left (x : (LocalField F v)ˣ) :
      d.symbol v (X*x) (-c) = z * d.symbol v x (-c) := by
    change ((d.unitPairing v (X*x) (-c)).val) = _
    rw [map_mul]
    rfl
  have right (x : (LocalField F v)ˣ) :
      d.symbol v x (-(X*c)) = d.symbol v x X * d.symbol v x (-c) := by
    change ((d.unitPairing v x (-(X*c))).val) = _
    rw [← mul_neg,map_mul]
    rfl
  have kernel (t : LocalField F v) : d.kernelIntegral v (fun x => W (x/X)) c t =
      z * d.kernelIntegral v W' (X*c) t := by
    unfold kernelIntegral
    rw [← d.lineIntegral_mul v X, ← d.lineIntegral_const_mul]
    congr 1
    funext x
    dsimp only
    rw [mul_div_cancel_left X x, left, right,Units.val_mul,Units.val_mul,
      show c.val*(X.val*x.val) = X.val*c.val*x.val by ring]
    dsimp only [W']
    field_simp [(show d.symbol v x X ≠ 0 from (d.unitPairing v x X).ne_zero)]
  unfold dualWeight
  simp_rw [kernel, ← mul_assoc, mul_comm (d.character.localValue F v _) z, mul_assoc z]
  rw [integral_const_mul]
  ring

/-- Change of additive character in the explicit dual weight of §10. -/
theorem dual_scaled (v : Place F) (W : Weight v) (_hw : TestWeight v W) (b : Fˣ)
    (c : (LocalField F v)ˣ) :
    (d.scaled b).dualWeight v W c =
      d.dualWeight v (fun x => W x * d.symbol v x (atPlace v b)) (atPlace v b ^ (n-1) * c) := by
  let B := atPlace v b
  let D := B^(n-1)*c
  let W' : Weight v := fun x => W x * d.symbol v x B
  let μ := selfDual F d.character v
  let ψ := d.character.localValue F v
  let r := NNReal.sqrt (modulus F v B.val).toNNReal
  have hM : 0 < modulus F v B.val := by cases v <;> simp [modulus,B,atPlace,b.ne_zero]
  have hr : (r : ℂ) * r = (modulus F v B.val : ℂ) := by
    rw [← Complex.ofReal_mul]
    apply congrArg Complex.ofReal
    change ((r*r : ℝ≥0) : ℝ) = _
    rw [← sq, NNReal.sq_sqrt,Real.coe_toNNReal _ hM.le]
  have hpow : B^(n-1)*B = B^n := by rw [← pow_succ,Nat.sub_add_cancel (NeZero.pos n)]
  have symb (x : (LocalField F v)ˣ) :
      d.symbol v x B * d.symbol v x (-D) = d.symbol v x (-c) := by
    have h : B * (-D) = B^n * (-c) := by
      dsimp only [D]
      rw [← mul_neg,← mul_assoc,mul_comm B (B^_),hpow]
    change (d.unitPairing v x B).val * (d.unitPairing v x (-D)).val = _
    rw [← Units.val_mul,← map_mul,h,map_mul,map_pow,d.unitPairing_pow,one_mul]
    rfl
  have phase (t : LocalField F v) (x : (LocalField F v)ˣ) :
      diagonal F v b * (-(t^n)/(c.val*x.val)) = -((B.val*t)^n)/(D.val*x.val) := by
    have hn : B.val^(n-1)*B.val = B.val^n := congrArg Units.val hpow
    change B.val * _ = -((B.val*t)^n)/((B.val^(n-1)*c.val)*x.val)
    rw [mul_pow,← hn]
    field_simp
  have kernel (t : LocalField F v) : (d.scaled b).kernelIntegral v W c t =
      (r : ℂ) * d.kernelIntegral v W' D (B.val*t) := by
    unfold kernelIntegral
    rw [d.lineIntegral_scaled]
    congr 2
    funext x
    rw [d.scaled_localValue,phase]
    change W x * d.symbol v x (-c) * _ = (W x * d.symbol v x B) * d.symbol v x (-D) * _
    rw [← symb x]
    ring
  let g (t : LocalField F v) := ψ t * d.kernelIntegral v W' D t
  have integrand (t : LocalField F v) :
      (d.scaled b).character.localValue F v t * (d.scaled b).kernelIntegral v W c t =
        (r : ℂ) * g (B.val*t) := by
    rw [kernel,d.scaled_localValue]
    exact mul_left_comm _ _ _
  unfold dualWeight
  congr 1
  rw [d.selfDual_scaled v b,integral_smul_nnreal_measure,NNReal.smul_def,Complex.real_smul]
  simp_rw [integrand]
  rw [integral_const_mul]
  change (r : ℂ) * (r * ∫ t, g (B.val*t) ∂μ) = ∫ t, g t ∂μ
  rw [d.integral_local_mul v B g, ← mul_assoc,hr]
  rw [← mul_div_assoc,mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr hM.ne')]

end MetaplecticPoisson.Datum
