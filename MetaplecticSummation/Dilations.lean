import MetaplecticSummation.RayFourier

/-! Dilation by n-th powers in the defining integral, Lemma 4.8(i). -/

noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField IsDedekindDomain MeasureTheory Set
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n) (v : Place F)
local notation "K" => LocalField F v

theorem dilateCharts_mul {L : Type} [Field L] (a b : Lˣ) (f : Charts L) :
    dilateCharts a (dilateCharts b f) = dilateCharts (b*a) f := by
  ext x y <;> simp only [dilateCharts,Units.val_mul,mul_assoc]

theorem dilateCharts_sub {L : Type} [Field L] (a : Lˣ) (f g : Charts L) :
    dilateCharts a (f-g) = dilateCharts a f - dilateCharts a g := rfl

theorem dilateCharts_smul {L : Type} [Field L] (a : Lˣ) (c : ℂ) (f : Charts L) :
    dilateCharts a (c • f) = c • dilateCharts a f := rfl

theorem dilateCharts_one {L : Type} [Field L] (f : Charts L) : dilateCharts 1 f = f := by
  ext x y <;> simp [dilateCharts]

private theorem dilate_symbol (a x y : Kˣ) : d.symbol v (a^n*x) (a^n*y) = d.symbol v x y := by
  let H := d.unitPairing v
  have ht (r s : Kˣ) : (H r s)^n = 1 := d.unitPairing_pow v r s
  change (H (a^n*x) (a^n*y)).val = _
  simp only [map_mul,map_pow,MonoidHom.mul_apply,MonoidHom.pow_apply,ht,one_mul]
  rfl

theorem dilateCharts_glues (a : Kˣ) {f : Charts K} (hf : Glues (d.symbol v) f) :
    Glues (d.symbol v) (dilateCharts (a^n) f) := by
  intro x y
  simpa only [dilateCharts,Units.val_mul,d.dilate_symbol] using hf (a^n*x) (a^n*y)

private theorem modulus_inv_mul (a b : Kˣ) :
    modulus F v (a⁻¹*b).val = (modulus F v a.val)⁻¹ * modulus F v b.val := by
  cases v <;> simp [modulus,norm_mul,mul_pow,inv_pow]

omit [NeZero n] in
private theorem rescale_integral (a b : Kˣ) (g h : K → ℂ) (he : ∀ z, g z = h (a.val*z)) :
    (∫ z, g z ∂selfDual F d.character v) / (modulus F v b.val : ℂ) =
      ((modulus F v a.val : ℂ)^2)⁻¹ *
        ((∫ z, h z ∂selfDual F d.character v) / (modulus F v (a⁻¹*b).val : ℂ)) := by
  simp_rw [he]
  rw [d.integral_local_mul,modulus_inv_mul,Complex.ofReal_mul,Complex.ofReal_inv]
  field_simp [Complex.ofReal_ne_zero.mpr (modulus_ne_zero v a),Complex.ofReal_ne_zero.mpr (modulus_ne_zero v b)]

theorem radon_dilateCharts (a : Kˣ) (f : Charts K) (t : K) :
    let R := fun g => radon n (d.symbol v) (modulus F v) (selfDual F d.character v) g t
    R (dilateCharts (a^n) f) = ((modulus F v (a^n).val : ℂ)^2)⁻¹ •
      dilateCharts (a^n)⁻¹ (R f) := by
  let A := a^n
  let H := d.unitPairing v
  have hs (x b : Kˣ) : d.symbol v (A*x) (A⁻¹*b) = d.symbol v x b := by
    have ht (r s : Kˣ) : (H r s)^n = 1 := d.unitPairing_pow v r s
    change (H (a^n*x) ((a^n)⁻¹*b)).val = _
    simp only [map_mul,map_inv,map_pow,MonoidHom.mul_apply,MonoidHom.pow_apply,ht,inv_one,one_mul]
    rfl
  have hm (b : Kˣ) : d.symbol v (-1) (A⁻¹*b) = d.symbol v (-1) b := by
    change (H (-1) ((a^n)⁻¹*b)).val = _
    rw [map_mul,map_inv,map_pow,show (H (-1) a)^n = 1 from d.unitPairing_pow v _ _,inv_one,one_mul]
    rfl
  apply Prod.ext
  · funext b z
    apply d.rescale_integral v A b
    intro x
    by_cases hx : x ≠ 0
    · have hax := mul_ne_zero A.ne_zero hx
      let X := Units.mk0 x hx
      have hc : (A.val*x*(A⁻¹.val*z)-t^n)/(A⁻¹*b).val = A.val*((x*z-t^n)/b.val) := by
        rw [Units.val_mul,Units.val_inv_eq_inv_val]
        field_simp
      simp only [dilateCharts,dif_pos hx,dif_pos hax]
      rw [show Units.mk0 (A.val*x) hax = A*X from Units.ext rfl,hc,← mul_neg,hs]
    · simp [hx]
  · funext z b
    apply d.rescale_integral v A b
    intro y
    by_cases hy : y ≠ 0
    · have hay := mul_ne_zero A.ne_zero hy
      let Y := Units.mk0 y hy
      have hc : ((A⁻¹.val*z)*(A.val*y)+t^n)/(A⁻¹*b).val = A.val*((z*y+t^n)/b.val) := by
        rw [Units.val_mul,Units.val_inv_eq_inv_val]
        field_simp
      simp only [dilateCharts,dif_pos hy,dif_pos hay]
      rw [show Units.mk0 (A.val*y) hay = A*Y from Units.ext rfl,hc,hs,hm]
    · simp [hy]

theorem integralTransform_dilateCharts (a : Kˣ) (f : Charts K) :
    d.integralTransform v (dilateCharts (a^n) f) = ((modulus F v (a^n).val : ℂ)^2)⁻¹ •
      dilateCharts (a^n)⁻¹ (d.integralTransform v f) := by
  have h := d.radon_dilateCharts v a f
  dsimp only at h
  ext x y <;> simp only [integralTransform,transform] <;> simp_rw [h] <;> simp only [Prod.smul_fst,Prod.smul_snd,
    dilateCharts,Pi.smul_apply,smul_eq_mul,mul_left_comm (d.character.localValue F v _) _,
    integral_const_mul,mul_left_comm _ (((modulus F v (a^n).val : ℂ)^2)⁻¹)]

/-- On a finite completion dilation preserves local constancy and pulls back
the compact support by an invertible linear map. -/
theorem finiteTest_dilate {L : Type} [NormedField L] (a : Lˣ) {f : Charts L} (hf : finiteTest f) :
    finiteTest (dilateCharts a f) := by
  obtain ⟨hx,hy,C,hC,h₀,ho⟩ := hf
  let S (a : Lˣ) (z : L × L) := (a.val*z.1,a.val*z.2)
  have he (z : L × L) : S a⁻¹ (S a z) = z := by
    simp only [S,Units.val_inv_eq_inv_val,← mul_assoc,inv_mul_cancel₀ a.ne_zero,one_mul]
  have hX (z : L × L) : xChart (dilateCharts a f) z = xChart f (S a z) := by
    by_cases h : z.1 ≠ 0
    · simp only [xChart,S,dilateCharts,dif_pos h,dif_pos (mul_ne_zero a.ne_zero h)]
      rw [show a*Units.mk0 z.1 h = Units.mk0 _ (mul_ne_zero a.ne_zero h) from Units.ext rfl]
    · simp [S,xChart,not_ne_iff.mp h]
  have hY (z : L × L) : yChart (dilateCharts a f) z = yChart f (S a z) := by
    by_cases h : z.2 ≠ 0
    · simp only [yChart,S,dilateCharts,dif_pos h,dif_pos (mul_ne_zero a.ne_zero h)]
      rw [show a*Units.mk0 z.2 h = Units.mk0 _ (mul_ne_zero a.ne_zero h) from Units.ext rfl]
    · simp [S,yChart,not_ne_iff.mp h]
  refine ⟨hx.comp_continuous ((continuous_const.mul continuous_fst).prodMk (continuous_const.mul continuous_snd)),
    hy.comp_continuous ((continuous_const.mul continuous_fst).prodMk (continuous_const.mul continuous_snd)),
    S a⁻¹ '' C,hC.image (by unfold S; fun_prop),?_,?_⟩
  · rintro ⟨⟨x,y⟩,hc,h⟩
    have h₁ : a⁻¹.val*x = 0 := congrArg Prod.fst h
    have h₂ : a⁻¹.val*y = 0 := congrArg Prod.snd h
    exact h₀ (show (0,0) ∈ C by simpa [(mul_eq_zero.mp h₁).resolve_left a⁻¹.ne_zero,
      (mul_eq_zero.mp h₂).resolve_left a⁻¹.ne_zero] using hc)
  · intro z hz
    rw [hX,hY]
    exact ho _ (fun h => hz ⟨S a z,h,he z⟩)

theorem finite_dilate_test (p : HeightOneSpectrum (𝓞 F)) (a : (LocalField F (.inr p))ˣ)
    {f : Charts (LocalField F (.inr p))} (hf : f ∈ d.testSet (.inr p)) :
    dilateCharts (a^n) f ∈ d.testSet (.inr p) :=
  ⟨d.dilateCharts_glues _ a hf.1,finiteTest_dilate _ hf.2⟩

private def dilateLinear {L : Type} [Field L] (a : Lˣ) : Charts L →ₗ[ℂ] Charts L where
  toFun := dilateCharts a
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The same power dilations preserve the span of tests and transformed tests. -/
theorem dilate_schwartz_of_test (a : Kˣ)
    (hd : ∀ (u : Kˣ) f, f ∈ d.testSet v → dilateCharts (u^n) f ∈ d.testSet v)
    {f : Charts K} (hf : f ∈ d.schwartz v) : dilateCharts (a^n) f ∈ d.schwartz v := by
  suffices h : d.schwartz v ≤ (d.schwartz v).comap (dilateLinear (a^n)) from h hf
  apply Submodule.span_le.mpr
  rintro g (hg | ⟨g,hg,rfl⟩)
  · exact Submodule.subset_span (Or.inl (hd a g hg))
  · let c : ℂ := (modulus F v (a⁻¹^n).val : ℂ)^2
    have hc : c ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (modulus_ne_zero v _))
    have ht := d.integralTransform_dilateCharts v a⁻¹ g
    change _ = c⁻¹ • _ at ht
    rw [inv_pow,inv_inv] at ht
    change dilateCharts (a^n) (d.integralTransform v g) ∈ d.schwartz v
    have he : c • d.integralTransform v (dilateCharts (a⁻¹^n) g) =
        dilateCharts (a^n) (d.integralTransform v g) := by rw [inv_pow,ht,smul_smul,mul_inv_cancel₀ hc,one_smul]
    rw [← he]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨_,hd a⁻¹ g hg,rfl⟩))

theorem finite_dilate_schwartz (p : HeightOneSpectrum (𝓞 F)) (a : (LocalField F (.inr p))ˣ)
    {f : Charts (LocalField F (.inr p))} (hf : f ∈ d.schwartz (.inr p)) :
    dilateCharts (a^n) f ∈ d.schwartz (.inr p) :=
  d.dilate_schwartz_of_test _ a (fun u _ h => d.finite_dilate_test p u h) hf

end MetaplecticPoisson.Datum
