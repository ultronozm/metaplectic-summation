import MetaplecticSummation.FiniteInversion

/-! Covariance of the defining integral under the diagonal lifts of §5. -/

noncomputable section
namespace MetaplecticPoisson.Datum
open MeasureTheory NumberField IsDedekindDomain Set
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n) (v : Place F)

omit [NeZero n] in
private theorem integral_rescale_line (a b : (LocalField F v)ˣ) (c : ℂ) (f g : LocalField F v → ℂ)
    (h : ∀ x, f x = c * g (a.val*x)) :
    (∫ x, f x ∂selfDual F d.character v) / (modulus F v b.val : ℂ) =
      c * ((∫ x, g x ∂selfDual F d.character v) / (modulus F v (a*b).val : ℂ)) := by
  have hm : modulus F v (a*b).val = modulus F v a.val * modulus F v b.val := by
    cases v <;> simp [modulus,norm_mul,mul_pow]
  simp_rw [h]
  rw [integral_const_mul,d.integral_local_mul,hm,Complex.ofReal_mul]
  ring

/-- The two normalized line integrals transform by the chart multipliers of the diagonal lift. -/
theorem radon_torusCharts (a : (LocalField F v)ˣ) (f : Charts (LocalField F v)) (t : LocalField F v) :
    let R := fun g => radon n (d.symbol v) (modulus F v) (selfDual F d.character v) g t
    R (d.torusCharts v a f) = d.torusCharts v a (R f) := by
  let H := d.lineSymbol v (by cases v with
    | inl w => exact d.arch_steinberg w
    | inr p => exact d.finite_steinberg p)
  have X (x b : (LocalField F v)ˣ) : H.pairing x a * H.pairing x (-b) =
      H.pairing b a * H.pairing (a*x) (-(a*b)) := by
    have h : H.pairing a a * H.pairing a (-b) = H.pairing a b := by
      rw [← map_mul,show a*(-b) = (-a)*b by simp,map_mul,H.neg_self,one_mul]
    rw [show -(a*b) = a*(-b) by simp]
    simp only [map_mul,MonoidHom.mul_apply]
    rw [H.skew b a,← h]
    apply Units.ext
    simp only [Units.val_mul,Units.val_inv_eq_inv_val]
    field_simp
  have Y (y b : (LocalField F v)ˣ) : H.pairing a y * H.pairing y b * H.pairing (-1) b =
      H.pairing a b * H.pairing (y/a) (b/a) * H.pairing (-1) (b/a) := by
    have haa : H.pairing (-1) a = H.pairing a a := by
      have h := H.neg_self a
      rw [← neg_one_mul a,map_mul] at h
      rw [H.skew]
      exact inv_eq_of_mul_eq_one_right h
    simp only [map_div,MonoidHom.div_apply,haa]
    rw [H.skew a y]
    apply Units.ext
    simp only [Units.val_mul,Units.val_inv_eq_inv_val,Units.val_div_eq_div_val]
    field_simp
  apply Prod.ext
  · funext b z
    apply d.integral_rescale_line v a b
    intro x
    by_cases hx : x = 0
    · simp [hx]
    · let u := Units.mk0 x hx
      have hax : a.val*x ≠ 0 := mul_ne_zero a.ne_zero hx
      have coord : (a.val*x*(z/a.val)-t^n)/(a*b).val = ((x*z-t^n)/b.val)/a.val := by
        rw [Units.val_mul]; field_simp
      simp only [dif_pos hx,dif_pos hax,torusCharts,coord]
      rw [show Units.mk0 (a.val*x) hax = a*u by ext; rfl]
      have hs := congrArg Units.val (X u b)
      change d.symbol v u a * d.symbol v u (-b) = d.symbol v b a * d.symbol v (a*u) (-(a*b)) at hs
      change d.symbol v u a * d.symbol v (-1) a * f.1 (a*u) _ * d.symbol v u (-b) =
        (d.symbol v b a * d.symbol v (-1) a) * (f.1 (a*u) _ * d.symbol v (a*u) (-(a*b)))
      linear_combination (d.symbol v (-1) a * f.1 (a*u) (((x*z-t^n)/b.val)/a.val)) * hs
  · funext z b
    have hb : b/a = a⁻¹*b := by simp [div_eq_mul_inv,mul_comm]
    dsimp only [torusCharts,radon]
    rw [hb]
    apply d.integral_rescale_line v a⁻¹ b
    intro y
    by_cases hy : y = 0
    · simp [hy]
    · let u := Units.mk0 y hy
      have hay : a⁻¹.val*y ≠ 0 := mul_ne_zero a⁻¹.ne_zero hy
      have coord : (a.val*z*(a⁻¹.val*y)+t^n)/(a⁻¹*b).val = a.val*((z*y+t^n)/b.val) := by
        rw [Units.val_mul,Units.val_inv_eq_inv_val]; field_simp
      simp only [dif_pos hy,dif_pos hay,coord]
      have hs := congrArg Units.val (Y u b)
      rw [hb,show u/a = a⁻¹*u by simp [div_eq_mul_inv,mul_comm]] at hs
      change d.symbol v a u * d.symbol v u b * d.symbol v (-1) b =
        d.symbol v a b * d.symbol v (a⁻¹*u) (a⁻¹*b) * d.symbol v (-1) (a⁻¹*b) at hs
      rw [show Units.mk0 (a⁻¹.val*y) hay = a⁻¹*u by ext; rfl]
      rw [show Units.mk0 y hy / a = a⁻¹*u by simp [u,div_eq_mul_inv,mul_comm]]
      linear_combination (f.2 (a.val*((z*y+t^n)/b.val)) (a⁻¹*u)) * hs

/-- The integral transform commutes with every diagonal lift at every place. -/
theorem integralTransform_torusCharts (a : (LocalField F v)ˣ) (f : Charts (LocalField F v)) :
    d.integralTransform v (d.torusCharts v a f) = d.torusCharts v a (d.integralTransform v f) := by
  have pull (c k : ℂ) (g : LocalField F v → ℂ) :
      k * (∫ t, d.character.localValue F v t * (c*g t) ∂selfDual F d.character v) =
        c * (k * ∫ t, d.character.localValue F v t * g t ∂selfDual F d.character v) := by
    simp_rw [mul_left_comm (d.character.localValue F v _) c,integral_const_mul]
    ring
  have ht := d.radon_torusCharts v a f
  dsimp only at ht
  apply Prod.ext <;> funext x y <;>
    simp only [integralTransform,transform] <;>
    simp_rw [ht] <;> apply pull

/-- The diagonal lift is linear on all pairs of chart functions. -/
def torusLinear (a : (LocalField F v)ˣ) : Charts (LocalField F v) →ₗ[ℂ] Charts (LocalField F v) where
  toFun := d.torusCharts v a
  map_add' f g := by ext x y <;> simp [torusCharts,mul_add]
  map_smul' c f := by ext x y <;> simp [torusCharts,mul_left_comm]

/-- At finite places every diagonal lift preserves the test space. -/
theorem torusCharts_finiteTest (p : HeightOneSpectrum (𝓞 F)) (a : (LocalField F (.inr p))ˣ)
    {f : Charts (LocalField F (.inr p))} (hf : f ∈ d.testSet (.inr p)) :
    d.torusCharts (.inr p) a f ∈ d.testSet (.inr p) := by
  let v : Place F := .inr p
  let K := LocalField F v
  obtain ⟨hx,hy,C,hC,h₀,hout⟩ := (show finiteTest f from hf.2)
  have hl := (d.locallyConstant_unitPairing v).comp Units.val
  let back (z : K × K) := (z.1/a.val,z.2*a.val)
  have hb : Continuous back := (continuous_fst.div_const a.val).prodMk (continuous_snd.mul continuous_const)
  refine ⟨d.torusCharts_glues _ _ hf.1,?_⟩
  change finiteTest (d.torusCharts v a f)
  refine ⟨?_,?_,back '' C,hC.image hb,?_,?_⟩
  · exact ((hl.comp_continuous (continuous_fst.prodMk continuous_const)).comp
      (fun z => z * d.symbol v (-1) a)).mul
        (hx.comp_continuous ((continuous_const.mul continuous_fst).prodMk (continuous_snd.div_const _)))
  · exact (hl.comp_continuous (continuous_const.prodMk continuous_snd)).mul
      (hy.comp_continuous ((continuous_const.mul continuous_fst).prodMk (continuous_snd.div_const _)))
  · rintro ⟨⟨x,y⟩,hc,he⟩
    have h₁ : x/a.val = 0 := congrArg Prod.fst he
    have h₂ : y*a.val = 0 := congrArg Prod.snd he
    exact h₀ (show (0,0) ∈ C by simpa [(div_eq_zero_iff.mp h₁).resolve_right a.ne_zero,
      (mul_eq_zero.mp h₂).resolve_right a.ne_zero] using hc)
  · rintro ⟨x,y⟩ h
    have ho : (a.val*x,y/a.val) ∉ C := fun hc => h ⟨_,hc,by simp [back,mul_div_cancel_left₀ _ a.ne_zero]⟩
    obtain ⟨hX,hY⟩ := hout _ ho
    constructor
    · by_cases hx : x ≠ 0
      · let u := Units.mk0 x hx
        have h := hX
        change xChart f ((a*u).val,y/a.val) = 0 at h
        simp only [xChart,dif_pos (a*u).ne_zero,Units.mk0_val] at h
        simpa [xChart,hx,torusCharts] using (show d.symbol v u a * d.symbol v (-1) a * f.1 (a*u) (y/a.val) = 0 by rw [h,mul_zero])
      · simp [xChart,hx]
    · by_cases hy : y ≠ 0
      · let u := Units.mk0 y hy
        have h := hY
        rw [← show (u/a).val = y/a.val by simp [u]] at h
        simp only [yChart,dif_pos (u/a).ne_zero,Units.mk0_val] at h
        simpa [yChart,hy,torusCharts] using (show d.symbol v a u * f.2 (a.val*x) (u/a) = 0 by rw [h,mul_zero])
      · simp [yChart,hy]

end MetaplecticPoisson.Datum
