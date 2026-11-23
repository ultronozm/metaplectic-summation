import MetaplecticSummation.ArchimedeanShears
import MetaplecticSummation.FiniteFourierInversion

/-! From ordinary Fourier inversion and the marginal identities to inversion
of the two-chart transform (Appendix A), with ordinary inversion proved at finite places. -/

noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField IsDedekindDomain MeasureTheory
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)
variable (v : Place F)
def torusCharts (a : (LocalField F v)ˣ) (Φ : Charts (LocalField F v)) : Charts (LocalField F v) :=
  (fun x y => d.symbol v x a * d.symbol v (-1) a * Φ.1 (a*x) (y/a),
   fun x y => d.symbol v a y * Φ.2 (a*x) (y/a))


theorem torusCharts_glues (a : (LocalField F v)ˣ) {f : Charts (LocalField F v)}
    (hf : Glues (d.symbol v) f) : Glues (d.symbol v) (d.torusCharts v a f) := by
  intro x y
  have hs : d.unitPairing v (-1) a = d.unitPairing v a a := by
    let H := d.lineSymbol v (by cases v with
      | inl w => exact d.arch_steinberg w
      | inr p => exact d.finite_steinberg p)
    have h := H.neg_self a
    rw [← neg_one_mul a,map_mul] at h
    change H.pairing (-1) a = H.pairing a a
    rw [H.skew]
    exact (inv_eq_of_mul_eq_one_right h)
  have hc : d.symbol v x a * d.symbol v (-1) a * d.symbol v (a*x) (y/a) =
      d.symbol v x y * d.symbol v a y := by
    change ((d.unitPairing v x a * d.unitPairing v (-1) a * d.unitPairing v (a*x) (y/a)).val) = _
    rw [hs,map_mul,MonoidHom.mul_apply,map_div,map_div]
    change ((d.unitPairing v x a * d.unitPairing v a a *
      (d.unitPairing v a y / d.unitPairing v a a * (d.unitPairing v x y / d.unitPairing v x a))).val) =
        ((d.unitPairing v x y * d.unitPairing v a y).val)
    congr 1
    let H := d.unitPairing v
    calc
      _ = (H x y * H a y) * ((H x a * (H x a)⁻¹) * (H a a * (H a a)⁻¹)) := by
        simp only [H,div_eq_mul_inv]
        ac_rfl
      _ = _ := by simp [H]
  simp only [torusCharts]
  have hg := hf (a*x) (y/a)
  simp only [Units.val_div_eq_div_val,Units.val_mul] at hg
  rw [hg,← mul_assoc,hc,mul_assoc]

/-- Composition of diagonal lifts has the Hilbert-symbol multiplier of §5. -/
theorem torusCharts_mul (a b : (LocalField F v)ˣ) (f : Charts (LocalField F v)) :
    d.torusCharts v a (d.torusCharts v b f) = d.symbol v a b • d.torusCharts v (a*b) f := by
  have hs (x y z : (LocalField F v)ˣ) : d.symbol v (x*y) z = d.symbol v x z * d.symbol v y z := by
    change ((d.unitPairing v (x*y) z).val) = _
    rw [map_mul,MonoidHom.mul_apply,Units.val_mul]
    rfl
  have hr (x y z : (LocalField F v)ˣ) : d.symbol v x (y*z) = d.symbol v x y * d.symbol v x z := by
    change ((d.unitPairing v x (y*z)).val) = _
    rw [map_mul,Units.val_mul]
    rfl
  have hd (y : (LocalField F v)ˣ) : d.symbol v b (y/a) = d.symbol v b y * d.symbol v a b := by
    let H := d.lineSymbol v (by cases v with
      | inl w => exact d.arch_steinberg w
      | inr p => exact d.finite_steinberg p)
    change (H.pairing b (y/a)).val = (H.pairing b y * H.pairing a b).val
    rw [map_div,div_eq_mul_inv,← H.skew a b]
  apply Prod.ext
  · funext x y
    change _ * _ * (_ * _ * f.1 (b*(a*x)) (y/a.val/b.val)) =
      d.symbol v a b * (d.symbol v x (a*b) * d.symbol v (-1) (a*b) * f.1 ((a*b)*x) (y/(a*b).val))
    rw [hs,hr,hr,Units.val_mul,div_div,show b*(a*x) = (a*b)*x by ac_rfl]
    ac_rfl
  · funext x y
    change d.symbol v a y * (d.symbol v b (y/a) * f.2 (b.val*(a.val*x)) (y/a/b)) =
      d.symbol v a b * (d.symbol v (a*b) y * f.2 ((a*b).val*x) (y/(a*b)))
    rw [hd,hs,Units.val_mul,div_div,show b.val*(a.val*x) = (a.val*b.val)*x by ac_rfl]
    ac_rfl

@[simp] theorem torusCharts_one (f : Charts (LocalField F v)) : d.torusCharts v 1 f = f := by
  have hr (x : (LocalField F v)ˣ) : d.symbol v x 1 = 1 := congrArg Units.val (map_one (d.unitPairing v x))
  have hl (x : (LocalField F v)ˣ) : d.symbol v 1 x = 1 := by
    change (d.unitPairing v 1 x).val = 1
    rw [map_one]
    rfl
  ext x y <;> simp [torusCharts,hr,hl]

/-- The square formula implies bijectivity. Applying it twice gives multiplication
by the nonzero central scalar {ε,ε}. -/
theorem bijective_of_torus_square (L : d.schwartz v →ₗ[ℂ] d.schwartz v)
    (hinv : ∀ Φ : d.schwartz v, (L (L Φ)).val =
      d.torusCharts v ((-1)^(n+1)) Φ.val) : Function.Bijective L := by
  let e : (LocalField F v)ˣ := (-1)^(n+1)
  let z := d.symbol v e e
  have he : e*e = 1 := by simp only [e,← mul_pow,neg_one_mul,neg_neg,one_pow]
  have hz : z ≠ 0 := (d.unitPairing v e e).ne_zero
  have h4 (Φ : d.schwartz v) : L (L (L (L Φ))) = z • Φ := by
    apply Subtype.ext
    change (L (L (L (L Φ)))).val = z • Φ.val
    rw [hinv,hinv,d.torusCharts_mul,show (-1:(LocalField F v)ˣ)^(n+1) * (-1)^(n+1) = 1 from he,
      d.torusCharts_one]
  constructor
  · intro f g h
    have hh : z • f = z • g := (h4 f).symm.trans ((congrArg (fun x => L (L (L x))) h).trans (h4 g))
    exact (smul_right_injective _ hz) hh
  · intro f
    use L (L (L (z⁻¹ • f)))
    rw [h4,smul_smul,mul_inv_cancel₀ hz,one_smul]

/-- On the axis only the reverse marginal identity for the given section and
ordinary inversion of its density at frequency one are needed. -/
theorem integralTransform_axis_of_marginal (Φ Ψ : d.schwartz v) (y : (LocalField F v)ˣ)
    (σ : LocalField F v → ℂ)
    (hev : σ (-1) = (modulus F v (n : LocalField F v) : ℂ) / (modulus F v y⁻¹.val : ℂ) *
      (modulus F v ((-1 : (LocalField F v)ˣ).val) : ℂ)^(n-1) * d.axis v Φ (-((-1)^n)/y⁻¹))
    (hrev : ∀ t : (LocalField F v)ˣ, d.marginal v Ψ (t^n*y⁻¹) =
      (Real.sqrt (modulus F v (n : LocalField F v)) : ℂ)⁻¹ * d.hat v σ t)
    (hinv : d.hat v (d.hat v σ) 1 = σ (-1)) :
    let e : (LocalField F v)ˣ := (-1)^(n+1)
    (d.integralTransform v Ψ.val).2 0 y = d.symbol v e y * d.axis v Φ (y/e) := by
  let e : (LocalField F v)ˣ := (-1)^(n+1)
  let m : ℝ := modulus F v (n : LocalField F v)
  let k : ℂ := (Real.sqrt m : ℂ)⁻¹
  let c : ℂ := d.symbol v (-1) y / (modulus F v y.val : ℂ) * k
  have he (t : (LocalField F v)ˣ) : d.axisLine v Ψ y t = c * d.hat v σ t := by
    rw [d.axisLine_unit,div_eq_mul_inv (t^n),hrev]
    exact (mul_assoc ..).symm
  let dx := selfDual F d.character v
  letI : NullSingletonClass dx := d.selfDual_nullSingleton v
  have hhat : d.hat v (d.axisLine v Ψ y) 1 = c * d.hat v (d.hat v σ) 1 := by
    unfold hat
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [dx.ae_ne 0] with z hz
    rw [show d.axisLine v Ψ y z = c * d.hat v σ z from he (Units.mk0 z hz),mul_assoc]
    rfl
  have ha := d.axis_integralTransform v Ψ y 1
  simp only [one_pow,one_mul,Units.val_one] at ha
  have hM : modulus F v 1 = 1 := by cases v <;> simp [modulus]
  rw [hM,Complex.ofReal_one,one_zpow,mul_one,hhat,hinv] at ha
  change (d.integralTransform v Ψ.val).2 0 y = k * (c * σ (-1)) at ha
  rw [hev] at ha
  have he₂ : e*e=1 := by simp only [e,← mul_pow,neg_one_mul,neg_neg,one_pow]
  have harg : -((-1:(LocalField F v)ˣ)^n)/y⁻¹ = y/e := by
    have he' : e⁻¹ = e := inv_eq_of_mul_eq_one_right he₂
    rw [div_inv_eq_mul,div_eq_mul_inv,he',mul_comm y]
    simp [e,pow_succ]
  have hsym : d.symbol v e y = d.symbol v (-1) y := by
    rw [show e = (-1)^n * (-1) from pow_succ _ _]
    change (d.unitPairing v ((-1)^n * (-1)) y).val = _
    rw [map_mul,MonoidHom.mul_apply,map_pow,MonoidHom.pow_apply,d.unitPairing_pow,one_mul]
    rfl
  have hn : (n : LocalField F v) ≠ 0 := by
    have h := (diagonal F v).injective.ne (Nat.cast_ne_zero.mpr (NeZero.ne n) : (n : F) ≠ 0)
    simpa only [map_natCast,map_zero] using h
  have hm : 0 < m := by cases v <;> simp [m,modulus,norm_pos_iff,hn,pow_pos]
  have hy : (modulus F v y.val : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (modulus_ne_zero v y)
  have hyi : modulus F v y⁻¹.val = (modulus F v y.val)⁻¹ := by cases v <;> simp [modulus, inv_pow]
  have hneg : modulus F v ((-1 : (LocalField F v)ˣ).val) = 1 := by cases v <;> simp [modulus]
  have hk : (Real.sqrt m : ℂ) * (Real.sqrt m : ℂ) = (m : ℂ) := by
    rw [← Complex.ofReal_mul,Real.mul_self_sqrt hm.le]
  have hk₀ : (Real.sqrt m : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos_of_pos hm).ne'
  change (d.integralTransform v Ψ.val).2 0 y = d.symbol v e y * d.axis v Φ (y/e)
  rw [ha,hsym,harg]
  simp only [c,k,hyi,hneg,Complex.ofReal_inv,Complex.ofReal_one,one_pow,mul_one,div_inv_eq_mul]
  change _ * (d.symbol v (-1) y / (modulus F v y.val : ℂ) * _ * ((m : ℂ) * _ * _)) = _
  rw [← hk]
  field_simp

/-- Lift the square formula on the vertical axis of test sections to both charts,
using the two unipotent shears and chart compatibility. -/
theorem integralTransform_square_of_test_axis
    (axisFormula : ∀ (Φ : d.schwartz v), Φ.val ∈ d.testSet v → ∀ y : (LocalField F v)ˣ,
      (d.integralTransform v (d.integralTransform v Φ.val)).2 0 y =
        d.symbol v ((-1)^(n+1)) y * d.axis v Φ (y/((-1)^(n+1))))
    {f : Charts (LocalField F v)} (hf : f ∈ d.testSet v) :
    d.integralTransform v (d.integralTransform v f) = d.torusCharts v ((-1)^(n+1)) f := by
  have shear {g : Charts (LocalField F v)} (hg : g ∈ d.testSet v) (u : LocalField F v) :
      upperShear (d.symbol v) u g ∈ d.testSet v ∧ lowerShear (d.symbol v) u g ∈ d.testSet v := by
    cases v with
    | inl w => exact d.arch_shear_test w hg u
    | inr p => exact d.finite_shear_test p hg u
  let T := d.integralTransform v
  let e : (LocalField F v)ˣ := (-1)^(n+1)
  have he : e.val*e.val = 1 := congrArg (Units.val : (LocalField F v)ˣ → LocalField F v)
    (show e*e = 1 by simp only [e,← mul_pow,neg_one_mul,neg_neg,one_pow])
  have Y (g : Charts (LocalField F v)) (hg : g ∈ d.testSet v) (x : LocalField F v) (y : (LocalField F v)ˣ) :
      (T (T g)).2 x y = (d.torusCharts v e g).2 x y := by
    let u := x/y.val
    let g' := lowerShear (d.symbol v) u g
    have hg' : g' ∈ d.testSet v := (shear hg u).2
    let Φ : d.schwartz v := ⟨g',Submodule.subset_span (Or.inl hg')⟩
    have ha := axisFormula Φ hg' y
    change (T (T (lowerShear (d.symbol v) u g))).2 0 y =
      d.symbol v e y * g.2 (0+u*(y/e).val) (y/e) at ha
    have hl := transform_square_lower (d.symbol v) n (modulus F v) (selfDual F d.character v)
      (d.character.localValue F v) u g 0 y
    change (T (T (lowerShear (d.symbol v) u g))).2 0 y = (T (T g)).2 (0+u*y.val) y at hl
    rw [hl,zero_add,zero_add] at ha
    have h₁ : u*y.val = x := div_mul_cancel₀ x y.ne_zero
    have h₂ : u*(y/e).val = e.val*x := by
      rw [Units.val_div_eq_div_val,← mul_div_assoc,h₁,div_eq_mul_inv,inv_eq_of_mul_eq_one_right he,mul_comm]
    rw [h₁,h₂] at ha
    exact ha
  have X (g : Charts (LocalField F v)) (hg : g ∈ d.testSet v) (x y : (LocalField F v)ˣ) :
      (T (T g)).1 x y.val = (d.torusCharts v e g).1 x y.val :=
    (d.integralTransform_glues v (d.integralTransform_glues v hg.1) x y).trans
      ((congrArg (d.symbol v x y * ·) (Y g hg x.val y)).trans ((d.torusCharts_glues v e hg.1) x y).symm)
  apply Prod.ext _ (funext fun x => funext (Y f hf x))
  funext x y
  by_cases hy : y ≠ 0
  · exact X f hf x (Units.mk0 y hy)
  · obtain rfl := not_ne_iff.mp hy
    have h := X _ (shear hf (-1)).1 x x
    change (T (T (upperShear (d.symbol v) (-1) f))).1 x x.val =
      d.symbol v x e * d.symbol v (-1) e * f.1 (e*x) (x.val/e.val + -1*(e*x).val) at h
    have hu := transform_square_upper (d.symbol v) n (modulus F v) (selfDual F d.character v)
      (d.character.localValue F v) (-1) f x x.val
    change (T (T (upperShear (d.symbol v) (-1) f))).1 x x.val = (T (T f)).1 x (x.val + -1*x.val) at hu
    rw [hu,neg_one_mul,add_neg_cancel] at h
    have hz : x.val/e.val + -1*(e*x).val = 0 := by
      rw [Units.val_mul,neg_one_mul,← sub_eq_add_neg,sub_eq_zero]
      apply (div_eq_iff e.ne_zero).2
      linear_combination -x*he
    rw [hz] at h
    simpa only [torusCharts,zero_div] using h

end MetaplecticPoisson.Datum
