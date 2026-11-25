import MetaplecticSummation.JacquetBasic

/-! Unit covariance of the Gauss–Ramanujan sum and of the basic function. -/

noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField MeasureTheory MeasureTheory.Measure Set
open scoped NNReal
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)
variable (p : Prime F)
local notation "K" => p.adicCompletion F

private theorem primitive_unit_mul (hp : p.asIdeal.absNorm.Coprime n)
    (u c : Kˣ) (hu : ‖u.val‖ = 1) (y : K) :
    d.primitiveJacquet p (u*c) (u.val*y) = d.symbol (.inr p) c u * d.primitiveJacquet p c y := by
  let H : Kˣ →* Kˣ →* ℂˣ := d.unitPairing (.inr p)
  have hc' : ‖(u*c).val‖ = ‖c.val‖ := by rw [Units.val_mul,norm_mul,hu,one_mul]
  have hy' : ‖u.val*y‖ = ‖y‖ := by rw [norm_mul,hu,one_mul]
  unfold primitiveJacquet
  rw [hc',hy']
  by_cases hc : ‖c.val‖ = 1
  · have he := congrArg Units.val (d.unitPairing_tame_units p hp c u hc hu)
    change d.symbol (.inr p) c u = 1 at he
    rw [if_pos hc,if_pos hc, he,one_mul]
  rw [if_neg hc,if_neg hc]
  by_cases h : ‖c.val‖ < 1 ∧ ‖y‖ = 1
  · have hy : y ≠ 0 := norm_ne_zero_iff.mp (h.2 ▸ one_ne_zero)
    let a := Units.mk0 y hy
    have hau : Units.mk0 (u.val*y) (mul_ne_zero u.ne_zero hy) = u*a := Units.ext rfl
    have he : H (u*c) (Units.mk0 (u.val*y) (mul_ne_zero u.ne_zero hy)) = H c u * H c a := by
      simp only [hau,map_mul,MonoidHom.mul_apply,
        show H u u = 1 from d.unitPairing_tame_units p hp u u hu hu,
        show H u a = 1 from d.unitPairing_tame_units p hp u a hu h.2,one_mul,one_mul]
    have hphase : -(u.val*y)/(u*c).val = -y/c.val := by rw [Units.val_mul]; field_simp
    simp only [if_pos h,residueTerm,dif_pos (mul_ne_zero u.ne_zero hy),dif_pos hy,hphase]
    rw [← mul_assoc]
    apply congrArg (fun z : ℂ => z * d.character.localValue F (.inr p) (-y/c.val))
    exact congrArg Units.val he
  · simp only [if_neg h,mul_zero]

theorem localGauss_unit_mul (hp : p.asIdeal.absNorm.Coprime n)
    (hψ : ∀ x : K, ‖x‖ ≤ 1 → d.character.localValue F (.inr p) x = 1)
    (u c : Kˣ) (hu : ‖u.val‖ = 1) :
    d.localGauss p (u*c) = d.symbol (.inr p) c u * d.localGauss p c := by
  letI : MeasurableSpace K := borel _
  letI : BorelSpace K := ⟨rfl⟩
  letI : NontriviallyNormedField K := FinitePlace.nontriviallyNormedCompletion p
  letI : ProperSpace K := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace _
  let μ : Measure K := addHaar
  letI : μ.IsAddHaarMeasure := inferInstanceAs ((addHaar : Measure K).IsAddHaarMeasure)
  let O := p.adicCompletionIntegers F
  let V := μ.real (O : Set K)
  have hc : ‖(u*c).val‖ = ‖c.val‖ := by rw [Units.val_mul,norm_mul,hu,one_mul]
  have hV : 0 < V := ENNReal.toReal_pos ((FinitePlace.isOpen_adicCompletionIntegers p).measure_pos μ
    ⟨0,O.zero_mem⟩).ne' (FinitePlace.isCompact_adicCompletionIntegers p).measure_ne_top
  have hn : ((V : ℂ) * (‖c.val‖ : ℂ)) ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hV.ne')
    (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr c.ne_zero))
  let g := d.primitiveJacquet p (u*c)
  have hi := integral_unit_mul_add μ u 0 g
  have hi' : (∫ y, g (u.val*y) ∂μ) = ∫ y, g y ∂μ := by
    simpa only [add_zero,FinitePlace.haarChar_eq_nnnorm,Units.val_inv_eq_inv_val,nnnorm_inv,
      show ‖u.val‖₊ = 1 from NNReal.eq hu,inv_one,one_smul] using hi
  have h₁ := (d.primitiveJacquet_integral p hp hψ μ (u*c)).2
  have h₂ := (d.primitiveJacquet_integral p hp hψ μ c).2
  apply mul_left_cancel₀ hn
  calc
    _ = ∫ y, g y ∂μ := hc ▸ h₁.symm
    _ = ∫ y, d.symbol (.inr p) c u * d.primitiveJacquet p c y ∂μ :=
      hi'.symm.trans (integral_congr_ae (Filter.Eventually.of_forall (d.primitive_unit_mul p hp u c hu)))
    _ = _ := by rw [integral_const_mul,h₂]; change _ = (μ.real (O : Set K) : ℂ) * _ * _; ring

/-- The second identity of the Gauss–Ramanujan lemma, for the Jacquet
weight at every nonzero argument. -/
theorem jacquet_basic_unit_mul (hp : p.asIdeal.absNorm.Coprime n)
    (hψ : ∀ x : K, ‖x‖ ≤ 1 → d.character.localValue F (.inr p) x = 1)
    (u c : Kˣ) (hu : ‖u.val‖ = 1) :
    let v : Place F := .inr p
    d.jacquet v (d.basic v) (u*c) = d.symbol v c u * d.jacquet v (d.basic v) c := by
  obtain ⟨π,hπ⟩ := FinitePlace.exists_norm_uniformizer p
  let v : Place F := .inr p
  let H : Kˣ →* Kˣ →* ℂˣ := d.unitPairing v
  have hterm (k : ℕ) : d.localGauss p ((u*c)/π^(n*k)) =
      d.symbol v c u * d.localGauss p (c/π^(n*k)) := by
    rw [mul_div_assoc,d.localGauss_unit_mul p hp hψ u _ hu]
    congr 1
    apply congrArg Units.val
    change H (c/π^(n*k)) u = H c u
    rw [Nat.mul_comm n k,pow_mul,map_div,MonoidHom.div_apply,map_pow,MonoidHom.pow_apply,
      show H (π^k) u^n = 1 from d.unitPairing_pow v _ _,div_one]
  have he := d.jacquet_basic p hp hψ π (u*c) hπ
  have he' := d.jacquet_basic p hp hψ π c hπ
  let V : ℂ := (selfDual F d.character v).real {x | ‖x‖ ≤ 1}
  let w (k : ℕ) : ℂ := (p.asIdeal.absNorm : ℂ)^((n-1)*k)
  change d.jacquet v (d.basic v) (u*c) = _
  rw [he,he']
  change V * (‖(u*c).val‖ : ℂ) * (∑' k, w k * d.localGauss p ((u*c)/π^(n*k))) =
    d.symbol v c u * (V * (‖c.val‖ : ℂ) * ∑' k, w k * d.localGauss p (c/π^(n*k)))
  simp_rw [hterm, mul_left_comm (w _) (d.symbol v c u)]
  rw [tsum_mul_left,Units.val_mul,norm_mul,hu,one_mul]
  ring

theorem gaussRamanujan_unit_pow (hp : p.asIdeal.absNorm.Coprime n)
    (hψ : ∀ x : K, ‖x‖ ≤ 1 → d.character.localValue F (.inr p) x = 1)
    (u c : Kˣ) (hu : ‖u.val‖ = 1) :
    let v : Place F := .inr p
    d.localGauss p (u^n*c) = d.localGauss p c ∧
      d.jacquet v (d.basic v) (u^n*c) = d.jacquet v (d.basic v) c := by
  have hnorm : ‖(u^n).val‖ = 1 := by rw [Units.val_pow_eq_pow_val,norm_pow,hu,one_pow]
  let H : Kˣ →* Kˣ →* ℂˣ := d.unitPairing (.inr p)
  have hH : H c (u^n) = 1 := (map_pow (H c) u n).trans (d.unitPairing_pow (.inr p) c u)
  have hs : d.symbol (.inr p) c (u^n) = 1 := congrArg Units.val hH
  exact ⟨(d.localGauss_unit_mul p hp hψ (u^n) c hnorm).trans (by rw [hs,one_mul]),
    (d.jacquet_basic_unit_mul p hp hψ (u^n) c hnorm).trans (by rw [hs,one_mul])⟩

end MetaplecticPoisson.Datum
