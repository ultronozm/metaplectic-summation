import MetaplecticSummation.RayFourier

/-! Conductors and self-dual measures under scaling of the additive character. -/

noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField IsDedekindDomain MeasureTheory
open scoped ENNReal NNReal
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [hn : NeZero n] (d : Datum F n)

abbrev Prime (F : Type) [Field F] [NumberField F] := HeightOneSpectrum (𝓞 F)

abbrev atPlace (v : Place F) (x : Fˣ) : (LocalField F v)ˣ := Units.map (diagonal F v) x

def UnramifiedAt (v : Place F) : Prop :=
  ∀ x : LocalField F v, (∀ y : LocalField F v, ‖y‖ ≤ 1 →
    d.character.localValue F v (x * y) = 1) ↔ ‖x‖ ≤ 1

omit hn in
theorem exists_scaled (b : Fˣ) : ∃ ψ : Character F, ∀ x,
    ψ.toChar x = d.character.toChar (algebraMap F (Adeles F) (b : F) * x) := by
  let χ := d.character.toChar.mulShift (algebraMap F (Adeles F) (b : F))
  refine ⟨⟨χ, d.character.continuous_toChar.comp (continuous_const.mul continuous_id), ?_, ?_⟩,
    fun _ => rfl⟩
  · obtain ⟨x, hx⟩ := d.character.nontrivial
    refine ⟨algebraMap F (Adeles F) (↑b⁻¹ : F) * x, ?_⟩
    simpa only [χ, AddChar.mulShift_apply, ← mul_assoc, ← map_mul, Units.mul_inv, map_one,
      one_mul] using hx
  · intro a
    exact (congrArg d.character.toChar (map_mul _ (b : F) a).symm).trans
      (d.character.trivial_diagonal _)

def scaled (b : Fˣ) : Datum F n := { d with character := (d.exists_scaled b).choose }

omit hn in
theorem scaled_localValue (b : Fˣ) (v : Place F) (x : LocalField F v) :
    (d.scaled b).character.localValue F v x = d.character.localValue F v (diagonal F v b * x) := by
  unfold Character.localValue
  rw [show (d.scaled b).character.toChar (singleAdele F v x) = _ from
    (d.exists_scaled b).choose_spec (singleAdele F v x)]
  congr 2
  classical
  cases v with
  | inl w =>
    apply Prod.ext
    · funext u
      change algebraMap F u.Completion (b : F) * Pi.single w x u = Pi.single w (_ * x) u
      by_cases h : u = w
      · subst u; simp only [Pi.single_eq_same]; rfl
      · simp only [Pi.single_eq_of_ne h, mul_zero]
    · exact mul_zero _
  | inr p =>
    apply Prod.ext (mul_zero _)
    exact (RestrictedProduct.mul_single _ p x (algebraMap F (Adeles F) (b : F)).2).symm

omit hn in
/-- The annihilator of the integers for the scaled character is the
inverse image of the original annihilator under multiplication by b. -/
theorem scaled_conductor (b : Fˣ) (v : Place F) (h : d.UnramifiedAt v)
    (x : LocalField F v) :
    (∀ y : LocalField F v, ‖y‖ ≤ 1 → (d.scaled b).character.localValue F v (x*y) = 1) ↔
      ‖x * diagonal F v b‖ ≤ 1 := by
  simp only [d.scaled_localValue, ← mul_assoc]
  simpa only [mul_comm x (diagonal F v b)] using h (diagonal F v b * x)

omit [NeZero n] in
/-- Replacing ψ(x) by ψ(bx) multiplies its self-dual measure by |b|^(1/2). -/
theorem selfDual_scaled (v : Place F) (b : Fˣ) :
    selfDual F (d.scaled b).character v =
      NNReal.sqrt (modulus F v (diagonal F v b)).toNNReal • selfDual F d.character v := by
  let μ := selfDual F d.character v
  let u := atPlace v b
  let M := (modulus F v u.val).toNNReal
  let r := NNReal.sqrt M
  have hm : 0 < modulus F v u.val := by cases v <;> simp [modulus,u,b.ne_zero,atPlace]
  have hM : M ≠ 0 := (Real.toNNReal_pos.mpr hm).ne'
  have hr : r ≠ 0 := by simpa [r] using hM
  have hμ := (existsUnique_selfDual F d.character v).exists.choose_spec
  letI : μ.IsAddHaarMeasure := hμ.1
  apply (existsUnique_selfDual F (d.scaled b).character v).unique
    (existsUnique_selfDual F (d.scaled b).character v).exists.choose_spec
  refine ⟨Measure.IsAddHaarMeasure.nnreal_smul μ hr,?_⟩
  intro f hf hfc
  let hat (y : LocalField F v) := ∫ x, f x * d.character.localValue F v (x*y) ∂μ
  have hhat (y : LocalField F v) :
      (∫ x, f x * (d.scaled b).character.localValue F v (x*y) ∂(r • μ)) =
        (r : ℂ) * hat (u.val*y) := by
    rw [integral_smul_nnreal_measure,NNReal.smul_def,Complex.real_smul]
    congr 1
    apply integral_congr_ae
    filter_upwards with x
    rw [d.scaled_localValue]
    change _ * d.character.localValue F v (u.val*(x*y)) = _
    rw [mul_left_comm]
  let g (y : LocalField F v) := ‖hat y‖ₑ^2
  have hg : (∫⁻ y, g (u.val*y) ∂μ) = (M : ℝ≥0∞)⁻¹ * ∫⁻ y, g y ∂μ := by
    have he := (lintegral_map_equiv (μ := μ) g (MeasurableEquiv.smul (α := LocalField F v) u)).symm
    change (∫⁻ y, g (u.val*y) ∂μ) = ∫⁻ y, g y ∂Measure.map (fun x => u.val*x) μ at he
    rw [d.map_local_mul v u,lintegral_smul_measure] at he
    rw [← ENNReal.coe_inv hM]
    exact he
  have hen : ‖(r : ℂ)‖ₑ = (r : ℝ≥0∞) := by
    change ((‖(r : ℂ)‖₊ : ℝ≥0) : ℝ≥0∞) = _
    rw [Complex.nnnorm_real]
    exact congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) (Real.nnnorm_of_nonneg r.property)
  change (∫⁻ y, ‖∫ x, f x * (d.scaled b).character.localValue F v (x*y) ∂(r • μ)‖ₑ^2 ∂(r • μ)) =
    ∫⁻ x, ‖f x‖ₑ^2 ∂(r • μ)
  simp_rw [hhat,enorm_mul,mul_pow,hen]
  have hsq : (r : ℝ≥0∞)^2 = M := by exact_mod_cast NNReal.sq_sqrt M
  rw [hsq,lintegral_smul_measure,lintegral_smul_measure,lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  change (r : ℝ≥0∞) * (M * ∫⁻ y, g (u.val*y) ∂μ) = _
  rw [hg,← mul_assoc (M : ℝ≥0∞),ENNReal.mul_inv_cancel (by exact_mod_cast hM) ENNReal.coe_ne_top,one_mul]
  exact congrArg (fun t : ℝ≥0∞ => (r : ℝ≥0∞) * t) (hμ.2 f hf hfc)

end MetaplecticPoisson.Datum
