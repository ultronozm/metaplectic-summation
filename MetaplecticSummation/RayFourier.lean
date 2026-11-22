import MetaplecticSummation.WildSymbols
import MetaplecticSummation.LocalCharacters

/-! The Fourier transform along an n-th-power ray (§4.3). -/

noncomputable section
namespace MetaplecticPoisson
open MeasureTheory Filter
open Classical
open scoped NNReal

variable {K : Type*} [Field K] [MeasurableSpace K] {n : ℕ}

/-- Scaling the output by u^n and the line parameter by u preserves the line.
The normalized line integral acquires the factor |u|^(-n). -/
theorem LineSymbol.radon_pow_ray (H : LineSymbol K n) (m : K → ℝ)
    (hm : ∀ (u a : Kˣ), m (u.val ^ n * a.val) = m u.val ^ n * m a.val)
    (dx : Measure K) (f : Charts K) (u : Kˣ) (t : K) :
    let R := radon n (fun a b => H.pairing a b) m dx f
    (∀ (a : Kˣ) (b : K), (R (u.val*t)).1 (u^n*a) (u.val^n*b) = (R t).1 a b / (m u.val : ℂ)^n) ∧
    (∀ (a : K) (b : Kˣ), (R (u.val*t)).2 (u.val^n*a) (u^n*b) = (R t).2 a b / (m u.val : ℂ)^n) := by
  constructor
  · intro a b
    have hcoord (x : K) :
        (x*(u.val^n*b)-(u.val*t)^n)/(u.val^n*a.val) = (x*b-t^n)/a.val := by
      rw [mul_pow]
      field_simp
    have hs (x : Kˣ) : H.pairing x (-(u^n*a)) = H.pairing x (-a) := by
      rw [← mul_neg, map_mul, H.pow_right, one_mul]
    simp only [radon, hcoord, hs, Units.val_mul, Units.val_pow_eq_pow_val, hm, Complex.ofReal_mul,
      Complex.ofReal_pow, div_div, mul_comm (m a.val : ℂ)]
  · intro a b
    have hcoord (y : K) :
        (u.val^n*a*y+(u.val*t)^n)/(u.val^n*b.val) = (a*y+t^n)/b.val := by
      rw [mul_pow]
      field_simp
    have hs (y : Kˣ) : H.pairing y (u^n*b) = H.pairing y b := by rw [map_mul, H.pow_right, one_mul]
    simp only [radon, hcoord, hs, Units.val_mul, Units.val_pow_eq_pow_val, hm, Complex.ofReal_mul,
      Complex.ofReal_pow, div_div, mul_comm (m b.val : ℂ)]

namespace Datum
open NumberField IsDedekindDomain
variable {F : Type} [Field F] [NumberField F] [NeZero n] (d : Datum F n)

omit [NeZero n] in
private theorem modulus_pow_mul (v : Place F) (u a : (LocalField F v)ˣ) :
    modulus F v (u.val^n * a.val) = modulus F v u.val ^ n * modulus F v a.val := by
  cases v with
  | inl w => simp [modulus, norm_mul, norm_pow, mul_pow, ← pow_mul, Nat.mul_comm n]
  | inr p => simp [modulus, norm_mul, norm_pow]

theorem modulus_ne_zero (v : Place F) (u : (LocalField F v)ˣ) : modulus F v u.val ≠ 0 := by
  cases v <;> simp [modulus, u.ne_zero]

omit [NeZero n] in
/-- Pushforward of additive Haar measure by multiplication on the local field. -/
theorem map_local_mul (v : Place F) (u : (LocalField F v)ˣ) :
    let dx := selfDual F d.character v
    Measure.map (fun x => u.val*x) dx = (modulus F v u.val).toNNReal⁻¹ • dx := by
  letI : LocallyCompactSpace (LocalField F v) := by
    cases v with
    | inl w => exact inferInstanceAs (LocallyCompactSpace w.Completion)
    | inr p => exact inferInstanceAs (LocallyCompactSpace (p.adicCompletion F))
  letI : TopologicalSpace.SeparableSpace (LocalField F v) := by
    cases v with
    | inl w =>
      letI : SecondCountableTopology (LocalField F (.inl w)) :=
        (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
      exact inferInstance
    | inr p =>
      letI : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
      exact TopologicalSpace.SeparableSpace.of_denseRange _ (HeightOneSpectrum.denseRange_algebraMap (K := F) p)
  let dx := selfDual F d.character v
  letI : dx.IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  have hm : modulus F v u.val = (distribHaarChar (LocalField F v) u : ℝ) := by
    cases v with
    | inl w => exact arch_modulus w u
    | inr p => exact (congrArg NNReal.toReal (FinitePlace.haarChar_eq_nnnorm p u)).symm
  let e := MeasurableEquiv.smul (α := LocalField F v) u
  change Measure.map e dx = _
  have hmap : Measure.map e dx = DomMulAct.mk u⁻¹ • dx := by
    change _ = Measure.map (fun x => (u⁻¹)⁻¹ • x) dx
    rw [inv_inv]
    rfl
  rw [hmap, Measure.isAddLeftInvariant_eq_smul_of_regular (DomMulAct.mk u⁻¹ • dx) dx,
    addHaarScalarFactor_smul_eq_distribHaarChar, map_inv, hm,Real.toNNReal_coe]

omit [NeZero n] in
/-- The one-dimensional substitution with the normalized modulus used in the paper. -/
theorem integral_local_mul (v : Place F) (u : (LocalField F v)ˣ) (g : LocalField F v → ℂ) :
    let dx := selfDual F d.character v
    (∫ x, g (u.val*x) ∂dx) = (∫ x, g x ∂dx) / (modulus F v u.val : ℂ) := by
  let e := MeasurableEquiv.smul (α := LocalField F v) u
  have h := (integral_map_equiv (μ := selfDual F d.character v) e g).symm
  change (∫ x, g (u.val*x) ∂_) = ∫ x, g x ∂Measure.map (fun x => u.val*x) _ at h
  rw [d.map_local_mul v u,integral_smul_nnreal_measure] at h
  have hm : 0 ≤ modulus F v u.val := by cases v <;> simp [modulus,pow_nonneg]
  simpa only [NNReal.smul_def,NNReal.coe_inv,Real.coe_toNNReal _ hm,Complex.real_smul,
    Complex.ofReal_inv,div_eq_inv_mul] using h

/-- The power-ray formula of §4.3. Multiplying the transform along a power ray by the factor
|u|^(n−1) gives an ordinary one-dimensional Fourier integral. -/
theorem transform_pow_ray (v : Place F) (f : Charts (LocalField F v)) (u : (LocalField F v)ˣ) :
    let ψ := d.character.localValue F v
    let dx := selfDual F d.character v
    let R := radon n (d.symbol v) (modulus F v) dx f
    let c : ℂ := (Real.sqrt (modulus F v (n : LocalField F v)))⁻¹
    let g := d.integralTransform v f
    (∀ (a : (LocalField F v)ˣ) (b : LocalField F v),
      (modulus F v u.val : ℂ)^(n-1) * g.1 (u^n*a) (u.val^n*b) = c * ∫ t, (R t).1 a b * ψ (u.val*t) ∂dx) ∧
    (∀ (a : LocalField F v) (b : (LocalField F v)ˣ),
      (modulus F v u.val : ℂ)^(n-1) * g.2 (u.val^n*a) (u^n*b) = c * ∫ t, (R t).2 a b * ψ (u.val*t) ∂dx) := by
  let ψ := d.character.localValue F v
  let dx := selfDual F d.character v
  let R := radon n (d.symbol v) (modulus F v) dx f
  let c : ℂ := (Real.sqrt (modulus F v (n : LocalField F v)))⁻¹
  let m : ℂ := modulus F v u.val
  have hm : m ≠ 0 := Complex.ofReal_ne_zero.mpr (modulus_ne_zero v u)
  let H := d.lineSymbol v (by cases v with
    | inl w => exact d.arch_steinberg w
    | inr p => exact d.finite_steinberg p)
  have scale (s t : LocalField F v → ℂ) (h : ∀ x, s (u.val*x) = t x / m^n) :
      m^(n-1) * (c * ∫ x, ψ x * s x ∂dx) = c * ∫ x, t x * ψ (u.val*x) ∂dx := by
    have he := d.integral_local_mul v u (fun x => ψ x * s x)
    change (∫ x, ψ (u.val*x) * s (u.val*x) ∂dx) = (∫ x, ψ x * s x ∂dx) / m at he
    simp_rw [h, mul_div_assoc', mul_comm (ψ _) (t _)] at he
    rw [integral_div] at he
    have e : m^(n-1) * m = m^n := by rw [← pow_succ, Nat.sub_add_cancel (NeZero.pos n)]
    rw [← (eq_div_iff hm).mp he, ← e]
    field_simp
  constructor
  · intro a b
    exact scale _ _ (fun t => (H.radon_pow_ray _ (modulus_pow_mul v) dx f u t).1 a b)
  · intro a b
    exact scale _ _ (fun t => (H.radon_pow_ray _ (modulus_pow_mul v) dx f u t).2 a b)

end Datum
end MetaplecticPoisson
