import MetaplecticSummation.LinearFactor
import MetaplecticSummation.FiniteGerms

/-! The Radon integral and its change of chart in the reverse marginal formula. -/

noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField IsDedekindDomain MeasureTheory Set
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

/-- The integral transform of a test section belongs to the defining span of
the Schwartz space before stability of the space under iteration is known. -/
def transformTest (v : Place F) (Φ : d.schwartz v) (hΦ : Φ.val ∈ d.testSet v) : d.schwartz v :=
  ⟨d.integralTransform v Φ.val, Submodule.subset_span (Or.inr ⟨Φ.val,hΦ,rfl⟩)⟩

theorem transformTest_eq_fourier (v : Place F) (Φ : d.schwartz v) (hΦ : Φ.val ∈ d.testSet v) :
    d.transformTest v Φ hΦ = d.fourier v Φ :=
  Subtype.ext (d.fourier_apply v Φ).symm

/-- The X-chart Radon integral expressed entirely in the Y chart, as in
Appendix A before the substitution u = 1/y'. -/
theorem radon_X_via_Y (v : Place F) {f : Charts (LocalField F v)} (hf : Glues (d.symbol v) f)
    (s u : (LocalField F v)ˣ) (t : LocalField F v) :
    let dx := selfDual F d.character v
    (radon n (d.symbol v) (modulus F v) dx f t).1 s u.val =
      (∫ y, if hy : y ≠ 0 then f.2 ((t^n+s.val*y)/u.val) (Units.mk0 y hy) *
        d.symbol v (-(s*Units.mk0 y hy)) u else 0 ∂dx) / (modulus F v u.val : ℂ) := by
  dsimp only
  rw [d.radon_glues v hf t s u]
  simp only [radon,mul_div_assoc',← integral_const_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards with y
  by_cases hy : y = 0
  · simp [hy]
  · have hs : d.symbol v (-(s * Units.mk0 y hy)) u =
        d.symbol v (-1) u * (d.symbol v s u * d.symbol v (Units.mk0 y hy) u) := by
      change (d.unitPairing v (-(s*Units.mk0 y hy)) u).val = _
      rw [← neg_one_mul (s*Units.mk0 y hy),map_mul,map_mul,MonoidHom.mul_apply,MonoidHom.mul_apply,
        Units.val_mul,Units.val_mul]
      rfl
    rw [dif_pos hy,dif_pos hy,hs,add_comm]
    ring

/-- The Fourier transform of the Radon slice at a nonzero frequency, with the
normalization needed when testing a marginal against multiplicative measure. -/
theorem hat_radon_scaled_charts (v : Place F) (f : Charts (LocalField F v)) (s u : (LocalField F v)ˣ) (y : LocalField F v) :
    let dx := selfDual F d.character v
    d.hat v (fun t => (radon n (d.symbol v) (modulus F v) dx f t).1 s y) u.val =
      (Real.sqrt (modulus F v (n : LocalField F v)) : ℂ) * (modulus F v u.val : ℂ)^(n-1) *
        (d.integralTransform v f).1 (u^n*s) (u.val^n*y) := by
  have hn : (n : LocalField F v) ≠ 0 := by
    have h := (diagonal F v).injective.ne (Nat.cast_ne_zero.mpr (NeZero.ne n) : (n : F) ≠ 0)
    simpa only [map_natCast,map_zero] using h
  have hpos : 0 < modulus F v (n : LocalField F v) := by cases v <;> simp [modulus,norm_pos_iff,hn,pow_pos]
  have hk := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos_of_pos hpos).ne'
  have h := (d.transform_pow_ray v f u).1 s y
  dsimp only at h ⊢
  rw [mul_assoc,h,← mul_assoc,mul_inv_cancel₀ hk,one_mul]
  rfl

theorem hat_radon_scaled (v : Place F) (Φ : d.schwartz v) (s u : (LocalField F v)ˣ) (y : LocalField F v) :
    let dx := selfDual F d.character v
    d.hat v (fun t => (radon n (d.symbol v) (modulus F v) dx Φ.val t).1 s y) u.val =
      (Real.sqrt (modulus F v (n : LocalField F v)) : ℂ) * (modulus F v u.val : ℂ)^(n-1) *
        (d.fourier v Φ).val.1 (u^n*s) (u.val^n*y) := by
  rw [d.fourier_apply]
  exact d.hat_radon_scaled_charts v Φ.val s u y

/-- The first identity in the proof of the axis-to-marginal lemma, after
changing the marginal variable by the n-th power of the frequency. -/
theorem marginal_scaled_radon_of_charts (v : Place F) (Φ Ψ : d.schwartz v)
    (hΨ : Ψ.val = d.integralTransform v Φ.val) (s u : (LocalField F v)ˣ) :
    let dx := selfDual F d.character v
    (Real.sqrt (modulus F v (n : LocalField F v)) : ℂ) * d.marginal v Ψ (u^n*s) =
      (modulus F v u.val : ℂ) * ∫ y,
        d.hat v (fun t => (radon n (d.symbol v) (modulus F v) dx Φ.val t).1 s y) u.val ∂dx := by
  dsimp only
  simp_rw [d.hat_radon_scaled_charts v Φ.val s u,← hΨ,integral_const_mul]
  have h := d.integral_local_mul v (u^n) (Ψ.val.1 (u^n*s))
  simp only [Units.val_pow_eq_pow_val] at h
  have hm : modulus F v (u.val^n) = (modulus F v u.val)^n := by
    cases v <;> simp [modulus,norm_pow,pow_right_comm]
  rw [h,hm,Complex.ofReal_pow,marginal]
  have hpos := NeZero.pos n
  have hpow (z : ℂ) : z * z^(n-1) = z^n := by
    rw [← pow_succ',Nat.sub_add_cancel hpos]
  have hne := Complex.ofReal_ne_zero.mpr (modulus_ne_zero v u)
  field_simp
  linear_combination (Real.sqrt (modulus F v (n : LocalField F v)) : ℂ) *
    (∫ y, Ψ.val.1 (u^n*s) y ∂(selfDual F d.character v)) * (hpow (modulus F v u.val)).symm

theorem marginal_scaled_radon (v : Place F) (Φ : d.schwartz v) (s u : (LocalField F v)ˣ) :
    let dx := selfDual F d.character v
    (Real.sqrt (modulus F v (n : LocalField F v)) : ℂ) * d.marginal v (d.fourier v Φ) (u^n*s) =
      (modulus F v u.val : ℂ) * ∫ y,
        d.hat v (fun t => (radon n (d.symbol v) (modulus F v) dx Φ.val t).1 s y) u.val ∂dx :=
  d.marginal_scaled_radon_of_charts v Φ _ (d.fourier_apply v Φ) s u

private theorem compact_frequency_set {K : Type*} [NormedField K] {ρ : K → ℂ}
    (hl : IsLocallyConstant ρ) (hk : HasCompactSupport ρ) (h₀ : ρ 0 = 0) :
    IsCompact ((Units.val : Kˣ → K) ⁻¹' tsupport ρ) := by
  apply Units.isEmbedding_val₀.isInducing.isCompact_preimage' hk
  intro x hx
  have hz : (0 : K) ∉ tsupport ρ := notMem_tsupport_iff_eventuallyEq.mpr (by
    filter_upwards [hl.eventually_eq 0] with t ht
    exact ht.trans h₀)
  exact ⟨Units.mk0 x (fun he => hz (he ▸ hx)),rfl⟩

/-- Absolute convergence for the first exchange of integrals in Appendix A.
The frequencies range over a compact subset of the units. The support of the
transformed section bounds the rescaled transverse coordinate uniformly. -/
private theorem finite_tested_radon_integrable (p : HeightOneSpectrum (𝓞 F)) (Φ : d.schwartz (.inr p))
    (Ψ : d.schwartz (.inr p)) (hΨ : Ψ.val = d.integralTransform (.inr p) Φ.val)
    (s : (LocalField F (.inr p))ˣ) {ρ : LocalField F (.inr p) → ℂ} (hρ : Bruhat (.inr p) ρ) (h₀ : ρ 0 = 0) :
    let v : Place F := .inr p
    let dx := selfDual F d.character v
    let R := radon n (d.symbol v) (modulus F v) dx Φ.val
    Integrable (fun z : (LocalField F v)ˣ × LocalField F v =>
      modulus F v z.1.val • (ρ z.1.val * d.hat v (fun t => (R t).1 s z.2) z.1.val)) ((d.lineMeasure v).prod dx) := by
  let v : Place F := .inr p
  let K := LocalField F v
  let dx := selfDual F d.character v
  letI : dx.IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  letI : NontriviallyNormedField (p.adicCompletion F) := FinitePlace.nontriviallyNormedCompletion p
  letI : ProperSpace K := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace (p.adicCompletion F)
  let k : ℂ := Real.sqrt (modulus F v (n : K))
  let G (z : Kˣ × K) := ‖z.1.val‖ • (ρ z.1.val * (k * (‖z.1.val‖ : ℂ)^(n-1) * Ψ.val.1 (z.1^n*s) (z.1.val^n*z.2)))
  dsimp only
  simp_rw [d.hat_radon_scaled_charts,← hΨ]
  change Integrable G ((d.lineMeasure v).prod dx)
  apply Continuous.integrable_of_hasCompactSupport
  · have hc := (d.locallyConstant_finite_schwartz p Ψ).1.continuous
    have hu : Continuous (fun z : Kˣ × K => z.1.val) := Units.continuous_val.comp continuous_fst
    apply hu.norm.smul ((hρ.1.continuous.comp hu).mul ?_)
    exact (continuous_const.mul ((Complex.continuous_ofReal.comp hu.norm).pow _)).mul
      (hc.comp (((continuous_fst.pow _).mul continuous_const).prodMk ((hu.pow _).mul continuous_snd)))
  · let U := (Units.val : Kˣ → K) ⁻¹' tsupport ρ
    have hU : IsCompact U := compact_frequency_set hρ.1 hρ.2 h₀
    obtain ⟨L,hL⟩ := d.exists_leading_finite p
    obtain ⟨B,hB,hout⟩ := (d.finite_support_and_germ_of_isLeadingTerm p Ψ (hL Ψ)).1
    let back (z : Kˣ × K) := (z.1,z.2 / z.1.val^n)
    have hc : Continuous back := continuous_fst.prodMk (continuous_snd.div
      ((Units.continuous_val.comp continuous_fst).pow n) (fun z => pow_ne_zero _ z.1.ne_zero))
    apply HasCompactSupport.intro ((hU.prod (hB.image continuous_snd)).image hc)
    intro z hz
    by_cases hu : z.1 ∈ U
    · have hB' : ((z.1^n*s).val,z.1.val^n*z.2) ∉ B := by
        intro hin
        apply hz
        refine ⟨(z.1,z.1.val^n*z.2),⟨hu,⟨_,hin,rfl⟩⟩,?_⟩
        simp [back,pow_ne_zero n z.1.ne_zero]
      have hval := (hout _ hB').1
      simp only [xChart,dif_pos (z.1^n*s).ne_zero,Units.mk0_val] at hval
      simp [G,hval]
    · have hval := image_eq_zero_of_notMem_tsupport (f := ρ) hu
      simp [G,hval]

private theorem finite_family_slice {P K : Type*} [TopologicalSpace P] [NormedField K]
    {g : P → K → ℂ} (hg : SmoothFiniteFamily g) (q : P) :
    IsLocallyConstant (g q) ∧ HasCompactSupport (g q) := by
  obtain ⟨C,hC,hout⟩ := (hg.2 {q} isCompact_singleton).2.1
  exact ⟨hg.1.comp_continuous ((continuous_const (y := q)).prodMk (continuous_id (X := K))),
    HasCompactSupport.intro hC (hout q (mem_singleton _))⟩

/-- The tested marginal formula before passing to the multiplicative difference
integral. Both Fourier integrations here use additive self-dual measure. -/
theorem finite_tested_marginal_on_test (p : HeightOneSpectrum (𝓞 F)) (Φ : d.schwartz (.inr p))
    (hΦ : Φ.val ∈ d.testSet (.inr p)) (s : (LocalField F (.inr p))ˣ)
    {ρ : LocalField F (.inr p) → ℂ} (hρ : Bruhat (.inr p) ρ) (h₀ : ρ 0 = 0) :
    let v : Place F := .inr p
    let dx := selfDual F d.character v
    let R := radon n (d.symbol v) (modulus F v) dx Φ.val
    (Real.sqrt (modulus F v (n : LocalField F v)) : ℂ) *
      d.lineIntegral v (fun u => d.marginal v (d.transformTest v Φ hΦ) (u^n*s) * ρ u.val) =
      ∫ y, ∫ t, d.hat v ρ t * (R t).1 s y ∂dx ∂dx := by
  let v : Place F := .inr p
  let dx := selfDual F d.character v
  letI : dx.IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  letI : NontriviallyNormedField (p.adicCompletion F) := FinitePlace.nontriviallyNormedCompletion p
  letI : ProperSpace (LocalField F v) := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace (p.adicCompletion F)
  let R := radon n (d.symbol v) (modulus F v) dx Φ.val
  let G (u : (LocalField F v)ˣ) (y : LocalField F v) :=
    modulus F v u.val • (ρ u.val * d.hat v (fun t => (R t).1 s y) u.val)
  have hi : Integrable (Function.uncurry G) ((d.lineMeasure v).prod dx) := d.finite_tested_radon_integrable p Φ (d.transformTest v Φ hΦ) rfl s hρ h₀
  dsimp only
  rw [← d.integral_lineMeasure,← integral_const_mul]
  refine Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun u => ?_))
    ((integral_integral_swap hi).trans ?_)
  · simp only [G,Complex.real_smul,integral_const_mul]
    rw [← mul_assoc,d.marginal_scaled_radon_of_charts v Φ (d.transformTest v Φ hΦ) rfl]
    ring
  · apply integral_congr_ae
    filter_upwards with y
    let r (t : LocalField F v) := (R t).1 s y
    have fam := (d.smooth_finiteTest_lines p hΦ).1
    have hr : Bruhat v r := finite_family_slice fam (s,y)
    have he := (d.lineMeasure_modulus v (fun x => ρ x * d.hat v r x)).2
    refine he.trans ?_
    have h := d.finite_linearFactor_pairing p hr hρ 0 1
    simpa only [Units.val_one,sub_zero,mul_one,div_one,mul_zero,Character.localValue_zero,
      modulus,norm_one,Complex.ofReal_one] using h.symm

theorem finite_tested_marginal (p : HeightOneSpectrum (𝓞 F)) (Φ : d.schwartz (.inr p))
    (hΦ : Φ.val ∈ d.testSet (.inr p)) (s : (LocalField F (.inr p))ˣ)
    {ρ : LocalField F (.inr p) → ℂ} (hρ : Bruhat (.inr p) ρ) (h₀ : ρ 0 = 0) :
    let v : Place F := .inr p
    let dx := selfDual F d.character v
    let R := radon n (d.symbol v) (modulus F v) dx Φ.val
    (Real.sqrt (modulus F v (n : LocalField F v)) : ℂ) *
      d.lineIntegral v (fun u => d.marginal v (d.fourier v Φ) (u^n*s) * ρ u.val) =
      ∫ y, ∫ t, d.hat v ρ t * (R t).1 s y ∂dx ∂dx := by
  simpa only [d.transformTest_eq_fourier] using d.finite_tested_marginal_on_test p Φ hΦ s hρ h₀

/-- The Y-chart integrand after the substitution u = 1/y'. The deleted line
y = 0 has additive measure zero. -/
def marginalSlice (v : Place F) (f : Charts (LocalField F v)) (s u : (LocalField F v)ˣ)
    (t y : LocalField F v) : ℂ :=
  if hy : y ≠ 0 then d.symbol v u (-(s*Units.mk0 y hy)) * f.2 ((t^n+s.val*y)*u.val) (Units.mk0 y hy) else 0

/-- Rewriting the tested Radon integral in the reciprocal variable replaces
dy' by d×u and moves the Jacobian from the line integral into the measure. -/
theorem tested_radon_reciprocal (v : Place F) {f : Charts (LocalField F v)} (hf : Glues (d.symbol v) f)
    (s : (LocalField F v)ˣ) (h : LocalField F v → ℂ) :
    let dx := selfDual F d.character v
    let R := radon n (d.symbol v) (modulus F v) dx f
    (∫ z, ∫ t, h t * (R t).1 s z ∂dx ∂dx) =
      d.lineIntegral v (fun u => ∫ t, h t * (∫ y, d.marginalSlice v f s u t y ∂dx) ∂dx) := by
  let dx := selfDual F d.character v
  let R := radon n (d.symbol v) (modulus F v) dx f
  let A (z : LocalField F v) := ∫ t, h t * (R t).1 s z ∂dx
  have he := (d.lineMeasure_modulus v A).2
  have hInv := d.lineIntegral_inv v (fun u => modulus F v u.val • A u.val)
  dsimp only
  refine he.symm.trans ((d.integral_lineMeasure _ _).trans (hInv.symm.trans ?_))
  congr 1
  funext u
  let m : ℂ := modulus F v u⁻¹.val
  have hm : m ≠ 0 := Complex.ofReal_ne_zero.mpr (modulus_ne_zero v u⁻¹)
  change m * A u⁻¹.val = _
  dsimp only [A]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  rw [show (R t).1 s u⁻¹.val = _ from d.radon_X_via_Y v hf s u⁻¹ t]
  have cancel (z : ℂ) : m * (h t * (z/m)) = h t * z := by field_simp
  rw [cancel]
  congr 1
  apply integral_congr_ae
  filter_upwards with y
  by_cases hy : y = 0
  · simp [hy,marginalSlice]
  · let Y := Units.mk0 y hy
    have hsym : d.symbol v (-(s*Y)) u⁻¹ = d.symbol v u (-(s*Y)) := by
      let H := d.lineSymbol v (by cases v with
        | inl w => exact d.arch_steinberg w
        | inr p => exact d.finite_steinberg p)
      change (H.pairing (-(s*Y)) u⁻¹).val = (H.pairing u (-(s*Y))).val
      rw [map_inv,← H.skew]
    simp only [marginalSlice,dif_pos hy,Units.val_inv_eq_inv_val,div_inv_eq_mul]
    rw [hsym,mul_comm]

/-- A test section's Fourier marginal paired with ρ, expressed using its
original Y chart and the multiplicative measure of Appendix A. -/
theorem finite_tested_marginal_slice_on_test (p : HeightOneSpectrum (𝓞 F)) (Φ : d.schwartz (.inr p))
    (hΦ : Φ.val ∈ d.testSet (.inr p)) (s : (LocalField F (.inr p))ˣ)
    {ρ : LocalField F (.inr p) → ℂ} (hρ : Bruhat (.inr p) ρ) (h₀ : ρ 0 = 0) :
    let v : Place F := .inr p
    let dx := selfDual F d.character v
    (Real.sqrt (modulus F v (n : LocalField F v)) : ℂ) *
      d.lineIntegral v (fun u => d.marginal v (d.transformTest v Φ hΦ) (u^n*s) * ρ u.val) =
      d.lineIntegral v (fun u => ∫ t, d.hat v ρ t * (∫ y, d.marginalSlice v Φ.val s u t y ∂dx) ∂dx) :=
  (d.finite_tested_marginal_on_test p Φ hΦ s hρ h₀).trans (d.tested_radon_reciprocal _ hΦ.1 s _)

theorem finite_tested_marginal_slice (p : HeightOneSpectrum (𝓞 F)) (Φ : d.schwartz (.inr p))
    (hΦ : Φ.val ∈ d.testSet (.inr p)) (s : (LocalField F (.inr p))ˣ)
    {ρ : LocalField F (.inr p) → ℂ} (hρ : Bruhat (.inr p) ρ) (h₀ : ρ 0 = 0) :
    let v : Place F := .inr p
    let dx := selfDual F d.character v
    (Real.sqrt (modulus F v (n : LocalField F v)) : ℂ) *
      d.lineIntegral v (fun u => d.marginal v (d.fourier v Φ) (u^n*s) * ρ u.val) =
      d.lineIntegral v (fun u => ∫ t, d.hat v ρ t * (∫ y, d.marginalSlice v Φ.val s u t y ∂dx) ∂dx) := by
  simpa only [d.transformTest_eq_fourier] using d.finite_tested_marginal_slice_on_test p Φ hΦ s hρ h₀

end MetaplecticPoisson.Datum
