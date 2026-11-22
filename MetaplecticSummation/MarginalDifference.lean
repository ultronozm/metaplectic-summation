import MetaplecticSummation.Marginals
import MetaplecticSummation.Jacquet.Local

/-! The multiplicative difference integral in the converse marginal identity of Appendix A. -/

noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField MeasureTheory Filter
open scoped Topology
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

/-- The density of a weight with respect to additive self-dual measure. -/
private def lineDensity (v : Place F) (W : Weight v) (z : LocalField F v) : ℂ :=
  if hz : z ≠ 0 then W (Units.mk0 z hz) / (modulus F v z : ℂ) else 0

def LineIntegrable (v : Place F) (W : Weight v) : Prop :=
  Integrable (lineDensity v W) (selfDual F d.character v)

omit [NeZero n] in
private theorem lineIntegral_sub (v : Place F) {W V : Weight v} (hW : d.LineIntegrable v W)
    (hV : d.LineIntegrable v V) : d.lineIntegral v (W-V) = d.lineIntegral v W - d.lineIntegral v V := by
  change _ = (∫ z, lineDensity v W z ∂(selfDual F d.character v)) -
    ∫ z, lineDensity v V z ∂(selfDual F d.character v)
  rw [← integral_sub hW hV]
  unfold lineIntegral
  apply integral_congr_ae
  filter_upwards with z
  by_cases hz : z ≠ 0 <;> simp [lineDensity,hz,sub_div]

/-- The integrand defining Lᵧ(b) with the second Hilbert-symbol argument a = −sy. -/
def marginalDifference (v : Place F) (f : LocalField F v → ℂ) (a b : (LocalField F v)ˣ) : Weight v :=
  fun z => d.symbol v z a * (f (b*z).val - f z.val)

/-- A finite-place Schwartz–Bruhat test has integrable multiplicative differences.
The subtraction removes the singularity of the multiplicative measure at zero. -/
theorem marginalDifference_finite_integrable (p : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    {f : LocalField F (.inr p) → ℂ} (hf : Bruhat (.inr p) f) (a b : (LocalField F (.inr p))ˣ) :
    d.LineIntegrable (.inr p) (d.marginalDifference (.inr p) f a b) := by
  let v : Place F := .inr p
  let K := LocalField F v
  let dx := selfDual F d.character v
  letI : dx.IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  obtain ⟨hl,hk⟩ : IsLocallyConstant f ∧ HasCompactSupport f := hf
  let g (z : K) := f (b.val*z) - f z
  let factor (z : K) : ℂ := if hz : z ≠ 0 then d.symbol v (Units.mk0 z hz) a / (‖z‖ : ℂ) else 0
  have eqn : lineDensity v (d.marginalDifference v f a b) = factor * g := by
    funext z
    by_cases hz : z ≠ 0 <;> simp [lineDensity,marginalDifference,factor,g,hz,v,modulus,mul_div_right_comm]
  have hg : HasCompactSupport g := (hk.comp_smul b.ne_zero).sub hk
  have hcg : Continuous g := (hl.continuous.comp (continuous_const.mul continuous_id)).sub hl.continuous
  change Integrable (lineDensity v (d.marginalDifference v f a b)) dx
  rw [eqn]
  apply Continuous.integrable_of_hasCompactSupport _ hg.mul_left
  apply continuous_iff_continuousAt.mpr
  intro z
  by_cases hz : z = 0
  · subst z
    have ht := (hl.comp_continuous (continuous_const.mul continuous_id : Continuous (fun z : K => b.val*z))).eventually_eq 0
    apply (continuousAt_const (y := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [ht,hl.eventually_eq 0] with z h₁ h₂
    change f (b.val*z) = f (b.val*0) at h₁
    rw [mul_zero] at h₁
    change f z = f 0 at h₂
    simp [g,h₁,h₂]
  · let U (z : K) := if hz : z = 0 then 1 else Units.mk0 z hz
    have hu : ContinuousAt U z := by
      apply Units.isEmbedding_val₀.tendsto_nhds_iff.mpr
      simp only [U,hz]
      exact tendsto_id.congr' ((eventually_ne_nhds hz).mono fun _ hu => by simp [hu])
    have hsym : ContinuousAt (fun w => d.symbol v (U w) a) z := (d.continuous_symbol v).continuousAt.comp (hu.prodMk continuousAt_const)
    have hfac : ContinuousAt factor z := by
      apply (hsym.div (Complex.continuous_ofReal.continuousAt.comp continuous_norm.continuousAt)
        (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz))).congr_of_eventuallyEq
      filter_upwards [eventually_ne_nhds hz] with w hw
      simp [factor,U,hw]
    exact hfac.mul hcg.continuousAt

/-- The cocycle identity, multiplied by the nonzero factor η(c). -/
theorem marginalDifference_cocycle (v : Place F) (f : LocalField F v → ℂ) (a b c : (LocalField F v)ˣ)
    (hbc : d.LineIntegrable v (d.marginalDifference v f a (b*c)))
    (hc : d.LineIntegrable v (d.marginalDifference v f a c)) :
    let L := fun w => d.lineIntegral v (d.marginalDifference v f a w)
    d.symbol v c a * (L (b*c) - L c) = L b := by
  dsimp only
  rw [← d.lineIntegral_sub v hbc hc,← d.lineIntegral_const_mul]
  have he (z : (LocalField F v)ˣ) : d.symbol v c a *
      ((d.marginalDifference v f a (b*c) - d.marginalDifference v f a c) z) =
      d.marginalDifference v f a b (c*z) := by
    have hs : d.symbol v (c*z) a = d.symbol v c a * d.symbol v z a := by
      change ((d.unitPairing v (c*z) a).val) = _
      rw [map_mul,MonoidHom.mul_apply,Units.val_mul]
      rfl
    simp only [marginalDifference,Pi.sub_apply,hs,mul_assoc b c z]
    ring
  simp_rw [he]
  exact d.lineIntegral_mul v c _

/-- In the nontrivial character case the difference integral vanishes on
b = τⁿ − a. This is the Steinberg cancellation before the sum over roots. -/
theorem marginalDifference_vanishes (v : Place F) (f : LocalField F v → ℂ) (a b : (LocalField F v)ˣ)
    (hi : ∀ c, d.LineIntegrable v (d.marginalDifference v f a c))
    (hχ : ∃ c, d.symbol v c a ≠ 1) (t : LocalField F v) (ht : b.val + a.val = t^n) :
    d.lineIntegral v (d.marginalDifference v f a b) = 0 := by
  let H := d.lineSymbol v (by cases v with
    | inl w => exact d.arch_steinberg w
    | inr p => exact d.finite_steinberg p)
  have hb : d.symbol v b a = 1 := congrArg Units.val (H.of_sum_eq_pow (NeZero.ne n) b a t ht)
  obtain ⟨c,hc⟩ := hχ
  have h₁ := d.marginalDifference_cocycle v f a b c (hi _) (hi _)
  have h₂ := d.marginalDifference_cocycle v f a c b (hi _) (hi _)
  dsimp only at h₁ h₂
  rw [hb,one_mul,mul_comm c b] at h₂
  rw [sub_eq_iff_eq_add.mp h₂,add_sub_cancel_left] at h₁
  exact by_contra fun hn => hc ((mul_eq_right₀ hn).mp h₁)

/-- The Y-chart slice occurring in the tested marginal identity is a finite-place
Schwartz–Bruhat test. -/
theorem finiteTest_axisSlice (p : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    {Φ : Charts (LocalField F (.inr p))} (hΦ : Φ ∈ d.testSet (.inr p)) (y : (LocalField F (.inr p))ˣ) :
    Bruhat (.inr p) (fun z => Φ.2 z y) := by
  obtain ⟨_,hl,C,hC,_,ho⟩ : finiteTest Φ := hΦ.2
  refine ⟨hl.comp_continuous (continuous_id.prodMk continuous_const),
    HasCompactSupport.intro (hC.image continuous_fst) ?_⟩
  intro z hz
  have h := (ho (z,y.val) (fun hy => hz ⟨_,hy,rfl⟩)).2
  simpa only [yChart,dif_pos y.ne_zero,Units.mk0_val] using h

/-- Cancellation in the nontrivial-character case of Appendix A for finite-place test sections. -/
theorem finiteTest_marginalDifference_vanishes (p : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    {Φ : Charts (LocalField F (.inr p))} (hΦ : Φ ∈ d.testSet (.inr p))
    (s y b : (LocalField F (.inr p))ˣ) (t : LocalField F (.inr p))
    (hb : b.val = t^n + s.val*y.val) (hχ : ∃ c, d.symbol (.inr p) c (-(s*y)) ≠ 1) :
    d.lineIntegral (.inr p) (d.marginalDifference (.inr p) (fun z => Φ.2 z y) (-(s*y)) b) = 0 := by
  apply d.marginalDifference_vanishes _ _ _ _ (fun c =>
    d.marginalDifference_finite_integrable p (d.finiteTest_axisSlice p hΦ y) _ c) hχ t
  rw [hb,Units.val_neg,Units.val_mul,add_neg_cancel_right]

end MetaplecticPoisson.Datum
