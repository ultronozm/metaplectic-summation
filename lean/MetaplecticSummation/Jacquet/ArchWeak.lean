import MetaplecticSummation.Jacquet.Weak
import MetaplecticSummation.Jacquet.ShearRegion
import MetaplecticSummation.Jacquet.ArchShearBound

/-! Testing the weak Jacquet identity away from zero at an infinite place. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField MeasureTheory Filter Set
open scoped ContDiff
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n) (w : InfinitePlace F)
local notation "v" => (Sum.inl w : Place F)
local notation "K" => LocalField F v
local notation "dx" => selfDual F d.character v

omit [NeZero n] in
/-- Smooth tests compactly supported in the punctured completion determine the
value at one of a function continuous away from zero. -/
private theorem arch_separate_at_one_coordinates {E : Type} [NormedField E] [NormedAlgebra ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (e : w.Completion ≃+* E) (he : Isometry e)
    (hb : ∀ g : SchwartzMap E ℂ, Bruhat v (fun x => g (e x)))
    {f : K → ℂ} (hf : ContinuousOn f {0}ᶜ)
    (ht : ∀ ρ : K → ℂ, Bruhat v ρ → Continuous ρ → HasCompactSupport ρ → 0 ∉ tsupport ρ →
      (∫ x, f x * ρ x ∂dx) = 0) : f 1 = 0 := by
  letI : (dx).IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  let i : K ≃ᵢ E := ⟨e.toEquiv,he⟩
  let ν := (dx).map i
  letI : ν.IsAddHaarMeasure := e.toAddEquiv.isAddHaarMeasure_map dx he.continuous i.symm.continuous
  let U : Set E := {0}ᶜ
  have hU : IsOpen U := isClosed_singleton.isOpen_compl
  have cf : ContinuousOn (f ∘ i.symm) U :=
    hf.comp i.symm.continuous.continuousOn (fun z hz => (map_ne_zero e.symm).mpr hz)
  have ae := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := ν)
    (cf.locallyIntegrableOn hU.measurableSet) (by
      intro φ hd hk hsup
      let φc (z : E) : ℂ := φ z
      have hdc : ContDiff ℝ ∞ φc := Complex.ofRealCLM.contDiff.comp hd
      have hkc : HasCompactSupport φc := hk.comp_left Complex.ofReal_zero
      let ρ (x : K) := φc (e x)
      have hρ : Bruhat v ρ := hb (hkc.toSchwartzMap hdc)
      have sub : tsupport ρ ⊆ e ⁻¹' tsupport φ := closure_minimal (fun x hx =>
        subset_tsupport φ (fun h => hx (by simp [ρ,φc,h]))) ((isClosed_tsupport φ).preimage he.continuous)
      have hz : 0 ∉ tsupport ρ := fun h => (show e 0 ≠ 0 from hsup (sub h)) e.map_zero
      have eqn := ht ρ hρ (hdc.continuous.comp he.continuous) (hkc.comp_homeomorph i.toHomeomorph) hz
      rw [show ν = (dx).map i.toHomeomorph.toMeasurableEquiv from rfl,integral_map_equiv]
      apply Eq.trans _ eqn
      apply integral_congr_ae
      filter_upwards with x
      change φ (i x) • f (i.symm (i x)) = f x * (φ (i x) : ℂ)
      rw [i.symm_apply_apply,Complex.real_smul,mul_comm])
  have h := Measure.eqOn_open_of_ae_eq ((ae_restrict_iff' hU.measurableSet).mpr ae) hU cf
    (continuousOn_const (c := (0 : ℂ)))
  simpa only [Function.comp_apply,show i.symm (1:E) = (1:K) from e.symm.map_one] using h (show (1:E) ∈ U from one_ne_zero)

omit [NeZero n] in
private theorem arch_test_at_one {A : Kˣ → ℂ} {g : K → ℂ} (hA : Continuous A) (hg : Continuous g)
    (h : ∀ ρ : K → ℂ, Bruhat v ρ → Continuous ρ → HasCompactSupport ρ → 0 ∉ tsupport ρ →
      d.lineIntegral v (fun u => A u * ρ u.val) = ∫ x, g x * ρ x ∂dx) :
    A 1 = g 1 := by
  letI : NontriviallyNormedField K := archNontriviallyNormedCompletion w
  letI : (dx).IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  let f (x : K) := A (liftUnit x) / (modulus F v x : ℂ)
  have cf : ContinuousOn f {0}ᶜ := by
    intro x hx
    have hn : x ≠ 0 := hx
    exact ((hA.continuousAt.comp (liftUnit_continuousAt hn)).div
      ((Complex.continuous_ofReal.comp (continuous_norm.pow w.mult)).continuousAt)
      (Complex.ofReal_ne_zero.mpr (pow_ne_zero _ (norm_ne_zero_iff.mpr hn)))).continuousWithinAt
  have tests (ρ : K → ℂ) (hρ : Bruhat v ρ) (hc : Continuous ρ) (hs : HasCompactSupport ρ)
      (hz : 0 ∉ tsupport ρ) : (∫ x, (f x - g x)*ρ x ∂dx) = 0 := by
    letI : NullSingletonClass dx := d.selfDual_nullSingleton v
    have si : Integrable (fun x => f x * ρ x) dx := by
      have cc := (cf.mono (show tsupport ρ ⊆ {0}ᶜ from fun x hx he => hz (he ▸ hx))).mul hc.continuousOn
      exact (cc.integrableOn_compact hs).integrable_of_forall_notMem_eq_zero
        (fun x hx => by rw [Pi.mul_apply,image_eq_zero_of_notMem_tsupport hx,mul_zero])
    have gi : Integrable (fun x => g x * ρ x) dx := (hg.mul hc).integrable_of_hasCompactSupport hs.mul_left
    simp_rw [sub_mul,integral_sub si gi,sub_eq_zero]
    exact Eq.trans (by
      apply integral_congr_ae
      filter_upwards [(dx).ae_ne 0] with x hx
      have hn : x ≠ 0 := hx
      change A (liftUnit x) / _ * ρ x = (if h : x ≠ 0 then A (Units.mk0 x h) * ρ x / _ else 0)
      rw [dif_pos hn,show liftUnit x = Units.mk0 x hn from Units.ext (liftUnit_val hn)]
      ring) (h ρ hρ hc hs hz)
  have zero : (f 1 - g 1) = 0 := by
    by_cases hr : w.IsReal
    · let e := InfinitePlace.Completion.ringEquivRealOfIsReal hr
      exact d.arch_separate_at_one_coordinates w e (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hr)
        (fun k => by simpa only [Bruhat,dif_pos hr] using (show ∃ f : SchwartzMap ℝ ℂ, ∀ x : K, k (e x) = f (e x)
          from ⟨k,fun _ => rfl⟩)) (cf.sub hg.continuousOn) tests
    · let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex (InfinitePlace.not_isReal_iff_isComplex.mp hr)
      exact d.arch_separate_at_one_coordinates w e (InfinitePlace.Completion.isometry_extensionEmbedding w)
        (fun k => by simpa only [Bruhat,dif_neg hr] using (show ∃ f : SchwartzMap ℂ ℂ, ∀ x : K, k (e x) = f (e x)
          from ⟨k,fun _ => rfl⟩)) (cf.sub hg.continuousOn) tests
  have unit : liftUnit (1:K) = 1 := Units.ext (liftUnit_val (one_ne_zero : (1:K) ≠ 0))
  simpa only [f,unit,modulus,norm_one,one_pow,Complex.ofReal_one,div_one,sub_eq_zero] using zero

/-- Pointwise Jacquet transformation at an infinite place for any section
whose X-chart is absolutely integrable for d×x dy and whose weight is a test. -/
theorem arch_jacquet_fourier_of_integrable_chart (Φ : d.schwartz v)
    (hw : TestWeight v (d.jacquet v Φ)) (hi : Integrable (Function.uncurry Φ.val.1) ((d.lineMeasure v).prod dx)) :
    d.jacquet v (d.fourier v Φ) = d.dualWeight v (d.jacquet v Φ) := by
  letI : (dx).IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  funext c
  let W := d.jacquet v Φ
  let H := d.kernelIntegral v W c
  let s : ℂ := (Real.sqrt (modulus F v (n:K)) : ℂ)⁻¹
  let A (u : Kˣ) := d.jacquet v (d.fourier v Φ) (u^n*c)
  have hH : Integrable H dx := Bruhat.integrable d (d.kernelIntegral_bruhat v hw c)
  have cH : Continuous H := (d.kernelIntegral_estimates v (d.testWeight_integrable v hw) c).1
  have h := d.arch_test_at_one w (A := A) (g := fun x => s*d.hat v H x)
    ((d.continuous_jacquet v _).comp ((continuous_id.pow n).mul_const c))
    (continuous_const.mul (d.continuous_hat v hH)) (by
      intro ρ hρ hc hs hz
      have htest := d.jacquet_weak_of_lines v Φ c (d.jacquet_radon_lines v Φ hi c) hc hs hz
        (Bruhat.integrable d (d.arch_hat_bruhat w hρ))
      have hswap := d.hat_pair_swap v cH hc hH (Bruhat.integrable d hρ)
      change d.lineIntegral v (fun u => A u * ρ u.val) = s*(∫ t, H t*d.hat v ρ t ∂dx) at htest
      rw [htest,← hswap]
      simp only [mul_assoc,integral_const_mul])
  simpa only [A,H,W,one_pow,one_mul,s,hat,dualWeight,mul_comm (d.kernelIntegral v _ c _) _] using h

/-- The explicit Jacquet lift has the prescribed transformed weight for
every choice of normalized auxiliary function. -/
theorem jacquetLift_dual (v₀ : Place F) {W : Weight v₀} (hw : TestWeight v₀ W)
    {β : LocalField F v₀ → ℂ} (hβ : d.IsJacquetLiftAuxiliary v₀ β) :
    let Φ : d.schwartz v₀ := ⟨d.jacquetLift v₀ W β,Submodule.subset_span (Or.inl (hβ.2 W hw))⟩
    d.jacquet v₀ (d.fourier v₀ Φ) = d.dualWeight v₀ W := by
  intro Φ
  have hJ : d.jacquet v₀ Φ = W := d.jacquet_jacquetLift v₀ W β hβ.1 (hβ.2 W hw)
  have hi : Integrable (Function.uncurry Φ.val.1) ((d.lineMeasure v₀).prod (selfDual F d.character v₀)) :=
    d.integrable_jacquetLift_chart v₀ hw β (hβ.2 W hw)
  refine Eq.trans ?_ (congrArg (d.dualWeight v₀) hJ)
  have htest : TestWeight v₀ (d.jacquet v₀ Φ) := hJ ▸ hw
  cases v₀ with
  | inl w => exact d.arch_jacquet_fourier_of_integrable_chart w Φ htest hi
  | inr p => exact d.finite_jacquet_fourier_test p Φ htest

/-- Every compactly supported test weight has a test lift on which the
Jacquet transform is given by the explicit kernel, at all places. -/
theorem exists_jacquet_lift_dual (v₀ : Place F) {W : Weight v₀} (hw : TestWeight v₀ W) :
    ∃ Φ : d.schwartz v₀, Φ.val ∈ d.testSet v₀ ∧ d.jacquet v₀ Φ = W ∧
      d.jacquet v₀ (d.fourier v₀ Φ) = d.dualWeight v₀ W := by
  obtain ⟨β,hβ,ht⟩ := d.exists_jacquetLift_auxiliary v₀
  exact ⟨_,ht W hw,d.jacquet_jacquetLift v₀ W β hβ (ht W hw),
    d.jacquetLift_dual v₀ hw (β := β) ⟨hβ,ht⟩⟩

/-- The archimedean shear estimate in the vertical region, from the bound of
order three on the far part of the vertical cone. -/
theorem arch_integrableOn_shear_vertical (u : K) {g : d.Operators v} (hg : d.IsUpper v u g)
    (Φ : d.schwartz v) :
    let Ξ := (d.jacquetDifference v u g)^[3] Φ
    IntegrableOn (Function.uncurry Ξ.val.1)
      {z : Kˣ × K | modulus F v z.1.val < 1 ∧ ‖z.1.val‖ < ‖z.2‖} ((d.lineMeasure v).prod dx) := by
  obtain ⟨C₀,B,hB,h⟩ := d.shearVerticalBound_arch w u hg Φ
  exact d.integrableOn_vertical_of_bound v _ hB h

/-- Absolute integrability for the third archimedean shear difference. -/
theorem integrable_arch_shear (u : K) {g : d.Operators v} (hg : d.IsUpper v u g)
    (Φ : d.schwartz v) :
    let Ξ := (d.jacquetDifference v u g)^[3] Φ
    Integrable (Function.uncurry Ξ.val.1) ((d.lineMeasure v).prod dx) := by
  intro Ξ
  have hi := (d.integrableOn_X_outside_vertical_cone v Ξ).union
    (d.arch_integrableOn_shear_vertical w u hg Φ)
  apply integrableOn_univ.mp (hi.mono_set ?_)
  intro z _
  by_cases hx : 1 ≤ modulus F v z.1.val
  · exact Or.inl (Or.inl hx)
  by_cases hy : ‖z.2‖ ≤ ‖z.1.val‖
  · exact Or.inl (Or.inr hy)
  exact Or.inr ⟨lt_of_not_ge hx,lt_of_not_ge hy⟩

/-- A representative with integrable X-chart preserves both Jacquet weights. -/
theorem exists_integrable_jacquet_representative (v₀ : Place F) (Φ : d.schwartz v₀) :
    ∃ Ξ : d.schwartz v₀, d.jacquet v₀ Ξ = d.jacquet v₀ Φ ∧
      d.jacquet v₀ (d.fourier v₀ Ξ) = d.jacquet v₀ (d.fourier v₀ Φ) ∧
      Integrable (Function.uncurry Ξ.val.1) ((d.lineMeasure v₀).prod (selfDual F d.character v₀)) := by
  obtain ⟨u,hu⟩ := d.character.nontrivial_localValue v₀
  obtain ⟨g,hg⟩ := (d.exists_upper v₀ u).exists
  obtain ⟨hJ,hF⟩ := d.jacquet_difference_iterate v₀ u hu hg 3 Φ
  refine ⟨_,hJ,hF,?_⟩
  cases v₀ with
  | inl w => exact d.integrable_arch_shear w u hg Φ
  | inr p => exact d.integrable_finite_shear p u hg Φ

/-- Absolute integrability of every Jacquet weight for multiplicative Haar measure. -/
theorem integrable_jacquet_weight (v₀ : Place F) (Φ : d.schwartz v₀) :
    Integrable (d.jacquet v₀ Φ) (d.lineMeasure v₀) := by
  obtain ⟨Ξ,hJ,_,hΞ⟩ := d.exists_integrable_jacquet_representative v₀ Φ
  letI : (selfDual F d.character v₀).IsAddHaarMeasure :=
    (existsUnique_selfDual F d.character v₀).exists.choose_spec.1
  rw [← hJ]
  apply hΞ.integral_norm_prod_left.mono' (d.continuous_jacquet v₀ Ξ).aestronglyMeasurable
  filter_upwards with x
  apply (norm_integral_le_integral_norm _).trans
  simp only [norm_mul,d.character.norm_localValue,mul_one,Function.uncurry_apply_pair,le_refl]

/-- The weak Jacquet formula with smooth tests compactly supported away from zero. -/
theorem jacquet_weak (v₀ : Place F) (Φ : d.schwartz v₀) (c : (LocalField F v₀)ˣ)
    {ρ : LocalField F v₀ → ℂ} (hρ : Bruhat v₀ ρ) (hs : HasCompactSupport ρ) (hz : 0 ∉ tsupport ρ) :
    d.lineIntegral v₀ (fun u => d.jacquet v₀ (d.fourier v₀ Φ) (u^n*c) * ρ u.val) =
      (Real.sqrt (modulus F v₀ (n:LocalField F v₀)) : ℂ)⁻¹ *
        ∫ t, d.kernelIntegral v₀ (d.jacquet v₀ Φ) c t * d.hat v₀ ρ t ∂selfDual F d.character v₀ := by
  obtain ⟨Ξ,hJ,hF,hΞ⟩ := d.exists_integrable_jacquet_representative v₀ Φ
  have hc : Continuous ρ := by
    cases v₀ with
    | inr p => exact hρ.1.continuous
    | inl w =>
      dsimp only [Bruhat] at hρ
      split at hρ
      · obtain ⟨f,hf⟩ := hρ
        exact (f.continuous.comp (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal _).continuous).congr
          (fun x => (hf x).symm)
      · obtain ⟨f,hf⟩ := hρ
        exact (f.continuous.comp (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous).congr
          (fun x => (hf x).symm)
  have hi : Integrable (d.hat v₀ ρ) (selfDual F d.character v₀) := by
    apply Bruhat.integrable d
    cases v₀ with
    | inl w => exact d.arch_hat_bruhat w hρ
    | inr p => exact d.hat_finite_bruhat p hρ
  simpa only [hJ,hF] using d.jacquet_weak_of_lines v₀ Ξ c (d.jacquet_radon_lines v₀ Ξ hΞ c) hc hs hz hi

end MetaplecticPoisson.Datum
