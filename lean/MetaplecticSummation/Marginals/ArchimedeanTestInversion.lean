import MetaplecticSummation.Marginals.ArchimedeanRootSum
import MetaplecticSummation.Marginals.ArchimedeanPowerRoots
import MetaplecticSummation.Marginals.ArchimedeanTest

/-! Lemma A.2 at real and complex places. Pairing with smooth tests supported away
from zero, the tested root sum becomes the Fourier transform of the axis density after
the change of variables y = −rⁿ/s. The marginal and that transform are continuous on
the units, and smooth tests separate continuous functions there. -/

noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField MeasureTheory Set Filter
open scoped Topology ContDiff
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n) (w : InfinitePlace F)
local notation "v" => (Sum.inl w : Place F)
local notation "K" => LocalField F v
local notation "dx" => selfDual F d.character v

omit [NeZero n] in
/-- Smooth tests compactly supported in the punctured completion determine a
function continuous away from zero. -/
private theorem arch_separate_coordinates {E : Type} [NormedField E] [NormedAlgebra ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (e : w.Completion ≃+* E) (he : Isometry e)
    (hb : ∀ g : SchwartzMap E ℂ, Bruhat v (fun x => g (e x)))
    {f : K → ℂ} (hf : ContinuousOn f {0}ᶜ)
    (ht : ∀ ρ : K → ℂ, Bruhat v ρ → HasCompactSupport ρ → 0 ∉ tsupport ρ →
      (∫ x, f x * ρ x ∂dx) = 0) (x : K) (hx : x ≠ 0) : f x = 0 := by
  let : (dx).IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  let i : K ≃ᵢ E := ⟨e.toEquiv,he⟩
  let ν := (dx).map i
  let : ν.IsAddHaarMeasure := e.toAddEquiv.isAddHaarMeasure_map dx he.continuous i.symm.continuous
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
      have eqn := ht ρ hρ (hkc.comp_homeomorph i.toHomeomorph) hz
      rw [show ν = (dx).map i.toHomeomorph.toMeasurableEquiv from rfl,integral_map_equiv]
      apply Eq.trans _ eqn
      apply integral_congr_ae
      filter_upwards with x
      change φ (i x) • f (i.symm (i x)) = f x * (φ (i x) : ℂ)
      rw [i.symm_apply_apply,Complex.real_smul,mul_comm])
  have h := Measure.eqOn_open_of_ae_eq ((ae_restrict_iff' hU.measurableSet).mpr ae) hU cf
    (continuousOn_const (c := (0 : ℂ)))
  have hex : e x ∈ U := (map_ne_zero e).mpr hx
  simpa only [Function.comp_apply,show i.symm (e x) = x from e.symm_apply_apply x] using h hex

omit [NeZero n] in
/-- Two functions continuous on the units of an infinite completion agree if they
have the same multiplicative integrals against all smooth tests supported away from zero. -/
theorem arch_lineIntegral_separate {a b : Kˣ → ℂ} (ha : Continuous a) (hb : Continuous b)
    (h : ∀ ρ : K → ℂ, Bruhat v ρ → HasCompactSupport ρ → 0 ∉ tsupport ρ →
      d.lineIntegral v (fun u => a u * ρ u.val) = d.lineIntegral v (fun u => b u * ρ u.val)) :
    a = b := by
  let : NontriviallyNormedField K := archNontriviallyNormedCompletion w
  let : (dx).IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  let : NullSingletonClass dx := d.selfDual_nullSingleton v
  let m := modulus F v
  have hm (x : K) (hx : x ≠ 0) : 0 < m x := by simp [m,modulus,norm_pos_iff.mpr hx,pow_pos]
  let f (x : K) := (a (liftUnit x) - b (liftUnit x)) / (m x : ℂ)
  have cf : ContinuousOn f {0}ᶜ := by
    intro x hx
    have hn : x ≠ 0 := hx
    exact (((ha.continuousAt.comp (liftUnit_continuousAt hn)).sub (hb.continuousAt.comp
      (liftUnit_continuousAt hn))).div (Complex.continuous_ofReal.comp
        (continuous_norm.pow w.mult)).continuousAt (Complex.ofReal_ne_zero.mpr (hm x hn).ne')).continuousWithinAt
  have tests (ρ : K → ℂ) (hρ : Bruhat v ρ) (hk : HasCompactSupport ρ) (h0 : 0 ∉ tsupport ρ) :
      (∫ x, f x * ρ x ∂dx) = 0 := by
    have hc : Continuous ρ := (d.arch_bruhat_estimates w hρ).1.choose_spec.continuous
    have integ (c : Kˣ → ℂ) (hc' : Continuous c) :
        Integrable (fun x : K => (c (liftUnit x) / (m x : ℂ)) * ρ x) dx := by
      have cc : ContinuousOn (fun x : K => (c (liftUnit x) / (m x : ℂ)) * ρ x) (tsupport ρ) := by
        intro x hx
        have hn : x ≠ 0 := fun e => h0 (e ▸ hx)
        exact ((hc'.continuousAt.comp (liftUnit_continuousAt hn)).div (Complex.continuous_ofReal.comp
          (continuous_norm.pow w.mult)).continuousAt (Complex.ofReal_ne_zero.mpr (hm x hn).ne')).mul
            hc.continuousAt |>.continuousWithinAt
      exact (cc.integrableOn_compact hk).integrable_of_forall_notMem_eq_zero
        (fun x hx => by rw [image_eq_zero_of_notMem_tsupport hx,mul_zero])
    have line (c : Kˣ → ℂ) : d.lineIntegral v (fun u => c u * ρ u.val) =
        ∫ x, (c (liftUnit x) / (m x : ℂ)) * ρ x ∂dx := by
      unfold lineIntegral
      apply integral_congr_ae
      filter_upwards [(dx).ae_ne 0] with x hx
      have hn : x ≠ 0 := hx
      simp only [ne_eq,hn,not_false_eq_true,dite_true]
      rw [show liftUnit x = Units.mk0 x hn from Units.ext (liftUnit_val hn)]
      simp only [Units.val_mk0,m]
      ring
    have e := h ρ hρ hk h0
    rw [line,line] at e
    have hsplit : (fun x => f x * ρ x) = fun x => (a (liftUnit x) / (m x : ℂ)) * ρ x -
        (b (liftUnit x) / (m x : ℂ)) * ρ x := by
      funext x; simp only [f]; ring
    rw [hsplit,integral_sub (integ a ha) (integ b hb),e,sub_self]
  have zero (x : K) (hx : x ≠ 0) : f x = 0 := by
    by_cases hw : w.IsReal
    · let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
      exact d.arch_separate_coordinates w e (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw)
        (fun k => by simpa only [Bruhat,hw,↓reduceDIte] using (show ∃ g : SchwartzMap ℝ ℂ, ∀ x : K, k (e x) = g (e x)
          from ⟨k,fun _ => rfl⟩)) cf tests x hx
    · let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex (InfinitePlace.not_isReal_iff_isComplex.mp hw)
      exact d.arch_separate_coordinates w e (InfinitePlace.Completion.isometry_extensionEmbedding w)
        (fun k => by simpa only [Bruhat,hw,↓reduceDIte] using (show ∃ g : SchwartzMap ℂ ℂ, ∀ x : K, k (e x) = g (e x)
          from ⟨k,fun _ => rfl⟩)) cf tests x hx
  funext u
  have hz := zero u.val u.ne_zero
  have hl : liftUnit u.val = u := Units.ext (liftUnit_val u.ne_zero)
  simp only [f,hl,div_eq_zero_iff,Complex.ofReal_eq_zero,(hm u.val u.ne_zero).ne',or_false] at hz
  exact sub_eq_zero.mp hz

/-- The marginal of any Archimedean Schwartz section is continuous on the units. -/
theorem arch_continuous_marginal (Ψ : d.schwartz v) : Continuous (d.marginal v Ψ) := by
  let : (dx).IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  let m := modulus F v
  let γ := growthExponent n
  have hγ : 0 ≤ γ := growthExponent_nonneg n
  obtain ⟨C,hC,H⟩ := d.schwartz_chart_growth v Ψ 3 (by decide)
  have hcont := (d.continuous_schwartz_charts v Ψ).1
  let : FirstCountableTopology Kˣ := Units.isEmbedding_val₀.firstCountableTopology
  rw [continuous_iff_continuousAt]
  intro x
  have hpos : 0 < m x.val := by simp [m,modulus,norm_pos_iff.mpr x.ne_zero,pow_pos]
  let δ := m x.val / 2
  have hδ : 0 < δ := half_pos hpos
  have near : ∀ᶠ a : Kˣ in 𝓝 x, δ < m a.val :=
    ((Units.continuous_val.norm.pow w.mult).continuousAt).eventually (lt_mem_nhds (half_lt_self hpos))
  let M := 8*C*max (δ^(-γ)) 1
  have bound (a : Kˣ) (ha : δ < m a.val) (y : K) : ‖Ψ.val.1 a y‖ ≤ M*((1+‖y‖)^3)⁻¹ := by
    have hz : (a.val,y) ≠ (0 : K × K) := fun h => a.ne_zero (congrArg Prod.fst h)
    have hb := (H _ hz).1
    simp only [xChart,ne_eq,a.ne_zero,not_false_eq_true,dite_true,Units.mk0_val] at hb
    set r := max (m a.val) (m y)
    have hr : δ < r := ha.trans_le (le_max_left _ _)
    have hr0 : 0 < r := hδ.trans hr
    rw [← div_eq_mul_inv,le_div_iff₀ (by positivity)]
    by_cases hy : ‖y‖ ≤ 1
    · have h1 : min (r^(-γ)) (r^(-((3:ℕ):ℝ))) ≤ max (δ^(-γ)) 1 :=
        (min_le_left _ _).trans ((Real.rpow_le_rpow_of_nonpos hδ hr.le (neg_nonpos.mpr hγ)).trans (le_max_left _ _))
      calc ‖Ψ.val.1 a y‖ * (1+‖y‖)^3 ≤ (C*max (δ^(-γ)) 1) * 2^3 :=
            mul_le_mul (hb.trans (mul_le_mul_of_nonneg_left h1 hC))
              (pow_le_pow_left₀ (by positivity) (by linarith) 3) (by positivity) (by positivity)
        _ = M := by simp only [M]; ring
    · have hy1 : 1 ≤ ‖y‖ := (lt_of_not_ge hy).le
      have hmy : ‖y‖ ≤ m y := by
        simp only [m,modulus]
        exact le_self_pow₀ hy1 w.mult_ne_zero
      have hyr : ‖y‖ ≤ r := hmy.trans (le_max_right _ _)
      have h1 : min (r^(-γ)) (r^(-((3:ℕ):ℝ))) ≤ (‖y‖^3)⁻¹ := by
        refine (min_le_right _ _).trans ?_
        rw [Real.rpow_neg hr0.le,Real.rpow_natCast]
        exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (norm_nonneg _) hyr 3)
      have h2 : (1+‖y‖)^3 ≤ 8*‖y‖^3 := by
        calc (1+‖y‖)^3 ≤ (2*‖y‖)^3 := pow_le_pow_left₀ (by positivity) (by linarith) 3
          _ = 8*‖y‖^3 := by ring
      have hyp : 0 < ‖y‖ := by linarith
      calc ‖Ψ.val.1 a y‖ * (1+‖y‖)^3 ≤ (C*(‖y‖^3)⁻¹) * (8*‖y‖^3) :=
            mul_le_mul (hb.trans (mul_le_mul_of_nonneg_left h1 hC)) h2 (by positivity) (by positivity)
        _ = 8*C := by field_simp
        _ ≤ M := by
            simp only [M]
            have : (1:ℝ) ≤ max (δ^(-γ)) 1 := le_max_right _ _
            nlinarith
  refine continuousAt_of_dominated (bound := fun y : K => M*((1+‖y‖)^3)⁻¹)
    (.of_forall fun a => (hcont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable) ?_
    ((d.integrable_local_inv_cube v).const_mul M) ?_
  · filter_upwards [near] with a ha
    exact .of_forall fun y => bound a ha y
  · filter_upwards with y
    exact (hcont.comp (continuous_id.prodMk continuous_const)).continuousAt

/-- The reverse marginal paired with a smooth test supported away from zero is the
pairing of the Fourier transform of the axis density, at an infinite place. -/
theorem arch_tested_hat_identity (Φ : d.schwartz v) (hΦ : Φ.val ∈ d.testSet v) (s : Kˣ)
    {ρ : K → ℂ} (hρ : Bruhat v ρ) (hk : HasCompactSupport ρ) (h₀ : 0 ∉ tsupport ρ) :
    (Real.sqrt (modulus F v (n : K)) : ℂ) *
      d.lineIntegral v (fun μ => d.marginal v (d.transformTest v Φ hΦ) (μ^n*s) * ρ μ.val) =
      d.lineIntegral v (fun μ => d.hat v (d.axisDensity v Φ s) μ.val * ρ μ.val) := by
  let : (dx).IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  let : SecondCountableTopology K :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let m := modulus F v
  let ψ := d.character.localValue F v
  have hm (x : K) (hx : x ≠ 0) : 0 < m x := by simp [m,modulus,norm_pos_iff.mpr hx,pow_pos]
  have rc : Continuous ρ := (d.arch_bruhat_estimates w hρ).1.choose_spec.continuous
  let g (x : K) : ℂ := if hx : x ≠ 0 then ρ x / (m x : ℂ) else 0
  have hgc : Continuous g := by
    apply continuous_iff_continuousAt.mpr
    intro x
    by_cases hx : x = 0
    · subst x
      apply (continuousAt_const (y := (0 : ℂ))).congr_of_eventuallyEq
      filter_upwards [(isClosed_tsupport ρ).isOpen_compl.mem_nhds h₀] with y hy
      simp [g,image_eq_zero_of_notMem_tsupport (show y ∉ tsupport ρ from hy)]
    · have hcz : ContinuousAt (fun y : K => ρ y / (m y : ℂ)) x :=
        rc.continuousAt.div (Complex.continuous_ofReal.comp (continuous_norm.pow w.mult)).continuousAt
          (Complex.ofReal_ne_zero.mpr (hm x hx).ne')
      refine hcz.congr ?_
      filter_upwards [isOpen_ne.mem_nhds hx] with y hy
      have hy' : y ≠ 0 := hy
      simp [g,hy']
  have hgs : HasCompactSupport g := hk.mono fun x hx h => hx (by simp [g,h])
  have hgi : Integrable g dx := hgc.integrable_of_hasCompactSupport hgs
  let kρ (r : K) := d.lineIntegral v (fun μ => ρ μ.val * ψ (μ.val*r))
  have hk_eq (r : K) : kρ r = d.hat v g r := by
    unfold kρ lineIntegral hat
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x = 0
    · simp [g,hx]
    · simp only [g,ne_eq,hx,not_false_eq_true,dite_true,Units.val_mk0,ψ,mul_comm r x]
      ring
  have hkc : Continuous kρ := by
    rw [show kρ = d.hat v g from funext hk_eq]; exact d.continuous_hat v hgi
  have hkb (r : K) : ‖kρ r‖ ≤ ∫ x, ‖g x‖ ∂dx := by
    rw [hk_eq]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr 1; funext x
    rw [norm_mul,d.character.norm_localValue,mul_one]
  have hσ := d.arch_axisDensity_test_bruhat w Φ hΦ s
  have σc : Continuous (d.axisDensity v Φ s) := (d.arch_bruhat_estimates w hσ).1.choose_spec.continuous
  have hσk : Integrable (fun r => d.axisDensity v Φ s r * kρ r) dx :=
    (hσ.integrable d).mul_bdd hkc.aestronglyMeasurable (.of_forall hkb)
  rw [d.arch_tested_root_sum_on_test w Φ hΦ s hρ hk h₀]
  change (∫ y, (if hy : y ≠ 0 then d.axis v Φ (Units.mk0 y hy) else 0) *
    ∑ r ∈ Polynomial.nthRootsFinset n (-(s.val*y)), kρ r ∂dx) = _
  rw [d.arch_axis_root_change w Φ s hkc hσk]
  simp_rw [hk_eq]
  rw [← d.hat_pair_swap v σc hgc (hσ.integrable d) hgi]
  unfold lineIntegral
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x = 0
  · simp [g,hx]
  · simp only [g,ne_eq,hx,not_false_eq_true,dite_true,Units.val_mk0]
    ring

/-- Lemma A.2 at an infinite place on test sections. -/
theorem arch_reverse_marginal (Φ : d.schwartz v) (hΦ : Φ.val ∈ d.testSet v) (x : Kˣ) :
    ∀ u : Kˣ, d.marginal v (d.transformTest v Φ hΦ) (u^n*x) =
      (Real.sqrt (modulus F v (n : K)) : ℂ)⁻¹ * d.hat v (d.axisDensity v Φ x) u := by
  let : (dx).IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  let c : ℂ := Real.sqrt (modulus F v (n : K))
  have hc : c ≠ 0 := by
    have hnz := (diagonal F v).injective.ne (Nat.cast_ne_zero.mpr (NeZero.ne n) : (n:F) ≠ 0)
    simp only [map_natCast,map_zero] at hnz
    exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos_of_pos (by simp [modulus,norm_pos_iff.mpr hnz,pow_pos])).ne'
  have hσ := d.arch_axisDensity_test_bruhat w Φ hΦ x
  let a (u : Kˣ) := c * d.marginal v (d.transformTest v Φ hΦ) (u^n*x)
  let b (u : Kˣ) := d.hat v (d.axisDensity v Φ x) u.val
  have ha : Continuous a := continuous_const.mul
    ((d.arch_continuous_marginal w _).comp ((continuous_id.pow n).mul continuous_const))
  have hb : Continuous b := (d.continuous_hat v (hσ.integrable d)).comp Units.continuous_val
  have hab := d.arch_lineIntegral_separate w ha hb (fun ρ hρ hk h₀ => by
    have e := d.arch_tested_hat_identity w Φ hΦ x hρ hk h₀
    simp only [a,mul_assoc]
    rw [d.lineIntegral_const_mul]
    exact e)
  intro u
  have hu := congrFun hab u
  simp only [a,b] at hu
  rw [← hu,← mul_assoc,inv_mul_cancel₀ hc,one_mul]

end MetaplecticPoisson.Datum

