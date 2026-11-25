import MetaplecticSummation.FiniteGerms
import MetaplecticSummation.FiniteInversion
import MetaplecticSummation.ArchimedeanInversion
import MetaplecticSummation.RootKernel
import MetaplecticSummation.PlancherelBounds

noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField IsDedekindDomain Filter MeasureTheory
open scoped Topology Matrix ENNReal
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)
variable (v : Place F)
def mass (Φ : d.schwartz v) : ℝ≥0∞ :=
  let dx := selfDual F d.character v
  ∫⁻ p, ‖xChart Φ p‖ₑ ^ 2 ∂(dx.prod dx)

/-- Ordinary Fourier inversion at frequency one for the chosen archimedean
character and its self-dual measure. -/
theorem hat_hat_arch_one (w : InfinitePlace F) (f : LocalField F (.inl w) → ℂ)
    (hf : Bruhat (.inl w) f) : d.hat (.inl w) (d.hat (.inl w) f) 1 = f (-1) :=
  congrFun (d.arch_hat_hat w f hf) 1

theorem schwartz_fourier_square (Φ : d.schwartz v) :
    (d.fourier v (d.fourier v Φ)).val = d.torusCharts v ((-1) ^ (n+1)) Φ.val := by
  cases v with
  | inl w => exact d.fourier_square_of_ordinary_inversion _ (d.hat_hat_arch_one w) Φ
  | inr p => exact d.finite_fourier_square p Φ

/-- Section 4's root kernel in the X chart. The deleted axis and the
zero-determinant line have measure zero and are assigned value zero. -/
def rootKernel (x' : (LocalField F v)ˣ) (y' : LocalField F v)
    (z : LocalField F v × LocalField F v) : ℂ := by
  classical
  let det := z.1 * y' - z.2 * x'
  exact if h : z.1 ≠ 0 ∧ det ≠ 0 then
    d.symbol v (Units.mk0 _ h.1) (-x') *
      ((modulus F v (n : LocalField F v) ^ (-(3/2 : ℝ)) : ℝ) : ℂ) *
      ∑ᶠ t : {t : LocalField F v // t^n = det},
        d.character.localValue F v t.val * ((modulus F v t.val : ℂ) ^ (1 - (n : ℤ)))
    else 0

theorem fourier_root_kernel (Φ : d.schwartz v) (x' : (LocalField F v)ˣ) (y' : LocalField F v) :
    let dx := selfDual F d.character v
    let integrand := fun z => xChart Φ z * d.rootKernel v x' y' z
    Integrable integrand (dx.prod dx) ∧
      (d.fourier v Φ).val.1 x' y' = ∫ z, integrand z ∂(dx.prod dx) := by
  intro dx integrand
  classical
  let : (dx).IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  let : NullSingletonClass dx := d.selfDual_nullSingleton v
  obtain ⟨hG,heq⟩ := d.integralTransform_root_kernel v Φ x' y'
  have hnK : (n : LocalField F v) ≠ 0 := by
    have hnz := (diagonal F v).injective.ne (Nat.cast_ne_zero.mpr (NeZero.ne n) : (n:F) ≠ 0)
    simpa only [map_natCast,map_zero] using hnz
  have hmn : 0 < modulus F v (n : LocalField F v) := by
    cases v <;> simp [modulus,norm_pos_iff.mpr hnK,pow_pos]
  let c : ℂ := (Real.sqrt (modulus F v (n : LocalField F v)) : ℂ)⁻¹ * (modulus F v (n : LocalField F v) : ℂ)⁻¹
  have hc : ((modulus F v (n : LocalField F v) ^ (-(3/2:ℝ)) : ℝ) : ℂ) = c := by
    simp only [c]
    rw [Real.sqrt_eq_rpow,← Complex.ofReal_inv,← Complex.ofReal_inv,← Complex.ofReal_mul,
      ← Real.rpow_neg hmn.le,← Real.rpow_neg_one,← Real.rpow_add hmn]
    norm_num
  have hroots (a : LocalField F v) (f : LocalField F v → ℂ) :
      ∑ᶠ t : {t : LocalField F v // t^n = a}, f t.val = ∑ t ∈ Polynomial.nthRootsFinset n a, f t := by
    rw [finsum_subtype_eq_finsum_cond (fun t : LocalField F v => t^n = a) (f := f)]
    change ∑ᶠ t ∈ {t : LocalField F v | t^n = a}, f t = _
    rw [show {t : LocalField F v | t^n = a} = (↑(Polynomial.nthRootsFinset n a) : Set (LocalField F v)) by
      ext t; simp [Polynomial.mem_nthRootsFinset (NeZero.pos n)],finsum_mem_coe_finset]
  let D (z : LocalField F v × LocalField F v) := z.1*y' - z.2*x'.val
  have hnull : ∀ᵐ z ∂(dx.prod dx), D z ≠ 0 := by
    have hDc : Continuous D := by fun_prop
    have hs : MeasurableSet {z : LocalField F v × LocalField F v | D z ≠ 0} :=
      (isOpen_ne_fun hDc continuous_const).measurableSet
    refine (Measure.ae_prod_mem_iff_ae_ae_mem hs).mpr (.of_forall fun x => ?_)
    filter_upwards [(dx).ae_ne (x*y'/x'.val)] with y hy
    intro h
    apply hy
    change x*y' - y*x'.val = 0 at h
    field_simp
    linear_combination -h
  have hpt : ∀ᵐ z ∂(dx.prod dx), integrand z = c * (if hx : z.1 ≠ 0 then
      Φ.val.1 (Units.mk0 z.1 hx) z.2 * d.symbol v (Units.mk0 z.1 hx) (-x') *
        ∑ τ ∈ Polynomial.nthRootsFinset n (z.1*y' - z.2*x'.val),
          d.character.localValue F v τ * (modulus F v τ : ℂ)^(1-(n:ℤ)) else 0) := by
    filter_upwards [hnull] with z hz
    by_cases h1 : z.1 = 0
    · simp [integrand,xChart,h1]
    · have hz' : z.1*y' - z.2*x'.val ≠ 0 := hz
      simp only [integrand,xChart,rootKernel,ne_eq,h1,not_false_eq_true,dite_true,hz',and_self]
      rw [hroots _ (fun t => d.character.localValue F v t * (modulus F v t : ℂ)^(1-(n:ℤ))),hc]
      ring
  refine ⟨(hG.const_mul c).congr (hpt.mono fun z h => h.symm),?_⟩
  rw [d.fourier_apply,heq,integral_congr_ae hpt,integral_const_mul]

section Plancherel

open Set
open scoped ComplexConjugate
open Classical

local notation "Kv" => LocalField F v
local notation "dx" => selfDual F d.character v
local notation "m" => modulus F v

theorem localValue_neg_conj' (x : Kv) :
    d.character.localValue F v (-x) = conj (d.character.localValue F v x) := by
  apply mul_left_cancel₀ (a := d.character.localValue F v x)
    (by intro h; have := d.character.norm_localValue v x; simp [h] at this)
  rw [← d.character.localValue_add,add_neg_cancel,d.character.localValue_zero,Complex.mul_conj',
    d.character.norm_localValue]
  simp

theorem finsum_roots (a : Kv) (f : Kv → ℂ) :
    ∑ᶠ t : {t : Kv // t^n = a}, f t.val = ∑ t ∈ Polynomial.nthRootsFinset n a, f t := by
  rw [finsum_subtype_eq_finsum_cond (fun t : Kv => t^n = a) (f := f)]
  change ∑ᶠ t ∈ {t : Kv | t^n = a}, f t = _
  rw [show {t : Kv | t^n = a} = (↑(Polynomial.nthRootsFinset n a) : Set Kv) by
    ext t; simp [Polynomial.mem_nthRootsFinset (NeZero.pos n)],finsum_mem_coe_finset]

/-- The root kernel off the null locus, with the sum over the finite set of roots. -/
theorem rootKernel_eq (x' : Kvˣ) (y' : Kv) (z : Kv × Kv) (h1 : z.1 ≠ 0) (h2 : z.1*y' - z.2*x'.val ≠ 0) :
    d.rootKernel v x' y' z = d.symbol v (Units.mk0 z.1 h1) (-x') *
      ((m (n : Kv) ^ (-(3/2:ℝ)) : ℝ) : ℂ) * ∑ t ∈ Polynomial.nthRootsFinset n (z.1*y' - z.2*x'.val),
        d.character.localValue F v t * (m t : ℂ)^(1-(n:ℤ)) := by
  simp only [rootKernel,ne_eq,h1,h2,not_false_eq_true,and_self,dite_true]
  rw [finsum_roots v _ (fun t => d.character.localValue F v t * (m t : ℂ)^(1-(n:ℤ)))]

/-- The pointwise bound for the root kernel. -/
theorem norm_rootKernel_le (x' : Kvˣ) (y' : Kv) (z : Kv × Kv) :
    ‖d.rootKernel v x' y' z‖ ≤ n * m (n : Kv) ^ (-(3/2:ℝ)) * (m (z.1*y' - z.2*x'.val))^(-growthExponent n) := by
  have hm0 (a : Kv) : 0 ≤ m a := by cases v <;> simp [modulus,pow_nonneg]
  by_cases h : z.1 ≠ 0 ∧ z.1*y' - z.2*x'.val ≠ 0
  · rw [d.rootKernel_eq v x' y' z h.1 h.2,norm_mul,norm_mul,d.norm_symbol,one_mul,Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_nonneg (hm0 _) _)]
    calc m (n:Kv) ^ (-(3/2:ℝ)) * ‖∑ t ∈ Polynomial.nthRootsFinset n (z.1*y' - z.2*x'.val),
          d.character.localValue F v t * (m t : ℂ)^(1-(n:ℤ))‖
        ≤ m (n:Kv) ^ (-(3/2:ℝ)) * (n * (m (z.1*y' - z.2*x'.val))^(-growthExponent n)) := by
          exact mul_le_mul_of_nonneg_left (d.rootSum_norm_le v _ h.2) (Real.rpow_nonneg (hm0 _) _)
      _ = _ := by ring
  · have h0 : d.rootKernel v x' y' z = 0 := by
      simp only [rootKernel,h,dite_false]
    rw [h0,norm_zero]
    exact mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg (hm0 _) _)) (Real.rpow_nonneg (hm0 _) _)

/-- The square of the transform at εv. -/
theorem fourier_square_eps (Φ : d.schwartz v) (x : Kvˣ) (y : Kv) :
    (d.fourier v (d.fourier v Φ)).val.1 ((-1)^(n+1) * x) ((-1:Kvˣ)^(n+1) * y) =
      d.symbol v ((-1)^(n+1) * x) ((-1)^(n+1)) * d.symbol v (-1) ((-1)^(n+1)) * Φ.val.1 x y := by
  rw [d.schwartz_fourier_square v Φ]
  simp only [torusCharts]
  congr 2
  · rw [← mul_assoc,← pow_add,← two_mul,pow_mul]; simp

/-- The adjoint relation of the root kernel: exchanging the two points and applying
the diagonal element ε conjugates the kernel up to a symbol depending only on v. -/
private theorem rootKernel_symm_of_det (v1 w1 : Kvˣ) (v2 w2 : Kv) (hdet : v1.val*w2 - v2*w1.val ≠ 0) :
    d.rootKernel v ((-1)^(n+1)*v1) (((-1:Kvˣ)^(n+1)).val*v2) (w1.val,w2) =
      d.symbol v ((-1)^(n+1)*v1) ((-1)^(n+1)) * d.symbol v (-1) ((-1)^(n+1)) *
        conj (d.rootKernel v w1 w2 (v1.val,v2)) := by
  let ε : Kvˣ := (-1)^(n+1)
  have hεv : (-ε).val = (-1)^n := by simp [ε,pow_succ]
  have hdet2 : w1.val*(ε.val*v2) - w2*(ε*v1).val = (-1)^n * (v1.val*w2 - v2*w1.val) := by
    rw [Units.val_mul,← hεv,Units.val_neg]; ring
  have hdet2' : w1.val*(ε.val*v2) - w2*(ε*v1).val ≠ 0 := by
    rw [hdet2]; exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hdet
  rw [d.rootKernel_eq v _ _ (w1.val,w2) w1.ne_zero hdet2',d.rootKernel_eq v _ _ (v1.val,v2) v1.ne_zero hdet]
  simp only [Units.mk0_val]
  -- the symbol factors
  let H := d.lineSymbol v (by cases v with
    | inl w => exact d.arch_steinberg w
    | inr p => exact d.finite_steinberg p)
  have hks := H.kernel_symbol w1 v1
  have hsym (a b : Kvˣ) : d.symbol v a b = (H.pairing a b).val := rfl
  have hconj (a b : Kvˣ) : conj (d.symbol v a b) = (d.symbol v a b)⁻¹ :=
    (Complex.inv_eq_conj (d.norm_symbol v a b)).symm
  -- the root sums
  have hsum : (∑ t ∈ Polynomial.nthRootsFinset n (w1.val*(ε.val*v2) - w2*(ε*v1).val),
      d.character.localValue F v t * (m t : ℂ)^(1-(n:ℤ))) =
      ∑ t ∈ Polynomial.nthRootsFinset n (v1.val*w2 - v2*w1.val),
        conj (d.character.localValue F v t) * (m t : ℂ)^(1-(n:ℤ)) := by
    have mneg (a : Kv) : m (-a) = m a := by cases v <;> simp [modulus]
    rw [hdet2]
    refine Finset.sum_nbij' (fun t => -t) (fun t => -t) ?_ ?_ (fun _ _ => neg_neg _) (fun _ _ => neg_neg _) ?_
    · intro t ht
      simp only [Polynomial.mem_nthRootsFinset (NeZero.pos n)] at ht ⊢
      rw [neg_pow,ht,← mul_assoc,← mul_pow]; simp
    · intro t ht
      simp only [Polynomial.mem_nthRootsFinset (NeZero.pos n)] at ht ⊢
      rw [neg_pow,ht]
    · intro t _
      rw [d.localValue_neg_conj' v,Complex.conj_conj,mneg]
  rw [hsum]
  simp only [map_mul,map_sum,map_zpow₀,Complex.conj_ofReal,hconj]
  rw [hsym,hsym,hsym,hsym] at *
  have key : (H.pairing w1 (-(ε*v1))).val = (H.pairing (ε*v1) ε).val * (H.pairing (-1) ε).val *
      ((H.pairing v1 (-w1)).val)⁻¹ := by
    rw [← Units.val_mul,← hks,Units.val_mul,mul_assoc,mul_inv_cancel₀ (Units.ne_zero _),mul_one]
  rw [key]
  ring

/-- The X-chart of a Schwartz section is continuous off the vertical axis. -/
theorem continuousAt_xChart (Φ : d.schwartz v) {z : Kv × Kv} (hz : z.1 ≠ 0) :
    ContinuousAt (xChart Φ.val) z := by
  let : NontriviallyNormedField Kv := { localNormedField F v with
    non_trivial := by
      cases v with
      | inl w => exact (archNontriviallyNormedCompletion w).non_trivial
      | inr p => exact (FinitePlace.nontriviallyNormedCompletion p).non_trivial }
  have hc : ContinuousAt (fun p : Kv × Kv => Function.uncurry Φ.val.1 (liftUnit p.1,p.2)) z :=
    (d.continuous_schwartz_charts v Φ).1.continuousAt.comp
      (((liftUnit_continuousAt hz).comp continuousAt_fst).prodMk continuousAt_snd)
  refine hc.congr ?_
  filter_upwards [(isOpen_ne_fun continuous_fst continuous_const).mem_nhds hz] with p hp
  have hp' : p.1 ≠ 0 := hp
  simp only [Function.uncurry,xChart,ne_eq,hp',not_false_eq_true,dite_true]
  rw [show liftUnit p.1 = Units.mk0 p.1 hp' from Units.ext (liftUnit_val hp')]

/-- Absolute integrability of the kernel pairing of two sections on the product of planes. -/
theorem integrable_kernel_pairing (Φ Ψ : d.schwartz v) :
    Integrable (fun p : (Kv × Kv) × (Kv × Kv) => if hw : p.1.1 ≠ 0 then
      conj (xChart Ψ.val p.1) * (xChart Φ.val p.2 * d.rootKernel v (Units.mk0 p.1.1 hw) p.1.2 p.2) else 0)
      (((dx).prod dx).prod ((dx).prod dx)) := by
  let : (dx).IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  let : NullSingletonClass dx := d.selfDual_nullSingleton v
  let : NontriviallyNormedField Kv := { localNormedField F v with
    non_trivial := by
      cases v with
      | inl w => exact (archNontriviallyNormedCompletion w).non_trivial
      | inr p => exact (FinitePlace.nontriviallyNormedCompletion p).non_trivial }
  let : SecondCountableTopology Kv := by
    cases v with
    | inl w => exact (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
    | inr p => exact inferInstanceAs (SecondCountableTopology (p.adicCompletion F))
  set H := fun p : (Kv × Kv) × (Kv × Kv) => if hw : p.1.1 ≠ 0 then
      conj (xChart Ψ.val p.1) * (xChart Φ.val p.2 * d.rootKernel v (Units.mk0 p.1.1 hw) p.1.2 p.2) else 0
  let ψ := d.character.localValue F v
  let M : ℝ := m (n : Kv) ^ (-(3/2:ℝ))
  let S := fun z : Kv => ∑ τ ∈ Polynomial.nthRootsFinset n z, ψ τ * (m τ : ℂ)^(1-(n:ℤ))
  have hm0 (z : Kv) : 0 ≤ m z := by cases v <;> simp [modulus,pow_nonneg]
  have hmpos (z : Kv) (hz : z ≠ 0) : 0 < m z := by cases v <;> simp [modulus,norm_pos_iff.mpr hz,pow_pos]
  have hmc : Continuous m := by
    show Continuous (modulus F v)
    cases v with
    | inl w => exact continuous_norm.pow _
    | inr p => exact continuous_norm
  have hSc : ContinuousOn S {0}ᶜ := by
    apply rootSum_continuousOn_ne v
    intro τ hτ
    have hτ' : τ ≠ 0 := hτ
    exact ((d.character.continuous_localValue v).continuousAt.mul
      ((Complex.continuous_ofReal.comp hmc).continuousAt.zpow₀ _
        (Or.inl (Complex.ofReal_ne_zero.mpr (hmpos τ hτ').ne')))).continuousWithinAt
  -- measurability
  let D (p : (Kv × Kv) × (Kv × Kv)) := p.2.1 * p.1.2 - p.2.2 * p.1.1
  have hDc : Continuous D := by fun_prop
  let U : Set ((Kv × Kv) × (Kv × Kv)) := {p | p.1.1 ≠ 0} ∩ {p | p.2.1 ≠ 0} ∩ {p | D p ≠ 0}
  have hU : IsOpen U :=
    ((isOpen_ne_fun (by fun_prop) continuous_const).inter (isOpen_ne_fun (by fun_prop) continuous_const)).inter
      (isOpen_ne_fun hDc continuous_const)
  have hzero (p) (hp : p ∉ U) : H p = 0 := by
    by_cases h1 : p.1.1 = 0
    · simp [H,h1]
    by_cases h2 : p.2.1 = 0
    · simp [H,h1,h2,xChart]
    have h3 : D p = 0 := by
      by_contra h3; exact hp ⟨⟨h1,h2⟩,h3⟩
    have hk : d.rootKernel v (Units.mk0 p.1.1 h1) p.1.2 p.2 = 0 := by
      have : ¬ (p.2.1 ≠ 0 ∧ p.2.1 * p.1.2 - p.2.2 * (Units.mk0 p.1.1 h1).val ≠ 0) := by
        simp only [Units.val_mk0]; exact fun h => h.2 h3
      simp only [rootKernel,this,dite_false]
    simp [H,h1,hk]
  have hcont : ContinuousOn H U := by
    intro p hp
    obtain ⟨⟨h1,h2⟩,h3⟩ := hp
    have hc : ContinuousAt (fun q : (Kv × Kv) × (Kv × Kv) => conj (xChart Ψ.val q.1) *
        (xChart Φ.val q.2 * (d.symbol v (liftUnit q.2.1) ((-1 : Kvˣ) * liftUnit q.1.1) * (M : ℂ) * S (D q)))) p := by
      refine (Complex.continuous_conj.continuousAt.comp ((d.continuousAt_xChart v Ψ h1).comp continuousAt_fst)).mul
        (((d.continuousAt_xChart v Φ h2).comp continuousAt_snd).mul (((?_ : ContinuousAt _ p).mul
          continuousAt_const).mul ((hSc.continuousAt (isOpen_ne.mem_nhds h3)).comp hDc.continuousAt)))
      have a2 : ContinuousAt (fun q : (Kv × Kv) × (Kv × Kv) => liftUnit q.2.1) p :=
        ContinuousAt.comp (f := fun q : (Kv × Kv) × (Kv × Kv) => q.2.1) (liftUnit_continuousAt h2)
          (by fun_prop : Continuous fun q : (Kv × Kv) × (Kv × Kv) => q.2.1).continuousAt
      have a1 : ContinuousAt (fun q : (Kv × Kv) × (Kv × Kv) => liftUnit q.1.1) p :=
        ContinuousAt.comp (f := fun q : (Kv × Kv) × (Kv × Kv) => q.1.1) (liftUnit_continuousAt h1)
          (by fun_prop : Continuous fun q : (Kv × Kv) × (Kv × Kv) => q.1.1).continuousAt
      exact (d.continuous_symbol v).continuousAt.comp (a2.prodMk (continuousAt_const.mul a1))
    refine (hc.congr ?_).continuousWithinAt
    filter_upwards [hU.mem_nhds ⟨⟨h1,h2⟩,h3⟩] with q hq
    obtain ⟨⟨q1,q2⟩,q3⟩ := hq
    have q1' : q.1.1 ≠ 0 := q1
    have q2' : q.2.1 ≠ 0 := q2
    have q3' : q.2.1 * q.1.2 - q.2.2 * (Units.mk0 q.1.1 q1').val ≠ 0 := q3
    simp only [H,ne_eq,q1',not_false_eq_true,dite_true]
    rw [d.rootKernel_eq v _ _ _ q2' q3']
    rw [show liftUnit q.1.1 = Units.mk0 q.1.1 q1' from Units.ext (liftUnit_val q1'),
      show liftUnit q.2.1 = Units.mk0 q.2.1 q2' from Units.ext (liftUnit_val q2')]
    simp only [Units.val_mk0,D,S,ψ,M,neg_one_mul]
  have hHm : AEStronglyMeasurable H (((dx).prod dx).prod ((dx).prod dx)) :=
    aesm_of_continuousOn hU hcont hzero _
  refine ⟨hHm,?_⟩
  -- the finite integral
  obtain ⟨CΨ,hCΨ,HΨ⟩ := d.xChart_radius_bound v Ψ
  obtain ⟨CΦ,hCΦ,HΦ⟩ := d.xChart_radius_bound v Φ
  let γ := growthExponent n
  have hγ0 : 0 ≤ γ := growthExponent_nonneg n
  have hγ1 : γ < 1 := by
    simp only [γ,growthExponent]
    rw [div_lt_one (by exact_mod_cast NeZero.pos n)]
    exact_mod_cast Nat.sub_lt (NeZero.pos n) one_pos
  let Kc : ℝ := n * m (n : Kv) ^ (-(3/2:ℝ))
  have hKc : 0 ≤ Kc := mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (hm0 _) _)
  let fr := fun z : Kv × Kv => min ((max (m z.1) (m z.2))^(-γ)) ((max (m z.1) (m z.2))^(-(4:ℝ)))
  have hfr0 (z : Kv × Kv) : 0 ≤ fr z :=
    le_min (Real.rpow_nonneg (le_max_of_le_left (hm0 _)) _) (Real.rpow_nonneg (le_max_of_le_left (hm0 _)) _)
  let c := fun w : Kv × Kv => CΨ * fr w * (CΦ * Kc)
  let G := fun p : (Kv × Kv) × (Kv × Kv) => if p.1.1 ≠ 0 then
    ENNReal.ofReal (c p.1) * (ENNReal.ofReal (fr p.2) *
      ENNReal.ofReal ((m (p.2.1*p.1.2 - p.2.2*p.1.1))^(-γ))) else 0
  have hHG (p) : ‖H p‖ₑ ≤ G p := by
    by_cases h1 : p.1.1 = 0
    · simp [H,h1]
    simp only [G,ne_eq,h1,not_false_eq_true,ite_true]
    simp only [H,ne_eq,h1,not_false_eq_true,dite_true]
    rw [← ofReal_norm,← ENNReal.ofReal_mul (hfr0 _),← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hCΨ (hfr0 _))
      (mul_nonneg hCΦ hKc))]
    apply ENNReal.ofReal_le_ofReal
    rw [norm_mul,norm_mul,Complex.norm_conj]
    have k := d.norm_rootKernel_le v (Units.mk0 p.1.1 h1) p.1.2 p.2
    rw [Units.val_mk0] at k
    have hD0 : 0 ≤ (m (p.2.1*p.1.2 - p.2.2*p.1.1))^(-γ) := Real.rpow_nonneg (hm0 _) _
    calc ‖xChart Ψ.val p.1‖ * (‖xChart Φ.val p.2‖ * ‖d.rootKernel v (Units.mk0 p.1.1 h1) p.1.2 p.2‖)
        ≤ (CΨ * fr p.1) * ((CΦ * fr p.2) * (Kc * (m (p.2.1*p.1.2 - p.2.2*p.1.1))^(-γ))) := by
          exact mul_le_mul (HΨ _) (mul_le_mul (HΦ _) k (norm_nonneg _) (mul_nonneg hCΦ (hfr0 _)))
            (by positivity) (mul_nonneg hCΨ (hfr0 _))
      _ = _ := by ring
  let r := fun z : Kv × Kv => max (m z.1) (m z.2)
  let cF := ∫⁻ s, ENNReal.ofReal (min ((m s)^(-γ)) ((m s)^(-(4:ℝ)))) ∂dx
  let I := ∫⁻ u, ENNReal.ofReal (min ((m u)^(-γ)) ((m u)^(-(2:ℝ)))) ∂dx
  let B := ∫⁻ z, ENNReal.ofReal (fr z) ∂((dx).prod dx)
  have hinner (w : Kv × Kv) : ∫⁻ z, G (w,z) ∂((dx).prod dx) ≤
      ENNReal.ofReal (c w) * (cF * I * ENNReal.ofReal (r w)⁻¹ + B) := by
    by_cases h1 : w.1 = 0
    · simp [G,h1]
    simp only [G,ne_eq,h1,not_false_eq_true,ite_true]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    gcongr
    have hb := d.lintegral_kernel_bound v γ hγ0 (by linarith) (Units.mk0 w.1 h1) w.2
    simp only [Units.val_mk0] at hb
    exact hb
  have hcF : cF < ∞ := (d.integrable_modulus_two_sided v hγ0 hγ1 (by norm_num)).lintegral_lt_top
  have hI : I < ∞ := (d.integrable_modulus_two_sided v hγ0 hγ1 (by norm_num)).lintegral_lt_top
  have hB : B < ∞ := d.lintegral_radius_finite v hγ0 (by linarith)
  have hB2 := d.lintegral_radius_finite v (γ' := 1+γ) (by linarith) (by linarith)
  have hrpos (w : Kv × Kv) (hw : w.1 ≠ 0) : 0 < r w := lt_max_of_lt_left (hmpos _ hw)
  have key (t : ℝ) (ht : 0 < t) : min (t^(-γ)) (t^(-(4:ℝ))) * t⁻¹ ≤ min (t^(-(1+γ))) (t^(-(4:ℝ))) := by
    have e1 : t^(-γ) * t⁻¹ = t^(-(1+γ)) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add ht]; ring_nf
    rw [min_mul_of_nonneg _ _ (inv_nonneg.mpr ht.le), e1]
    refine le_min (min_le_left _ _) ?_
    rcases le_total t 1 with h|h
    · exact (min_le_left _ _).trans (Real.rpow_le_rpow_of_exponent_ge ht h (by linarith))
    · exact (min_le_right _ _).trans (mul_le_of_le_one_right (Real.rpow_nonneg ht.le _) (inv_le_one_of_one_le₀ h))
  have hmr : Measurable r := (hmc.measurable.comp measurable_fst).max (hmc.measurable.comp measurable_snd)
  have hmeas2 : Measurable fun w : Kv × Kv => ENNReal.ofReal (min ((r w)^(-(1+γ))) ((r w)^(-(4:ℝ)))) :=
    ENNReal.measurable_ofReal.comp ((hmr.pow_const _).min (hmr.pow_const _))
  calc ∫⁻ p, ‖H p‖ₑ ∂(((dx).prod dx).prod ((dx).prod dx))
      ≤ ∫⁻ p, G p ∂(((dx).prod dx).prod ((dx).prod dx)) := lintegral_mono hHG
    _ ≤ ∫⁻ w, ∫⁻ z, G (w,z) ∂((dx).prod dx) ∂((dx).prod dx) := lintegral_prod_le _
    _ ≤ ∫⁻ w, ENNReal.ofReal (CΨ * (CΦ * Kc)) * (cF * I * ENNReal.ofReal (min ((r w)^(-(1+γ))) ((r w)^(-(4:ℝ))))
          + B * ENNReal.ofReal (fr w)) ∂((dx).prod dx) := by
        apply lintegral_mono_ae
        filter_upwards [Measure.quasiMeasurePreserving_fst.ae ((dx).ae_ne 0)] with w hw
        have hrinv : 0 ≤ (r w)⁻¹ := inv_nonneg.mpr (hrpos w hw).le
        refine (hinner w).trans ?_
        calc ENNReal.ofReal (c w) * (cF * I * ENNReal.ofReal (r w)⁻¹ + B)
            = ENNReal.ofReal (CΨ * (CΦ * Kc)) * (cF * I * ENNReal.ofReal (fr w * (r w)⁻¹) +
                B * ENNReal.ofReal (fr w)) := by
              simp only [c]
              rw [ENNReal.ofReal_mul (hfr0 w), ENNReal.ofReal_mul (mul_nonneg hCΨ (hfr0 w)),
                ENNReal.ofReal_mul hCΨ, ENNReal.ofReal_mul hCΨ]
              ring
          _ ≤ _ := by
              gcongr
              exact key _ (hrpos w hw)
    _ = ENNReal.ofReal (CΨ * (CΦ * Kc)) * (cF * I * ∫⁻ w, ENNReal.ofReal (min ((r w)^(-(1+γ))) ((r w)^(-(4:ℝ))))
          ∂((dx).prod dx) + B * B) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left (hmeas2.const_mul _),
          lintegral_const_mul _ hmeas2, lintegral_const_mul' _ _ hB.ne]
    _ < ∞ := by
        refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.mpr ⟨?_, ENNReal.mul_lt_top hB hB⟩)
        exact ENNReal.mul_lt_top (ENNReal.mul_lt_top hcF hI) hB2

/-- The adjoint symmetry of the root kernel, including the null line where both sides vanish. -/
theorem rootKernel_symm (v1 w1 : Kvˣ) (v2 w2 : Kv) :
    d.rootKernel v ((-1)^(n+1)*v1) (((-1:Kvˣ)^(n+1)).val*v2) (w1.val,w2) =
      d.symbol v ((-1)^(n+1)*v1) ((-1)^(n+1)) * d.symbol v (-1) ((-1)^(n+1)) *
        conj (d.rootKernel v w1 w2 (v1.val,v2)) := by
  by_cases hdet : v1.val*w2 - v2*w1.val = 0
  · let ε : Kvˣ := (-1)^(n+1)
    have h1 : ¬ ((w1.val,w2).1 ≠ 0 ∧ (w1.val,w2).1*(ε.val*v2) - (w1.val,w2).2*(ε*v1).val ≠ 0) := by
      rintro ⟨-,h⟩; apply h
      simp only [Units.val_mul]; linear_combination (-ε.val) * hdet
    have h2 : ¬ ((v1.val,v2).1 ≠ 0 ∧ (v1.val,v2).1*w2 - (v1.val,v2).2*w1.val ≠ 0) := by
      rintro ⟨-,h⟩; exact h hdet
    simp only [rootKernel]
    rw [dite_cond_eq_false (eq_false h1),dite_cond_eq_false (eq_false h2)]; simp
  · exact d.rootKernel_symm_of_det v v1 w1 v2 w2 hdet

theorem aesm_xChart (Φ : d.schwartz v) : AEStronglyMeasurable (xChart Φ.val) ((dx).prod dx) := by
  let : SecondCountableTopology Kv := by
    cases v with
    | inl w => exact (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
    | inr p => exact inferInstanceAs (SecondCountableTopology (p.adicCompletion F))
  refine aesm_of_continuousOn (s := {p : Kv × Kv | p.1 ≠ 0}) (isOpen_ne_fun continuous_fst continuous_const)
    (fun z hz => (d.continuousAt_xChart v Φ hz).continuousWithinAt) (fun z hz => ?_) _
  have : z.1 = 0 := by simpa using hz
  simp [xChart,this]

/-- The mass as the real integral of the squared norm. -/
theorem mass_eq_integral (Φ : d.schwartz v) :
    Integrable (fun z => ‖xChart Φ.val z‖^2) ((dx).prod dx) ∧
      d.mass v Φ = ENNReal.ofReal (∫ z, ‖xChart Φ.val z‖^2 ∂((dx).prod dx)) := by
  have hm : AEStronglyMeasurable (fun z => ‖xChart Φ.val z‖^2) ((dx).prod dx) :=
    ((d.aesm_xChart v Φ).norm).pow 2
  have hi : Integrable (fun z => ‖xChart Φ.val z‖^2) ((dx).prod dx) := by
    refine ⟨hm,?_⟩
    simp only [HasFiniteIntegral,enorm_pow,enorm_norm]
    exact d.lintegral_xChart_sq_lt_top v Φ
  refine ⟨hi,?_⟩
  rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun _ => by positivity)]
  simp only [mass]
  congr 1; funext z
  rw [← ofReal_norm,← ENNReal.ofReal_pow (norm_nonneg _)]

/-- Finiteness and invariance of the squared norm in Theorem 7.1. -/
theorem fourier_mass (Φ : d.schwartz v) :
    d.mass v Φ < ⊤ ∧ d.mass v (d.fourier v Φ) = d.mass v Φ := by
  let : (dx).IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  let : NullSingletonClass dx := d.selfDual_nullSingleton v
  refine ⟨d.lintegral_xChart_sq_lt_top v Φ,?_⟩
  set Ψ := d.fourier v Φ
  let μ := (dx).prod dx
  let ε : Kvˣ := (-1)^(n+1)
  have hae : ∀ᵐ w ∂μ, w.1 ≠ 0 := Measure.quasiMeasurePreserving_fst.ae ((dx).ae_ne 0)
  have hcx (Θ : d.schwartz v) : ((∫ w, ‖xChart Θ.val w‖^2 ∂μ : ℝ) : ℂ) =
      ∫ w, conj (xChart Θ.val w) * xChart Θ.val w ∂μ := by
    rw [← integral_complex_ofReal]; congr 1; funext w; rw [Complex.conj_mul']; push_cast; rfl
  let H := fun w z : Kv × Kv => if hw : w.1 ≠ 0 then
      conj (xChart Ψ.val w) * (xChart Φ.val z * d.rootKernel v (Units.mk0 w.1 hw) w.2 z) else 0
  have hint : Integrable (Function.uncurry H) (μ.prod μ) := d.integrable_kernel_pairing v Φ Ψ
  have main : ∫ w, conj (xChart Ψ.val w) * xChart Ψ.val w ∂μ =
      ∫ w, conj (xChart Φ.val w) * xChart Φ.val w ∂μ := by
    calc ∫ w, conj (xChart Ψ.val w) * xChart Ψ.val w ∂μ = ∫ w, ∫ z, H w z ∂μ ∂μ := by
          apply integral_congr_ae
          filter_upwards [hae] with w hw
          simp only [H,ne_eq,hw,not_false_eq_true,dite_true]
          rw [integral_const_mul]
          congr 1
          have hk := (d.fourier_root_kernel v Φ (Units.mk0 w.1 hw) w.2).2
          simp only at hk
          rw [← hk]
          simp [xChart,hw,Ψ]
      _ = ∫ z, ∫ w, H w z ∂μ ∂μ := integral_integral_swap hint
      _ = ∫ z, conj (xChart Φ.val z) * xChart Φ.val z ∂μ := by
          apply integral_congr_ae
          filter_upwards [hae] with z hz
          let Z := Units.mk0 z.1 hz
          let c := d.symbol v (ε*Z) ε * d.symbol v (-1) ε
          have hc : c ≠ 0 := by
            apply norm_ne_zero_iff.mp; simp [c,d.norm_symbol]
          have hpt (w : Kv × Kv) : H w z = xChart Φ.val z *
              conj (c⁻¹ * (xChart Ψ.val w * d.rootKernel v (ε*Z) (ε.val*z.2) w)) := by
            by_cases hw : w.1 = 0
            · rw [show xChart Ψ.val w = 0 by simp [xChart,hw]]
              simp [H,hw]
            simp only [H,ne_eq,hw,not_false_eq_true,dite_true]
            have hs := d.rootKernel_symm v Z (Units.mk0 w.1 hw) z.2 w.2
            rw [show ((Units.mk0 w.1 hw).val, w.2) = w from Prod.ext (Units.val_mk0 hw) rfl,
              show (Z.val, z.2) = z from Prod.ext (Units.val_mk0 hz) rfl] at hs
            change d.rootKernel v (ε*Z) (ε.val*z.2) w = c * _ at hs
            rw [hs, show c⁻¹ * (xChart Ψ.val w * (c * conj (d.rootKernel v (Units.mk0 w.1 hw) w.2 z))) =
              xChart Ψ.val w * conj (d.rootKernel v (Units.mk0 w.1 hw) w.2 z) by field_simp]
            simp only [map_mul,Complex.conj_conj]; ring
          rw [show (fun w => H w z) = _ from funext hpt,integral_const_mul,integral_conj,integral_const_mul]
          have hk := (d.fourier_root_kernel v Ψ (ε*Z) (ε.val*z.2)).2
          simp only at hk
          rw [← hk]
          have hsq := d.fourier_square_eps v Φ Z z.2
          change (d.fourier v Ψ).val.1 (ε*Z) (ε.val*z.2) = c * Φ.val.1 Z z.2 at hsq
          rw [hsq, show c⁻¹ * (c * Φ.val.1 Z z.2) = Φ.val.1 Z z.2 by field_simp,
            show xChart Φ.val z = Φ.val.1 Z z.2 by simp [xChart,hz,Z]]
          ring
  rw [(d.mass_eq_integral v Ψ).2,(d.mass_eq_integral v Φ).2]
  congr 1
  exact_mod_cast (hcx Ψ).trans (main.trans (hcx Φ).symm)

end Plancherel

/-- Theorem 7.1, in the chart model, with §5's lift of the diagonal matrix. -/
theorem schwartz_inversion :
    Function.Bijective (d.fourier v) ∧
    (∀ Φ, (d.fourier v (d.fourier v Φ)).val = d.torusCharts v ((-1) ^ (n+1)) Φ.val) ∧
    (∀ (g : d.cover v) Φ, d.fourier v (g.val Φ) = g.val (d.fourier v Φ)) ∧
    (∀ Φ, d.mass v Φ < ⊤ ∧ d.mass v (d.fourier v Φ) = d.mass v Φ) :=
  ⟨d.fourier_bijective_of_square v (d.schwartz_fourier_square v),
    d.schwartz_fourier_square v, d.fourier_equivariant v, d.fourier_mass v⟩

end MetaplecticPoisson.Datum
