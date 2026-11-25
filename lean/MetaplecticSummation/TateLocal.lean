import MetaplecticSummation.Jacquet.Kernel
import MetaplecticSummation.Jacquet.TestBump
import MetaplecticSummation.RootKernel
import MetaplecticSummation.ArchimedeanDifference

/-! Tate's local functional equation (§10.4) in the form used by Proposition 10.20.

For a continuous unitary character χ and 0 < Re z < 1, Tate's symmetry
Z(a, χ, z) Z(b̂, χ⁻¹, 1−z) = Z(b, χ, z) Z(â, χ⁻¹, 1−z)
holds for Schwartz–Bruhat functions a and b. A test bump with nonvanishing zeta
integral then produces one constant γ with Z(ĝ, χ⁻¹, 1−z) = γ Z(g, χ, z) for every
test weight and every Schwartz–Bruhat function. -/

noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField MeasureTheory Filter Set
open scoped Topology
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n) (v : Place F)

/-- The local zeta integral Z(W, ω, s) = ∫ W(x) ω(x) |x|^s d^×x. -/
def mellin (v : Place F) (W ω : Weight v) (s : ℂ) :=
  d.lineIntegral v fun x => W x * ω x * (modulus F v x : ℂ) ^ s

/-- Tate's normalization on the open strip. Smooth compact tests supported
away from zero suffice to determine the scalar at each point of the strip. -/
def TateEquation (v : Place F) (ω : Weight v) (s γ : ℂ) : Prop :=
  ∀ g : Weight v, TestWeight v g →
    let ĝ : Weight v := fun y => d.lineIntegral v fun x =>
      (modulus F v x : ℂ) * g x * d.character.localValue F v ((x : LocalField F v) * y)
    d.mellin v ĝ (fun x => (ω x)⁻¹) (1-s) = γ * d.mellin v g ω s

open scoped ContDiff

/-- The involution W ↦ W(1/x)/|x| on weights. -/
def invWeight (W : Weight v) : Weight v := fun u => W u⁻¹ / (modulus F v u.val : ℂ)

private theorem arch_invWeight_smooth {w : InfinitePlace F} {L : Type} [NormedField L] [NormedAlgebra ℝ L]
    (e : w.Completion ≃+* L) (he : Isometry e) (hnorm : ∀ x : L, x ≠ 0 → ContDiffAt ℝ ∞ norm x)
    {W : Weight (.inl w)} (hsW : archSmooth e W) : archSmooth e (invWeight (.inl w) W) := by
  let W₀ (z : L) : ℂ := if h : e.symm z ≠ 0 then W (Units.mk0 _ h) else 0
  intro z hz
  have hz' : z ≠ 0 := hz
  apply ContDiffAt.contDiffWithinAt
  have hw : ContDiffAt ℝ ∞ W₀ z⁻¹ := (hsW z⁻¹ (inv_ne_zero hz')).contDiffAt
    (isOpen_compl_singleton.mem_nhds (inv_ne_zero hz'))
  have hm := Complex.ofRealCLM.contDiff.contDiffAt.comp z ((hnorm z hz').pow w.mult)
  apply ((hw.comp z (contDiffAt_inv ℝ hz')).mul
    (hm.inv (Complex.ofReal_ne_zero.mpr (pow_ne_zero _ (norm_ne_zero_iff.mpr hz'))))).congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hz'] with t ht
  have ht' := (map_ne_zero e.symm).mpr ht
  have ha : (Units.mk0 (e.symm t : LocalField F (.inl w)) ht')⁻¹ =
      Units.mk0 (e.symm t⁻¹) ((map_ne_zero e.symm).mpr (inv_ne_zero ht)) :=
    Units.ext (map_inv₀ e.symm t).symm
  have hn : ‖e.symm t‖ = ‖t‖ := by simpa using (he.norm_map_of_map_zero e.map_zero (e.symm t)).symm
  simp only [invWeight,W₀,ne_eq,ht',(map_ne_zero e.symm).mpr (inv_ne_zero ht),not_false_eq_true,dite_true,modulus,
    div_eq_mul_inv,Function.comp_apply,Units.val_mk0,Pi.inv_apply,Complex.ofRealCLM_apply]
  exact congrArg₂ (fun (a : (LocalField F (.inl w))ˣ) (r : ℝ) => W a * ((r^w.mult : ℝ) : ℂ)⁻¹) ha hn

/-- Test weights are stable under W ↦ W(1/x)/|x|. -/
theorem testWeight_invWeight {W : Weight v} (hw : TestWeight v W) : TestWeight v (invWeight v W) := by
  refine ⟨?_,?_⟩
  · apply HasCompactSupport.intro (hw.1.image continuous_inv)
    intro u hu
    have : u⁻¹ ∉ tsupport W := fun h => hu ⟨u⁻¹,h,inv_inv u⟩
    simp [invWeight,image_eq_zero_of_notMem_tsupport this]
  cases v with
  | inr p =>
    let : NontriviallyNormedField (p.adicCompletion F) := FinitePlace.nontriviallyNormedCompletion p
    let : NontriviallyNormedField (LocalField F (.inr p)) := inferInstanceAs (NontriviallyNormedField (p.adicCompletion F))
    let : IsUltrametricDist (LocalField F (.inr p)) := inferInstanceAs (IsUltrametricDist (p.adicCompletion F))
    have hW : IsLocallyConstant W := hw.2
    exact (hW.comp_continuous continuous_inv).div (locallyConstant_norm_units.comp (fun r : ℝ => (r : ℂ)))
  | inl w =>
    have h2 := hw.2
    dsimp only [TestWeight] at h2 ⊢
    split at h2 <;> rename_i h
    · simp only [h,dite_true]
      exact arch_invWeight_smooth _ (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal h)
        (fun _ hz => contDiffAt_id.norm ℝ hz) h2
    · simp only [h,dite_false]
      exact arch_invWeight_smooth _ (InfinitePlace.Completion.isometry_extensionEmbedding w)
        (fun _ hz => contDiffAt_id.norm ℝ hz) h2

local notation "Kv" => LocalField F v
local notation "dx" => selfDual F d.character v
local notation "m" => modulus F v
local notation "μ" => d.lineMeasure v

/-- A weight extended by zero to the whole local field. -/
def extWeight (g : Weight v) (x : Kv) : ℂ := if h : x ≠ 0 then g (Units.mk0 x h) else 0

@[simp] theorem extWeight_unit (g : Weight v) (u : (Kv)ˣ) : extWeight v g u.val = g u := by
  simp [extWeight,u.ne_zero]

theorem kernelAmplitude_bruhat {W : Weight v} (hw : TestWeight v W) (c : (Kv)ˣ) :
    Bruhat v (d.kernelAmplitude v W c) := by
  cases v with
  | inl w => exact d.arch_kernelAmplitude_bruhat w hw c
  | inr p => exact d.finite_kernelAmplitude_bruhat p hw c

theorem extWeight_eq_kernelAmplitude (g : Weight v) :
    extWeight v g = d.kernelAmplitude v (invWeight v g) (-1) := by
  funext x
  by_cases hx : x = 0
  · simp [extWeight,kernelAmplitude,hx]
  have hk := d.kernelAmplitude_unit v (invWeight v g) (-1) (Units.mk0 x hx)
  simp only [Units.val_mk0] at hk
  rw [hk]
  have hinv : m ((Units.mk0 x hx)⁻¹).val = (m x)⁻¹ := by
    simp only [Units.val_inv_eq_inv_val,Units.val_mk0]
    cases v <;> simp [modulus,norm_inv,inv_pow]
  have hm : (m x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (modulus_ne_zero v (Units.mk0 x hx))
  have h1 : d.symbol v (Units.mk0 x hx)⁻¹ (-(-1)) = 1 := by
    rw [neg_neg,← coe_unitPairing,map_one,Units.val_one]
  simp only [invWeight,inv_inv,hinv,h1,extWeight,ne_eq,hx,not_false_eq_true,dite_true,Complex.ofReal_inv]
  field_simp

include d in
/-- The zero extension of a test weight is Schwartz–Bruhat. -/
theorem extWeight_bruhat {g : Weight v} (hg : TestWeight v g) : Bruhat v (extWeight v g) := by
  rw [d.extWeight_eq_kernelAmplitude v g]
  exact d.kernelAmplitude_bruhat v (testWeight_invWeight v hg) (-1)

theorem continuous_modulus : Continuous m := by
  cases v with
  | inl w => exact continuous_norm.pow _
  | inr p => exact continuous_norm

omit [NeZero n] in
include d in
/-- Schwartz–Bruhat functions are bounded, also after multiplication by the squared modulus. -/
theorem bruhat_bound {G : Kv → ℂ} (hG : Bruhat v G) :
    Continuous G ∧ ∃ C, ∀ x, ‖G x‖ ≤ C ∧ m x ^ 2 * ‖G x‖ ≤ C := by
  cases v with
  | inr p =>
    obtain ⟨hl,hc⟩ := hG
    have hcont := hl.continuous
    obtain ⟨C1,h1⟩ := hcont.bounded_above_of_compact_support hc
    have hc2 : HasCompactSupport (fun x => ((modulus F (.inr p) x ^ 2 : ℝ) : ℂ) * G x) := hc.mul_left
    have hcc : Continuous (fun x => ((modulus F (.inr p) x ^ 2 : ℝ) : ℂ) * G x) :=
      (Complex.continuous_ofReal.comp ((continuous_modulus (.inr p)).pow 2)).mul hcont
    obtain ⟨C2,h2⟩ := hcc.bounded_above_of_compact_support hc2
    refine ⟨hcont,max C1 C2,fun x => ⟨(h1 x).trans (le_max_left _ _),?_⟩⟩
    have := h2 x
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (by cases p; positivity)] at this
    exact this.trans (le_max_right _ _)
  | inl w =>
    obtain ⟨⟨L,lip⟩,est,_⟩ := d.arch_bruhat_estimates w hG
    obtain ⟨C0,h0⟩ := est 0
    obtain ⟨C1,h1⟩ := est (w.mult*2)
    refine ⟨lip.continuous,max C0 C1,fun x => ⟨?_,?_⟩⟩
    · simpa using (h0 x).trans (le_max_left _ _)
    · simp only [modulus,← pow_mul]
      exact (h1 x).trans (le_max_right _ _)

theorem continuous_cpow_modulus (z : ℂ) : Continuous (fun u : (Kv)ˣ => ((m u.val : ℝ) : ℂ)^z) :=
  (Complex.continuous_ofReal.comp ((continuous_modulus v).comp Units.continuous_val)).cpow continuous_const
    (fun u => Complex.ofReal_mem_slitPlane.mpr (by cases v <;> simp [modulus,u.ne_zero,pow_pos]))

omit [NeZero n] in
/-- Zeta integrals of test weights converge for every exponent. -/
theorem integrable_mellin_test {g : Weight v} (hg : TestWeight v g) {χ : (Kv)ˣ → ℂ} (hχ : Continuous χ)
    (z : ℂ) : Integrable (fun u => g u * χ u * ((m u.val : ℝ) : ℂ)^z) μ :=
  ((hg.continuous.mul hχ).mul (continuous_cpow_modulus v z)).integrable_of_hasCompactSupport
    (hg.1.mul_right.mul_right)

omit [NeZero n] in
/-- Zeta integrals of Schwartz–Bruhat functions converge on the critical strip. -/
theorem integrable_mellin_bruhat {G : Kv → ℂ} (hG : Bruhat v G) {χ : (Kv)ˣ → ℂ} (hχc : Continuous χ)
    (hχ1 : ∀ x, ‖χ x‖ = 1) {z : ℂ} (h0 : 0 < z.re) (h1 : z.re < 1) :
    Integrable (fun u : (Kv)ˣ => G u * χ u * ((m u.val : ℝ) : ℂ)^z) μ := by
  obtain ⟨hc,C,hC⟩ := d.bruhat_bound v hG
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0).1
  set σ := z.re
  let F0 (x : Kv) := min (m x ^ (-(1-σ))) (m x ^ (-(3-σ)))
  have hF : Integrable F0 dx := d.integrable_modulus_two_sided v (by linarith) (by linarith) (by linarith)
  have hg : Integrable (fun u : (Kv)ˣ => m u.val • F0 u.val) μ := ((d.lineMeasure_modulus v F0).1).mpr hF
  refine Integrable.mono' (hg.const_mul C) ?_ (Eventually.of_forall fun u => ?_)
  · exact (((hc.comp Units.continuous_val).mul hχc).mul (continuous_cpow_modulus v z)).aestronglyMeasurable
  have hm : 0 < m u.val := by cases v <;> simp [modulus,u.ne_zero,pow_pos]
  rw [norm_mul,norm_mul,hχ1,mul_one,Complex.norm_cpow_eq_rpow_re_of_pos hm,smul_eq_mul]
  have e1 : m u.val * m u.val ^ (-(1-σ)) = m u.val ^ σ := by
    calc m u.val * m u.val ^ (-(1-σ)) = m u.val ^ (1:ℝ) * m u.val ^ (-(1-σ)) := by rw [Real.rpow_one]
      _ = m u.val ^ ((1:ℝ) + -(1-σ)) := (Real.rpow_add hm _ _).symm
      _ = _ := by ring_nf
  have e2 : m u.val * m u.val ^ (-(3-σ)) = m u.val ^ σ / m u.val ^ 2 := by
    calc m u.val * m u.val ^ (-(3-σ)) = m u.val ^ (1:ℝ) * m u.val ^ (-(3-σ)) := by rw [Real.rpow_one]
      _ = m u.val ^ ((1:ℝ) + -(3-σ)) := (Real.rpow_add hm _ _).symm
      _ = m u.val ^ (σ - 2) := by ring_nf
      _ = _ := by rw [Real.rpow_sub hm,Real.rpow_two]
  have hs : 0 ≤ m u.val ^ σ := Real.rpow_nonneg hm.le _
  simp only [F0]
  rw [mul_min_of_nonneg _ _ hm.le,e1,e2,mul_min_of_nonneg _ _ hC0]
  refine le_min (mul_le_mul_of_nonneg_right (hC _).1 hs) ?_
  rw [mul_div_assoc']
  rw [le_div_iff₀ (by positivity)]
  calc ‖G u.val‖ * m u.val ^ σ * m u.val ^ 2 = (m u.val ^ 2 * ‖G u.val‖) * m u.val ^ σ := by ring
    _ ≤ C * m u.val ^ σ := mul_le_mul_of_nonneg_right (hC _).2 hs

omit [NeZero n] in
/-- The symmetric inner integral in Tate's proof of the local functional equation. -/
theorem tate_inner_symm (a b : Kv → ℂ) (ha : Integrable a dx) (hb : Integrable b dx) (t : Kv) :
    ∫ x, a x * d.hat v b (x*t) ∂dx = ∫ x, b x * d.hat v a (x*t) ∂dx := by
  let : (dx).IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  let ψ := d.character.localValue F v
  have hψ : Continuous ψ := d.character.continuous_localValue v
  have hi : Integrable (fun p : Kv × Kv => a p.1 * (b p.2 * ψ ((p.1*t)*p.2))) ((dx).prod dx) := by
    have h0 := ha.mul_prod hb
    refine h0.mono ?_ (Filter.Eventually.of_forall fun p => ?_)
    · exact (ha.aestronglyMeasurable.comp_fst).mul (hb.aestronglyMeasurable.comp_snd.mul
        (hψ.comp (by fun_prop)).aestronglyMeasurable)
    · simp only [norm_mul,Character.norm_localValue,ψ,mul_one,le_refl]
  simp only [hat]
  simp_rw [← integral_const_mul]
  rw [integral_integral_swap hi]
  congr 1; funext y; congr 1; funext x
  rw [show (y*t)*x = (x*t)*y by ring]; ring

theorem modulus_mul (x y : Kv) : m (x*y) = m x * m y := by
  cases v <;> simp [modulus,norm_mul,mul_pow]

theorem modulus_nonneg' (x : Kv) : 0 ≤ m x := by cases v <;> simp [modulus,pow_nonneg]

omit [NeZero n] in
/-- One half of Tate's argument: the product of zeta integrals unfolds to the symmetric inner integral. -/
theorem tate_unfold (a b : Kv → ℂ) (χ : (Kv)ˣ → ℂ) (hχ : ∀ x y, χ (x*y) = χ x * χ y)
    (hχ0 : ∀ x, χ x ≠ 0) (z : ℂ)
    (hZa : Integrable (fun u : (Kv)ˣ => a u * χ u * (m u : ℂ)^z) μ)
    (hZb : Integrable (fun u : (Kv)ˣ => d.hat v b u * (χ u)⁻¹ * (m u : ℂ)^(1-z)) μ) :
    (∫ u, a u * χ u * (m u : ℂ)^z ∂μ) * (∫ u, d.hat v b u * (χ u)⁻¹ * (m u : ℂ)^(1-z) ∂μ) =
      ∫ t, (χ t)⁻¹ * (m t : ℂ)^(1-z) * ∫ x, a x * d.hat v b (x*t) ∂dx ∂μ := by
  let : SecondCountableTopology (Kv)ˣ := Units.isEmbedding_val₀.secondCountableTopology
  let A := fun u : (Kv)ˣ => a u * χ u * (m u : ℂ)^z
  let B := fun u : (Kv)ˣ => d.hat v b u * (χ u)⁻¹ * (m u : ℂ)^(1-z)
  have hprod : Integrable (fun p : (Kv)ˣ × (Kv)ˣ => A p.1 * B p.2) ((μ).prod μ) := hZa.mul_prod hZb
  have hshear : Integrable (fun p : (Kv)ˣ × (Kv)ˣ => A p.1 * B (p.1*p.2)) ((μ).prod μ) := by
    have := (measurePreserving_prod_mul μ μ).integrable_comp hprod.aestronglyMeasurable
    exact this.mpr hprod
  have hpt (x t : (Kv)ˣ) : A x * B (x*t) =
      (χ t)⁻¹ * (m t : ℂ)^(1-z) * (((m x : ℝ) : ℂ) * (a x * d.hat v b (x.val*t.val))) := by
    simp only [A,B,hχ,Units.val_mul,modulus_mul v]
    rw [Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (modulus_nonneg' v _) (modulus_nonneg' v _)]
    have hm : ((m x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (modulus_ne_zero v x)
    have e : ((m x : ℝ) : ℂ)^z * ((m x : ℝ) : ℂ)^(1-z) = (m x : ℂ) := by
      rw [← Complex.cpow_add _ _ hm]; simp
    rw [mul_inv]
    calc _ = (χ x * (χ x)⁻¹) * ((m x : ℂ)^z * (m x : ℂ)^(1-z)) *
          ((χ t)⁻¹ * (m t : ℂ)^(1-z) * (a x * d.hat v b (x.val*t.val))) := by ring
      _ = _ := by rw [mul_inv_cancel₀ (hχ0 x), e]; ring
  calc (∫ u, A u ∂μ) * (∫ u, B u ∂μ) = ∫ x, ∫ t, A x * B (x*t) ∂μ ∂μ := by
        rw [← integral_mul_const]
        congr 1; funext x
        rw [← integral_const_mul,integral_mul_left_eq_self (fun t => A x * B t) x]
    _ = ∫ t, ∫ x, A x * B (x*t) ∂μ ∂μ := integral_integral_swap hshear
    _ = _ := by
        congr 1; funext t
        simp_rw [hpt]
        rw [integral_const_mul]
        congr 1
        have := (d.lineMeasure_modulus v (fun x => a x * d.hat v b (x*t.val))).2
        simpa only [Complex.real_smul] using this

omit [NeZero n] in
/-- Tate's symmetry: Z(a,χ,z) Z(b̂,χ⁻¹,1−z) is symmetric in a and b. -/
theorem tate_symmetry (a b : Kv → ℂ) (χ : (Kv)ˣ → ℂ) (hχ : ∀ x y, χ (x*y) = χ x * χ y)
    (hχ0 : ∀ x, χ x ≠ 0) (z : ℂ) (ha : Integrable a dx) (hb : Integrable b dx)
    (hZa : Integrable (fun u : (Kv)ˣ => a u * χ u * (m u : ℂ)^z) μ)
    (hZb : Integrable (fun u : (Kv)ˣ => b u * χ u * (m u : ℂ)^z) μ)
    (hZa' : Integrable (fun u : (Kv)ˣ => d.hat v a u * (χ u)⁻¹ * (m u : ℂ)^(1-z)) μ)
    (hZb' : Integrable (fun u : (Kv)ˣ => d.hat v b u * (χ u)⁻¹ * (m u : ℂ)^(1-z)) μ) :
    (∫ u, a u * χ u * (m u : ℂ)^z ∂μ) * (∫ u, d.hat v b u * (χ u)⁻¹ * (m u : ℂ)^(1-z) ∂μ) =
      (∫ u, b u * χ u * (m u : ℂ)^z ∂μ) * (∫ u, d.hat v a u * (χ u)⁻¹ * (m u : ℂ)^(1-z) ∂μ) := by
  rw [d.tate_unfold v a b χ hχ hχ0 z hZa hZb',d.tate_unfold v b a χ hχ hχ0 z hZb hZa']
  simp_rw [d.tate_inner_symm v a b ha hb]

omit [NeZero n] in
theorem hat_bruhat {G : Kv → ℂ} (hG : Bruhat v G) : Bruhat v (d.hat v G) := by
  cases v with
  | inl w => exact d.arch_hat_bruhat w hG
  | inr p => exact d.hat_finite_bruhat p hG

omit [NeZero n] in
theorem mellin_eq_integral (W χ : Weight v) (z : ℂ) :
    d.mellin v W χ z = ∫ u, W u * χ u * ((m u.val : ℝ) : ℂ)^z ∂μ :=
  (d.integral_lineMeasure v _).symm

omit [NeZero n] in
/-- The transform in Tate's equation is the additive Fourier transform of the zero extension. -/
theorem tate_hat_eq (g : Weight v) (y : Kv) :
    d.lineIntegral v (fun x => (m x.val : ℂ) * g x * d.character.localValue F v (x.val * y)) =
      d.hat v (extWeight v g) y := by
  unfold lineIntegral hat
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x = 0
  · simp [hx,extWeight]
  have hm : (m x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (modulus_ne_zero v (Units.mk0 x hx))
  simp only [ne_eq,hx,not_false_eq_true,dite_true,Units.val_mk0,extWeight]
  field_simp

/-- Tate's local functional equation in the form needed for Proposition 10.20: for a
continuous unitary character on the open critical strip, one constant serves for all
test weights and all Schwartz–Bruhat functions. -/
theorem exists_tateEquation (χ : Weight v) (hχm : ∀ x y, χ (x*y) = χ x * χ y) (hχc : Continuous χ)
    (hχ1 : ∀ x, ‖χ x‖ = 1) {z : ℂ} (h0 : 0 < z.re) (h1 : z.re < 1) :
    ∃ γ : ℂ, d.TateEquation v χ z γ ∧ ∀ G : Kv → ℂ, Bruhat v G →
      d.mellin v (fun y => d.hat v G y.val) (fun x => (χ x)⁻¹) (1-z) =
        γ * d.mellin v (fun u => G u.val) χ z := by
  let : (dx).IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  have hχ0 (x) : χ x ≠ 0 := by intro h; have := hχ1 x; simp [h] at this
  have hχ1' : χ 1 = 1 := by
    have := hχm 1 1; rw [one_mul] at this
    exact (mul_eq_left₀ (hχ0 1)).mp this.symm
  have hic : Continuous fun x => (χ x)⁻¹ := hχc.inv₀ hχ0
  have hin (x) : ‖(χ x)⁻¹‖ = 1 := by rw [norm_inv,hχ1,inv_one]
  have hre : 0 < (1-z).re := by simp; linarith
  have hre' : (1-z).re < 1 := by simp; linarith
  -- a bump with nonvanishing zeta integral
  let φ := fun u : (Kv)ˣ => χ u * ((m u.val : ℝ) : ℂ)^z
  have hφ : Continuous φ := hχc.mul (continuous_cpow_modulus v z)
  let U := {u : (Kv)ˣ | ‖φ u - 1‖ < 1/2}
  have hU : IsOpen U := isOpen_lt (continuous_norm.comp (hφ.sub continuous_const)) continuous_const
  have h1U : (1 : (Kv)ˣ) ∈ U := by
    have : m (1 : Kv) = 1 := by cases v <;> simp [modulus]
    simp [U,φ,this,hχ1']
  obtain ⟨b,hbc,hbk,hb0,hb1,hbU,hbt⟩ := exists_test_bump v hU 1 h1U
  let g₀ : Weight v := fun x => (1:ℂ) * (b x : ℂ)
  have hg₀ : TestWeight v g₀ := hbt 1
  have hZ0 : d.mellin v g₀ χ z ≠ 0 := by
    rw [mellin_eq_integral]
    have hpos : 0 < ∫ u, b u ∂μ := hbc.integral_pos_of_hasCompactSupport_nonneg_nonzero hbk hb0
      (by rw [hb1]; exact one_ne_zero)
    have hib : Integrable (fun u => ((b u : ℝ) : ℂ)) μ :=
      (Complex.continuous_ofReal.comp hbc).integrable_of_hasCompactSupport (hbk.comp_left Complex.ofReal_zero)
    have hI := d.integrable_mellin_test v hg₀ hχc z
    intro hZ
    have hdiff : ‖∫ u, g₀ u * χ u * ((m u.val : ℝ) : ℂ)^z ∂μ - ∫ u, ((b u : ℝ) : ℂ) ∂μ‖ ≤
        ∫ u, b u * (1/2) ∂μ := by
      rw [← integral_sub hI hib]
      refine norm_integral_le_of_norm_le ((hbc.mul continuous_const).integrable_of_hasCompactSupport
        hbk.mul_right) (Eventually.of_forall fun u => ?_)
      have : g₀ u * χ u * ((m u.val : ℝ) : ℂ)^z - b u = b u * (φ u - 1) := by simp only [g₀,φ]; ring
      rw [this,norm_mul,Complex.norm_real,Real.norm_of_nonneg (hb0 u)]
      by_cases hu : u ∈ U
      · exact mul_le_mul_of_nonneg_left (le_of_lt hu) (hb0 u)
      · simp [hbU u hu]
    rw [hZ,zero_sub,norm_neg,integral_complex_ofReal,Complex.norm_real,Real.norm_of_nonneg hpos.le,
      integral_mul_const] at hdiff
    linarith
  -- the constant
  let γ := d.mellin v (fun y => d.hat v (extWeight v g₀) y.val) (fun x => (χ x)⁻¹) (1-z) /
    d.mellin v g₀ χ z
  have key (G : Kv → ℂ) (hG : Bruhat v G) : d.mellin v (fun y => d.hat v G y.val) (fun x => (χ x)⁻¹) (1-z) =
      γ * d.mellin v (fun u => G u.val) χ z := by
    have hE := d.extWeight_bruhat v hg₀
    have hs := d.tate_symmetry v G (extWeight v g₀) χ hχm hχ0 z (hG.integrable d) (hE.integrable d)
      (d.integrable_mellin_bruhat v hG hχc hχ1 h0 h1) (d.integrable_mellin_bruhat v hE hχc hχ1 h0 h1)
      (d.integrable_mellin_bruhat v (d.hat_bruhat v hG) hic hin hre hre')
      (d.integrable_mellin_bruhat v (d.hat_bruhat v hE) hic hin hre hre')
    simp only [mellin_eq_integral,extWeight_unit] at hs ⊢
    simp only [γ,mellin_eq_integral]
    rw [mellin_eq_integral] at hZ0
    rw [div_mul_eq_mul_div,eq_div_iff hZ0]
    linear_combination -hs
  refine ⟨γ,fun g hg => ?_,key⟩
  have := key (extWeight v g) (d.extWeight_bruhat v hg)
  simp only [extWeight_unit] at this
  simp only [d.tate_hat_eq v g]
  exact this

end MetaplecticPoisson.Datum
