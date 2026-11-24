import MetaplecticSummation.Jacquet.FiniteShear
import MetaplecticSummation.Marginals.FrequencyTest
import Mathlib.Topology.LocallyConstant.Algebra

/-! The tested Jacquet identity of §10. The two exchanges of integrals use
different bounds, in the frequency and the determinant parameter respectively. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField MeasureTheory Filter Set
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n) (v : Place F)
local notation "K" => LocalField F v
local notation "dx" => selfDual F d.character v
local notation "ψ" => d.character.localValue F v
local notation "m" => modulus F v

private theorem integrable_tested_radon_frequency (Φ : d.schwartz v) (c : Kˣ) {ρ : K → ℂ}
    (hc : Continuous ρ) (hs : HasCompactSupport ρ) (hz : 0 ∉ tsupport ρ) :
    let R (y t : K) := (d.radonAt v Φ.val t).1 c y
    Integrable (fun z : K × K => (d.hat v (R z.1) z.2 * ρ z.2) * ψ (-z.1/c.val)) ((dx).prod dx) := by
  intro R
  let f := fun z : K × K => d.hat v (R z.1) z.2 * ρ z.2
  have hi : Integrable f ((dx).prod dx) :=
    d.integrable_radon_frequency_test v Φ (d.fourier v Φ) (d.fourier_apply v Φ) c hc hs hz
  have hp : Continuous (fun z : K × K => ψ (-z.1/c.val)) :=
    (d.character.continuous_localValue v).comp (continuous_fst.neg.div_const _)
  apply hi.norm.mono' (hi.aestronglyMeasurable.mul hp.aestronglyMeasurable)
  exact .of_forall fun z => by simp [f,norm_mul,d.character.norm_localValue]

/-- The weak Jacquet identity for a section satisfying the transverse line
identity and its uniform L¹ bound. The test is extended by zero across zero. -/
theorem jacquet_weak_of_lines (Φ : d.schwartz v) (c : Kˣ) {H : K → ℂ} {B : ℝ}
    (lines : ∀ t : K, let R := (d.radonAt v Φ.val t).1 c
      Integrable R dx ∧ (∫ y, R y * ψ (-y/c.val) ∂dx) = H t ∧ (∫ y, ‖R y‖ ∂dx) ≤ B)
    {ρ : K → ℂ} (hc : Continuous ρ) (hs : HasCompactSupport ρ) (hz : 0 ∉ tsupport ρ)
    (hi : Integrable (d.hat v ρ) dx) :
    d.lineIntegral v (fun u => d.jacquet v (d.fourier v Φ) (u^n*c) * ρ u.val) =
      (Real.sqrt (m (n:K)) : ℂ)⁻¹ * ∫ t, H t * d.hat v ρ t ∂dx := by
  letI : (dx).IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  letI : NullSingletonClass dx := d.selfDual_nullSingleton v
  let R (y t : K) := (d.radonAt v Φ.val t).1 c y
  let p (y : K) := ψ (-y/c.val)
  let L (y u : K) := (d.hat v (R y) u * ρ u) * p y
  let G (t y : K) := (R y t * d.hat v ρ t) * p y
  let s : ℂ := Real.sqrt (m (n:K))
  have hρ : Integrable ρ dx := hc.integrable_of_hasCompactSupport hs
  have rapid : RapidRadonValues R := (d.schwartz_radon_rapid v Φ).1.comp (fun y : K => (c,y))
    (continuous_const.prodMk continuous_id)
  have hL : Integrable (Function.uncurry L) ((dx).prod dx) := d.integrable_tested_radon_frequency v Φ c hc hs hz
  have cG : Continuous (Function.uncurry G) :=
    ((rapid.1.comp (f := Prod.swap) continuous_swap).mul ((d.continuous_hat v hρ).comp continuous_fst)).mul
      ((d.character.continuous_localValue v).comp (continuous_snd.neg.div_const _))
  have normG (t y : K) : ‖G t y‖ = ‖R y t‖ * ‖d.hat v ρ t‖ := by
    simp only [G,p,norm_mul,d.character.norm_localValue,mul_one]
  have hG : Integrable (Function.uncurry G) ((dx).prod dx) := by
    apply (integrable_prod_iff cG.aestronglyMeasurable).mpr
    constructor
    · apply Eventually.of_forall
      intro t
      exact ((lines t).1.norm.mul_const ‖d.hat v ρ t‖).mono'
        (cG.comp (f := fun y => (t,y)) (continuous_const.prodMk continuous_id)).aestronglyMeasurable
        (.of_forall fun y => (normG t y).le)
    · apply (hi.norm.const_mul B).mono' cG.aestronglyMeasurable.norm.integral_prod_right'
      filter_upwards with t
      change ‖∫ y, ‖G t y‖ ∂dx‖ ≤ _
      rw [Real.norm_of_nonneg (integral_nonneg fun y => norm_nonneg _)]
      simp_rw [normG,integral_mul_const]
      exact mul_le_mul_of_nonneg_right (lines t).2.2 (norm_nonneg _)
  have inner (y : K) : (∫ u, L y u ∂dx) = ∫ t, G t y ∂dx := by
    simp only [L,G,integral_mul_const]
    rw [d.hat_pair_swap v (f := R y) (rapid.1.comp (f := fun t => (y,t)) (continuous_const.prodMk continuous_id)) hc
      (rapid.integrable dx (d.integrable_local_inv_cube v) y) hρ]
  have outer (t : K) : (∫ y, G t y ∂dx) = H t * d.hat v ρ t := by
    simp only [G,mul_right_comm (R _ t) (d.hat v ρ t),integral_mul_const]
    rw [show (∫ y, R y t*p y ∂dx) = H t from (lines t).2.1]
  have hn : (n:K) ≠ 0 := by
    simpa only [map_natCast,map_zero] using (diagonal F v).injective.ne (Nat.cast_ne_zero.mpr (NeZero.ne n) : (n:F) ≠ 0)
  have hm : 0 < m (n:K) := by cases v <;> simp [modulus,hn,norm_pos_iff,pow_pos]
  have hsn : s ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos_of_pos hm).ne'
  apply (eq_inv_mul_iff_mul_eq₀ hsn).mpr
  calc
    s*d.lineIntegral v _ = ∫ u, ∫ y, L y u ∂dx ∂dx := by
      rw [lineIntegral,← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [(dx).ae_ne 0] with x hx
      let u := Units.mk0 x hx
      simp only [dif_pos hx]
      change s*(d.jacquet v (d.fourier v Φ) (u^n*c)*ρ x/(m u.val : ℂ)) = ∫ y, L y x ∂dx
      have hmul := d.jacquet_scaled_radon v Φ c u
      change s*d.jacquet v (d.fourier v Φ) (u^n*c) = (m u.val : ℂ)*∫ y, d.hat v (R y) x*p y ∂dx at hmul
      simp only [L,mul_right_comm (d.hat v _ x) (ρ x),integral_mul_const]
      rw [← mul_div_assoc,← mul_assoc,hmul]
      field_simp [Complex.ofReal_ne_zero.mpr (modulus_ne_zero v u)]
    _ = ∫ y, ∫ u, L y u ∂dx ∂dx := (integral_integral_swap hL).symm
    _ = ∫ y, ∫ t, G t y ∂dx ∂dx := by simp_rw [inner]
    _ = ∫ t, ∫ y, G t y ∂dx ∂dx := (integral_integral_swap hG).symm
    _ = _ := by simp_rw [outer]

/-- At every finite place the shear representative makes the weak formula
valid for every Schwartz section. -/
theorem finite_jacquet_weak (p : Prime F) (Φ : d.schwartz (.inr p))
    (c : (LocalField F (.inr p))ˣ) {ρ : LocalField F (.inr p) → ℂ}
    (hρ : Bruhat (.inr p) ρ) (hz : 0 ∉ tsupport ρ) :
    let vp : Place F := .inr p
    d.lineIntegral vp (fun u => d.jacquet vp (d.fourier vp Φ) (u^n*c) * ρ u.val) =
      (Real.sqrt (modulus F vp (n:LocalField F vp)) : ℂ)⁻¹ *
        ∫ t, d.kernelIntegral vp (d.jacquet vp Φ) c t * d.hat vp ρ t ∂selfDual F d.character vp := by
  let vp : Place F := .inr p
  obtain ⟨Ξ,_,hF,B,h⟩ := d.finite_jacquet_radon_representative p Φ
  have hi := Bruhat.integrable d (d.hat_finite_bruhat p hρ)
  obtain ⟨hl,hs⟩ := hρ
  have eqn := d.jacquet_weak_of_lines vp Ξ c (h c) hl.continuous hs hz hi
  simpa only [vp,hF] using eqn

section Finite
variable (p : Prime F)
local notation "vp" => (Sum.inr p : Place F)
local notation "L" => LocalField F vp
local notation "μ" => selfDual F d.character vp

omit [NeZero n] in
private theorem finite_test_at_one {A : Lˣ → ℂ} {g : L → ℂ}
    (hA : IsLocallyConstant A) (hg : IsLocallyConstant g)
    (h : ∀ ρ : L → ℂ, Bruhat vp ρ → 0 ∉ tsupport ρ →
      d.lineIntegral vp (fun u => A u * ρ u.val) = ∫ x, g x * ρ x ∂μ) :
    A 1 = g 1 := by
  letI : NontriviallyNormedField (p.adicCompletion F) := FinitePlace.nontriviallyNormedCompletion p
  letI : ProperSpace L := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace (p.adicCompletion F)
  letI : IsUltrametricDist L := inferInstanceAs (IsUltrametricDist (p.adicCompletion F))
  letI : (μ).IsAddHaarMeasure := (existsUnique_selfDual F d.character vp).exists.choose_spec.1
  have lc : IsLocallyConstant (fun u : Lˣ => (A u,‖u.val‖)) :=
    hA.prodMk (show IsLocallyConstant (fun u : (p.adicCompletion F)ˣ => ‖u.val‖) from locallyConstant_norm_units)
  obtain ⟨V,hV,hpre⟩ := Units.isEmbedding_val₀.isInducing.isOpen_iff.mp (lc {(A 1,(1:ℝ))})
  have hv : (1:L) ∈ V := by
    change (1:Lˣ) ∈ Units.val ⁻¹' V
    rw [hpre]
    simp
  have onV (u : Lˣ) (hu : u.val ∈ V) : A u = A 1 ∧ ‖u.val‖ = 1 := by
    change u ∈ Units.val ⁻¹' V at hu
    rw [hpre] at hu
    exact Prod.mk.inj hu
  have near := (show ∀ᶠ x : L in nhds 1, x ∈ V from hV.mem_nhds hv).and ((eventually_ne_nhds (one_ne_zero : (1:L) ≠ 0)).and (hg.eventually_eq 1))
  obtain ⟨r,hr,hU⟩ := Metric.mem_nhds_iff.mp near
  let S := Metric.closedBall (1:L) (r/2)
  have hS : IsClopen S := IsUltrametricDist.isClopen_closedBall _ (half_pos hr).ne'
  have hC : IsCompact S := isCompact_closedBall _ _
  have onS (x) (hx : x ∈ S) := hU (Metric.closedBall_subset_ball (half_lt_self hr) hx)
  let ρ : L → ℂ := S.indicator (fun _ => 1)
  have hsup : tsupport ρ ⊆ S := closure_minimal (fun x hx => by
    by_contra hn
    exact hx (indicator_of_notMem hn _)) hS.isClosed
  have hl : IsLocallyConstant ρ := (LocallyConstant.charFn ℂ hS).isLocallyConstant
  have eqn := h ρ ⟨hl,hC.of_isClosed_subset (isClosed_tsupport _) hsup⟩ (fun h => (onS 0 (hsup h)).2.1 rfl)
  have left (x : L) : (if hx : x ≠ 0 then A (Units.mk0 x hx) * ρ x / (modulus F vp x : ℂ) else 0) = A 1 * ρ x := by
    by_cases hx : x ∈ S
    · obtain ⟨hv,hn,_⟩ := onS x hx
      obtain ⟨ha,hm⟩ := onV (Units.mk0 x hn) hv
      rw [dif_pos hn,ha,show modulus F vp x = 1 from hm,Complex.ofReal_one,div_one]
    · simp only [ρ,indicator_of_notMem hx,mul_zero,zero_div,dite_eq_ite,ite_self]
  have right (x : L) : g x * ρ x = g 1 * ρ x := by
    by_cases hx : x ∈ S
    · rw [(onS x hx).2.2]
    · simp only [ρ,indicator_of_notMem hx,mul_zero]
  have el : d.lineIntegral vp (fun u => A u * ρ u.val) = A 1 * ∫ x, ρ x ∂μ := by
    rw [← integral_const_mul]
    exact integral_congr_ae (.of_forall left)
  rw [el] at eqn
  simp_rw [right,integral_const_mul] at eqn
  apply mul_right_cancel₀ _ eqn
  have hm := hS.isOpen.measure_ne_zero μ ⟨1,Metric.mem_closedBall_self (half_pos hr).le⟩
  have hpos : (μ).real S ≠ 0 := (ENNReal.toReal_pos hm hC.measure_ne_top).ne'
  simpa only [ρ,integral_indicator hS.isClosed.measurableSet,integral_const,measureReal_restrict_apply_univ,
    Complex.real_smul, mul_one] using Complex.ofReal_ne_zero.mpr hpos

/-- Proposition 10.8 at λ = 1, for every finite place and every Schwartz
section whose Jacquet integral is a compactly supported test weight. -/
theorem finite_jacquet_fourier_test (Φ : d.schwartz vp) (hw : TestWeight vp (d.jacquet vp Φ)) :
    d.jacquet vp (d.fourier vp Φ) = d.dualWeight vp (d.jacquet vp Φ) := by
  letI : (μ).IsAddHaarMeasure := (existsUnique_selfDual F d.character vp).exists.choose_spec.1
  funext c
  let H := d.kernelIntegral vp (d.jacquet vp Φ) c
  let s : ℂ := (Real.sqrt (modulus F vp (n:L)) : ℂ)⁻¹
  let A (u : Lˣ) := d.jacquet vp (d.fourier vp Φ) (u^n*c)
  have hA : IsLocallyConstant A := (d.locallyConstant_finite_jacquet p _).comp_continuous
    ((continuous_id.pow n).mul_const c)
  have hH := d.kernelIntegral_bruhat vp hw c
  have lc : IsLocallyConstant H := hH.1
  have hg : IsLocallyConstant (fun x => s*d.hat vp H x) :=
    (d.hat_finite_bruhat p hH).1.comp (fun t : ℂ => s*t)
  have h := d.finite_test_at_one p hA hg (by
    intro ρ hρ hz
    have he := d.finite_jacquet_weak p Φ c hρ hz
    have hc : IsLocallyConstant ρ := hρ.1
    have hs := d.hat_pair_swap vp lc.continuous hc.continuous (Bruhat.integrable d hH) (Bruhat.integrable d hρ)
    change d.lineIntegral vp (fun u => A u * ρ u.val) = s*(∫ t, H t*d.hat vp ρ t ∂μ) at he
    rw [he,← hs]
    simp only [mul_assoc,integral_const_mul])
  simpa only [A,H,one_pow,one_mul,s,hat,dualWeight,mul_comm (d.kernelIntegral vp _ c _) _] using h

end Finite
end MetaplecticPoisson.Datum
