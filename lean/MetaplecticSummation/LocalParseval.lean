import MetaplecticSummation.FourierDifferences
import MetaplecticSummation.FiniteFourierInversion
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.CompactlySupported

/-! Polarization of the local self-dual normalization and Fourier inversion on test functions. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open MeasureTheory NumberField ComplexConjugate CompactlySupported
open scoped ENNReal InnerProductSpace
variable {F : Type} [Field F] [NumberField F] {n : ℕ} (d : Datum F n) (v : Place F)
local notation "K" => LocalField F v
local notation "dxᵥ" => selfDual F d.character v

private theorem eLpNorm_hat (f : C_c(K, ℂ)) : eLpNorm (d.hat v f) 2 dxᵥ = eLpNorm f 2 dxᵥ := by
  have hp := (existsUnique_selfDual F d.character v).exists.choose_spec.2 f f.continuous f.hasCompactSupport
  letI : (dxᵥ).IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
        (d.continuous_hat v f.integrable).aestronglyMeasurable,
      eLpNorm_eq_lintegral_rpow_enorm_toReal (f := ⇑f) (by norm_num) (by norm_num) f.continuous.aestronglyMeasurable]
  simp only [ ENNReal.toReal_ofNat, ENNReal.rpow_ofNat]
  simpa only [hat, mul_comm] using! congrArg (fun a : ℝ≥0∞ => a ^ ((1:ℝ)/2)) hp

/-- For the self-dual measure the Fourier integral distinguishes continuous
compactly supported functions pointwise. -/
theorem hat_injective_compact (f g : C_c(K, ℂ)) (h : d.hat v f = d.hat v g) : f = g := by
  letI : (dxᵥ).IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  have hz : d.hat v (f-g : C_c(K,ℂ)) = 0 := by
    funext y
    simp only [hat,CompactlySupportedContinuousMap.sub_apply,sub_mul,Pi.zero_apply]
    rw [integral_sub (d.integrable_phase v f.integrable y) (d.integrable_phase v g.integrable y)]
    exact sub_eq_zero.mpr (congrFun h y)
  have he := (d.eLpNorm_hat v (f-g)).symm
  rw [hz,eLpNorm_zero] at he
  have ae := (eLpNorm_eq_zero_iff (by norm_num : (2:ℝ≥0∞) ≠ 0)).mp he
  have eqn := ((f-g).continuous.ae_eq_iff_eq (μ := dxᵥ) continuous_zero).mp ae
  ext y
  exact sub_eq_zero.mp (congrFun eqn y)

private theorem compact_hat_memLp (f : C_c(K, ℂ)) : MemLp (d.hat v f) 2 dxᵥ := by
  letI : (dxᵥ).IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  exact (d.eLpNorm_hat v f).trans_lt (f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport)

/-- Send a compactly supported continuous test to its Fourier integral in L². -/
private def compactFourierL2 : C_c(K, ℂ) →ₗ[ℂ] Lp ℂ 2 dxᵥ := by
  letI : (dxᵥ).IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  let mem := d.compact_hat_memLp v
  refine { toFun := fun f => (mem f).toLp _
           map_add' := ?_, map_smul' := ?_ }
  · intro f g
    apply Lp.ext
    filter_upwards [(mem (f+g)).coeFn_toLp, Lp.coeFn_add ((mem f).toLp _) ((mem g).toLp _),
      (mem f).coeFn_toLp,(mem g).coeFn_toLp] with y a b c h
    rw [a,b,Pi.add_apply,c,h]
    simp only [hat,CompactlySupportedContinuousMap.add_apply,add_mul]
    exact integral_add (d.integrable_phase v f.integrable y) (d.integrable_phase v g.integrable y)
  · intro a f
    apply Lp.ext
    filter_upwards [(mem (a • f)).coeFn_toLp, Lp.coeFn_smul a ((mem f).toLp _), (mem f).coeFn_toLp] with y h l m
    simp only [RingHom.id_apply] at *
    rw [h,l,Pi.smul_apply,m]
    simp [hat, mul_assoc, integral_const_mul, smul_eq_mul]

private def compactL2 : C_c(K, ℂ) →ₗ[ℂ] Lp ℂ 2 dxᵥ := by
  letI : (dxᵥ).IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  have mem (f : C_c(K, ℂ)) : MemLp f 2 dxᵥ := f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport
  exact { toFun := fun f => (mem f).toLp _, map_add' := fun f g => MemLp.toLp_add (mem f) (mem g)
          map_smul' := fun a f => MemLp.toLp_const_smul a (mem f) }

/-- Parseval's identity for two compactly supported tests, with the paper's character and measure. -/
theorem hat_parseval (f g : C_c(K, ℂ)) :
    (∫ y, conj (d.hat v f y) * d.hat v g y ∂dxᵥ) = ∫ x, conj (f x) * g x ∂dxᵥ := by
  letI : (dxᵥ).IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  let A := d.compactFourierL2 v
  let B := d.compactL2 v
  have hn (h : C_c(K, ℂ)) : ‖A h‖ = ‖B h‖ := by
    simp only [A,B,compactFourierL2,compactL2,LinearMap.coe_mk,AddHom.coe_mk,Lp.norm_toLp,d.eLpNorm_hat]
  have hinner : ⟪A f, A g⟫_ℂ = ⟪B f, B g⟫_ℂ := by
    simp only [inner_eq_sum_norm_sq_div_four, ← map_add, ← map_sub, ← map_smul, hn]
  have aeA (h : C_c(K, ℂ)) : ⇑(A h) =ᵐ[dxᵥ] d.hat v h := (d.compact_hat_memLp v h).coeFn_toLp
  have aeB (h : C_c(K, ℂ)) : ⇑(B h) =ᵐ[dxᵥ] ⇑h := (h.continuous.memLp_of_hasCompactSupport h.hasCompactSupport (μ := dxᵥ) (p := 2)).coeFn_toLp
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def] at hinner
  convert hinner using 1 <;> apply integral_congr_ae
  · filter_upwards [aeA f, aeA g] with x hf hg
    simp [hf,hg, RCLike.inner_apply,mul_comm]
  · filter_upwards [aeB f, aeB g] with x hf hg
    simp [hf,hg, RCLike.inner_apply,mul_comm]

private theorem localValue_neg_conj (x : K) :
    d.character.localValue F v (-x) = conj (d.character.localValue F v x) := by
  apply mul_left_cancel₀ (a := d.character.localValue F v x)
    (by intro h; have := d.character.norm_localValue v x; simp [h] at this)
  rw [← d.character.localValue_add,add_neg_cancel,d.character.localValue_zero,Complex.mul_conj',
    d.character.norm_localValue]
  simp

private theorem compact_hat_pair [LocallyCompactSpace K] [SecondCountableTopology K] (f g : C_c(K, ℂ)) :
    (∫ x, d.hat v f x * d.hat v g x ∂dxᵥ) = ∫ x, f (-x) * g x ∂dxᵥ := by
  letI : (dxᵥ).IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  let h : C_c(K, ℂ) :=
    { toFun := fun x => conj (f (-x))
      continuous_toFun := Complex.continuous_conj.comp (f.continuous.comp continuous_neg)
      hasCompactSupport' := (f.hasCompactSupport.comp_homeomorph (Homeomorph.neg K)).comp_left (map_zero _) }
  have happ (x : K) : h x = conj (f (-x)) := rfl
  have hh (y : K) : conj (d.hat v h y) = d.hat v f y := by
    rw [hat,← integral_conj,hat,← integral_neg_eq_self (fun t : K => f t * d.character.localValue F v (y*t))]
    apply integral_congr_ae
    filter_upwards with x
    simp [happ,mul_neg,d.localValue_neg_conj v]
  have H := d.hat_parseval v h g
  simp_rw [hh] at H
  simpa [happ] using H

/-- Plancherel on compact tests implies pointwise inversion whenever the compact tests
with integrable transforms distinguish continuous functions. -/
theorem hat_hat_of_separating_tests [LocallyCompactSpace K] [SecondCountableTopology K] [SFinite dxᵥ]
    (separate : ∀ a b : K → ℂ, Continuous a → Continuous b →
      (∀ p : C_c(K, ℂ), Integrable (d.hat v p) dxᵥ →
        (∫ x, p x * a x ∂dxᵥ) = ∫ x, p x * b x ∂dxᵥ) → a = b)
    {f : K → ℂ} (hf : Continuous f) (hi : Integrable f dxᵥ) (hi' : Integrable (d.hat v f) dxᵥ) :
    d.hat v (d.hat v f) = fun x => f (-x) := by
  letI : (dxᵥ).IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  have reflect (a b : K → ℂ) : (∫ x, a (-x) * b x ∂dxᵥ) = ∫ x, a x * b (-x) ∂dxᵥ := by
    simpa only [neg_neg] using integral_neg_eq_self (μ := dxᵥ) (fun x : K => a x * b (-x))
  have compactInv (g : C_c(K, ℂ)) (hg : Integrable (d.hat v g) dxᵥ) :
      d.hat v (d.hat v g) = fun x => g (-x) := by
    apply separate _ _ (d.continuous_hat v hg) (g.continuous.comp continuous_neg)
    intro p _
    exact ((d.hat_pair_swap v (f := p) p.continuous (d.continuous_hat v g.integrable) p.integrable hg).symm.trans
      (d.compact_hat_pair v p g)).trans (reflect p g)
  apply separate _ _ (d.continuous_hat v hi') (hf.comp continuous_neg)
  intro p hp
  calc
    _ = ∫ x, d.hat v p x * d.hat v f x ∂dxᵥ :=
      (d.hat_pair_swap v p.continuous (d.continuous_hat v hi) p.integrable hi').symm
    _ = ∫ x, d.hat v (d.hat v p) x * f x ∂dxᵥ :=
      (d.hat_pair_swap v (d.continuous_hat v p.integrable) hf hp hi).symm
    _ = _ := by rw [compactInv p hp]; exact reflect p f

end MetaplecticPoisson.Datum
