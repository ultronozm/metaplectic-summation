import MetaplecticSummation.ArchimedeanRadon
import MetaplecticSummation.SchwartzSliceIntegral

/-! Schwartz estimates for integrals over affine lines in an open rapid chart. -/
noncomputable section
namespace MetaplecticPoisson
open MeasureTheory Set Filter
open scoped Topology ContDiff
open Classical

variable {E L : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedField L] [NormedAlgebra ℝ L] {U : Set E} {f : E → ℂ}

private theorem affine_line_deriv (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (z : E) (A : L →L[ℝ] E) (hz : ∀ t, z + A t ∈ U) (k : ℕ) (t : L) :
    iteratedFDeriv ℝ k (fun u => f (z + A u)) t =
      (iteratedFDeriv ℝ k f (z + A t)).compContinuousLinearMap (fun _ => A) := by
  let V := (fun y : E => z + y) ⁻¹' U
  have hV : IsOpen V := hU.preimage (continuous_const.add continuous_id)
  have hF : ContDiffOn ℝ ∞ (fun y : E => f (z+y)) V :=
    hf.comp ((contDiff_const.add contDiff_id).contDiffOn) (fun _ h => h)
  have pre : A ⁻¹' V = univ := eq_univ_of_forall hz
  have h := A.iteratedFDerivWithin_comp_right hF hV.uniqueDiffOn
    (by rw [pre]; exact uniqueDiffOn_univ) (hz t) (i := k) (by exact_mod_cast le_top)
  rw [pre,iteratedFDerivWithin_univ, iteratedFDerivWithin_eq_iteratedFDeriv hV.uniqueDiffOn
    ((hF.contDiffAt (hV.mem_nhds (hz t))).of_le (by exact_mod_cast le_top)) (hz t),
    iteratedFDeriv_comp_add_left] at h
  exact h

/-- A rapid chart integrated along affine lines gives a bounded Schwartz family.
The factors in the line integral may depend on the fiber and the output parameter.
The two geometric inequalities compare the fiber and determinant norms with the chart norm. -/
theorem schwartz_affine_line_integrals
    {P K : Type} [TopologicalSpace P] [NormedField K] [MeasurableSpace K] [BorelSpace K]
    [SecondCountableTopology K] (μ : Measure K) (e : K ≃+* L)
    (hint : Integrable (fun x : K => ((1+‖x‖)^3)⁻¹) μ)
    (hU : IsOpen U) (hf : rapidChart U f)
    (z : P → K → E) (A : P → L →L[ℝ] E) (c : P → K → ℂ) (D : P → ℝ)
    (hz : ∀ q, ContinuousOn (z q) {x | x ≠ 0}) (hc : ∀ q, ContinuousOn (c q) {x | x ≠ 0})
    (hD : Continuous D)
    (hA : ∀ q, ‖A q‖ ≤ D q) (hC : ∀ q x, x ≠ 0 → ‖c q x‖ ≤ D q)
    (hmem : ∀ q x, x ≠ 0 → ∀ t, z q x + A q t ∈ U)
    (hX : ∀ q x, x ≠ 0 → ∀ t, ‖x‖ ≤ ‖z q x + A q t‖)
    (hT : ∀ q x, x ≠ 0 → ∀ t, 1+‖t‖ ≤ D q * (1+‖z q x + A q t‖)) :
    SchwartzSliceFamily e (fun q t => ∫ x, if x = 0 then 0 else c q x * f (z q x + A q (e t)) ∂μ) := by
  classical
  let G (q : P) (x : K) (t : L) := if x = 0 then 0 else c q x * f (z q x + A q t)
  have smooth (q x) (hx : x ≠ 0) : ContDiff ℝ ∞ (fun t => f (z q x + A q t)) :=
    contDiff_iff_contDiffAt.mpr fun t =>
      (hf.1.contDiffAt (hU.mem_nhds (hmem q x hx t))).comp t
        (contDiff_const.add (A q).contDiff).contDiffAt
  have deriv (q x) (hx : x ≠ 0) (k t) : iteratedFDeriv ℝ k (G q x) t =
      c q x • (iteratedFDeriv ℝ k f (z q x + A q t)).compContinuousLinearMap (fun _ => A q) := by
    simp only [G, if_neg hx, ← smul_eq_mul]
    change iteratedFDeriv ℝ k (c q x • (fun u => f (z q x + A q u))) t = _
    rw [iteratedFDeriv_const_smul_apply, affine_line_deriv hU hf.1 _ _ (hmem q x hx)]
    exact (smooth q x hx).contDiffAt.of_le (by exact_mod_cast le_top)
  apply SchwartzSliceFamily.of_integral e G
  · intro q x
    by_cases hx : x = 0
    · simpa only [G,if_pos hx] using (contDiff_const : ContDiff ℝ ∞ (fun _ : L => (0 : ℂ)))
    · simpa only [G,if_neg hx] using (contDiff_const.mul (smooth q x hx) :
        ContDiff ℝ ∞ (fun t => c q x * f (z q x + A q t)))
  · intro q k t
    let V : Set K := {x | x ≠ 0}
    have hV : MeasurableSet V := (measurableSet_singleton 0).compl
    have hcon : ContinuousOn (fun x => iteratedFDeriv ℝ k f (z q x + A q t)) V := by
      have h := hf.1.continuousOn_iteratedFDerivWithin (m := k) (by exact_mod_cast le_top) hU.uniqueDiffOn
      apply (h.comp ((hz q).add continuousOn_const) (fun x hx => hmem q x hx t)).congr
      intro x hx
      exact (iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn
        ((hf.1.contDiffAt (hU.mem_nhds (hmem q x hx t))).of_le (by exact_mod_cast le_top)) (hmem q x hx t)).symm
    let B := ContinuousMultilinearMap.compContinuousLinearMapL (F := ℂ) (fun _ : Fin k => A q)
    have hm := (((hc q).smul (B.continuous.comp_continuousOn hcon)).congr
      (fun x hx => deriv q x hx k t)).aestronglyMeasurable (μ := μ) hV
    rw [← Measure.restrict_add_restrict_compl (μ := μ) (measurableSet_singleton (0 : K))]
    exact aestronglyMeasurable_add_measure_iff.mpr
      ⟨(continuousOn_singleton _ _).aestronglyMeasurable (measurableSet_singleton _), hm⟩
  · intro T hcomp k N
    obtain ⟨M,hM⟩ := hcomp.bddAbove_image hD.continuousOn
    let B := max 0 M
    have hB : 0 ≤ B := le_max_left ..
    obtain ⟨C,hC',H⟩ := rapidChart_derivative_polynomial hf k (3+N)
    let V := B * B^k * C * B^N
    have hV : 0 ≤ V := by dsimp [V]; positivity
    refine ⟨fun x => V*((1+‖x‖)^3)⁻¹,hint.const_mul _,fun q hq x t => ?_⟩
    by_cases hx : x = 0
    · simp only [G,if_pos hx]
      rw [iteratedFDeriv_fun_zero]
      simp only [Pi.zero_apply,norm_zero,zero_mul]
      positivity
    let u := z q x + A q t
    have hDB : D q ≤ B := (hM (mem_image_of_mem D hq)).trans (le_max_right ..)
    have hder : ‖iteratedFDeriv ℝ k (G q x) t‖ ≤
        B * B^k * ‖iteratedFDeriv ℝ k f u‖ := by
      rw [deriv q x hx, norm_smul]
      have h := (iteratedFDeriv ℝ k f u).norm_compContinuousLinearMap_le (fun _ : Fin k => A q)
      simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at h
      calc
        _ ≤ B * (‖iteratedFDeriv ℝ k f u‖ * ‖A q‖^k) :=
          mul_le_mul ((hC q x hx).trans hDB) h (norm_nonneg _) hB
        _ ≤ B * (‖iteratedFDeriv ℝ k f u‖ * B^k) := by
          gcongr
          exact (hA q).trans hDB
        _ = _ := by ring
    have ht : 1+‖t‖ ≤ B*(1+‖u‖) := (hT q x hx t).trans (mul_le_mul_of_nonneg_right hDB (by positivity))
    change _ ≤ V * ((1 + ‖x‖)^3)⁻¹
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    calc
      _ ≤ (B * B^k * ‖iteratedFDeriv ℝ k f u‖) * (B*(1+‖u‖))^N * (1+‖u‖)^3 := by
        gcongr
        exact hX q x hx t
      _ = B*B^k*(‖iteratedFDeriv ℝ k f u‖*(1+‖u‖)^(3+N))*B^N := by rw [pow_add,mul_pow]; ring
      _ ≤ V := by dsimp [V]; gcongr; exact H u (hmem q x hx t)

/-- The normalized Radon chart in unit-first coordinates, with either determinant sign. -/
theorem schwartz_normalized_radon_chart
    {K : Type} [NormedField K] [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]
    (μ : Measure K) (e : K ≃+* L) (he : Isometry e) (s : K) (hs : ‖s‖ = 1)
    (hint : Integrable (fun x : K => ((1+‖x‖)^3)⁻¹) μ)
    (f : L × L → ℂ) (hf : rapidChart {u | u.1 ≠ 0} f)
    (phase : Kˣ → Kˣ → ℂ) (hc : Continuous (Function.uncurry phase)) (hn : ∀ x a, ‖phase x a‖ = 1)
    (m : Kˣ → ℝ) (hm : Continuous m) (hm' : ∀ a, 0 < m a) :
    SchwartzSliceFamily e (fun (q : Kˣ × K) t =>
      (∫ x, if hx : x ≠ 0 then f (e x, e ((x*q.2+s*t)/q.1.val)) * phase (Units.mk0 x hx) q.1 else 0 ∂μ) /
        (m q.1 : ℂ)) := by
  let z (q : Kˣ × K) (x : K) : L × L := (e x, e (x*q.2/q.1.val))
  let A (q : Kˣ × K) : L →L[ℝ] L × L :=
    (0 : L →L[ℝ] L).prod (ContinuousLinearMap.lsmul ℝ L (e s / e q.1.val))
  let c (q : Kˣ × K) (x : K) := if hx : x ≠ 0 then phase (Units.mk0 x hx) q.1 / (m q.1 : ℂ) else 0
  let D (q : Kˣ × K) := 2 + ‖q.1.val‖ + ‖q.2‖ + ‖q.1.val‖⁻¹ + (m q.1)⁻¹
  have hD (q : Kˣ × K) : 2 + ‖q.1.val‖ + ‖q.2‖ ≤ D q := by
    dsimp [D]; linarith [inv_nonneg.mpr (hm' q.1).le,inv_nonneg.mpr (norm_nonneg q.1.val), norm_nonneg q.1.val,norm_nonneg q.2]
  have ha (q : Kˣ × K) : e q.1.val ≠ 0 := (map_ne_zero e).mpr q.1.ne_zero
  have norm_e := he.norm_map_of_map_zero e.map_zero
  have pos (q : Kˣ × K) (x : K) (t : L) :
      z q x + A q t = (e x, (e x * e q.2 + e s * t) / e q.1.val) := by
    ext <;> simp [z,A,ContinuousLinearMap.lsmul_apply,smul_eq_mul]
    ring
  have h := schwartz_affine_line_integrals μ e hint (isOpen_ne_fun continuous_fst continuous_const)
    hf z A c D (fun q => (he.continuous.prodMk
      (he.continuous.comp ((continuous_id.mul continuous_const).div_const _))).continuousOn)
    (by
      intro q
      rw [continuousOn_iff_continuous_restrict]
      let lift (x : {x : K // x ≠ 0}) := Units.mk0 x.val x.property
      have hl : Continuous lift := Units.isEmbedding_val₀.continuous_iff.mpr continuous_subtype_val
      exact ((hc.comp (hl.prodMk (continuous_const (y := q.1)))).div_const (m q.1 : ℂ)).congr
        (fun x => by simp [c,x.property,Function.uncurry,lift,Set.restrict])) (by
      apply Continuous.add
      · apply Continuous.add
        · exact ((continuous_const.add (Units.continuous_val.comp continuous_fst).norm).add continuous_snd.norm)
        · exact (Units.continuous_val.comp continuous_fst).norm.inv₀ fun q => norm_ne_zero_iff.mpr q.1.ne_zero
      · exact (hm.comp continuous_fst).inv₀ (fun q => (hm' q.1).ne'))
    (by
      intro q
      rw [show ‖A q‖ = ‖q.1.val‖⁻¹ by
        simp [A,ContinuousLinearMap.opNorm_prod, Prod.norm_def,norm_div,norm_e,hs,one_div]]
      dsimp [D]; linarith [norm_nonneg q.1.val,norm_nonneg q.2,inv_nonneg.mpr (hm' q.1).le])
    (by
      intro q x hx
      simp only [c,dif_pos hx,norm_div,hn,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hm' _),one_div]
      dsimp [D]; linarith [inv_nonneg.mpr (hm' q.1).le,inv_nonneg.mpr (norm_nonneg q.1.val), norm_nonneg q.1.val,norm_nonneg q.2])
    (fun q x hx t => by rw [pos]; exact (map_ne_zero e).mpr hx)
    (fun q x _ t => by rw [pos,Prod.norm_def, norm_e]; exact le_max_left ..) (by
      intro q x _ t
      rw [pos]
      let y := (e x * e q.2 + e s * t) / e q.1.val
      let r := max ‖e x‖ ‖y‖
      have eqn : e s*t = y*e q.1.val - e x*e q.2 := by dsimp [y]; field_simp; ring
      have ht : ‖t‖ ≤ r*(‖q.1.val‖+‖q.2‖) := by
        calc
          _ = ‖e s * t‖ := by rw [norm_mul,norm_e,hs,one_mul]
          _ ≤ ‖y * e q.1.val‖ + ‖e x * e q.2‖ := eqn ▸ norm_sub_le ..
          _ ≤ _ := by
            rw [norm_mul,norm_mul,norm_e q.1.val,norm_e q.2,mul_add]
            exact add_le_add (mul_le_mul_of_nonneg_right (le_max_right ..) (norm_nonneg _))
              (mul_le_mul_of_nonneg_right (le_max_left ..) (norm_nonneg _))
      change 1+‖t‖ ≤ D q * (1+r)
      have hr : 0 ≤ r := (norm_nonneg _).trans (le_max_left ..)
      nlinarith [hD q, mul_le_mul_of_nonneg_right (hD q) hr, norm_nonneg q.1.val,norm_nonneg q.2])
  convert h using 1
  funext q t
  rw [← integral_div]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x = 0
  · simp [hx]
  · simp [hx,c,pos,map_add,map_mul]; ring

end MetaplecticPoisson
