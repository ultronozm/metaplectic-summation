import MetaplecticSummation.Jacquet.Lines
import MetaplecticSummation.Jacquet.WeightIntegrability

/-! The finite-place shear estimate of §10. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField IsDedekindDomain MeasureTheory Filter Set Metric
open scoped Topology
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)
variable (p : Prime F)
local notation "vp" => (Sum.inr p : Place F)
private theorem ray_axis_cone {L : Type} [NontriviallyNormedField L] [ProperSpace L]
    {f : L → Lˣ → ℂ}
    (extn : HasFiniteRayExtension n (fun (u : Lˣ) (q : L × Lˣ) => (u.val^n*q.1,u^n*q.2))
      (fun q => f q.1 q.2)) (haxis : ∀ b, f 0 b = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : Lˣ) (y : L) (hy : y ≠ 0), C * ‖a.val‖ < ‖y‖ →
      f a.val (Units.mk0 y hy) = 0 := by
  letI : LocallyCompactSpace {x : L // x ≠ 0} :=
    (isOpen_ne_fun continuous_id (continuous_const (y := (0 : L)))).locallyCompactSpace
  letI : LocallyCompactSpace Lˣ := unitsHomeomorphNeZero.isOpenEmbedding.locallyCompactSpace
  obtain ⟨T,B,hT,hB,hs⟩ := compact_ray_shell (K := L) (NeZero.ne n)
  obtain ⟨E,hE,hval⟩ := extn
  let U := {q : L × Lˣ | E q = E (0,q.2)}
  have hop : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    intro q hq
    have hsnd : Continuous (fun w : L × Lˣ => ((0:L),w.2)) := continuous_const.prodMk continuous_snd
    filter_upwards [hE.locallyConstant.eventually_eq q,
      (hE.locallyConstant.comp_continuous hsnd).eventually_eq q] with w hw hw'
    exact hw.trans ((show E q = E (0,q.2) from hq).trans hw'.symm)
  obtain ⟨V,W,hV,_,h0,hW,hVW⟩ := generalized_tube_lemma
    (isCompact_singleton (x := (0:L))) (hT.image continuous_fst) hop (by
      rintro ⟨z,b⟩ ⟨hz,_⟩
      obtain rfl : z = 0 := hz
      rfl)
  obtain ⟨δ,hδ,hd⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds (h0 rfl))
  refine ⟨B / δ,div_pos hB hδ,?_⟩
  intro a y hy h
  let b := Units.mk0 y hy
  obtain ⟨q,u,hq,he,_,hh⟩ := hs b 0 (by simp)
  have eb := congrArg Prod.fst he
  change u^n * q.1 = b at eb
  have hu : 0 < ‖u.val‖^n := pow_pos (norm_pos_iff.mpr u.ne_zero) _
  let z := a.val / u.val^n
  have hz : z ∈ ball 0 δ := by
    rw [mem_ball_zero_iff,norm_div,norm_pow,div_lt_iff₀ hu]
    change ‖y‖ ≤ B * ‖u.val‖^n at hh
    have H := h.trans_le hh
    rw [div_mul_eq_mul_div,div_lt_iff₀ hδ] at H
    exact (mul_lt_mul_iff_right₀ hB).mp (by convert H using 1; ring)
  have eqn : E (z,q.1) = E (0,q.1) := hVW (show (z,q.1) ∈ V ×ˢ W from ⟨hd hz,hW ⟨q,hq,rfl⟩⟩)
  have hv := congrFun eqn u.val
  rw [hval,hval] at hv
  change (‖u.val‖ : ℂ)^(n-1) * f (u.val^n*z) (u^n*q.1) =
    (‖u.val‖ : ℂ)^(n-1) * f (u.val^n*(0 : L)) (u^n*q.1) at hv
  rw [eb,mul_zero,haxis,mul_zero,show u.val^n*z = a.val by
    dsimp [z]; field_simp] at hv
  exact (mul_eq_zero.mp hv).resolve_left (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr
    (norm_ne_zero_iff.mpr u.ne_zero)))

local notation "Kv" => LocalField F vp

/-- A section vanishing on the vertical axis vanishes on an entire cone about
that axis, uniformly over all scales. -/
theorem finite_axis_cone (Φ : d.schwartz vp) (haxis : ∀ b : Kvˣ, Φ.val.2 0 b = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : Kvˣ) (y : Kv), C * ‖a.val‖ < ‖y‖ → Φ.val.1 a y = 0 := by
  let K := p.adicCompletion F
  letI : NontriviallyNormedField K := FinitePlace.nontriviallyNormedCompletion p
  letI : ProperSpace K := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace _
  obtain ⟨C,hC,H⟩ := ray_axis_cone (L := K) (d.finite_schwartz_rayExtensions p Φ).2 haxis
  refine ⟨C,hC,?_⟩
  intro a y h
  have hy : y ≠ 0 := norm_pos_iff.mp ((mul_pos hC (norm_pos_iff.mpr a.ne_zero)).trans h)
  let b := Units.mk0 y hy
  change Φ.val.1 a b.val = 0
  rw [d.schwartz_glues vp Φ a b,show Φ.val.2 a.val b = 0 from H a y hy h,mul_zero]

local notation "dx" => selfDual F d.character vp

/-- Integrating a section supported off a cone about the vertical axis
gains one power of the modulus of the first coordinate. -/
theorem finite_axis_slice_bound (Φ : d.schwartz vp) (haxis : ∀ b : Kvˣ, Φ.val.2 0 b = 0) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ a : Kvˣ,
      (∫ y, ‖Φ.val.1 a y‖ ∂dx) ≤ D * ‖a.val‖^(1 / (n : ℝ)) := by
  letI : NontriviallyNormedField (p.adicCompletion F) := FinitePlace.nontriviallyNormedCompletion p
  letI : NontriviallyNormedField Kv := FinitePlace.nontriviallyNormedCompletion p
  letI : LocallyCompactSpace Kv := inferInstanceAs (LocallyCompactSpace (p.adicCompletion F))
  letI : ProperSpace Kv := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace (p.adicCompletion F)
  letI : (dx).IsAddHaarMeasure := (existsUnique_selfDual F d.character vp).exists.choose_spec.1
  obtain ⟨C,hC,hcone⟩ := d.finite_axis_cone p Φ haxis
  obtain ⟨M,hM,hg⟩ := d.finite_vertical_growth p Φ
  let S := closedBall (0:Kv) C
  have hS : MeasurableSet S := measurableSet_closedBall
  have hfin : (dx) S ≠ ⊤ := (isCompact_closedBall (0:Kv) C).measure_lt_top.ne
  refine ⟨(dx).real S * M,mul_nonneg (measureReal_nonneg) hM,?_⟩
  intro a
  let r := ‖a.val‖
  have hr : 0 < r := norm_pos_iff.mpr a.ne_zero
  let m := M / r^(growthExponent n)
  have bound (t : Kv) : ‖Φ.val.1 a (a.val*t)‖ ≤ S.indicator (fun _ => m) t := by
    by_cases ht : t ∈ S
    · rw [indicator_of_mem ht]
      exact (le_div_iff₀ (Real.rpow_pos_of_pos hr _)).mpr (hg a _)
    · rw [indicator_of_notMem ht,hcone,norm_zero]
      rw [norm_mul,mul_comm C]
      exact mul_lt_mul_of_pos_left (lt_of_not_ge (by simpa only [S,mem_closedBall_zero_iff] using ht)) hr
  have hm : Integrable (S.indicator fun _ => m) dx :=
    (integrable_indicator_iff hS).mpr (integrableOn_const hfin)
  have H := integral_mono_of_nonneg (μ := dx) (.of_forall (fun t => norm_nonneg (Φ.val.1 a (a.val*t))))
    hm (.of_forall bound)
  rw [integral_indicator_const m hS,smul_eq_mul] at H
  have eqn := d.integral_local_mul vp a (fun y => (‖Φ.val.1 a y‖ : ℂ))
  dsimp only [modulus] at eqn
  rw [eq_div_iff (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr a.ne_zero))] at eqn
  simp only [integral_complex_ofReal,← Complex.ofReal_mul,Complex.ofReal_inj] at eqn
  change (∫ t, ‖Φ.val.1 a (a.val*t)‖ ∂dx) * r = _ at eqn
  rw [← eqn]
  apply (mul_le_mul_of_nonneg_right H hr.le).trans_eq
  have hn : (0:ℝ) < n := by exact_mod_cast NeZero.pos n
  have he : 1 - growthExponent n = 1 / n := by
    rw [growthExponent,Nat.cast_sub (NeZero.one_le : 1 ≤ n),Nat.cast_one]
    field_simp
    ring
  dsimp only [m]
  rw [← he,Real.rpow_sub hr,Real.rpow_one]
  ring

/-- The finite-place estimate of the shear-integrability lemma, for the
paper's third normalized difference and every real decay exponent A ≥ 0. -/
theorem finite_shear_bound (u : Kv) {g : d.Operators vp} (hg : d.IsUpper vp u g)
    (Φ : d.schwartz vp) {A : ℝ} (hA : 0 ≤ A) :
    let Ξ := (d.jacquetDifference vp u g)^[3] Φ
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : Kvˣ,
      (∫ y, ‖Ξ.val.1 a y‖ ∂dx) ≤ C * min (‖a.val‖^(1/(n:ℝ))) (‖a.val‖^(-A)) := by
  intro Ξ
  have haxis (b : Kvˣ) : Ξ.val.2 0 b = 0 := by
    exact d.jacquetDifference_axis vp u hg _ b
  obtain ⟨D,hD,H⟩ := d.finite_axis_slice_bound p Ξ haxis
  obtain ⟨S,hS,hout⟩ := (d.finite_germs p Ξ).2.1
  obtain ⟨R,hR⟩ := hS.isBounded.exists_norm_le
  let e := 1 / (n:ℝ)
  let B := (max 1 R)^(e+A)
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hB : 1 ≤ B := Real.one_le_rpow (le_max_left ..) (add_nonneg he hA)
  refine ⟨D*B,mul_nonneg hD (zero_le_one.trans hB),?_⟩
  intro a
  let r := ‖a.val‖
  have hr : 0 < r := norm_pos_iff.mpr a.ne_zero
  by_cases ha : r ≤ R
  · rw [mul_min_of_nonneg _ _ (mul_nonneg hD (zero_le_one.trans hB)),le_min_iff]
    refine ⟨(H a).trans (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hD hB) (Real.rpow_nonneg hr.le _)),?_⟩
    apply (H a).trans
    rw [Real.rpow_neg hr.le,← div_eq_mul_inv,le_div_iff₀ (Real.rpow_pos_of_pos hr _),mul_assoc,← Real.rpow_add hr]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hr.le (ha.trans (le_max_right ..)) (add_nonneg he hA)) hD
  · have hz (y : Kv) : Ξ.val.1 a y = 0 := by
      have hn : (a.val,y) ∉ S := by
        intro hin
        exact ha ((le_max_left ‖a.val‖ ‖y‖).trans (hR (a.val,y) hin))
      have h := (hout (a.val,y) hn).1
      simpa only [xChart,dif_pos a.ne_zero,Units.mk0_val] using h
    simp_rw [hz,norm_zero,integral_zero]
    exact mul_nonneg (mul_nonneg hD (zero_le_one.trans hB))
      (le_min (Real.rpow_nonneg hr.le _) (Real.rpow_nonneg hr.le _))

/-- Finite-place decay of every Jacquet weight, at zero and infinity. -/
theorem finite_jacquet_decay (Φ : d.schwartz vp) {A : ℝ} (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : Kvˣ,
      ‖d.jacquet vp Φ a‖ ≤ C * min (‖a.val‖^(1/(n:ℝ))) (‖a.val‖^(-A)) := by
  obtain ⟨u,hu⟩ := d.character.nontrivial_localValue vp
  obtain ⟨g,hg⟩ := (d.exists_upper vp u).exists
  let Ξ := (d.jacquetDifference vp u g)^[3] Φ
  obtain ⟨C,hC,H⟩ := d.finite_shear_bound p u hg Φ hA
  refine ⟨C,hC,fun a => ?_⟩
  rw [← (d.jacquet_difference_iterate vp u hu hg 3 Φ).1]
  change ‖∫ y, Ξ.val.1 a y * d.character.localValue F vp (-y/a.val) ∂dx‖ ≤ _
  apply (norm_integral_le_integral_norm _).trans
  simpa only [norm_mul,d.character.norm_localValue,mul_one] using H a

omit [NeZero n] in
private theorem finite_integrable_min_rpow {e : ℝ} (he : 0 < e) :
    Integrable (fun x : Kvˣ => min (‖x.val‖^e) (‖x.val‖^(-e))) (d.lineMeasure vp) := by
  letI : NontriviallyNormedField (p.adicCompletion F) := FinitePlace.nontriviallyNormedCompletion p
  letI : ProperSpace Kv := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace (p.adicCompletion F)
  letI : SecondCountableTopology Kvˣ := Units.isEmbedding_val₀.secondCountableTopology
  obtain ⟨c,hc,hc'⟩ := NormedField.exists_norm_lt_one (p.adicCompletion F)
  exact integrable_units_min_rpow (d.lineMeasure vp) (Units.mk0 c (norm_pos_iff.mp hc)) hc' he

/-- Absolute integrability of every finite Jacquet weight for d×c. -/
theorem integrable_finite_jacquet (Φ : d.schwartz vp) :
    Integrable (d.jacquet vp Φ) (d.lineMeasure vp) := by
  have he : 0 < 1 / (n : ℝ) := one_div_pos.mpr (by exact_mod_cast NeZero.pos n)
  obtain ⟨C,_,H⟩ := d.finite_jacquet_decay p Φ he.le
  exact ((d.finite_integrable_min_rpow p he).const_mul C).mono'
    (d.continuous_jacquet vp Φ).aestronglyMeasurable (.of_forall H)

/-- The third shear difference has absolutely integrable X-chart for d×x dy. -/
theorem integrable_finite_shear (u : Kv) {g : d.Operators vp} (hg : d.IsUpper vp u g)
    (Φ : d.schwartz vp) :
    let Ξ := (d.jacquetDifference vp u g)^[3] Φ
    Integrable (Function.uncurry Ξ.val.1) ((d.lineMeasure vp).prod dx) := by
  intro Ξ
  letI : (dx).IsAddHaarMeasure := (existsUnique_selfDual F d.character vp).exists.choose_spec.1
  have hc : Continuous (Function.uncurry Ξ.val.1) := (d.locallyConstant_finite_schwartz p Ξ).1.continuous
  apply (integrable_prod_iff hc.aestronglyMeasurable).mpr
  refine ⟨.of_forall (d.integrable_jacquet_slice vp Ξ),?_⟩
  have he : 0 < 1 / (n : ℝ) := one_div_pos.mpr (by exact_mod_cast NeZero.pos n)
  obtain ⟨C,_,H⟩ := d.finite_shear_bound p u hg Φ he.le
  apply ((d.finite_integrable_min_rpow p he).const_mul C).mono' hc.aestronglyMeasurable.norm.integral_prod_right'
  filter_upwards with a
  rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
  exact H a

/-- Every finite-place Schwartz section has a representative giving the same
two Jacquet weights and satisfying the absolutely convergent Radon identity. -/
theorem finite_jacquet_radon_representative (Φ : d.schwartz vp) :
    ∃ Ξ : d.schwartz vp, d.jacquet vp Ξ = d.jacquet vp Φ ∧
      d.jacquet vp (d.fourier vp Ξ) = d.jacquet vp (d.fourier vp Φ) ∧
      ∃ B : ℝ, ∀ (c : Kvˣ) (t : Kv),
        let R := (radon n (d.symbol vp) (modulus F vp) dx Ξ.val t).1 c
        Integrable R dx ∧ (∫ y, R y * d.character.localValue F vp (-y/c.val) ∂dx) =
          d.kernelIntegral vp (d.jacquet vp Φ) c t ∧ (∫ y, ‖R y‖ ∂dx) ≤ B := by
  obtain ⟨u,hu⟩ := d.character.nontrivial_localValue vp
  obtain ⟨g,hg⟩ := (d.exists_upper vp u).exists
  let Ξ := (d.jacquetDifference vp u g)^[3] Φ
  obtain ⟨hJ,hF⟩ := d.jacquet_difference_iterate vp u hu hg 3 Φ
  refine ⟨Ξ,hJ,hF,∫ z, ‖Ξ.val.1 z.1 z.2‖ ∂((d.lineMeasure vp).prod dx),fun c t => ?_⟩
  simpa only [← hJ] using d.jacquet_radon_lines vp Ξ (d.integrable_finite_shear p u hg Φ) c t

end MetaplecticPoisson.Datum
