import MetaplecticSummation.Marginals.DifferenceConvergence
import MetaplecticSummation.ArchimedeanRadon

/-! Uniform bounds in the transverse coordinate for the subtracted Archimedean
integrand in Appendix A. -/
noncomputable section
namespace MetaplecticPoisson
open NumberField Set MeasureTheory
open scoped ContDiff
open Classical

private theorem rapidChart_horizontal_difference {L : Type} [NormedField L] [NormedAlgebra ℝ L]
    {g : L × L → ℂ} (hg : rapidChart {p : L × L | p.2 ≠ 0} g) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x z y : L), y ≠ 0 →
      ‖g (x,y)-g (z,y)‖ ≤ C/((1+‖y‖)^j)*‖x-z‖ := by
  obtain ⟨C,hC,H⟩ := rapidChart_derivative_polynomial hg 1 j
  refine ⟨C,hC,fun x z y hy => ?_⟩
  let S : Set (L × L) := univ ×ˢ {y}
  have hs : Convex ℝ S := (convex_univ : Convex ℝ (univ : Set L)).prod (convex_singleton y)
  have hu : IsOpen {p : L × L | p.2 ≠ 0} := isOpen_ne_fun continuous_snd continuous_const
  have hd (p : L × L) (hp : p ∈ S) : DifferentiableAt ℝ g p := by
    have hpy : p.2 = y := hp.2
    exact (hg.1.contDiffAt (hu.mem_nhds (hpy ▸ hy : p.2 ≠ 0))).differentiableAt (by simp)
  have bound (p : L × L) (hp : p ∈ S) : ‖fderiv ℝ g p‖ ≤ C/((1+‖y‖)^j) := by
    have hpy : p.2 = y := hp.2
    have hb := H p (hpy ▸ hy : p.2 ≠ 0)
    rw [norm_iteratedFDeriv_one] at hb
    apply (le_div_iff₀ (by positivity)).mpr
    apply le_trans _ hb
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact pow_le_pow_left₀ (by positivity) (add_le_add_right (hpy ▸ (le_max_right ‖p.1‖ ‖p.2‖)) 1) _
  have h := hs.norm_image_sub_le_of_norm_fderiv_le hd bound (x := (z,y)) (y := (x,y)) ⟨mem_univ _,rfl⟩ ⟨mem_univ _,rfl⟩
  simpa [Prod.norm_def] using h

namespace Datum
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n) (w : InfinitePlace F)
local notation "v" => (Sum.inl w : Place F)
local notation "K" => w.Completion

theorem arch_test_horizontal_difference {f : Charts K} (hf : f ∈ d.testSet v) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x z : K) (y : Kˣ),
      ‖f.2 x y-f.2 z y‖ ≤ C/((1+‖y.val‖)^j)*‖x-z‖ := by
  have go {L : Type} [NormedField L] [NormedAlgebra ℝ L] (e : K ≃+* L) (he : Isometry e)
      (ht : archTest e f) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (x z : K) (y : Kˣ),
        ‖f.2 x y-f.2 z y‖ ≤ C/((1+‖y.val‖)^j)*‖x-z‖ := by
    obtain ⟨C,hC,H⟩ := rapidChart_horizontal_difference ht.2 j
    refine ⟨C,hC,fun x z y => ?_⟩
    simpa [yChart,y.ne_zero,← map_sub,he.norm_map_of_map_zero e.map_zero] using
      H (e x) (e z) (e y.val) ((map_ne_zero e).mpr y.ne_zero)
  by_cases hw : w.IsReal
  · exact go _ (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw) (by simpa only [testSet,dite_eq_left hw] using hf.2)
  · exact go _ (InfinitePlace.Completion.isometry_extensionEmbedding w) (by simpa only [testSet,dite_eq_right hw] using hf.2)

/-- The subtraction gains one power of the scaling variable uniformly in the
slice, with arbitrary polynomial decay in the ordinate. -/
theorem arch_chartDifference_bound {f : Charts (LocalField F v)} (hf : f ∈ d.testSet v) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s u : (LocalField F v)ˣ) (t y : LocalField F v),
      ‖d.chartDifference v f s u t y‖ ≤
        C/((1+‖y‖)^j)*‖t^n+s.val*y-1‖*‖u.val‖ := by
  obtain ⟨C,hC,H⟩ := d.arch_test_horizontal_difference w hf j
  refine ⟨C,hC,fun s u t y => ?_⟩
  by_cases hy : y = 0
  · simp only [hy,chartDifference,ne_eq,not_true_eq_false,dite_false,norm_zero]
    positivity
  · rw [chartDifference,dite_eq_left hy,norm_mul,d.norm_symbol,one_mul]
    have h : ‖f.2 ((t^n+s.val*y)*u.val) (Units.mk0 y hy)-f.2 u.val (Units.mk0 y hy)‖ ≤
        C/((1+‖y‖)^j)*‖(t^n+s.val*y)*u.val-u.val‖ := H _ _ _
    simpa only [← sub_one_mul,norm_mul,mul_assoc] using h

/-- After integrating in the ordinate, the small-scale bound grows only
polynomially in the determinant parameter. -/
theorem arch_integral_chartDifference_small {f : Charts (LocalField F v)} (hf : f ∈ d.testSet v) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (s u : (LocalField F v)ˣ) (t : LocalField F v),
      (∫ y, ‖d.chartDifference v f s u t y‖ ∂(selfDual F d.character v)) ≤
        A*(1+‖t‖^n+‖s.val‖)*‖u.val‖ := by
  let dx := selfDual F d.character v
  let k := fun y : LocalField F v => ((1+‖y‖)^3)⁻¹
  have hi := d.arch_integrable_inv_cube w
  obtain ⟨C,hC,H⟩ := d.arch_chartDifference_bound w hf 4
  refine ⟨C*(∫ y, k y ∂dx),mul_nonneg hC (integral_nonneg (fun y => by dsimp [k]; positivity)),fun s u t => ?_⟩
  let b := 1+‖t‖^n+‖s.val‖
  have bound (y : LocalField F v) :
      ‖d.chartDifference v f s u t y‖ ≤ (C*b*‖u.val‖)*k y := by
    have e : ‖t^n+s.val*y-1‖ ≤ b*(1+‖y‖) := by
      refine (norm_sub_le ..).trans ((add_le_add (norm_add_le ..) le_rfl).trans ?_)
      rw [norm_pow,norm_mul,norm_one]
      dsimp only [b]
      nlinarith [mul_nonneg (pow_nonneg (norm_nonneg t) n) (norm_nonneg y), norm_nonneg s.val, norm_nonneg y]
    calc
      _ ≤ _ := H s u t y
      _ ≤ C/((1+‖y‖)^4)*(b*(1+‖y‖))*‖u.val‖ := by gcongr
      _ = _ := by dsimp only [k]; field_simp
  have h := integral_mono_of_nonneg (Filter.Eventually.of_forall (fun y => norm_nonneg _))
    (hi.const_mul (C*b*‖u.val‖)) (Filter.Eventually.of_forall bound)
  rw [integral_const_mul] at h
  exact h.trans_eq (by dsimp only [b,k,dx]; ring)

/-- At large scaling parameter the affine change in the ordinate contributes the
inverse Haar modulus. The unshifted chart is bounded by rapid decay. -/
theorem arch_integral_chartDifference_large {f : Charts (LocalField F v)} (hf : f ∈ d.testSet v)
    (s : (LocalField F v)ˣ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (u : (LocalField F v)ˣ) (t : LocalField F v), 1 ≤ ‖u.val‖ →
      (∫ y, ‖d.chartDifference v f s u t y‖ ∂(selfDual F d.character v)) ≤ A / ‖u.val‖ := by
  let dx := selfDual F d.character v
  let : dx.IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  let k := fun y : LocalField F v => ((1+‖y‖)^3)⁻¹
  let V := ∫ y, k y ∂dx
  have hi : Integrable k dx := d.arch_integrable_inv_cube w
  have hV : 0 ≤ V := integral_nonneg fun y => by dsimp [k]; positivity
  obtain ⟨C,hC,H⟩ := (d.arch_test_lineCharts w hf).2.2 4
  let ms := modulus F v s.val
  have hms : 0 < ms := pow_pos (norm_pos_iff.mpr s.ne_zero) _
  refine ⟨C*V/ms+C*V,by positivity,fun u t hu => ?_⟩
  let b := t^n*u.val
  let a := s*u
  let q := fun y : LocalField F v => (t^n+s.val*y)*u.val
  have eqn (y : LocalField F v) : q y = a.val*y+b := by simp only [q,a,b,Units.val_mul]; ring
  have hI : Integrable (fun y => k (q y)) dx := by
    let e := MeasurableEquiv.smul (α := LocalField F v) a
    have hi' := hi.comp_add_right b
    change Integrable (k ∘ (fun y => y+b)) dx at hi'
    simp_rw [eqn]
    apply (e.measurableEmbedding.integrable_map_iff (g := k ∘ (fun y => y+b))).mp
    change Integrable _ (Measure.map (fun y => a.val*y) dx)
    rw [d.map_local_mul]
    exact hi'.smul_measure_nnreal
  have hscale : (∫ y, k (q y) ∂dx) = V/(ms*modulus F v u.val) := by
    have h := d.integral_local_mul v a (fun x => (k (x+b) : ℂ))
    simp only [integral_complex_ofReal,integral_add_right_eq_self] at h
    apply Complex.ofReal_injective
    simp_rw [eqn]
    simpa [dx,V,a,ms,modulus,norm_mul,mul_pow] using h
  have bound (y : LocalField F v) : ‖d.chartDifference v f s u t y‖ ≤ C*k (q y)+(C/‖u.val‖)*k y := by
    by_cases hy : y = 0
    · simp only [hy,chartDifference,ne_eq,not_true_eq_false,dite_false,norm_zero]
      dsimp only [k]
      positivity
    · let Y := Units.mk0 _ hy
      have base (x : LocalField F v) :
          ‖f.2 x Y‖*(1+max ‖y‖ ‖x‖)^4 ≤ C := H Y x
      have hq : ‖f.2 (q y) Y‖ ≤ C*k (q y) := by
        rw [show C*k (q y) = C/((1+‖q y‖)^3) by rfl,le_div_iff₀ (by positivity)]
        apply le_trans _ (base (q y))
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        exact (pow_le_pow_left₀ (by positivity) (add_le_add_right (le_max_right ‖y‖ ‖q y‖) 1) 3).trans
          (pow_le_pow_right₀ (by have := le_max_left ‖y‖ ‖q y‖; linarith [norm_nonneg y]) (by decide : 3 ≤ 4))
      have hy' : ‖f.2 u.val Y‖ ≤ C/‖u.val‖ * k y := by
        change _ ≤ C/‖u.val‖ / ((1+‖y‖)^3)
        rw [le_div_iff₀ (by positivity),le_div_iff₀ (norm_pos_iff.mpr u.ne_zero),mul_assoc]
        apply le_trans _ (base u.val)
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        rw [show (1+max ‖y‖ ‖u.val‖)^4 = (1+max ‖y‖ ‖u.val‖)^3*(1+max ‖y‖ ‖u.val‖) from pow_succ _ 3]
        apply mul_le_mul _ _ (norm_nonneg _) (by positivity)
        · exact pow_le_pow_left₀ (by positivity) (add_le_add_right (le_max_left ..) 1) _
        · linarith [le_max_right ‖y‖ ‖u.val‖]
      rw [chartDifference,dite_eq_left hy,norm_mul,d.norm_symbol,one_mul]
      exact (norm_sub_le ..).trans (add_le_add hq hy')
  have h := integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => norm_nonneg _)
    ((hI.const_mul C).add (hi.const_mul (C/‖u.val‖))) (Filter.Eventually.of_forall bound)
  change _ ≤ ∫ y, C*k (q y) + C/‖u.val‖*k y ∂dx at h
  rw [integral_add (hI.const_mul C) (hi.const_mul _),integral_const_mul,integral_const_mul,hscale] at h
  have hm : ‖u.val‖ ≤ modulus F v u.val := le_self_pow₀ hu w.mult_ne_zero
  refine h.trans ?_
  change C*(V/(ms*modulus F v u.val)) + C/‖u.val‖*V ≤ _
  calc
    _ ≤ C*(V/(ms*‖u.val‖)) + C/‖u.val‖*V := by gcongr
    _ = _ := by ring

/-- A single bound at both ends of the multiplicative scaling integral. -/
theorem arch_integral_chartDifference_bound {f : Charts (LocalField F v)} (hf : f ∈ d.testSet v)
    (s : (LocalField F v)ˣ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : (LocalField F v)ˣ) (t : LocalField F v),
      (∫ y, ‖d.chartDifference v f s u t y‖ ∂(selfDual F d.character v)) ≤
        C*(1+‖t‖^n+‖s.val‖)*min ‖u.val‖ ‖u.val‖⁻¹ := by
  obtain ⟨A,hA,small⟩ := d.arch_integral_chartDifference_small w hf
  obtain ⟨B,hB,large⟩ := d.arch_integral_chartDifference_large w hf s
  refine ⟨max A B,hA.trans (le_max_left ..),fun u t => ?_⟩
  have pos := norm_pos_iff.mpr u.ne_zero
  by_cases hu : ‖u.val‖ ≤ 1
  · rw [min_eq_left (hu.trans ((one_le_inv₀ pos).mpr hu))]
    exact (small s u t).trans (by gcongr; exact le_max_left ..)
  · have hu' := le_of_not_ge hu
    rw [min_eq_right ((inv_le_one_of_one_le₀ hu').trans hu')]
    refine (large u t hu').trans ?_
    rw [div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr pos.le)
    exact (le_max_right A B).trans (le_mul_of_one_le_right (hB.trans (le_max_right ..)) (by
      linarith [pow_nonneg (norm_nonneg t) n,norm_nonneg s.val]))

end Datum
end MetaplecticPoisson
