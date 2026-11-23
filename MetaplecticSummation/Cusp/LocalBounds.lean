import MetaplecticSummation.Cusp.SectionNorm
import MetaplecticSummation.Reduction.CompactBounds
import MetaplecticSummation.RadonConvergence

/-! Weighted local bounds at arbitrary row vectors, in the normalization of Appendix B. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField IsDedekindDomain Filter Set
open scoped Topology Matrix
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

theorem continuousAt_sectionNorm (v : Place F) (Φ : d.schwartz v) {z : Fin 2 → LocalField F v} (hz : z ≠ 0) :
    ContinuousAt (d.sectionNorm v Φ) z := by
  let : NontriviallyNormedField (LocalField F v) := { localNormedField F v with
    non_trivial := by
      cases v with
      | inl w => exact (archNontriviallyNormedCompletion w).non_trivial
      | inr p => exact (FinitePlace.nontriviallyNormedCompletion p).non_trivial }
  have coord (i : Fin 2) : ContinuousAt (fun y : Fin 2 → LocalField F v => y i) z := (continuous_apply i).continuousAt
  obtain ⟨cx,cy⟩ := d.continuous_schwartz_charts v Φ
  by_cases hx : z 0 ≠ 0
  · have hc := (liftUnit_continuousAt hx).comp (f := fun y : Fin 2 → LocalField F v => y 0) (coord 0)
    have near := (coord 0).eventually (eventually_ne_nhds hx)
    apply ((cx.continuousAt.comp (hc.prodMk (coord 1))).norm).congr_of_eventuallyEq
    filter_upwards [near] with y hy
    simp only [sectionNorm_x _ _ _ _ hy,Function.comp_apply,Function.uncurry_apply_pair,liftUnit,dite_eq_left hy]
  · have hy : z 1 ≠ 0 := fun h => hz (funext fun i => by fin_cases i <;> simp [not_ne_iff.mp hx,h])
    have hc := (liftUnit_continuousAt hy).comp (f := fun y : Fin 2 → LocalField F v => y 1) (coord 1)
    have near := (coord 1).eventually (eventually_ne_nhds hy)
    apply ((cy.continuousAt.comp ((coord 0).prodMk hc)).norm).congr_of_eventuallyEq
    filter_upwards [near] with y h
    simp only [sectionNorm_y _ _ _ _ h,Function.comp_apply,Function.uncurry_apply_pair,liftUnit,dite_eq_left h]

private theorem finite_row_bound (p : Prime F) (Φ : d.schwartz (.inr p)) (C : ℝ)
    (H : ∀ z, ‖d.localValue z (.inr p) Φ‖ ≤ localThetaBound (growthExponent n) (.inr p) C (vectorModulus (.inr p) z))
    (z : Fin 2 → LocalField F (.inr p)) (hz : z ≠ 0) :
    d.sectionNorm (.inr p) Φ z ≤ localThetaBound (growthExponent n) (.inr p) C (localRowModulus F (.inr p) z) := by
  let v : Place F := .inr p
  let K := LocalField F v
  let : IsUltrametricDist K := inferInstanceAs (IsUltrametricDist (p.adicCompletion F))
  let ι := diagonal F v
  have hd : DenseRange ι := HeightOneSpectrum.denseRange_algebraMap (K := F) p
  let atRow := fun (a : Fin 2 → F) (i : Fin 2) => ι (a i)
  have dense : DenseRange atRow := DenseRange.piMap (fun _ : Fin 2 => hd)
  have radius (y : Fin 2 → K) : localRowModulus F v y = ‖y‖ := by
    change max ‖y 0‖ ‖y 1‖ = ‖y‖
    refine le_antisymm (max_le (norm_le_pi_norm ..) (norm_le_pi_norm ..)) ((pi_norm_le_iff_of_nonempty _).mpr ?_)
    intro i
    fin_cases i <;> first | exact le_max_left .. | exact le_max_right ..
  have hs : ∀ᶠ y : Fin 2 → K in 𝓝 z, ‖y‖ = ‖z‖ := by
    have op := IsUltrametricDist.isOpen_sphere (0 : Fin 2 → K) (norm_ne_zero_iff.mpr hz)
    filter_upwards [op.mem_nhds (show z ∈ Metric.sphere 0 ‖z‖ by simp)] with y hy
    simpa only [Metric.mem_sphere,dist_zero_right] using hy
  by_contra! bad
  have hc := (continuousAt_const.eventually_lt (d.continuousAt_sectionNorm v Φ hz) bad).and hs
  obtain ⟨a,ha,hr⟩ := dense.mem_nhds hc
  have hne : a ≠ 0 := by
    rintro rfl
    have h0 : atRow 0 = 0 := funext fun _ => map_zero ι
    exact (norm_ne_zero_iff.mpr hz) (hr.symm.trans (by rw [h0,norm_zero]))
  let q : RationalPoint F := ⟨(a 0,a 1),fun he => hne (by funext i; fin_cases i <;> first | exact congrArg Prod.fst he | exact congrArg Prod.snd he)⟩
  have hq : ![diagonal F v q.val.1,diagonal F v q.val.2] = atRow a := by funext i; fin_cases i <;> rfl
  have e : vectorModulus v q = localRowModulus F v (atRow a) := rfl
  have hb := H q
  rw [← d.sectionNorm_diagonal v q Φ,hq,e,radius,hr,← radius] at hb
  exact ha.not_ge hb

theorem weighted_section_bounds (Φ : ∀ v, d.schwartz v) (hΦ : ∀ᶠ v in cofinite, Φ v = d.basic v) (L : ℕ) :
    ∃ C : Place F → ℝ, (∀ v, 1 ≤ C v) ∧ (∀ᶠ v in cofinite, C v = 1) ∧
      ∀ v (z : Fin 2 → LocalField F v), z ≠ 0 →
        (max 1 (localRowModulus F v z))^L * d.sectionNorm v (Φ v) z ≤
          localThetaBound (growthExponent n) v (C v) (localRowModulus F v z) := by
  obtain ⟨B,_,hfin,hB,hb⟩ := d.theta_local_bounds Φ hΦ
  choose A hA ha using fun w => d.arch_local_growth w (Φ (.inl w)) (4+L) (by omega)
  let C : Place F → ℝ := Sum.elim (fun w => max 1 (A w)) (fun p => (B (.inr p))^L * B (.inr p))
  refine ⟨C,?_,?_,?_⟩
  · rintro (w|p)
    · exact le_max_left ..
    · exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (hfin p)) (hfin p)
  · apply eventually_place_of_finite
    have h : ∀ᶠ p : Prime F in cofinite, B (.inr p) = 1 :=
      (show Function.Injective (Sum.inr : Prime F → Place F) from Sum.inr_injective).tendsto_cofinite.eventually hB
    exact h.mono fun p hp => by simp [C,hp]
  intro v z hz
  let r := localRowModulus F v z
  cases v with
  | inr p =>
    let b := B (.inr p)
    have h := d.finite_row_bound p _ b (fun q => hb q (.inr p)) z hz
    change (max 1 r)^L * _ ≤ if r ≤ b^L*b then b^L*b*r^(-(growthExponent n)) else 0
    change _ ≤ if r ≤ b then b*r^(-(growthExponent n)) else 0 at h
    by_cases hr : r ≤ b
    · have hle := le_mul_of_one_le_left (zero_le_one.trans (hfin p)) (one_le_pow₀ (n := L) (hfin p))
      rw [ite_eq_left hr] at h
      rw [ite_eq_left (hr.trans hle),mul_assoc]
      exact mul_le_mul (pow_le_pow_left₀ (zero_le_one.trans (le_max_left ..)) (max_le (hfin p) hr) L)
        h (by unfold sectionNorm; split <;> exact norm_nonneg _) (pow_nonneg (zero_le_one.trans (hfin p)) _)
    · rw [ite_eq_right hr] at h
      have hh := mul_nonpos_of_nonneg_of_nonpos (pow_nonneg (zero_le_one.trans (le_max_left (1:ℝ) r)) L) h
      apply hh.trans
      split
      · exact mul_nonneg (mul_nonneg (pow_nonneg (zero_le_one.trans (hfin p)) _) (zero_le_one.trans (hfin p)))
          (Real.rpow_nonneg ((norm_nonneg _).trans (le_max_left ..)) _)
      · exact le_rfl
  | inl w =>
    have hn : (z 0,z 1) ≠ 0 := fun he => hz (by funext i; fin_cases i <;> first | exact congrArg Prod.fst he | exact congrArg Prod.snd he)
    obtain ⟨hx,hy⟩ := ha w (z 0,z 1) hn
    have h : d.sectionNorm (.inl w) (Φ (.inl w)) z ≤ A w * min (r^(-(growthExponent n))) (r^(-((4+L : ℕ) : ℝ))) := by
      unfold sectionNorm
      split <;> assumption
    have hr : 0 < r := by
      rcases (not_and_or.mp (show ¬ (z 0 = 0 ∧ z 1 = 0) from fun h => hn (Prod.ext h.1 h.2))) with e|e
      · exact (pow_pos (norm_pos_iff.mpr e) _).trans_le (le_max_left ..)
      · exact (pow_pos (norm_pos_iff.mpr e) _).trans_le (le_max_right ..)
    change (max 1 r)^L * _ ≤ max 1 (A w) * min (r^(-(growthExponent n))) (r^(-4:ℝ))
    rcases le_total r 1 with hr₁|hr₁
    · rw [max_eq_left hr₁,one_pow,one_mul]
      apply h.trans
      apply mul_le_mul (le_max_right ..) _ (le_min (Real.rpow_nonneg hr.le _) (Real.rpow_nonneg hr.le _)) (zero_le_one.trans (le_max_left ..))
      apply le_min (min_le_left ..)
      exact (min_le_left ..).trans (Real.rpow_le_rpow_of_exponent_ge hr hr₁ (by linarith [growthExponent_le_one n]))
    · have hsmall : r^(-4:ℝ) ≤ r^(-(growthExponent n)) := Real.rpow_le_rpow_of_exponent_le hr₁ (by linarith [growthExponent_le_one n])
      rw [max_eq_right hr₁,min_eq_right hsmall]
      calc
        _ ≤ r^L * (A w * r^(-((4+L : ℕ) : ℝ))) := by
          gcongr
          exact h.trans (mul_le_mul_of_nonneg_left (min_le_right ..) (hA w))
        _ = A w * r^(-4:ℝ) := by
          rw [mul_left_comm,← Real.rpow_natCast,← Real.rpow_add hr]
          congr 1
          push_cast
          ring_nf
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right ..) (Real.rpow_nonneg hr.le _)

end MetaplecticPoisson.Datum
