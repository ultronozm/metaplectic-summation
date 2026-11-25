import MetaplecticSummation.FourierCoefficients.Orbits

/-! An adelic majorant for the integrals over the nonzero unipotent orbits. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField IsDedekindDomain MeasureTheory Set Filter
open Classical
open scoped ENNReal
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

private theorem shear_max_nonarch {K : Type} [NormedField K] [IsUltrametricDist K]
    (x y u : K) (hu : ‖u‖ ≤ 1) : max ‖x‖ ‖y+u*x‖ = max ‖x‖ ‖y‖ := by
  have aux (b c : K) (hc : ‖c‖ ≤ ‖x‖) : max ‖x‖ ‖b+c‖ ≤ max ‖x‖ ‖b‖ := by
    apply max_le (le_max_left ..)
    exact (IsUltrametricDist.norm_add_le_max b c).trans (max_le (le_max_right ..) (hc.trans (le_max_left ..)))
  have hux : ‖u*x‖ ≤ ‖x‖ := by rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) hu
  exact le_antisymm (aux _ _ hux) (by simpa using aux (y+u*x) (-(u*x)) (by rwa [norm_neg]))

private theorem finite_translated_local_bound (p : Prime F) (Φ : d.schwartz (.inr p)) (C : ℝ)
    (H : ∀ z, ‖d.localValue z (.inr p) Φ‖ ≤ localThetaBound (growthExponent n) (.inr p) C (vectorModulus (.inr p) z))
    (x : Fˣ) (y : F) (u : LocalField F (.inr p)) (hu : ‖u‖ ≤ 1) :
    ‖Φ.val.1 (atPlace (.inr p) x) (diagonal F (.inr p) y + u*(atPlace (.inr p) x).val)‖ ≤
      localThetaBound (growthExponent n) (.inr p) C (max ‖(atPlace (.inr p) x).val‖ ‖diagonal F (.inr p) y‖) := by
  let v : Place F := .inr p
  let K := LocalField F v
  let : IsUltrametricDist K := inferInstanceAs (IsUltrametricDist (p.adicCompletion F))
  let a := atPlace v x
  let b := diagonal F v y
  let L (t : K) := Φ.val.1 a (b + t*a.val)
  let R := localThetaBound (growthExponent n) v C (max ‖a.val‖ ‖b‖)
  have cont : Continuous L := (d.continuous_schwartz_charts v Φ).1.comp
    (continuous_const.prodMk (continuous_const.add (continuous_id.mul continuous_const)))
  have rat (t : F) (ht : ‖diagonal F v t‖ ≤ 1) : ‖L (diagonal F v t)‖ ≤ R := by
    let z : RationalPoint F := ⟨(x.val,y+t*x.val),fun hz => x.ne_zero (congrArg Prod.fst hz)⟩
    have val : d.localValue z v Φ = L (diagonal F v t) := by
      dsimp only [localValue,z,diagonalPoint]
      rw [ite_eq_left x.ne_zero,xChart]
      dsimp only
      rw [dite_eq_left (show diagonal F v x.val ≠ 0 from a.ne_zero)]
      simp only [map_add,map_mul,L,a,b]
      exact congrArg (fun c => Φ.val.1 c _) (Units.ext rfl)
    have radius : vectorModulus v z = max ‖a.val‖ ‖b‖ := by
      change max ‖a.val‖ ‖diagonal F v (y+t*x.val)‖ = _
      rw [map_add,map_mul]
      exact shear_max_nonarch a.val b (diagonal F v t) ht
    have hz := H z
    change ‖d.localValue z v Φ‖ ≤ localThetaBound (growthExponent n) v C (vectorModulus v z) at hz
    rwa [val,radius] at hz
  change ‖L u‖ ≤ R
  by_contra! h
  have O : IsOpen {s : K | ‖s‖ ≤ 1} := by
    simpa [Metric.closedBall,dist_zero_right] using IsUltrametricDist.isOpen_closedBall (0 : K) (one_ne_zero : (1:ℝ) ≠ 0)
  have hd : DenseRange (diagonal F v) := HeightOneSpectrum.denseRange_algebraMap (K := F) p
  obtain ⟨t,hlt,ht⟩ := hd.exists_mem_open ((isOpen_lt continuous_const cont.norm).inter O)
    (show ({s : K | R < ‖L s‖} ∩ {s | ‖s‖ ≤ 1}).Nonempty from ⟨u,h,hu⟩)
  exact (rat t ht).not_gt hlt

omit [NumberField F] in
private theorem arch_shear_scaled (w : InfinitePlace F) (x y u : w.Completion) (T : ℝ)
    (hu : ‖u‖ ≤ T) :
    ((1+T)^w.mult)⁻¹ * max (‖x‖^w.mult) (‖y‖^w.mult) ≤ max (‖x‖^w.mult) (‖y+u*x‖^w.mult) := by
  let R := max ‖x‖ ‖y+u*x‖
  have ht : 0 ≤ T := (norm_nonneg u).trans hu
  have hx : ‖x‖ ≤ R := le_max_left ..
  have hxy : max ‖x‖ ‖y‖ ≤ (1+T)*R := by
    apply max_le
    · exact hx.trans (le_mul_of_one_le_left ((norm_nonneg _).trans hx) (by linarith))
    calc
      ‖y‖ = ‖(y+u*x)-u*x‖ := by rw [add_sub_cancel_right]
      _ ≤ ‖y+u*x‖ + ‖u*x‖ := norm_sub_le ..
      _ ≤ R + T*R := by rw [norm_mul]; gcongr; exact le_max_right ..
      _ = _ := by ring
  have pow := pow_le_pow_left₀ ((norm_nonneg _).trans (le_max_left ..)) hxy w.mult
  rw [mul_pow] at pow
  have hp : 0 < (1+T)^w.mult := by positivity
  rw [inv_mul_le_iff₀ hp]
  have maxpow (z : w.Completion) :
      max ‖x‖ ‖z‖ ^ w.mult = max (‖x‖^w.mult) (‖z‖^w.mult) := by
    rcases le_total ‖x‖ ‖z‖ with h | h
    · rw [max_eq_right h,max_eq_right (pow_le_pow_left₀ (norm_nonneg _) h _)]
    · rw [max_eq_left h,max_eq_left (pow_le_pow_left₀ (norm_nonneg _) h _)]
  simpa only [R,maxpow] using pow

/-- A single summable majorant for the nonzero-coordinate summands on the
adelic fundamental domain. -/
theorem slope_majorant_on_fundamental (Φ : ∀ v, d.schwartz v) (hΦ : ∀ᶠ v in cofinite, Φ v = d.basic v) :
    ∃ B : Fˣ × F → ℝ, Summable B ∧ ∀ (z : Fˣ × F) u, u ∈ GroundTheory.Global.fundamentalSet F →
      ‖d.adelicSlopeSlice Φ z.1 (u + algebraMap F (Adeles F) z.2)‖ ≤ B z := by
  obtain ⟨C,hC,hfin,hC₁,hbound⟩ := d.theta_local_bounds Φ hΦ
  choose D hD hd using fun w => d.arch_local_growth w (Φ (.inl w)) 4 (by decide)
  have bounded (w : InfinitePlace F) : ∃ T : ℝ, 0 ≤ T ∧ ∀ u ∈ GroundTheory.Global.fundamentalSetInfinite F,
      ‖u w‖ ≤ T := by
    obtain ⟨R,hR⟩ := (GroundTheory.Global.isCompact_closure_fundamentalSetInfinite F).bddAbove_image
      (f := fun u : InfiniteAdeleRing F => ‖u w‖) (continuous_apply w).norm.continuousOn
    exact ⟨max 0 R,le_max_left ..,fun u hu => (hR ⟨u,subset_closure hu,rfl⟩).trans (le_max_right ..)⟩
  choose T hT hTu using bounded
  let c : Place F → ℝ := Sum.elim D (fun p => C (.inr p))
  let a : Place F → ℝ := Sum.elim (fun w => ((1+T w)^w.mult)⁻¹) (fun _ => 1)
  have hc : ∀ v, 0 ≤ c v := fun v => by cases v with
    | inl w => exact hD w
    | inr p => exact hC _
  have ha : ∀ v, 0 < a v := fun v => by cases v with
    | inr _ => exact zero_lt_one
    | inl w => exact inv_pos.mpr (pow_pos (by linarith [hT w]) _)
  have ha₁ : ∀ᶠ v in cofinite, a v = 1 := eventually_place_of_finite (.of_forall (fun _ => rfl))
  have hc₁ : ∀ᶠ v in cofinite, c v = 1 := eventually_place_of_finite
    ((Sum.inr_injective (α := InfinitePlace F)).tendsto_cofinite.eventually hC₁)
  let j (z : Fˣ × F) := rationalShearOrbits F (.inr z)
  let M := thetaMajorant (growthExponent n) c a
  obtain ⟨_,_,hm⟩ := theta_majorant_bound (growthExponent_nonneg n) (growthExponent_le_one n) c hc hfin hc₁
  refine ⟨M ∘ j,((hm a ha ha₁).1.comp_injective ((rationalShearOrbits F).injective.comp Sum.inr_injective)),?_⟩
  rintro ⟨x,t⟩ u hu
  let z := j (x,t)
  let U := u + algebraMap F (Adeles F) t
  let X (v : Place F) := (atPlace v x).val
  let Y (v : Place F) := diagonal F v (x.val*t)
  let y' (v : Place F) := Y v + component u v * X v
  let f (v : Place F) := (Φ v).val.1 (atPlace v x) (X v * component U v)
  have eqy (v : Place F) : X v * component U v = y' v := by
    have e : component U v = component u v + diagonal F v t := by cases v <;> rfl
    simp only [y',Y,map_mul,e]
    change X v * _ = X v * _ + _ * X v
    ring
  have unit : ∀ᶠ v in cofinite, f v = 1 := d.eventually_slope_factor_one Φ hΦ x U
  change (normHom.toMonoidHom : ℂ →* ℝ) (∏ᶠ v, f v) ≤ _
  rw [MonoidHom.map_finprod _ (eventually_cofinite.mp unit)]
  change (∏ᶠ v, ‖f v‖) ≤ ∏ᶠ v, localThetaBound (growthExponent n) v (c v) (a v*vectorModulus v z)
  apply finprod_mono_real (a := fun v => ‖f v‖) (unit.mono (fun v hv => by rw [hv,norm_one]))
    (localThetaBound_cofinite (growthExponent n) hc₁ ha₁ z) (fun _ => norm_nonneg _)
  intro v
  dsimp only [f]
  rw [eqy]
  cases v with
  | inr p =>
    have hint := (GroundTheory.Global.mem_integralFiniteAdeles.mp hu.2) p
    have hu' : ‖component u (.inr p)‖ ≤ 1 := (Valued.toNormedField.norm_le_one_iff (x := u.2 p)).mpr
      ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F p).mp hint)
    change _ ≤ localThetaBound _ (.inr p) (C (.inr p)) (1 * _)
    rw [one_mul]
    exact d.finite_translated_local_bound p _ _ (fun z => hbound z (.inr p)) x _ _ hu'
  | inl w =>
    let v : Place F := .inl w
    let R := max (‖X v‖^w.mult) (‖y' v‖^w.mult)
    have pos : 0 < a v * vectorModulus v z := mul_pos (ha _) (vectorModulus_pos v z)
    have lower : a v * vectorModulus v z ≤ R :=
      arch_shear_scaled w (X v) (Y v) (component u v) (T w) (hTu w u.1 hu.1)
    have bound := (hd w (X v,y' v) (fun h => (atPlace v x).ne_zero (congrArg Prod.fst h))).1
    change ‖xChart (Φ v).val (X v,y' v)‖ ≤ D w * min (R^(-(growthExponent n))) (R^(-(4:ℝ))) at bound
    rw [xChart,dite_eq_left (atPlace v x).ne_zero,Units.mk0_val] at bound
    apply bound.trans
    apply mul_le_mul_of_nonneg_left _ (hD w)
    exact min_le_min (Real.rpow_le_rpow_of_nonpos pos lower (neg_nonpos.mpr (growthExponent_nonneg n)))
      (Real.rpow_le_rpow_of_nonpos pos lower (by norm_num))

/-- Absolute convergence of the unfolded sum of slope integrals. -/
theorem summable_slope_integrals (Φ : ∀ v, d.schwartz v)
    (hΦ : ∀ᶠ v in cofinite, Φ v = d.basic v) :
    (∑' x : Fˣ, ∫⁻ u : Adeles F, ‖d.adelicSlopeSlice Φ x u‖ₑ ∂GroundTheory.Global.adeleMeasure F) ≠ ⊤ := by
  let := GroundTheory.Global.countable_numberField F
  let : Countable Fˣ := (Units.val_injective (α := F)).countable
  let D := GroundTheory.Global.fundamentalSet F
  let μ := GroundTheory.Global.adeleMeasure F
  let L (x : Fˣ) (u : Adeles F) := ∑' t : F, ‖d.adelicSlopeSlice Φ x (u + algebraMap F (Adeles F) t)‖ₑ
  have ml (x) : Measurable (L x) := Measurable.tsum fun t : F =>
    ((d.measurable_adelicSlopeSlice Φ hΦ x).comp (continuous_add_const _).measurable).enorm
  obtain ⟨B,hB,h⟩ := d.slope_majorant_on_fundamental Φ hΦ
  let b (z : Fˣ × F) := ENNReal.ofReal (B z)
  have bound : (∑' z, b z) ≠ ⊤ := hB.tsum_ofReal_ne_top
  have eqn (x) : (∫⁻ u, ‖d.adelicSlopeSlice Φ x u‖ₑ ∂μ) = ∫⁻ u in D, L x u ∂μ :=
    (lintegral_rational_translates F (d.measurable_adelicSlopeSlice Φ hΦ x).enorm).symm
  change (∑' x, ∫⁻ u, ‖d.adelicSlopeSlice Φ x u‖ₑ ∂μ) ≠ ⊤
  simp_rw [eqn]
  rw [← lintegral_tsum (fun x => (ml x).aemeasurable)]
  apply ne_top_of_le_ne_top bound
  calc
    _ ≤ ∫⁻ _ in D, ∑' z, b z ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (μ := μ) (GroundTheory.Global.measurableSet_fundamentalSet F)] with u hu
      rw [show (∑' z, b z) = ∑' (x : Fˣ) (t : F), b (x,t) from ENNReal.tsum_prod (f := fun x t => b (x,t))]
      apply ENNReal.tsum_le_tsum
      intro x
      apply ENNReal.tsum_le_tsum
      intro t
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (h (x,t) u hu)
    _ = _ := by simp [D,μ,GroundTheory.Global.adeleMeasure_fundamentalSet]

end MetaplecticPoisson.Datum
