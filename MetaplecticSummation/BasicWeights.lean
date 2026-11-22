import MetaplecticSummation.BasicConductor

/-! The unit and nonintegral shells in the local factors of the global Gauss sum. -/

noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField MeasureTheory Set
open scoped Pointwise
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

theorem basic_x_outside (p : Prime F) (ht : p.asIdeal.absNorm.Coprime n)
    (x : (LocalField F (.inr p))ˣ) (y : LocalField F (.inr p)) (h : 1 < max ‖x.val‖ ‖y‖) :
    (d.basic (.inr p)).val.1 x y = 0 := by
  have hq : 1 ≤ (p.asIdeal.absNorm : ℝ) := by
    exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm p).le
  have he (k : ℕ) : max ‖x.val‖ ‖y‖ ≠ ((p.asIdeal.absNorm : ℝ)^(n*k))⁻¹ :=
    ne_of_gt ((inv_le_one_of_one_le₀ (one_le_pow₀ hq)).trans_lt h)
  simp [basic, dif_pos ht, basicCharts, he]

theorem jacquet_basic_nonintegral (p : Prime F) (ht : p.asIdeal.absNorm.Coprime n)
    (c : (LocalField F (.inr p))ˣ) (hc : 1 < ‖c.val‖) :
    d.jacquet (.inr p) (d.basic (.inr p)) c = 0 := by
  unfold jacquet
  simp only [d.basic_x_outside p ht c _ (hc.trans_le (le_max_left _ _)), zero_mul, integral_zero]

theorem jacquet_basic_unit (p : Prime F) (ht : p.asIdeal.absNorm.Coprime n)
    (hψ : ∀ x : LocalField F (.inr p), ‖x‖ ≤ 1 → d.character.localValue F (.inr p) x = 1)
    (c : (LocalField F (.inr p))ˣ) (hc : ‖c.val‖ = 1) :
    d.jacquet (.inr p) (d.basic (.inr p)) c =
      ((selfDual F d.character (.inr p)).real {x | ‖x‖ ≤ 1} : ℂ) := by
  let O := {x : LocalField F (.inr p) | ‖x‖ ≤ 1}
  have hO : MeasurableSet O := (isClosed_le continuous_norm continuous_const).measurableSet
  unfold jacquet
  calc
    _ = ∫ x, O.indicator (fun _ => (1:ℂ)) x ∂(selfDual F d.character (.inr p)) := by
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : ‖x‖ ≤ 1
      · have he := d.basic_xChart_unit p ht c.val x hc hx
        simp only [xChart, c.ne_zero, ne_eq, not_false_eq_true, dif_pos] at he
        have hval : (d.basic (.inr p)).val.1 c x = 1 := by
          rwa [show Units.mk0 c.val c.ne_zero = c from Units.ext rfl] at he
        rw [hval, hψ _ (by simpa only [norm_div, norm_neg, hc, div_one] using hx),
          one_mul, indicator_of_mem (show x ∈ O from hx)]
      · rw [d.basic_x_outside p ht c x ((lt_of_not_ge hx).trans_le (le_max_right _ _)),
          zero_mul, indicator_of_notMem (show x ∉ O from hx)]
    _ = _ := by simp [integral_indicator hO, Measure.real, O]

theorem scaled_basic_unit {S : Finset (Place F)} (h : d.ClassicalSetting S) (b : NonzeroInteger S)
    (p : Prime F) (hp : Sum.inr p ∉ S) (c : (LocalField F (.inr p))ˣ) (hc : ‖c.val‖ = 1) :
    let db := d.scaled (fieldUnit b)
    db.jacquet (.inr p) (db.basic (.inr p)) c = (Real.sqrt ‖diagonal F (.inr p) (b.val : F)‖ : ℂ) := by
  let db := d.scaled (fieldUnit b)
  have hg := (d.scaled_good h b).2.2 p hp
  exact (db.jacquet_basic_unit p hg.1 hg.2 c hc).trans
    (congrArg Complex.ofReal (d.scaled_selfDual_volume p (h.unramified p hp) (fieldUnit b)))

/-- The factor outside S in the product of basic functions in §10. -/
def outsideBasic (S : Finset (Place F)) (c : Fˣ) : ℂ :=
  ∏ᶠ p : Prime F, if Sum.inr p ∈ S then 1 else
    d.jacquet (.inr p) (d.basic (.inr p)) (atPlace (.inr p) c)

theorem eventually_scaled_basic_one {S : Finset (Place F)} (h : d.ClassicalSetting S)
    (b : NonzeroInteger S) (c : Fˣ) :
    let db := d.scaled (fieldUnit b)
    ∀ᶠ p : Prime F in Filter.cofinite, (if Sum.inr p ∈ S then 1 else
      db.jacquet (.inr p) (db.basic (.inr p)) (atPlace (.inr p) c)) = 1 := by
  filter_upwards [eventually_diagonal_norm_one (fieldUnit b).ne_zero,
    eventually_diagonal_norm_one c.ne_zero] with p hb hc
  split_ifs with hp
  · rfl
  · apply (d.scaled_basic_unit h b p hp (atPlace (.inr p) c) hc).trans
    change ‖diagonal F (.inr p) (b.val : F)‖ = 1 at hb
    rw [hb, Real.sqrt_one, Complex.ofReal_one]

theorem outsideBasic_zero_of_nonintegral {S : Finset (Place F)} (h : d.ClassicalSetting S)
    (b : NonzeroInteger S) (c : Fˣ) (hc : (c : F) ∉ SIntegers S) :
    (d.scaled (fieldUnit b)).outsideBasic S c = 0 := by
  classical
  change ¬ ∀ p : Prime F, Sum.inr p ∉ S → p.valuation F (c : F) ≤ 1 at hc
  obtain ⟨p, hfail⟩ := not_forall.mp hc
  obtain ⟨hp, hbig⟩ := Classical.not_imp.mp hfail
  unfold outsideBasic
  apply finprod_eq_zero _ p _ (Filter.eventually_cofinite.mp (d.eventually_scaled_basic_one h b c))
  rw [if_neg hp]
  apply (d.scaled (fieldUnit b)).jacquet_basic_nonintegral p (h.good.2.2 p hp).1
  exact lt_of_not_ge (fun h => hbig ((diagonal_norm_le_one_iff (c : F) p).mp h))

theorem outsideBasic_unit {S : Finset (Place F)} (h : d.ClassicalSetting S)
    (b : NonzeroInteger S) (c : (SIntegers S)ˣ) :
    (d.scaled (fieldUnit b)).outsideBasic S (Units.map (algebraMap (SIntegers S) F).toMonoidHom c) =
      ((Real.sqrt (sNorm S (b.val : F)))⁻¹ : ℝ) := by
  classical
  let g (p : Prime F) : ℝ := if Sum.inr p ∈ S then 1 else Real.sqrt ‖diagonal F (.inr p) (b.val : F)‖
  have he (p : Prime F) : (if Sum.inr p ∈ S then 1 else
      (d.scaled (fieldUnit b)).jacquet (.inr p) ((d.scaled (fieldUnit b)).basic (.inr p))
        (atPlace (.inr p) (Units.map (algebraMap (SIntegers S) F).toMonoidHom c))) = (g p : ℂ) := by
    by_cases hp : Sum.inr p ∈ S
    · simp [hp,g]
    · simp only [hp, if_false,g]
      exact d.scaled_basic_unit h b p hp _ (unit_norm_eq_one c p hp)
  have hg : Function.HasFiniteMulSupport g := Filter.eventually_cofinite.mp (by
    filter_upwards [eventually_diagonal_norm_one (fieldUnit b).ne_zero] with p hb
    change ‖diagonal F (.inr p) (b.val : F)‖ = 1 at hb
    simp [g,hb])
  unfold outsideBasic
  simp_rw [he]
  exact (Complex.ofRealHom.toMonoidHom.map_finprod hg).symm.trans
    (congrArg Complex.ofReal (outside_sqrt_norm S h.good.2.1 (fieldUnit b)))

theorem basic_dual (p : Prime F) (hp : p.asIdeal.absNorm.Coprime n)
    (b : (LocalField F (.inr p))ˣ) (hb : ‖(b : LocalField F (.inr p))‖ ≤ 1)
    (conductor : ∀ x : LocalField F (.inr p), (∀ y : LocalField F (.inr p), ‖y‖ ≤ 1 →
      d.character.localValue F (.inr p) (x*y) = 1) ↔ ‖x * b‖ ≤ 1)
    (c : (LocalField F (.inr p))ˣ) :
    d.jacquet (.inr p) (d.fourier (.inr p) (d.basic (.inr p))) c =
      d.jacquet (.inr p) (d.basic (.inr p)) (b^n * c) := by
  clear hb -- The integral identity holds for every conductor parameter.
  unfold jacquet
  rw [d.fourier_apply,basic,dif_pos hp]
  exact d.basicCharts_jacquet_dual p hp b conductor c

end MetaplecticPoisson.Datum
