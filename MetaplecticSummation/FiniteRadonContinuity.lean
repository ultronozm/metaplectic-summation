import MetaplecticSummation.Jacquet.WeightIntegrability
import MetaplecticSummation.LocalGrowth
import MetaplecticSummation.TransformLinearity

/-! Absolute convergence and joint continuity of both finite-place Radon
charts on the entire Schwartz space, including the zero-determinant fiber. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField MeasureTheory Set
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)
variable (p : Prime F)
local notation "vₚ" => (Sum.inr p : Place F)
local notation "Kv" => LocalField F vₚ
local notation "dx" => selfDual F d.character vₚ

private theorem finite_line_family {P : Type*} [TopologicalSpace P] [FirstCountableTopology P]
    (g : P → Kvˣ → ℂ) (hc : ∀ q, Continuous (g q)) (hq : ∀ a, Continuous fun q => g q a)
    {M R : ℝ} (hM : 0 ≤ M) (hg : ∀ q (a : Kvˣ), ‖g q a‖ * ‖a.val‖^(growthExponent n) ≤ M)
    (ho : ∀ q (a : Kvˣ), R < ‖a.val‖ → g q a = 0) :
    let f (q : P) (z : Kv) := if h : z ≠ 0 then g q (Units.mk0 z h) else 0
    (∀ q, Integrable (f q) dx) ∧ Continuous (fun q => ∫ z, f q z ∂dx) := by
  intro f
  let ν := d.lineMeasure vₚ
  let G (q : P) (a : Kvˣ) := ‖a.val‖ • g q a
  have cont (q : P) : Continuous (G q) := Units.continuous_val.norm.smul (hc q)
  let e := 1 / (n:ℝ)
  have he : 0 < e := one_div_pos.mpr (by exact_mod_cast NeZero.pos n)
  have hadd : growthExponent n + e = 1 := by
    dsimp only [growthExponent,e]
    rw [Nat.cast_sub (NeZero.one_le : 1 ≤ n),Nat.cast_one,← add_div,sub_add_cancel,
      div_self (by exact_mod_cast NeZero.ne n)]
  let B := (max 1 R)^(e+e)
  have hB : 1 ≤ B := Real.one_le_rpow (le_max_left ..) (add_nonneg he.le he.le)
  let W (a : Kvˣ) := (M*B) * min (‖a.val‖^e) (‖a.val‖^(-e))
  have bound (q : P) (a : Kvˣ) : ‖G q a‖ ≤ W a := by
    let r := ‖a.val‖
    have hr : 0 < r := norm_pos_iff.mpr a.ne_zero
    have hMB := mul_nonneg hM (zero_le_one.trans hB)
    change ‖r • g q a‖ ≤ (M*B)*min (r^e) (r^(-e))
    rw [norm_smul,Real.norm_of_nonneg hr.le]
    by_cases ha : r ≤ R
    · have H : r*‖g q a‖ ≤ M*r^e := by
        calc
          _ = (‖g q a‖ * r^(growthExponent n))*r^e := by rw [mul_assoc,← Real.rpow_add hr,hadd,Real.rpow_one,mul_comm]
          _ ≤ _ := mul_le_mul_of_nonneg_right (hg q a) (Real.rpow_nonneg hr.le e)
      rw [mul_min_of_nonneg _ _ hMB,le_min_iff]
      refine ⟨H.trans (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hM hB) (Real.rpow_nonneg hr.le _)),H.trans ?_⟩
      rw [Real.rpow_neg hr.le,← div_eq_mul_inv,le_div_iff₀ (Real.rpow_pos_of_pos hr e),mul_assoc,← Real.rpow_add hr]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hr.le (ha.trans (le_max_right ..)) (add_nonneg he.le he.le)) hM
    · rw [ho q a (lt_of_not_ge ha),norm_zero,mul_zero]
      exact mul_nonneg hMB (le_min (Real.rpow_nonneg hr.le _) (Real.rpow_nonneg hr.le _))
  have hW : Integrable W ν := (d.finite_integrable_min_rpow p he).const_mul (M*B)
  have hG (q : P) : Integrable (G q) ν := hW.mono' (cont q).aestronglyMeasurable (.of_forall (bound q))
  have hval (q : P) (a : Kvˣ) : modulus F vₚ a.val • f q a.val = G q a := by
    simp only [modulus,f,dif_pos a.ne_zero,Units.mk0_val,G]
  have transfer (q : P) := d.lineMeasure_modulus vₚ (f q)
  simp_rw [hval] at transfer
  refine ⟨fun q => (transfer q).1.mp (hG q),?_⟩
  apply Continuous.congr _ (fun q => (transfer q).2)
  exact continuous_of_dominated (bound := W) (fun q => (hG q).aestronglyMeasurable)
    (fun q => .of_forall (bound q)) hW (.of_forall fun a => (continuous_const (y := ‖a.val‖)).smul (hq a))

private theorem finite_radon_X (Φ : d.schwartz vₚ) :
    (∀ t a b, Integrable (lineIntegrandX (d.symbol vₚ) Φ.val n t a b) dx) ∧
    Continuous (fun q : (Kvˣ × Kv) × Kv => (d.radonAt vₚ Φ.val q.2).1 q.1.1 q.1.2) := by
  letI : FirstCountableTopology Kvˣ := Units.isEmbedding_val₀.firstCountableTopology
  obtain ⟨hX,hY⟩ := d.locallyConstant_finite_schwartz p Φ
  obtain ⟨S,hS,hout⟩ := (d.finite_germs p Φ).2.1
  obtain ⟨R,hR⟩ := hS.isBounded.exists_norm_le
  let X (q : (Kvˣ × Kv) × Kv) (a : Kvˣ) :=
    Φ.val.1 a ((a.val*q.1.2-q.2^n)/q.1.1.val) * d.symbol vₚ a (-q.1.1)
  have ccX : Continuous (Function.uncurry X) := by
    apply (hX.continuous.comp (continuous_snd.prodMk (show Continuous (fun q : ((Kvˣ × Kv) × Kv) × Kvˣ =>
      (q.2.val*q.1.1.2-q.1.2^n)/q.1.1.1.val) by fun_prop (disch := simp)))).mul
    exact (d.continuous_symbol vₚ).comp (continuous_snd.prodMk (Units.isEmbedding_val₀.continuous_iff.mpr
      (show Continuous (fun q : ((Kvˣ × Kv) × Kv) × Kvˣ => -q.1.1.1.val) by fun_prop)))
  obtain ⟨A,hA,HX⟩ := d.finite_vertical_growth p Φ
  have bx (q : (Kvˣ × Kv) × Kv) (a : Kvˣ) : ‖X q a‖ * ‖a.val‖^(growthExponent n) ≤ A := by
    simp only [X,norm_mul,d.norm_symbol,mul_one]
    exact HX a _
  have ox (q : (Kvˣ × Kv) × Kv) (a : Kvˣ) (ha : R < ‖a.val‖) : X q a = 0 := by
    let y := (a.val*q.1.2-q.2^n)/q.1.1.val
    have hn : (a.val,y) ∉ S := fun h => ha.not_ge ((le_max_left ‖a.val‖ ‖y‖).trans (hR (a.val,y) h))
    have hz := (hout (a.val,y) hn).1
    change Φ.val.1 a y * _ = 0
    rw [show Φ.val.1 a y = 0 from by simpa only [xChart,dif_pos a.ne_zero,Units.mk0_val] using hz,zero_mul]
  have contX (q : (Kvˣ × Kv) × Kv) : Continuous (X q) := ccX.comp (f := fun a : Kvˣ => (q,a)) ((continuous_const (y := q)).prodMk continuous_id)
  have parX (a : Kvˣ) : Continuous (fun q => X q a) := ccX.comp (f := fun q => (q,a)) (continuous_id.prodMk (continuous_const (y := a)))
  obtain ⟨iX,cX⟩ := d.finite_line_family p X contX parX hA bx ox
  refine ⟨fun t a b => iX ((a,b),t),?_⟩
  exact cX.div (Complex.continuous_ofReal.comp ((Units.continuous_val.comp
    (continuous_fst.comp continuous_fst)).norm)) (fun q => Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr q.1.1.ne_zero))

private theorem finite_radon_Y (Φ : d.schwartz vₚ) :
    (∀ t a b, Integrable (lineIntegrandY (d.symbol vₚ) Φ.val n t a b) dx) ∧
    Continuous (fun q : (Kv × Kvˣ) × Kv => (d.radonAt vₚ Φ.val q.2).2 q.1.1 q.1.2) := by
  letI : FirstCountableTopology Kvˣ := Units.isEmbedding_val₀.firstCountableTopology
  obtain ⟨hX,hY⟩ := d.locallyConstant_finite_schwartz p Φ
  obtain ⟨S,hS,hout⟩ := (d.finite_germs p Φ).2.1
  obtain ⟨R,hR⟩ := hS.isBounded.exists_norm_le
  let Y (q : (Kv × Kvˣ) × Kv) (b : Kvˣ) :=
    Φ.val.2 ((q.1.1*b.val+q.2^n)/q.1.2.val) b * d.symbol vₚ b q.1.2 * d.symbol vₚ (-1) q.1.2
  have ccY : Continuous (Function.uncurry Y) := by
    let b (q : ((Kv × Kvˣ) × Kv) × Kvˣ) := q.1.1.2
    have cb : Continuous b := continuous_snd.comp (continuous_fst.comp continuous_fst)
    have hsym := (d.continuous_symbol vₚ).comp (continuous_snd.prodMk cb)
    have hneg := (d.continuous_symbol vₚ).comp ((continuous_const (y := (-1 : Kvˣ))).prodMk cb)
    have harg : Continuous (fun q : ((Kv × Kvˣ) × Kv) × Kvˣ =>
        (q.1.1.1*q.2.val+q.1.2^n)/q.1.1.2.val) := by fun_prop (disch := simp)
    exact ((hY.continuous.comp (harg.prodMk continuous_snd)).mul hsym).mul hneg
  obtain ⟨B,hB,HY⟩ := d.finite_horizontal_growth p Φ
  have by' (q : (Kv × Kvˣ) × Kv) (b : Kvˣ) : ‖Y q b‖ * ‖b.val‖^(growthExponent n) ≤ B := by
    simp only [Y,norm_mul,d.norm_symbol,mul_one]
    exact HY _ b
  have oy (q : (Kv × Kvˣ) × Kv) (b : Kvˣ) (hb : R < ‖b.val‖) : Y q b = 0 := by
    let x := (q.1.1*b.val+q.2^n)/q.1.2.val
    have hn : (x,b.val) ∉ S := fun h => hb.not_ge ((le_max_right ‖x‖ ‖b.val‖).trans (hR (x,b.val) h))
    have hz := (hout (x,b.val) hn).2
    change Φ.val.2 x b * _ * _ = 0
    rw [show Φ.val.2 x b = 0 from by simpa only [yChart,dif_pos b.ne_zero,Units.mk0_val] using hz,zero_mul,zero_mul]
  have contY (q : (Kv × Kvˣ) × Kv) : Continuous (Y q) := ccY.comp (f := fun a : Kvˣ => (q,a)) ((continuous_const (y := q)).prodMk continuous_id)
  have parY (b : Kvˣ) : Continuous (fun q => Y q b) := ccY.comp (f := fun q => (q,b)) (continuous_id.prodMk (continuous_const (y := b)))
  obtain ⟨iY,cY⟩ := d.finite_line_family p Y contY parY hB by' oy
  refine ⟨fun t a b => iY ((a,b),t),?_⟩
  exact cY.div (Complex.continuous_ofReal.comp ((Units.continuous_val.comp
    (continuous_snd.comp continuous_fst)).norm)) (fun q => Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr q.1.2.ne_zero))

/-- Both inner chart integrals converge absolutely on every line, and both
normalized integrals depend continuously on the chart vector and determinant parameter. -/
theorem finite_radon_convergence (Φ : d.schwartz vₚ) :
    (∀ t a b, Integrable (lineIntegrandX (d.symbol vₚ) Φ.val n t a b) dx) ∧
    (∀ t a b, Integrable (lineIntegrandY (d.symbol vₚ) Φ.val n t a b) dx) ∧
    (Continuous fun q : (Kvˣ × Kv) × Kv => (d.radonAt vₚ Φ.val q.2).1 q.1.1 q.1.2) ∧
    (Continuous fun q : (Kv × Kvˣ) × Kv => (d.radonAt vₚ Φ.val q.2).2 q.1.1 q.1.2) := by
  obtain ⟨ix,cx⟩ := d.finite_radon_X p Φ
  obtain ⟨iy,cy⟩ := d.finite_radon_Y p Φ
  exact ⟨ix,iy,cx,cy⟩

end MetaplecticPoisson.Datum
