import MetaplecticSummation.Jacquet.WeightIntegrability
import MetaplecticSummation.TransformLinearity
import MetaplecticSummation.Schwartz.ChartGrowth

/-! Absolute convergence and joint continuity in Lemma 4.2(i). -/
noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField MeasureTheory Set
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n) (v : Place F)
local notation "K" => LocalField F v
local notation "m" => modulus F v
local notation "dx" => selfDual F d.character v

private theorem continuous_local_modulus : Continuous (modulus F v) := by
  cases v with
  | inl w => exact continuous_norm.pow w.mult
  | inr _ => exact continuous_norm

omit [NeZero n] in
/-- A positive power of the normalized modulus at zero and its reciprocal
at infinity give an integrable majorant for multiplicative Haar measure. -/
theorem integrable_modulus_min_rpow {e : ℝ} (he : 0 < e) :
    Integrable (fun a : Kˣ => min ((m a.val)^e) ((m a.val)^(-e))) (d.lineMeasure v) := by
  cases v with
  | inr p => exact d.finite_integrable_min_rpow p he
  | inl w =>
    let L := LocalField F (.inl w)
    letI : LocallyCompactSpace L := inferInstanceAs (LocallyCompactSpace w.Completion)
    letI : NontriviallyNormedField L := archNontriviallyNormedCompletion w
    letI : ProperSpace L := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace _
    letI : SecondCountableTopology Lˣ := Units.isEmbedding_val₀.secondCountableTopology
    obtain ⟨c,hc,hc'⟩ := NormedField.exists_norm_lt_one L
    have h := integrable_units_min_rpow (d.lineMeasure (.inl w)) (Units.mk0 c (norm_pos_iff.mp hc))
      hc' (mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero w.mult_ne_zero)) he)
    simpa only [modulus,← Real.rpow_natCast_mul (norm_nonneg _),mul_neg] using h

private theorem line_weight_bound {r s C b : ℝ} (hs : 0 < s) (hsr : s ≤ r) (hC : 0 ≤ C)
    (h : b ≤ C * min (r^(-growthExponent n)) (r^(-(2:ℝ)))) :
    s*b ≤ C * min (s^(1/(n:ℝ))) (s^(-(1/(n:ℝ)))) := by
  let e := 1/(n:ℝ)
  have he : 0 < e := one_div_pos.mpr (by exact_mod_cast NeZero.pos n)
  have he' : e ≤ 1 := (one_div_le_one_div_of_le zero_lt_one (by exact_mod_cast NeZero.one_le (n := n))).trans_eq (by norm_num)
  have hk : 1 - growthExponent n = e := by
    dsimp only [growthExponent,e]
    rw [Nat.cast_sub (NeZero.one_le : 1 ≤ n),Nat.cast_one]
    field_simp [show (n:ℝ) ≠ 0 by exact_mod_cast NeZero.ne n]
    ring
  have bound (j : ℝ) (hj : 0 ≤ j) (hb : b ≤ C*r^(-j)) : s*b ≤ C*s^(1-j) := by
    have h' := hb.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hs hsr (neg_nonpos.mpr hj)) hC)
    calc
      _ ≤ s*(C*s^(-j)) := mul_le_mul_of_nonneg_left h' hs.le
      _ = C*s^(1-j) := by rw [sub_eq_add_neg,Real.rpow_add hs,Real.rpow_one]; ring
  have hsmall := bound _ (growthExponent_nonneg n) (h.trans (mul_le_mul_of_nonneg_left (min_le_left ..) hC))
  rw [hk] at hsmall
  rw [mul_min_of_nonneg _ _ hC,le_min_iff]
  refine ⟨hsmall,?_⟩
  by_cases hs1 : s ≤ 1
  · exact hsmall.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hs hs1 (by linarith : -e ≤ e)) hC)
  · exact (bound 2 (by norm_num) (h.trans (mul_le_mul_of_nonneg_left (min_le_right ..) hC))).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hs1) (by linarith : 1-2 ≤ -e)) hC)

private theorem line_family_of_growth {P : Type*} [TopologicalSpace P] [FirstCountableTopology P]
    (g : P → Kˣ → ℂ) (hc : Continuous (Function.uncurry g)) {C : ℝ} (hC : 0 ≤ C)
    (hg : ∀ q (a : Kˣ), ∃ r, m a.val ≤ r ∧ ‖g q a‖ ≤ C*min (r^(-growthExponent n)) (r^(-(2:ℝ)))) :
    let f (q : P) (z : K) := if h : z ≠ 0 then g q (Units.mk0 z h) else 0
    (∀ q, Integrable (f q) dx) ∧ Continuous (fun q => ∫ z, f q z ∂dx) := by
  intro f
  let G (q : P) (a : Kˣ) := m a.val • g q a
  have cont : Continuous (Function.uncurry G) :=
    ((continuous_local_modulus v).comp (Units.continuous_val.comp continuous_snd)).smul hc
  let e := 1/(n:ℝ)
  let W (a : Kˣ) := C*min ((m a.val)^e) ((m a.val)^(-e))
  have hW : Integrable W (d.lineMeasure v) :=
    (d.integrable_modulus_min_rpow v (one_div_pos.mpr (by exact_mod_cast NeZero.pos n))).const_mul C
  have bound (q : P) (a : Kˣ) : ‖G q a‖ ≤ W a := by
    have hs : 0 < m a.val := by cases v <;> simp [modulus,norm_pos_iff,a.ne_zero,pow_pos]
    obtain ⟨r,hr,h⟩ := hg q a
    exact (show ‖G q a‖ = m a.val * ‖g q a‖ by simp only [G,norm_smul,Real.norm_of_nonneg hs.le]).le.trans
      (line_weight_bound hs hr hC h)
  have hi (q : P) : Integrable (G q) (d.lineMeasure v) :=
    hW.mono' (cont.comp (f := fun a : Kˣ => (q,a)) (continuous_const.prodMk continuous_id)).aestronglyMeasurable
      (.of_forall (bound q))
  have transfer (q : P) := d.lineMeasure_modulus v (f q)
  have val (q : P) (a : Kˣ) : m a.val • f q a.val = G q a := by
    simp only [f,dif_pos a.ne_zero,Units.mk0_val,G]
  simp_rw [val] at transfer
  refine ⟨fun q => (transfer q).1.mp (hi q),?_⟩
  apply Continuous.congr _ (fun q => (transfer q).2)
  exact continuous_of_dominated (bound := W) (fun q => (hi q).aestronglyMeasurable)
    (fun q => .of_forall (bound q)) hW (.of_forall fun a =>
      cont.comp (f := fun q : P => (q,a)) (continuous_id.prodMk continuous_const))

/-- The local chart bound (4.2) at order N. -/
def ChartGrowth (v : Place F) (n N : ℕ) (f : Charts (LocalField F v)) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ z : LocalField F v × LocalField F v, z ≠ 0 →
    let r := max (modulus F v z.1) (modulus F v z.2)
    let bound := C * min (r^(-(growthExponent n))) (r^(-(N : ℝ)))
    ‖xChart f z‖ ≤ bound ∧ ‖yChart f z‖ ≤ bound

/-- Absolute convergence and joint continuity for any two continuous charts satisfying
the growth estimate (4.2) at order two, including on the line through the origin. -/
theorem radon_convergence_of_growth (f : Charts K)
    (hx : Continuous (Function.uncurry f.1)) (hy : Continuous (Function.uncurry f.2))
    (h : ChartGrowth v n 2 f) :
    (∀ t a b, Integrable (lineIntegrandX (d.symbol v) f n t a b) dx) ∧
    (∀ t a b, Integrable (lineIntegrandY (d.symbol v) f n t a b) dx) ∧
    (Continuous fun q : (Kˣ × K) × K => (d.radonAt v f q.2).1 q.1.1 q.1.2) ∧
    (Continuous fun q : (K × Kˣ) × K => (d.radonAt v f q.2).2 q.1.1 q.1.2) := by
  obtain ⟨C,hC,hg⟩ := h
  letI : FirstCountableTopology Kˣ := Units.isEmbedding_val₀.firstCountableTopology
  let X (q : (Kˣ × K) × K) (a : Kˣ) :=
    f.1 a ((a.val*q.1.2-q.2^n)/q.1.1.val) * d.symbol v a (-q.1.1)
  have ccX : Continuous (Function.uncurry X) := by
    apply (hx.comp (continuous_snd.prodMk (show Continuous (fun q : ((Kˣ × K) × K) × Kˣ =>
      (q.2.val*q.1.1.2-q.1.2^n)/q.1.1.1.val) by fun_prop (disch := simp)))).mul
    exact (d.continuous_symbol v).comp (continuous_snd.prodMk (Units.isEmbedding_val₀.continuous_iff.mpr
      (show Continuous (fun q : ((Kˣ × K) × K) × Kˣ => -q.1.1.1.val) by fun_prop)))
  obtain ⟨iX,cX⟩ := d.line_family_of_growth v X ccX hC (by
    intro q a
    let y := ((a.val*q.1.2-q.2^n)/q.1.1.val)
    have hn : (a.val,y) ≠ (0 : K × K) := fun h => a.ne_zero (congrArg Prod.fst h)
    refine ⟨_,le_max_left (m a.val) (m y),?_⟩
    simpa only [Nat.cast_ofNat,X,norm_mul,d.norm_symbol,mul_one,xChart,dif_pos a.ne_zero,Units.mk0_val]
      using (hg (a.val,y) hn).1)
  let Y (q : (K × Kˣ) × K) (b : Kˣ) :=
    f.2 ((q.1.1*b.val+q.2^n)/q.1.2.val) b * d.symbol v b q.1.2 * d.symbol v (-1) q.1.2
  have ccY : Continuous (Function.uncurry Y) := by
    let b (q : ((K × Kˣ) × K) × Kˣ) := q.1.1.2
    have cb : Continuous b := continuous_snd.comp (continuous_fst.comp continuous_fst)
    have hsym := (d.continuous_symbol v).comp (continuous_snd.prodMk cb)
    have hneg := (d.continuous_symbol v).comp ((continuous_const (y := (-1 : Kˣ))).prodMk cb)
    have harg : Continuous (fun q : ((K × Kˣ) × K) × Kˣ =>
        (q.1.1.1*q.2.val+q.1.2^n)/q.1.1.2.val) := by fun_prop (disch := simp)
    exact ((hy.comp (harg.prodMk continuous_snd)).mul hsym).mul hneg
  obtain ⟨iY,cY⟩ := d.line_family_of_growth v Y ccY hC (by
    intro q b
    let x := ((q.1.1*b.val+q.2^n)/q.1.2.val)
    have hn : (x,b.val) ≠ (0 : K × K) := fun h => b.ne_zero (congrArg Prod.snd h)
    refine ⟨_,le_max_right (m x) (m b.val),?_⟩
    simpa only [Nat.cast_ofNat,Y,norm_mul,d.norm_symbol,mul_one,yChart,dif_pos b.ne_zero,Units.mk0_val]
      using (hg (x,b.val) hn).2)
  refine ⟨fun t a b => iX ((a,b),t),fun t a b => iY ((a,b),t),?_,?_⟩
  · exact cX.div (Complex.continuous_ofReal.comp ((continuous_local_modulus v).comp
      (Units.continuous_val.comp (continuous_fst.comp continuous_fst))))
      (fun q => Complex.ofReal_ne_zero.mpr (modulus_ne_zero v q.1.1))
  · exact cY.div (Complex.continuous_ofReal.comp ((continuous_local_modulus v).comp
      (Units.continuous_val.comp (continuous_snd.comp continuous_fst))))
      (fun q => Complex.ofReal_ne_zero.mpr (modulus_ne_zero v q.1.2))

/-- The local growth estimate (4.2) for an arbitrary pair of local coordinates
at a finite place, including the two axes. -/
theorem finite_chart_growth (p : Prime F) (Φ : d.schwartz (.inr p)) (N : ℕ) (hN : 1 ≤ N) :
    ChartGrowth (.inr p) n N Φ.val := by
  let vp : Place F := .inr p
  let L := LocalField F vp
  obtain ⟨A,hA,hx⟩ := d.finite_vertical_growth p Φ
  obtain ⟨B,_,hy⟩ := d.finite_horizontal_growth p Φ
  obtain ⟨S,hS,hout⟩ := (d.finite_germs p Φ).2.1
  obtain ⟨R,hR⟩ := hS.isBounded.exists_norm_le
  let M := max A B
  let D := max 1 R
  let C := M*D^N
  have hM : 0 ≤ M := hA.trans (le_max_left ..)
  have hD : 1 ≤ D := le_max_left ..
  have hMC : M ≤ C := le_mul_of_one_le_right hM (one_le_pow₀ hD)
  have he (a b : Lˣ) : ‖Φ.val.1 a b.val‖ = ‖Φ.val.2 a.val b‖ := by
    rw [d.schwartz_glues vp Φ a b,norm_mul,d.norm_symbol,one_mul]
  have bound {r b : ℝ} (hr : 0 < r) (hrD : r ≤ D) (hb : 0 ≤ b) (H : b*r^(growthExponent n) ≤ M) :
      b ≤ C*min (r^(-growthExponent n)) (r^(-(N:ℝ))) := by
    rw [mul_min_of_nonneg _ _ (hM.trans hMC),le_min_iff,Real.rpow_neg hr.le,Real.rpow_neg hr.le,
      ← div_eq_mul_inv,← div_eq_mul_inv,le_div_iff₀ (Real.rpow_pos_of_pos hr _),
      le_div_iff₀ (Real.rpow_pos_of_pos hr _)]
    refine ⟨H.trans hMC,?_⟩
    rcases le_total r 1 with h|h
    · have he' : growthExponent n ≤ (N:ℝ) := (growthExponent_le_one n).trans (by exact_mod_cast hN)
      exact (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hr h he') hb).trans (H.trans hMC)
    · rw [Real.rpow_natCast]
      have h' : b ≤ M := (le_mul_of_one_le_right hb (Real.one_le_rpow h (growthExponent_nonneg n))).trans H
      exact mul_le_mul h' (pow_le_pow_left₀ hr.le hrD N) (pow_nonneg hr.le _) hM
  refine ⟨C,hM.trans hMC,?_⟩
  rintro ⟨x,y⟩ hn
  let r := max ‖x‖ ‖y‖
  let W := C*min (r^(-growthExponent n)) (r^(-(N:ℝ)))
  change ‖xChart Φ.val (x,y)‖ ≤ W ∧ ‖yChart Φ.val (x,y)‖ ≤ W
  have hr : 0 < r := norm_pos_iff.mpr hn
  have hW : 0 ≤ W := mul_nonneg (hM.trans hMC) (le_min (Real.rpow_nonneg hr.le _) (Real.rpow_nonneg hr.le _))
  by_cases hs : (x,y) ∈ S
  · have hrD : r ≤ D := (hR _ hs).trans (le_max_right ..)
    rcases le_total ‖y‖ ‖x‖ with h|h
    · have er : r = ‖x‖ := max_eq_left h
      have hn' : x ≠ 0 := norm_pos_iff.mp (er ▸ hr)
      let a := Units.mk0 x hn'
      have H : ‖Φ.val.1 a y‖ ≤ W := bound hr hrD (norm_nonneg _) (er ▸ (hx a y).trans (le_max_left ..))
      refine ⟨by simpa only [xChart,dif_pos hn',a] using H,?_⟩
      by_cases hy' : y ≠ 0
      · simpa only [yChart,dif_pos hy',a,Units.val_mk0] using! (he a (Units.mk0 y hy')).symm.trans_le H
      · simpa only [yChart,dif_neg hy',norm_zero] using hW
    · have er : r = ‖y‖ := max_eq_right h
      have hn' : y ≠ 0 := norm_pos_iff.mp (er ▸ hr)
      let b := Units.mk0 y hn'
      have H : ‖Φ.val.2 x b‖ ≤ W := bound hr hrD (norm_nonneg _) (er ▸ (hy x b).trans (le_max_right ..))
      refine ⟨?_,by simpa only [yChart,dif_pos hn',b] using H⟩
      by_cases hx' : x ≠ 0
      · simpa only [xChart,dif_pos hx',b,Units.val_mk0] using! (he (Units.mk0 x hx') b).trans_le H
      · simpa only [xChart,dif_neg hx',norm_zero] using hW
  · obtain ⟨hz,hz'⟩ := hout _ hs
    simpa only [hz,hz',norm_zero,and_self] using hW

theorem schwartz_chart_growth (Φ : d.schwartz v) (N : ℕ) (hN : 1 ≤ N) : ChartGrowth v n N Φ.val := by
  cases v with
  | inl w => exact d.arch_local_growth w Φ N hN
  | inr p => exact d.finite_chart_growth p Φ N hN

theorem continuous_schwartz_charts (Φ : d.schwartz v) :
    Continuous (Function.uncurry Φ.val.1) ∧ Continuous (Function.uncurry Φ.val.2) := by
  cases v with
  | inl w => exact d.continuous_arch_schwartz_charts w Φ
  | inr p =>
    obtain ⟨hx,hy⟩ := d.locallyConstant_finite_schwartz p Φ
    exact ⟨hx.continuous,hy.continuous⟩

/-- Every local Schwartz section has absolutely convergent Radon integrals,
jointly continuous in the chart vector and the root parameter. -/
theorem schwartz_radon_convergence (Φ : d.schwartz v) :
    (∀ t a b, Integrable (lineIntegrandX (d.symbol v) Φ.val n t a b) dx) ∧
    (∀ t a b, Integrable (lineIntegrandY (d.symbol v) Φ.val n t a b) dx) ∧
    (Continuous fun q : (Kˣ × K) × K => (d.radonAt v Φ.val q.2).1 q.1.1 q.1.2) ∧
    (Continuous fun q : (K × Kˣ) × K => (d.radonAt v Φ.val q.2).2 q.1.1 q.1.2) := by
  obtain ⟨hx,hy⟩ := d.continuous_schwartz_charts v Φ
  exact d.radon_convergence_of_growth v Φ.val hx hy (d.schwartz_chart_growth v Φ 2 (by decide))

end MetaplecticPoisson.Datum
