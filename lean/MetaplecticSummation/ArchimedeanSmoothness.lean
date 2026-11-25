import MetaplecticSummation.LineSmoothness
import MetaplecticSummation.ArchimedeanFourierDecay
import MetaplecticSummation.Schwartz

/-! Smoothness at real and complex places (Lemma 4.2(iii), Proposition 4.5).

The Radon charts of a test section are jointly smooth in the point of the punctured plane
and the line parameter, the charts of its transform are smooth, and hence every element of
the local Schwartz space has smooth charts. The substitution x = x′z identifies each
Radon chart with the linearized line integral of `LineSmoothness`. -/

noncomputable section
namespace MetaplecticPoisson
open NumberField MeasureTheory Set Filter
open scoped Topology ContDiff
open Classical

/-- A total lift to the units, used only away from zero. -/
def unitOf {K : Type} [NormedField K] (x : K) : Kˣ := if hx : x ≠ 0 then Units.mk0 x hx else 1

theorem unitOf_val {K : Type} [NormedField K] {x : K} (hx : x ≠ 0) : (unitOf x).val = x := by
  simp [unitOf,hx]

theorem unitOf_continuousAt {K : Type} [NormedField K] {x : K} (hx : x ≠ 0) : ContinuousAt unitOf x := by
  apply Units.isEmbedding_val₀.tendsto_nhds_iff.mpr
  rw [unitOf_val hx]
  exact tendsto_id.congr' ((eventually_ne_nhds hx).mono fun _ hz => (unitOf_val hz).symm)

namespace Datum
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n) (w : InfinitePlace F)
local notation "v" => (Sum.inl w : Place F)
local notation "K" => LocalField F v
local notation "dx" => selfDual F d.character v

theorem symbol_mul_left_units (a b c : Kˣ) : d.symbol v (a*b) c = d.symbol v a c * d.symbol v b c := by
  simp only [← coe_unitPairing,map_mul,MonoidHom.mul_apply,Units.val_mul]

theorem symbol_neg_self' (a : Kˣ) : d.symbol v a (-a) = 1 := by
  rw [← coe_unitPairing,d.unitPairing_neg_self v a,Units.val_one]

/-- The X-chart phase after the substitution x = x′z. -/
def phaseX {L : Type} [NormedField L] (e : K ≃+* L) (z : K) (U : L) : ℂ :=
  if z ≠ 0 ∧ e.symm U ≠ 0 then d.symbol v (unitOf z) (-unitOf (e.symm U)) else 0

/-- The Y-chart phase after the substitution y = y′z. -/
def phaseY {L : Type} [NormedField L] (e : K ≃+* L) (z : K) (U : L) : ℂ :=
  if z ≠ 0 ∧ e.symm U ≠ 0 then d.symbol v (unitOf z) (unitOf (e.symm U)) else 0

set_option backward.isDefEq.respectTransparency false in
/-- The substitution x = x′z in the X-chart Radon integral. -/
theorem radon_fst_eq_lineRadon {L : Type} [NormedField L] [NormedAlgebra ℝ L] (e : K ≃+* L)
    (f : Charts K) (t : K) (u : Kˣ) (y : K) :
    (radon n (d.symbol v) (modulus F v) dx f t).1 u y =
      lineRadon dx e (d.phaseX w e) (fun p => xChart f (e.symm p.1, e.symm p.2))
        (e u, e y, e (t^n / u)) := by
  let G : K → ℂ := fun x => if hx : x ≠ 0 then
    f.1 (Units.mk0 x hx) ((x * y - t ^ n) / (u : K)) * d.symbol v (Units.mk0 x hx) (-u) else 0
  have hl := d.integral_local_mul v u G
  dsimp only at hl
  change (∫ x, G x ∂dx) / (modulus F v u : ℂ) = _
  rw [← hl]
  unfold lineRadon
  congr 1; funext z
  by_cases hz : z = 0
  · simp [G,hz]
  have hzu : (u : K) * z ≠ 0 := mul_ne_zero u.ne_zero hz
  have hU : unitOf z = Units.mk0 z hz := Units.ext (unitOf_val hz)
  have hu : unitOf (u : K) = u := Units.ext (unitOf_val u.ne_zero)
  have hmk : Units.mk0 ((u : K) * z) hzu = u * Units.mk0 z hz := Units.ext rfl
  simp only [G,ne_eq,hzu,not_false_eq_true,dite_true,hz,ite_false,phaseX,e.symm_apply_apply,u.ne_zero,
    and_self,ite_true,lineAffine_apply,xChart,hU,hu]
  rw [hmk,symbol_mul_left_units,symbol_neg_self',one_mul]
  have h1 : e.symm (e z * e u) = (u : K) * z := by rw [← map_mul,e.symm_apply_apply,mul_comm]
  have h2 : e.symm (e z * e y - e (t ^ n / u)) = ((u : K) * z * y - t ^ n) / u := by
    rw [← map_mul,← map_sub,e.symm_apply_apply]; field_simp [u.ne_zero]
  simp only [h1,h2,hzu,not_false_eq_true,dite_true,hmk]
  ring

set_option backward.isDefEq.respectTransparency false in
/-- The substitution y = y′z in the Y-chart Radon integral. -/
theorem radon_snd_eq_lineRadon {L : Type} [NormedField L] [NormedAlgebra ℝ L] (e : K ≃+* L)
    (f : Charts K) (t : K) (x : K) (u : Kˣ) :
    (radon n (d.symbol v) (modulus F v) dx f t).2 x u =
      lineRadon dx e (d.phaseY w e) (fun p => yChart f (e.symm p.2, e.symm p.1))
        (e u, e x, -e (t^n / u)) := by
  let G : K → ℂ := fun y => if hy : y ≠ 0 then
    f.2 ((x * y + t ^ n) / (u : K)) (Units.mk0 y hy) * d.symbol v (Units.mk0 y hy) u * d.symbol v (-1) u else 0
  have hl := d.integral_local_mul v u G
  dsimp only at hl
  change (∫ y, G y ∂dx) / (modulus F v u : ℂ) = _
  rw [← hl]
  unfold lineRadon
  congr 1; funext z
  by_cases hz : z = 0
  · simp [G,hz]
  have hzu : (u : K) * z ≠ 0 := mul_ne_zero u.ne_zero hz
  have hU : unitOf z = Units.mk0 z hz := Units.ext (unitOf_val hz)
  have hu : unitOf (u : K) = u := Units.ext (unitOf_val u.ne_zero)
  have hmk : Units.mk0 ((u : K) * z) hzu = u * Units.mk0 z hz := Units.ext rfl
  have hs : d.symbol v u u * d.symbol v (-1) u = 1 := by
    rw [← symbol_mul_left_units,show u * (-1) = -u by simp]
    have := d.symbol_neg_self' w (-u); rwa [neg_neg] at this
  simp only [G,ne_eq,hzu,not_false_eq_true,dite_true,hz,ite_false,phaseY,e.symm_apply_apply,u.ne_zero,
    and_self,ite_true,lineAffine_apply,yChart,hU,hu]
  have h1 : e.symm (e z * e u) = (u : K) * z := by rw [← map_mul,e.symm_apply_apply,mul_comm]
  have h2 : e.symm (e z * e x - -e (t ^ n / u)) = (x * ((u : K) * z) + t ^ n) / u := by
    rw [sub_neg_eq_add,← map_mul,← map_add,e.symm_apply_apply]; field_simp [u.ne_zero]
  simp only [h1,h2,hzu,not_false_eq_true,dite_true,hmk,symbol_mul_left_units]
  linear_combination (f.2 ((x * (↑u * z) + t ^ n) / ↑u) (u * Units.mk0 z hz) * d.symbol v (Units.mk0 z hz) u) * hs

theorem isometry_symm {L : Type} [NormedField L] (e : K ≃+* L) (he : Isometry e) : Isometry e.symm :=
  fun x y => by rw [← he (e.symm x) (e.symm y),e.apply_symm_apply,e.apply_symm_apply]

/-- A phase built from the symbol is locally constant in U, continuous in z, and bounded by one. -/
theorem phase_properties {L : Type} [NormedField L] [NormedAlgebra ℝ L] (e : K ≃+* L) (he : Isometry e)
    (σ : Kˣ → Kˣ) (hσ : Continuous σ) :
    let c : K → L → ℂ := fun z U =>
      if z ≠ 0 ∧ e.symm U ≠ 0 then d.symbol v (unitOf z) (σ (unitOf (e.symm U))) else 0
    (∀ z, z ≠ 0 → ∀ U : L, U ≠ 0 → ∀ᶠ U' in 𝓝 U, c z U' = c z U) ∧
    (∀ U : L, U ≠ 0 → ContinuousOn (fun z => c z U) {z | z ≠ 0}) ∧
    (∀ z U, ‖c z U‖ ≤ 1) := by
  intro c
  have hes : Continuous e.symm := (isometry_symm w e he).continuous
  refine ⟨fun z hz U hU => ?_,fun U hU => ?_,fun z U => ?_⟩
  · have hU1 : e.symm U ≠ 0 := (map_ne_zero e.symm).mpr hU
    have hlc : IsLocallyConstant (fun b : Kˣ => d.symbol v (unitOf z) (σ b)) :=
      ((d.locallyConstant_unitPairing v).comp_continuous (continuous_const.prodMk hσ)).comp Units.val
    have h1 := ((unitOf_continuousAt hU1).comp hes.continuousAt).eventually (hlc.eventually_eq (unitOf (e.symm U)))
    filter_upwards [h1,eventually_ne_nhds hU] with U2 h hU2
    have hU3 : e.symm U2 ≠ 0 := (map_ne_zero e.symm).mpr hU2
    simp only [c,hz,hU1,hU3,ne_eq,not_false_eq_true,and_self,ite_true]
    exact h
  · have hU1 : e.symm U ≠ 0 := (map_ne_zero e.symm).mpr hU
    intro z hz
    have hz' : z ≠ 0 := hz
    have h1 : ContinuousAt (fun z => d.symbol v (unitOf z) (σ (unitOf (e.symm U)))) z :=
      (d.continuous_symbol v).continuousAt.comp ((unitOf_continuousAt hz').prodMk continuousAt_const)
    refine (h1.congr ?_).continuousWithinAt
    filter_upwards [eventually_ne_nhds hz'] with z2 hz2
    simp [c,hz2,hU]
  · simp only [c]; split_ifs
    · rw [d.norm_symbol]
    · simp

theorem phaseX_eq {L : Type} [NormedField L] (e : K ≃+* L) :
    d.phaseX w e = fun z U => if z ≠ 0 ∧ e.symm U ≠ 0 then
      d.symbol v (unitOf z) ((fun a : Kˣ => -a) (unitOf (e.symm U))) else 0 := rfl

theorem phaseY_eq {L : Type} [NormedField L] (e : K ≃+* L) :
    d.phaseY w e = fun z U => if z ≠ 0 ∧ e.symm U ≠ 0 then
      d.symbol v (unitOf z) (id (unitOf (e.symm U))) else 0 := rfl

theorem rapid_swapped_yChart {L : Type} [NormedField L] [NormedAlgebra ℝ L] (e : K ≃+* L) {f : Charts K}
    (htest : archTest e f) :
    rapidChart {p : L × L | p.1 ≠ 0} (fun p => yChart f (e.symm p.2, e.symm p.1)) := by
  have hy := rapidChart_comp_equiv htest.2 (ContinuousLinearEquiv.prodComm ℝ L L)
  exact hy

theorem contDiffOn_reciprocal_coords {L : Type} [NormedField L] [NormedAlgebra ℝ L] (k : ℕ) (s : L) :
    ContDiffOn ℝ ∞ (fun P : L × L × L => (P.1, P.2.1, s * (P.2.2 ^ k * P.1⁻¹))) {P | P.1 ≠ 0} := by
  intro P hP
  have hP' : P.1 ≠ 0 := hP
  refine ContDiffAt.contDiffWithinAt ?_
  refine contDiffAt_fst.prodMk (contDiffAt_fst.comp P contDiffAt_snd |>.prodMk ?_)
  exact contDiffAt_const.mul (((contDiffAt_snd.comp P contDiffAt_snd).pow k).mul
    ((contDiffAt_inv ℝ hP').comp P contDiffAt_fst))

/-- Lemma 4.2(iii) at a real or complex place: both Radon charts are jointly smooth in the
point of the punctured plane and the line parameter. -/
theorem arch_radon_smooth {L : Type} [NormedField L] [NormedAlgebra ℝ L] (e : K ≃+* L) (he : Isometry e)
    {f : Charts K} (htest : archTest e f) :
    let R := radon n (d.symbol v) (modulus F v) dx f
    ContDiffOn ℝ ∞ (fun P : L × L × L => (R (e.symm P.2.2)).1 (unitOf (e.symm P.1)) (e.symm P.2.1))
      {P | P.1 ≠ 0} ∧
    ContDiffOn ℝ ∞ (fun P : L × L × L => (R (e.symm P.2.2)).2 (e.symm P.1) (unitOf (e.symm P.2.1)))
      {P | P.2.1 ≠ 0} := by
  intro R
  let : SecondCountableTopology K :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  have hneg : Continuous (fun a : Kˣ => -a) := Units.isEmbedding_val₀.continuous_iff.mpr Units.continuous_val.neg
  obtain ⟨hx1,hx2,hx3⟩ := d.phase_properties w e he (fun a => -a) hneg
  obtain ⟨hy1,hy2,hy3⟩ := d.phase_properties w e he id continuous_id
  have HX := (lineRadon_smooth dx e he (d.arch_integrable_inv_cube w) htest.1 (d.phaseX w e)
    hx1 hx2 hx3).1
  have HY := (lineRadon_smooth dx e he (d.arch_integrable_inv_cube w) (rapid_swapped_yChart w e htest)
    (d.phaseY w e) hy1 hy2 hy3).1
  have key (P : L × L × L) (h : e.symm P.1 ≠ 0) : e (unitOf (e.symm P.1)) = P.1 := by
    rw [unitOf_val h,e.apply_symm_apply]
  constructor
  · refine (HX.comp (contDiffOn_reciprocal_coords n 1) (fun P hP => by simpa using hP)).congr ?_
    intro P hP
    have hP' : e.symm P.1 ≠ 0 := (map_ne_zero e.symm).mpr hP
    simp only [Function.comp_apply,R]
    rw [d.radon_fst_eq_lineRadon w e f,key P hP',e.apply_symm_apply,map_div₀,map_pow,e.apply_symm_apply,
      key P hP',one_mul,div_eq_mul_inv]
  · refine (HY.comp (contDiffOn_reciprocal_coords n (-1))
      (fun P hP => by simpa using hP)).comp (f := fun P : L × L × L => (P.2.1, P.1, P.2.2))
      (by fun_prop : ContDiff ℝ ∞ fun P : L × L × L => (P.2.1, P.1, P.2.2)).contDiffOn
      (fun P hP => hP) |>.congr ?_
    intro P hP
    have hP0 : P.2.1 ≠ 0 := hP
    have hP' : e.symm P.2.1 ≠ 0 := (map_ne_zero e.symm).mpr hP0
    have key' : e (unitOf (e.symm P.2.1)) = P.2.1 := by rw [unitOf_val hP',e.apply_symm_apply]
    simp only [Function.comp_apply,R]
    rw [d.radon_snd_eq_lineRadon w e f,key',e.apply_symm_apply,map_div₀,map_pow,e.apply_symm_apply,key']
    congr 2
    ring_nf

/-- The Fourier integrals of the Radon charts at any unitary continuous frequency function are smooth. -/
theorem arch_radon_fourier_smooth {L : Type} [NormedField L] [NormedAlgebra ℝ L] (e : K ≃+* L) (he : Isometry e)
    {f : Charts K} (htest : archTest e f) {ψ : K → ℂ} (hψ : Continuous ψ) (hψ1 : ∀ t, ‖ψ t‖ = 1) :
    let R := radon n (d.symbol v) (modulus F v) dx f
    let c₀ : ℂ := (Real.sqrt (modulus F v (n : K)))⁻¹
    let g : Charts K := (fun a b => c₀ * ∫ t, ψ t * (R t).1 a b ∂dx, fun a b => c₀ * ∫ t, ψ t * (R t).2 a b ∂dx)
    ContDiffOn ℝ ∞ (fun p : L × L => xChart g (e.symm p.1, e.symm p.2)) {p | p.1 ≠ 0} ∧
    ContDiffOn ℝ ∞ (fun p : L × L => yChart g (e.symm p.1, e.symm p.2)) {p | p.2 ≠ 0} := by
  intro R c₀ g
  let : SecondCountableTopology K :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  have hneg : Continuous (fun a : Kˣ => -a) := Units.isEmbedding_val₀.continuous_iff.mpr Units.continuous_val.neg
  obtain ⟨hx1,hx2,hx3⟩ := d.phase_properties w e he (fun a => -a) hneg
  obtain ⟨hy1,hy2,hy3⟩ := d.phase_properties w e he id continuous_id
  have hint := d.arch_integrable_inv_cube w
  have HX := lineRadon_smooth dx e he hint htest.1 (d.phaseX w e) hx1 hx2 hx3
  have HY := lineRadon_smooth dx e he hint (rapid_swapped_yChart w e htest) (d.phaseY w e) hy1 hy2 hy3
  have QX := lineFourier_smooth dx e he hint n (NeZero.pos n) hψ hψ1 HX.1 HX.2
  have QY := lineFourier_smooth dx e he hint n (NeZero.pos n) hψ hψ1 HY.1 HY.2
  have hinvX : ContDiffOn ℝ ∞ (fun p : L × L => (p.1, p.2, p.1⁻¹)) {p | p.1 ≠ 0} := by
    intro p hp
    exact (contDiffAt_fst.prodMk (contDiffAt_snd.prodMk
      ((contDiffAt_inv ℝ (show p.1 ≠ 0 from hp)).comp p contDiffAt_fst))).contDiffWithinAt
  have hinvY : ContDiffOn ℝ ∞ (fun p : L × L => (p.2, p.1, -p.2⁻¹)) {p | p.2 ≠ 0} := by
    intro p hp
    exact (contDiffAt_snd.prodMk (contDiffAt_fst.prodMk
      ((contDiffAt_inv ℝ (show p.2 ≠ 0 from hp)).comp p contDiffAt_snd).neg)).contDiffWithinAt
  constructor
  · refine (contDiffOn_const (c := c₀).mul (QX.comp hinvX ?_)).congr ?_
    · intro p hp; exact ⟨hp,inv_ne_zero hp⟩
    intro p hp
    have hp' : e.symm p.1 ≠ 0 := (map_ne_zero e.symm).mpr hp
    have hu : e (Units.mk0 (e.symm p.1) hp') = p.1 := by simp
    have hx : xChart g (e.symm p.1, e.symm p.2) = g.1 (Units.mk0 (e.symm p.1) hp') (e.symm p.2) := by
      simp [xChart,hp']
    simp only [Function.comp_apply]
    rw [hx]
    change c₀ * ∫ t, ψ t * (R t).1 (Units.mk0 (e.symm p.1) hp') (e.symm p.2) ∂dx = _
    congr 1; congr 1; funext t
    rw [d.radon_fst_eq_lineRadon w e f,hu,e.apply_symm_apply,map_div₀,map_pow,hu,div_eq_mul_inv]
  · refine (contDiffOn_const (c := c₀).mul (QY.comp hinvY ?_)).congr ?_
    · intro p hp; exact ⟨hp,neg_ne_zero.mpr (inv_ne_zero hp)⟩
    intro p hp
    have hp' : e.symm p.2 ≠ 0 := (map_ne_zero e.symm).mpr hp
    have hu : e (Units.mk0 (e.symm p.2) hp') = p.2 := by simp
    have hy : yChart g (e.symm p.1, e.symm p.2) = g.2 (e.symm p.1) (Units.mk0 (e.symm p.2) hp') := by
      simp [yChart,hp']
    simp only [Function.comp_apply]
    rw [hy]
    change c₀ * ∫ t, ψ t * (R t).2 (e.symm p.1) (Units.mk0 (e.symm p.2) hp') ∂dx = _
    congr 1; congr 1; funext t
    rw [d.radon_snd_eq_lineRadon w e f,hu,e.apply_symm_apply,map_div₀,map_pow,hu]
    congr 2; ring_nf

/-- Proposition 4.5 at a real or complex place: the transform of a test section has smooth charts. -/
theorem arch_transform_smooth {L : Type} [NormedField L] [NormedAlgebra ℝ L] (e : K ≃+* L) (he : Isometry e)
    {f : Charts K} (htest : archTest e f) :
    let g := d.integralTransform v f
    ContDiffOn ℝ ∞ (fun p : L × L => xChart g (e.symm p.1, e.symm p.2)) {p | p.1 ≠ 0} ∧
    ContDiffOn ℝ ∞ (fun p : L × L => yChart g (e.symm p.1, e.symm p.2)) {p | p.2 ≠ 0} :=
  d.arch_radon_fourier_smooth w e he htest (d.character.continuous_localValue v)
    (d.character.norm_localValue v)

/-- The leading term (§8) of the transform of a test section has smooth charts at a real or
complex place: it is the Fourier integral of the Radon charts at frequency zero. -/
theorem arch_radonLeading_smooth {L : Type} [NormedField L] [NormedAlgebra ℝ L] (e : K ≃+* L)
    (he : Isometry e) {f : Charts K} (htest : archTest e f) :
    let g := d.radonLeading v f
    ContDiffOn ℝ ∞ (fun p : L × L => xChart g (e.symm p.1, e.symm p.2)) {p | p.1 ≠ 0} ∧
    ContDiffOn ℝ ∞ (fun p : L × L => yChart g (e.symm p.1, e.symm p.2)) {p | p.2 ≠ 0} := by
  have h := d.arch_radon_fourier_smooth w e he htest (ψ := fun _ => 1) continuous_const (fun _ => norm_one)
  simp only [one_mul] at h
  exact h

/-- Both charts are smooth in real coordinates on their open domains. -/
def archSmoothCharts {L : Type} [NormedField L] [NormedAlgebra ℝ L] (e : K ≃+* L) (g : Charts K) : Prop :=
  ContDiffOn ℝ ∞ (fun p : L × L => xChart g (e.symm p.1, e.symm p.2)) {p | p.1 ≠ 0} ∧
  ContDiffOn ℝ ∞ (fun p : L × L => yChart g (e.symm p.1, e.symm p.2)) {p | p.2 ≠ 0}

omit [NeZero n] in
theorem archSmoothCharts_add {L : Type} [NormedField L] [NormedAlgebra ℝ L] (e : K ≃+* L) {g h : Charts K}
    (hg : archSmoothCharts w e g) (hh : archSmoothCharts w e h) : archSmoothCharts w e (g + h) := by
  refine ⟨(hg.1.add hh.1).congr fun p _ => ?_,(hg.2.add hh.2).congr fun p _ => ?_⟩
  · simp only [xChart,Prod.fst_add,Pi.add_apply]; split_ifs <;> simp
  · simp only [yChart,Prod.snd_add,Pi.add_apply]; split_ifs <;> simp

omit [NeZero n] in
theorem archSmoothCharts_smul {L : Type} [NormedField L] [NormedAlgebra ℝ L] (e : K ≃+* L) {g : Charts K}
    (a : ℂ) (hg : archSmoothCharts w e g) : archSmoothCharts w e (a • g) := by
  refine ⟨((contDiffOn_const (c := a)).mul hg.1).congr fun p _ => ?_,((contDiffOn_const (c := a)).mul hg.2).congr fun p _ => ?_⟩
  · simp only [xChart,Prod.smul_fst,Pi.smul_apply,smul_eq_mul]; split_ifs <;> simp
  · simp only [yChart,Prod.smul_snd,Pi.smul_apply,smul_eq_mul]; split_ifs <;> simp

omit [NeZero n] in
theorem archSmoothCharts_zero {L : Type} [NormedField L] [NormedAlgebra ℝ L] (e : K ≃+* L) :
    archSmoothCharts w e (0 : Charts K) := by
  refine ⟨(contDiffOn_const (c := (0:ℂ))).congr fun p _ => ?_,(contDiffOn_const (c := (0:ℂ))).congr fun p _ => ?_⟩
  · show xChart 0 _ = (0 : ℂ); simp [xChart]
  · show yChart 0 _ = (0 : ℂ); simp [yChart]

/-- At a real or complex place, every element of the local Schwartz space has smooth charts,
given real coordinates in which the test sections are rapid. -/
theorem schwartz_archSmoothCharts {L : Type} [NormedField L] [NormedAlgebra ℝ L] (e : K ≃+* L)
    (he : Isometry e) (htests : ∀ f ∈ d.testSet v, archTest e f) :
    ∀ Φ ∈ d.schwartz v, archSmoothCharts w e Φ := by
  intro Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem f hf =>
    rcases hf with hf | ⟨f₀,hf₀,rfl⟩
    · exact ⟨(htests f hf).1.1,(htests f hf).2.1⟩
    · exact d.arch_transform_smooth w e he (htests f₀ hf₀)
  | zero => exact archSmoothCharts_zero w e
  | add _ _ _ _ hg hh => exact archSmoothCharts_add w e hg hh
  | smul a _ _ hg => exact archSmoothCharts_smul w e a hg

/-- Proposition 8.1 at a real or complex place: the leading term of every element of the
local Schwartz space has smooth charts. -/
theorem leading_archSmoothCharts {L : Type} [NormedField L] [NormedAlgebra ℝ L] (e : K ≃+* L)
    (he : Isometry e) (htests : ∀ f ∈ d.testSet v, archTest e f) (Φ : d.schwartz v) :
    archSmoothCharts w e (d.leading v Φ) := by
  refine Submodule.span_induction (p := fun f hf => archSmoothCharts w e (d.leading v ⟨f,hf⟩))
    ?_ ?_ ?_ ?_ Φ.property
  · rintro f (hf | ⟨g,hg,rfl⟩)
    · rw [d.leading_archTest_eq_zero w _ hf]
      exact archSmoothCharts_zero w e
    · rw [d.leading_archTest_transform w hg]
      exact d.arch_radonLeading_smooth w e he (htests g hg)
  · change archSmoothCharts w e (d.leading v 0)
    rw [map_zero]
    exact archSmoothCharts_zero w e
  · intro f g hf hg H J
    change archSmoothCharts w e (d.leading v (⟨f,hf⟩ + ⟨g,hg⟩))
    rw [map_add]
    exact archSmoothCharts_add w e H J
  · intro c f hf H
    change archSmoothCharts w e (d.leading v (c • ⟨f,hf⟩))
    rw [map_smul]
    exact archSmoothCharts_smul w e c H

/-- §4 at a real place: the local Schwartz space consists of smooth sections. -/
theorem schwartz_smooth_real (hw : w.IsReal) :
    ∀ Φ ∈ d.schwartz v, archSmoothCharts w (InfinitePlace.Completion.ringEquivRealOfIsReal hw) Φ :=
  d.schwartz_archSmoothCharts w _ (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw)
    fun f hf => by simpa only [testSet,hw,↓reduceDIte] using! hf.2

/-- §4 at a complex place: the local Schwartz space consists of smooth sections. -/
theorem schwartz_smooth_complex (hw : ¬ w.IsReal) :
    ∀ Φ ∈ d.schwartz v, archSmoothCharts w (InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (InfinitePlace.not_isReal_iff_isComplex.mp hw)) Φ :=
  d.schwartz_archSmoothCharts w _ (InfinitePlace.Completion.isometry_extensionEmbedding w)
    fun f hf => by simpa only [testSet,hw,↓reduceDIte] using! hf.2

/-- Proposition 8.1 at a real place: leading terms of the local Schwartz space are smooth. -/
theorem leading_smooth_real (hw : w.IsReal) (Φ : d.schwartz v) :
    archSmoothCharts w (InfinitePlace.Completion.ringEquivRealOfIsReal hw) (d.leading v Φ) :=
  d.leading_archSmoothCharts w _ (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw)
    (fun f hf => by simpa only [testSet,hw,↓reduceDIte] using! hf.2) Φ

/-- Proposition 8.1 at a complex place: leading terms of the local Schwartz space are smooth. -/
theorem leading_smooth_complex (hw : ¬ w.IsReal) (Φ : d.schwartz v) :
    archSmoothCharts w (InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (InfinitePlace.not_isReal_iff_isComplex.mp hw)) (d.leading v Φ) :=
  d.leading_archSmoothCharts w _ (InfinitePlace.Completion.isometry_extensionEmbedding w)
    (fun f hf => by simpa only [testSet,hw,↓reduceDIte] using! hf.2) Φ

end Datum
end MetaplecticPoisson
