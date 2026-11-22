import MetaplecticSummation.FiniteLines
import MetaplecticSummation.WildSymbols
import MetaplecticSummation.PowerSubgroup

/-! Smooth extension of the line integrands at the axes and local constancy
under integration at a finite place (Lemma 4.2(iii)). -/

noncomputable section
namespace MetaplecticPoisson
open MeasureTheory Filter Set
open scoped Topology
open Classical

/-- A jointly locally constant family with locally uniform compact support is locally
constant even as a family of functions on the entire integration space. -/
theorem locallyConstant_slices_of_localSupport {P X V : Type*} [TopologicalSpace P] [TopologicalSpace X]
    [Zero V] {G : P × X → V} (h : IsLocallyConstant G)
    (hs : ∀ p, ∃ C : Set X, IsCompact C ∧ ∀ᶠ q in 𝓝 p, ∀ x ∉ C, G (q,x) = 0) :
    IsLocallyConstant (fun p x => G (p,x)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro p
  obtain ⟨C,hc,ho⟩ := hs p
  let U : Set (P × X) := {w | G w = G (p,w.2)}
  have he : IsLocallyConstant (fun w : P × X => (G w, G (p,w.2))) :=
    h.prodMk (h.comp_continuous (continuous_const.prodMk continuous_snd))
  have hopen : IsOpen U := he {z | z.1 = z.2}
  obtain ⟨A, B, hA, _, hp, hB, hAB⟩ := generalized_tube_lemma (isCompact_singleton (x := p)) hc hopen
    (by rintro ⟨q,x⟩ ⟨rfl : q = p, _⟩; rfl)
  filter_upwards [hA.mem_nhds (hp rfl), ho] with q hq hq₀
  funext x
  by_cases hx : x ∈ C
  · exact hAB (show (q,x) ∈ A ×ˢ B from ⟨hq, hB hx⟩)
  · rw [hq₀ x hx, ho.self_of_nhds x hx]

private theorem locallyConstant_slices {P X V : Type*} [TopologicalSpace P] [TopologicalSpace X]
    [Zero V] {G : P × X → V} (h : IsLocallyConstant G) {C : Set X} (hc : IsCompact C)
    (hs : ∀ p x, x ∉ C → G (p,x) = 0) : IsLocallyConstant (fun p x => G (p,x)) :=
  locallyConstant_slices_of_localSupport h fun _ => ⟨C,hc,Eventually.of_forall hs⟩

variable {K : Type} [NontriviallyNormedField K] {n : ℕ}

private def liftUnit (x : K) : Kˣ := if hx : x ≠ 0 then Units.mk0 x hx else 1

private theorem liftUnit_val {x : K} (hx : x ≠ 0) : (liftUnit x).val = x := by simp [liftUnit, hx]

private theorem liftUnit_continuousAt {x : K} (hx : x ≠ 0) : ContinuousAt liftUnit x := by
  apply Units.isEmbedding_val₀.tendsto_nhds_iff.mpr
  rw [liftUnit_val hx]
  exact tendsto_id.congr' ((eventually_ne_nhds hx).mono fun _ hz => (liftUnit_val hz).symm)

/-- On the missing axis use the other chart. At the deleted origin both chart
extensions are zero. -/
private def extendedIntegrand (H : LineSymbol K n) (f : Charts K) (x y : K) (c : Kˣ) : ℂ :=
  if x = 0 then yChart f (x,y) else f.1 (liftUnit x) y * (H.pairing (liftUnit x) c : ℂ)

private theorem extendedIntegrand_outside (H : LineSymbol K n) {f : Charts K} {x y : K}
    (c : Kˣ) (hx : xChart f (x,y) = 0) (hy : yChart f (x,y) = 0) :
    extendedIntegrand H f x y c = 0 := by
  by_cases hz : x = 0
  · simp [extendedIntegrand, hz, hz ▸ hy]
  · simp [xChart, hz] at hx
    simp [extendedIntegrand, liftUnit, hz, hx]

private theorem extendedIntegrand_on_powers (H : LineSymbol K n) {f : Charts K}
    (hf : Glues (fun a b => H.pairing a b) f) (x y : K) (c : Kˣ)
    (hy : y ≠ 0) (hp : y * c.val ∈ range (fun z : Kˣ => z.val ^ n)) :
    extendedIntegrand H f x y c = f.2 x (liftUnit y) := by
  by_cases hx : x = 0
  · simp [extendedIntegrand, yChart, hx, hy, liftUnit]
  rcases hp with ⟨z, hz⟩
  have he : liftUnit y * c = z^n :=
    Units.ext (by simpa only [Units.val_mul, Units.val_pow_eq_pow_val, liftUnit_val hy] using hz.symm)
  have hmul : (H.pairing (liftUnit x) (liftUnit y) : ℂ) * (H.pairing (liftUnit x) c : ℂ) = 1 := by
    rw [← Units.val_mul, ← map_mul, he, H.pow_right, Units.val_one]
  have gl := hf (liftUnit x) (liftUnit y)
  simp only [liftUnit_val hx, liftUnit_val hy] at gl
  simp only [extendedIntegrand, if_neg hx, gl]
  linear_combination (f.2 x (liftUnit y)) * hmul

variable [CompleteSpace K]

private theorem locallyConstant_extendedIntegrand {Z : Type*} [TopologicalSpace Z]
    (H : LineSymbol K n) (hn : (n : K) ≠ 0)
    (hl : IsLocallyConstant (fun w : Kˣ × Kˣ => (H.pairing w.1 w.2 : ℂ)))
    {f : Charts K} (gl : Glues (fun a b => H.pairing a b) f) (hf : finiteTest f)
    {x y : Z → K} {c : Z → Kˣ} (hx : Continuous x) (hy : Continuous y) (hc : Continuous c)
    (haxis : ∀ z, x z = 0 → y z ≠ 0 → y z * (c z).val ∈ range (fun u : Kˣ => u.val^n)) :
    IsLocallyConstant (fun z => extendedIntegrand H f (x z) (y z) (c z)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro z
  by_cases xz : x z = 0
  · by_cases yz : y z = 0
    · obtain ⟨C, hC, h0, hs⟩ := hf.2.2
      have hmem : (x z,y z) ∈ Cᶜ := by rw [xz, yz]; exact h0
      have hev := (hx.prodMk hy).continuousAt.eventually (hC.isClosed.isOpen_compl.mem_nhds hmem)
      filter_upwards [hev] with w hw
      rw [extendedIntegrand_outside H _ (hs _ hw).1 (hs _ hw).2,
        extendedIntegrand_outside H _ (hs _ hmem).1 (hs _ hmem).2]
    · have hp := haxis z xz yz
      have he := (hy.mul (Units.continuous_val.comp hc)).continuousAt.eventually
        ((isOpen_nonzero_powers n hn).mem_nhds hp)
      have ht := (hx.continuousAt.prodMk ((liftUnit_continuousAt yz).comp hy.continuousAt)).eventually
        (hf.2.1.eventually_eq (x z,liftUnit (y z)))
      filter_upwards [hy.continuousAt.eventually (eventually_ne_nhds yz), he, ht] with w hw hp' ht'
      exact (extendedIntegrand_on_powers H gl _ _ _ hw hp').trans
        (ht'.trans (extendedIntegrand_on_powers H gl _ _ _ yz hp).symm)
  · have hu := (liftUnit_continuousAt xz).comp hx.continuousAt
    have he := (hu.prodMk hy.continuousAt).eventually (hf.1.eventually_eq (liftUnit (x z),y z))
    have ht := (hu.prodMk hc.continuousAt).eventually (hl.eventually_eq (liftUnit (x z),c z))
    filter_upwards [hx.continuousAt.eventually (eventually_ne_nhds xz), he, ht] with w hw he' ht'
    simp only [extendedIntegrand, if_neg hw, if_neg xz]
    exact congrArg₂ (· * ·) he' ht'

private theorem locallyConstant_line_integral {P : Type*} [TopologicalSpace P]
    [MeasurableSpace K] (dx : Measure K) [NullSingletonClass dx]
    (H : LineSymbol K n) (hn : (n : K) ≠ 0)
    (hl : IsLocallyConstant (fun w : Kˣ × Kˣ => (H.pairing w.1 w.2 : ℂ)))
    {f : Charts K} (gl : Glues (fun a b => H.pairing a b) f) (hf : finiteTest f)
    (y : P × K → K) (c : P → Kˣ) (hy : Continuous y) (hc : Continuous c)
    (haxis : ∀ p, y (p,0) ≠ 0 → y (p,0) * (c p).val ∈ range (fun u : Kˣ => u.val^n)) :
    IsLocallyConstant (fun p => ∫ x : K, if hx : x ≠ 0 then
      f.1 (Units.mk0 x hx) (y (p,x)) * (H.pairing (Units.mk0 x hx) (c p) : ℂ) else 0 ∂dx) := by
  let G (w : P × K) := extendedIntegrand H f w.2 (y w) (c w.1)
  have hg : IsLocallyConstant G := locallyConstant_extendedIntegrand H hn hl gl hf continuous_snd hy
    (hc.comp continuous_fst) (by rintro ⟨p,x⟩ hx; change x = 0 at hx; subst x; exact haxis p)
  obtain ⟨C, hC, _, hs⟩ := hf.2.2
  have hout (p : P) (x : K) (hx : x ∉ Prod.fst '' C) : G (p,x) = 0 := by
    have ho : (x,y (p,x)) ∉ C := fun h => hx ⟨_,h,rfl⟩
    exact extendedIntegrand_outside H _ (hs _ ho).1 (hs _ ho).2
  have h := (locallyConstant_slices hg (hC.image continuous_fst) hout).comp (fun g => ∫ x, g x ∂dx)
  convert h using 1
  funext p
  apply integral_congr_ae
  filter_upwards [dx.ae_ne 0] with x hx
  simp [G, extendedIntegrand, liftUnit, hx]

private def swapCharts (f : Charts K) : Charts K := (fun x y => f.2 y x, fun x y => f.1 y x)

omit [CompleteSpace K] in
private theorem finiteTest_swap {f : Charts K} (hf : finiteTest f) : finiteTest (swapCharts f) := by
  obtain ⟨h₁, h₂, C, hC, h0, hs⟩ := hf
  refine ⟨h₂.comp_continuous continuous_swap, h₁.comp_continuous continuous_swap,
    Prod.swap '' C, hC.image continuous_swap, ?_, ?_⟩
  · rintro ⟨⟨x,y⟩, h, he⟩
    exact h0 (by simpa using (Prod.swap_injective (show (x,y).swap = (0 : K × K).swap from he)) ▸ h)
  · rintro ⟨x,y⟩ hp
    have hz := hs (y,x) (fun h => hp ⟨_,h,rfl⟩)
    exact ⟨hz.2, hz.1⟩

omit [CompleteSpace K] in
private theorem glues_swap (H : LineSymbol K n) {f : Charts K} (hf : Glues (fun a b => H.pairing a b) f) :
    Glues (fun a b => H.pairing a b) (swapCharts f) := by
  intro x y
  change f.2 y x = _ * f.1 y x
  rw [hf, ← mul_assoc, ← Units.val_mul, H.skew x y, inv_mul_cancel, Units.val_one, one_mul]

omit [CompleteSpace K] in
private theorem locallyConstant_norm_units [IsUltrametricDist K] :
    IsLocallyConstant (fun u : Kˣ => ‖u.val‖) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro u
  have hn : 0 < ‖u.val‖ := norm_pos_iff.mpr u.ne_zero
  filter_upwards [Units.continuous_val.continuousAt.eventually (Metric.ball_mem_nhds u.val hn)] with v hv
  have h : ‖v.val + -u.val‖ < ‖u.val‖ := by simpa [Metric.mem_ball, dist_eq_norm, sub_eq_add_neg] using hv
  simpa using IsUltrametricDist.norm_eq_of_add_norm_lt_max (x := v.val) (y := -u.val)
    (h.trans_le (by simp))

/-- For finite test sections both normalized Radon charts are jointly locally
constant on the full chart times the line parameter. -/
theorem finiteTest_locallyConstant_radon [MeasurableSpace K] [IsUltrametricDist K]
    (dx : Measure K) [NullSingletonClass dx] (H : LineSymbol K n) (hn : (n : K) ≠ 0)
    (hl : IsLocallyConstant (fun w : Kˣ × Kˣ => (H.pairing w.1 w.2 : ℂ)))
    {f : Charts K} (gl : Glues (fun a b => H.pairing a b) f) (hf : finiteTest f) :
    let R := radon n (fun a b => H.pairing a b) norm dx f
    (IsLocallyConstant fun p : (Kˣ × K) × K => (R p.2).1 p.1.1 p.1.2) ∧
    (IsLocallyConstant fun p : (K × Kˣ) × K => (R p.2).2 p.1.1 p.1.2) := by
  have hn₀ : n ≠ 0 := fun h => hn (by rw [h, Nat.cast_zero])
  constructor
  · let y (w : ((Kˣ × K) × K) × K) := (w.2*w.1.1.2-w.1.2^n)/w.1.1.1.val
    let c (p : (Kˣ × K) × K) := -p.1.1
    have hc : Continuous c := Units.isEmbedding_val₀.continuous_iff.mpr (by
      change Continuous fun p : (Kˣ × K) × K => -p.1.1.val
      fun_prop)
    have hi := locallyConstant_line_integral dx H hn hl gl hf y c (by dsimp [y]; fun_prop (disch := simp)) hc
      (by
        intro p hy
        have ht : p.2 ≠ 0 := by
          intro ht
          exact hy (by simp [y, ht, zero_pow hn₀])
        refine ⟨Units.mk0 _ ht, ?_⟩
        simp [y, c, p.1.1.ne_zero])
    exact hi.comp₂ ((locallyConstant_norm_units.comp_continuous (continuous_fst.comp continuous_fst)).comp
      (fun r : ℝ => (r : ℂ))) (· / ·)
  · let x (w : ((K × Kˣ) × K) × K) := (w.1.1.1*w.2+w.1.2^n)/w.1.1.2.val
    let c (p : (K × Kˣ) × K) := p.1.2
    have hc : Continuous c := continuous_snd.comp continuous_fst
    have hi := locallyConstant_line_integral dx H hn hl (glues_swap H gl) (finiteTest_swap hf)
      x c (by dsimp [x]; fun_prop (disch := simp)) hc (by
        intro p hx
        have ht : p.2 ≠ 0 := by
          intro ht
          exact hx (by simp [x, ht, zero_pow hn₀])
        refine ⟨Units.mk0 _ ht, ?_⟩
        simp [x,c])
    have hsign := hl.comp_continuous (continuous_const (y := (-1 : Kˣ)) |>.prodMk hc)
    have hm := (locallyConstant_norm_units.comp_continuous hc).comp (fun r : ℝ => (r : ℂ))
    have h := (hi.comp₂ hsign (· * ·)).comp₂ hm (· / ·)
    convert h using 1
    funext p
    dsimp only [radon, Function.comp_apply]
    congr 1
    rw [← integral_mul_const]
    apply integral_congr_ae
    filter_upwards [dx.ae_ne 0] with z hz
    simp [swapCharts, x, c, hz]

/-- The finite-place Schwartz–Bruhat bounds over compact parameter sets:
only finitely many slices occur, with common compact support and a common
neighborhood of translation invariance. -/
def SmoothFiniteFamily {P K : Type*} [TopologicalSpace P] [NormedField K] (g : P → K → ℂ) : Prop :=
  IsLocallyConstant (Function.uncurry g) ∧ ∀ T : Set P, IsCompact T →
    (g '' T).Finite ∧
    (∃ C : Set K, IsCompact C ∧ ∀ p ∈ T, ∀ t ∉ C, g p t = 0) ∧
    ∀ᶠ h in 𝓝 (0 : K), ∀ p ∈ T, ∀ t, g p (t+h) = g p t

private theorem smoothFiniteFamily_of_support {P K : Type*} [TopologicalSpace P] [NormedField K]
    {g : P → K → ℂ} (hl : IsLocallyConstant (Function.uncurry g))
    (hs : ∀ T : Set P, IsCompact T → ∃ C : Set K, IsCompact C ∧ ∀ p ∈ T, ∀ t ∉ C, g p t = 0) :
    SmoothFiniteFamily g := by
  refine ⟨hl, fun T hT => ?_⟩
  obtain ⟨C, hC, ho⟩ := hs T hT
  have hi : IsLocallyConstant (fun p : T => g p.val) := by
    apply locallyConstant_slices (G := fun w : T × K => g w.1.val w.2) _ hC (fun p => ho p.val p.property)
    exact hl.comp_continuous ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  letI : CompactSpace T := isCompact_iff_compactSpace.mp hT
  refine ⟨?_, ⟨C,hC,ho⟩, ?_⟩
  · simpa only [← image_eq_range] using hi.range_finite
  let G (w : K × (P × K)) := g w.2.1 (w.2.2 + w.1)
  have hG : IsLocallyConstant G :=
    hl.comp_continuous ((continuous_fst.comp continuous_snd).prodMk
      ((continuous_snd.comp continuous_snd).add continuous_fst))
  let U : Set (K × (P × K)) := {w | G w = g w.2.1 w.2.2}
  have hU : IsOpen U := (hG.prodMk (hl.comp_continuous continuous_snd)) {v | v.1 = v.2}
  obtain ⟨A, B, hA, _, ha, hb, hab⟩ := generalized_tube_lemma (isCompact_singleton (x := (0:K)))
    (hT.prod hC) hU (by rintro ⟨h,p,t⟩ ⟨rfl : h = 0,_⟩; simp [U,G])
  have hev : ∀ᶠ h in 𝓝 (0:K), ∀ p ∈ T, ∀ t ∈ C, g p (t+h) = g p t := by
    filter_upwards [hA.mem_nhds (ha rfl)] with h hh p hp t ht
    exact hab (show (h,(p,t)) ∈ A ×ˢ B from ⟨hh,hb ⟨hp,ht⟩⟩)
  have hneg : Tendsto Neg.neg (𝓝 (0:K)) (𝓝 0) := by simpa using (continuous_neg.tendsto (0:K))
  filter_upwards [hev, hneg.eventually hev] with h h₁ h₂ p hp t
  by_cases ht : t ∈ C
  · exact h₁ p hp t ht
  by_cases hth : t+h ∈ C
  · simpa using (h₂ p hp (t+h) hth).symm
  · rw [ho p hp _ hth, ho p hp _ ht]

theorem finiteTest_smoothFamilies [MeasurableSpace K] [IsUltrametricDist K] [ProperSpace K]
    (dx : Measure K) [NullSingletonClass dx] (H : LineSymbol K n) (hn : (n : K) ≠ 0)
    (hl : IsLocallyConstant (fun w : Kˣ × Kˣ => (H.pairing w.1 w.2 : ℂ)))
    {f : Charts K} (gl : Glues (fun a b => H.pairing a b) f) (hf : finiteTest f) :
    let R := radon n (fun a b => H.pairing a b) norm dx f
    (SmoothFiniteFamily fun (v : Kˣ × K) t => (R t).1 v.1 v.2) ∧
    (SmoothFiniteFamily fun (v : K × Kˣ) t => (R t).2 v.1 v.2) := by
  obtain ⟨hx,hy⟩ := finiteTest_locallyConstant_radon dx H hn hl gl hf
  have hn₀ : n ≠ 0 := fun h => hn (by rw [h,Nat.cast_zero])
  have bound (B : ℝ) (t : K) (ht : t ∉ Metric.closedBall 0 (max B 1)) : B < ‖t‖^n := by
    have hlt : max B 1 < ‖t‖ := by simpa [Metric.mem_closedBall, dist_zero_right] using ht
    exact ((le_max_left _ _).trans_lt hlt).trans_le (le_self_pow₀ ((le_max_right _ _).trans hlt.le) hn₀)
  constructor
  · apply smoothFiniteFamily_of_support hx
    intro T hT
    let e (p : Kˣ × K) := (p.1.val,p.2)
    obtain ⟨B,hB⟩ := finiteTest_radon_vanishes dx hf n (fun a b => H.pairing a b) norm
      (hT.image (show Continuous e from (Units.continuous_val.comp continuous_fst).prodMk continuous_snd))
    exact ⟨_,isCompact_closedBall 0 (max B 1),fun p hp t ht =>
      (hB t (bound B t ht)).1 _ _ ⟨p,hp,rfl⟩⟩
  · apply smoothFiniteFamily_of_support hy
    intro T hT
    let e (p : K × Kˣ) := (p.1,p.2.val)
    obtain ⟨B,hB⟩ := finiteTest_radon_vanishes dx hf n (fun a b => H.pairing a b) norm
      (hT.image (show Continuous e from continuous_fst.prodMk (Units.continuous_val.comp continuous_snd)))
    exact ⟨_,isCompact_closedBall 0 (max B 1),fun p hp t ht =>
      (hB t (bound B t ht)).2 _ _ ⟨p,hp,rfl⟩⟩

namespace Datum
open NumberField IsDedekindDomain
variable {F : Type} [Field F] [NumberField F] [NeZero n] (d : Datum F n)

/-- Lemma 4.2(iii) at every finite place of the number field. -/
theorem smooth_finiteTest_lines (p : HeightOneSpectrum (𝓞 F)) {f : Charts (LocalField F (.inr p))}
    (hf : f ∈ d.testSet (.inr p)) :
    let v : Place F := .inr p
    let R := radon n (d.symbol v) (modulus F v) (selfDual F d.character v) f
    (SmoothFiniteFamily fun (q : (LocalField F v)ˣ × LocalField F v) t => (R t).1 q.1 q.2) ∧
    (SmoothFiniteFamily fun (q : LocalField F v × (LocalField F v)ˣ) t => (R t).2 q.1 q.2) := by
  let v : Place F := .inr p
  let dx := selfDual F d.character v
  letI : NontriviallyNormedField (p.adicCompletion F) := FinitePlace.nontriviallyNormedCompletion p
  letI : ProperSpace (p.adicCompletion F) := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace _
  letI : CharZero (p.adicCompletion F) := charZero_of_injective_ringHom (algebraMap F (p.adicCompletion F)).injective
  letI : MeasurableSpace (p.adicCompletion F) := borel _
  letI : LocallyCompactSpace (LocalField F v) := inferInstanceAs (LocallyCompactSpace (p.adicCompletion F))
  letI : dx.IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  letI : (𝓝[≠] (0 : LocalField F v)).NeBot := NormedField.nhdsNE_neBot (0 : p.adicCompletion F)
  letI : NullSingletonClass dx := Measure.IsAddHaarMeasure.nullSingletonClass dx
  let μ : Measure (p.adicCompletion F) := dx
  letI : NullSingletonClass μ := (inferInstance : NullSingletonClass dx)
  let H := d.lineSymbol v (d.finite_steinberg p)
  have ht : Glues (d.symbol v) f ∧ finiteTest f := hf
  exact finiteTest_smoothFamilies (K := p.adicCompletion F) μ H (Nat.cast_ne_zero.mpr (NeZero.ne n))
    ((d.locallyConstant_unitPairing v).comp Units.val) ht.1 ht.2

end Datum
end MetaplecticPoisson
