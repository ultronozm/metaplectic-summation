import MetaplecticSummation.SmoothFiniteLines

/-! Continuity of a family of genuine sections under shears with varying parameter. -/
noncomputable section
namespace MetaplecticPoisson
open Filter Set
open scoped Topology
open Classical
variable {K : Type} [NontriviallyNormedField K] [CompleteSpace K] {n : ℕ}

omit [CompleteSpace K] in
/-- On the overlap the symbol introduced by an upper shear cancels wherever
the ratio of the new and old second coordinates is an n-th power. -/
theorem upperShear_on_powers (H : LineSymbol K n) {f : Charts K}
    (gl : Glues (fun a b => H.pairing a b) f) (u x : K) (y : Kˣ)
    (hw : y.val+u*x ≠ 0) (hp : (y.val+u*x)/y.val ∈ range (fun a : Kˣ => a.val^n)) :
    (upperShear (fun a b => H.pairing a b) u f).2 x y = f.2 x (Units.mk0 _ hw) := by
  by_cases hx : x = 0
  · subst x
    simp [upperShear]
  · let X := Units.mk0 x hx
    let W := Units.mk0 (y.val+u*x) hw
    obtain ⟨a,ha⟩ := hp
    have he : W = y * a^n := Units.ext (by
      simp only [W,Units.val_mk0,Units.val_mul,Units.val_pow_eq_pow_val,ha]
      field_simp)
    have hs : H.pairing X W = H.pairing X y := by rw [he,map_mul,H.pow_right,mul_one]
    have h := gl X W
    change f.1 X (y.val+u*x) = (H.pairing X W : ℂ)*f.2 x W at h
    rw [hs] at h
    simp only [upperShear,dif_pos hx]
    exact (div_eq_iff (H.pairing X y).ne_zero).mpr (h.trans (mul_comm ..))

variable {T : Type*} [TopologicalSpace T]

/-- Both chart evaluations remain continuous when their coordinates vary with the parameter. -/
def ChartFamilyContinuousAt (f : T → Charts K) (t : T) : Prop :=
  (∀ (x : T → Kˣ) (y : T → K), ContinuousAt x t → ContinuousAt y t →
    ContinuousAt (fun s => (f s).1 (x s) (y s)) t) ∧
  (∀ (x : T → K) (y : T → Kˣ), ContinuousAt x t → ContinuousAt y t →
    ContinuousAt (fun s => (f s).2 (x s) (y s)) t)

omit [CompleteSpace K] in
theorem ChartFamilyContinuousAt.swap {f : T → Charts K} {t : T} (hf : ChartFamilyContinuousAt f t) :
    ChartFamilyContinuousAt (fun s => swapCharts (f s)) t :=
  ⟨fun x y hx hy => hf.2 y x hy hx,fun x y hx hy => hf.1 y x hy hx⟩

theorem ChartFamilyContinuousAt.upper {f : T → Charts K} {t : T} (hf : ChartFamilyContinuousAt f t)
    (H : LineSymbol K n) (hn : (n : K) ≠ 0) (hc : Continuous (fun z : Kˣ × Kˣ => (H.pairing z.1 z.2 : ℂ)))
    (gl : ∀ s, Glues (fun a b => H.pairing a b) (f s)) {u : T → K} (hu : ContinuousAt u t) :
    ChartFamilyContinuousAt (fun s => upperShear (fun a b => H.pairing a b) (u s) (f s)) t := by
  refine ⟨fun x y hx hy => hf.1 x _ hx (hy.add (hu.mul (Units.continuous_val.continuousAt.comp hx))),?_⟩
  intro x y hx hy
  let w := fun s => (y s).val + u s*x s
  have cy := Units.continuous_val.continuousAt.comp hy
  have cw : ContinuousAt w t := cy.add (hu.mul hx)
  by_cases h : x t = 0
  · have he : w t = (y t).val := by simp [w,h]
    have hw : w t ≠ 0 := he ▸ (y t).ne_zero
    have hp : w t / (y t).val ∈ range (fun a : Kˣ => a.val^n) := ⟨1,by simp [he]⟩
    have near := (cw.div cy (y t).ne_zero).eventually ((isOpen_nonzero_powers n hn).mem_nhds hp)
    apply (hf.2 x (fun s => liftUnit (w s)) hx ((liftUnit_continuousAt hw).comp cw)).congr_of_eventuallyEq
    filter_upwards [near,cw.eventually (eventually_ne_nhds hw)] with s hs hws
    simpa only [liftUnit,dite_eq_left hws] using upperShear_on_powers H (gl s) (u s) (x s) (y s) hws hs
  · have cx := (liftUnit_continuousAt h).comp hx
    have den := hc.continuousAt.comp (cx.prodMk hy)
    apply ((hf.1 _ w cx cw).div den (H.pairing (liftUnit (x t)) (y t)).ne_zero).congr_of_eventuallyEq
    filter_upwards [hx.eventually (eventually_ne_nhds h)] with s hs
    simp [upperShear,liftUnit,hs,w]

theorem ChartFamilyContinuousAt.lower {f : T → Charts K} {t : T} (hf : ChartFamilyContinuousAt f t)
    (H : LineSymbol K n) (hn : (n : K) ≠ 0) (hc : Continuous (fun z : Kˣ × Kˣ => (H.pairing z.1 z.2 : ℂ)))
    (gl : ∀ s, Glues (fun a b => H.pairing a b) (f s)) {u : T → K} (hu : ContinuousAt u t) :
    ChartFamilyContinuousAt (fun s => lowerShear (fun a b => H.pairing a b) (u s) (f s)) t := by
  simp_rw [lowerShear_eq_swap_upperShear H]
  exact (hf.swap.upper H hn hc (fun s => glues_swap H (gl s)) hu).swap

end MetaplecticPoisson
