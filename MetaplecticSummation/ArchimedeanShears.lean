import MetaplecticSummation.RapidCharts
import MetaplecticSummation.SmoothFiniteLines

/-! Preservation of rapid test sections by the archimedean shear operators. -/

noncomputable section
namespace MetaplecticPoisson
open NumberField Filter Set
open scoped Topology ContDiff
open Classical
variable {K L : Type} [NontriviallyNormedField K] [CompleteSpace K] [NormedField L] [NormedAlgebra ℝ L]
  {n : ℕ}

omit [CompleteSpace K] in
private theorem archTest_swap (e : K ≃+* L) {f : Charts K} (hf : archTest e f) :
    archTest e (swapCharts f) :=
  ⟨rapidChart_comp_equiv hf.2 (ContinuousLinearEquiv.prodComm ℝ L L),
    rapidChart_comp_equiv hf.1 (ContinuousLinearEquiv.prodComm ℝ L L)⟩

omit [CompleteSpace K] in
/-- On the overlap the symbol introduced by an upper shear cancels wherever
the ratio of the new and old second coordinates is an n-th power. -/
private theorem upperShear_on_powers (H : LineSymbol K n) {f : Charts K}
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

private theorem archTest_upperShear (e : K ≃+* L) (hc : Continuous e.symm)
    (H : LineSymbol K n) (hn : (n : K) ≠ 0)
    (hl : IsLocallyConstant fun z : Kˣ × Kˣ => (H.pairing z.1 z.2 : ℂ))
    (hu : ∀ a b, ‖(H.pairing a b : ℂ)‖ = 1)
    {f : Charts K} (gl : Glues (fun a b => H.pairing a b) f) (hf : archTest e f) (u : K) :
    archTest e (upperShear (fun a b => H.pairing a b) u f) := by
  let P := L × L
  let x (z : P) := e.symm z.1
  let y (z : P) := e.symm z.2
  let w (z : P) := y z + u*x z
  let A := (ContinuousLinearEquiv.refl ℝ L).skewProd (ContinuousLinearEquiv.refl ℝ L)
    (e u • ContinuousLinearMap.id ℝ L)
  have xA (z : P) : x (A z) = x z := rfl
  have yA (z : P) : y (A z) = w z := by
    change e.symm (z.2+e u*z.1) = _
    simp [w,x,y]
  let X (z : P) := xChart f (x z,y z)
  let Y (z : P) := yChart f (x z,y z)
  let U : Set P := {z | z.1 ≠ 0}
  let V : Set P := {z | z.2 ≠ 0}
  let g := upperShear (fun a b => H.pairing a b) u f
  have hX : rapidChart (A ⁻¹' U) (fun z => X (A z)) := rapidChart_comp_equiv hf.1 A
  have hY : rapidChart (A ⁻¹' V) (fun z => Y (A z)) := rapidChart_comp_equiv hf.2 A
  have cx : Continuous x := hc.comp continuous_fst
  have cy : Continuous y := hc.comp continuous_snd
  have cw : Continuous w := cy.add (continuous_const.mul cx)
  constructor
  · change rapidChart U (fun z => xChart g (x z,y z))
    have he : (fun z => xChart g (x z,y z)) = fun z => X (A z) := by
      funext z
      by_cases hx : x z ≠ 0 <;> simp [X,xChart,xA,yA,g,upperShear,w,hx]
    rw [he]
    exact hX
  · change rapidChart V (fun z => yChart g (x z,y z))
    apply rapidChart_of_local_branches
      ((isOpen_ne_fun continuous_fst continuous_const).preimage A.continuous)
      ((isOpen_ne_fun continuous_snd continuous_const).preimage A.continuous) hX hY
    intro z hz
    have hy : y z ≠ 0 := (map_ne_zero_iff e.symm e.symm.injective).mpr hz
    by_cases hx : x z = 0
    · right
      have hw : w z = y z := by simp [w,hx]
      have h₁ : A z ∈ V := by
        change (A z).2 ≠ 0
        exact fun h => hy (hw ▸ yA z ▸ (show y (A z) = 0 by simp [y,h]))
      refine ⟨h₁,1,norm_one,?_⟩
      have hr : w z / y z ∈ range (fun a : Kˣ => a.val^n) := ⟨1,by simp [hw,hy]⟩
      have hp := (cw.continuousAt.div cy.continuousAt hy).eventually ((isOpen_nonzero_powers n hn).mem_nhds hr)
      filter_upwards [cy.continuousAt.eventually (eventually_ne_nhds hy),
        cw.continuousAt.eventually (eventually_ne_nhds (hw ▸ hy)),hp] with q hyq hwq hpq
      change y q ≠ 0 at hyq
      change w q ≠ 0 at hwq
      change yChart g (x q,y q) = (1 : ℂ) * yChart f (x (A q),y (A q))
      simp only [yChart,xA,yA,dif_pos hyq,dif_pos hwq,one_mul]
      exact upperShear_on_powers H gl u (x q) (Units.mk0 _ hyq) hwq hpq
    · left
      have h₁ : A z ∈ U := by
        change z.1 ≠ 0
        exact fun h => hx (by simp [x,h])
      let c := (H.pairing (liftUnit (x z)) (liftUnit (y z)) : ℂ)⁻¹
      refine ⟨h₁,c,by simp [c,hu],?_⟩
      have he := ((liftUnit_continuousAt hx).comp cx.continuousAt).prodMk
        ((liftUnit_continuousAt hy).comp cy.continuousAt)
      have hv := he.eventually (hl.eventually_eq (liftUnit (x z),liftUnit (y z)))
      filter_upwards [cx.continuousAt.eventually (eventually_ne_nhds hx),
        cy.continuousAt.eventually (eventually_ne_nhds hy),hv] with q hxq hyq hq
      change x q ≠ 0 at hxq
      change y q ≠ 0 at hyq
      change yChart g (x q,y q) = c * X (A q)
      simp only [g,X,yChart,xChart,xA,yA,upperShear,dif_pos hyq,dif_pos hxq,w,Units.val_mk0]
      change (H.pairing (liftUnit (x q)) (liftUnit (y q)) : ℂ) = _ at hq
      simp only [liftUnit,dif_pos hxq,dif_pos hyq] at hq
      rw [div_eq_mul_inv,hq,mul_comm]
      rfl

namespace Datum
variable {F : Type} [Field F] [NumberField F] [NeZero n] (d : Datum F n)

/-- At every archimedean place both shear formulas preserve rapid test sections. -/
theorem arch_shear_test (w : InfinitePlace F) {f : Charts (LocalField F (.inl w))}
    (hf : f ∈ d.testSet (.inl w)) (u : LocalField F (.inl w)) :
    let v : Place F := .inl w
    upperShear (d.symbol v) u f ∈ d.testSet v ∧ lowerShear (d.symbol v) u f ∈ d.testSet v := by
  let v : Place F := .inl w
  letI : CompleteSpace (LocalField F (.inl w)) := inferInstanceAs (CompleteSpace w.Completion)
  letI := archNontriviallyNormedCompletion w
  let H := d.lineSymbol v (d.arch_steinberg w)
  have hn : (n : LocalField F (.inl w)) ≠ 0 := by
    simpa using (diagonal F v).injective.ne (Nat.cast_ne_zero.mpr (NeZero.ne n) : (n : F) ≠ 0)
  have both {M : Type} [NormedField M] [NormedAlgebra ℝ M] (e : LocalField F (.inl w) ≃+* M)
      (he : Continuous e.symm) (ht : archTest e f) :
      archTest e (upperShear (d.symbol v) u f) ∧ archTest e (lowerShear (d.symbol v) u f) := by
    have upper {g : Charts (LocalField F (.inl w))} (gl : Glues (d.symbol v) g) (test : archTest e g) :=
      archTest_upperShear (K := LocalField F (.inl w)) e he H hn ((d.locallyConstant_unitPairing v).comp Units.val)
        (d.norm_symbol v) gl test u
    refine ⟨upper hf.1 ht,?_⟩
    rw [show lowerShear (d.symbol v) u f = _ from lowerShear_eq_swap_upperShear H u f]
    exact archTest_swap e (upper (glues_swap H hf.1) (archTest_swap e ht))
  have hg := upperShear_glues (d.symbol v) (fun a b => (d.unitPairing v a b).ne_zero) u f
  have hg' := lowerShear_glues (d.symbol v) u f
  by_cases hw : w.IsReal
  · have ht := hf.2
    simp only [testSet, dif_pos hw] at ht ⊢
    have h := both _ (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.continuous ht
    exact ⟨⟨hg,h.1⟩,⟨hg',h.2⟩⟩
  · have ht := hf.2
    simp only [testSet, dif_neg hw] at ht ⊢
    have h := both _ (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
      (InfinitePlace.not_isReal_iff_isComplex.mp hw)).symm.continuous ht
    exact ⟨⟨hg,h.1⟩,⟨hg',h.2⟩⟩

end Datum
end MetaplecticPoisson
