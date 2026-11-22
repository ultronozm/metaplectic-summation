import MetaplecticSummation.DiagonalTransform

/-! The diagonal lifts preserve archimedean test sections. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField Set Filter
open scoped Topology
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)
variable (w : InfinitePlace F)
local notation "v" => (Sum.inl w : Place F)
local notation "K" => LocalField F v

private theorem archTest_torusCharts {L : Type} [NormedField L] [NormedAlgebra ℝ L]
    (e : K ≃+* L) (he : Continuous e.symm) (a : Kˣ) {f : Charts K} (hf : archTest e f) :
    archTest e (d.torusCharts v a f) := by
  letI := archNontriviallyNormedCompletion w
  let u := Units.map e.toMonoidHom a
  let D := (ContinuousLinearEquiv.unitsEquivAut L u).restrictScalars ℝ
  let A := D.prodCongr D.symm
  let x (z : L×L) := e.symm z.1
  let y (z : L×L) := e.symm z.2
  have xA (z : L×L) : x (A z) = a.val*x z := by
    change e.symm (z.1*e a.val) = _
    simp [x,mul_comm]
  have yA (z : L×L) : y (A z) = y z/a.val := by
    change e.symm (z.2*e (a⁻¹).val) = _
    simp [y,div_eq_mul_inv]
  let U : Set (L×L) := {z | z.1 ≠ 0}
  let V : Set (L×L) := {z | z.2 ≠ 0}
  have hU : IsOpen U := isOpen_ne_fun continuous_fst continuous_const
  have hV : IsOpen V := isOpen_ne_fun continuous_snd continuous_const
  have hX := rapidChart_comp_equiv hf.1 A
  have hY := rapidChart_comp_equiv hf.2 A
  have hl := (d.locallyConstant_unitPairing v).comp Units.val
  constructor
  · apply rapidChart_of_local_branches (hU.preimage A.continuous) (hU.preimage A.continuous) hX hX
    intro z hz
    have hn : x z ≠ 0 := (map_ne_zero_iff e.symm e.symm.injective).mpr hz
    have hAz : A z ∈ U := fun hz' => (mul_ne_zero a.ne_zero hn) ((xA z).symm.trans (by simp [x,show (A z).1 = 0 from hz']))
    let c := d.symbol v (liftUnit (x z)) a * d.symbol v (-1) a
    refine Or.inl ⟨hAz,c,by simp [c,d.norm_symbol],?_⟩
    have cx : ContinuousAt (fun q : L×L => liftUnit (x q)) z := (liftUnit_continuousAt hn).comp (he.comp continuous_fst).continuousAt
    have hloc := (cx.prodMk (show ContinuousAt (fun _ : L×L => a) z from continuousAt_const)).eventually (hl.eventually_eq (liftUnit (x z),a))
    filter_upwards [hloc,(he.comp continuous_fst).continuousAt.eventually (eventually_ne_nhds hn)] with q hq hne
    change x q ≠ 0 at hne
    change d.symbol v (liftUnit (x q)) a = d.symbol v (liftUnit (x z)) a at hq
    change xChart (d.torusCharts v a f) (x q,y q) = c * xChart f (x (A q),y (A q))
    simp only [xA,yA,xChart,dif_pos hne,dif_pos (mul_ne_zero a.ne_zero hne),torusCharts]
    rw [← show Units.mk0 (a.val*x q) _ = a * Units.mk0 (x q) hne from Units.ext rfl]
    simpa only [c,liftUnit,dif_pos hne] using congrArg (fun k => k * d.symbol v (-1) a *
      f.1 (Units.mk0 (a.val*x q) (mul_ne_zero a.ne_zero hne)) (y q/a.val)) hq
  · apply rapidChart_of_local_branches (hV.preimage A.continuous) (hV.preimage A.continuous) hY hY
    intro z hz
    have hn : y z ≠ 0 := (map_ne_zero_iff e.symm e.symm.injective).mpr hz
    have hAz : A z ∈ V := fun hz' => (div_ne_zero hn a.ne_zero) ((yA z).symm.trans (by simp [y,show (A z).2 = 0 from hz']))
    let c := d.symbol v a (liftUnit (y z))
    refine Or.inl ⟨hAz,c,d.norm_symbol _ _ _,?_⟩
    have cy : ContinuousAt (fun q : L×L => liftUnit (y q)) z := (liftUnit_continuousAt hn).comp (he.comp continuous_snd).continuousAt
    have hloc := ((show ContinuousAt (fun _ : L×L => a) z from continuousAt_const).prodMk cy).eventually (hl.eventually_eq (a,liftUnit (y z)))
    filter_upwards [hloc,(he.comp continuous_snd).continuousAt.eventually (eventually_ne_nhds hn)] with q hq hne
    change y q ≠ 0 at hne
    change d.symbol v a (liftUnit (y q)) = d.symbol v a (liftUnit (y z)) at hq
    change yChart (d.torusCharts v a f) (x q,y q) = c * yChart f (x (A q),y (A q))
    simp only [xA,yA,yChart,dif_pos hne,dif_pos (div_ne_zero hne a.ne_zero),torusCharts]
    rw [← show Units.mk0 (y q/a.val) (div_ne_zero hne a.ne_zero) = Units.mk0 (y q) hne / a from Units.ext (by rw [Units.val_div_eq_div_val]; rfl)]
    simpa only [c,liftUnit,dif_pos hne] using congrArg (fun k => k *
      f.2 (a.val*x q) (Units.mk0 (y q/a.val) (div_ne_zero hne a.ne_zero))) hq

/-- The diagonal translate of any test section is again a test section at
every archimedean place. -/
theorem torusCharts_archTest (a : Kˣ) {f : Charts K} (hf : f ∈ d.testSet v) :
    d.torusCharts v a f ∈ d.testSet v := by
  refine ⟨d.torusCharts_glues v a hf.1,?_⟩
  by_cases hw : w.IsReal
  · simp only [testSet,dif_pos hw] at hf ⊢
    exact d.archTest_torusCharts w _ (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.continuous a hf.2
  · simp only [testSet,dif_neg hw] at hf ⊢
    exact d.archTest_torusCharts w _ (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (InfinitePlace.not_isReal_iff_isComplex.mp hw)).symm.continuous a hf.2

end MetaplecticPoisson.Datum
