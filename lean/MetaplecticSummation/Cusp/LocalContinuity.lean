import MetaplecticSummation.Cusp.Localization
import MetaplecticSummation.Schwartz.ChartFamilies

/-! A section of the local cover near the identity with continuous chart evaluations. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField Filter Set
open scoped Topology Matrix MatrixGroups
open Classical

private theorem shear_chart {K : Type} [Field K] (m : SL(2,K)) (h : m.val 1 0 + m.val 1 1 ≠ 0) :
    let z := m.val 1 0 + m.val 1 1
    let x := (m.val 0 0 + m.val 0 1 - 1)/z
    let y := (m.val 1 1 - 1)/z
    !![1,x;0,1] * !![1,0;z,1] * !![1,y;0,1] * !![1,0;-1,1] = m.val := by
  let a := m.val 0 0
  let b := m.val 0 1
  let c := m.val 1 0
  let e := m.val 1 1
  let z := c+e
  let x := (a+b-1)/z
  let y := (e-1)/z
  have det : a*e-b*c=1 := by simpa only [a,b,c,e,Matrix.det_fin_two] using m.property
  have hz : z ≠ 0 := h
  have hx : 1+x*z = a+b := by dsimp only [x]; rw [div_mul_cancel₀ _ hz]; ring
  have hy : z*y+1 = e := by dsimp only [y]; rw [mul_div_cancel₀ _ hz]; ring
  have hb : (a+b)*y+x=b := by
    dsimp only [x,y]
    field_simp [hz]
    dsimp only [z]
    linear_combination det
  change !![1,x;0,1] * !![1,0;z,1] * !![1,y;0,1] * !![1,0;-1,1] = m.val
  have eqn : !![1,x;0,1] * !![1,0;z,1] * !![1,y;0,1] = !![a+b,b;z,e] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_two,hx,hy,hb]
  rw [eqn]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_two,a,b,z,c,e]

variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n) (v : Place F)
local notation "K" => LocalField F v
local notation "M" => SL(2,K)

/-- On the open chart where the bottom-row sum is nonzero, four shear lifts
give a section of the projection. Their parameters are continuous at the identity. -/
theorem hasLocalEvaluationLifts : d.HasLocalEvaluationLifts v := by
  let : NontriviallyNormedField K := { localNormedField F v with
    non_trivial := by
      cases v with
      | inl w => exact (archNontriviallyNormedCompletion w).non_trivial
      | inr p => exact (FinitePlace.nontriviallyNormedCompletion p).non_trivial }
  let : CompleteSpace K := by
    cases v with
    | inl w => exact inferInstanceAs (CompleteSpace w.Completion)
    | inr p => exact inferInstanceAs (CompleteSpace (p.adicCompletion F))
  let H := d.lineSymbol v (by cases v with
    | inl w => exact d.arch_steinberg w
    | inr p => exact d.finite_steinberg p)
  have hn : (n : K) ≠ 0 := by simpa using (diagonal F v).injective.ne (Nat.cast_ne_zero.mpr (NeZero.ne n) : (n : F) ≠ 0)
  choose u hu _ using d.exists_upper v
  choose l hl _ using d.exists_lower v
  let U (a : K) : d.cover v := ⟨u a,Subgroup.subset_closure (Or.inr (Or.inl ⟨a,hu a⟩))⟩
  let L (a : K) : d.cover v := ⟨l a,Subgroup.subset_closure (Or.inr (Or.inr ⟨a,hl a⟩))⟩
  let z := fun m : M => m.val 1 0 + m.val 1 1
  let x := fun m : M => (m.val 0 0 + m.val 0 1 - 1)/z m
  let y := fun m : M => (m.val 1 1 - 1)/z m
  let word := fun m : M => U (x m) * L (z m) * U (y m) * L (-1)
  have proj (m : M) (hm : z m ≠ 0) : d.coverProjection v (word m) = m := by
    apply Subtype.ext
    dsimp only [word]
    simp only [map_mul,Matrix.SpecialLinearGroup.coe_mul]
    have hU (s : K) : (d.coverProjection v (U s)).val = !![1,s;0,1] :=
      (d.kubota_projection v).choose_spec.2.2.1 _ s (hu s)
    have hL (s : K) : (d.coverProjection v (L s)).val = !![1,0;s,1] :=
      (d.kubota_projection v).choose_spec.2.2.2 _ s (hl s)
    rw [hU,hL,hU,hL]
    exact shear_chart m hm
  let lift := fun m : M => if z m ≠ 0 then word m else ((d.kubota_projection v).choose_spec.1 m).choose
  have entry (i j : Fin 2) : ContinuousAt (fun m : M => m.val i j) 1 :=
    ((continuous_apply j).comp ((continuous_apply i).comp (continuous_subtype_val : Continuous (fun m : M => m.val)))).continuousAt
  have cz : ContinuousAt z 1 := (entry 1 0).add (entry 1 1)
  have hz : z 1 ≠ 0 := by simp [z]
  have cx : ContinuousAt x 1 := (((entry 0 0).add (entry 0 1)).sub continuousAt_const).div cz hz
  have cy : ContinuousAt y 1 := ((entry 1 1).sub continuousAt_const).div cz hz
  let R := fun f : M → d.schwartz v => ChartFamilyContinuousAt (fun m => (f m).val) 1
  have up {f : M → d.schwartz v} (hf : R f) {t : M → K} (ht : ContinuousAt t 1) :
      R (fun m => (U (t m)).val (f m)) := by
    have he (m : M) := d.eq_upperShear v (d.schwartz_glues v ((u (t m)) (f m))) (t m) ((hu _ _).1) ((hu _ _).2)
    change ChartFamilyContinuousAt (fun m => ((u (t m)) (f m)).val) 1
    simp_rw [he]
    exact hf.upper H hn (d.continuous_symbol v) (fun m => d.schwartz_glues v (f m)) ht
  have low {f : M → d.schwartz v} (hf : R f) {t : M → K} (ht : ContinuousAt t 1) :
      R (fun m => (L (t m)).val (f m)) := by
    have he (m : M) := d.eq_lowerShear v (d.schwartz_glues v ((l (t m)) (f m))) (t m) ((hl _ _).1) ((hl _ _).2)
    change ChartFamilyContinuousAt (fun m => ((l (t m)) (f m)).val) 1
    simp_rw [he]
    exact hf.lower H hn (d.continuous_symbol v) (fun m => d.schwartz_glues v (f m)) ht
  refine ⟨lift,fun m => ?_,fun f p => ?_⟩
  · dsimp only [lift]
    split
    · exact proj m ‹_›
    · exact ((d.kubota_projection v).choose_spec.1 m).choose_spec
  · obtain ⟨cX,cY⟩ := d.continuous_schwartz_charts v f
    have hconst : R (fun _ => f) := ⟨fun _ _ a b => cX.continuousAt.comp (a.prodMk b),
      fun _ _ a b => cY.continuousAt.comp (a.prodMk b)⟩
    have hf : R (fun m => (word m).val f) := up (low (up (low hconst continuousAt_const) cy) cz) cx
    suffices hw : ContinuousAt (fun m => d.localValue p v ((word m).val f)) 1 by
      apply hw.congr_of_eventuallyEq
      filter_upwards [cz.eventually (eventually_ne_nhds hz)] with m hm
      simp [lift,hm]
    unfold localValue
    split
    · unfold xChart
      split
      · exact hf.1 _ _ continuousAt_const continuousAt_const
      · exact continuousAt_const
    · unfold yChart
      split
      · exact hf.2 _ _ continuousAt_const continuousAt_const
      · exact continuousAt_const

end MetaplecticPoisson.Datum
