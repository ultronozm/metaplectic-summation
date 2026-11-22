import MetaplecticSummation.Jacquet.LineWeights

/-! The general line summation formula and uniqueness of its main term (§10). -/

noncomputable section
namespace MetaplecticPoisson.Datum
open MeasureTheory Filter NumberField Set
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

private def testLiftLinear (v : Place F) {β : LocalField F v → ℂ} (hβ : d.IsJacquetLiftAuxiliary v β) :
    testWeights v →ₗ[ℂ] d.schwartz v where
  toFun W := ⟨d.jacquetLift v W.val β,Submodule.subset_span (Or.inl (hβ.2 _ W.property))⟩
  map_add' W V := by
    apply Subtype.ext
    apply Prod.ext <;> funext x y
    · simp [jacquetLift,jacquetLiftX,mul_add,add_mul]
    · by_cases hx : x = 0 <;> simp [jacquetLift,jacquetLiftX,hx,mul_add,add_mul]
  map_smul' a W := by
    apply Subtype.ext
    apply Prod.ext <;> funext x y
    · simp [jacquetLift,jacquetLiftX]; ring
    · by_cases hx : x = 0
      · simp [jacquetLift,jacquetLiftX,hx]
      · simp [jacquetLift,jacquetLiftX,hx]; ring

private def jacquetLinear (v : Place F) : d.schwartz v →ₗ[ℂ] Weight v where
  toFun := d.jacquet v
  map_add' Φ Ψ := by
    have h := d.jacquet_sub v (Φ+Ψ) Ψ
    rw [add_sub_cancel_right] at h
    exact sub_eq_iff_eq_add.mp h.symm
  map_smul' := d.jacquet_smul v

private def localWeightLinear (v : Place F) (b : Bool) : testWeights v →ₗ[ℂ] Weight v :=
  if b then
    (d.jacquetLinear v).comp ((d.fourier v).comp
      (d.testLiftLinear v (d.exists_jacquetLift_auxiliary v).choose_spec))
  else (testWeights v).subtype

private theorem localWeightLinear_apply (v : Place F) (b : Bool) (W : testWeights v) :
    d.localWeightLinear v b W = if b then d.dualWeight v W.val else W.val := by
  cases b with
  | false => rfl
  | true => exact d.jacquetLift_dual v W.property (d.exists_jacquetLift_auxiliary v).choose_spec

/-- At each rational argument the adelic product is multilinear in the tests. -/
private theorem globalWeight_multilinear {S : Finset (Place F)} (b : Bool) (c : Fˣ) :
    ∃ L : MultilinearMap ℂ (fun v : S => testWeights v.val) ℂ,
      ∀ W, L W = d.globalWeight (fun v => (W v).val) b c := by
  let J (v : Place F) := d.jacquet v (if b then d.fourier v (d.basic v) else d.basic v) (atPlace v c)
  let out (v : Place F) := if v ∈ S then 1 else J v
  let eval (v : S) := (LinearMap.proj (R := ℂ) (φ := fun _ : (LocalField F v.val)ˣ => ℂ) (atPlace v.val c)).comp
    (d.localWeightLinear v.val b)
  let L := (MultilinearMap.mkPiAlgebra ℂ S ℂ).compLinearMap eval
  refine ⟨(∏ᶠ v, out v) • L,fun W => ?_⟩
  let ins (v : Place F) := if hv : v ∈ S then eval ⟨v,hv⟩ (W ⟨v,hv⟩) else 1
  have hI : Function.mulSupport ins ⊆ (S : Set (Place F)) := fun v hv => by_contra fun h => hv (dif_neg h)
  have hJ : ∀ᶠ v in cofinite, d.jacquet v (d.basic v) (atPlace v c) = 1 := by
    apply eventually_place_of_finite
    filter_upwards [eventually_tame (F := F) (n := n),eventually_trivial_on_integers d.character,
      eventually_diagonal_norm_one c.ne_zero,d.eventually_selfDual_volume_one] with p ht hψ hc hm
    have h := d.jacquet_basic_unit p ht hψ (atPlace (.inr p) c) hc
    simpa only [hm,Complex.ofReal_one] using h
  have hO : Function.HasFiniteMulSupport out := eventually_cofinite.mp (by
    filter_upwards [hJ,d.eventually_fourier_basic] with v h hf
    simp [out,J,hf,h])
  have he : d.globalWeight (fun v => (W v).val) b c = (∏ᶠ v, out v) * ∏ᶠ v, ins v := by
    rw [← finprod_mul_distrib hO (S.finite_toSet.subset hI)]
    unfold globalWeight
    apply finprod_congr
    intro v
    by_cases hv : v ∈ S <;> simp [out,ins,J,eval,hv,d.localWeightLinear_apply]
  rw [he,finprod_eq_prod_of_mulSupport_subset _ hI,← Finset.prod_attach S]
  change _ * (∏ v : S, eval v (W v)) = _
  congr 1
  apply Finset.prod_congr rfl
  intro v _
  simp only [ins,dif_pos v.property]

/-- Unfolding gives an absolutely convergent sum of multilinear forms. -/
private def sumWeightForm (S : Finset (Place F)) (b : Bool) :
    MultilinearMap ℂ (fun v : S => testWeights v.val) ℂ := by
  let L (c : Fˣ) := (d.globalWeight_multilinear (S := S) b c).choose
  have eqn (W) (c : Fˣ) : L c W = d.globalWeight (fun v => (W v).val) b c :=
    (d.globalWeight_multilinear b c).choose_spec W
  have hs (W : (v : S) → testWeights v.val) : Summable (fun c => L c W) := by
    obtain ⟨_,_,_,_,h⟩ := d.lineWeights_unfold (fun v => (W v).val) (fun v => (W v).property)
    exact ((h b).1.of_norm).congr (fun c => (eqn W c).symm)
  exact {
    toFun := fun W => ∑' c, L c W
    map_update_add' := fun W v x y => by
      simp_rw [MultilinearMap.map_update_add]
      exact (hs _).tsum_add (hs _)
    map_update_smul' := fun W v a x => by simp [MultilinearMap.map_update_smul,tsum_mul_left] }

private theorem sumWeightForm_apply {S : Finset (Place F)} (b : Bool) (W : (v : S) → testWeights v.val) :
    d.sumWeightForm S b W = ∑' c, d.globalWeight (fun v => (W v).val) b c :=
  tsum_congr fun c => (d.globalWeight_multilinear b c).choose_spec W

/-- The difference of the two adelic sums factors through the local moment maps. -/
theorem lineBoundary_momentForm (S : Finset (Place F)) :
    ∃ M : MultilinearMap ℂ (fun v : S => PowerClass n v.val → ℂ) ℂ, ∀ W : Weights S, Admissible W →
      (∑' c, d.globalWeight W false c) - (∑' c, d.globalWeight W true c) =
        M (fun v => d.classMoment v.val (W v)) := by
  let D := d.sumWeightForm S false - d.sumWeightForm S true
  have eval (W) : D W = (∑' c, d.globalWeight (fun v => (W v).val) false c) -
      ∑' c, d.globalWeight (fun v => (W v).val) true c := by
    simp only [D,sub_apply,d.sumWeightForm_apply]
  have vanish (W : (v : S) → testWeights v.val) (i : S) (h : d.momentMap i.val (W i) = 0) : D W = 0 := by
    rw [eval,sub_eq_zero]
    exact d.lineSummation_of_zero_moments _ (fun v => (W v).property) i (fun β => congrFun h β)
  choose L hL using fun i : S => (d.momentMap i.val).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (d.momentMap_surjective i.val))
  refine ⟨D.compLinearMap L,fun W hW => ?_⟩
  let X (v : S) : testWeights v.val := ⟨W v,hW v⟩
  let Y (v : S) := L v (d.momentMap v.val (X v))
  have same (v : S) : d.momentMap v.val (Y v) = d.momentMap v.val (X v) :=
    LinearMap.congr_fun (hL v) _
  have step (T : Finset S) : D (T.piecewise Y X) = D X := by
    induction T using Finset.induction_on with
    | empty => simp
    | insert i T hi ih =>
      rw [Finset.piecewise_insert, D.map_update, ← ih]
      apply sub_eq_self.mpr
      apply vanish _ i
      rw [Function.update_self,T.piecewise_eq_of_notMem Y X hi,map_sub,same,sub_self]
  change _ = D Y
  rw [← eval X]
  simpa only [Finset.piecewise_univ] using (step Finset.univ).symm

open Classical in
theorem lineSummation (S : Finset (Place F)) (hS : d.GoodOutside S) :
    ∃! ρ, d.LineFormula S ρ := by
  obtain ⟨M,hM⟩ := d.lineBoundary_momentForm S
  letI (v : S) : Fintype (PowerClass n v.val) := @Fintype.ofFinite _ (finite_power_classes v.val)
  let e (v : S) (b : PowerClass n v.val) : PowerClass n v.val → ℂ := Pi.single b 1
  let ρ (β : Classes n S) := M fun v => e v (β v)
  suffices hρ : d.LineFormula S ρ from ⟨ρ,hρ,fun _ h => d.lineFormula_unique h hρ⟩
  intro W hW
  obtain ⟨_,_,_,_,hu⟩ := d.lineWeights_unfold W hW
  refine ⟨d.globalWeight_original_summable hS W hW,(hu true).1,?_⟩
  let I (v : S) := d.classMoment v.val (W v)
  have expand (v : S) : I v = ∑ b, (I v b) • e v b := pi_eq_sum_univ' _
  have sum : M I = ∑ᶠ β, ρ β * d.moment W β := by
    rw [show I = (fun v => ∑ b, I v b • e v b) from funext expand]
    rw [M.map_sum, finsum_eq_sum_of_fintype]
    apply Finset.sum_congr rfl
    intro β _
    rw [M.map_smul_univ]
    exact mul_comm _ _
  have h := hM W hW
  change _ = M I at h
  rw [sum] at h
  exact (sub_eq_iff_eq_add.mp h).trans (add_comm ..)

theorem line_degree_one (a : Datum F 1) (S : Finset (Place F)) (hS : a.GoodOutside S) :
    a.LineFormula S (fun _ => 0) := by
  classical
  intro W hW
  have dual (c : Fˣ) : a.globalWeight W true c = a.globalWeight W false c⁻¹ := by
    unfold globalWeight
    apply finprod_congr
    intro v
    by_cases hv : v ∈ S
    · simpa only [dif_pos hv,Bool.false_eq_true,ite_true,ite_false,atPlace,map_inv] using
        a.dualWeight_degree_one v (hW ⟨v,hv⟩) (atPlace v c)
    · cases v with
      | inl w => exact (hv (hS.2.1 w)).elim
      | inr p =>
        simpa only [dif_neg hv,Bool.false_eq_true,ite_true,ite_false,atPlace,map_inv] using
          a.jacquet_basic_dual_degree_one p (atPlace (.inr p) c)
  have hs := a.globalWeight_original_summable hS W hW
  refine ⟨hs,?_,?_⟩
  · exact (hs.comp_injective (Equiv.inv Fˣ).injective).congr (fun c => congrArg norm (dual c).symm)
  · simp only [zero_mul,finsum_zero,add_zero,dual]
    exact ((Equiv.inv Fˣ).tsum_eq (a.globalWeight W false)).symm

end MetaplecticPoisson.Datum
