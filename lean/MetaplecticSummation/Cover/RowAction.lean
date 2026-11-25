import MetaplecticSummation.Cover.Operators
import MetaplecticSummation.Cover.RowPairing

/-! Matrix and root-of-unity data for the local action on genuine sections. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField
open scoped Matrix MatrixGroups
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n) (v : Place F)
local notation "K" => LocalField F v
local notation "M" => SL(2,K)
local notation "R" => Fin 2 → K

private noncomputable local instance : NontriviallyNormedField K := {localNormedField F v with
  non_trivial := by cases v with
    | inl w => exact (archNontriviallyNormedCompletion w).non_trivial
    | inr p => exact (FinitePlace.nontriviallyNormedCompletion p).non_trivial }

/-- Evaluate in the X chart when possible, using the Y chart on the vertical axis. -/
def rowEval (Φ : d.schwartz v) (p : R) : ℂ :=
  if p 0 = 0 then yChart Φ.val (p 0,p 1) else xChart Φ.val (p 0,p 1)

private def rowEvalY (Φ : d.schwartz v) (p : R) : ℂ :=
  if p 1 = 0 then xChart Φ.val (p 0,p 1) else yChart Φ.val (p 0,p 1)

private def transition (p : R) := d.family v (liftUnit (p 0)) (liftUnit (p 1))
private def pairX (p q : R) := d.family v (liftUnit (p 0)) (-liftUnit (q 0))
private def pairY (p q : R) := d.family v (-liftUnit (p 1)) (liftUnit (q 1))

private theorem transition_pair (p q : R) (h : RowPairing.det p q = 1) :
    d.transition v p * d.pairX v p q = d.transition v q * d.pairY v p q := by
  apply d.injective
  simp only [map_mul]
  let H := d.lineSymbol v (by cases v with
    | inl w => exact d.arch_steinberg w
    | inr t => exact d.finite_steinberg t)
  exact H.row_pairing p q h

private theorem rowEval_transition (Φ : d.schwartz v) (p : R) :
    d.rowEval v Φ p = (d.embedding (d.transition v p) : ℂˣ).val * d.rowEvalY v Φ p := by
  change _ = (d.unitPairing v (liftUnit (p 0)) (liftUnit (p 1))).val * _
  by_cases hx : p 0 = 0 <;> by_cases hy : p 1 = 0
  all_goals try simp [rowEval,rowEvalY,hx,hy,xChart,yChart,liftUnit,map_one]
  exact d.schwartz_glues v Φ (Units.mk0 _ hx) (Units.mk0 _ hy)

private theorem rowEval_smul (c : ℂ) (Φ : d.schwartz v) (p : R) :
    d.rowEval v (c • Φ) p = c * d.rowEval v Φ p := by
  by_cases hx : p 0 = 0 <;> by_cases hy : p 1 = 0 <;>
    simp [rowEval,xChart,yChart,hx,hy,smul_eq_mul]

private theorem ext_rowEval {Φ Ψ : d.schwartz v} (h : ∀ p, p ≠ 0 → d.rowEval v Φ p = d.rowEval v Ψ p) :
    Φ = Ψ := by
  have hx (x : Kˣ) (y : K) := h ![x.val,y] (fun e => x.ne_zero (congrFun e 0))
  apply Subtype.ext
  apply Prod.ext
  · funext x y
    simpa [rowEval,xChart,x.ne_zero] using hx x y
  · funext x y
    have he := h ![x,y.val] (fun e => y.ne_zero (congrFun e 1))
    rw [d.rowEval_transition,d.rowEval_transition] at he
    simpa [rowEvalY,yChart,y.ne_zero] using he

/-- The multiplier at a row compares evaluations before and after its matrix action.
Its ratio at a determinant-one pair is fixed by the X-chart pairing. -/
def HasRowAction (g : d.Operators v) (m : M) : Prop :=
  ∃ c : R → Mu F n,
    (∀ Φ p, d.rowEval v (g Φ) p = (d.embedding (c p)).val * d.rowEval v Φ (p ᵥ* m.val)) ∧
    ∀ p q, RowPairing.det p q = 1 →
      c p * d.pairX v p q = c q * d.pairX v (p ᵥ* m.val) (q ᵥ* m.val)

/-- Every lift with identity matrix acts by a single global root of unity. -/
theorem isCentralScalar_of_rowAction_one {g : d.Operators v} (h : d.HasRowAction v g 1) :
    d.IsCentralScalar v g := by
  obtain ⟨c,ev,ratio⟩ := h
  have constancy (p q : R) (he : RowPairing.det p q = 1) : c p = c q := by
    have hr := ratio p q he
    simpa only [Matrix.SpecialLinearGroup.coe_one,Matrix.vecMul_one,mul_left_inj] using hr
  refine ⟨c ![1,0],fun Φ => d.ext_rowEval v (fun p hp => ?_)⟩
  rw [ev,d.rowEval_smul,RowPairing.eq_of_det_one constancy hp]
  simp

protected theorem HasRowAction.mul {g h : d.Operators v} {A B : M}
    (ha : d.HasRowAction v g A) (hb : d.HasRowAction v h B) : d.HasRowAction v (g*h) (A*B) := by
  obtain ⟨a,ea,ra⟩ := ha
  obtain ⟨b,eb,rb⟩ := hb
  refine ⟨fun p => a p * b (p ᵥ* A.val),fun Φ p => ?_,fun p q hpq => ?_⟩
  · change d.rowEval v (g (h Φ)) p = _
    rw [ea,eb,map_mul,Units.val_mul,mul_assoc,Matrix.vecMul_vecMul]
    rfl
  · have hr := rb (p ᵥ* A.val) (q ᵥ* A.val) ((RowPairing.det_vecMul _ _ _).trans hpq)
    rw [Matrix.vecMul_vecMul,Matrix.vecMul_vecMul] at hr
    calc
      _ = b (p ᵥ* A.val) * (a p * d.pairX v p q) := by dsimp only; ac_rfl
      _ = a q * (b (p ᵥ* A.val) * d.pairX v (p ᵥ* A.val) (q ᵥ* A.val)) := by rw [ra p q hpq]; ac_rfl
      _ = _ := by rw [hr,mul_assoc]; rfl

protected theorem HasRowAction.inv {g : d.Operators v} {A : M} (ha : d.HasRowAction v g A) :
    d.HasRowAction v g⁻¹ A⁻¹ := by
  obtain ⟨a,ea,ra⟩ := ha
  let back := fun p : R => p ᵥ* A⁻¹.val
  have cancel (p : R) : back p ᵥ* A.val = p := by
    change (p ᵥ* (A⁻¹).val) ᵥ* A.val = p
    rw [Matrix.vecMul_vecMul,← Matrix.SpecialLinearGroup.coe_mul,inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one,Matrix.vecMul_one]
  refine ⟨fun p => (a (back p))⁻¹,fun Φ p => ?_,fun p q hpq => ?_⟩
  · have h := ea (g⁻¹ Φ) (back p)
    change d.rowEval v (g (g.symm Φ)) _ = _ at h
    rw [LinearEquiv.apply_symm_apply,cancel] at h
    change _ = (d.embedding ((a (back p))⁻¹)).val * d.rowEval v Φ (back p)
    rw [h,map_inv,← mul_assoc,← Units.val_mul,inv_mul_cancel,Units.val_one,one_mul]
  · have hr := ra (back p) (back q) ((RowPairing.det_vecMul _ _ A⁻¹).trans hpq)
    rw [cancel,cancel] at hr
    change (a (back p))⁻¹ * d.pairX v p q = (a (back q))⁻¹ * d.pairX v (back p) (back q)
    calc
      _ = (a (back p) * a (back q))⁻¹ * (a (back q) * d.pairX v p q) := by simp [mul_assoc,mul_left_comm,mul_comm]
      _ = _ := by rw [← hr]; simp [mul_assoc,mul_left_comm,mul_comm]

theorem rowAction_of_scalar {g : d.Operators v} (hg : d.IsCentralScalar v g) :
    d.HasRowAction v g 1 := by
  obtain ⟨c,hc⟩ := hg
  exact ⟨fun _ => c,fun Φ p => by simp [hc,d.rowEval_smul],fun p q _ => by simp⟩

def upperMatrix (u : K) : M := ⟨!![1,u;0,1],by simp [Matrix.det_fin_two]⟩
def lowerMatrix (u : K) : M := ⟨!![1,0;u,1],by simp [Matrix.det_fin_two]⟩

theorem upper_row (p : R) (u : K) :
    p ᵥ* (upperMatrix v u).val = ![p 0,p 1+u*p 0] := by
  ext i
  fin_cases i <;> simp [upperMatrix,Matrix.vecHead,Matrix.vecTail,mul_comm,add_comm]
  abel

theorem lower_row (p : R) (u : K) :
    p ᵥ* (lowerMatrix v u).val = ![p 0+u*p 1,p 1] := by
  ext i
  fin_cases i <;> simp [lowerMatrix,Matrix.vecHead,Matrix.vecTail,mul_comm,add_comm]
  abel

theorem rowAction_of_upper {g : d.Operators v} {u : K} (hg : d.IsUpper v u g) :
    d.HasRowAction v g (upperMatrix v u) := by
  refine ⟨fun _ => 1,fun Φ p => ?_,fun p q _ => by simp [pairX,upper_row]⟩
  rw [upper_row]
  by_cases hx : p 0 = 0
  · by_cases hy : p 1 = 0 <;> simp [rowEval,hx,hy,yChart,(hg Φ).2]
  · simp [rowEval,xChart,hx,(hg Φ).1]

theorem rowAction_of_lower {g : d.Operators v} {u : K} (hg : d.IsLower v u g) :
    d.HasRowAction v g (lowerMatrix v u) := by
  let shift := fun p : R => p ᵥ* (lowerMatrix v u).val
  have ev (Φ : d.schwartz v) (p : R) : d.rowEvalY v (g Φ) p = d.rowEvalY v Φ (shift p) := by
    dsimp only [shift]
    rw [lower_row]
    by_cases hy : p 1 = 0
    · by_cases hx : p 0 = 0 <;> simp [rowEvalY,hy,hx,xChart,(hg Φ).2]
    · simp [rowEvalY,hy,yChart,(hg Φ).1]
  refine ⟨fun p => d.transition v p / d.transition v (shift p),fun Φ p => ?_,fun p q hpq => ?_⟩
  · change _ = _ * d.rowEval v Φ (shift p)
    rw [d.rowEval_transition,ev,d.rowEval_transition,map_div,Units.val_div_eq_div_val,← mul_assoc,
      div_mul_cancel₀ _ (d.embedding _).ne_zero]
  · have same : d.pairY v (shift p) (shift q) = d.pairY v p q := by simp [pairY,shift,lower_row]
    have h := d.transition_pair v (shift p) (shift q) ((RowPairing.det_vecMul _ _ _).trans hpq)
    rw [same] at h
    change _ = _ * d.pairX v (shift p) (shift q)
    calc
      _ = (d.transition v (shift p))⁻¹ * (d.transition v p * d.pairX v p q) := by simp [div_eq_mul_inv,mul_assoc,mul_comm]
      _ = (d.transition v q / d.transition v (shift q)) * ((d.transition v (shift p))⁻¹ *
            (d.transition v (shift q) * d.pairY v p q)) := by rw [d.transition_pair v p q hpq]; simp [div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm]
      _ = _ := by rw [← h]; simp [div_eq_mul_inv,mul_assoc,mul_comm]

/-- Every word in the local cover generators has an underlying matrix and compatible
row multipliers. This construction uses only the chart formulas of the generators. -/
theorem exists_rowAction (g : d.cover v) : ∃ m, d.HasRowAction v g.val m := by
  obtain ⟨g,hg⟩ := g
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    rcases hg with h | ⟨u,h⟩ | ⟨u,h⟩
    · exact ⟨1,d.rowAction_of_scalar v h⟩
    · exact ⟨_,d.rowAction_of_upper v h⟩
    · exact ⟨_,d.rowAction_of_lower v h⟩
  | one => exact ⟨1,d.rowAction_of_scalar v ⟨1,fun Φ => by simp⟩⟩
  | mul a b _ _ ia ib =>
    obtain ⟨A,ha⟩ := ia
    obtain ⟨B,hb⟩ := ib
    exact ⟨A*B,HasRowAction.mul d v ha hb⟩
  | inv a _ ia =>
    obtain ⟨A,ha⟩ := ia
    exact ⟨A⁻¹,HasRowAction.inv d v ha⟩

end MetaplecticPoisson.Datum
