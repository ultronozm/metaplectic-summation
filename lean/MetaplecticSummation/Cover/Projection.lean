import MetaplecticSummation.Cover.RowAction
import MetaplecticSummation.Jacquet.TestBump
import MetaplecticSummation.Jacquet.Local
import MetaplecticSummation.RationalOrbits

/-! Faithfulness of the underlying matrix action on Schwartz test sections and the
exact sequence of the local metaplectic cover. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField MeasureTheory Set
open scoped Matrix MatrixGroups
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n) (v : Place F)
local notation "K" => LocalField F v
local notation "M" => SL(2,K)
local notation "R" => Fin 2 → K

/-- A test weight supported away from the second abscissa distinguishes the two
rows. An upper shear moves the ordinate of the first row to a nonzero value of
the auxiliary function in a compact Jacquet lift. -/
theorem exists_rowEval_ne_zero_of_first_ne (p q : R) (hp : p 0 ≠ 0) (hne : p 0 ≠ q 0) :
    ∃ Φ : d.schwartz v, d.rowEval v Φ p ≠ 0 ∧ d.rowEval v Φ q = 0 := by
  let X := Units.mk0 (p 0) hp
  let U := {x : Kˣ | x.val ≠ q 0}
  have hU : IsOpen U := isOpen_ne_fun Units.continuous_val continuous_const
  obtain ⟨b,_,_,_,hb,hs,ht⟩ := exists_test_bump v hU X hne
  let W : Weight v := fun x => (1:ℂ) * (b x : ℂ)
  obtain ⟨β,hβ,hW⟩ := d.exists_jacquetLift_auxiliary v
  obtain ⟨t,htβ⟩ : ∃ t, β t ≠ 0 := by
    by_contra! zero
    simp [zero] at hβ
  let f : d.schwartz v := ⟨d.jacquetLift v W β,Submodule.subset_span (Or.inl (hW W (ht 1)))⟩
  let u := (p 0*t - p 1)/p 0
  obtain ⟨g,hg,_⟩ := d.exists_upper v u
  refine ⟨g f,?_,?_⟩
  · have e : (p 1+u*p 0)/p 0 = t := by dsimp [u]; field_simp; ring
    have hm := Complex.ofReal_ne_zero.mpr (modulus_ne_zero v X)
    simp only [rowEval,ite_eq_right hp,xChart,dite_eq_left hp,(hg f).1]
    change (modulus F v X.val : ℂ)⁻¹ * W X * β ((p 1+u*p 0)/p 0) ≠ 0
    simpa [W,hb,e] using mul_ne_zero (inv_ne_zero hm) htβ
  · by_cases hx : q 0 = 0
    · by_cases hy : q 1 = 0
      · simp [rowEval,hx,hy,yChart]
      · simp only [rowEval,hx,ite_true,yChart,dite_eq_left hy,(hg f).2]
        simp [f,jacquetLift]
    · have hout := hs (Units.mk0 _ hx) (show Units.mk0 _ hx ∉ U by simp [U])
      simp only [rowEval,ite_eq_right hx,xChart,dite_eq_left hx,(hg f).1]
      change (modulus F v (q 0) : ℂ)⁻¹ * W (Units.mk0 _ hx) * _ = 0
      simp [W,hout]

private theorem first_eq_of_rowEval {p q : R}
    (h : ∀ Φ, d.rowEval v Φ p = 0 ↔ d.rowEval v Φ q = 0) : p 0 = q 0 := by
  by_contra hn
  by_cases hp : p 0 = 0
  · obtain ⟨Φ,ha,hb⟩ := d.exists_rowEval_ne_zero_of_first_ne v q p (hp ▸ Ne.symm hn) (Ne.symm hn)
    exact ha ((h Φ).mp hb)
  · obtain ⟨Φ,ha,hb⟩ := d.exists_rowEval_ne_zero_of_first_ne v p q hp hn
    exact ha ((h Φ).mpr hb)

theorem rowAction_unique {g : d.Operators v} {A B : M}
    (ha : d.HasRowAction v g A) (hb : d.HasRowAction v g B) : A = B := by
  have first {k : d.Operators v} {C D : M} (hc : d.HasRowAction v k C)
      (hd : d.HasRowAction v k D) (p : R) : (p ᵥ* C.val) 0 = (p ᵥ* D.val) 0 := by
    obtain ⟨c,ec,_⟩ := hc
    obtain ⟨e,ee,_⟩ := hd
    apply d.first_eq_of_rowEval v
    intro Φ
    have h := (ec Φ p).symm.trans (ee Φ p)
    simpa using congrArg (· = (0:ℂ)) h |> Eq.to_iff
  obtain ⟨gL,hgL,_⟩ := d.exists_lower v 1
  have hl := d.rowAction_of_lower v hgL
  apply Subtype.ext
  ext i j
  have h := first ha hb (Pi.single i 1)
  have h' := first (ha.mul d v hl) (hb.mul d v hl) (Pi.single i 1)
  simp only [Matrix.SpecialLinearGroup.coe_mul,← Matrix.vecMul_vecMul,lower_row,
    Matrix.single_one_vecMul,Matrix.cons_val_zero,one_mul] at h'
  simp only [Matrix.single_one_vecMul] at h
  fin_cases j
  · exact h
  · exact add_left_cancel (h ▸ h')

/-- The projection obtained from the unique matrix acting on row evaluations. -/
theorem kubota_projection :
    ∃ π : d.cover v →* M, Function.Surjective π ∧
      (∀ g, π g = 1 ↔ d.IsCentralScalar v g.val) ∧
      (∀ g u, d.IsUpper v u g.val → (π g).val = !![1,u;0,1]) ∧
      (∀ g u, d.IsLower v u g.val → (π g).val = !![1,0;u,1]) := by
  choose mat act using d.exists_rowAction v
  let π : d.cover v →* M := {
    toFun := mat
    map_one' := d.rowAction_unique v (act 1) (d.rowAction_of_scalar v ⟨1,fun Φ => by simp⟩)
    map_mul' := fun g h => d.rowAction_unique v (act (g*h)) (HasRowAction.mul d v (act g) (act h)) }
  have hu (g : d.cover v) (u : K) (hg : d.IsUpper v u g.val) : π g = upperMatrix v u :=
    d.rowAction_unique v (act g) (d.rowAction_of_upper v hg)
  have hl (g : d.cover v) (u : K) (hg : d.IsLower v u g.val) : π g = lowerMatrix v u :=
    d.rowAction_unique v (act g) (d.rowAction_of_lower v hg)
  refine ⟨π,?_,fun g => ⟨fun e => d.isCentralScalar_of_rowAction_one v (e ▸ (act g : d.HasRowAction v g.val (π g))),
    fun h => d.rowAction_unique v (act g) (d.rowAction_of_scalar v h)⟩,
    fun g u hg => congrArg Subtype.val (hu g u hg),fun g u hg => congrArg Subtype.val (hl g u hg)⟩
  intro m
  apply Matrix.SL2.transvection_induction (fun m => ∃ g, π g = m) _ _ m
  · intro i j hij u
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · obtain ⟨g,hg,_⟩ := d.exists_upper v u
      let G : d.cover v := ⟨g,Subgroup.subset_closure (Or.inr (Or.inl ⟨u,hg⟩))⟩
      refine ⟨G,(hu G u hg).trans (Subtype.ext ?_)⟩
      exact (upperTransvection_matrix u).symm
    · obtain ⟨g,hg,_⟩ := d.exists_lower v u
      let G : d.cover v := ⟨g,Subgroup.subset_closure (Or.inr (Or.inr ⟨u,hg⟩))⟩
      refine ⟨G,(hl G u hg).trans (Subtype.ext ?_)⟩
      exact (lowerTransvection_matrix u).symm
    · exact (hij rfl).elim
  · rintro A B ⟨a,rfl⟩ ⟨b,rfl⟩
    exact ⟨a*b,map_mul π a b⟩

end MetaplecticPoisson.Datum
