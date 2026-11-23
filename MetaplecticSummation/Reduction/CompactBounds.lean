import MetaplecticSummation.Reduction.AdelicIwasawa

/-! Uniform local norm bounds on compact sets of adelic matrices, for Lemmas B.8 and B.9. -/
noncomputable section
namespace MetaplecticPoisson
open Set Filter NumberField IsDedekindDomain
open GroundTheory.Global (integralFiniteAdeles mem_integralFiniteAdeles isOpen_integralFiniteAdeles)
open scoped Pointwise MatrixGroups Matrix
open Classical
variable (F : Type) [Field F] [NumberField F]
local notation "A" => Adeles F
local notation "P" => HeightOneSpectrum (𝓞 F)
local notation "G" => AdelicSL F
local notation "I" => integralFiniteAdeles (𝓞 F) F

private theorem compact_integral_cofinite {C : Set (FiniteAdeleRing (𝓞 F) F)} (hC : IsCompact C) :
    ∀ᶠ p : P in cofinite, ∀ x ∈ C, x p ∈ p.adicCompletionIntegers F := by
  let U (a : FiniteAdeleRing (𝓞 F) F) := a +ᵥ (I : Set (FiniteAdeleRing (𝓞 F) F))
  have self (a : FiniteAdeleRing (𝓞 F) F) : a ∈ U a := by
    change a ∈ (fun b : FiniteAdeleRing (𝓞 F) F => a+b) '' (I : Set (FiniteAdeleRing (𝓞 F) F))
    exact ⟨0,(I).zero_mem,add_zero a⟩
  obtain ⟨T,hT⟩ := hC.elim_finite_subcover
    U (fun a => isOpen_integralFiniteAdeles.vadd a)
    (fun a _ => mem_iUnion.mpr ⟨a,self a⟩)
  have he : ∀ᶠ p : P in cofinite, ∀ a ∈ T, a p ∈ p.adicCompletionIntegers F :=
    T.eventually_all.mpr fun a _ => a.property
  filter_upwards [he] with p hp
  intro x hx
  obtain ⟨a,ha,b,hb,rfl⟩ := mem_iUnion₂.mp (hT hx)
  exact (p.adicCompletionIntegers F).add_mem _ _ (hp a ha) ((mem_integralFiniteAdeles.mp hb) p)

private theorem continuous_entry (i j : Fin 2) : Continuous (fun g : G => g.val i j) :=
  (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)

/-- A compact family of adelic matrices and their inverses has one common
entry bound at every place. Outside a finite set the bound is one. -/
theorem exists_compact_matrix_bounds {K : Set G} (hK : IsCompact K) :
    ∃ C : Place F → ℝ, (∀ v, 1 ≤ C v) ∧ (∀ᶠ v in cofinite, C v = 1) ∧
      ∀ g ∈ K, ∀ v i j, ‖(localMatrix F v g).val i j‖ ≤ C v ∧
        ‖(localMatrix F v g⁻¹).val i j‖ ≤ C v := by
  let B := K ∪ K⁻¹
  have hB : IsCompact B := hK.union hK.inv
  let E : Set A := ⋃ i : Fin 2, ⋃ j : Fin 2, (fun g : G => g.val i j) '' B
  have hE : IsCompact E := isCompact_iUnion fun i => isCompact_iUnion fun j => hB.image (continuous_entry F i j)
  have mem (g : G) (hg : g ∈ B) (i j : Fin 2) : g.val i j ∈ E :=
    mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨j,⟨g,hg,rfl⟩⟩⟩
  let good (v : Place F) := ∀ x ∈ E, ‖Datum.component x v‖ ≤ 1
  have hgood : ∀ᶠ v in cofinite, good v := Datum.eventually_place_of_finite <| by
    filter_upwards [compact_integral_cofinite F (hE.image continuous_snd)] with p hp
    intro x hx
    exact (Datum.mem_localIntegers_iff p _).mp (hp _ ⟨x,hx,rfl⟩)
  choose R hR using fun v => hE.bddAbove_image (Datum.continuous_component v).norm.continuousOn
  let C := fun v => if good v then 1 else max 1 (R v)
  have h (v) (x : A) (hx : x ∈ E) : ‖Datum.component x v‖ ≤ C v := by
    unfold C
    split_ifs with hv
    · exact hv x hx
    · exact (hR v ⟨x,hx,rfl⟩).trans (le_max_right ..)
  refine ⟨C,fun v => by by_cases hv : good v <;> simp [C,hv],hgood.mono fun v hv => by simp [C,hv],?_⟩
  intro g hg v i j
  exact ⟨h v _ (mem g (Or.inl hg) i j),h v _ (mem g⁻¹ (Or.inr (by simpa using hg)) i j)⟩

private def triangleFactor : Place F → ℝ
  | .inl _ => 2
  | .inr _ => 1

private theorem local_row_bound (v : Place F) (a : SL(2,LocalField F v)) (z : Fin 2 → LocalField F v)
    {C : ℝ} (ha : ∀ i j, ‖a.val i j‖ ≤ C) :
    max ‖(z ᵥ* a.val) 0‖ ‖(z ᵥ* a.val) 1‖ ≤ (triangleFactor F v * C) * max ‖z 0‖ ‖z 1‖ := by
  let R := max ‖z 0‖ ‖z 1‖
  have term (i j : Fin 2) : ‖z i * a.val i j‖ ≤ C*R := by
    rw [norm_mul,mul_comm C]
    have h : ‖z i‖ ≤ R := by fin_cases i <;> first | exact le_max_left .. | exact le_max_right ..
    exact mul_le_mul h (ha i j) (norm_nonneg _) ((norm_nonneg _).trans (le_max_left ..))
  have entry (j : Fin 2) : ‖(z ᵥ* a.val) j‖ ≤ (triangleFactor F v*C)*R := by
    change ‖∑ i, z i*a.val i j‖ ≤ _
    rw [Fin.sum_univ_two]
    cases v with
    | inl w =>
      change _ ≤ (2*C)*R
      exact (norm_add_le ..).trans ((add_le_add (term 0 j) (term 1 j)).trans_eq (by ring))
    | inr p =>
      let : IsUltrametricDist (LocalField F (.inr p)) := inferInstanceAs (IsUltrametricDist (p.adicCompletion F))
      change _ ≤ (1*C)*R
      rw [one_mul]
      exact (IsUltrametricDist.norm_add_le_max ..).trans (max_le (term 0 j) (term 1 j))
  exact max_le (entry 0) (entry 1)

/-- Uniform two-sided comparison of local maximum norms for row vectors multiplied by
matrices in a compact adelic set. Almost all finite places preserve the norm exactly. -/
theorem exists_compact_row_bounds {K : Set G} (hK : IsCompact K) :
    ∃ B : Place F → ℝ, (∀ v, 1 ≤ B v) ∧ (∀ᶠ v in cofinite, B v = 1) ∧
      ∀ g ∈ K, ∀ v (z : Fin 2 → LocalField F v),
        let a := (localMatrix F v g).val
        max ‖(z ᵥ* a) 0‖ ‖(z ᵥ* a) 1‖ ≤ B v * max ‖z 0‖ ‖z 1‖ ∧
        max ‖z 0‖ ‖z 1‖ ≤ B v * max ‖(z ᵥ* a) 0‖ ‖(z ᵥ* a) 1‖ := by
  obtain ⟨C,hC,hgood,bounds⟩ := exists_compact_matrix_bounds F hK
  have htri (v : Place F) : 1 ≤ triangleFactor F v := by cases v <;> norm_num [triangleFactor]
  have ht : ∀ᶠ v in cofinite, triangleFactor F v = 1 := Datum.eventually_place_of_finite (Filter.Eventually.of_forall fun _ => rfl)
  refine ⟨fun v => triangleFactor F v*C v,fun v => one_le_mul_of_one_le_of_one_le (htri v) (hC v),?_,?_⟩
  · filter_upwards [ht,hgood] with v h₁ h₂
    rw [h₁,h₂,one_mul]
  intro g hg v z
  let a := localMatrix F v g
  have hb := bounds g hg v
  refine ⟨local_row_bound F v a z (fun i j => (hb i j).1),?_⟩
  have hinv (i j) : ‖a⁻¹.val i j‖ ≤ C v := by simpa only [a,map_inv] using (hb i j).2
  have inv := local_row_bound F v a⁻¹ (z ᵥ* a.val) hinv
  have hmul : a.val * a⁻¹.val = 1 := congrArg Subtype.val (mul_inv_cancel a)
  simpa only [Matrix.vecMul_vecMul,hmul,Matrix.vecMul_one] using inv

/-- The paper's maximum row modulus, using squared complex absolute values. -/
def localRowModulus (v : Place F) (z : Fin 2 → LocalField F v) : ℝ :=
  max (modulus F v (z 0)) (modulus F v (z 1))

theorem exists_compact_row_modulus_bounds {K : Set G} (hK : IsCompact K) :
    ∃ C : Place F → ℝ, (∀ v, 1 ≤ C v) ∧ (∀ᶠ v in cofinite, C v = 1) ∧
      ∀ g ∈ K, ∀ v (z : Fin 2 → LocalField F v),
        let y := z ᵥ* (localMatrix F v g).val
        localRowModulus F v y ≤ C v * localRowModulus F v z ∧
        localRowModulus F v z ≤ C v * localRowModulus F v y := by
  obtain ⟨B,hB,hgood,bound⟩ := exists_compact_row_bounds F hK
  let m : Place F → ℕ := Sum.elim InfinitePlace.mult (fun _ => 1)
  have hm (v : Place F) (z : Fin 2 → LocalField F v) :
      localRowModulus F v z = (max ‖z 0‖ ‖z 1‖)^(m v) := by
    cases v with
    | inr p => exact (pow_one _).symm
    | inl w =>
      change max (‖z 0‖^w.mult) (‖z 1‖^w.mult) = (max ‖z 0‖ ‖z 1‖)^w.mult
      rcases le_total ‖z 0‖ ‖z 1‖ with h | h
      · rw [max_eq_right h,max_eq_right (pow_le_pow_left₀ (norm_nonneg _) h _)]
      · rw [max_eq_left h,max_eq_left (pow_le_pow_left₀ (norm_nonneg _) h _)]
  refine ⟨fun v => (B v)^(m v),fun v => one_le_pow₀ (hB v),hgood.mono fun v hv => by simp [hv],?_⟩
  intro g hg v z
  obtain ⟨h₁,h₂⟩ := bound g hg v z
  simp only [hm,← mul_pow]
  exact ⟨pow_le_pow_left₀ ((norm_nonneg _).trans (le_max_left ..)) h₁ _,
    pow_le_pow_left₀ ((norm_nonneg _).trans (le_max_left ..)) h₂ _⟩

end MetaplecticPoisson
