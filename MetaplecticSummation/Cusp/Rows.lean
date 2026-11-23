import MetaplecticSummation.Reduction.CompactBounds

/-! Local sizes of rows in the cusp and the compact set of conjugated upper unipotents. -/
noncomputable section
namespace MetaplecticPoisson
open NumberField IsDedekindDomain Set Filter
open GroundTheory.Global (fundamentalSet fundamentalSetInfinite integralFiniteAdeles mem_integralFiniteAdeles)
open scoped Matrix MatrixGroups Pointwise
open Classical
variable (F : Type) [Field F] [NumberField F]
local notation "A" => Adeles F
local notation "P" => HeightOneSpectrum (𝓞 F)
local notation "G" => AdelicSL F
local notation "Z" => fun w : P => IdeleGroup.equivAdeleRingUnits (cuspIdele F w)
local notation "N" => adelicUpper F

def cuspScale (w : P) (v : Place F) : ℝ := if v = .inr w then w.asIdeal.absNorm else 1

theorem cuspScale_one_le (w : P) (v : Place F) : 1 ≤ cuspScale F w v := by
  unfold cuspScale
  split_ifs
  · exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm w).le
  · exact le_rfl

theorem cuspScale_cofinite (w : P) : ∀ᶠ v in cofinite, cuspScale F w v = 1 :=
  (eventually_cofinite_ne (.inr w : Place F)).mono fun v hv => by simp [cuspScale,hv]

theorem cuspScale_product (w : P) : ∏ᶠ v, cuspScale F w v = (w.asIdeal.absNorm : ℝ) := by
  rw [finprod_eq_single _ (.inr w) (fun v hv => by simp [cuspScale,hv])]
  simp [cuspScale]

private theorem cuspComponent_infinite (w : P) (v : InfinitePlace F) :
    Units.map (Datum.componentHom (.inl v)).toMonoidHom (Z w) = 1 := by
  let t := FiniteIdeleGroup.chosenLocalOrderSection w 1
  change IdeleGroup.infiniteComponent v ((IdeleGroup.finitePlaceIdele w t)⁻¹) = _
  rw [map_inv,IdeleGroup.finitePlaceIdele_infiniteComponent,inv_one]
  rfl

private theorem cuspComponent_norm (w p : P) :
    ‖(Units.map (Datum.componentHom (.inr p)).toMonoidHom (Z w)).val‖ = cuspScale F w (.inr p) := by
  let t := FiniteIdeleGroup.chosenLocalOrderSection w 1
  change ‖(IdeleGroup.finiteComponent p ((IdeleGroup.finitePlaceIdele w t)⁻¹)).val‖ = _
  rw [map_inv,Units.val_inv_eq_inv_val,norm_inv]
  by_cases hp : p = w
  · subst p
    rw [IdeleGroup.finitePlaceIdele_finiteComponent_same,chosenLocalUniformizer_norm,inv_inv]
    simp [cuspScale]
  · simp [IdeleGroup.finitePlaceIdele_finiteComponent_of_ne w p t hp,cuspScale,hp]

/-- A row multiplied by the expanding diagonal dominates its isotropically contracted
size. Its first coordinate has exactly the prescribed expansion. -/
theorem cusp_row_modulus (w : P) (k : ℕ) (v : Place F) (x : Fin 2 → LocalField F v) :
    let y := x ᵥ* (localMatrix F v (ideleDiagonal F (cuspIdele F w)^k)).val
    (cuspScale F w v ^ k)⁻¹ * localRowModulus F v x ≤ localRowModulus F v y ∧
      cuspScale F w v ^ k * modulus F v (x 0) = modulus F v (y 0) := by
  let a := Units.map (Datum.componentHom v).toMonoidHom (Z w)
  have eqn : localMatrix F v (ideleDiagonal F (cuspIdele F w)^k) = diagonalSL (a^k) := by
    change localMatrix F v ((diagonalSL (Z w))^k) = _
    rw [map_pow,localMatrix_diagonal,map_pow]
  rw [eqn,diagonalSL_matrix]
  cases v with
  | inl s =>
    have ha : a = 1 := cuspComponent_infinite F w s
    simp [ha,cuspScale,localRowModulus,Matrix.vecHead,Matrix.vecTail]
  | inr p =>
    have ha : ‖a.val‖ = cuspScale F w (.inr p) := cuspComponent_norm F w p
    let Q := cuspScale F w (.inr p)^k
    have hQ : 1 ≤ Q := one_le_pow₀ (cuspScale_one_le F w _)
    have e₀ : ‖(x ᵥ* !![(a^k).val,0;0,((a^k)⁻¹).val]) 0‖ = ‖x 0‖*Q := by
      simp [Matrix.vecHead,Matrix.vecTail,Q,ha]
    have e₁ : ‖(x ᵥ* !![(a^k).val,0;0,((a^k)⁻¹).val]) 1‖ = ‖x 1‖*Q⁻¹ := by
      simp [Matrix.vecHead,Matrix.vecTail,Q,ha]
    change Q⁻¹ * max ‖x 0‖ ‖x 1‖ ≤ max _ _ ∧ Q*‖x 0‖ = _
    dsimp only [modulus]
    rw [e₀,e₁]
    refine ⟨?_,mul_comm ..⟩
    rw [mul_max_of_nonneg _ _ (inv_nonneg.mpr (zero_le_one.trans hQ))]
    apply max_le
    · rw [mul_comm]
      exact (mul_le_mul_of_nonneg_left ((inv_le_one_of_one_le₀ hQ).trans hQ) (norm_nonneg _)).trans (le_max_left ..)
    · rw [mul_comm]; exact le_max_right ..

/-- Conjugating the upper unipotents in the additive fundamental domain by a negative
cusp power leaves their parameters in a fixed compact set. -/
theorem compact_cusp_shears (w : P) :
    ∃ B : Set A, IsCompact B ∧ ∀ k : ℕ, ∀ u ∈ fundamentalSet F, ((Z w)⁻¹.val)^(2*k)*u ∈ B := by
  let B : Set A := closure (fundamentalSetInfinite F) ×ˢ (integralFiniteAdeles (𝓞 F) F : Set _)
  refine ⟨B,(GroundTheory.Global.isCompact_closure_fundamentalSetInfinite F).prod
    (GroundTheory.Global.isCompact_integralFiniteAdeles F),?_⟩
  intro k u hu
  have one : ((Z w)⁻¹.val).1 = 1 := by
    funext s
    exact congrArg Units.val (show (Units.map (Datum.componentHom (.inl s)).toMonoidHom (Z w))⁻¹ = 1 by rw [cuspComponent_infinite,inv_one])
  refine ⟨?_,mem_integralFiniteAdeles.mpr fun p => ?_⟩
  · change ((Z w)⁻¹.val).1^(2*k)*u.1 ∈ _
    rw [one,one_pow,one_mul]
    exact subset_closure hu.1
  · apply (Datum.mem_localIntegers_iff p _).mpr
    let a := Units.map (Datum.componentHom (.inr p)).toMonoidHom (Z w)
    change ‖a⁻¹.val^(2*k)*Datum.component u (.inr p)‖ ≤ 1
    rw [norm_mul,norm_pow,Units.val_inv_eq_inv_val,norm_inv]
    apply le_trans (mul_le_of_le_one_left (norm_nonneg _) ?_) ((Datum.mem_localIntegers_iff p _).mp (mem_integralFiniteAdeles.mp hu.2 p))
    exact pow_le_one₀ (inv_nonneg.mpr (norm_nonneg _)) (inv_le_one_of_one_le₀ ((cuspComponent_norm F w p).symm ▸ cuspScale_one_le F w _))

/-- Moving an arbitrary upper unipotent past the diagonal costs only a rational
upper unipotent on the left and a compact factor on the right. -/
theorem exists_compact_cusp_remainder (w : P) {K : Set G} (hK : IsCompact K) :
    ∃ K' : Set G, IsCompact K' ∧ ∀ (u : A) (k : ℕ), ∀ ω ∈ K,
      ∃ t : F, ∃ ω' ∈ K', N u * ideleDiagonal F (cuspIdele F w)^k * ω =
        rationalSLMap F (upperUnipotentParam (Multiplicative.ofAdd t)) * ideleDiagonal F (cuspIdele F w)^k * ω' := by
  obtain ⟨B,hB,bound⟩ := compact_cusp_shears F w
  refine ⟨(N '' B)*K,(hB.image (continuous_adelicUpper F)).mul hK,?_⟩
  intro u k ω hω
  obtain ⟨t,ht,_⟩ := GroundTheory.Global.existsUnique_sub_mem_fundamentalSet F u
  let a := (Z w)^k
  let u₀ := u - algebraMap F A t
  let u' := (a⁻¹).val^2*u₀
  have hb : u' ∈ B := by
    have ep : (a⁻¹).val^2 = ((Z w)⁻¹.val)^(2*k) := by
      dsimp only [a]
      rw [← inv_pow]
      change (((Z w)⁻¹.val)^k)^2 = _
      rw [← pow_mul,Nat.mul_comm k 2]
    change (a⁻¹).val^2*u₀ ∈ B
    rw [ep]
    exact bound k _ ht
  have swap : N u₀ * diagonalSL a = diagonalSL a * N u' := by
    rw [diagonalSL_mul_adelicUpper]
    simp only [u',← mul_assoc,← mul_pow,← Units.val_mul,mul_inv_cancel,Units.val_one,one_pow,one_mul]
  have hd : ideleDiagonal F (cuspIdele F w)^k = diagonalSL a := (map_pow diagonalSL _ _).symm
  refine ⟨t,N u'*ω,Set.mul_mem_mul ⟨_,hb,rfl⟩ hω,?_⟩
  rw [hd,← adelicUpper_diagonal,show u = algebraMap F A t + u₀ by dsimp [u₀]; abel,adelicUpper_add,mul_assoc _ (N u₀),swap]
  simp only [mul_assoc]

def diagonalRow (v : Place F) (p : RationalPoint F) : Fin 2 → LocalField F v :=
  ![diagonal F v p.val.1,diagonal F v p.val.2]

private theorem diagonalRow_rational (v : Place F) (p : RationalPoint F) (γ : SL(2,F)) :
    diagonalRow F v (rationalRowPerm γ p) = diagonalRow F v p ᵥ* (localMatrix F v (rationalSLMap F γ)).val := by
  have h (i j : Fin 2) : (localMatrix F v (rationalSLMap F γ)).val i j = diagonal F v (γ.val i j) := by cases v <;> rfl
  funext i
  fin_cases i <;> simp [diagonalRow,rationalRowPerm_val,Matrix.vecMul,dotProduct,Fin.sum_univ_two,h]

/-- Uniform lower bounds for the transformed radius and for the height of a nonzero
first coordinate. A rational upper shear permutes the summation rows. -/
theorem cusp_row_bounds_on_compact (w : P) {K : Set G} (hK : IsCompact K) :
    ∃ B : Place F → ℝ, (∀ v, 1 ≤ B v) ∧ (∀ᶠ v in cofinite, B v = 1) ∧
      ∀ (u : A) (k : ℕ), ∀ ω ∈ K, ∃ σ : Equiv.Perm (RationalPoint F),
        (∀ p, (σ p).val.1 = p.val.1) ∧ ∀ (p : RationalPoint F) (v : Place F),
          let y := diagonalRow F v p ᵥ* (localMatrix F v (N u * ideleDiagonal F (cuspIdele F w)^k * ω)).val
          (B v*cuspScale F w v^k)⁻¹ * Datum.vectorModulus v (σ p) ≤ localRowModulus F v y ∧
          cuspScale F w v^k * modulus F v (diagonal F v p.val.1) ≤ B v * localRowModulus F v y := by
  obtain ⟨K',hK',reps⟩ := exists_compact_cusp_remainder F w hK
  obtain ⟨B,hB,co,bounds⟩ := exists_compact_row_modulus_bounds F hK'
  refine ⟨B,hB,co,?_⟩
  intro u k ω hω
  obtain ⟨t,c,hc,he⟩ := reps u k ω hω
  let γ := upperUnipotentParam (Multiplicative.ofAdd t)
  let σ := rationalRowPerm γ
  have first (p : RationalPoint F) : (σ p).val.1 = p.val.1 := by
    change (rationalRowPerm γ p).val.1 = _
    rw [rationalRowPerm_val,show γ.val = _ from upperTransvection_matrix t]
    simp
  refine ⟨σ,first,fun p v => ?_⟩
  let h := ideleDiagonal F (cuspIdele F w)^k
  let x := diagonalRow F v (σ p)
  let s := x ᵥ* (localMatrix F v h).val
  let y := s ᵥ* (localMatrix F v c).val
  have row : diagonalRow F v p ᵥ* (localMatrix F v (N u * h * ω)).val = y := by
    rw [he,map_mul,map_mul]
    simp only [Matrix.SpecialLinearGroup.coe_mul,← Matrix.vecMul_vecMul,y,s,x,σ,diagonalRow_rational,h,γ]
  rw [row]
  obtain ⟨hr,hx⟩ := cusp_row_modulus F w k v x
  have hb := (bounds c hc v s).2
  refine ⟨?_,?_⟩
  · rw [mul_inv, mul_assoc, inv_mul_le_iff₀ (zero_lt_one.trans_le (hB v))]
    exact hr.trans hb
  · have h₀ : x 0 = diagonal F v p.val.1 := by simp [x,diagonalRow,first]
    rw [← h₀,hx]
    exact (le_max_left _ (modulus F v (s 1))).trans hb

end MetaplecticPoisson
