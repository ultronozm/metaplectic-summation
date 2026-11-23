import MetaplecticSummation.Reduction.SmallRow

/-! Reduction of adelic SL₂ to the nonnegative powers of a fixed cusp idele. -/
noncomputable section
namespace MetaplecticPoisson
open Set NumberField MeasureTheory IsDedekindDomain
open GroundTheory.Global (integralFiniteAdeles mem_integralFiniteAdeles isCompact_integralFiniteAdeles
  fundamentalSet fundamentalSetInfinite isCompact_closure_fundamentalSetInfinite adeleMeasure
  adeleMeasure_smul adeleMeasure_fundamentalSet)
open scoped Pointwise ENNReal MatrixGroups
open Classical
variable (F : Type) [Field F] [NumberField F]
local notation "A" => Adeles F
local notation "I" => integralFiniteAdeles (𝓞 F) F

private theorem exists_compact_pivot_bound (C : Set A) (hC : IsCompact C)
    (hfin : ∀ x ∈ C, x.2 ∈ I) :
    ∃ E : Set A, IsCompact E ∧ ∀ x ∈ C, ∀ y ∈ C, ∀ b : A,
      (∀ v, ‖Datum.component b v‖ = max ‖Datum.component x v‖ ‖Datum.component y v‖) → b ∈ E := by
  have bound (w : InfinitePlace F) := hC.bddAbove_image
    (show Continuous (fun x : A => ‖x.1 w‖) from ((continuous_apply w).comp continuous_fst).norm).continuousOn
  choose R hR using bound
  let B : Set (InfiniteAdeleRing F) := univ.pi fun w : InfinitePlace F => Metric.closedBall (0 : w.Completion) (R w)
  have hB : IsCompact B := by
    apply isCompact_univ_pi
    intro w
    have h := InfinitePlace.Completion.isometry_extensionEmbedding w
    rw [← h.preimage_closedBall (0 : w.Completion) (R w)]
    exact h.isClosedEmbedding.isCompact_preimage (isCompact_closedBall _ _)
  refine ⟨B ×ˢ (I : Set _),hB.prod (isCompact_integralFiniteAdeles F),?_⟩
  intro x hx y hy b hb
  constructor
  · intro w _
    have h : ‖b.1 w‖ = max ‖x.1 w‖ ‖y.1 w‖ := hb (.inl w)
    exact Metric.mem_closedBall.mpr <| (dist_zero_right _).trans_le <| h.trans_le <|
      max_le (hR w ⟨x,hx,rfl⟩) (hR w ⟨y,hy,rfl⟩)
  · apply mem_integralFiniteAdeles.mpr
    intro p
    apply (Datum.mem_localIntegers_iff p _).mpr
    exact (hb (.inr p)).trans_le (max_le
      ((Datum.mem_localIntegers_iff p _).mp (mem_integralFiniteAdeles.mp (hfin x hx) p))
      ((Datum.mem_localIntegers_iff p _).mp (mem_integralFiniteAdeles.mp (hfin y hy) p)))

private theorem module_bounded_on_compact (C : Set A) (hC : IsCompact C) :
    ∃ M : ℝ, ∀ b : Aˣ, b.val ∈ C → (GroundTheory.Global.IdeleGroup.ideleModule F b : ℝ) ≤ M := by
  let B : Set A := closure (fundamentalSetInfinite F) ×ˢ (I : Set _)
  have hB : IsCompact B := (isCompact_closure_fundamentalSetInfinite F).prod (isCompact_integralFiniteAdeles F)
  let μ := adeleMeasure F
  refine ⟨(μ (C * B)).toReal,fun b hb => ?_⟩
  have hsub : b • fundamentalSet F ⊆ C * B := by
    rintro _ ⟨x,hx,rfl⟩
    exact Set.mul_mem_mul hb ⟨subset_closure hx.1,hx.2⟩
  have h := measure_mono (μ := μ) hsub
  change adeleMeasure F _ ≤ μ (C * B) at h
  rw [adeleMeasure_smul,adeleMeasure_fundamentalSet,mul_one] at h
  simpa only [ENNReal.toReal_ofReal (GroundTheory.Global.IdeleGroup.ideleModule F b).property.le]
    using ENNReal.toReal_mono (hC.mul hB).measure_lt_top.ne h


local notation "P" => HeightOneSpectrum (𝓞 F)
local notation "J" => IdeleGroup F
local notation "e" => (IdeleGroup.equivAdeleRingUnits (K := F))
local notation "principal" => IdeleGroup.principalIdele F
local notation "m" => GroundTheory.Global.IdeleGroup.ideleModule F

private theorem exists_natural_torus_representatives (w : P) (E : Set A) (hE : IsCompact E) :
    ∃ C : Set J, IsCompact C ∧ ∀ b : Aˣ, (b⁻¹).val ∈ E →
      ∃ t : Fˣ, ∃ k : ℕ, ∃ c ∈ C, b = e (principal t * cuspIdele F w ^ k * c) := by
  let z := cuspIdele F w
  obtain ⟨C,hC,rep⟩ := exists_compact_idele_representatives F z (cuspIdele_expands F w)
  let f := fun j : J => (e j).val
  have hf : Continuous f := Units.continuous_val.comp (IdeleGroup.continuous_equivAdeleRingUnits F)
  obtain ⟨M,hM⟩ := module_bounded_on_compact F (E * (f '' C)) (hE.mul (hC.image hf))
  let q : ℝ := w.asIdeal.absNorm
  have hq : 1 < q := by dsimp [q]; exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm w
  obtain ⟨N,hN⟩ := pow_unbounded_of_one_lt M hq
  let shift := z ^ (-(N : ℤ))
  refine ⟨(shift * ·) '' C,hC.image (continuous_const_mul _),?_⟩
  intro b hb
  obtain ⟨t,k,c,hc,he,_⟩ := rep ((e).symm b)
  have hb' : b = e (principal t * z ^ k * c) := ((e).apply_symm_apply b).symm.trans (congrArg e he)
  let y := (e (principal t))⁻¹ * (e z)^(-k)
  have hy : y = b⁻¹ * e c := by
    rw [hb',map_mul,map_mul,map_zpow]
    dsimp only [y]
    rw [zpow_neg]
    calc
      _ = (e c)⁻¹ * (e c) * ((e (principal t))⁻¹ * ((e z)^k)⁻¹) := by simp
      _ = _ := by simp only [mul_inv_rev]; ac_rfl
  have hbound := hM y (hy ▸ Set.mul_mem_mul hb (show (e c).val ∈ f '' C from ⟨c,hc,rfl⟩))
  have hdiag : e (principal t) = GroundTheory.Global.IdeleGroup.diagonal F t := (e).apply_symm_apply _
  have hmod : (m y : ℝ) = q^(-k) := by
    dsimp only [y]
    rw [map_mul,map_inv,hdiag,GroundTheory.Global.IdeleGroup.ideleModule_diagonal,inv_one,one_mul,map_zpow]
    change (m (e z) : ℝ)^(-k) = _
    rw [show (m (e z) : ℝ) = q from cuspIdele_haarModule F w]
  rw [hmod] at hbound
  have hlt : -k < (N : ℤ) := (zpow_lt_zpow_iff_right₀ hq).mp (by simpa using hbound.trans_lt hN)
  let l := (k+N).toNat
  have hl : (l : ℤ) - N = k := by dsimp [l]; omega
  refine ⟨t,l,shift*c,⟨c,hc,rfl⟩,?_⟩
  rw [hb']
  apply congrArg e
  simp only [shift,← mul_assoc]
  rw [mul_assoc (principal t) (z ^ l),← zpow_natCast,← zpow_add,← sub_eq_add_neg,hl]

local notation "G" => AdelicSL F

private theorem bottomRow_triangular (δ : SL(2,F)) (u : A) (a : Aˣ) :
    let g := rationalSLMap F δ * (adelicUpper F u * diagonalSL a)
    (g.val 1 0,g.val 1 1) = triangularRow F u a
      (algebraMap F A (δ.val 1 0),algebraMap F A (δ.val 1 1)) := by
  let d := (rationalSLMap F δ).val
  change ((d * ((adelicUpper F u).val * (diagonalSL a).val)) 1 0,
    (d * ((adelicUpper F u).val * (diagonalSL a).val)) 1 1) = _
  rw [show (adelicUpper F u).val = _ from upperTransvection_matrix u,diagonalSL_matrix]
  have h (i j : Fin 2) : d i j = algebraMap F A (δ.val i j) := rfl
  apply Prod.ext <;> simp [triangularRow,Matrix.mul_apply,Fin.sum_univ_two,h] <;> ring

private theorem exists_reduced_iwasawa :
    ∃ E : Set A, IsCompact E ∧ ∃ K : Set G, IsCompact K ∧ ∀ g : G,
      ∃ γ : SL(2,F), ∃ u : A, ∃ b : Aˣ, (b⁻¹).val ∈ E ∧ ∃ ω ∈ K,
        g = rationalSLMap F γ * adelicUpper F u * diagonalSL b * ω := by
  obtain ⟨C,hC,hfin,small⟩ := exists_uniform_small_row F
  obtain ⟨E,hE,bound⟩ := exists_compact_pivot_bound F C hC hfin
  let B := boundedAdelicMatrices F
  have hB := isCompact_boundedAdelicMatrices F
  refine ⟨E,hE,B * B,hB.mul hB,fun g => ?_⟩
  obtain ⟨u,a,ω,hω,he,_⟩ := exists_adelic_iwasawa F g
  obtain ⟨v,hv,hvC⟩ := small u a
  obtain ⟨δ,hδ⟩ := rationalBottomRow_surjective (⟨v,hv⟩ : RationalPoint F)
  have hrow := congrArg Subtype.val hδ
  rw [rationalBottomRow_val] at hrow
  change (δ.val 1 0,δ.val 1 1) = v at hrow
  let g₁ := rationalSLMap F δ * (adelicUpper F u * diagonalSL a)
  have mem : (g₁.val 1 0,g₁.val 1 1) ∈ C ×ˢ C := by
    rw [show (g₁.val 1 0,g₁.val 1 1) = _ from bottomRow_triangular F δ u a]
    rwa [← hrow] at hvC
  obtain ⟨u',b,ω',hω',he',hpivot⟩ := exists_adelic_iwasawa F g₁
  refine ⟨δ⁻¹,u',b,bound _ mem.1 _ mem.2 _ hpivot,ω'*ω,Set.mul_mem_mul hω' hω,?_⟩
  rw [he,map_inv]
  calc
    _ = (rationalSLMap F δ)⁻¹ * g₁ * ω := by simp [g₁]
    _ = _ := by rw [he']; group

/-- A single compact set and the nonnegative powers of the cusp idele give a Siegel
cover of adelic SL₂ modulo rational matrices and upper unipotents. -/
theorem exists_natural_cusp_cover (w : P) :
    ∃ Ω : Set G, IsCompact Ω ∧ ∀ g : G, ∃ γ : SL(2,F), ∃ u : A, ∃ k : ℕ, ∃ ω ∈ Ω,
      g = rationalSLMap F γ * adelicUpper F u * ideleDiagonal F (cuspIdele F w)^k * ω := by
  obtain ⟨E,hE,K,hK,rep⟩ := exists_reduced_iwasawa F
  obtain ⟨C,hC,torus⟩ := exists_natural_torus_representatives F w E hE
  refine ⟨(ideleDiagonal F '' C) * K,(hC.image (continuous_ideleDiagonal F)).mul hK,fun g => ?_⟩
  obtain ⟨γ,u,b,hb,ω,hω,he⟩ := rep g
  obtain ⟨t,k,c,hc,hbc⟩ := torus b hb
  have hd : diagonalSL b = rationalSLMap F (diagonalSL t) * ideleDiagonal F (cuspIdele F w)^k * ideleDiagonal F c := by
    rw [hbc]
    change ideleDiagonal F _ = _
    rw [map_mul,map_mul,map_pow,ideleDiagonal_principal]
  let d := e (principal t)
  have ht : rationalSLMap F (diagonalSL t) = diagonalSL d := (ideleDiagonal_principal F t).symm
  have hu : adelicUpper F u * diagonalSL d = diagonalSL d * adelicUpper F ((d⁻¹).val^2*u) := by
    rw [diagonalSL_mul_adelicUpper,← mul_assoc,← mul_pow,← Units.val_mul,mul_inv_cancel,Units.val_one,one_pow,one_mul]
  refine ⟨γ * diagonalSL t,(d⁻¹).val^2*u,k,ideleDiagonal F c * ω,Set.mul_mem_mul ⟨c,hc,rfl⟩ hω,?_⟩
  rw [he,hd,map_mul,ht]
  simp only [mul_assoc]
  rw [← mul_assoc (adelicUpper F u) (diagonalSL d),hu]
  simp only [mul_assoc]

end MetaplecticPoisson
