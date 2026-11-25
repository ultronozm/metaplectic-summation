import MetaplecticSummation.Reduction.LocalIwasawa

/-! Local Iwasawa factors over all places and compact reduction with integer torus exponent. -/
noncomputable section
namespace MetaplecticPoisson
open Set NumberField IsDedekindDomain Topology Filter
open scoped Matrix MatrixGroups Pointwise
open Classical
variable (F : Type) [Field F] [NumberField F]
local notation "G" => AdelicSL F
local notation "A" => Adeles F
local notation "P" => HeightOneSpectrum (𝓞 F)

abbrev localMatrix (v : Place F) : G →* SL(2,LocalField F v) :=
  Matrix.SpecialLinearGroup.map (Datum.componentHom v)

private def adeleOfLocal (f : ∀ v, LocalField F v)
    (h : ∀ᶠ p : P in cofinite, ‖f (.inr p)‖ ≤ 1) : A :=
  (fun w => f (.inl w), ⟨fun p => f (.inr p), h.mono fun p hp => (Datum.mem_localIntegers_iff p _).mpr hp⟩)

private theorem component_adeleOfLocal (f : ∀ v, LocalField F v) h (v : Place F) :
    Datum.component (adeleOfLocal F f h) v = f v := by cases v <;> rfl

private theorem exists_idele_of_local (a : ∀ v, (LocalField F v)ˣ)
    (ha : ∀ᶠ p : P in cofinite, ‖(a (.inr p)).val‖ = 1) :
    ∃ z : Aˣ, ∀ v, Units.map (Datum.componentHom v).toMonoidHom z = a v := by
  let b := adeleOfLocal F (fun v => (a v).val) (ha.mono fun _ h => h.le)
  let c := adeleOfLocal F (fun v => (a v)⁻¹.val) (ha.mono fun p h => by simp [h])
  have hc (v) : Datum.component c v = (a v)⁻¹.val := component_adeleOfLocal F _ _ v
  have hb (v) : Datum.component b v = (a v).val := component_adeleOfLocal F _ _ v
  have localOne (v : Place F) : Datum.component (b*c) v = Datum.component 1 v := by
    change Datum.componentHom v (b*c) = Datum.componentHom v 1
    rw [map_mul,map_one]
    exact (congrArg₂ (· * ·) (hb v) (hc v)).trans (a v).val_inv
  have one : b*c=1 := Prod.ext (funext fun w => localOne (.inl w)) (Subtype.ext (funext fun p => localOne (.inr p)))
  exact ⟨⟨b,c,one,(mul_comm _ _).trans one⟩,fun v => Units.ext (hb v)⟩

/-- Matrices with all entries in the adelic unit ball. -/
def boundedAdelicMatrices : Set G :=
  {g | ∀ i j v, ‖Datum.component (g.val i j) v‖ ≤ 1}

theorem isCompact_boundedAdelicMatrices : IsCompact (boundedAdelicMatrices F) := by
  let B : Set (InfiniteAdeleRing F) := univ.pi fun w : InfinitePlace F => Metric.closedBall (0 : w.Completion) 1
  have hB : IsCompact B := by
    apply isCompact_univ_pi
    intro w
    have h := InfinitePlace.Completion.isometry_extensionEmbedding w
    rw [← h.preimage_closedBall (0 : w.Completion) 1]
    exact h.isClosedEmbedding.isCompact_preimage (isCompact_closedBall _ _)
  let C : Set A := B ×ˢ (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set _)
  have hC := hB.prod (GroundTheory.Global.isCompact_integralFiniteAdeles F)
  have memC (x : A) : x ∈ C ↔ ∀ v, ‖Datum.component x v‖ ≤ 1 := by
    constructor
    · intro h v
      cases v with
      | inl w =>
        change ‖x.1 w‖ ≤ 1
        simpa only [Metric.mem_closedBall,dist_zero_right] using h.1 w (mem_univ w)
      | inr p => exact (Datum.mem_localIntegers_iff p _).mp ((GroundTheory.Global.mem_integralFiniteAdeles.mp h.2) p)
    · intro h
      refine ⟨fun w _ => ?_,GroundTheory.Global.mem_integralFiniteAdeles.mpr fun p => (Datum.mem_localIntegers_iff p _).mpr (h (.inr p))⟩
      have hx : ‖x.1 w‖ ≤ 1 := h (.inl w)
      exact Metric.mem_closedBall.mpr ((dist_zero_right _).trans_le hx)
  have eqn : boundedAdelicMatrices F = ((↑) : G → Matrix (Fin 2) (Fin 2) A) ⁻¹' C.matrix := by
    ext g
    change (∀ i j v, ‖Datum.component (g.val i j) v‖ ≤ 1) ↔ ∀ i j, g.val i j ∈ C
    simp only [memC]
  rw [eqn]
  exact Matrix.SpecialLinearGroup.isClosedEmbedding_val.isCompact_preimage (IsCompact.matrix (show IsCompact C from hC))

private theorem localMatrix_upper (v : Place F) (u : A) :
    localMatrix F v (adelicUpper F u) = upperUnipotentParam (Multiplicative.ofAdd (Datum.component u v)) := by
  apply Subtype.ext
  change (adelicUpper F u).val.map (Datum.componentHom v) = _
  rw [show (adelicUpper F u).val = _ from upperTransvection_matrix u,
    show (upperUnipotentParam (Multiplicative.ofAdd (Datum.component u v))).val = _ from upperTransvection_matrix _]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [show Datum.component u v = Datum.componentHom v u from rfl]

theorem localMatrix_diagonal (v : Place F) (a : Aˣ) :
    localMatrix F v (diagonalSL a) = diagonalSL (Units.map (Datum.componentHom v).toMonoidHom a) := by
  apply Subtype.ext
  change (diagonalSL a).val.map (Datum.componentHom v) = _
  rw [diagonalSL_matrix,diagonalSL_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem exists_adelic_iwasawa (g : G) :
    ∃ (u : A) (z : Aˣ) (ω : G), ω ∈ boundedAdelicMatrices F ∧
      g = adelicUpper F u * diagonalSL z * ω ∧
      ∀ v : Place F, ‖(Units.map (Datum.componentHom v).toMonoidHom z)⁻¹.val‖ =
        max ‖(localMatrix F v g).val 1 0‖ ‖(localMatrix F v g).val 1 1‖ := by
  let gᵥ := fun v => localMatrix F v g
  choose u a s r hr ha hu he using fun v => exists_local_iwasawa (gᵥ v)
  have integral : ∀ᶠ p : P in cofinite, ∀ i j, ‖(gᵥ (.inr p)).val i j‖ ≤ 1 :=
    eventually_all.mpr fun i => eventually_all.mpr fun j =>
      (g.val i j).2.property.mono fun p hp => (Datum.mem_localIntegers_iff p _).mp hp
  have ha₀ : ∀ᶠ p : P in cofinite, ‖(a (.inr p)).val‖ = 1 := by
    filter_upwards [integral] with p hp
    let : IsUltrametricDist (LocalField F (.inr p)) := inferInstanceAs (IsUltrametricDist (p.adicCompletion F))
    have h := ha (.inr p)
    rwa [max_norm_bottomRow_of_integral _ hp,Units.val_inv_eq_inv_val,norm_inv,inv_eq_one] at h
  have hu₀ : ∀ᶠ p : P in cofinite, ‖u (.inr p)‖ ≤ 1 := by
    filter_upwards [integral,ha₀] with p hp h
    exact (hu (.inr p)).trans (by rw [h,mul_one]; exact max_le (hp _ _) (hp _ _))
  let U := adeleOfLocal F u hu₀
  obtain ⟨z,hz⟩ := exists_idele_of_local F a ha₀
  let b := adelicUpper F U * diagonalSL z
  let ω := b⁻¹*g
  have hω (v : Place F) : localMatrix F v ω = iwasawaChart (s v) (r v) := by
    change localMatrix F v (b⁻¹*g) = _
    rw [map_mul,map_inv,show b = adelicUpper F U * diagonalSL z from rfl,map_mul,localMatrix_upper,localMatrix_diagonal,hz,component_adeleOfLocal]
    change _ * gᵥ v = _
    rw [he v,inv_mul_cancel_left]
  refine ⟨U,z,ω,?_,(mul_inv_cancel_left b g).symm,fun v => by rw [hz v]; exact ha v⟩
  intro i j v
  change ‖(localMatrix F v ω).val i j‖ ≤ 1
  rw [hω]
  cases hs : s v <;> fin_cases i <;> fin_cases j <;> simp [iwasawaChart, hr v]

private theorem upper_mul_diagonal (u : A) (a : Aˣ) :
    adelicUpper F u * diagonalSL a = diagonalSL a * adelicUpper F ((a⁻¹).val^2*u) := by
  rw [diagonalSL_mul_adelicUpper, ← mul_assoc, ← mul_pow, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_pow, one_mul]

/-- The rational translates of the unipotent, integral powers of the fixed cusp
idele and a single compact set cover adelic SL₂. Here the torus exponent ranges over ℤ. -/
theorem exists_integer_cusp_cover (w : P) :
    ∃ Ω : Set G, IsCompact Ω ∧ ∀ g : G, ∃ γ : SL(2,F), ∃ u : A, ∃ k : ℤ, ∃ ω ∈ Ω,
      g = rationalSLMap F γ * adelicUpper F u * ideleDiagonal F (cuspIdele F w)^k * ω := by
  obtain ⟨C,hC,rep⟩ := exists_compact_diagonal_representatives F w
  refine ⟨C * boundedAdelicMatrices F,hC.mul (isCompact_boundedAdelicMatrices F),fun g => ?_⟩
  obtain ⟨u,a,b,hb,he,_⟩ := exists_adelic_iwasawa F g
  let e := IdeleGroup.equivAdeleRingUnits (K := F)
  obtain ⟨t,k,c,hc,ht⟩ := rep (e.symm a)
  have hdiag : diagonalSL a = rationalSLMap F (diagonalSL t) * ideleDiagonal F (cuspIdele F w)^k * c := by
    simpa only [ideleDiagonal,MonoidHom.coe_comp,Function.comp_apply,MulEquiv.coe_toMonoidHom,
      show IdeleGroup.equivAdeleRingUnits (e.symm a) = a from e.apply_symm_apply a] using ht
  let d := e (IdeleGroup.principalIdele F t)
  have hd : rationalSLMap F (diagonalSL t) = diagonalSL d := (ideleDiagonal_principal F t).symm
  refine ⟨diagonalSL t,(d⁻¹).val^2*u,k,c*b,⟨c,hc,b,hb,rfl⟩,?_⟩
  rw [he,hdiag,hd]
  simp only [← mul_assoc,upper_mul_diagonal]

end MetaplecticPoisson
