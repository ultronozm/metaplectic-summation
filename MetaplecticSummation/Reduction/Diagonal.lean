import MetaplecticSummation.Reduction.CuspIdele
import ClassFieldTheory.AlgebraicNumberTheory.Idele.FiniteMathlibTopologyComparison
import MetaplecticSummation.Reduction.UnipotentFiber
import GroundTheory.GlobalFields.TateThesis.AdeleScaling

/-! The diagonal torus, rational reduction of its idele parameter, and the cusp Haar factor. -/
noncomputable section
namespace MetaplecticPoisson
open Set NumberField Topology
open scoped Matrix MatrixGroups
variable (F : Type) [Field F] [NumberField F]

/-- The split torus in SL₂ over a commutative ring. -/
def diagonalSL {R : Type} [CommRing R] : Rˣ →* SL(2,R) where
  toFun a := ⟨!![a.val,0;0,(a⁻¹).val], by simp [Matrix.det_fin_two]⟩
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_mul' a b := by
    apply Subtype.ext
    change !![(a*b).val,0;0,((a*b)⁻¹).val] = !![a.val,0;0,(a⁻¹).val] * !![b.val,0;0,(b⁻¹).val]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_two,mul_comm]

theorem diagonalSL_matrix {R : Type} [CommRing R] (a : Rˣ) :
    (diagonalSL a).val = !![a.val,0;0,(a⁻¹).val] := rfl

theorem continuous_diagonalSL {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous (diagonalSL (R := R)) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j
  · exact Units.continuous_val
  · exact continuous_const
  · exact continuous_const
  · exact Units.continuous_val.comp continuous_inv

def ideleDiagonal : IdeleGroup F →* AdelicSL F :=
  diagonalSL.comp (IdeleGroup.equivAdeleRingUnits (K := F)).toMonoidHom

theorem continuous_ideleDiagonal : Continuous (ideleDiagonal F) :=
  continuous_diagonalSL.comp (IdeleGroup.continuous_equivAdeleRingUnits F)

theorem ideleDiagonal_principal (t : Fˣ) :
    ideleDiagonal F (IdeleGroup.principalIdele F t) = rationalSLMap F (diagonalSL t) := by
  change diagonalSL ((IdeleGroup.equivAdeleRingUnits (K := F))
    ((IdeleGroup.equivAdeleRingUnits (K := F)).symm _)) = _
  rw [MulEquiv.apply_symm_apply]
  apply Subtype.ext
  change (diagonalSL _).val = (diagonalSL t).val.map (algebraMap F (Adeles F))
  rw [diagonalSL_matrix, diagonalSL_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem diagonalSL_mul_adelicUpper (a : (Adeles F)ˣ) (u : Adeles F) :
    diagonalSL a * adelicUpper F u = adelicUpper F (a.val ^ 2 * u) * diagonalSL a := by
  have h (v : Adeles F) : (adelicUpper F v).val = !![1,v;0,1] := upperTransvection_matrix v
  apply Subtype.ext
  change (diagonalSL a).val * (adelicUpper F u).val = (adelicUpper F _).val * (diagonalSL a).val
  simp only [h, diagonalSL_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, sq, mul_assoc, mul_comm]

/-- Discretize the adelic split torus modulo its rational points, using the inverse uniformizer at w. -/
theorem exists_compact_diagonal_representatives (w : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    ∃ Ω : Set (AdelicSL F), IsCompact Ω ∧ ∀ a : IdeleGroup F,
      ∃ t : Fˣ, ∃ k : ℤ, ∃ ω ∈ Ω, ideleDiagonal F a =
        rationalSLMap F (diagonalSL t) * ideleDiagonal F (cuspIdele F w)^k * ω := by
  obtain ⟨C,hC,rep⟩ := exists_compact_idele_representatives F _ (cuspIdele_expands F w)
  refine ⟨ideleDiagonal F '' C,hC.image (continuous_ideleDiagonal F),fun a => ?_⟩
  obtain ⟨t,k,c,hc,he,_⟩ := rep a
  refine ⟨t,k,_,⟨c,hc,rfl⟩,?_⟩
  rw [he,map_mul,map_mul,map_zpow,ideleDiagonal_principal]


private theorem equivAdeleRingUnits_finitePlace (w : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (x : (w.adicCompletion F)ˣ) :
    IdeleGroup.equivAdeleRingUnits (IdeleGroup.finitePlaceIdele w x) =
      GroundTheory.Global.IdeleGroup.finiteEmbedding w x := by
  apply Units.ext
  apply Prod.ext
  · rfl
  apply RestrictedProduct.ext
  intro v
  change (IdeleGroup.finiteComponent v (IdeleGroup.finitePlaceIdele w x)).val =
    GroundTheory.Global.IdeleGroup.finiteAdeleSingle w x.val v
  by_cases he : v = w
  · subst v
    rw [IdeleGroup.finitePlaceIdele_finiteComponent_same, GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self]
  · rw [IdeleGroup.finitePlaceIdele_finiteComponent_of_ne w v x he, GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_of_ne he]
    rfl

theorem cuspIdele_haarModule (w : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    (GroundTheory.Global.IdeleGroup.ideleModule F (IdeleGroup.equivAdeleRingUnits (cuspIdele F w)) : ℝ) =
      w.asIdeal.absNorm := by
  let t := FiniteIdeleGroup.chosenLocalOrderSection w 1
  have hv : Valued.v t.val = WithZero.exp (-1 : ℤ) :=
    Classical.choose_spec (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_surjective F w (WithZero.exp (-1 : ℤ)))
  have hnorm : ‖t.val‖ = (w.asIdeal.absNorm : ℝ)⁻¹ := by
    rw [NumberField.FinitePlace.norm_def,hv,WithZeroMulInt.toNNReal_neg_apply _ (WithZero.exp_ne_zero (a := (-1 : ℤ)))]
    change (((w.asIdeal.absNorm : NNReal) ^ (-1 : ℤ) : NNReal) : ℝ) = _
    simp
  change ((GroundTheory.Global.IdeleGroup.ideleModule F)
    (IdeleGroup.equivAdeleRingUnits ((IdeleGroup.finitePlaceIdele w t)⁻¹)) : ℝ) = _
  rw [map_inv, equivAdeleRingUnits_finitePlace, ← map_inv, GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding]
  rw [Units.val_inv_eq_inv_val, norm_inv, hnorm, inv_inv]

/-- The pushforward of additive Haar under the unipotent parameter change
for the kth cusp translate contributes exactly the Siegel weight. -/
theorem map_cusp_shear_measure (w : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (k : ℕ) :
    (GroundTheory.Global.adeleMeasure F).map
      (fun u : Adeles F => (IdeleGroup.equivAdeleRingUnits (cuspIdele F w)).val^(2*k) * u) =
      ENNReal.ofReal (((w.asIdeal.absNorm : ℝ) ^ (2*k))⁻¹) • GroundTheory.Global.adeleMeasure F := by
  let z := IdeleGroup.equivAdeleRingUnits (cuspIdele F w)
  change (GroundTheory.Global.adeleMeasure F).map (fun u : Adeles F => z^(2*k) • u) = _
  rw [GroundTheory.Global.map_smul_adeleMeasure, map_pow]
  change ENNReal.ofReal (((GroundTheory.Global.IdeleGroup.ideleModule F z : ℝ) ^ (2*k))⁻¹) • _ = _
  rw [show (GroundTheory.Global.IdeleGroup.ideleModule F z : ℝ) = _ from cuspIdele_haarModule F w]

end MetaplecticPoisson
