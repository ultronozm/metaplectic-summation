import PairBridge
import ClassFieldTheory.Theorems.HilbertSymbols.HilbertProductFormula

noncomputable section
open NumberField IsDedekindDomain ClassFieldTheory MetaplecticPoisson
namespace MetaplecticBridge
variable {F : Type} [Field F] [NumberField F] (n : ℕ+) {ζ : F} (hζ : IsPrimitiveRoot ζ (n : ℕ))

/-- At a real quadratic place the factor is the sign pairing; at complex
places and in every other degree the factor is one. -/
def infiniteValue (w : InfinitePlace F) (a b : (LocalField F (.inl w))ˣ) : Mu F (n : ℕ) := by
  classical
  exact (if hn : (n : ℕ) = 2 then
    if hw : w.IsReal then
      if InfinitePlace.Completion.ringEquivRealOfIsReal hw a.val < 0 then
        if InfinitePlace.Completion.ringEquivRealOfIsReal hw b.val < 0 then
          ⟨-1,by change (-1 : Fˣ)^(n : ℕ) = 1; rw [hn]; simp⟩
        else 1
      else 1
    else 1
  else 1 : Mu F (n : ℕ))⁻¹

theorem infiniteValue_diagonal (w : InfinitePlace F) (a b : Fˣ) :
    infiniteValue n w (Units.map (diagonal F (.inl w)) a) (Units.map (diagonal F (.inl w)) b) =
      (globalInfinitePlaceHilbertSymbol F n w a b)⁻¹ := by
  classical
  unfold infiniteValue globalInfinitePlaceHilbertSymbol
  congr 1
  split <;> rename_i hn
  · split <;> rename_i hw
    · have agree (u : Fˣ) : InfinitePlace.Completion.ringEquivRealOfIsReal hw
          (diagonal F (.inl w) u.val) = InfinitePlace.embedding_of_isReal hw u.val :=
        InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hw ((WithAbs.equiv w.1).symm u.val)
      simp only [Units.coe_map,MonoidHom.coe_ofClass] at *
      have signs (u : Fˣ) := congrArg (fun x : ℝ => x < 0) (agree u)
      by_cases ha : InfinitePlace.embedding_of_isReal hw a.val < 0 <;>
        by_cases hb : InfinitePlace.embedding_of_isReal hw b.val < 0 <;>
        simp only [signs a,signs b,ha,hb,ite_true,ite_false,dite_true,dite_false]
    · simp
  · simp

include hζ in
theorem finiteValue_diagonal (p : HeightOneSpectrum (𝓞 F)) (a b : Fˣ) :
    let hm : (primitiveRoots (n : ℕ) F).Nonempty := ⟨ζ,(mem_primitiveRoots n.pos).2 hζ⟩
    finiteValue n hζ p (Units.map (diagonal F (.inr p)) a) (Units.map (diagonal F (.inr p)) b) =
      (GlobalHilbertPairingFamily.finiteFactor F (finitePlaceAdicHilbertPairingFamily F n hm) hm p a b)⁻¹ := by
  dsimp only
  unfold finiteValue GlobalHilbertPairingFamily.finiteFactor
  exact map_inv _ _

theorem finiteValue_support (a b : Fˣ) :
    Function.HasFiniteMulSupport (fun p : HeightOneSpectrum (𝓞 F) =>
      finiteValue n hζ p (Units.map (diagonal F (.inr p)) a) (Units.map (diagonal F (.inr p)) b)) := by
  let hm : (primitiveRoots (n : ℕ) F).Nonempty := ⟨ζ,(mem_primitiveRoots n.pos).2 hζ⟩
  simp_rw [finiteValue_diagonal]
  exact ((finitePlaceAdicHilbertPairingFamily_productFormula F n hm).2.1 a b).fun_inv

/-- Reciprocity for the candidate's values on the project's diagonal embeddings. -/
theorem normalized_product (a b : Fˣ) :
    (∏ w : InfinitePlace F,
      infiniteValue n w (Units.map (diagonal F (.inl w)) a) (Units.map (diagonal F (.inl w)) b)) *
    (∏ᶠ p : HeightOneSpectrum (𝓞 F),
      finiteValue n hζ p (Units.map (diagonal F (.inr p)) a) (Units.map (diagonal F (.inr p)) b)) = 1 := by
  let hm : (primitiveRoots (n : ℕ) F).Nonempty := ⟨ζ,(mem_primitiveRoots n.pos).2 hζ⟩
  have hr := (finitePlaceAdicHilbertPairingFamily_productFormula F n hm).2.2 a b
  simp_rw [infiniteValue_diagonal,finiteValue_diagonal]
  rw [Finset.prod_inv_distrib,finprod_inv_distrib,← mul_inv,hr,inv_one]

#print axioms infiniteValue_diagonal
#print axioms finiteValue_diagonal
#print axioms finiteValue_support
#print axioms normalized_product
end MetaplecticBridge
