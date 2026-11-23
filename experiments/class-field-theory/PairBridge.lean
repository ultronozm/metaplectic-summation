import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FinitePlaceAdicLocalField
import ClassFieldTheory.Theorems.HilbertSymbols.PowerClassEqOneIff
import MetaplecticSummation.Arithmetic

noncomputable section
open NumberField IsDedekindDomain ClassFieldTheory MetaplecticPoisson
namespace MetaplecticBridge

variable {F : Type} [Field F] [NumberField F] (n : ℕ+) {ζ : F} (hζ : IsPrimitiveRoot ζ (n : ℕ))
variable (p : HeightOneSpectrum (𝓞 F))
local notation "K" => LocalField F (Sum.inr p)

include hζ in
private theorem hasRoots : (primitiveRoots (n : ℕ) F).Nonempty :=
  ⟨ζ,(mem_primitiveRoots n.pos).2 hζ⟩

/-- The inverted coherent finite-place pairing, valued in the project's global roots. -/
def finiteValue (a b : Kˣ) : Mu F (n : ℕ) :=
  letI : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  let e := rootsOfUnityEquivOfPrimitiveRoots (diagonal F (.inr p)).injective (hasRoots n hζ)
  let B := finitePlaceAdicHilbertPairingFamily F n (hasRoots n hζ) p
  e.symm ((B (powerClass (p.adicCompletion F) n a) (powerClass (p.adicCompletion F) n b))⁻¹)

/-- This is precisely the power criterion in MarginalRootFormula for the
candidate, including when the residue characteristic divides the degree. -/
theorem finiteValue_right_kernel (b : Kˣ) :
    (∀ a, finiteValue n hζ p a b = 1) ↔ ∃ c : Kˣ, c^(n : ℕ) = b := by
  letI : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  let B := finitePlaceAdicHilbertPairingFamily F n (hasRoots n hζ) p
  let e := rootsOfUnityEquivOfPrimitiveRoots (diagonal F (.inr p)).injective (hasRoots n hζ)
  have hk := ((finitePlaceAdicHilbertPairingFamily_isLocallyHilbert F n (hasRoots n hζ) p).2.2.1).2
  constructor
  · intro h
    apply (powerClass_eq_one_iff (p.adicCompletion F) n b).mp
    apply hk
    intro x
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range x
    have he := h a
    change e.symm ((B (powerClass _ n a) (powerClass _ n b))⁻¹) = 1 at he
    exact inv_eq_one.mp (e.symm.injective (he.trans e.symm.map_one.symm))
  · rintro ⟨c,rfl⟩ a
    have hc : powerClass (p.adicCompletion F) n (c^(n : ℕ)) = 1 :=
      (powerClass_eq_one_iff _ n _).mpr ⟨c,rfl⟩
    change e.symm ((B (powerClass _ n a) (powerClass _ n (c ^ (n : ℕ))))⁻¹) = 1
    have hl := (congrArg (B (powerClass _ n a)) hc).trans (B (powerClass _ n a)).map_one
    exact (congrArg e.symm ((congrArg Inv.inv hl).trans inv_one)).trans e.symm.map_one

#print axioms finiteValue
#print axioms finiteValue_right_kernel
end MetaplecticBridge
