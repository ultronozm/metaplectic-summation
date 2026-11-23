import MetaplecticSummation.Places
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots

/-! The normalized Hilbert pairing over all places of a number field. -/
namespace MetaplecticPoisson
open NumberField IsDedekindDomain Filter
variable (F : Type) [Field F] [NumberField F]

abbrev Mu (n : ℕ) := rootsOfUnity n F
abbrev SymbolFamily (n : ℕ) := (v : Place F) → (LocalField F v)ˣ → (LocalField F v)ˣ → Mu F n

/-- Reciprocity and the tame convention determine the family, including at
wild and infinite places, by weak approximation. The convention is
{uniformizer,u} reducing to u^((q-1)/n). -/
structure IsHilbertFamily (n : ℕ) (H : SymbolFamily F n) : Prop where
  continuous_pair : ∀ v, Continuous (fun a : (LocalField F v)ˣ × (LocalField F v)ˣ =>
    diagonal F v (((H v a.1 a.2 : Fˣ) : F)))
  mul_left : ∀ v a b c, H v (a*b) c = H v a c * H v b c
  mul_right : ∀ v a b c, H v a (b*c) = H v a b * H v a c
  skew : ∀ v a b, H v a b * H v b a = 1
  neg_self : ∀ v a, H v a (-a) = 1
  tame_units : ∀ (p : HeightOneSpectrum (𝓞 F)), p.asIdeal.absNorm.Coprime n →
    ∀ a b : (LocalField F (.inr p))ˣ, ‖(a : LocalField F (.inr p))‖ = 1 →
      ‖(b : LocalField F (.inr p))‖ = 1 → H (.inr p) a b = 1
  tame_uniformizer : ∀ (p : HeightOneSpectrum (𝓞 F)), p.asIdeal.absNorm.Coprime n →
    ∀ π u : (LocalField F (.inr p))ˣ, ‖(π : LocalField F (.inr p))‖ = (p.asIdeal.absNorm : ℝ)⁻¹ →
      ‖(u : LocalField F (.inr p))‖ = 1 →
      ‖diagonal F (.inr p) (((H (.inr p) π u : Fˣ) : F)) -
        (u : LocalField F (.inr p)) ^ ((p.asIdeal.absNorm - 1) / n)‖ < 1
  unramified : ∀ a b : Fˣ, ∀ᶠ v in cofinite,
    H v (Units.map (diagonal F v) a) (Units.map (diagonal F v) b) = 1
  reciprocity : ∀ a b : Fˣ,
    (∏ᶠ v, H v (Units.map (diagonal F v) a) (Units.map (diagonal F v) b)) = 1

end MetaplecticPoisson
