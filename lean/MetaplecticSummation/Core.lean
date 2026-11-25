import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.LinearAlgebra.PiTensorProduct.Basic

/-! Chart formulas, ray limits and algebraic restricted tensor products. -/

namespace MetaplecticPoisson

noncomputable section

open MeasureTheory Filter
open scoped TensorProduct Topology

variable {K : Type*} [Field K]

/-- Coordinates on the two charts, with the nonzero coordinate a unit. -/
abbrev Charts (K : Type*) [Field K] := (Kˣ → K → ℂ) × (K → Kˣ → ℂ)

def Glues (h : Kˣ → Kˣ → ℂ) (f : Charts K) : Prop :=
  ∀ x y : Kˣ, f.1 x y = h x y * f.2 x y

section Local
variable [MeasurableSpace K]

/-- The two line integrals at determinant t^n (§4.1). -/
def radon (n : ℕ) (h : Kˣ → Kˣ → ℂ) (modulus : K → ℝ)
    (dx : Measure K) (f : Charts K) (t : K) : Charts K := by
  classical
  exact
    (fun u v => (∫ x, if hx : x ≠ 0 then
        f.1 (Units.mk0 x hx) ((x * v - t ^ n) / (u : K)) * h (Units.mk0 x hx) (-u)
        else 0 ∂dx) / (modulus u : ℂ),
     fun u v => (∫ y, if hy : y ≠ 0 then
        f.2 ((u * y + t ^ n) / (v : K)) (Units.mk0 y hy) *
          h (Units.mk0 y hy) v * h (-1) v else 0 ∂dx) / (modulus v : ℂ))

/-- Definition 4.4. The outer Fourier integral uses the same self-dual measure. -/
def transform (n : ℕ) (ψ : K → ℂ) (h : Kˣ → Kˣ → ℂ) (modulus : K → ℝ)
    (dx : Measure K) (f : Charts K) : Charts K :=
  let c : ℂ := (Real.sqrt (modulus (n : K)))⁻¹
  let R := radon n h modulus dx f
  (fun u v => c * ∫ t, ψ t * (R t).1 u v ∂dx,
   fun u v => c * ∫ t, ψ t * (R t).2 u v ∂dx)

end Local

/-- The two chart values of the leading term, specified by punctured ray limits. -/
def IsLeadingTerm [TopologicalSpace K] (n : ℕ) (modulus : K → ℝ)
    (f g : Charts K) : Prop :=
  let atZero := comap (fun t : Kˣ => (t : K)) (𝓝 0)
  (∀ x y, Tendsto (fun t : Kˣ => (modulus t : ℂ) ^ (n - 1) *
      f.1 (t ^ n * x) ((t : K) ^ n * y)) atZero (𝓝 (g.1 x y))) ∧
  (∀ x y, Tendsto (fun t : Kˣ => (modulus t : ℂ) ^ (n - 1) *
      f.2 ((t : K) ^ n * x) (t ^ n * y)) atZero (𝓝 (g.2 x y)))

/-- The span model used in GroundTheory.Automorphic.RestrictedTensor.restrictedTensor. -/
def restrictedTensor {ι : Type*} {V : ι → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)] (basic : ∀ i, V i) :
    Submodule ℂ (⨂[ℂ] i, V i) :=
  Submodule.span ℂ (PiTensorProduct.tprod ℂ '' {x | ∀ᶠ i in cofinite, x i = basic i})

abbrev RationalPoint (F : Type*) [Field F] := {v : F × F // v ≠ 0}

section Adelic
variable {F ι : Type*} [Field F] {V W : ι → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

/-- A family preserving the reference vectors almost everywhere acts on the
restricted tensor product. In particular this applies to the local transforms. -/
def tensorMap (ξ : ∀ i, V i) (η : ∀ i, W i) (L : ∀ i, V i →ₗ[ℂ] W i)
    (h : ∀ᶠ i in cofinite, L i (ξ i) = η i) :
    restrictedTensor ξ →ₗ[ℂ] restrictedTensor η :=
  ((PiTensorProduct.map L).comp (restrictedTensor ξ).subtype).codRestrict _ (by
    intro f
    apply Submodule.mapsTo_span (f := PiTensorProduct.map L) _ f.property
    rintro _ ⟨x, hx, rfl⟩
    rw [PiTensorProduct.map_tprod]
    refine ⟨_, ?_, rfl⟩
    change ∀ᶠ i in cofinite, x i = ξ i at hx
    exact (hx.and h).mono fun i ⟨hi, hi'⟩ => (congrArg (L i) hi).trans hi')

/-- A family of surjective local maps induces a surjection of restricted tensor
products. When lifting a pure tensor one can choose the reference vector at
every place where it maps to the requested factor. -/
theorem tensorMap_surjective (ξ : ∀ i, V i) (η : ∀ i, W i) (L : ∀ i, V i →ₗ[ℂ] W i)
    (h : ∀ᶠ i in cofinite, L i (ξ i) = η i) (hs : ∀ i, Function.Surjective (L i)) :
    Function.Surjective (tensorMap ξ η L h) := by
  classical
  rintro ⟨y, hy⟩
  let T := tensorMap ξ η L h
  suffices pre : ∃ x, (T x).val = y by
    obtain ⟨x, hx⟩ := pre
    exact ⟨x, Subtype.ext hx⟩
  refine Submodule.span_induction (p := fun y _ => ∃ x, (T x).val = y) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨g, hg, rfl⟩
    let f (i : ι) := if L i (ξ i) = g i then ξ i else (hs i (g i)).choose
    have hfg (i : ι) : L i (f i) = g i := by
      dsimp only [f]
      split_ifs with hi
      · exact hi
      · exact (hs i (g i)).choose_spec
    have hf : ∀ᶠ i in cofinite, f i = ξ i := by
      filter_upwards [h, hg] with i hi hgi
      simp [f, hi.trans hgi.symm]
    refine ⟨⟨_, Submodule.subset_span ⟨f, hf, rfl⟩⟩, ?_⟩
    change PiTensorProduct.map L (PiTensorProduct.tprod ℂ f) = _
    rw [PiTensorProduct.map_tprod]
    exact congrArg (PiTensorProduct.tprod ℂ) (funext hfg)
  · exact ⟨0, by simp⟩
  · rintro _ _ _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x+y, by simp⟩
  · rintro c _ _ ⟨x, rfl⟩
    exact ⟨c • x, by simp⟩

end Adelic

end
end MetaplecticPoisson
