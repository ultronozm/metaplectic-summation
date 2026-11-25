import MetaplecticSummation.UnramifiedGauss
import MetaplecticSummation.Gauss
import MetaplecticSummation.FiniteBoundaryImage
import MetaplecticSummation.Inversion
import MetaplecticSummation.Jacquet.Convergence
import MetaplecticSummation.TateLocal
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField MeasureTheory
open scoped ComplexConjugate
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

def jacquetSpace (v : Place F) := Set.range (d.jacquet v)

open scoped ContDiff in
theorem testWeight_zero (v : Place F) : TestWeight v (0 : Weight v) := by
  refine ⟨HasCompactSupport.intro isCompact_empty (fun _ _ => rfl),?_⟩
  cases v with
  | inr p => exact IsLocallyConstant.const 0
  | inl w =>
    have smooth {L : Type} [NormedField L] [NormedAlgebra ℝ L] (e : w.Completion ≃+* L) :
        archSmooth e (0 : Weight (.inl w)) := by
      change ContDiffOn ℝ ∞ (fun x : L => if _h : e.symm x ≠ 0 then (0 : ℂ) else 0) {0}ᶜ
      simpa only [dite_eq_ite,ite_self] using
        (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : L => (0 : ℂ)) {0}ᶜ)
    dsimp only [TestWeight]
    split <;> exact smooth _

theorem dualWeight_zero (v : Place F) : d.dualWeight v (0 : Weight v) = 0 := by
  funext x
  simp [dualWeight,kernelIntegral,lineIntegral]

theorem jacquet_transform_descends (v : Place F) (Φ Ψ : d.schwartz v)
    (h : d.jacquet v Φ = d.jacquet v Ψ) :
    d.jacquet v (d.fourier v Φ) = d.jacquet v (d.fourier v Ψ) := by
  have hz : d.jacquet v (Φ-Ψ) = 0 := by rw [d.jacquet_sub,h,sub_self]
  have hd := d.jacquet_fourier_test v (Φ-Ψ) (hz ▸ testWeight_zero v)
  rw [map_sub,d.jacquet_sub,hz,d.dualWeight_zero] at hd
  exact sub_eq_zero.mp hd

/-- The induced transform W ↦ Wᵛ on the full image of the Jacquet integral. -/
def jacquetSpaceTransform (v : Place F) (W : d.jacquetSpace v) : d.jacquetSpace v :=
  ⟨_,Set.mem_range_self (d.fourier v W.property.choose)⟩

theorem jacquetSpaceTransform_apply (v : Place F) (Φ : d.schwartz v) :
    (d.jacquetSpaceTransform v ⟨d.jacquet v Φ,Set.mem_range_self Φ⟩).val = d.jacquet v (d.fourier v Φ) :=
  d.jacquet_transform_descends v _ _ (Set.mem_range_self (f := d.jacquet v) Φ).choose_spec

theorem jacquet_inversion (v : Place F) (Φ : d.schwartz v) (c : (LocalField F v)ˣ) :
    let e : (LocalField F v)ˣ := (-1) ^ (n+1)
    d.jacquet v (d.fourier v (d.fourier v Φ)) c = d.symbol v (-c) e * d.jacquet v Φ (e*c) := by
  let e : (LocalField F v)ˣ := (-1) ^ (n+1)
  have he : e*e = 1 := by rw [← mul_pow]; simp
  have hval : e.val*e.val = 1 := congrArg Units.val he
  have hm : modulus F v e.val = 1 := by
    cases v <;> simp [modulus,e,Units.val_pow_eq_pow_val]
  have hs : d.symbol v c e * d.symbol v (-1) e = d.symbol v (-c) e := by
    change ((d.unitPairing v c e).val) * ((d.unitPairing v (-1) e).val) = _
    rw [show -c = c * (-1) by simp, ← d.coe_unitPairing, map_mul]
    rfl
  let f (y : LocalField F v) := Φ.val.1 (e*c) (y/e.val) * d.character.localValue F v (-y/c.val)
  have ht := d.integral_local_mul v e f
  dsimp only at ht
  rw [hm,Complex.ofReal_one,div_one] at ht
  have hphase (y : LocalField F v) : -(e.val*y)/c.val = -y/(e*c).val := by
    rw [Units.val_mul]
    field_simp
    linear_combination -y * hval
  have eval (y : LocalField F v) : f (e.val*y) = Φ.val.1 (e*c) y *
      d.character.localValue F v (-y/(e*c).val) := by
    simp only [f,hphase,mul_div_cancel_left₀ _ e.ne_zero]
  simp_rw [eval] at ht
  change d.jacquet v (d.fourier v (d.fourier v Φ)) c = d.symbol v (-c) e * d.jacquet v Φ (e*c)
  unfold jacquet
  rw [d.schwartz_fourier_square v Φ]
  change (∫ y, (d.symbol v c e * d.symbol v (-1) e * Φ.val.1 (e*c) (y/e.val)) *
    d.character.localValue F v (-y/c.val) ∂_) = _
  rw [hs]
  simp_rw [mul_assoc (d.symbol v (-c) e)]
  rw [integral_const_mul]
  exact congrArg (d.symbol v (-c) e * ·) ht.symm

theorem jacquetSpaceTransform_square (v : Place F) (W : d.jacquetSpace v) (c : (LocalField F v)ˣ) :
    let e : (LocalField F v)ˣ := (-1)^(n+1)
    (d.jacquetSpaceTransform v (d.jacquetSpaceTransform v W)).val c = d.symbol v (-c) e * W.val (e*c) := by
  obtain ⟨W,Φ,rfl⟩ := W
  have ht : d.jacquetSpaceTransform v ⟨_,Set.mem_range_self Φ⟩ = ⟨_,Set.mem_range_self (d.fourier v Φ)⟩ :=
    Subtype.ext (d.jacquetSpaceTransform_apply v Φ)
  rw [ht,d.jacquetSpaceTransform_apply]
  exact d.jacquet_inversion v Φ c

theorem jacquetSpaceTransform_bijective (v : Place F) : Function.Bijective (d.jacquetSpaceTransform v) := by
  constructor
  · intro W V h
    let e : (LocalField F v)ˣ := (-1)^(n+1)
    apply Subtype.ext
    funext x
    let c := e⁻¹*x
    have he := congrArg (fun G => (d.jacquetSpaceTransform v G).val c) h
    rw [d.jacquetSpaceTransform_square,d.jacquetSpaceTransform_square] at he
    have eqn := mul_left_cancel₀ (d.unitPairing v (-c) e).ne_zero he
    simpa only [c,← mul_assoc,mul_inv_cancel,one_mul,e] using eqn
  · rintro ⟨W,Φ,rfl⟩
    obtain ⟨Ψ,rfl⟩ := (d.fourier_bijective_of_square v (d.schwartz_fourier_square v)).surjective Φ
    exact ⟨⟨_,Set.mem_range_self Ψ⟩,Subtype.ext (d.jacquetSpaceTransform_apply v Ψ)⟩

/-- Proposition 10.20, with both gamma factors specified by Tate's equation. -/
theorem mellin_dual (v : Place F) (W : Weight v) (hw : TestWeight v W) (β : (LocalField F v)ˣ)
    (support : ∀ x, W x ≠ 0 → ∃ u : (LocalField F v)ˣ, x = β * u ^ n)
    (ω : (LocalField F v)ˣ →* Circle) (hω : Continuous ω) (s : ℂ)
    (lo : -(1/(n : ℝ)) < s.re) (hi : s.re < 0) :
    let η : Weight v := fun x => (ω x : ℂ) * d.symbol v β x
    ∃ γ₁ γ₂ : ℂ, d.TateEquation v (fun x => ((ω x : ℂ)^n)⁻¹) (-(n : ℂ)*s) γ₁ ∧
      d.TateEquation v η (1+s) γ₂ ∧
      d.mellin v (d.dualWeight v W) (fun x => ω x) s =
        (Real.sqrt (modulus F v (n : LocalField F v)) : ℂ)⁻¹ * η (-1) * γ₁ * γ₂ *
          d.mellin v W (fun x => (ω x : ℂ)⁻¹) (-s) := by sorry

end MetaplecticPoisson.Datum
