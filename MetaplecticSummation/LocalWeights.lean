import MetaplecticSummation.UnramifiedGauss
import MetaplecticSummation.Gauss
import MetaplecticSummation.Inversion
import MetaplecticSummation.Jacquet.Convergence
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

def mellin (v : Place F) (W ω : Weight v) (s : ℂ) :=
  d.lineIntegral v fun x => W x * ω x * (modulus F v x : ℂ) ^ s

/-- Tate's normalization on the open strip. Smooth compact tests supported
away from zero suffice to determine the scalar at each point of the strip. -/
def TateEquation (v : Place F) (ω : Weight v) (s γ : ℂ) : Prop :=
  ∀ g : Weight v, TestWeight v g →
    let ĝ : Weight v := fun y => d.lineIntegral v fun x =>
      (modulus F v x : ℂ) * g x * d.character.localValue F v ((x : LocalField F v) * y)
    d.mellin v ĝ (fun x => (ω x)⁻¹) (1-s) = γ * d.mellin v g ω s

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

def powerAverage (v : Place F) (f : Charts (LocalField F v)) : Charts (LocalField F v) :=
  let avg := fun g : Weight v => d.lineIntegral v fun x =>
    if ∃ u : (LocalField F v)ˣ, x = u^n then (modulus F v x ^ (1+1/(n : ℝ)) : ℝ) * g x else 0
  (fun x y => avg fun a => (dilateCharts a f).1 x y,
   fun x y => avg fun a => (dilateCharts a f).2 x y)

/-- The X-chart of the power average of a Jacquet lift, in terms of the weighted
moment on the power class of its first coordinate (equation `eq:lift-average`). -/
theorem powerAverage_jacquetLift (v : Place F) (W : Weight v) (β : LocalField F v → ℂ)
    (x : (LocalField F v)ˣ) (y : LocalField F v) :
    (d.powerAverage v (d.jacquetLift v W β)).1 x y =
      β (y / x.val) / ((modulus F v x.val ^ (1 + 1 / (n : ℝ)) : ℝ) : ℂ) *
        d.lineIntegral v (fun t =>
          if (QuotientGroup.mk t : PowerClass n v) = QuotientGroup.mk x then
            W t * ((modulus F v t.val ^ (1 / (n : ℝ)) : ℝ) : ℂ) else 0) := by
  let m (u : (LocalField F v)ˣ) := modulus F v u.val
  have pos (u : (LocalField F v)ˣ) : 0 < m u := by
    cases v <;> simp [m,modulus,norm_pos_iff,u.ne_zero,pow_pos (norm_pos_iff.mpr u.ne_zero)]
  let s := 1 / (n : ℝ)
  let g (t : (LocalField F v)ˣ) : ℂ :=
    if (QuotientGroup.mk t : PowerClass n v) = QuotientGroup.mk x then W t * (m t ^ s : ℝ) else 0
  let b := β (y / x.val) / ((m x ^ (1 + s) : ℝ) : ℂ)
  unfold powerAverage
  dsimp only
  change _ = b * d.lineIntegral v g
  rw [← d.lineIntegral_mul v x g,← d.lineIntegral_const_mul]
  congr 1
  funext a
  have coset : (QuotientGroup.mk (x*a) : PowerClass n v) = QuotientGroup.mk x ↔
      ∃ u : (LocalField F v)ˣ, a = u^n := by
    rw [QuotientGroup.eq_iff_div_mem,mul_comm x a,mul_div_cancel_right]
    exact ⟨fun ⟨u,hu⟩ => ⟨u,hu.symm⟩,fun ⟨u,hu⟩ => ⟨u,hu.symm⟩⟩
  change (if ∃ u : (LocalField F v)ˣ, a = u^n then
    ((m a ^ (1+s) : ℝ) : ℂ) * jacquetLiftX v W β (a*x) (a.val*y) else 0) = b * g (x*a)
  simp only [g,coset]
  split_ifs
  · have hm : m (a*x) = m a * m x := by cases v <;> simp [m,modulus,norm_mul,mul_pow]
    have ratio : a.val*y / (a*x).val = y / x.val := by rw [Units.val_mul]; field_simp
    rw [jacquetLiftX,ratio,mul_comm x a]
    change ((m a ^ (1+s) : ℝ) : ℂ) * ((m (a*x) : ℂ)⁻¹ * W (a*x) * β (y/x.val)) =
      β (y/x.val) / ((m x ^ (1+s) : ℝ) : ℂ) * (W (a*x) * ((m (a*x)^s : ℝ) : ℂ))
    rw [hm,Real.mul_rpow (pos a).le (pos x).le,Real.rpow_add (pos a),Real.rpow_add (pos x)]
    simp only [Real.rpow_one,Complex.ofReal_mul]
    field_simp [Complex.ofReal_ne_zero.mpr (pos a).ne', Complex.ofReal_ne_zero.mpr (pos x).ne',
      Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (pos x) s).ne']
  · exact (mul_zero _).symm

theorem powerAverage_glues (v : Place F) {f : Charts (LocalField F v)} (hf : Glues (d.symbol v) f) :
    Glues (d.symbol v) (d.powerAverage v f) := by
  intro x y
  unfold powerAverage
  dsimp only
  rw [← d.lineIntegral_const_mul]
  congr 1
  funext a
  split_ifs with ha
  · obtain ⟨u,rfl⟩ := ha
    rw [d.dilateCharts_glues v u hf x y]
    ring
  · rw [mul_zero]

/-- Vanishing of all the power-class moments kills the average in both charts. -/
theorem powerAverage_jacquetLift_eq_zero (v : Place F) (W : Weight v) (β : LocalField F v → ℂ)
    (h : ∀ c : PowerClass n v, d.lineIntegral v (fun t =>
      if (QuotientGroup.mk t : PowerClass n v) = c then
        W t * ((modulus F v t.val ^ (1 / (n : ℝ)) : ℝ) : ℂ) else 0) = 0) :
    d.powerAverage v (d.jacquetLift v W β) = 0 := by
  let f := d.jacquetLift v W β
  have hx (x : (LocalField F v)ˣ) (y : LocalField F v) : (d.powerAverage v f).1 x y = 0 := by
    dsimp only [f]
    rw [d.powerAverage_jacquetLift,h,mul_zero]
  refine Prod.ext (funext fun x => funext fun y => hx x y) (funext fun x => funext fun y => ?_)
  by_cases hn : x = 0
  · subst x
    simp [powerAverage,dilateCharts,jacquetLift,lineIntegral]
  · let x' := Units.mk0 x hn
    have eqn := d.powerAverage_glues v (d.jacquetLift_glues v W β) x' y
    rw [hx] at eqn
    exact (mul_eq_zero.mp eqn.symm).resolve_left (d.unitPairing v x' y).ne_zero

def intertwiner (v : Place F) (f : Charts (LocalField F v)) :=
  radon n (d.symbol v) (modulus F v) (selfDual F d.character v) f 1

theorem leading_fourier_test (v : Place F) (Φ : d.schwartz v) (h : Φ.val ∈ d.testSet v) :
    d.leading v (d.fourier v Φ) =
      ((n : ℂ) / ((modulus F v (n : LocalField F v) ^ (3/2 : ℝ) : ℝ) : ℂ)) •
        d.intertwiner v (d.powerAverage v Φ.val) := by sorry

theorem finite_boundary_image (p : Prime F) (g : Charts (LocalField F (.inr p))) :
    let v : Place F := .inr p
    g ∈ LinearMap.range (d.leading v) ↔ ∃ f : Charts (LocalField F v),
      Glues (d.symbol v) f ∧ IsLocallyConstant (fun z : (LocalField F v)ˣ × LocalField F v => f.1 z.1 z.2) ∧
      IsLocallyConstant (fun z : LocalField F v × (LocalField F v)ˣ => f.2 z.1 z.2) ∧
      (∀ u : (LocalField F v)ˣ, dilateCharts (u^n) f =
        ((modulus F v (u^n : (LocalField F v)ˣ) ^ (-1-1/(n : ℝ)) : ℝ) : ℂ) • f) ∧
      g = d.intertwiner v f := by sorry

end MetaplecticPoisson.Datum
