import MetaplecticSummation.PowerClassPairing
import ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassPowerLocalUnitQuotient.FinitePlacePowerIndex
import ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassPowerLocalUnitQuotient.ArchimedeanPowerIndex
import Mathlib.RingTheory.IntegralDomain

/-! Finite Fourier inversion for the Hilbert pairing of Appendix B. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open Classical NumberField GlobalClassFieldTheory.ClassFieldAxiom
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n) (v : Place F)
local notation "G" => PowerClass n v

theorem localClassPairing_skew (a b : G) :
    d.localClassPairing v a b = (d.localClassPairing v b a)⁻¹ := by
  induction a using QuotientGroup.induction_on with | _ a => _
  induction b using QuotientGroup.induction_on with | _ b => _
  apply eq_inv_of_mul_eq_one_left
  change d.embedding (d.family v a b) * d.embedding (d.family v b a) = 1
  rw [← map_mul,d.family_spec.skew,map_one]

/-- Orthogonality of the Hilbert characters, including at wild and infinite places. -/
theorem localClassPairing_sum (b : G) :
    (∑ᶠ a : G, (d.localClassPairing v a b : ℂ)) = if b = 1 then (Nat.card G : ℂ) else 0 := by
  letI := finite_power_classes (n := n) v
  letI := Fintype.ofFinite G
  rw [finsum_eq_sum_of_fintype]
  by_cases hb : b = 1
  · simp [hb,Nat.card_eq_fintype_card]
  · rw [if_neg hb]
    let χ : G →* ℂ := (Units.coeHom ℂ).comp ((d.localClassPairing v).flip b)
    apply sum_hom_units_eq_zero χ
    intro h
    apply hb
    apply d.localClassPairing_right_kernel
    intro a
    exact Units.ext (DFunLike.congr_fun h a)

/-- The paper's local transform, with counting measure divided by n. -/
def powerClassTransform (β : G → ℂ) (y : G) : ℂ :=
  (n : ℂ)⁻¹ * ∑ᶠ c : G, (d.localClassPairing v c y : ℂ) * β c

theorem powerClassTransform_representatives (β : G → ℂ) (y : G) :
    d.powerClassTransform v β y = (n : ℂ)⁻¹ * ∑ᶠ c : G, d.symbol v c.out y.out * β c := by
  unfold powerClassTransform
  congr 1
  apply finsum_congr
  intro c
  have eqn := d.localClassPairing_mk v c.out y.out
  have rep (a : G) : (QuotientGroup.mk a.out : G) = a := Quotient.out_eq a
  rw [rep,rep] at eqn
  exact congrArg (fun t : ℂˣ => (t : ℂ) * β c) eqn

/-- The number of local power classes times the normalized local modulus
of n is n squared, at every finite and infinite place. -/
theorem card_powerClass_mul_modulus (d : Datum F n) (v : Place F) :
    (Nat.card (PowerClass n v) : ℝ) * modulus F v (n : LocalField F v) = (n : ℝ)^2 := by
  let m : ℕ+ := ⟨n,NeZero.pos n⟩
  cases v with
  | inr p =>
    have hm : (primitiveRoots n F).Nonempty := ⟨d.root,(mem_primitiveRoots m.pos).mpr d.primitive⟩
    have hc : Nat.card (PowerClass n (.inr p)) = n * (n * _) :=
      card_finitePlace_nthPowerQuotient_eq_defect (K := F) m hm p
    rw [finitePlaceNthPowerDefect_eq_absNorm_maxPowDividing] at hc
    let I := p.maxPowDividing (Ideal.span {(n : 𝓞 F)})
    have he := NumberField.HeightOneSpectrum.embedding_mul_absNorm (K := F) p
      (x := (n : 𝓞 F)) (Nat.cast_ne_zero.mpr (NeZero.ne n))
    have he' : modulus F (.inr p) (n : LocalField F (.inr p)) * (I.absNorm : ℝ) = 1 := by
      change ‖(n : p.adicCompletion F)‖ * _ = 1
      simpa only [map_natCast] using he
    rw [hc,Nat.cast_mul,Nat.cast_mul]
    change ((n : ℝ) * (n * (I.absNorm : ℝ))) * _ = _
    linear_combination (n : ℝ)^2 * he'
  | inl w =>
    have hc : Nat.card (PowerClass n (.inl w)) = if w.IsReal ∧ Even n then 2 else 1 :=
      card_infinitePlace_nthPowerQuotient (K := F) m w
    change (Nat.card (PowerClass n (.inl w)) : ℝ) * ‖(n : w.Completion)‖^w.mult = _
    have he := (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
      (map_zero (InfinitePlace.Completion.extensionEmbedding w)) (n : w.Completion)
    rw [hc,show ‖(n : w.Completion)‖ = (n : ℝ) by simpa only [map_natCast,Complex.norm_natCast] using he.symm]
    by_cases hw : w.IsReal
    · have hdeg : n ≤ 2 := by
        by_contra! hn
        have hz := InfinitePlace.IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt hn d.primitive
        have pos : 0 < InfinitePlace.nrRealPlaces F := Fintype.card_pos_iff.mpr ⟨⟨w,hw⟩⟩
        omega
      rw [InfinitePlace.mult_isReal ⟨w,hw⟩]
      rcases (show n = 1 ∨ n = 2 by have := NeZero.pos n; omega) with hn | hn <;> rw [hn] <;> norm_num [hw]
    · simp [hw,InfinitePlace.mult_isComplex ⟨w,InfinitePlace.not_isReal_iff_isComplex.mp hw⟩]

theorem powerClassTransform_const_mul (k : ℂ) (β : G → ℂ) (z : G) :
    d.powerClassTransform v (fun c => k * β c) z = k * d.powerClassTransform v β z := by
  let := finite_power_classes (n := n) v
  letI := Fintype.ofFinite G
  simp only [powerClassTransform,finsum_eq_sum_of_fintype,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  ring

/-- Applying the skew-pairing transform twice gives the local cardinality
divided by the square of the covering degree, times the original function. -/
theorem powerClassTransform_square (β : G → ℂ) (z : G) :
    d.powerClassTransform v (d.powerClassTransform v β) z =
      (n : ℂ)⁻¹ ^ 2 * (Nat.card G : ℂ) * β z := by
  letI := finite_power_classes (n := n) v
  letI := Fintype.ofFinite G
  let B := d.localClassPairing v
  have kernel (c y : G) : (B y z : ℂ) * (B c y : ℂ) = (B y (z/c) : ℂ) := by
    rw [map_div, d.localClassPairing_skew v c y]
    rfl
  simp only [powerClassTransform,finsum_eq_sum_of_fintype]
  change _ * (∑ y : G, (B y z : ℂ) * (_ * ∑ c : G, (B c y : ℂ) * β c)) = _
  calc
    _ = (n : ℂ)⁻¹ ^ 2 * ∑ y : G, ∑ c : G, (B y (z/c) : ℂ) * β c := by
      simp only [← kernel, pow_two, Finset.mul_sum]
      ring_nf
    _ = (n : ℂ)⁻¹ ^ 2 * ∑ c : G, (∑ y : G, (B y (z/c) : ℂ)) * β c := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ = _ := by
      have H (c : G) : (∑ y : G, (B y (z/c) : ℂ)) = if z = c then (Nat.card G : ℂ) else 0 := by
        simpa only [finsum_eq_sum_of_fintype,div_eq_one] using d.localClassPairing_sum v (z/c)
      simp only [H,ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,if_true]
      ring

/-- The square of the counting-measure transform with the paper's
normalization contributes the inverse modulus of n. -/
theorem modulus_mul_powerClassTransform_square (β : G → ℂ) (z : G) :
    (modulus F v (n : LocalField F v) : ℂ) * d.powerClassTransform v (d.powerClassTransform v β) z = β z := by
  have hc : (Nat.card G : ℂ) * (modulus F v (n : LocalField F v) : ℂ) = (n : ℂ)^2 := by
    exact_mod_cast d.card_powerClass_mul_modulus v
  rw [d.powerClassTransform_square]
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  field_simp
  linear_combination β z * hc

/-- With self-dual measure the skew Hilbert Fourier transform is an involution. -/
theorem involutive_normalized_powerClassTransform :
    Function.Involutive (fun β : G → ℂ => fun z =>
      (Real.sqrt (modulus F v (n : LocalField F v)) : ℂ) * d.powerClassTransform v β z) := by
  let m := modulus F v (n : LocalField F v)
  have hm : 0 ≤ m := by cases v with
    | inl w => exact pow_nonneg (norm_nonneg _) _
    | inr p => exact norm_nonneg _
  have hsq : (Real.sqrt m : ℂ) * Real.sqrt m = (m : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt hm
  intro β
  funext z
  change (Real.sqrt m : ℂ) * d.powerClassTransform v (fun c => (Real.sqrt m : ℂ) * d.powerClassTransform v β c) z = _
  rw [d.powerClassTransform_const_mul,← mul_assoc,hsq]
  exact d.modulus_mul_powerClassTransform_square v β z

end MetaplecticPoisson.Datum
