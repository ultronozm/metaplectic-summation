import MetaplecticSummation.FinitePlaceNorm
import MetaplecticSummation.Places
import MetaplecticSummation.PowerSubgroup

/-! Finiteness of the groups of local power classes in a number field. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n]

abbrev nontrivialArchNorm (w : InfinitePlace F) : NontriviallyNormedField w.Completion where
  non_trivial := by
    refine ⟨algebraMap F w.Completion (2 : F), ?_⟩
    have h := InfinitePlace.Completion.norm_coe w ((WithAbs.equiv w.1).symm (2 : F))
    change 1 < ‖algebraMap F w.Completion (2 : F)‖
    rw [show ‖algebraMap F w.Completion (2 : F)‖ = w (2 : F) from h]
    simpa only [← Nat.cast_ofNat (R := F) (n := 2), w.map_natCast] using (by norm_num : (1:ℝ) < (2:ℕ))

abbrev PowerClass (n : ℕ) (v : Place F) := (LocalField F v)ˣ ⧸ (powMonoidHom n :
  (LocalField F v)ˣ →* (LocalField F v)ˣ).range

def integralUnits (p : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) : Subgroup (LocalField F (.inr p))ˣ where
  carrier := {u | ‖(u : LocalField F (.inr p))‖ = 1}
  one_mem' := norm_one
  mul_mem' := by intro a b ha hb; change ‖(a : LocalField F (.inr p)) * b‖ = 1; rw [norm_mul, ha, hb, one_mul]
  inv_mem' := by
    intro a ha
    change ‖((a⁻¹ : (LocalField F (.inr p))ˣ) : LocalField F (.inr p))‖ = 1
    rw [Units.val_inv_eq_inv_val, norm_inv, ha, inv_one]

theorem finite_power_classes (v : Place F) : Finite (PowerClass n v) := by
  cases v with
  | inl w =>
    letI := nontrivialArchNorm w
    letI : ProperSpace w.Completion := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace _
    letI : CharZero w.Completion := charZero_of_injective_ringHom (algebraMap F w.Completion).injective
    exact finite_unit_power_quotient (K := w.Completion) n (Nat.cast_ne_zero.mpr (NeZero.ne n))
  | inr p =>
    letI : NontriviallyNormedField (p.adicCompletion F) := FinitePlace.nontriviallyNormedCompletion p
    letI : ProperSpace (p.adicCompletion F) := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace _
    letI : CharZero (p.adicCompletion F) := charZero_of_injective_ringHom (algebraMap F (p.adicCompletion F)).injective
    exact finite_unit_power_quotient (K := p.adicCompletion F) n (Nat.cast_ne_zero.mpr (NeZero.ne n))

end MetaplecticPoisson.Datum
