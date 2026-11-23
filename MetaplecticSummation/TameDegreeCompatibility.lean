import MetaplecticSummation.TamePowers
import MetaplecticSummation.ConductorMeasure

/-! Compatibility of tame Hilbert symbols when passing to a divisor of the cover degree. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField IsDedekindDomain
variable {F : Type} [Field F] [NumberField F] {n m : ℕ} [NeZero n] [NeZero m]
variable (p : HeightOneSpectrum (𝓞 F))
local notation "K" => p.adicCompletion F
local notation "O" => p.adicCompletionIntegers F
local notation "q" => p.asIdeal.absNorm

/-- On a uniformizer and a unit the degree-m symbol is the (n/m)-th power
of the degree-n symbol, as roots of unity in the number field. -/
theorem tame_uniformizer_change_degree (D : Datum F n) (d : Datum F m) (l : ℕ)
    (hn : n = m*l) (hp : Nat.Coprime q n) (π u : Kˣ)
    (hπ : ‖π.val‖ = (q : ℝ)⁻¹) (hu : ‖u.val‖ = 1) :
    (D.family (.inr p) π u).val ^ l = (d.family (.inr p) π u).val := by
  let z := D.family (.inr p) π u
  let w := d.family (.inr p) π u
  let U : O := ⟨u.val,(mem_localIntegers_iff p _).mpr hu.le⟩
  have hpm : Nat.Coprime q m := hp.coprime_dvd_right (hn ▸ dvd_mul_right m l)
  have red {k : ℕ} [NeZero k] (a : Datum F k) (hk : Nat.Coprime q k) :
      IsLocalRing.residue O (rootInteger p (a.family (.inr p) π u)) =
        (IsLocalRing.residue O U)^((q-1)/k) := by
    rw [← map_pow]
    exact (residue_eq_iff_norm_sub_lt p _ _).mpr (a.family_spec.tame_uniformizer p hk π u hπ hu)
  obtain ⟨r,hr⟩ := D.tame_degree_dvd p hp
  have exp : ((q-1)/n)*l = (q-1)/m := by
    rw [hr,Nat.mul_div_cancel_left _ (NeZero.pos n),hn,Nat.mul_assoc,Nat.mul_div_cancel_left _ (NeZero.pos m),Nat.mul_comm]
  have eqn : rootInteger p z ^ l = rootInteger p w := by
    apply d.tame_root_reduction_injective p hpm
    · rw [← pow_mul,Nat.mul_comm,← hn,rootInteger_pow]
    · exact rootInteger_pow p w
    · rw [map_pow,red D hp,← pow_mul,exp,red d hpm]
  apply Units.ext
  apply (diagonal F (.inr p)).injective
  rw [Units.val_pow_eq_pow_val,map_pow]
  exact congrArg Subtype.val eqn

/-- The tame change-of-degree identity extends to arbitrary valuation in the first
argument when the second argument is an integral unit. -/
theorem tame_change_degree_on_units (D : Datum F n) (d : Datum F m) (l : ℕ)
    (hn : n = m*l) (hp : Nat.Coprime q n) (a u : Kˣ) (hu : ‖u.val‖ = 1) :
    (D.family (.inr p) a u).val ^ l = (d.family (.inr p) a u).val := by
  obtain ⟨π,hπ⟩ := FinitePlace.exists_norm_uniformizer p
  obtain ⟨j,hj⟩ := norm_zpow_residue_card p a
  let b := a / π^(-j)
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm p)).ne'
  have hb : ‖b.val‖ = 1 := by
    simp [b,Units.val_zpow_eq_zpow_val,norm_zpow,hπ,hj,zpow_ne_zero _ hq]
  have decomp {k : ℕ} [NeZero k] (A : Datum F k) (hk : Nat.Coprime q k) :
      (A.family (.inr p) a u).val = (A.family (.inr p) π u).val ^ (-j) := by
    let H : Kˣ →* Mu F k := MonoidHom.mk' (fun t => A.family (.inr p) t u)
      (fun x y => A.family_spec.mul_left (.inr p) x y u)
    have one : H b = 1 := A.family_spec.tame_units p hk b u hb hu
    have h : H a = (H π)^(-j) := by
      calc
        H a = H (b * π^(-j)) := by rw [div_mul_cancel]
        _ = _ := by rw [map_mul,map_zpow,one,one_mul]
    exact congrArg Subtype.val h
  rw [decomp D hp,decomp d (hp.coprime_dvd_right (hn ▸ dvd_mul_right m l)),
    ← tame_uniformizer_change_degree p D d l hn hp π u hπ hu]
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]

end MetaplecticPoisson.Datum
