import MetaplecticSummation.Schwartz.Local
import MetaplecticSummation.Dilations
import MetaplecticSummation.FiniteGerms

/-! The local modification used to construct the boundary functional in Appendix B. -/

noncomputable section
namespace MetaplecticPoisson.Datum
open Filter NumberField IsDedekindDomain
open scoped Topology
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)
variable (p : HeightOneSpectrum (𝓞 F))
local notation "v" => (Sum.inr p : Place F)
local notation "K" => LocalField F v
local notation "q" => (p.asIdeal.absNorm : ℂ)

def finiteDilation (a : Kˣ) : d.schwartz v →ₗ[ℂ] d.schwartz v where
  toFun f := ⟨dilateCharts (a^n) f.val,d.finite_dilate_schwartz p a f.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem leading_dilate (a : Kˣ) (f : d.schwartz v) :
    d.leading v (d.finiteDilation p a f) = (‖a.val‖ : ℂ)^(-(n-1 : ℕ) : ℤ) • d.leading v f := by
  letI : NontriviallyNormedField K := FinitePlace.nontriviallyNormedCompletion p
  letI : NeBot (comap (fun u : Kˣ => u.val) (𝓝 0)) := units_neBot_at_zero
  let g := d.leading v f
  have h : d.leading v (d.finiteDilation p a f) = dilateCharts (a^n) g := by
    apply (d.leading_spec _ _).unique
    constructor
    · intro x y
      simpa only [finiteDilation,LinearMap.coe_mk,AddHom.coe_mk,dilateCharts,Units.val_pow_eq_pow_val,
        mul_left_comm (a^n),mul_left_comm (a.val^n)] using (d.leading_spec v f).1 (a^n*x) (a.val^n*y)
    · intro x y
      simpa only [finiteDilation,LinearMap.coe_mk,AddHom.coe_mk,dilateCharts,Units.val_pow_eq_pow_val,
        mul_left_comm (a^n),mul_left_comm (a.val^n)] using (d.leading_spec v f).2 (a.val^n*x) (a^n*y)
  rw [h,zpow_neg,zpow_natCast]
  have hs := d.finite_leading_properties p f
  have ha : (‖a.val‖ : ℂ)^(n-1) ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr a.ne_zero))
  apply Prod.ext
  · exact funext fun x => funext fun y => (eq_inv_mul_iff_mul_eq₀ ha).mpr (hs.1.2 x y a)
  · exact funext fun x => funext fun y => (eq_inv_mul_iff_mul_eq₀ ha).mpr (hs.2.2 x y a)

private theorem fourier_dilate (a : Kˣ) (f : d.schwartz v) :
    d.fourier v (d.finiteDilation p a f) = ((‖a.val‖ : ℂ)^(2*n))⁻¹ • d.finiteDilation p a⁻¹ (d.fourier v f) := by
  apply Subtype.ext
  rw [d.fourier_apply]
  change d.integralTransform v (dilateCharts (a^n) f.val) = _ • dilateCharts (a⁻¹^n) (d.fourier v f).val
  rw [d.integralTransform_dilateCharts,d.fourier_apply,inv_pow]
  change ((‖(a^n).val‖ : ℂ)^2)⁻¹ • _ = _
  rw [Units.val_pow_eq_pow_val,norm_pow,Complex.ofReal_pow,← pow_mul,Nat.mul_comm n 2]

/-- For a uniformizer π this is the operator Q on the local factor in the proof
of Theorem 9.1. -/
def boundaryModification (π : Kˣ) : d.schwartz v →ₗ[ℂ] d.schwartz v :=
  (q^(n+1) - q^(n-1))⁻¹ • (q^(n+1) • LinearMap.id - d.finiteDilation p π)

/-- Equation (B.8). The modification preserves the leading term and kills the leading term
of the Fourier transform. -/
theorem boundaryModification_spec (π : Kˣ) (hπ : ‖π.val‖ = (p.asIdeal.absNorm : ℝ)⁻¹)
    (f : d.schwartz v) :
    d.leading v (d.boundaryModification p π f) = d.leading v f ∧
      d.leading v (d.fourier v (d.boundaryModification p π f)) = 0 := by
  have h₀ : q ≠ 0 := by exact_mod_cast (Nat.zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm p)).ne'
  have hn := NeZero.pos n
  have he : q^(n+1)-q^(n-1) ≠ 0 := by
    rw [sub_ne_zero]
    exact_mod_cast (pow_lt_pow_right₀ (NumberField.HeightOneSpectrum.one_lt_absNorm p) (by omega : n-1 < n+1)).ne'
  have hL := d.leading_dilate p π f
  have hF := d.fourier_dilate p π f
  have hLF := d.leading_dilate p π⁻¹ (d.fourier v f)
  simp only [hπ,Complex.ofReal_inv,Complex.ofReal_natCast,zpow_neg,zpow_natCast,inv_pow,inv_inv] at hL hF
  simp only [Units.val_inv_eq_inv_val,norm_inv,hπ,inv_inv,Complex.ofReal_natCast,zpow_neg,zpow_natCast] at hLF
  simp only [boundaryModification,LinearMap.smul_apply,LinearMap.sub_apply,LinearMap.id_apply,map_smul,map_sub,
    hL,hF,hLF,smul_smul]
  constructor
  · rw [← sub_smul,smul_smul,inv_mul_cancel₀ he,one_smul]
  · have hcoeff : q^(2*n) * (q^(n-1))⁻¹ = q^(n+1) := by
      rw [← div_eq_mul_inv,div_eq_iff (pow_ne_zero _ h₀),← pow_add]
      congr 1
      omega
    rw [hcoeff,sub_self,smul_zero]

end MetaplecticPoisson.Datum
