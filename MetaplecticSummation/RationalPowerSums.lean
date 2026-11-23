import MetaplecticSummation.PowerClassPairing
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-! Regrouping absolutely convergent rational sums in Proposition B.4. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

include d in
private theorem tsum_on_powers (g : (powMonoidHom n : Fˣ →* Fˣ).range → ℂ) (hg : Summable g) :
    (∑' u : Fˣ, g ((powMonoidHom n : Fˣ →* Fˣ).rangeRestrict u)) = (n : ℂ) * ∑' b, g b := by
  let P := (powMonoidHom n : Fˣ →* Fˣ).rangeRestrict
  have hk : P.ker = rootsOfUnity n F := by
    ext x
    change P x = 1 ↔ x^n = 1
    exact Subtype.ext_iff
  let e := (Equiv.sigmaFiberEquiv P).symm.trans ((Equiv.sigmaCongrRight (fun b =>
    MonoidHom.fiberEquivKerOfSurjective (MonoidHom.rangeRestrict_surjective _) b)).trans
      (Equiv.sigmaEquivProd _ P.ker))
  have hfirst (x : Fˣ) : (e x).1 = P x := rfl
  letI : Finite P.ker := hk ▸ inferInstanceAs (Finite (rootsOfUnity n F))
  letI := Fintype.ofFinite P.ker
  have card : Fintype.card P.ker = n := by
    rw [← Nat.card_eq_fintype_card,hk]
    exact d.primitive.card_rootsOfUnity
  let one := fun _ : P.ker => (1:ℂ)
  have h1 : (∑' z, one z) = (n:ℂ) := by simp [one,tsum_fintype,card]
  have eqn := tsum_mul_tsum_of_summable_norm hg.norm ((hasSum_fintype (fun k => ‖one k‖)).summable)
  rw [h1,mul_comm] at eqn
  calc
    _ = ∑' u, g (e u).1 * one (e u).2 := tsum_congr fun u => by simp [one,hfirst,P]
    _ = _ := (e.tsum_eq (fun z => g z.1 * one z.2)).trans eqn.symm

include d in
/-- Summing a function on rational units over all power classes and all power
parameters counts each unit exactly n times, for any system of representatives. -/
theorem hasSum_powerClass_representatives (f : Fˣ → ℂ) (hf : Summable f)
    (e : GlobalClass n F ≃ GlobalClass n F) (r : GlobalClass n F → Fˣ)
    (hr : ∀ c, QuotientGroup.mk (r c) = e c) :
    HasSum (fun c => ∑' t : Fˣ, f (r c * t^n)) ((n:ℂ) * ∑' x, f x) := by
  let H := (powMonoidHom n : Fˣ →* Fˣ).range
  let Q : Fˣ →* GlobalClass n F := QuotientGroup.mk' H
  let k (x : Fˣ) := e.symm (Q x)
  have hsum := (hf.hasSum.tsum_fiberwise k).mul_left (n:ℂ)
  apply hsum.congr_fun
  intro c
  let E : H ≃ k ⁻¹' {c} := {
    toFun := fun b => ⟨r c * b.val, by
      change e.symm (Q (r c * b.val)) = c
      rw [map_mul,show Q b.val = 1 from (QuotientGroup.eq_one_iff _).mpr b.2]
      exact e.symm_apply_eq.mpr ((mul_one (Q (r c))).trans (hr c))⟩
    invFun := fun x => ⟨x.val / r c, by
      apply (QuotientGroup.eq_one_iff _).mp
      change Q (x.val / r c) = 1
      rw [map_div]
      apply div_eq_one.mpr
      exact (e.symm_apply_eq.mp x.2).trans (hr c).symm⟩
    left_inv := fun b => Subtype.ext (mul_div_cancel_left _ _)
    right_inv := fun x => Subtype.ext (mul_div_cancel _ _) }
  let g (b : H) := f (E b).val
  have hg : Summable g := (E.summable_iff).mpr (hf.subtype _)
  exact (d.tsum_on_powers g hg).trans (congrArg ((n:ℂ) * ·) (E.tsum_eq (fun x => f x.val)))

end MetaplecticPoisson.Datum
