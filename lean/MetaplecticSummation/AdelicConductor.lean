import MetaplecticSummation.AdelicAnnihilator
import MetaplecticSummation.LocalCharacterScaling

/-! The conductor at almost every finite place. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField Filter Set
open Classical
variable {F : Type} [Field F] [NumberField F]
local notation "A" => Adeles F
local notation "ι" => algebraMap F A

/-- At almost every finite place the annihilator of the local integers is
exactly the local integers. No choice of a standard global character is needed. -/
theorem eventually_unramified {n : ℕ} (d : Datum F n) :
    ∀ᶠ p : Prime F in cofinite, d.UnramifiedAt (.inr p) := by
  obtain ⟨C,hC,rep⟩ := AdeleLattice.exists_isCompact_forall_exists_sub_mem F
  let O := AdeleLattice.integralFiniteAdeles (𝓞 F) F
  let D : Set A := C ×ˢ (O : Set _)
  have hc : IsCompact D := hC.prod (AdeleLattice.isCompact_integralFiniteAdeles F)
  let S := {k : F | ∃ r ∈ D, ∀ z ∈ D, d.character.toChar ((ι k + r)*z) = 1}
  have hs : S.Finite := finite_annihilating_translates d.character hc rep
  have hi : ∀ᶠ p : Prime F in cofinite, ∀ k ∈ S, (ι k).2 p ∈ p.adicCompletionIntegers F :=
    hs.eventually_all.mpr (fun k _ => (ι k).2.2)
  filter_upwards [hi,eventually_trivial_on_integers d.character] with p hp ht
  intro x
  change p.adicCompletion F at x
  constructor
  · intro hx
    let a := singleAdele F (.inr p) x
    obtain ⟨k,hk⟩ := rep a
    have mem : k ∈ S := by
      refine ⟨a-ι k,hk,fun z hz => ?_⟩
      rw [show ι k + (a-ι k) = a by abel]
      rw [show a*z = _ from singleAdele_mul (.inr p) x z]
      apply Subtype.ext
      exact hx (z.2 p) ((Valued.toNormedField.norm_le_one_iff (x := z.2 p)).mpr (hz.2 p))
    have hb := Subring.add_mem (p.adicCompletionIntegers F).toSubring (hk.2 p) (hp k mem)
    have hval : a.2 p = x := component_single_self (.inr p) x
    change a.2 p - (ι k).2 p + (ι k).2 p ∈ p.adicCompletionIntegers F at hb
    rw [sub_add_cancel,hval] at hb
    exact (Valued.toNormedField.norm_le_one_iff (x := (x : p.adicCompletion F))).mpr hb
  · intro hx y hy
    exact ht _ ((norm_mul x y).le.trans (mul_le_one₀ hx (norm_nonneg _) hy))

end MetaplecticPoisson.Datum
