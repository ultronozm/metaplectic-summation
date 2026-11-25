import CompletionTame
import MetaplecticSummation.PowerSubgroup
import MetaplecticSummation.FinitePlaceNorm

noncomputable section
open NumberField IsDedekindDomain MetaplecticPoisson ClassFieldTheory Filter Set
open scoped Topology
namespace MetaplecticBridge

variable {F : Type} [Field F] [NumberField F] (n : ℕ+) {ζ : F} (hζ : IsPrimitiveRoot ζ (n : ℕ))
variable (p : HeightOneSpectrum (𝓞 F))
local notation "D" => IsDedekindDomain.HeightOneSpectrum.adicCompletion F p

private def onClasses : PowerClassGroup D n →* PowerClassGroup D n →* Mu F (n : ℕ) := by
  letI : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  let hm : (primitiveRoots (n : ℕ) F).Nonempty := ⟨ζ,(mem_primitiveRoots n.pos).2 hζ⟩
  let e := rootsOfUnityEquivOfPrimitiveRoots (algebraMap F D).injective hm
  exact (MonoidHom.compHom (M := PowerClassGroup D n) (e.symm.toMonoidHom.comp invMonoidHom)).comp
    (finitePlaceAdicHilbertPairingFamily F n hm p)

private theorem finiteValue_classes (a b : Dˣ) : finiteValue n hζ p a b =
    onClasses n hζ p (powerClass D n a) (powerClass D n b) := rfl

theorem finiteValue_mul_left (a b c : Dˣ) :
    finiteValue n hζ p (a*b) c = finiteValue n hζ p a c * finiteValue n hζ p b c := by
  simp only [finiteValue_classes,map_mul,MonoidHom.mul_apply]

theorem finiteValue_mul_right (a b c : Dˣ) :
    finiteValue n hζ p a (b*c) = finiteValue n hζ p a b * finiteValue n hζ p a c := by
  simp only [finiteValue_classes,map_mul]

theorem finiteValue_skew (a b : Dˣ) : finiteValue n hζ p a b * finiteValue n hζ p b a = 1 := by
  let hm : (primitiveRoots (n : ℕ) F).Nonempty := ⟨ζ,(mem_primitiveRoots n.pos).2 hζ⟩
  have hs := (finitePlaceAdicHilbertPairingFamily_isLocallyHilbert F n hm p).2.1
    (powerClass D n a) (powerClass D n b)
  letI : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  let e := rootsOfUnityEquivOfPrimitiveRoots (algebraMap F D).injective hm
  let B := finitePlaceAdicHilbertPairingFamily F n hm p
  change e.symm ((B (powerClass D n a) (powerClass D n b))⁻¹) *
    e.symm ((B (powerClass D n b) (powerClass D n a))⁻¹) = 1
  rw [hs,inv_inv,map_inv,mul_inv_cancel]

private theorem powerClass_locallyConstant : IsLocallyConstant (powerClass D n) := by
  letI : NontriviallyNormedField D := MetaplecticPoisson.FinitePlace.nontriviallyNormedCompletion p
  have hi := isOpen_unit_powers (K := D) (n : ℕ) (Nat.cast_ne_zero.mpr n.ne_zero)
  have near : ∀ᶠ y : Dˣ in 𝓝 1, powerClass D n y = 1 := by
    filter_upwards [hi.mem_nhds (show (1 : Dˣ) ∈ range (fun x : Dˣ => x^(n : ℕ)) from ⟨1,one_pow _⟩)] with y hy
    exact (powerClass_eq_one_iff D n y).mpr hy
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro x
  have ct : Tendsto (fun y : Dˣ => y/x) (𝓝 x) (𝓝 1) := by
    have h : Continuous (fun y : Dˣ => y / x) := continuous_id.div' continuous_const
    simpa only [div_self'] using h.tendsto x
  filter_upwards [ct.eventually near] with y hy
  exact div_eq_one.mp ((map_div (powerClass D n) y x).symm.trans hy)

theorem finiteValue_continuous :
    Continuous (fun z : Dˣ × Dˣ => algebraMap F D ((finiteValue n hζ p z.1 z.2).val : F)) := by
  apply IsLocallyConstant.continuous
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro z
  have h := powerClass_locallyConstant n p
  filter_upwards [continuous_fst.continuousAt.eventually (h.eventually_eq z.1),
    continuous_snd.continuousAt.eventually (h.eventually_eq z.2)] with y hy hy'
  unfold finiteValue
  rw [hy,hy']

end MetaplecticBridge
