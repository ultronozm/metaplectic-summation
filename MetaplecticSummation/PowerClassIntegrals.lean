import MetaplecticSummation.PowerClassFourier
import MetaplecticSummation.LineMoments

/-! Class integrals of the axis values in the proof of Proposition B.4. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField MeasureTheory Set
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n) (v : Place F)
local notation "K" => LocalField F v
local notation "G" => PowerClass n v
local notation "dx" => selfDual F d.character v

private def classFiber (c : G) : Set K := Units.val '' {u : Kˣ | QuotientGroup.mk u = c}

private theorem classFiber_measurable (c : G) : MeasurableSet (classFiber v c) := by
  have he : Topology.IsOpenEmbedding (Units.val : Kˣ → K) :=
    (IsOpen.isOpenEmbedding_subtypeVal isOpen_compl_singleton).comp unitsHomeomorphNeZero.isOpenEmbedding
  exact (he.isOpenMap _ (open_powerClass v c)).measurableSet

private theorem mem_classFiber (c : G) (u : Kˣ) : u.val ∈ classFiber v c ↔ QuotientGroup.mk u = c :=
  ⟨fun ⟨a,ha,he⟩ => Units.val_injective he ▸ ha,fun h => ⟨u,h,rfl⟩⟩

/-- The local function β used to cancel the two power-class sums in Proposition B.4. -/
def axisClassIntegral (Φ : d.schwartz v) (c : G) : ℂ :=
  (n : ℂ) * ∫ y in classFiber v c, (if hy : y ≠ 0 then d.axis v Φ (Units.mk0 y hy) else 0) ∂dx

/-- Its finite Hilbert transform is the symbol-weighted additive integral
of the axis. The factor n from the class integrals cancels the counting normalization. -/
theorem powerClassTransform_axisClassIntegral (Φ : d.schwartz v) (a : Kˣ)
    (hi : Integrable (fun y : K => if hy : y ≠ 0 then d.axis v Φ (Units.mk0 y hy) else 0) dx) :
    d.powerClassTransform v (d.axisClassIntegral v Φ) (QuotientGroup.mk a) =
      ∫ y, (if hy : y ≠ 0 then d.symbol v (Units.mk0 y hy) a * d.axis v Φ (Units.mk0 y hy) else 0) ∂dx := by
  let := finite_power_classes (n := n) v
  letI := Fintype.ofFinite G
  let f (y : K) := if hy : y ≠ 0 then d.axis v Φ (Units.mk0 y hy) else 0
  let χ (c : G) : ℂ := d.localClassPairing v c (QuotientGroup.mk a)
  let g (c : G) := (classFiber v c).indicator (fun y => χ c * f y)
  have hg (c : G) : Integrable (g c) dx := (hi.const_mul (χ c)).indicator (classFiber_measurable v c)
  have term (c : G) : χ c * d.axisClassIntegral v Φ c = (n : ℂ) * ∫ y, g c y ∂dx := by
    rw [show (∫ y, g c y ∂dx) = _ from integral_indicator (classFiber_measurable v c),integral_const_mul]
    change χ c * ((n : ℂ) * _) = n * (χ c * _)
    ring
  rw [powerClassTransform,finsum_eq_sum_of_fintype]
  change (n : ℂ)⁻¹ * (∑ c : G, χ c * d.axisClassIntegral v Φ c) = _
  simp_rw [term]
  rw [← Finset.mul_sum,← mul_assoc,inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne n)),one_mul,
    ← integral_finsetSum _ (fun c _ => hg c)]
  apply integral_congr_ae
  filter_upwards with y
  by_cases hy : y = 0
  · subst y
    have he (c : G) : g c 0 = 0 := by
      apply indicator_of_notMem
      rintro ⟨u,_,hu⟩
      exact u.ne_zero hu
    simp [he]
  · let u := Units.mk0 y hy
    rw [Finset.sum_eq_single (QuotientGroup.mk u)]
    · change (classFiber v _).indicator _ u.val = _
      rw [indicator_of_mem ((mem_classFiber v _ u).mpr rfl)]
      simp only [χ,localClassPairing_mk,coe_unitPairing,f,dif_pos hy]
      rw [dif_pos u.ne_zero]
      rfl
    · intro c _ hne
      exact indicator_of_notMem (fun h => hne ((mem_classFiber v c u).mp h).symm) _
    · simp

end MetaplecticPoisson.Datum
