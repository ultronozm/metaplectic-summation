import MetaplecticSummation.LocalSymbols
import MetaplecticSummation.LineMeasures
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! The Steinberg relation and normalization of the measures at infinite places. -/

noncomputable section
namespace MetaplecticPoisson
open NumberField MeasureTheory MeasureTheory.Measure Metric
open scoped NNReal Pointwise

/-- Identify the Haar modulus by measuring balls after an isometric ring equivalence
with a finite-dimensional real normed field. -/
private theorem arch_haarChar {K L : Type*} [NormedField K] [LocallyCompactSpace K]
    [NormedField L] [NormedAlgebra ℝ L]
    [FiniteDimensional ℝ L] [MeasurableSpace L] [BorelSpace L]
    (e : K ≃+* L) (he : Isometry e) (a : Kˣ) :
    distribHaarChar K a = ‖(a : K)‖₊ ^ Module.finrank ℝ L := by
  letI := borel K
  letI : BorelSpace K := ⟨rfl⟩
  let μ := (addHaar : Measure K)
  let ν := μ.map e
  let i : K ≃ᵢ L := ⟨e.toEquiv, he⟩
  letI : ν.IsAddHaarMeasure := e.toAddEquiv.isAddHaarMeasure_map μ he.continuous i.symm.continuous
  have balls (r : ℝ) : ν (ball 0 r) = μ (ball 0 r) := by
    rw [Measure.map_apply (μ := μ) he.continuous.measurable isOpen_ball.measurableSet]
    simpa only [map_zero] using congrArg μ (he.preimage_ball 0 r)
  have hpos : μ (ball 0 1) ≠ 0 := (isOpen_ball.measure_pos μ (nonempty_ball.mpr zero_lt_one)).ne'
  have hfin : μ (ball 0 1) ≠ ⊤ := by rw [← balls]; exact measure_ball_ne_top
  apply distribHaarChar_eq_of_measure_smul_eq_mul hpos hfin
  change μ ((a : K) • ball (0 : K) 1) = _
  rw [_root_.smul_ball a.ne_zero, smul_zero, mul_one, ← balls, ← balls,
    addHaar_ball_of_pos ν _ (norm_pos_iff.mpr a.ne_zero)]
  simp [enorm]

namespace Datum
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

private theorem unit_pow_of_field_pow {K L : Type*} [Field K] [Field L] (e : K ≃+* L) (a : Kˣ)
    {z : L} (hz : z ^ n = e (a : K)) : ∃ u : Kˣ, u ^ n = a := by
  have hz₀ : z ≠ 0 := by
    intro h
    exact (e.injective.ne a.ne_zero) (by simpa [h, zero_pow (NeZero.ne n)] using hz.symm)
  refine ⟨Units.mk0 (e.symm z) (by simpa using hz₀), Units.ext (e.injective ?_)⟩
  simpa using hz

/-- At an infinite place at least one of a pair summing to one is an n-th power:
over the reals at least one is positive, and over the complex numbers every unit is a power. -/
theorem arch_steinberg (w : InfinitePlace F) (a b : (LocalField F (.inl w))ˣ)
    (hab : (a : LocalField F (.inl w)) + b = 1) : d.unitPairing (.inl w) a b = 1 := by
  suffices h : (∃ u, u ^ n = a) ∨ (∃ u, u ^ n = b) by
    rcases h with ⟨u, rfl⟩ | ⟨u, rfl⟩
    · rw [map_pow, MonoidHom.pow_apply, d.unitPairing_pow]
    · rw [map_pow, d.unitPairing_pow]
  by_cases hw : w.IsReal
  · let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
    have h : e a.val + e b.val = 1 := by
      calc
        _ = e (a.val + b.val) := (e.map_add _ _).symm
        _ = e 1 := congrArg e hab
        _ = 1 := e.map_one
    by_cases ha : 0 ≤ e a.val
    · exact Or.inl (unit_pow_of_field_pow e a (Real.rpow_inv_natCast_pow ha (NeZero.ne n)))
    · have hb : 0 ≤ e b.val := by linarith
      exact Or.inr (unit_pow_of_field_pow e b (Real.rpow_inv_natCast_pow hb (NeZero.ne n)))
  · let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex (InfinitePlace.not_isReal_iff_isComplex.mp hw)
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (e a.val) (NeZero.pos n)
    exact Or.inl (unit_pow_of_field_pow e a hz)

/-- The Haar modulus at an infinite place is the usual norm to the local degree. -/
theorem arch_modulus (w : InfinitePlace F) (u : w.Completionˣ) :
    modulus F (.inl w) u.val = (distribHaarChar w.Completion u : ℝ) := by
  change ‖u.val‖ ^ w.mult = _
  by_cases hw : w.IsReal
  · have h := arch_haarChar (InfinitePlace.Completion.ringEquivRealOfIsReal hw)
      (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw) u
    rw [h, InfinitePlace.mult_isReal ⟨w, hw⟩]
    simp
  · have hw' := InfinitePlace.not_isReal_iff_isComplex.mp hw
    have h := arch_haarChar (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw')
      (InfinitePlace.Completion.isometry_extensionEmbedding w) u
    rw [h, InfinitePlace.mult_isComplex ⟨w, hw'⟩]
    simp

abbrev archNontriviallyNormedCompletion (w : InfinitePlace F) : NontriviallyNormedField (LocalField F (.inl w)) :=
    { (inferInstance : NormedField (LocalField F (.inl w))) with
      non_trivial := ⟨2, by
        change 1 < ‖(2 : w.Completion)‖
        rw [← (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
          (map_zero _) (2 : w.Completion), map_ofNat]
        norm_num⟩ }

/-- Lemma 4.2(ii) with the paper's symbol and measures at every infinite place. -/
theorem arch_radon_glues (w : InfinitePlace F) {f : Charts (LocalField F (.inl w))}
    (hf : Glues (d.symbol (.inl w)) f) (t : LocalField F (.inl w)) :
    Glues (d.symbol (.inl w)) (radon n (d.symbol (.inl w)) (modulus F (.inl w))
      (selfDual F d.character (.inl w)) f t) := by
  let dx := selfDual F d.character (.inl w)
  letI : LocallyCompactSpace (LocalField F (.inl w)) := inferInstanceAs (LocallyCompactSpace w.Completion)
  letI : dx.IsAddHaarMeasure := (existsUnique_selfDual F d.character (.inl w)).exists.choose_spec.1
  letI : SecondCountableTopology (LocalField F (.inl w)) :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  letI := archNontriviallyNormedCompletion w
  exact (d.lineSymbol (.inl w) (d.arch_steinberg w)).radon_glues dx (NeZero.ne n) _
    (arch_modulus w) hf t

theorem arch_transform_glues (w : InfinitePlace F) {f : Charts (LocalField F (.inl w))}
    (hf : Glues (d.symbol (.inl w)) f) :
    Glues (d.symbol (.inl w)) (d.integralTransform (.inl w) f) :=
  transform_glues_of_radon_glues _ _ _ _ _ _ (d.arch_radon_glues w hf)

end Datum
end MetaplecticPoisson
