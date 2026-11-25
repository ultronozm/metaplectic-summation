import MetaplecticSummation.Places
import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.NumberTheory.NumberField.ProductFormula

/-! Approximation and the finite set of places over the cover degree. -/

noncomputable section
namespace MetaplecticPoisson
open NumberField IsDedekindDomain Filter
open scoped Topology

namespace FinitePlace
variable {K : Type} [Field K] [NumberField K]

theorem adicAbv_lt_one_iff_mem (v : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) :
    NumberField.HeightOneSpectrum.adicAbv K v (algebraMap (𝓞 K) K x) < 1 ↔ x ∈ v.asIdeal := by
  rw [← FinitePlace.norm_embedding]
  exact FinitePlace.norm_lt_one_iff_mem K v x

theorem adicAbv_isNontrivial (v : HeightOneSpectrum (𝓞 K)) : (NumberField.HeightOneSpectrum.adicAbv K v).IsNontrivial := by
  obtain ⟨x, hxv, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  refine ⟨algebraMap (𝓞 K) K x, ?_, ?_⟩
  · simpa using hx0
  · exact ((adicAbv_lt_one_iff_mem v x).2 hxv).ne

theorem not_isEquiv_adicAbv {v v' : HeightOneSpectrum (𝓞 K)} (h : v ≠ v') :
    ¬ (NumberField.HeightOneSpectrum.adicAbv K v).IsEquiv (NumberField.HeightOneSpectrum.adicAbv K v') := by
  intro he
  have hle : ¬ v.asIdeal ≤ v'.asIdeal := fun hle ↦
    h (HeightOneSpectrum.ext (v.isMaximal.eq_of_le v'.isPrime.ne_top hle))
  obtain ⟨x, hxv, hxv'⟩ := Set.not_subset.1 hle
  have h1 := (adicAbv_lt_one_iff_mem v x).2 hxv
  rw [he.lt_one_iff] at h1
  exact hxv' ((adicAbv_lt_one_iff_mem v' x).1 h1)

theorem isometry_algebraMap_adicCompletion (v : HeightOneSpectrum (𝓞 K)) :
    Isometry ((algebraMap K (v.adicCompletion K)).comp
      (WithAbs.equiv (NumberField.HeightOneSpectrum.adicAbv K v)).toRingHom) := by
  refine AddMonoidHomClass.isometry_of_norm _ fun x ↦ ?_
  rw [WithAbs.norm_eq_apply_ofAbs, ← FinitePlace.norm_embedding]
  rfl

theorem denseRange_diagonal (S : Finset (HeightOneSpectrum (𝓞 K))) :
    DenseRange (fun x : K => fun p : S => diagonal K (.inr p.val) x) := by
  let A (p : S) := NumberField.HeightOneSpectrum.adicAbv K p.val
  let φ (p : S) := (algebraMap K (p.val.adicCompletion K)).comp (WithAbs.equiv (A p)).toRingHom
  have hc (p : S) : Continuous (φ p) := (isometry_algebraMap_adicCompletion p.val).continuous
  have hd (p : S) : DenseRange (φ p) := by
    have hd' := HeightOneSpectrum.denseRange_algebraMap (K := K) p.val
    unfold DenseRange at hd' ⊢
    convert hd' using 1
    change Set.range ((algebraMap K (p.val.adicCompletion K)) ∘ (WithAbs.equiv (A p))) = _
    exact (WithAbs.equiv (A p)).surjective.range_comp _
  have hf := AbsoluteValue.denseRange_algebraMap_pi (v := A) (fun p => adicAbv_isNontrivial p.val)
    (fun _ _ hp => not_isEquiv_adicAbv (fun he => hp (Subtype.ext he)))
  exact (DenseRange.piMap hd).comp hf (continuous_pi fun p => (hc p).comp (continuous_apply p))

/-- A finite set containing every finite place whose residue characteristic divides n. -/
theorem finite_places_over_degree (n : ℕ) [NeZero n] :
    Set.Finite {p : HeightOneSpectrum (𝓞 K) | (n : 𝓞 K) ∈ p.asIdeal} := by
  have h : Ideal.span {(n : 𝓞 K)} ≠ 0 := by simp [NeZero.ne n]
  simp only [← Ideal.dvd_span_singleton, Ideal.finite_factors h]

theorem tame_of_degree_not_mem (n : ℕ) (p : HeightOneSpectrum (𝓞 K)) (hp : (n : 𝓞 K) ∉ p.asIdeal) :
    p.asIdeal.absNorm.Coprime n := by
  letI := p.isMaximal
  obtain ⟨q, k, _, hq, hprime, hcard⟩ := Ideal.exists_prime_and_absNorm_eq_pow p.asIdeal
  rw [hcard]
  apply Nat.Coprime.pow_left
  apply hprime.coprime_iff_not_dvd.mpr
  rintro ⟨r, rfl⟩
  exact hp (by simpa [Nat.cast_mul] using p.asIdeal.mul_mem_right (r : 𝓞 K) hq)

end FinitePlace
end MetaplecticPoisson
