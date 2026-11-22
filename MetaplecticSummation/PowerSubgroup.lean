import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv

/-! Openness of the subgroup of n-th powers (§2(e)). -/

namespace MetaplecticPoisson
open Filter Set
open scoped Topology
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]

/-- The nonzero n-th powers form an open subset of the field, also in positive
characteristic whenever the characteristic does not divide n. -/
theorem isOpen_nonzero_powers (n : ℕ) (hn : (n : K) ≠ 0) :
    IsOpen (range fun u : Kˣ => u.val ^ n) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨u, rfl⟩
  have hd := hasStrictDerivAt_pow n u.val
  rw [← hd.map_nhds_eq (mul_ne_zero hn (pow_ne_zero _ u.ne_zero))]
  change ∀ᶠ x in 𝓝 u.val, x ^ n ∈ range (fun u : Kˣ => u.val ^ n)
  filter_upwards [eventually_ne_nhds u.ne_zero] with x hx
  exact ⟨Units.mk0 x hx, rfl⟩

theorem isOpen_unit_powers (n : ℕ) (hn : (n : K) ≠ 0) : IsOpen (range fun u : Kˣ => u ^ n) := by
  have h : range (fun u : Kˣ => u ^ n) = Units.val ⁻¹' range (fun u : Kˣ => u.val ^ n) := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨u, rfl⟩
    · rintro ⟨u, hu⟩
      exact ⟨u, Units.ext hu⟩
  rw [h]
  exact (isOpen_nonzero_powers n hn).preimage Units.continuous_val

end MetaplecticPoisson
