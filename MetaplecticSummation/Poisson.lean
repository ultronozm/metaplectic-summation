import MetaplecticSummation.Schwartz

noncomputable section
namespace MetaplecticPoisson
namespace Datum
open Filter
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

/-- Algebraic adelic Schwartz space of §9.2. -/
abbrev Schwartz := restrictedTensor d.basic

def adelicFourier : d.Schwartz →ₗ[ℂ] d.Schwartz :=
  tensorMap d.basic d.basic d.fourier d.eventually_fourier_basic

abbrev Boundary := restrictedTensor (fun v => (d.leading v).rangeRestrict (d.basic v))

def adelicLeading : d.Schwartz →ₗ[ℂ] d.Boundary :=
  tensorMap d.basic (fun v => (d.leading v).rangeRestrict (d.basic v))
    (fun v => (d.leading v).rangeRestrict) (Eventually.of_forall fun _ => rfl)

theorem adelicLeading_surjective : Function.Surjective d.adelicLeading :=
  tensorMap_surjective _ _ _ _ (fun v => (d.leading v).surjective_rangeRestrict)

def pure (f : ∀ v, d.schwartz v) (hf : ∀ᶠ v in cofinite, f v = d.basic v) : d.Schwartz :=
  ⟨PiTensorProduct.tprod ℂ f, Submodule.subset_span ⟨f, hf, rfl⟩⟩

def diagonalPoint (p : RationalPoint F) (v : Place F) : LocalField F v × LocalField F v :=
  (diagonal F v p.val.1, diagonal F v p.val.2)

/-- The chart choice is made once at the rational point. -/
def localValue (p : RationalPoint F) (v : Place F) (f : d.schwartz v) : ℂ := by
  classical exact if p.val.1 ≠ 0 then xChart f (diagonalPoint p v) else yChart f (diagonalPoint p v)

theorem eventually_basic_value (p : RationalPoint F) :
    ∀ᶠ v in cofinite, d.localValue p v (d.basic v) = 1 := by sorry

/-- Extension from restricted pure tensors by multilinearity. -/
theorem exists_evaluation :
    ∃ ev : d.Schwartz →ₗ[ℂ] (RationalPoint F → ℂ),
      ∀ f hf p, ev (d.pure f hf) p = ∏ᶠ v, d.localValue p v (f v) := by sorry

def evaluation := d.exists_evaluation.choose

theorem evaluation_pure (f : ∀ v, d.schwartz v) (hf) (p : RationalPoint F) :
    d.evaluation (d.pure f hf) p = ∏ᶠ v, d.localValue p v (f v) :=
  d.exists_evaluation.choose_spec f hf p

/-- Reciprocity gives the same product in the Y chart whenever that chart is available. -/
theorem evaluation_pure_y (f : ∀ v, d.schwartz v) (hf) (p : RationalPoint F) (hy : p.val.2 ≠ 0) :
    d.evaluation (d.pure f hf) p = ∏ᶠ v, yChart (f v) (diagonalPoint p v) := by sorry

/-- Theorem 9.1. Both sums range over the nonzero rational vectors. -/
theorem poisson :
    ∃! B : d.Boundary →ₗ[ℂ] ℂ, ∀ Φ : d.Schwartz,
      Summable (fun v => ‖d.evaluation Φ v‖) ∧
      Summable (fun v => ‖d.evaluation (d.adelicFourier Φ) v‖) ∧
      (∑' v, d.evaluation Φ v) + B (d.adelicLeading Φ) =
        (∑' v, d.evaluation (d.adelicFourier Φ) v) +
          B (d.adelicLeading (d.adelicFourier Φ)) := by sorry

/-- Corollary 9.2. The two boundary contributions vanish. -/
theorem poisson_of_leading_eq_zero (Φ : d.Schwartz)
    (h : d.adelicLeading Φ = 0) (hF : d.adelicLeading (d.adelicFourier Φ) = 0) :
    (∑' v, d.evaluation Φ v) = ∑' v, d.evaluation (d.adelicFourier Φ) v := by
  obtain ⟨B, hB, _⟩ := d.poisson
  simpa only [h, hF, map_zero, add_zero] using (hB Φ).2.2

/-- The paragraph following Theorem 9.1. In degree one the leading term
in the direction (1,0) gives the local Schwartz function's value at zero. -/
theorem boundary_degree_one (a : Datum F 1) (f : ∀ v, a.schwartz v)
    (hf : ∀ᶠ v in cofinite, f v = a.basic v) :
    a.poisson.exists.choose (a.adelicLeading (a.pure f hf)) =
      ∏ᶠ v, ((a.leading v) (f v)).1 1 0 := by sorry

end Datum
end MetaplecticPoisson
