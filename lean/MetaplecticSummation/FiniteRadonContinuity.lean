import MetaplecticSummation.RadonConvergence

/-! Absolute convergence and joint continuity of both finite-place Radon
charts on the entire Schwartz space, including the zero-determinant fiber. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField MeasureTheory Set
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)
variable (p : Prime F)
local notation "vₚ" => (Sum.inr p : Place F)
local notation "Kv" => LocalField F vₚ
local notation "dx" => selfDual F d.character vₚ

/-- Both inner chart integrals converge absolutely on every line, and both
normalized integrals depend continuously on the chart vector and determinant parameter. -/
theorem finite_radon_convergence (Φ : d.schwartz vₚ) :
    (∀ t a b, Integrable (lineIntegrandX (d.symbol vₚ) Φ.val n t a b) dx) ∧
    (∀ t a b, Integrable (lineIntegrandY (d.symbol vₚ) Φ.val n t a b) dx) ∧
    (Continuous fun q : (Kvˣ × Kv) × Kv => (d.radonAt vₚ Φ.val q.2).1 q.1.1 q.1.2) ∧
    (Continuous fun q : (Kv × Kvˣ) × Kv => (d.radonAt vₚ Φ.val q.2).2 q.1.1 q.1.2) :=
  d.schwartz_radon_convergence (.inr p) Φ

end MetaplecticPoisson.Datum
