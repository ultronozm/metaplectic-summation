import MetaplecticSummation.Schwartz.Local
import MetaplecticSummation.BasicMembership
import MetaplecticSummation.AdelicConductor

noncomputable section
namespace MetaplecticPoisson.Datum
open Filter NumberField
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

/-- An arbitrary reference vector suffices at the finitely many exceptional
places, since every pure tensor may vary there. We choose zero. -/
def basic : (v : Place F) → d.schwartz v
  | .inl _ => 0
  | .inr p => if h : p.asIdeal.absNorm.Coprime n then ⟨_, d.basic_mem p h⟩ else 0

theorem eventually_fourier_basic :
    ∀ᶠ v in cofinite, d.fourier v (d.basic v) = d.basic v := by
  apply eventually_place_of_finite
  filter_upwards [d.eventually_unramified] with p hψ
  by_cases hp : p.asIdeal.absNorm.Coprime n
  · apply Subtype.ext
    rw [d.fourier_apply,basic,dif_pos hp]
    exact d.basicCharts_fourier_fixed p hp hψ
  · simp only [basic,dif_neg hp,map_zero]

end MetaplecticPoisson.Datum
