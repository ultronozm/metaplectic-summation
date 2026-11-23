import MetaplecticSummation.Reduction.FundamentalDomain
import MetaplecticSummation.FourierCoefficients.Orbits

noncomputable section
namespace MetaplecticPoisson
open Set Topology TopologicalSpace MeasureTheory NumberField
variable (F : Type) [Field F] [NumberField F]

instance secondCountableAdeles : SecondCountableTopology (Adeles F) := by
  let := sigmaCompactAdeles F
  let := Datum.places_countable F
  let K := CompactExhaustion.choice (Adeles F)
  have inj : Function.Injective (fun x : Adeles F => Datum.component x) := by
    intro x y eqn
    exact Prod.ext (funext fun w => congrFun eqn (.inl w))
      (Subtype.ext (funext fun p => congrFun eqn (.inr p)))
  let (n : ℕ) : SecondCountableTopology (interior (K n)) := by
    let := isCompact_iff_compactSpace.mp (K.isCompact n)
    have hc : Continuous (fun x : K n => Datum.component x.val) :=
      continuous_pi fun v => (Datum.continuous_component v).comp continuous_subtype_val
    let := (hc.isClosedEmbedding (inj.comp Subtype.val_injective)).isEmbedding.secondCountableTopology
    exact (Topology.IsEmbedding.inclusion (interior_subset (s := K n))).secondCountableTopology
  apply secondCountableTopology_of_countable_cover (U := fun n => interior (K n)) (fun _ => isOpen_interior)
  apply iUnion_eq_univ_iff.mpr
  intro x
  obtain ⟨n,hn⟩ := K.exists_mem x
  exact ⟨n+1,K.subset_interior_succ n hn⟩

instance secondCountableAdelicSL : SecondCountableTopology (AdelicSL F) := by
  let : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (Adeles F)) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → Adeles F))
  exact Matrix.SpecialLinearGroup.isClosedEmbedding_val.isEmbedding.secondCountableTopology

end MetaplecticPoisson
