import MetaplecticSummation.Schwartz
import MetaplecticSummation.SymbolOnLines

noncomputable section
namespace MetaplecticPoisson.Datum

variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

private abbrev family := (existsUnique_hilbert F n d.primitive).exists.choose
private theorem family_spec : IsHilbertFamily F n d.family :=
  (existsUnique_hilbert F n d.primitive).exists.choose_spec

/-- The unit-valued pairing underlying the chart transition function. -/
def unitPairing (v : Place F) : (LocalField F v)ˣ →* (LocalField F v)ˣ →* ℂˣ :=
  MonoidHom.mk' (fun x => d.embedding.comp
    (MonoidHom.mk' (d.family v x) (d.family_spec.mul_right v x))) (by
    intro x y
    ext z
    change ((d.embedding (d.family v (x*y) z) : ℂˣ) : ℂ) = _
    rw [d.family_spec.mul_left v, map_mul]
    rfl)

@[simp] theorem coe_unitPairing (v : Place F) (a b : (LocalField F v)ˣ) :
    (d.unitPairing v a b : ℂ) = d.symbol v a b := rfl

theorem unitPairing_pow (v : Place F) (a b : (LocalField F v)ˣ) :
    d.unitPairing v a b ^ n = 1 := by
  change (d.embedding (d.family v a b)) ^ n = 1
  have h : d.family v a b ^ n = 1 := Subtype.ext (d.family v a b).property
  rw [← map_pow, h, map_one]

@[simp] theorem norm_symbol (v : Place F) (a b : (LocalField F v)ˣ) :
    ‖d.symbol v a b‖ = 1 :=
  Complex.norm_eq_one_of_pow_eq_one (congrArg Units.val (d.unitPairing_pow v a b)) (NeZero.ne n)

/-- Continuity is unchanged upon replacing local roots of unity by complex roots:
the local image has the discrete topology. -/
theorem continuous_symbol (v : Place F) :
    Continuous (fun p : (LocalField F v)ˣ × (LocalField F v)ˣ => d.symbol v p.1 p.2) := by
  let e (z : Mu F n) := diagonal F v ((z.val : Fˣ) : F)
  letI : TopologicalSpace (Mu F n) := TopologicalSpace.induced e inferInstance
  have he : Topology.IsEmbedding e := ⟨⟨rfl⟩,
    (diagonal F v).injective.comp (Units.val_injective.comp Subtype.val_injective)⟩
  letI : T1Space (Mu F n) := he.t1Space
  have hc : Continuous (fun p : (LocalField F v)ˣ × (LocalField F v)ˣ => d.family v p.1 p.2) :=
    continuous_induced_rng.mpr (d.family_spec.continuous_pair v)
  exact (continuous_of_discreteTopology (f := fun z : Mu F n => ((d.embedding z : ℂˣ) : ℂ))).comp hc

/-- All inputs to the overlap calculation except the Steinberg relation follow
from the existing characterization of the number-field Hilbert symbol. -/
def lineSymbol (v : Place F) (steinberg : ∀ a b : (LocalField F v)ˣ,
    (a : LocalField F v) + b = 1 → d.unitPairing v a b = 1) : LineSymbol (LocalField F v) n where
  pairing := d.unitPairing v
  torsion := d.unitPairing_pow v
  skew a b := by
    apply eq_inv_of_mul_eq_one_left
    change d.embedding (d.family v a b) * d.embedding (d.family v b a) = 1
    rw [← map_mul, d.family_spec.skew, map_one]
  neg_self a := by
    change d.embedding (d.family v a (-a)) = 1
    rw [d.family_spec.neg_self, map_one]
  steinberg := steinberg

end MetaplecticPoisson.Datum
