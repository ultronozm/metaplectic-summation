import GroundTheory.GlobalFields.TateThesis.SchwartzBruhatFinite
import MetaplecticSummation.PowerClassIntegrals
import MetaplecticSummation.TransformedMarginals
import Mathlib.Topology.LocallyConstant.Algebra

/-! Finite parts of decomposable additive Schwartz–Bruhat functions in Proposition B.4. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField IsDedekindDomain Filter Set
open scoped Topology
open Classical
variable {F : Type} [Field F] [NumberField F]
local notation "P" => HeightOneSpectrum (𝓞 F)
local notation "A" => FiniteAdeleRing (𝓞 F) F

/-- A restricted product of local finite Schwartz–Bruhat tests is a finite
adelic Schwartz–Bruhat function for the ordinary Poisson theorem. -/
theorem finiteTensor_mem_schwartzBruhat (f : (p : P) → p.adicCompletion F → ℂ)
    (hf : ∀ p, Bruhat (.inr p) (f p))
    (h : ∀ᶠ p in cofinite, ∀ t, f p t = if ‖t‖ ≤ 1 then 1 else 0) :
    (fun x : A => ∏ᶠ p, f p (x p)) ∈ GroundTheory.Global.finiteSchwartzBruhat F := by
  let S := (eventually_cofinite.mp h).toFinset
  let O (p : P) : Set (p.adicCompletion F) := p.adicCompletionIntegers F
  have good (p : P) (hp : p ∉ S) (t : p.adicCompletion F) :
      f p t = if t ∈ O p then 1 else 0 := by
    have := of_not_not fun hn => hp ((eventually_cofinite.mp h).mem_toFinset.mpr hn)
    exact (this t).trans (if_congr (mem_localIntegers_iff p t).symm rfl rfl)
  have finiteFactors (x : A) : Function.HasFiniteMulSupport (fun p => f p (x p)) := by
    apply eventually_cofinite.mp
    filter_upwards [h,x.2] with p h hp
    exact (h _).trans (if_pos ((mem_localIntegers_iff p _).mp hp))
  let U : Set A := {x | ∀ p ∉ S, x p ∈ O p}
  have ho : IsOpen U := RestrictedProduct.isOpen_forall_imp_mem
    (fun p : P => FinitePlace.isOpen_adicCompletionIntegers p)
  have hc : IsClosed U := by
    have eqn : U = ⋂ p : P, ⋂ (_ : p ∉ S), (fun x : A => x p) ⁻¹' O p := by
      ext; simp [U]
    rw [eqn]
    exact isClosed_iInter (fun p => isClosed_iInter fun _ =>
      (FinitePlace.isCompact_adicCompletionIntegers p).isClosed.preimage (RestrictedProduct.continuous_eval p))
  let g (p : P) : LocallyConstant A ℂ := (⟨f p,(hf p).1⟩ : LocallyConstant _ ℂ).comap
    ⟨_,RestrictedProduct.continuous_eval p⟩
  let G := (∏ p ∈ S, g p).indicator (show IsClopen U from ⟨hc,ho⟩)
  have he (x : A) : ∏ᶠ p, f p (x p) = G x := by
    by_cases hx : x ∈ U
    · rw [finprod_eq_prod_of_mulSupport_subset (s := S) _ (fun p hp => by
        by_contra hn
        exact hp ((good p hn _).trans (if_pos (hx p hn))))]
      rw [show G x = (∏ p ∈ S, g p) x from LocallyConstant.indicator_of_mem _ _ hx]
      exact (map_prod (LocallyConstant.evalMonoidHom x : LocallyConstant A ℂ →* ℂ) g S).symm
    · obtain ⟨p,hp,hx'⟩ : ∃ p ∉ S, x p ∉ O p := by
        by_contra! hh
        exact hx hh
      rw [finprod_eq_zero _ p ((good p hp _).trans (if_neg hx')) (finiteFactors x)]
      exact (LocallyConstant.indicator_of_notMem _ _ hx).symm
  rw [GroundTheory.Global.mem_finiteSchwartzBruhat]
  refine ⟨(funext he).symm ▸ G.isLocallyConstant,?_⟩
  let D (p : P) := if p ∈ S then tsupport (f p) else O p
  have hD (p : P) : IsCompact (D p) := by
    dsimp only [D]
    split
    · exact (hf p).2
    · exact FinitePlace.isCompact_adicCompletionIntegers p
  letI (p : P) : CompactSpace (D p) := isCompact_iff_compactSpace.mp (hD p)
  let lift (z : ∀ p, D p) : RestrictedProduct _ (fun p : P => p.adicCompletionIntegers F) (𝓟 (↑S : Set P)ᶜ) :=
    ⟨fun p => (z p).val, fun p hp => by
      change p ∉ S at hp
      change (z p).val ∈ O p
      exact (show D p = O p from if_neg hp) ▸ (z p).property⟩
  have hcont : Continuous lift := RestrictedProduct.continuous_rng_of_principal.mpr
    (continuous_pi fun p => continuous_subtype_val.comp (continuous_apply p))
  have hfilter : cofinite ≤ 𝓟 (↑S : Set P)ᶜ := le_principal_iff.mpr S.finite_toSet.compl_mem_cofinite
  have compact := isCompact_range ((RestrictedProduct.continuous_inclusion hfilter).comp hcont)
  apply HasCompactSupport.intro compact
  intro x hx
  contrapose! hx
  have nz (p : P) : f p (x p) ≠ 0 := by
    intro hzero
    exact hx (finprod_eq_zero _ p hzero (finiteFactors x))
  refine ⟨fun p => ⟨x p,?_⟩,rfl⟩
  by_cases hp : p ∈ S
  · rw [show D p = tsupport (f p) from if_pos hp]
    exact subset_tsupport _ (nz p)
  · rw [show D p = O p from if_neg hp]
    by_contra hh
    exact nz p ((good p hp _).trans (if_neg hh))

variable {n : ℕ} [NeZero n] (d : Datum F n)

/-- The finite adelic test in the first application of additive Poisson in B.4. -/
theorem finiteTensor_axisLine (Φ : ∀ v, d.schwartz v) (hΦ : ∀ᶠ v in cofinite, Φ v = d.basic v) (y : Fˣ) :
    (fun z : A => ∏ᶠ p : P, d.axisLine (.inr p) (Φ (.inr p)) (atPlace (.inr p) y) (z p)) ∈
      GroundTheory.Global.finiteSchwartzBruhat F :=
  finiteTensor_mem_schwartzBruhat _ (fun p => d.finite_axisLine_bruhat p _ _) (d.eventually_axisLine_basic Φ hΦ y)

/-- The finite adelic test in the second application of additive Poisson in B.4. -/
theorem finiteTensor_axisDensity (Φ : ∀ v, d.schwartz v) (hΦ : ∀ᶠ v in cofinite, Φ v = d.basic v) (y : Fˣ) :
    (fun z : A => ∏ᶠ p : P, d.axisDensity (.inr p) (Φ (.inr p)) (atPlace (.inr p) y) (z p)) ∈
      GroundTheory.Global.finiteSchwartzBruhat F :=
  finiteTensor_mem_schwartzBruhat _ (fun p => d.axisDensity_finite_bruhat p _ _) (d.eventually_axisDensity_basic Φ hΦ y)

end MetaplecticPoisson.Datum
