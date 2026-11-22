import MetaplecticSummation.TameSymbols
import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.NumberTheory.NumberField.ProductFormula

/-! Isolating a finite-place Steinberg symbol by reciprocity. The weak
approximation argument follows GroundTheory.GlobalFields.Adele.WeakApprox. -/

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

namespace Datum
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

/-- Perturbing a nonzero pair with fixed sum one preserves its symbol. -/
private theorem eventually_same_pair (v : Place F) (a b : (LocalField F v)ˣ)
    (hab : a.val + b.val = 1) :
    ∀ᶠ x in 𝓝 a.val, ∃ u z : (LocalField F v)ˣ, u.val = x ∧ z.val = 1 - x ∧
      d.unitPairing v u z = d.unitPairing v a b := by
  classical
  let lift (x : LocalField F v) : (LocalField F v)ˣ := if hx : x ≠ 0 then Units.mk0 x hx else 1
  have near (u : (LocalField F v)ˣ) : ∀ᶠ x in 𝓝 u.val, (lift x).val = x := by
    filter_upwards [eventually_ne_nhds u.ne_zero] with x hx
    simp [lift, hx]
  have hl (u : (LocalField F v)ˣ) : Tendsto lift (𝓝 u.val) (𝓝 u) := by
    apply Units.isEmbedding_val₀.isInducing.tendsto_nhds_iff.mpr
    exact tendsto_id.congr' ((near u).mono fun _ h => h.symm)
  have hb : 1 - a.val = b.val := by linear_combination -hab
  have hs : Tendsto (fun x : LocalField F v => 1-x) (𝓝 a.val) (𝓝 b.val) := by
    rw [← hb]; exact tendsto_const_nhds.sub tendsto_id
  have he := ((hl a).prodMk_nhds ((hl b).comp hs)).eventually
    ((d.locallyConstant_unitPairing v).eventually_eq (a,b))
  filter_upwards [near a, hs.eventually (near b), he] with x hx hy hh
  exact ⟨lift x, lift (1-x), hx, hy, hh⟩

/-- Global reciprocity forces the Steinberg relation at a wild place. Weak
approximation prescribes the symbol there and makes it trivial at every other
place above n. All remaining factors are trivial by the tame and infinite-place cases. -/
theorem finite_steinberg (p : HeightOneSpectrum (𝓞 F)) (a b : (LocalField F (.inr p))ˣ)
    (hab : a.val + b.val = 1) : d.unitPairing (.inr p) a b = 1 := by
  classical
  let bad := (FinitePlace.finite_places_over_degree (K := F) n).toFinset
  let S := insert p bad
  let target := d.unitPairing (.inr p) a b
  let c : Fˣ := Units.mk0 2 (by norm_num)
  have hcz : (1 : F) - (c.val ^ n) ≠ 0 := by
    apply sub_ne_zero_of_ne
    change (1 : F) ≠ (2 : F)^n
    exact_mod_cast (Nat.one_lt_pow (NeZero.ne n) (by decide : 1 < 2)).ne
  let g := Units.mk0 _ hcz
  have goals (i : S) : ∃ u z : (LocalField F (.inr i.val))ˣ, u.val + z.val = 1 ∧
      d.unitPairing (.inr i.val) u z = if i.val = p then target else 1 := by
    obtain ⟨q, hq⟩ := i
    by_cases eq : q = p
    · subst q
      exact ⟨a, b, hab, by simp [target]⟩
    · let v : Place F := .inr q
      let e := diagonal F v
      let u := Units.map e.toMonoidHom g
      let z := Units.map e.toMonoidHom c
      refine ⟨u, z ^ n, ?_, ?_⟩
      · change e (1-c.val^n) + (e c.val)^n = 1
        rw [map_sub, map_one, map_pow]; ring
      · change d.unitPairing v u (z ^ n) = if q = p then _ else _
        rw [if_neg eq, map_pow, d.unitPairing_pow]
  choose u z hsum htarget using goals
  let good (i : S) (x : LocalField F (.inr i.val)) := ∃ l r : (LocalField F (.inr i.val))ˣ,
    l.val = x ∧ r.val = 1-x ∧ d.unitPairing (.inr i.val) l r = d.unitPairing (.inr i.val) (u i) (z i)
  have near : ∀ᶠ X in 𝓝 (fun i => (u i).val), ∀ i, good i (X i) :=
    Filter.eventually_all.mpr fun i => (continuous_apply i).continuousAt.eventually
      (d.eventually_same_pair _ _ _ (hsum i))
  obtain ⟨x, hx⟩ := (FinitePlace.denseRange_diagonal S).mem_nhds near
  change ∀ i, good i (diagonal F (.inr i.val) x) at hx
  let j : S := ⟨p, Finset.mem_insert_self ..⟩
  obtain ⟨l, r, hl, hr, _⟩ := hx j
  have hx₀ : x ≠ 0 := fun h => l.ne_zero (hl.trans (h ▸ map_zero _))
  have hy₀ : 1-x ≠ 0 := by
    intro h
    apply r.ne_zero
    rw [hr, ← map_one (diagonal F (.inr j.val)), ← map_sub, h, map_zero]
  let A := Units.mk0 x hx₀
  let B := Units.mk0 (1-x) hy₀
  let L (v : Place F) := Units.map (diagonal F v).toMonoidHom A
  let R (v : Place F) := Units.map (diagonal F v).toMonoidHom B
  have hLR (v : Place F) : (L v).val + (R v).val = 1 := by
    change diagonal F v x + diagonal F v (1-x) = 1
    rw [map_sub, map_one]; ring
  have he (i : S) : d.unitPairing (.inr i.val) (L _) (R _) = if i.val = p then target else 1 := by
    obtain ⟨l, r, hl, hr, h⟩ := hx i
    have hl' : l = L (.inr i.val) := Units.ext hl
    have hr' : r = R (.inr i.val) := Units.ext (hr.trans (by simp [R, B]))
    exact (hl' ▸ hr' ▸ h).trans (htarget i)
  have hv := d.unitPairing_single_place (.inr p) A B (by
    intro v hv
    change d.unitPairing v (L v) (R v) = 1
    cases v with
    | inl w => exact d.arch_steinberg w _ _ (hLR _)
    | inr q =>
      by_cases hq : q ∈ S
      · simpa [show q ≠ p from fun h => hv (congrArg Sum.inr h)] using he ⟨q, hq⟩
      · have hbad : (n : 𝓞 F) ∉ q.asIdeal := by
          intro h
          exact hq (Finset.mem_insert_of_mem (by simpa [bad] using h))
        exact d.tame_steinberg q (FinitePlace.tame_of_degree_not_mem n q hbad) _ _ (hLR _))
  exact (show d.unitPairing (.inr p) (L _) (R _) = target by simpa [j] using he j).symm.trans hv

/-- Lemma 4.2(ii) for every completion of the number field, including at τ = 0. -/
theorem radon_glues (v : Place F) {f : Charts (LocalField F v)} (hf : Glues (d.symbol v) f)
    (t : LocalField F v) :
    Glues (d.symbol v) (radon n (d.symbol v) (modulus F v) (selfDual F d.character v) f t) := by
  cases v with
  | inl w => exact d.arch_radon_glues w hf t
  | inr p => exact d.finite_radon_glues p (d.finite_steinberg p) hf t

theorem integralTransform_glues (v : Place F) {f : Charts (LocalField F v)} (hf : Glues (d.symbol v) f) :
    Glues (d.symbol v) (d.integralTransform v f) :=
  transform_glues_of_radon_glues _ _ _ _ _ f (d.radon_glues v hf)

theorem schwartz_glues (v : Place F) (Φ : d.schwartz v) : Glues (d.symbol v) Φ.val :=
  d.schwartz_glues_of_transform v (fun _ hf => d.integralTransform_glues v hf.1) Φ

end Datum
end MetaplecticPoisson
