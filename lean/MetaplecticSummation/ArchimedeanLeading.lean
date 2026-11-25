import MetaplecticSummation.ArchimedeanRadon

/-! The archimedean normalized limits of §8 for test functions and their transforms. -/
noncomputable section
namespace MetaplecticPoisson
open Filter NumberField
open scoped Topology

private theorem rapidChart_zero_limit {E I : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} {f : E → ℂ} (hf : rapidChart U f) {z : I → E} {l : Filter I}
    (hz : Tendsto z l (𝓝 0)) (hU : ∀ i, z i ∈ U) : Tendsto (fun i => f (z i)) l (𝓝 0) := by
  obtain ⟨C,hC⟩ := hf.2 0 1
  have H (i : I) : ‖f (z i)‖ ≤ max C 0*‖z i‖ := by
    have h := hC (z i) (hU i)
    rw [norm_iteratedFDeriv_zero,pow_one] at h
    exact h.trans ((mul_le_mul_of_nonneg_right (le_max_left ..) (le_min (norm_nonneg _) (inv_nonneg.mpr (norm_nonneg _)))).trans
      (mul_le_mul_of_nonneg_left (min_le_left ..) (le_max_right ..)))
  exact squeeze_zero_norm H (by simpa using hz.norm.const_mul (max C 0))

private theorem archTest_zero_leading {K L : Type} [NormedField K] [NormedField L] [NormedAlgebra ℝ L]
    (e : K ≃+* L) (he : Isometry e) {f : Charts K} (hf : archTest e f) (n m : ℕ) (hn : n ≠ 0) :
    IsLeadingTerm n (fun x : K => ‖x‖^m) f 0 := by
  let l := comap (fun u : Kˣ => u.val) (𝓝 0)
  have hu : Tendsto (fun u : Kˣ => u.val) l (𝓝 0) := tendsto_comap
  have hw : Tendsto (fun u : Kˣ => ((‖u.val‖^m : ℝ) : ℂ)^(n-1)) l
      (𝓝 (((‖(0:K)‖^m : ℝ) : ℂ)^(n-1))) := ((Complex.continuous_ofReal.tendsto _).comp (hu.norm.pow m)).pow _
  have hp : Tendsto (fun u : Kˣ => u.val^n) l (𝓝 0) := by simpa only [zero_pow hn] using hu.pow n
  let Z (x y : K) (u : Kˣ) := (e (u.val^n*x),e (u.val^n*y))
  have hZ (x y : K) : Tendsto (Z x y) l (𝓝 0) := by
    have H (c : K) : Tendsto (fun u : Kˣ => e (u.val^n*c)) l (𝓝 0) := by
      simpa only [Function.comp_def,zero_mul,map_zero] using (he.continuous.tendsto (0*c)).comp (hp.mul_const c)
    exact (H x).prodMk_nhds (H y)
  constructor
  · intro a b
    have h := rapidChart_zero_limit hf.1 (hZ a.val b)
      (fun u => (map_ne_zero e).mpr (mul_ne_zero (pow_ne_zero _ u.ne_zero) a.ne_zero))
    have eqn (u : Kˣ) : xChart f (e.symm (Z a.val b u).1,e.symm (Z a.val b u).2) = f.1 (u^n*a) (u.val^n*b) := by
      change xChart f (e.symm (e (u.val^n*a.val)),e.symm (e (u.val^n*b))) = _
      rw [e.symm_apply_apply,e.symm_apply_apply,xChart,dif_pos (mul_ne_zero (pow_ne_zero _ u.ne_zero) a.ne_zero)]
      exact congrArg (fun c : Kˣ => f.1 c (u.val^n*b)) (Units.ext rfl)
    simpa only [eqn,mul_zero,Prod.fst_zero,Prod.snd_zero,Pi.zero_apply] using hw.mul h
  · intro a b
    have h := rapidChart_zero_limit hf.2 (hZ a b.val)
      (fun u => (map_ne_zero e).mpr (mul_ne_zero (pow_ne_zero _ u.ne_zero) b.ne_zero))
    have eqn (u : Kˣ) : yChart f (e.symm (Z a b.val u).1,e.symm (Z a b.val u).2) = f.2 (u.val^n*a) (u^n*b) := by
      change yChart f (e.symm (e (u.val^n*a)),e.symm (e (u.val^n*b.val))) = _
      rw [e.symm_apply_apply,e.symm_apply_apply,yChart,dif_pos (mul_ne_zero (pow_ne_zero _ u.ne_zero) b.ne_zero)]
      exact congrArg (fun c : Kˣ => f.2 (u.val^n*a) c) (Units.ext rfl)
    simpa only [eqn,mul_zero,Prod.fst_zero,Prod.snd_zero,Pi.zero_apply] using hw.mul h

namespace Datum
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

theorem arch_test_zero_leading (w : InfinitePlace F) {f : Charts (LocalField F (.inl w))}
    (hf : f ∈ d.testSet (.inl w)) : IsLeadingTerm n (modulus F (.inl w)) f 0 := by
  by_cases hw : w.IsReal
  · exact archTest_zero_leading (InfinitePlace.Completion.ringEquivRealOfIsReal hw)
      (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw)
      (by simpa only [testSet,dif_pos hw] using! hf.2) n w.mult (NeZero.ne n)
  · exact archTest_zero_leading (InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (InfinitePlace.not_isReal_iff_isComplex.mp hw)) (InfinitePlace.Completion.isometry_extensionEmbedding w)
      (by simpa only [testSet,dif_neg hw] using! hf.2) n w.mult (NeZero.ne n)

theorem arch_test_transform_leading (w : InfinitePlace F) {f : Charts (LocalField F (.inl w))}
    (hf : f ∈ d.testSet (.inl w)) : IsLeadingTerm n (modulus F (.inl w))
      (d.integralTransform (.inl w) f) (d.radonLeading (.inl w) f) :=
  d.isLeadingTerm_integralTransform _ _ (d.arch_test_integrable_slices w hf)

theorem arch_units_neBot (w : InfinitePlace F) :
    NeBot (comap (fun u : (LocalField F (.inl w))ˣ => u.val) (𝓝 0)) := by
  letI := archNontriviallyNormedCompletion w
  exact units_neBot_at_zero (L := LocalField F (.inl w))

theorem exists_leading_arch (w : InfinitePlace F) :
    let v : Place F := .inl w
    ∃ b : d.schwartz v →ₗ[ℂ] Charts (LocalField F v), ∀ f : d.schwartz v,
      IsLeadingTerm n (modulus F v) f (b f) := by
  letI := arch_units_neBot w
  exact d.exists_leading_of_generators _ (d.arch_test_zero_leading w) (d.arch_test_transform_leading w)

/-- The one-dimensional Fourier integrals on the two archimedean Radon charts,
with the unit coordinate first in each parameter pair. -/
def archRadonHat (w : InfinitePlace F) (f : Charts w.Completion) (q : w.Completionˣ × w.Completion)
    (u : w.Completion) : ℂ × ℂ :=
  let v : Place F := .inl w
  let R := radon n (d.symbol v) (modulus F v) (selfDual F d.character v) f
  (d.hat v (fun t => (R t).1 q.1 q.2) u, d.hat v (fun t => (R t).2 q.2 q.1) u)

/-- Joint continuity of the Fourier integrals and boundedness uniformly over
all frequencies for chart vectors in a compact set. -/
theorem arch_radon_hat_bounded (w : InfinitePlace F) {f : Charts w.Completion} (hf : f ∈ d.testSet (.inl w)) :
    Continuous (Function.uncurry (d.archRadonHat w f)) ∧ ∀ T : Set (w.Completionˣ × w.Completion),
      IsCompact T → ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ T, ∀ u, ‖d.archRadonHat w f q u‖ ≤ C := by
  let K := LocalField F (.inl w)
  letI : LocallyCompactSpace K := inferInstanceAs (LocallyCompactSpace w.Completion)
  letI : LocallyCompactSpace {x : K // x ≠ 0} :=
    (isOpen_ne_fun continuous_id (continuous_const (y := (0 : K)))).locallyCompactSpace
  letI : LocallyCompactSpace Kˣ := unitsHomeomorphNeZero.isOpenEmbedding.locallyCompactSpace
  letI : FirstCountableTopology Kˣ := Units.isEmbedding_val₀.firstCountableTopology
  obtain ⟨_,_,hx,hy⟩ := d.arch_test_radon w hf
  have hy' := hy.comp (Prod.swap : Kˣ × K → K × Kˣ) continuous_swap
  obtain ⟨cx,bx⟩ := hx.fourier _ (d.arch_integrable_inv_cube w) (d.character.continuous_localValue _) (d.character.norm_localValue _)
  obtain ⟨cy,by'⟩ := hy'.fourier _ (d.arch_integrable_inv_cube w) (d.character.continuous_localValue _) (d.character.norm_localValue _)
  refine ⟨cx.prodMk cy,?_⟩
  intro T hT
  obtain ⟨A,hA,H⟩ := bx T hT
  obtain ⟨B,_,H'⟩ := by' T hT
  exact ⟨max A B,hA.trans (le_max_left ..),fun q hq u => max_le ((H q hq u).trans (le_max_left ..))
    ((H' q hq u).trans (le_max_right ..))⟩

end Datum
end MetaplecticPoisson
