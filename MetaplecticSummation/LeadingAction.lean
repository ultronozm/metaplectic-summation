import MetaplecticSummation.Cover.Operators

/-! Homogeneity and equivariance of the leading term in §8. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open Filter NumberField MeasureTheory
open scoped Topology
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

private theorem place_units_neBot (v : Place F) :
    NeBot (comap (fun u : (LocalField F v)ˣ => u.val) (𝓝 0)) := by
  cases v with
  | inl w => exact arch_units_neBot w
  | inr p =>
    letI := FinitePlace.nontriviallyNormedCompletion p
    exact units_neBot_at_zero (L := p.adicCompletion F)

private theorem continuous_arch_radonLeading (w : InfinitePlace F) {g : Charts w.Completion} (hg : g ∈ d.testSet (.inl w)) :
    Continuous (Function.uncurry (d.radonLeading (.inl w) g).1) ∧
      Continuous (Function.uncurry (d.radonLeading (.inl w) g).2) := by
  let v : Place F := .inl w
  let c : ℂ := (Real.sqrt (modulus F v (n : LocalField F v)))⁻¹
  have H := (d.arch_radon_hat_bounded w hg).1
  let i (q : w.Completionˣ × w.Completion) := (q,(0 : w.Completion))
  have hi : Continuous i := continuous_id.prodMk continuous_const
  have H₀ := H.comp (f := i) hi
  have e (q : w.Completionˣ × w.Completion) :
      (c * (d.archRadonHat w g q 0).1,c * (d.archRadonHat w g q 0).2) =
      ((d.radonLeading (.inl w) g).1 q.1 q.2,(d.radonLeading (.inl w) g).2 q.2 q.1) := by
    let R := radon n (d.symbol v) (modulus F v) (selfDual F d.character v) g
    have hat0 (f : LocalField F v → ℂ) : d.hat v f 0 = ∫ t, f t ∂(selfDual F d.character v) := by
      simp only [hat,zero_mul,Character.localValue_zero,mul_one]
    exact Prod.ext (congrArg (c * ·) (hat0 (fun t => (R t).1 q.1 q.2)))
      (congrArg (c * ·) (hat0 (fun t => (R t).2 q.2 q.1)))
  have hx := (continuous_const (y := c)).mul H₀.fst
  have hy := (continuous_const (y := c)).mul H₀.snd
  exact ⟨hx.congr (fun q => congrArg Prod.fst (e q)),
    (hy.comp (continuous_swap : Continuous (Prod.swap : w.Completion × w.Completionˣ → _))).congr
      (fun q => congrArg Prod.snd (e q.swap))⟩

/-- Continuity of both archimedean charts of the leading term, including the
axis in each chart. On a transformed generator this is continuity of the
Fourier integral of the corresponding Radon slice at frequency zero. -/
theorem continuous_arch_leading (w : InfinitePlace F) (Φ : d.schwartz (.inl w)) :
    Continuous (Function.uncurry (d.leading (.inl w) Φ).1) ∧
    Continuous (Function.uncurry (d.leading (.inl w) Φ).2) := by
  let v : Place F := .inl w
  let K := LocalField F v
  let P (g : Charts K) := Continuous (Function.uncurry g.1) ∧ Continuous (Function.uncurry g.2)
  have hz : P 0 := ⟨continuous_const,continuous_const⟩
  refine Submodule.span_induction (p := fun f hf => P (d.leading v ⟨f,hf⟩)) ?_ ?_ ?_ ?_ Φ.property
  · rintro f (hf | ⟨g,hg,rfl⟩)
    · rw [d.leading_archTest_eq_zero w _ hf]
      exact hz
    · rw [d.leading_archTest_transform w hg]
      exact d.continuous_arch_radonLeading w hg
  · change P (d.leading v 0)
    rw [map_zero]
    exact hz
  · intro f g hf hg H J
    change P (d.leading v (⟨f,hf⟩ + ⟨g,hg⟩))
    rw [map_add]
    exact ⟨H.1.add J.1,H.2.add J.2⟩
  · intro c f hf H
    change P (d.leading v (c • ⟨f,hf⟩))
    rw [map_smul]
    exact ⟨continuous_const.mul H.1,continuous_const.mul H.2⟩

/-- The two leading-term charts have the original Hilbert symbol transition. -/
theorem leading_glues (v : Place F) (Φ : d.schwartz v) : Glues (d.symbol v) (d.leading v Φ) := by
  letI := place_units_neBot v
  intro x y
  have he (s : (LocalField F v)ˣ) : d.symbol v (s^n*x) (s^n*y) = d.symbol v x y := by
    let H := d.unitPairing v
    change (H (s^n*x) (s^n*y)).val = _
    simp only [map_mul,map_pow,MonoidHom.mul_apply,MonoidHom.pow_apply,d.unitPairing_pow,one_mul,H]
    rfl
  have h := d.leading_spec v Φ
  apply tendsto_nhds_unique (h.1 x y.val)
  apply ((h.2 x.val y).const_mul (d.symbol v x y)).congr
  intro s
  have gl := d.schwartz_glues v Φ (s^n*x) (s^n*y)
  rw [he] at gl
  simp only [Units.val_mul,Units.val_pow_eq_pow_val] at gl
  rw [gl,mul_left_comm]

/-- The leading term scales by |u|^(1−n) under the power dilation u^n. -/
theorem leading_homogeneous (v : Place F) (Φ : d.schwartz v) (u : (LocalField F v)ˣ) :
    let K := LocalField F v
    let b := d.leading v Φ
    let c := (modulus F v u.val : ℂ)^(n-1)
    (∀ (a : Kˣ) (y : K), c*b.1 (u^n*a) (u.val^n*y) = b.1 a y) ∧
    (∀ (x : K) (a : Kˣ), c*b.2 (u.val^n*x) (u^n*a) = b.2 x a) := by
  let K := LocalField F v
  let l := comap (fun s : Kˣ => s.val) (𝓝 0)
  letI := place_units_neBot v
  have ht : Tendsto (fun s : Kˣ => s*u) l l := by
    apply tendsto_comap_iff.mpr
    simpa only [Function.comp_def,Units.val_mul,zero_mul] using
      (tendsto_comap (f := fun s : Kˣ => s.val) (x := 𝓝 0)).mul_const u.val
  have hm (s : Kˣ) : modulus F v (s.val*u.val) = modulus F v s.val * modulus F v u.val := by
    cases v <;> simp [modulus,norm_mul,mul_pow,K]
  have L := d.leading_spec v Φ
  constructor
  · intro a y
    apply tendsto_nhds_unique ((L.1 (u^n*a) (u.val^n*y)).const_mul _)
    apply ((L.1 a y).comp ht).congr
    intro s
    simp only [Function.comp_apply,hm,Complex.ofReal_mul,mul_pow,Units.val_mul,mul_assoc]
    ring
  · intro x a
    apply tendsto_nhds_unique ((L.2 (u.val^n*x) (u^n*a)).const_mul _)
    apply ((L.2 x a).comp ht).congr
    intro s
    simp only [Function.comp_apply,hm,Complex.ofReal_mul,mul_pow,Units.val_mul,mul_assoc]
    ring

/-- Equivariance on the two unipotent generators of the local cover. -/
theorem leading_upper (v : Place F) (u : LocalField F v) {s : d.Operators v} (h : d.IsUpper v u s)
    (Φ : d.schwartz v) :
    d.leading v (s Φ) = upperShear (d.symbol v) u (d.leading v Φ) := by
  letI := place_units_neBot v
  have A := d.leading_spec v (s Φ)
  have B := d.leading_spec v Φ
  apply d.eq_upperShear v (d.leading_glues v _) u
  · intro x y
    apply tendsto_nhds_unique (A.1 x y)
    apply (B.1 x (y+u*x.val)).congr
    intro r
    rw [(h Φ).1,Units.val_mul,Units.val_pow_eq_pow_val,mul_add]
    ring_nf
  · intro y
    apply tendsto_nhds_unique (A.2 0 y)
    exact (B.2 0 y).congr (fun r => by simp only [mul_zero,(h Φ).2])

theorem leading_lower (v : Place F) (u : LocalField F v) {s : d.Operators v} (h : d.IsLower v u s)
    (Φ : d.schwartz v) :
    d.leading v (s Φ) = lowerShear (d.symbol v) u (d.leading v Φ) := by
  letI := place_units_neBot v
  have A := d.leading_spec v (s Φ)
  have B := d.leading_spec v Φ
  apply d.eq_lowerShear v (d.leading_glues v _) u
  · intro x y
    apply tendsto_nhds_unique (A.2 x y)
    apply (B.2 (x+u*y.val) y).congr
    intro r
    rw [(h Φ).1,Units.val_mul,Units.val_pow_eq_pow_val,mul_add]
    ring_nf
  · intro x
    apply tendsto_nhds_unique (A.1 x 0)
    exact (B.1 x 0).congr (fun r => by simp only [mul_zero,(h Φ).2])

/-- Vanishing of the leading term is invariant under the entire local cover,
as needed for the translated constant terms in Appendix B. -/
theorem leading_cover_zero_iff (v : Place F) (g : d.cover v) (Φ : d.schwartz v) :
    d.leading v (g.val Φ) = 0 ↔ d.leading v Φ = 0 := by
  let P (s : d.Operators v) := ∀ f, d.leading v (s f) = 0 ↔ d.leading v f = 0
  suffices P g.val from this Φ
  refine Subgroup.closure_induction (p := fun s _ => P s) ?_ (fun _ => Iff.rfl) ?_ ?_ g.property
  · rintro s (⟨z,h⟩ | ⟨u,hu⟩ | ⟨u,hu⟩) f
    · rw [h,(d.leading v).map_smul]
      simp [(d.embedding z).ne_zero]
    · rw [d.leading_upper v u hu]
      have hz (t) : upperShear (d.symbol v) t 0 = 0 := (upperShearLinear (d.symbol v) t).map_zero
      refine ⟨fun H => ?_,fun H => H ▸ hz u⟩
      have HH := congrArg (upperShear (d.symbol v) (-u)) H
      rwa [upperShear_add,neg_add_cancel,upperShear_zero (d.symbol v) (fun a b => (d.unitPairing v a b).ne_zero) (d.leading_glues v f),hz] at HH
    · rw [d.leading_lower v u hu]
      have hz (t) : lowerShear (d.symbol v) t 0 = 0 := (lowerShearLinear (d.symbol v) t).map_zero
      refine ⟨fun H => ?_,fun H => H ▸ hz u⟩
      have HH := congrArg (lowerShear (d.symbol v) (-u)) H
      rwa [lowerShear_add,neg_add_cancel,lowerShear_zero _ (d.leading_glues v f),hz] at HH
  · intro s t _ _ hs ht f
    exact (hs (t f)).trans (ht f)
  · intro s _ hs f
    change d.leading v (s.symm f) = 0 ↔ _
    simpa only [LinearEquiv.apply_symm_apply] using! (hs (s.symm f)).symm

/-- The action of the local cover descends uniquely to the space of leading
terms. The leading-term map intertwines the two actions for every lift. -/
theorem existsUnique_leading_action (v : Place F) :
    ∃! ρ : d.cover v →* ((d.leading v).range ≃ₗ[ℂ] (d.leading v).range), ∀ g Φ,
      ρ g ((d.leading v).rangeRestrict Φ) = (d.leading v).rangeRestrict (g.val Φ) := by
  let L := (d.leading v).rangeRestrict
  have surj : Function.Surjective L := (d.leading v).surjective_rangeRestrict
  obtain ⟨S,hS⟩ := L.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr surj)
  have hsec (y) : L (S y) = y := LinearMap.congr_fun hS y
  let A (g : d.cover v) := L.comp (g.val.toLinearMap.comp S)
  have hA (g : d.cover v) (Φ) : A g (L Φ) = L (g.val Φ) := by
    have hsub : d.leading v (S (L Φ) - Φ) = 0 := by
      rw [map_sub,sub_eq_zero]
      exact congrArg Subtype.val (hsec (L Φ))
    have h := (d.leading_cover_zero_iff v g _).mpr hsub
    rw [map_sub,map_sub,sub_eq_zero] at h
    exact Subtype.ext h
  let E (g : d.cover v) : (d.leading v).range ≃ₗ[ℂ] (d.leading v).range := by
    apply LinearEquiv.ofLinear (A g) (A g⁻¹)
    · apply LinearMap.ext
      intro y
      obtain ⟨x,rfl⟩ := surj y
      change A g (A g⁻¹ (L x)) = L x
      rw [hA,hA]
      exact congrArg L (g.val.apply_symm_apply x)
    · apply LinearMap.ext
      intro y
      obtain ⟨x,rfl⟩ := surj y
      change A g⁻¹ (A g (L x)) = L x
      rw [hA,hA]
      exact congrArg L (g.val.symm_apply_apply x)
  have he g x : E g (L x) = L (g.val x) := hA g x
  let ρ : d.cover v →* ((d.leading v).range ≃ₗ[ℂ] (d.leading v).range) :=
    { toFun := E
      map_one' := LinearEquiv.ext fun y => by obtain ⟨x,rfl⟩ := surj y; exact he 1 x
      map_mul' := fun g h => LinearEquiv.ext fun y => by
        obtain ⟨x,rfl⟩ := surj y
        change E (g*h) (L x) = E g (E h (L x))
        rw [he,he,he]
        rfl }
  refine ⟨ρ,he,fun ρ' h => MonoidHom.ext fun g => LinearEquiv.ext fun y => ?_⟩
  obtain ⟨x,rfl⟩ := surj y
  exact (h g x).trans (he g x).symm

end MetaplecticPoisson.Datum
