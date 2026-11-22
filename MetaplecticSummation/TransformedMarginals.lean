import MetaplecticSummation.ArchimedeanFourierSchwartz
import MetaplecticSummation.SchwartzStability
import MetaplecticSummation.FiniteRadonContinuity
import MetaplecticSummation.Jacquet.Convergence

/-! Appendix A's marginal identities for transformed generators of the Schwartz space. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField IsDedekindDomain MeasureTheory CompactlySupported
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)
variable (v : Place F)
local notation "K" => LocalField F v
local notation "N" => modulus F v (n : K)
local notation "dx" => selfDual F d.character v

/-- The defining Radon integral on the vertical axis is Schwartz–Bruhat for
a test section at every place (the last assertion of the marginal-axis lemma). -/
theorem axisLine_test_bruhat (Φ : d.schwartz v) (hΦ : Φ.val ∈ d.testSet v) (y : Kˣ) :
    Bruhat v (d.axisLine v Φ y) := by
  cases v with
  | inr p => exact d.axisLine_finiteTest_bruhat p Φ hΦ y
  | inl w =>
    have go {L : Type} [NormedField L] [NormedAlgebra ℝ L] (e : w.Completion ≃+* L) (he : Isometry e) :
        ∃ G : SchwartzMap L ℂ, ∀ t, d.axisLine (.inl w) Φ y t = G (e t) := by
      obtain ⟨G,hG,_⟩ := (d.arch_radon_schwartz_slices w hΦ e he).2
      exact ⟨G (y,0),hG (y,0)⟩
    dsimp only [Bruhat]
    split
    · exact go _ (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal _)
    · exact go _ (InfinitePlace.Completion.isometry_extensionEmbedding w)

omit [NeZero n] in
theorem Bruhat.const_mul {f : K → ℂ} (hf : Bruhat v f) (c : ℂ) :
    Bruhat v (fun t => c * f t) := by
  cases v with
  | inr p => exact ⟨hf.1.comp (c * ·),hf.2.mul_left (f := fun _ => c)⟩
  | inl w =>
    dsimp only [Bruhat] at hf ⊢
    split at hf <;> rename_i h
    · rw [dif_pos h]; obtain ⟨G,hG⟩ := hf; exact ⟨c • G,fun t => congrArg (c * ·) (hG t)⟩
    · rw [dif_neg h]; obtain ⟨G,hG⟩ := hf; exact ⟨c • G,fun t => congrArg (c * ·) (hG t)⟩

/-- Formula for the density of a transformed section, including its value
at the origin. The normalization uses the self-dual additive measure. -/
theorem axisDensity_transform_eq_hat (Φ Ψ : d.schwartz v) (hΨ : Ψ.val = d.integralTransform v Φ.val)
    (x : Kˣ) (hi : Integrable (d.axisLine v Φ (-1/x)) dx) :
    d.axisDensity v Ψ x = fun t =>
      ((N : ℂ) / (modulus F v x.val : ℂ) * (Real.sqrt N : ℂ)⁻¹) * d.hat v (d.axisLine v Φ (-1/x)) t := by
  funext t
  by_cases ht : t = 0
  · subst t
    rw [d.axisDensity_zero,← d.axisLine_hat_zero_of_charts v Φ Ψ hΨ _ hi,mul_assoc]
  let u := Units.mk0 t ht
  have h := (d.transform_pow_ray v Φ.val u).2 0 (-1/x)
  rw [mul_zero,← hΨ] at h
  change (modulus F v u.val : ℂ)^(n-1) * d.axis v Ψ (u^n*(-1/x)) =
    (Real.sqrt N : ℂ)⁻¹ * d.hat v (d.axisLine v Φ (-1/x)) u.val at h
  change d.axisDensity v Ψ x u.val = _
  rw [d.axisDensity_unit,mul_assoc,← show u^n*(-1/x) = -(u^n)/x by rw [mul_div_assoc',mul_neg_one],h,mul_assoc]
  rfl

/-- The density of the transform of a test section is Schwartz–Bruhat at
every real, complex, and finite place. -/
theorem axisDensity_transformTest_bruhat (Φ : d.schwartz v) (hΦ : Φ.val ∈ d.testSet v) (x : Kˣ) :
    Bruhat v (d.axisDensity v (d.transformTest v Φ hΦ) x) := by
  have hb := d.axisLine_test_bruhat v Φ hΦ (-1/x)
  rw [d.axisDensity_transform_eq_hat v Φ _ rfl x (hb.integrable d)]
  apply Bruhat.const_mul
  cases v with
  | inl w => exact d.arch_hat_bruhat w hb
  | inr p => exact d.hat_finite_bruhat p hb

private theorem marginal_symbol_sign (x u : Kˣ) :
    let e : Kˣ := (-1)^(n+1)
    d.symbol v (u^n*x) e * d.symbol v (-1) e = d.symbol v (-1) (-1/x) := by
  let H := d.lineSymbol v (by cases v with
    | inl w => exact d.arch_steinberg w
    | inr p => exact d.finite_steinberg p)
  let P := d.unitPairing v
  have neg (b : Kˣ) : P b ((-1)^(n+1)) = P b (-1) := by
    rw [pow_succ,map_mul,map_pow,d.unitPairing_pow,one_mul]
  have skew : P (-1) x = (P x (-1))⁻¹ := H.skew _ _
  change ((P (u^n*x) _ * P (-1) _).val) = (P (-1) (-1/x)).val
  congr 1
  rw [neg,neg,map_mul,MonoidHom.mul_apply,map_pow,MonoidHom.pow_apply,d.unitPairing_pow,one_mul,
    map_div,skew,div_inv_eq_mul,mul_comm]

/-- On a transformed test section, ordinary Fourier inversion and the
square formula on the original section give the converse marginal identity. -/
theorem reverse_marginal_transformTest_of_square (Φ : d.schwartz v) (hΦ : Φ.val ∈ d.testSet v)
    (Ψ Ω : d.schwartz v) (hΨ : Ψ.val = d.integralTransform v Φ.val)
    (hsq : Ω.val = d.torusCharts v ((-1)^(n+1)) Φ.val) (x u : Kˣ) :
    d.marginal v Ω (u^n*x) = (Real.sqrt N : ℂ)⁻¹ * d.hat v (d.axisDensity v Ψ x) u.val := by
  let e : Kˣ := (-1)^(n+1)
  let b : Kˣ := -1/x
  let ν := d.axisLine v Φ b
  have hν : Bruhat v ν := d.axisLine_test_bruhat v Φ hΦ b
  have hinv : d.hat v (d.hat v ν) u.val = ν (-u.val) := by
    cases v with
    | inl w => exact congrFun (d.arch_hat_hat w ν hν) u.val
    | inr p => exact d.hat_hat_finite p hν _
  let k := (Real.sqrt N : ℂ)⁻¹
  let m := (modulus F v x.val : ℂ)
  have hdens := d.axisDensity_transform_eq_hat v Φ Ψ hΨ x (hν.integrable d)
  have hhat : d.hat v (d.axisDensity v Ψ x) u.val = ((N : ℂ)/m*k) * ν (-u.val) := by
    rw [hdens,← hinv]
    unfold hat
    simp only [mul_assoc,integral_const_mul,ν,b,k,m]
  let a := u^n*x
  have hb : modulus F v b.val = (modulus F v x.val)⁻¹ := by cases v <;> simp [modulus,b,inv_pow]
  have he : modulus F v e.val = 1 := by cases v <;> simp [e,modulus,Units.val_pow_eq_pow_val]
  have harg : (-u)^n/b = e*a := by
    apply Units.ext
    simp only [b,e,a,Units.val_div_eq_div_val,Units.val_pow_eq_pow_val, Units.val_neg,Units.val_one,Units.val_mul]
    rw [show -u.val = (-1)*u.val by ring,mul_pow,pow_succ (-1 : K) n,div_div_eq_mul_div]
    ring
  have hline := d.axisLine_unit v Φ b (-u)
  change ν (-u.val) = _ at hline
  rw [hb,harg,Complex.ofReal_inv,div_inv_eq_mul] at hline
  have hs := d.marginal_symbol_sign v x u
  change d.symbol v a e * d.symbol v (-1) e = d.symbol v (-1) b at hs
  have hsub := d.integral_local_mul v e⁻¹ (Φ.val.1 (e*a))
  dsimp only at hsub
  have hei : modulus F v e⁻¹.val = 1 := by cases v <;> simp [modulus,e,Units.val_pow_eq_pow_val]
  rw [hei,Complex.ofReal_one,div_one] at hsub
  have hmarg : d.marginal v Ω a = d.symbol v (-1) b * d.marginal v Φ (e*a) := by
    unfold marginal
    rw [hsq]
    change (∫ y, (d.symbol v a e * d.symbol v (-1) e) * Φ.val.1 (e*a) (y/e.val) ∂dx) = _
    rw [hs,integral_const_mul,← hsub]
    simp only [Units.val_inv_eq_inv_val,div_eq_inv_mul]
  have hn : (n : K) ≠ 0 := by
    simpa only [map_natCast,map_zero] using (diagonal F v).injective.ne (Nat.cast_ne_zero.mpr (NeZero.ne n) : (n:F) ≠ 0)
  have hN : 0 < N := by cases v <;> simp [modulus,hn,pow_pos,norm_pos_iff]
  have hroot : (Real.sqrt N : ℂ) * (Real.sqrt N : ℂ) = (N : ℂ) := by
    rw [← Complex.ofReal_mul,Real.mul_self_sqrt hN.le]
  change d.marginal v Ω a = k * _
  rw [hmarg,hhat,hline]
  dsimp only [k,m]
  rw [← hroot]
  field_simp [Complex.ofReal_ne_zero.mpr (modulus_ne_zero v x),
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos_of_pos hN).ne']

/-- Integration on a vertical line as a linear functional on Schwartz sections. -/
def marginalLinear (x : Kˣ) : d.schwartz v →ₗ[ℂ] ℂ where
  toFun Φ := d.marginal v Φ x
  map_add' Φ Ψ := integral_add (d.integrable_jacquet_slice v Φ x) (d.integrable_jacquet_slice v Ψ x)
  map_smul' c Φ := integral_const_mul c (Φ.val.1 x)

private def axisDensityLinear (x : Kˣ) : d.schwartz v →ₗ[ℂ] (K → ℂ) where
  toFun Φ := d.axisDensity v Φ x
  map_add' Φ Ψ := by
    funext t
    by_cases ht : t = 0
    · subst t
      simp only [Pi.add_apply,axisDensity_zero,map_add]
      exact mul_add _ _ _
    · let u := Units.mk0 t ht
      change d.axisDensity v (Φ+Ψ) x u.val = d.axisDensity v Φ x u.val + d.axisDensity v Ψ x u.val
      simp only [d.axisDensity_unit]
      exact mul_add _ _ _
  map_smul' c Φ := by
    funext t
    by_cases ht : t = 0
    · subst t
      simp only [Pi.smul_apply,axisDensity_zero,map_smul,smul_eq_mul,RingHom.id_apply]
      exact mul_left_comm _ _ _
    · let u := Units.mk0 t ht
      change d.axisDensity v (c • Φ) x u.val = c * d.axisDensity v Φ x u.val
      simp only [d.axisDensity_unit]
      exact mul_left_comm _ _ _

section Finite
variable (p : Prime F)
local notation "vp" => (Sum.inr p : Place F)
local notation "Kv" => LocalField F vp

private def finiteDensityHatLinear (x u : Kvˣ) : d.schwartz vp →ₗ[ℂ] ℂ where
  toFun Φ := d.hat vp (d.axisDensity vp Φ x) u.val
  map_add' Φ Ψ := by
    let D := d.axisDensityLinear vp x
    change d.hat vp (D (Φ + Ψ)) u.val = _
    rw [map_add]
    unfold hat
    simp only [Pi.add_apply,add_mul]
    exact integral_add (d.integrable_phase vp ((d.axisDensity_finite_bruhat p Φ x).integrable d) _)
      (d.integrable_phase vp ((d.axisDensity_finite_bruhat p Ψ x).integrable d) _)
  map_smul' c Φ := by
    let D := d.axisDensityLinear vp x
    change d.hat vp (D (c • Φ)) u.val = _
    rw [map_smul]
    unfold hat
    simp only [Pi.smul_apply,smul_eq_mul,mul_assoc,integral_const_mul,RingHom.id_apply]
    rfl

/-- The converse marginal identity on the entire finite-place Schwartz
space under nondegeneracy of the Hilbert pairing. The transform used here
is the one constructed directly from its chart integrals. -/
theorem finite_reverse_marginal (hpow : ∀ a : Kvˣ, (∀ u, d.symbol vp u a = 1) → ∃ b, b^n = a)
    (Φ : d.schwartz vp) (x u : Kvˣ) :
    d.marginal vp (d.finiteSchwartzTransform p hpow Φ) (u^n*x) =
      (Real.sqrt (modulus F vp (n : Kv)) : ℂ)⁻¹ * d.hat vp (d.axisDensity vp Φ x) u.val := by
  let L := d.finiteSchwartzTransform p hpow
  let A := (d.marginalLinear vp (u^n*x)).comp L
  let B := (Real.sqrt (modulus F vp (n : Kv)) : ℂ)⁻¹ • d.finiteDensityHatLinear p x u
  suffices h : A = B from DFunLike.congr_fun h Φ
  apply LinearMap.ext_on (Submodule.span_span_coe_preimage (R := ℂ)
    (s := d.testSet vp ∪ d.integralTransform vp '' d.testSet vp))
  rintro ⟨f,hf⟩ (ht | ⟨g,hg,rfl⟩)
  · exact d.finite_reverse_marginal_on_test p ⟨f,hf⟩ ht x u hpow
  · let Γ : d.schwartz vp := ⟨g,Submodule.subset_span (Or.inl hg)⟩
    exact d.reverse_marginal_transformTest_of_square vp Γ hg (L Γ) (L (L Γ)) rfl
      (d.finiteSchwartzTransform_square p hpow Γ) x u

/-- At tame places the reverse marginal formula holds on every section. -/
theorem tame_reverse_marginal (hp : p.asIdeal.absNorm.Coprime n) (Φ : d.schwartz vp) (x u : Kvˣ) :
    d.marginal vp (d.fourier vp Φ) (u^n*x) =
      (Real.sqrt (modulus F vp (n : Kv)) : ℂ)⁻¹ * d.hat vp (d.axisDensity vp Φ x) u.val := by
  let hpow := fun a => (d.tame_symbol_radical p hp a).mp
  have he : d.fourier vp Φ = d.finiteSchwartzTransform p hpow Φ := Subtype.ext (d.fourier_apply vp Φ)
  rw [he]
  exact d.finite_reverse_marginal p hpow Φ x u

omit [NeZero n] in
/-- A continuous compactly supported function at a finite place is
Schwartz–Bruhat if its ordinary Fourier transform is Schwartz–Bruhat. -/
theorem finite_bruhat_of_hat {f : Kv → ℂ} (hc : Continuous f) (hs : HasCompactSupport f)
    (hh : Bruhat vp (d.hat vp f)) : Bruhat vp f := by
  let g := d.hat vp (d.hat vp f)
  have hg := d.hat_finite_bruhat p hh
  have hr : Bruhat vp (fun t => g (-t)) :=
    ⟨hg.1.comp_continuous continuous_neg,hg.2.comp_homeomorph (Homeomorph.neg Kv)⟩
  let F₀ : C_c(Kv,ℂ) := ⟨⟨f,hc⟩,hs⟩
  let G₀ : C_c(Kv,ℂ) := ⟨⟨fun t => g (-t),hr.1.continuous⟩,hr.2⟩
  have eqn : F₀ = G₀ := by
    apply d.hat_injective_compact vp
    funext u
    have aff := d.hat_affine vp g 0 u (-1)
    have inv := d.hat_hat_finite p hh (-u)
    change d.hat vp g (-u) = _ at inv
    simpa only [G₀,F₀,CompactlySupportedContinuousMap.coe_mk,ContinuousMap.coe_mk,
      sub_zero,Units.val_neg,Units.val_one,mul_neg_one,div_neg,div_one,modulus,norm_neg,norm_one,
      Complex.ofReal_one,mul_zero,d.character.localValue_zero,mul_one,inv,neg_neg] using aff.symm
  exact (show f = (fun t => g (-t)) from congrArg DFunLike.coe eqn) ▸ hr

private theorem finite_axisLine_compact (Φ : d.schwartz vp) (y : Kvˣ) :
    HasCompactSupport (d.axisLine vp Φ y) := by
  letI : NontriviallyNormedField (p.adicCompletion F) := FinitePlace.nontriviallyNormedCompletion p
  letI : ProperSpace Kv := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace (p.adicCompletion F)
  obtain ⟨S,hS,hout⟩ := (d.finite_germs p Φ).2.1
  obtain ⟨R,hR⟩ := hS.isBounded.exists_norm_le
  apply HasCompactSupport.intro (isCompact_closedBall (0 : Kv) (max 1 (R*‖y.val‖)))
  intro t ht
  have H : max 1 (R*‖y.val‖) < ‖t‖ := by simpa only [mem_closedBall_zero_iff,not_le] using ht
  have ht₁ := (le_max_left ..).trans_lt H
  let u := Units.mk0 t (norm_pos_iff.mp (zero_lt_one.trans ht₁))
  have hbig : R < ‖(u^n/y).val‖ := by
    rw [Units.val_div_eq_div_val,norm_div,Units.val_pow_eq_pow_val,norm_pow,lt_div_iff₀ (norm_pos_iff.mpr y.ne_zero)]
    exact ((le_max_right ..).trans_lt H).trans_le (le_self_pow₀ ht₁.le (NeZero.ne n))
  change d.axisLine vp Φ y u.val = 0
  rw [d.axisLine_unit]
  have hz (b : Kv) : Φ.val.1 (u^n/y) b = 0 := by
    have hn : ((u^n/y).val,b) ∉ S := fun h => hbig.not_ge
      ((le_max_left ‖(u^n/y).val‖ ‖b‖).trans (hR ((u^n/y).val,b) h))
    simpa only [xChart,dif_pos (u^n/y).ne_zero,Units.mk0_val] using (hout _ hn).1
  simp only [marginal,hz,integral_zero,mul_zero]

/-- The first Schwartz marginal kernel at every finite place, including
wild places. The proof uses only that the prescribed integral transform
of this particular section belongs to the local Schwartz space. -/
theorem finite_axisLine_bruhat_of_transform (Φ Ψ : d.schwartz vp)
    (hΨ : Ψ.val = d.integralTransform vp Φ.val) (y : Kvˣ) :
    Bruhat vp (d.axisLine vp Φ y) := by
  have hc : Continuous (d.axisLine vp Φ y) := (d.finite_radon_convergence p Φ).2.2.2.comp
    (f := fun t : Kv => (((0 : Kv),y),t)) (continuous_const.prodMk continuous_id)
  have hs := d.finite_axisLine_compact p Φ y
  apply d.finite_bruhat_of_hat p hc hs
  letI : (selfDual F d.character vp).IsAddHaarMeasure := (existsUnique_selfDual F d.character vp).exists.choose_spec.1
  let x := -1/y
  have hx : -1/x = y := div_div_cancel _ _
  have eqn := d.axisDensity_transform_eq_hat vp Φ Ψ hΨ x (hx ▸ hc.integrable_of_hasCompactSupport hs)
  rw [hx] at eqn
  let c := ((modulus F vp (n:Kv) : ℂ) / (modulus F vp x.val : ℂ)) * (Real.sqrt (modulus F vp (n:Kv)) : ℂ)⁻¹
  have hn : (n : Kv) ≠ 0 := by
    simpa only [map_natCast,map_zero] using (diagonal F vp).injective.ne (Nat.cast_ne_zero.mpr (NeZero.ne n) : (n:F) ≠ 0)
  have hc₀ : c ≠ 0 := by
    apply mul_ne_zero (div_ne_zero (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hn))
      (Complex.ofReal_ne_zero.mpr (modulus_ne_zero vp x)))
    exact inv_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos_of_pos (norm_pos_iff.mpr hn)).ne')
  have hh : d.hat vp (d.axisLine vp Φ y) = fun t => c⁻¹ * d.axisDensity vp Ψ x t := by
    funext t
    rw [eqn]
    exact (inv_mul_cancel_left₀ hc₀ _).symm
  rw [hh]
  exact Bruhat.const_mul vp (d.axisDensity_finite_bruhat p Ψ x) _

theorem finite_axisLine_bruhat (Φ : d.schwartz vp) (y : Kvˣ) : Bruhat vp (d.axisLine vp Φ y) :=
  d.finite_axisLine_bruhat_of_transform p Φ (d.fourier vp Φ) (d.fourier_apply vp Φ) y

/-- Appendix A's marginal kernels and converse Fourier identity for the
transform constructed under Hilbert nondegeneracy. -/
theorem finite_schwartz_marginal_kernels (hpow : ∀ a : Kvˣ, (∀ u, d.symbol vp u a = 1) → ∃ b, b^n = a)
    (Φ : d.schwartz vp) (x y : Kvˣ) :
    let L := d.finiteSchwartzTransform p hpow
    Bruhat vp (d.axisLine vp Φ y) ∧ Bruhat vp (d.axisDensity vp Φ x) ∧
    ∀ u : Kvˣ, d.marginal vp (L Φ) (u^n*x) =
      (Real.sqrt (modulus F vp (n : Kv)) : ℂ)⁻¹ * d.hat vp (d.axisDensity vp Φ x) u.val :=
  ⟨d.finite_axisLine_bruhat_of_transform p Φ (d.finiteSchwartzTransform p hpow Φ) rfl y,
    d.axisDensity_finite_bruhat p Φ x,d.finite_reverse_marginal p hpow Φ x⟩

/-- Both Schwartz–Bruhat kernels and the pointwise converse Fourier identity
of Appendix A for every tame finite place and every Schwartz section. -/
theorem tame_schwartz_marginal_kernels (hp : p.asIdeal.absNorm.Coprime n) (Φ : d.schwartz vp) (x y : Kvˣ) :
    Bruhat vp (d.axisLine vp Φ y) ∧ Bruhat vp (d.axisDensity vp Φ x) ∧
    ∀ u : Kvˣ, d.marginal vp (d.fourier vp Φ) (u^n*x) =
      (Real.sqrt (modulus F vp (n : Kv)) : ℂ)⁻¹ * d.hat vp (d.axisDensity vp Φ x) u.val := by
  let hpow := fun a => (d.tame_symbol_radical p hp a).mp
  have he : d.fourier vp Φ = d.finiteSchwartzTransform p hpow Φ := Subtype.ext (d.fourier_apply vp Φ)
  rw [he]
  exact d.finite_schwartz_marginal_kernels p hpow Φ x y

end Finite
end MetaplecticPoisson.Datum
