import MetaplecticSummation.RationalEvaluation
import MetaplecticSummation.LocalPowerClasses
import MetaplecticSummation.Marginals.RootSum
import MetaplecticSummation.Hilbert.ArchimedeanRadical

/-! The Hilbert pairing on the local and adelic power classes of Appendix B. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField Filter
open Classical

private abbrev Powers (n : ℕ) (G : Type*) [CommGroup G] := (powMonoidHom n : G →* G).range

private def descendPowers {G M : Type*} [CommGroup G] [CommGroup M] (n : ℕ)
    (f : G →* M) (h : ∀ x, f x ^ n = 1) : G ⧸ Powers n G →* M :=
  QuotientGroup.lift _ f (by
    rintro _ ⟨x,rfl⟩
    exact (f.map_pow x n).trans (h x))

private def descendPairing {G M : Type*} [CommGroup G] [CommGroup M] (n : ℕ)
    (B : G →* G →* M) (h : ∀ a b, B a b ^ n = 1) :
    G ⧸ Powers n G →* G ⧸ Powers n G →* M := by
  let R : G →* G ⧸ Powers n G →* M := MonoidHom.mk'
    (fun a => descendPowers n (B a) (h a)) (by
      intro a b
      apply MonoidHom.ext
      intro c
      induction c using QuotientGroup.induction_on with | _ c => exact DFunLike.congr_fun (B.map_mul a b) c)
  apply descendPowers n R
  intro a
  apply MonoidHom.ext
  intro c
  induction c using QuotientGroup.induction_on with | _ c => exact h a c

private def mapPowerClasses {G H : Type*} [CommGroup G] [CommGroup H] (n : ℕ) (f : G →* H) :
    G ⧸ Powers n G →* H ⧸ Powers n H :=
  QuotientGroup.map _ _ f (by rintro _ ⟨x,rfl⟩; exact ⟨f x,(f.map_pow x n).symm⟩)

abbrev GlobalClass (n : ℕ) (F : Type) [Field F] := Fˣ ⧸ (powMonoidHom n : Fˣ →* Fˣ).range
abbrev AdelicPowerClass (n : ℕ) (F : Type) [Field F] [NumberField F] :=
  (Adeles F)ˣ ⧸ (powMonoidHom n : (Adeles F)ˣ →* (Adeles F)ˣ).range

variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

def localClassPairing (v : Place F) : PowerClass n v →* PowerClass n v →* ℂˣ :=
  descendPairing n (d.unitPairing v) (d.unitPairing_pow v)

@[simp] theorem localClassPairing_mk (v : Place F) (a b : (LocalField F v)ˣ) :
    d.localClassPairing v (QuotientGroup.mk a) (QuotientGroup.mk b) = d.unitPairing v a b := rfl

private abbrev componentUnit (v : Place F) := Units.map (componentHom v).toMonoidHom

private theorem idelePairing_support (a b : (Adeles F)ˣ) :
    Function.HasFiniteMulSupport (fun v => d.unitPairing v (componentUnit v a) (componentUnit v b)) := by
  apply eventually_cofinite.mp
  apply eventually_place_of_finite
  filter_upwards [eventually_tame (F := F) (n := n),eventually_unit_component a,eventually_unit_component b]
    with p ht ha hb
  exact d.unitPairing_tame_units p ht _ _ ha hb

/-- Product of the local Hilbert symbols of two ideles. -/
def idelePairing : (Adeles F)ˣ →* (Adeles F)ˣ →* ℂˣ :=
  MonoidHom.mk' (fun a => MonoidHom.mk' (fun b =>
    ∏ᶠ v, d.unitPairing v (componentUnit v a) (componentUnit v b)) (by
      intro b c
      simp only [map_mul]
      exact finprod_mul_distrib (d.idelePairing_support a b) (d.idelePairing_support a c))) (by
    intro a b
    apply MonoidHom.ext
    intro c
    change (∏ᶠ v, d.unitPairing v (componentUnit v (a*b)) (componentUnit v c)) = _
    simp only [map_mul,MonoidHom.mul_apply]
    exact finprod_mul_distrib (d.idelePairing_support a c) (d.idelePairing_support b c))

/-- The product symbol descends in both variables to ideles modulo powers. -/
def adelicClassPairing : AdelicPowerClass n F →* AdelicPowerClass n F →* ℂˣ :=
  descendPairing n d.idelePairing (by
    intro a b
    change (powMonoidHom n : ℂˣ →* ℂˣ) (∏ᶠ v, d.unitPairing v (componentUnit v a) (componentUnit v b)) = 1
    rw [MonoidHom.map_finprod _ (d.idelePairing_support a b)]
    simp only [powMonoidHom_apply,d.unitPairing_pow,finprod_one])

def rationalClassMap (n : ℕ) (F : Type) [Field F] [NumberField F] :
    GlobalClass n F →* AdelicPowerClass n F :=
  mapPowerClasses n (Units.map (algebraMap F (Adeles F)).toMonoidHom)

private theorem componentUnit_rational (v : Place F) (x : Fˣ) :
    componentUnit v (Units.map (algebraMap F (Adeles F)).toMonoidHom x) = atPlace v x := by
  cases v <;> rfl

/-- Rational power classes annihilate one another for the adelic pairing. -/
theorem rationalClassPairing_eq_one (a b : GlobalClass n F) :
    d.adelicClassPairing (rationalClassMap n F a) (rationalClassMap n F b) = 1 := by
  induction a using QuotientGroup.induction_on with | _ a => _
  induction b using QuotientGroup.induction_on with | _ b => _
  let H (v : Place F) := d.family v (atPlace v a) (atPlace v b)
  change (∏ᶠ v, d.unitPairing v _ _) = 1
  simp only [componentUnit_rational]
  change (∏ᶠ v, d.embedding (H v)) = 1
  rw [← MonoidHom.map_finprod _ (eventually_cofinite.mp (d.family_spec.unramified a b))]
  exact (congrArg d.embedding (d.family_spec.reciprocity a b)).trans d.embedding.map_one

/-- Localization on the quotient of the ideles by n-th powers. -/
def adelicClassAt (n : ℕ) (v : Place F) : AdelicPowerClass n F →* PowerClass n v :=
  mapPowerClasses n (componentUnit v)

private theorem component_ext {a b : Adeles F} (h : ∀ v, component a v = component b v) : a = b :=
  Prod.ext (funext fun w => h (.inl w)) (Subtype.ext (funext fun p => h (.inr p)))

private def adeleOfUnits (a : ∀ v : Place F, (LocalField F v)ˣ)
    (h : ∀ᶠ p in cofinite, ‖(a (.inr p)).val‖ = 1) : Adeles F :=
  (fun w => (a (.inl w)).val, ⟨fun p => (a (.inr p)).val, h.mono fun p hp =>
    (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F p).mpr
      (Valued.toNormedField.norm_le_one_iff.mp hp.le)⟩)

/-- Local roots of an idele assemble to an idele root, since their norms
are one at every finite place where the original idele has norm one. -/
theorem adelicClass_eq_one_of_local (x : AdelicPowerClass n F)
    (h : ∀ v, adelicClassAt n v x = 1) : x = 1 := by
  induction x using QuotientGroup.induction_on with | _ a => _
  have H (v : Place F) : ∃ b : (LocalField F v)ˣ, b ^ n = componentUnit v a :=
    (QuotientGroup.eq_one_iff _).mp (h v)
  choose b hb using H
  have hu : ∀ᶠ p in cofinite, ‖(b (.inr p)).val‖ = 1 := by
    filter_upwards [eventually_unit_component a] with p hp
    apply (pow_eq_one_iff_of_nonneg (norm_nonneg _) (NeZero.ne n)).mp
    exact ((norm_pow _ _).symm.trans (congrArg (fun u => ‖Units.val u‖) (hb (.inr p)))).trans hp
  let B := adeleOfUnits b hu
  let I := adeleOfUnits (fun v => (b v)⁻¹) (hu.mono fun p hp => by
    rw [Units.val_inv_eq_inv_val,norm_inv,hp,inv_one])
  have hB (v) : component B v = (b v).val := by cases v <;> rfl
  have hI (v) : component I v = ((b v)⁻¹).val := by cases v <;> rfl
  have hBI : B * I = 1 := by
    apply component_ext
    intro v
    change componentHom v (B * I) = componentHom v 1
    rw [map_mul,map_one]
    exact (congrArg₂ (· * ·) (hB v) (hI v)).trans (b v).val_inv
  apply (QuotientGroup.eq_one_iff _).mpr
  refine ⟨⟨B,I,hBI,(mul_comm _ _).trans hBI⟩,Units.ext (component_ext fun v => ?_)⟩
  change componentHom v (B^n) = component a v
  rw [map_pow]
  exact (congrArg (· ^ n) (hB v)).trans (congrArg Units.val (hb v))

/-- The local Hilbert pairing of power classes has trivial right kernel. -/
theorem localClassPairing_right_kernel (v : Place F) (c : PowerClass n v)
    (h : ∀ a, d.localClassPairing v a c = 1) : c = 1 := by
  induction c using QuotientGroup.induction_on with | _ c => _
  apply (QuotientGroup.eq_one_iff _).mpr
  have H (u : (LocalField F v)ˣ) : d.symbol v u c = 1 :=
    congrArg Units.val (h (QuotientGroup.mk u))
  cases v with
  | inr p => exact d.finite_symbol_power p c H
  | inl w =>
    by_cases hw : w.IsReal
    · exact d.real_symbol_power w hw c H
    · exact complex_unit_power w (InfinitePlace.not_isReal_iff_isComplex.mp hw) c

/-- The subgroup orthogonal to the diagonal rational power classes. -/
def rationalOrthogonal : Subgroup (AdelicPowerClass n F) :=
  ⨅ a : GlobalClass n F, (d.adelicClassPairing (rationalClassMap n F a)).ker

theorem rationalClass_le_orthogonal : (rationalClassMap n F).range ≤ d.rationalOrthogonal := by
  rintro _ ⟨b,rfl⟩
  exact Subgroup.mem_iInf.mpr fun a => d.rationalClassPairing_eq_one a b

/-- A class orthogonal to the rational units and trivial outside a finite
set of places is trivial. Weak approximation isolates each place in that set. -/
theorem eq_one_of_orthogonal_of_finite_support (x : AdelicPowerClass n F)
    (hx : x ∈ d.rationalOrthogonal) (hs : ∀ᶠ v in cofinite, adelicClassAt n v x = 1) : x = 1 := by
  classical
  induction x using QuotientGroup.induction_on with | _ x => _
  let S := (eventually_cofinite.mp hs).toFinset
  have outside (v : Place F) (hv : v ∉ S) : adelicClassAt n v (QuotientGroup.mk x) = 1 := by
    simpa [S] using hv
  apply adelicClass_eq_one_of_local
  intro v
  by_cases hv : v ∈ S
  · let j : S := ⟨v,hv⟩
    let P (A : (i : S) → (LocalField F i.val)ˣ) :=
      ∏ i : S, d.unitPairing i.val (A i) (componentUnit i.val x)
    have hc : Continuous P := by
      apply continuous_finsetProd
      intro i _
      let f (A : (k : S) → (LocalField F k.val)ˣ) := (A i, componentUnit i.val x)
      have hf : Continuous f := (continuous_apply i).prodMk continuous_const
      exact (d.locallyConstant_unitPairing i.val).continuous.comp hf
    have hP : P = fun _ => 1 := by
      apply (denseRange_unitDiagonal S j).equalizer hc continuous_const
      funext a
      have hr := Subgroup.mem_iInf.mp hx (QuotientGroup.mk a : GlobalClass n F)
      change (∏ᶠ v, d.unitPairing v (componentUnit v (Units.map (algebraMap F (Adeles F)).toMonoidHom a))
        (componentUnit v x)) = 1 at hr
      simp only [componentUnit_rational] at hr
      rw [finprod_eq_prod_of_mulSupport_subset (s := S) _ (by
        intro w hw
        by_contra hn
        apply hw
        change d.localClassPairing w (QuotientGroup.mk (atPlace w a)) (adelicClassAt n w (QuotientGroup.mk x)) = 1
        rw [outside w hn,map_one]),← Finset.prod_attach] at hr
      exact hr
    apply d.localClassPairing_right_kernel
    intro c
    induction c using QuotientGroup.induction_on with | _ u => _
    let A := Function.update (1 : (i : S) → (LocalField F i.val)ˣ) j u
    have h := congrFun hP A
    change (∏ i : S, d.unitPairing i.val (A i) (componentUnit i.val x)) = 1 at h
    rw [Finset.prod_eq_single j] at h
    · change d.unitPairing j.val u (componentUnit j.val x) = 1
      simpa only [A,Function.update_self] using h
    · intro i _ hi
      simp only [A,Function.update_of_ne hi,Pi.one_apply,map_one,MonoidHom.one_apply]
    · simp
  · exact outside v hv

/-- Within the orthogonal complement, recognizing a rational class only
requires matching its local power classes at cofinitely many places. -/
theorem mem_rationalClass_iff_eventually (x : AdelicPowerClass n F) (hx : x ∈ d.rationalOrthogonal) :
    x ∈ (rationalClassMap n F).range ↔
      ∃ a : GlobalClass n F, ∀ᶠ v in cofinite, adelicClassAt n v x = adelicClassAt n v (rationalClassMap n F a) := by
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨a,.of_forall fun _ => rfl⟩
  · rintro ⟨a,ha⟩
    have hr := d.rationalClass_le_orthogonal (show rationalClassMap n F a ∈ (rationalClassMap n F).range from ⟨a,rfl⟩)
    have h := d.eq_one_of_orthogonal_of_finite_support (x / rationalClassMap n F a)
      (d.rationalOrthogonal.div_mem hx hr) (ha.mono fun v hv => by rw [map_div,hv,div_self'])
    exact ⟨a,(div_eq_one.mp h).symm⟩

/-- Evaluation of an adelic character on a principal idele. -/
theorem rationalClassPairing_eq_finprod (a : Fˣ) (x : AdelicPowerClass n F) :
    d.adelicClassPairing (rationalClassMap n F (QuotientGroup.mk a)) x =
      ∏ᶠ v, d.localClassPairing v (QuotientGroup.mk (atPlace v a)) (adelicClassAt n v x) := by
  induction x using QuotientGroup.induction_on with | _ x => _
  change (∏ᶠ v, d.unitPairing v (componentUnit v (Units.map (algebraMap F (Adeles F)).toMonoidHom a))
    (componentUnit v x)) = _
  simp only [componentUnit_rational]
  rfl

/-- At a tame prime a unit class is detected by pairing with any uniformizer. -/
theorem unitClass_eq_one_of_uniformizer (p : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (ht : p.asIdeal.absNorm.Coprime n) (π u : (LocalField F (.inr p))ˣ)
    (hπ : ‖π.val‖ = (p.asIdeal.absNorm : ℝ)⁻¹) (hu : ‖u.val‖ = 1)
    (h : d.unitPairing (.inr p) π u = 1) :
    (QuotientGroup.mk u : PowerClass n (.inr p)) = 1 := by
  apply d.localClassPairing_right_kernel
  intro a
  induction a using QuotientGroup.induction_on with | _ a => _
  obtain ⟨j,hj⟩ : ∃ j : ℤ, ‖a.val‖ = (p.asIdeal.absNorm : ℝ)^j := norm_zpow_residue_card p a
  let b := a / π^(-j)
  have hq : (p.asIdeal.absNorm : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm p)).ne'
  have hb : ‖b.val‖ = 1 := by
    simp [b,Units.val_zpow_eq_zpow_val,norm_zpow,hπ,hj,zpow_ne_zero _ hq]
  have he : a = b * π^(-j) := (div_mul_cancel ..).symm
  change (d.unitPairing (.inr p)).flip u a = 1
  rw [he,map_mul,map_zpow]
  change d.unitPairing (.inr p) b u * d.unitPairing (.inr p) π u ^ (-j) = 1
  rw [d.unitPairing_tame_units p ht b u hb hu,h,one_zpow,one_mul]

/-- If rational prime generators exist outside S, an orthogonal idele
class represented by units there is determined by its components on S. -/
theorem eq_one_of_orthogonal_of_unit_outside (S : Finset (Place F)) (x : AdelicPowerClass n F)
    (hx : x ∈ d.rationalOrthogonal) (hS : ∀ v ∈ S, adelicClassAt n v x = 1)
    (hinf : ∀ w : InfinitePlace F, Sum.inl w ∈ S)
    (ht : ∀ p : IsDedekindDomain.HeightOneSpectrum (𝓞 F), Sum.inr p ∉ S → p.asIdeal.absNorm.Coprime n)
    (hu : ∀ p : IsDedekindDomain.HeightOneSpectrum (𝓞 F), Sum.inr p ∉ S →
      ∃ u : (LocalField F (.inr p))ˣ, ‖u.val‖ = 1 ∧ QuotientGroup.mk u = adelicClassAt n (.inr p) x)
    (hg : ∀ p : IsDedekindDomain.HeightOneSpectrum (𝓞 F), Sum.inr p ∉ S →
      ∃ a : Fˣ, ‖(atPlace (.inr p) a).val‖ = (p.asIdeal.absNorm : ℝ)⁻¹ ∧
        ∀ q, Sum.inr q ∉ S → q ≠ p → ‖(atPlace (.inr q) a).val‖ = 1) : x = 1 := by
  apply adelicClass_eq_one_of_local
  intro v
  by_cases hv : v ∈ S
  · exact hS v hv
  cases v with
  | inl w => exact False.elim (hv (hinf w))
  | inr p =>
    obtain ⟨u,hu₁,hu₂⟩ := hu p hv
    obtain ⟨a,ha,hq⟩ := hg p hv
    let f (v : Place F) := d.localClassPairing v (QuotientGroup.mk (atPlace v a)) (adelicClassAt n v x)
    have hf : ∀ v ≠ Sum.inr p, f v = 1 := by
      intro v hne
      by_cases hmem : v ∈ S
      · simp only [f,hS v hmem,map_one]
      cases v with
      | inl w => exact False.elim (hmem (hinf w))
      | inr q =>
        obtain ⟨z,hz,he⟩ := hu q hmem
        change d.localClassPairing (.inr q) _ _ = 1
        rw [← he,localClassPairing_mk]
        exact d.unitPairing_tame_units q (ht q hmem) _ z (hq q hmem (fun e => hne (congrArg Sum.inr e))) hz
    have one : (∏ᶠ v, f v) = 1 :=
      (d.rationalClassPairing_eq_finprod a x).symm.trans (Subgroup.mem_iInf.mp hx (QuotientGroup.mk a))
    rw [finprod_eq_single f _ hf] at one
    change d.localClassPairing (.inr p) _ (adelicClassAt n (.inr p) x) = 1 at one
    rw [← hu₂,localClassPairing_mk] at one
    exact hu₂ ▸ d.unitClass_eq_one_of_uniformizer p (ht p hv) _ _ ha hu₁ one

end MetaplecticPoisson.Datum
