import MetaplecticSummation.BasicWeights

/-! Local Gauss–Ramanujan sums in §10.3. -/

noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField MeasureTheory Set
open scoped Pointwise
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

def residueTerm (p : Prime F) (c : (p.adicCompletion F)ˣ)
    (a : p.adicCompletion F) : ℂ := by
  classical
  exact if ha : a ≠ 0 then d.symbol (.inr p) c (Units.mk0 a ha) *
    d.character.localValue F (.inr p) (-a / (c : p.adicCompletion F)) else 0

/-- The local Gauss–Ramanujan sum of §10.3 with the negative additive phase. -/
def localGauss (p : Prime F) (c : (p.adicCompletion F)ˣ) : ℂ := by
  classical
  let O := p.adicCompletionIntegers F
  exact if ‖(c : p.adicCompletion F)‖ = 1 then 1 else
    if hc : (c : p.adicCompletion F) ∈ O then
      let c₀ : O := ⟨_,hc⟩
      ∑ᶠ u : (O ⧸ Ideal.span {c₀})ˣ,
        let a : O := Quotient.out (u : O ⧸ Ideal.span {c₀})
        d.residueTerm p c a.val
    else 0

section ResidueRing
variable (p : Prime F)
local notation "K" => p.adicCompletion F
local notation "O" => p.adicCompletionIntegers F

private theorem span_iff_div_mem (c x : O) (hc : (c : K) ≠ 0) :
    x ∈ Ideal.span {c} ↔ (x : K) / c ∈ O := by
  rw [Ideal.mem_span_singleton]
  constructor
  · rintro ⟨k,rfl⟩
    change (c : K) * k / c ∈ O
    rw [mul_div_cancel_left₀ _ hc]
    exact k.property
  · intro h
    exact ⟨⟨_,h⟩,Subtype.ext (by change (x : K) = c * ((x : K) / c); field_simp)⟩

theorem finite_local_residues (c : O) (hc : (c : K) ≠ 0) : Finite (O ⧸ Ideal.span {c}) := by
  apply AddSubgroup.quotient_finite_of_isOpen (Ideal.span {c}).toAddSubgroup
  have he : ((Ideal.span {c}).toAddSubgroup : Set O) =
      (fun x : O => (x : K) / c) ⁻¹' (O : Set K) := Set.ext fun x => span_iff_div_mem p c x hc
  rw [he]
  exact (FinitePlace.isOpen_adicCompletionIntegers p).preimage (continuous_subtype_val.div_const _)

/-- Congruence modulo c is the condition that the difference belongs to cO. -/
theorem localResidues_eq_iff (c a b : O) (hc : (c : K) ≠ 0) :
    Ideal.Quotient.mk (Ideal.span {c}) a = Ideal.Quotient.mk _ b ↔
      ((a : K) - b) / c ∈ O :=
  Ideal.Quotient.eq.trans (span_iff_div_mem p c (a-b) hc)

theorem localResidues_isUnit_iff (c a : O) (hc : ‖(c : K)‖ < 1) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {c}) a) ↔ ‖(a : K)‖ = 1 := by
  let I : Ideal O := Ideal.span {c}
  have hI : I ≠ ⊤ := fun he => hc.ne ((localInteger_isUnit_iff p c).mp (Ideal.span_singleton_eq_top.mp he))
  letI : Nontrivial (O ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  letI : IsLocalHom (Ideal.Quotient.mk I) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  exact (isUnit_map_iff (Ideal.Quotient.mk I) a).trans (localInteger_isUnit_iff p a)

theorem residueTerm_congr (hp : p.asIdeal.absNorm.Coprime n)
    (hψ : ∀ x : K, ‖x‖ ≤ 1 → d.character.localValue F (.inr p) x = 1)
    (c : Kˣ) (hc : ‖c.val‖ < 1) (a b : K) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hab : (a-b)/c.val ∈ O) : d.residueTerm p c a = d.residueTerm p c b := by
  have ha0 := norm_ne_zero_iff.mp (ha ▸ one_ne_zero)
  have hb0 := norm_ne_zero_iff.mp (hb ▸ one_ne_zero)
  have hsub : ‖a-b‖ < 1 := by
    have h := (mem_localIntegers_iff p _).mp hab
    rw [norm_div,div_le_one (norm_pos_iff.mpr c.ne_zero)] at h
    exact h.trans_lt hc
  have he : -a / c.val = -b / c.val + -((a-b)/c.val) := by ring
  have hadd := d.character.localValue_add (.inr p) (-b/c.val) (-((a-b)/c.val))
  have htriv := hψ (-((a-b)/c.val)) (by rw [norm_neg]; exact (mem_localIntegers_iff p _).mp hab)
  simp only [residueTerm,dif_pos ha0,dif_pos hb0]
  apply congrArg₂ (· * ·) (d.tame_symbol_congr p hp c (Units.mk0 a ha0) (Units.mk0 b hb0) hb hsub)
  exact (congrArg (d.character.localValue F (.inr p)) he).trans (hadd.trans (by rw [htriv,mul_one]))

/-- A residue class as a compact open subset of the additive local field. -/
def localCoset (c : Kˣ) (a : K) : Set K := {x | (x-a)/c.val ∈ O}

private theorem localCoset_eq (c : Kˣ) (a : K) :
    localCoset p c a = a +ᵥ (c • (O : Set K)) := by
  ext x
  constructor
  · intro hx
    exact ⟨c.val*((x-a)/c.val),⟨(x-a)/c.val,hx,rfl⟩,by
      change a + c.val*((x-a)/c.val) = x
      field_simp; ring⟩
  · rintro ⟨_,⟨t,ht,rfl⟩,rfl⟩
    change (a+c.val*t-a)/c.val ∈ O
    rwa [add_sub_cancel_left,mul_div_cancel_left₀ _ c.ne_zero]

private theorem mem_integer_of_mem_localCoset {c : Kˣ} (hc : c.val ∈ O) (a : O)
    {x : K} (hx : x ∈ localCoset p c a) : x ∈ O := by
  rw [localCoset_eq] at hx
  obtain ⟨_,⟨t,ht,rfl⟩,rfl⟩ := hx
  exact (p.adicCompletionIntegers F).toSubring.add_mem a.property ((p.adicCompletionIntegers F).toSubring.mul_mem hc ht)

local instance : MeasurableSpace K := borel _
local instance : BorelSpace K := ⟨rfl⟩

private theorem localCoset_volume (μ : Measure K) [μ.IsAddHaarMeasure] [μ.Regular] (c : Kˣ) (a : K) :
    μ.real (localCoset p c a) = ‖c.val‖ * μ.real (O : Set K) := by
  rw [localCoset_eq,Measure.real,measure_vadd,← distribHaarChar_mul μ,FinitePlace.haarChar_eq_nnnorm,
    ENNReal.toReal_mul,ENNReal.coe_toReal]
  rfl

/-- Each unit residue class contributes the volume of cO times its value. -/
theorem unit_residueTerm_integral (hp : p.asIdeal.absNorm.Coprime n)
    (hψ : ∀ x : K, ‖x‖ ≤ 1 → d.character.localValue F (.inr p) x = 1)
    (μ : Measure K) [μ.IsAddHaarMeasure] [μ.Regular] (c : Kˣ) (hc : ‖c.val‖ < 1) :
    Integrable (fun x : K => if ‖x‖ = 1 then d.residueTerm p c x else 0) μ ∧
    (∫ x, (if ‖x‖ = 1 then d.residueTerm p c x else 0) ∂μ) =
      (μ.real (O : Set K) : ℂ) * (‖c.val‖ : ℂ) * d.localGauss p c := by
  classical
  have hcO := (mem_localIntegers_iff p c.val).mpr hc.le
  let C : O := ⟨c.val,hcO⟩
  let I : Ideal O := Ideal.span {C}
  let Q := O ⧸ I
  let q := Ideal.Quotient.mk I
  letI : Finite Q := finite_local_residues p C c.ne_zero
  letI : Fintype Qˣ := Fintype.ofFinite _
  let r (u : Qˣ) : O := Quotient.out u.val
  have hr (u : Qˣ) : q (r u) = u.val := Quotient.out_eq _
  have hu (u : Qˣ) : ‖((r u : O) : K)‖ = 1 := (localResidues_isUnit_iff p C (r u) hc).mp
    ((hr u).symm ▸ u.isUnit)
  let A (u : Qˣ) := localCoset p c (r u)
  let w (u : Qˣ) := d.residueTerm p c (r u)
  have hA (u : Qˣ) : MeasurableSet (A u) :=
    ((FinitePlace.isOpen_adicCompletionIntegers p).preimage
      ((continuous_id.sub (continuous_const (y := ((r u : O) : K)))).div_const c.val)).measurableSet
  have hk (u : Qˣ) : IsCompact (A u) := by
    change IsCompact (localCoset p c _)
    rw [localCoset_eq]
    exact ((FinitePlace.isCompact_adicCompletionIntegers p).smul c).vadd _
  have hmem (x : O) (u : Qˣ) : (x : K) ∈ A u ↔ q x = u.val := by
    rw [← hr u]
    exact (localResidues_eq_iff p C x (r u) c.ne_zero).symm
  have he (x : K) : (if ‖x‖ = 1 then d.residueTerm p c x else 0) =
      ∑ u : Qˣ, (A u).indicator (fun _ => w u) x := by
    by_cases hx : ‖x‖ = 1
    · let y : O := ⟨x,(mem_localIntegers_iff p x).mpr hx.le⟩
      have hy := (localResidues_isUnit_iff p C y hc).mpr hx
      let u : Qˣ := hy.unit
      have huq : q y = u.val := hy.unit_spec.symm
      have hxu := (hmem y u).mpr huq
      rw [if_pos hx,Finset.sum_eq_single u,indicator_of_mem hxu]
      · exact d.residueTerm_congr p hp hψ c hc x (r u) hx (hu u) hxu
      · intro v _ hv
        apply indicator_of_notMem
        exact fun h => hv (Units.ext (((hmem y v).mp h).symm.trans huq))
      · simp
    · rw [if_neg hx]
      symm
      apply Finset.sum_eq_zero
      intro u _
      apply indicator_of_notMem
      intro h
      let y : O := ⟨x, mem_integer_of_mem_localCoset p hcO (r u) h⟩
      exact hx ((localResidues_isUnit_iff p C y hc).mp (((hmem y u).mp h).symm ▸ u.isUnit))
  simp_rw [he]
  have hint (u : Qˣ) : Integrable ((A u).indicator (fun _ => w u)) μ :=
    (integrableOn_const (hk u).measure_ne_top).integrable_indicator (hA u)
  refine ⟨integrable_finsetSum _ (fun u _ => hint u), ?_⟩
  rw [integral_finsetSum _ (fun u _ => hint u)]
  simp only [integral_indicator (hA _), integral_const,measureReal_restrict_apply_univ,Complex.real_smul]
  have hvol (u : Qˣ) : μ.real (A u) = ‖c.val‖ * μ.real (O : Set K) := localCoset_volume p μ c _
  simp_rw [hvol, Complex.ofReal_mul, mul_comm (‖c.val‖ : ℂ) (μ.real (O : Set K) : ℂ)]
  rw [← Finset.mul_sum]
  unfold localGauss
  rw [if_neg hc.ne, dif_pos hcO, finsum_eq_sum_of_fintype]

/-- The primitive shell in the X-chart of the basic section, including
the additive phase in the Jacquet integral. -/
def primitiveJacquet (c : Kˣ) (y : K) : ℂ :=
  if ‖c.val‖ = 1 then (if ‖y‖ ≤ 1 then 1 else 0)
  else if ‖c.val‖ < 1 ∧ ‖y‖ = 1 then d.residueTerm p c y else 0

theorem primitiveJacquet_integral (hp : p.asIdeal.absNorm.Coprime n)
    (hψ : ∀ x : K, ‖x‖ ≤ 1 → d.character.localValue F (.inr p) x = 1)
    (μ : Measure K) [μ.IsAddHaarMeasure] [μ.Regular] (c : Kˣ) :
    Integrable (d.primitiveJacquet p c) μ ∧
    (∫ y, d.primitiveJacquet p c y ∂μ) = (μ.real (O : Set K) : ℂ) * (‖c.val‖ : ℂ) * d.localGauss p c := by
  rcases lt_trichotomy ‖c.val‖ 1 with h|h|h
  · have he : d.primitiveJacquet p c = fun x => if ‖x‖ = 1 then d.residueTerm p c x else 0 := by
      funext x; simp only [primitiveJacquet,if_neg h.ne,h,true_and]
    rw [he]
    exact d.unit_residueTerm_integral p hp hψ μ c h
  · have he : d.primitiveJacquet p c = (O : Set K).indicator (fun _ => (1:ℂ)) := by
      funext y
      by_cases hy : y ∈ O
      · rw [indicator_of_mem hy,primitiveJacquet,if_pos h,if_pos ((mem_localIntegers_iff p _).mp hy)]
      · rw [indicator_of_notMem hy,primitiveJacquet,if_pos h,if_neg (fun hh => hy ((mem_localIntegers_iff p _).mpr hh))]
    rw [he]
    have ho := (FinitePlace.isOpen_adicCompletionIntegers p).measurableSet
    refine ⟨(integrableOn_const (FinitePlace.isCompact_adicCompletionIntegers p).measure_ne_top).integrable_indicator ho,?_⟩
    simp [integral_indicator ho,localGauss,h]
  · have h' : c.val ∉ O := fun hc => h.not_ge ((mem_localIntegers_iff p _).mp hc)
    have he : d.primitiveJacquet p c = 0 := by funext x; simp [primitiveJacquet,h.ne',h.not_gt]
    rw [he]
    simp [localGauss, h.ne', h']

end ResidueRing
end MetaplecticPoisson.Datum
