import MetaplecticSummation.Jacquet
import MetaplecticSummation.AdeleLattice
import Mathlib.RingTheory.DedekindDomain.SInteger
import Mathlib.RingTheory.UniqueFactorizationDomain.Finite

noncomputable section
namespace MetaplecticPoisson.Datum
open Classical
open NumberField IsDedekindDomain MeasureTheory
open scoped ComplexConjugate
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [hn : NeZero n] (d : Datum F n)

abbrev SIntegers (S : Finset (Place F)) := ({p : Prime F | Sum.inr p ∈ S}.integer F)
abbrev NonzeroInteger (S : Finset (Place F)) := {c : SIntegers S // c ≠ 0}

def fieldUnit {S : Finset (Place F)} (c : NonzeroInteger S) : Fˣ :=
  Units.mk0 (c.val : F) (fun h => c.property (Subtype.ext h))

def sNorm (S : Finset (Place F)) (x : F) := ∏ v ∈ S, modulus F v (diagonal F v x)
def sPsi (S : Finset (Place F)) (x : F) := ∏ v ∈ S, d.character.localValue F v (diagonal F v x)
def sSymbol (S : Finset (Place F)) (a b : Fˣ) := ∏ v ∈ S, d.symbol v (atPlace v a) (atPlace v b)

def residue (S : Finset (Place F)) (a c : F) : ℂ := by
  classical
  exact ∏ᶠ p : Prime F, if Sum.inr p ∉ S ∧ ‖diagonal F (.inr p) c‖ < 1 then
    if h : a ≠ 0 ∧ c ≠ 0 ∧ ‖diagonal F (.inr p) a‖ = 1 then
      d.symbol (.inr p) (atPlace _ (Units.mk0 c h.2.1)) (atPlace _ (Units.mk0 a h.1))
    else 0 else 1

theorem diagonal_norm_le_one_iff (x : F) (p : Prime F) :
    ‖diagonal F (.inr p) x‖ ≤ 1 ↔ p.valuation F x ≤ 1 := by
  change ‖(x : p.adicCompletion F)‖ ≤ 1 ↔ _
  rw [Valued.toNormedField.norm_le_one_iff, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']

theorem integer_norm_le_one {S : Finset (Place F)} (x : SIntegers S) (p : Prime F)
    (hp : Sum.inr p ∉ S) : ‖diagonal F (.inr p) x‖ ≤ 1 :=
  (diagonal_norm_le_one_iff (x : F) p).mpr (x.property p hp)

omit hn in
theorem sPsi_add (S : Finset (Place F)) (x y : F) :
    d.sPsi S (x + y) = d.sPsi S x * d.sPsi S y := by
  simp only [sPsi, map_add, Character.localValue_add, Finset.prod_mul_distrib]

omit hn in
theorem sPsi_integer {S : Finset (Place F)} (hS : d.GoodOutside S) (x : SIntegers S) :
    d.sPsi S x = 1 := by
  have hχ : HasProd (fun v => d.character.localValue F v (diagonal F v x)) (1 : ℂ) := by
    have he (v : Place F) : component (algebraMap F (Adeles F) (x : F)) v = diagonal F v x := by
      cases v <;> rfl
    simpa only [he, d.character.trivial_diagonal, Circle.coe_one] using
      hasProd_localValue d.character (algebraMap F (Adeles F) (x : F))
  apply HasProd.unique _ hχ
  apply hasProd_prod_of_ne_finset_one
  rintro (w | p) hv
  · exact (hv (hS.2.1 w)).elim
  · exact (hS.2.2 p hv).2 _ (integer_norm_le_one x p hv)

/-- Every residue class of S-integers modulo a nonzero integral element
has a representative in the ordinary ring of integers. -/
theorem exists_integer_representative (S : Finset (Place F)) (r : 𝓞 F) (hr : r ≠ 0)
    (x : SIntegers S) : ∃ z : 𝓞 F, ∃ k : SIntegers S,
      x - algebraMap (𝓞 F) (SIntegers S) z = algebraMap (𝓞 F) (SIntegers S) r * k := by
  classical
  let T := S.preimage (Sum.inr : Prime F → Place F) Sum.inr_injective.injOn
  obtain ⟨k, hk, hk'⟩ := AdeleLattice.exists_valuation_sub_le_one T (fun _ => (x : F) / r)
  have hT (v : Prime F) : v ∈ T ↔ Sum.inr v ∈ S := Finset.mem_preimage
  have hkS : k ∈ ({p : Prime F | Sum.inr p ∈ S}.integer F) :=
    fun v hv => hk' v (fun h => hv ((hT v).mp h))
  have hrF : (r : F) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hr
  have hv (v : Prime F) : v.valuation F ((x : F) - r * k) ≤ 1 := by
    by_cases h : v ∈ T
    · have he : (x : F) - r * k = r * (((x : F) / r) - k) := by field_simp
      rw [he, map_mul]
      exact mul_le_one₀ (v.valuation_le_one r) zero_le
        ((v.valuation F).map_sub_swap _ _ ▸ hk v h)
    · exact (v.valuation F).map_sub_le (x.property v (fun hs => h ((hT v).mpr hs)))
        (by rw [map_mul]; exact mul_le_one₀ (v.valuation_le_one r) zero_le (hk' v h))
  obtain ⟨z, hz⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F _ hv
  refine ⟨z, ⟨k, hkS⟩, Subtype.ext ?_⟩
  change (x : F) - algebraMap (𝓞 F) F z = r * k
  rw [hz]
  ring

theorem finite_residues (S : Finset (Place F)) (c : NonzeroInteger S) :
    Finite (SIntegers S ⧸ Ideal.span {c.val}) := by
  obtain ⟨r, t, ht, he⟩ := IsFractionRing.div_surjective (𝓞 F) (c.val : F)
  have htF := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (K := F) ht
  have hrt := (div_eq_iff htF).mp he
  have hr : r ≠ 0 := by
    intro h
    apply c.property
    apply Subtype.ext
    simpa [h] using he.symm
  let I : Ideal (SIntegers S) := Ideal.span {c.val}
  let f := (Ideal.Quotient.mk I).comp (algebraMap (𝓞 F) (SIntegers S))
  have hfr : f r = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply Ideal.mem_span_singleton.mpr
    exact ⟨algebraMap (𝓞 F) (SIntegers S) t, Subtype.ext hrt⟩
  let J : Ideal (𝓞 F) := Ideal.span {r}
  haveI : Finite (𝓞 F ⧸ J) := J.finiteQuotientOfFreeOfNeBot (by simpa [J] using hr)
  have hker : J ≤ RingHom.ker f := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hfr)
  let g := Ideal.Quotient.lift J f (fun a ha => hker ha)
  apply Finite.of_surjective g
  intro y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨z, k, hk⟩ := exists_integer_representative S r hr x
  refine ⟨Ideal.Quotient.mk J z, Eq.symm (Ideal.Quotient.eq.mpr ?_)⟩
  rw [hk]
  exact I.mul_mem_right _ (Ideal.Quotient.eq_zero_iff_mem.mp hfr)

include hn in
theorem finite_power_divisors (S : Finset (Place F)) [IsPrincipalIdealRing (SIntegers S)]
    (c : NonzeroInteger S) :
    Set.Finite {t : Associates (SIntegers S) | t ^ n ∣ Associates.mk c.val} := by
  classical
  let a := Associates.mk c.val
  have ha : a ≠ 0 := by simpa [a] using c.property
  letI := Fintype.ofFinite (Associates (SIntegers S))ˣ
  let s : Set (Associates (SIntegers S)) := {t | t ∣ a}
  letI : Fintype s := UniqueFactorizationMonoid.fintypeSubtypeDvd a ha
  exact s.toFinite.subset (fun t ht => (dvd_pow_self t (NeZero.ne n)).trans ht)

/-- A unit residue class modulo (c) is evaluated on an S-integer representative.
For a unit modulus the product defining the residue symbol is empty. -/
def gauss (S : Finset (Place F)) (b c : SIntegers S) : ℂ :=
  ∑ᶠ u : (SIntegers S ⧸ Ideal.span {c})ˣ,
    let a : SIntegers S := Quotient.out (u : SIntegers S ⧸ Ideal.span {c})
    d.residue S a c * d.sPsi S ((b : F) * a / c)

private theorem norm_one_iff_of_close {K : Type*} [NormedField K] [IsUltrametricDist K]
    {x y : K} (h : ‖x - y‖ < 1) : ‖x‖ = 1 ↔ ‖y‖ = 1 := by
  by_cases he : ‖x‖ = ‖y‖
  · rw [he]
  · have hd : ‖x - y‖ = max ‖x‖ ‖y‖ := by
      rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by simpa only [norm_neg] using he), norm_neg]
    rw [hd, max_lt_iff] at h
    exact iff_of_false h.1.ne h.2.ne

theorem tame_symbol_congr (p : Prime F) (hp : p.asIdeal.absNorm.Coprime n)
    (c a b : (p.adicCompletion F)ˣ) (hb : ‖b.val‖ = 1) (hab : ‖a.val - b.val‖ < 1) :
    d.symbol (.inr p) c a = d.symbol (.inr p) c b := by
  let H : (p.adicCompletion F)ˣ →* ℂˣ := d.unitPairing (.inr p) c
  have hr : ‖(a / b).val - 1‖ < 1 := by
    rw [Units.val_div_eq_div_val, div_sub_one b.ne_zero, norm_div, hb, div_one]
    exact hab
  obtain ⟨z, hz⟩ := FinitePlace.principal_unit_pow p hp (a / b) hr
  have hone : H (a / b) = 1 := by rw [← hz, map_pow]; exact d.unitPairing_pow (.inr p) c z
  exact congrArg Units.val (div_eq_one.mp ((map_div H a b).symm.trans hone))

theorem residue_congr {S : Finset (Place F)} (hS : d.GoodOutside S) (c : NonzeroInteger S)
    (a b : SIntegers S) (hab : c.val ∣ a - b) : d.residue S a c.val = d.residue S b c.val := by
  classical
  obtain ⟨k, hk⟩ := hab
  unfold residue
  apply finprod_congr
  intro p
  by_cases h : Sum.inr p ∉ S ∧ ‖diagonal F (.inr p) c.val‖ < 1
  · simp only [if_pos h]
    let e := diagonal F (.inr p)
    have hd : ‖e a - e b‖ < 1 := by
      have he : e a - e b = e c.val * e k := by
        rw [← map_sub, ← map_mul]
        exact congrArg e (congrArg Subtype.val hk)
      rw [he, norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) (integer_norm_le_one k p h.1)).trans_lt h.2
    have hu : ‖e a‖ = 1 ↔ ‖e b‖ = 1 := norm_one_iff_of_close (K := p.adicCompletion F) hd
    by_cases ha : ‖e a‖ = 1
    · have hb := hu.mp ha
      have ne (t : SIntegers S) (ht : ‖e t‖ = 1) : (t : F) ≠ 0 := by rintro h; simp [h] at ht
      have hc : (c.val : F) ≠ 0 := fun h => c.property (Subtype.ext h)
      rw [dif_pos ⟨ne a ha, hc, ha⟩, dif_pos ⟨ne b hb, hc, hb⟩]
      exact d.tame_symbol_congr p (hS.2.2 p h.1).1 _ _ _ hb hd
    · rw [dif_neg (fun h => ha h.2.2), dif_neg (fun h => ha (hu.mpr h.2.2))]
  · simp only [if_neg h]

theorem gauss_lift_independent {S : Finset (Place F)} (hS : d.GoodOutside S)
    (b : SIntegers S) (c : NonzeroInteger S) (u : (SIntegers S ⧸ Ideal.span {c.val})ˣ)
    (a a' : SIntegers S) (ha : Ideal.Quotient.mk _ a = u.val)
    (ha' : Ideal.Quotient.mk _ a' = u.val) :
    d.residue S a c.val * d.sPsi S ((b : F) * a / c.val) =
    d.residue S a' c.val * d.sPsi S ((b : F) * a' / c.val) := by
  have hdiv := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp (ha.trans ha'.symm))
  rw [d.residue_congr hS c a a' hdiv]
  obtain ⟨k, hk⟩ := hdiv
  have hc : (c.val : F) ≠ 0 := fun h => c.property (Subtype.ext h)
  have he : (a : F) - a' = c.val * (k : F) := congrArg Subtype.val hk
  have hadd : (b : F) * a / c.val = (b : F) * a' / c.val + ((b * k : SIntegers S) : F) := by
    change _ = _ + (b : F) * k
    field_simp
    linear_combination (b : F) * he
  rw [hadd, d.sPsi_add, d.sPsi_integer hS, mul_one]

theorem unit_norm_eq_one {S : Finset (Place F)} (u : (SIntegers S)ˣ) (p : Prime F)
    (hp : Sum.inr p ∉ S) : ‖diagonal F (.inr p) (u.val : F)‖ = 1 := by
  let e := diagonal F (.inr p)
  have he : (u.val : F) * (u⁻¹.val : F) = 1 := congrArg Subtype.val u.val_inv
  have hprod : ‖e (u.val : F)‖ * ‖e (u⁻¹.val : F)‖ = 1 := by
    rw [← norm_mul, ← map_mul, he, map_one, norm_one]
  apply le_antisymm (integer_norm_le_one u.val p hp)
  exact hprod ▸ mul_le_of_le_one_right (norm_nonneg _) (integer_norm_le_one u⁻¹.val p hp)

theorem gauss_unit_modulus {S : Finset (Place F)} (hS : d.GoodOutside S)
    (b : SIntegers S) (u : (SIntegers S)ˣ) : d.gauss S b u.val = 1 := by
  classical
  let c : NonzeroInteger S := ⟨u.val,u.ne_zero⟩
  letI : Subsingleton (SIntegers S ⧸ Ideal.span {u.val}) :=
    Ideal.Quotient.subsingleton_iff.mpr (Ideal.span_singleton_eq_top.mpr u.isUnit)
  have hr : d.residue S 0 (u.val : F) = 1 := by
    unfold residue
    apply finprod_eq_one_of_forall_eq_one
    intro p
    by_cases h : Sum.inr p ∈ S
    · simp [h]
    · simp [h,unit_norm_eq_one u p h]
  unfold gauss
  rw [finsum_eq_single _ 1 (fun x hx => (hx (Subsingleton.elim _ _)).elim)]
  have he := d.gauss_lift_independent hS b c 1 (Quotient.out (1 : SIntegers S ⧸ Ideal.span {u.val})) 0
    (Subsingleton.elim _ _) (Subsingleton.elim _ _)
  change d.residue S _ (u.val : F) * d.sPsi S _ = 1
  calc
    _ = d.residue S (0 : F) (u.val : F) * d.sPsi S ((b : F) * 0 / u.val) := he
    _ = 1 := by simp [hr,sPsi]

theorem residue_mul_unit_pow {S : Finset (Place F)} (u : (SIntegers S)ˣ) (a c : F) :
    d.residue S ((u.val : F)^n * a) ((u.val : F)^n * c) = d.residue S a c := by
  classical
  let U : Fˣ := Units.map (algebraMap (SIntegers S) F).toMonoidHom u
  have hu : (u.val : F) ≠ 0 := U.ne_zero
  apply finprod_congr
  intro p
  by_cases hp : Sum.inr p ∈ S
  · simp only [hp, not_true_eq_false, false_and, if_false]
  have hne (z : F) : (u.val : F)^n * z ≠ 0 ↔ z ≠ 0 :=
    mul_ne_zero_iff.trans (and_iff_right (pow_ne_zero n hu))
  have hnrm := unit_norm_eq_one u p hp
  simp only [hp, not_false_eq_true, true_and, map_mul, map_pow, norm_mul, norm_pow, hnrm,
    one_pow, one_mul, hne]
  split_ifs with hc ha
  · let C := Units.mk0 c ha.2.1
    let A := Units.mk0 a ha.1
    let v : Place F := .inr p
    let H := d.unitPairing v
    have he (t : F) (ht : t ≠ 0) : Units.mk0 ((u.val : F)^n*t) (mul_ne_zero (pow_ne_zero n hu) ht) =
        U^n * Units.mk0 t ht := Units.ext rfl
    rw [he c ha.2.1, he a ha.1]
    change (H (atPlace v (U^n*C)) (atPlace v (U^n*A)) : ℂ) = (H (atPlace v C) (atPlace v A) : ℂ)
    apply congrArg Units.val
    have hpow (x y : (LocalField F v)ˣ) : H x y ^ n = 1 := d.unitPairing_pow v x y
    simp only [atPlace, map_mul, map_pow, MonoidHom.mul_apply, MonoidHom.pow_apply, hpow, one_mul]
  all_goals rfl

theorem gauss_unit_power {S : Finset (Place F)} (hS : d.GoodOutside S)
    (b : SIntegers S) (c : NonzeroInteger S) (u : (SIntegers S)ˣ) :
    d.gauss S b ((u : SIntegers S)^n * c.val) = d.gauss S b c.val := by
  classical
  let m : SIntegers S := u.val ^ n
  let c' : NonzeroInteger S := ⟨m * c.val, mul_ne_zero (pow_ne_zero n u.ne_zero) c.property⟩
  let I : Ideal (SIntegers S) := Ideal.span {c.val}
  have hI : Ideal.span {c'.val} = I := Ideal.span_singleton_mul_left_unit (u.isUnit.pow n) _
  let q := Ideal.Quotient.mk I
  let w := Units.map q.toMonoidHom (u^n)
  let term (t : (SIntegers S ⧸ I)ˣ) :=
    let a : SIntegers S := Quotient.out t.val
    d.residue S a c'.val * d.sPsi S ((b : F) * a / c'.val)
  change d.gauss S b c'.val = _
  unfold gauss
  rw [hI]
  change (∑ᶠ t, term t) = _
  rw [← finsum_comp_equiv (Equiv.mulLeft w) (f := term)]
  apply finsum_congr
  intro t
  let a : SIntegers S := Quotient.out t.val
  let a' : SIntegers S := Quotient.out (w*t).val
  have ha : q a = t.val := Quotient.out_eq _
  have hma : q (m * a) = (w*t).val := by rw [map_mul, ha]; rfl
  have ha' : q a' = (w*t).val := Quotient.out_eq _
  have heq : Ideal.Quotient.mk (Ideal.span {c'.val}) a' =
      Ideal.Quotient.mk (Ideal.span {c'.val}) (m*a) := by rw [hI]; exact ha'.trans hma.symm
  have hunit : IsUnit (Ideal.Quotient.mk (Ideal.span {c'.val}) a') := by
    rw [hI]; exact ha' ▸ (w*t).isUnit
  have h := d.gauss_lift_independent hS b c' hunit.unit a' (m*a) hunit.unit_spec.symm
    (heq.symm.trans hunit.unit_spec.symm)
  change d.residue S a' c'.val * d.sPsi S ((b : F)*a'/c'.val) = _
  rw [h]
  change d.residue S ((u.val : F)^n * a) ((u.val : F)^n * c.val) *
    d.sPsi S ((b : F)*((u.val : F)^n*a)/((u.val : F)^n*c.val)) = _
  rw [d.residue_mul_unit_pow]
  congr 2
  have hu : (u.val : F) ≠ 0 := fun hz => u.ne_zero (Subtype.ext hz)
  have hc : (c.val : F) ≠ 0 := fun hz => c.property (Subtype.ext hz)
  change (b : F)*((u.val : F)^n*a)/((u.val : F)^n*c.val) = (b : F)*a/c.val
  field_simp

theorem sNorm_mul (S : Finset (Place F)) (x y : F) :
    sNorm S (x*y) = sNorm S x * sNorm S y := by
  unfold sNorm
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  rintro (w|p) _
  · simp [modulus, map_mul, norm_mul, mul_pow]
  · simp [modulus, map_mul, norm_mul]

theorem sNorm_unit {S : Finset (Place F)} (hS : ∀ w, Sum.inl w ∈ S) (u : (SIntegers S)ˣ) :
    sNorm S (u.val : F) = 1 := by
  have hu : (u.val : F) ≠ 0 := fun h => u.ne_zero (Subtype.ext h)
  rw [← diagonal_modulus_product hu]
  symm
  apply finprod_eq_prod_of_mulSupport_subset
  rintro (w|p) h
  · exact hS w
  · by_contra hp
    exact h (unit_norm_eq_one u p hp)

/-- The product of the square roots of the finite moduli outside S,
with the normalization of the scaled self-dual measures. -/
theorem outside_sqrt_norm (S : Finset (Place F)) (hS : ∀ w, Sum.inl w ∈ S) (b : Fˣ) :
    (∏ᶠ p : Prime F, if Sum.inr p ∈ S then 1 else Real.sqrt ‖diagonal F (.inr p) (b : F)‖) =
      (Real.sqrt (sNorm S (b : F)))⁻¹ := by
  classical
  let r (p : Prime F) := ‖diagonal F (.inr p) (b : F)‖
  let m (v : Place F) := modulus F v (diagonal F v (b : F))
  let P := (Filter.eventually_cofinite.mp (eventually_diagonal_norm_one b.ne_zero)).toFinset
  let T := P.filter fun p => Sum.inr p ∉ S
  have hT (p : Prime F) : p ∈ T ↔ r p ≠ 1 ∧ Sum.inr p ∉ S := by
    simp [T,P,r]
  let i : Prime F ↪ Place F := ⟨Sum.inr, Sum.inr_injective⟩
  have hdis : Disjoint S (T.map i) := by
    rw [Finset.disjoint_left]
    rintro _ hv hw
    obtain ⟨p,hp,rfl⟩ := Finset.mem_map.mp hw
    exact ((hT p).mp hp).2 hv
  have hsub : Function.mulSupport m ⊆ (↑(S ∪ T.map i) : Set (Place F)) := by
    rintro (w|p) hp
    · exact Finset.mem_union_left _ (hS w)
    · by_cases h : Sum.inr p ∈ S
      · exact Finset.mem_union_left _ h
      · exact Finset.mem_union_right _ (Finset.mem_map.mpr ⟨p,(hT p).mpr ⟨hp,h⟩,rfl⟩)
  have he : sNorm S (b : F) * (∏ p ∈ T, r p) = 1 := by
    have h := diagonal_modulus_product b.ne_zero
    change finprod m = 1 at h
    rwa [finprod_eq_prod_of_mulSupport_subset _ hsub, Finset.prod_union hdis, Finset.prod_map] at h
  rw [finprod_eq_prod_of_mulSupport_subset (s := T) _ (by
    intro p hp
    apply (hT p).mpr
    by_contra! h
    by_cases hv : Sum.inr p ∈ S
    · exact hp (by simp [hv])
    · have hr : r p = 1 := by by_contra hr; exact hv (h hr)
      exact hp (by simp [hv, show ‖diagonal F (.inr p) (b : F)‖ = 1 from hr]))]
  calc
    _ = ∏ p ∈ T, Real.sqrt (r p) := Finset.prod_congr rfl fun p hp => if_neg ((hT p).mp hp).2
    _ = _ := by
      rw [← Real.sqrt_prod T (fun _ _ => norm_nonneg _),
        show (∏ p ∈ T, r p) = (sNorm S (b : F))⁻¹ from (eq_inv_of_mul_eq_one_right he),
        Real.sqrt_inv]

def powerDivisorTerm (S : Finset (Place F)) (b c t : SIntegers S) : ℂ := by
  classical exact if h : t ^ n ∣ c then
    (sNorm S t : ℂ) ^ (n-1) * d.gauss S b h.choose else 0

theorem powerDivisorTerm_congr {S : Finset (Place F)} (hS : d.GoodOutside S)
    (b : SIntegers S) (c : NonzeroInteger S) {t t' : SIntegers S} (ht : Associated t t') :
    d.powerDivisorTerm S b c.val t = d.powerDivisorTerm S b c.val t' := by
  obtain ⟨u, rfl⟩ := ht
  have hm : sNorm S (((t * u.val : SIntegers S) : F)) = sNorm S t := by
    rw [show ((t*u.val : SIntegers S) : F) = (t : F)*(u.val : F) from rfl,
      sNorm_mul, sNorm_unit hS.2.1, mul_one]
  unfold powerDivisorTerm
  have he : (t*u.val)^n ∣ c.val ↔ t^n ∣ c.val := by rw [mul_pow]; exact (u.isUnit.pow n).mul_right_dvd
  by_cases h : t^n ∣ c.val
  · have h' := he.mpr h
    rw [dif_pos h, dif_pos h', hm]
    have ht0 : t^n ≠ 0 := fun hz => c.property (by simpa [hz] using h.choose_spec)
    have hz : h.choose = u.val^n * h'.choose := by
      apply mul_left_cancel₀ ht0
      rw [← mul_assoc, ← mul_pow, ← h.choose_spec, ← h'.choose_spec]
    have hc' : h'.choose ≠ 0 := fun hz => c.property (by simpa [hz] using h'.choose_spec)
    rw [hz, d.gauss_unit_power hS b ⟨_,hc'⟩ u]
  · rw [dif_neg h, dif_neg (fun h' => h (he.mp h'))]

def normalizedGauss (S : Finset (Place F)) (b c : SIntegers S) : ℂ :=
  (sNorm S c : ℂ)⁻¹ * ∑ᶠ t : Associates (SIntegers S), d.powerDivisorTerm S b c (Quotient.out t)

/-- If no nonunit n-th power divides the modulus, only the unit divisor
contributes to the normalized Gauss sum. -/
theorem normalizedGauss_power_free {S : Finset (Place F)} (hS : d.GoodOutside S)
    (b : SIntegers S) (c : NonzeroInteger S) (hfree : ∀ t : SIntegers S, t^n ∣ c.val → IsUnit t) :
    d.normalizedGauss S b c.val = d.gauss S b c.val / (sNorm S c.val : ℂ) := by
  classical
  unfold normalizedGauss
  rw [finsum_eq_single _ (1 : Associates (SIntegers S))]
  · have hassoc : Associated (Quotient.out (1 : Associates (SIntegers S))) 1 :=
      Associates.mk_quot_out (1 : SIntegers S)
    rw [d.powerDivisorTerm_congr hS b c hassoc]
    have h1 : sNorm S (1 : F) = 1 := sNorm_unit hS.2.1 (1 : (SIntegers S)ˣ)
    simp [powerDivisorTerm, h1, div_eq_inv_mul]
  · intro t ht
    apply dif_neg
    intro h
    apply ht
    rw [← Associates.quot_out t, Associates.mk_eq_one]
    exact hfree _ h

theorem normalizedGauss_unit_modulus {S : Finset (Place F)} (hS : d.GoodOutside S)
    (b : SIntegers S) (u : (SIntegers S)ˣ) : d.normalizedGauss S b u.val = 1 := by
  let c : NonzeroInteger S := ⟨u.val,u.ne_zero⟩
  have hfree (t : SIntegers S) (ht : t^n ∣ c.val) : IsUnit t :=
    isUnit_of_dvd_unit ((dvd_pow_self t (NeZero.ne n)).trans ht) u.isUnit
  change d.normalizedGauss S b c.val = 1
  rw [d.normalizedGauss_power_free hS b c hfree]
  change d.gauss S b u.val / (sNorm S (u.val : F) : ℂ) = 1
  rw [d.gauss_unit_modulus hS, sNorm_unit hS.2.1, Complex.ofReal_one, div_one]

end MetaplecticPoisson.Datum
