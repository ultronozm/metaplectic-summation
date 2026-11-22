import MetaplecticSummation.AdeleLattice
import MetaplecticSummation.AdelicCharacters

/-! Compact annihilators for an adelic character trivial on the diagonal. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField Filter Set IsDedekindDomain
open Classical
variable {F : Type} [Field F] [NumberField F]
local notation "A" => Adeles F
local notation "ι" => algebraMap F A

/-- A rational multiple of the character is determined by its restriction
to a set of representatives. The centered arc detects its vanishing. -/
private theorem rational_eq_zero_of_arc (ψ : Character F) {D : Set A}
    (rep : ∀ x : A, ∃ b : F, x - ι b ∈ D) {k : F}
    (h : ∀ x ∈ D, ψ.toChar (ι k * x) ∈ Circle.centeredArc (Real.pi/2)) : k = 0 := by
  have allArc (x : A) : ψ.toChar (ι k * x) ∈ Circle.centeredArc (Real.pi/2) := by
    obtain ⟨b,hb⟩ := rep x
    have ht := h _ hb
    rwa [mul_sub,← map_mul,AddChar.map_sub_eq_div,ψ.trivial_diagonal,div_one] at ht
  have one (x : A) : ψ.toChar (ι k * x) = 1 := by
    apply Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two
    intro m _
    rw [← AddChar.map_nsmul_eq_pow]
    simpa only [nsmul_eq_mul,mul_left_comm] using allArc (m • x)
  by_contra hk
  obtain ⟨x,hx⟩ := ψ.nontrivial
  have := one (ι k⁻¹*x)
  rw [← mul_assoc,← map_mul,mul_inv_cancel₀ hk,map_one,one_mul] at this
  exact hx this

/-- Only finitely many rational translates of a compact set of representatives
can contain an adele annihilating the entire set. -/
theorem finite_annihilating_translates (ψ : Character F) {D : Set A} (hc : IsCompact D)
    (rep : ∀ x : A, ∃ b : F, x - ι b ∈ D) :
    {k : F | ∃ r ∈ D, ∀ x ∈ D, ψ.toChar ((ι k + r)*x) = 1}.Finite := by
  let arc := Circle.centeredArc (Real.pi/2)
  have near (a : A) : ∃ U : Set A, IsOpen U ∧ a ∈ U ∧
      ∀ r ∈ U, ∀ s ∈ U, ∀ x ∈ D, ψ.toChar ((r-s)*x) ∈ arc := by
    let f (z : (A × A) × A) := ψ.toChar ((z.1.1-z.1.2)*z.2)
    have cf : Continuous f := ψ.continuous_toChar.comp
      (((continuous_fst.comp continuous_fst).sub (continuous_snd.comp continuous_fst)).mul continuous_snd)
    have h1 : (1:Circle) ∈ arc := ⟨0,by simpa using half_pos Real.pi_pos,Circle.exp_zero⟩
    obtain ⟨U,V,hU,_,ha,hD,huv⟩ := generalized_tube_lemma (isCompact_singleton (X := A × A) (x := (a,a))) hc
      ((Circle.isOpen_centeredArc (Real.pi/2)).preimage cf) (by
        rintro ⟨z,x⟩ ⟨hz,_⟩
        obtain rfl : z = (a,a) := hz
        simpa only [Set.mem_preimage,f,sub_self,zero_mul,AddChar.map_zero_eq_one] using h1)
    obtain ⟨P,Q,hP,hQ,hp,hq,hsub⟩ := isOpen_prod_iff.mp hU a a (ha (mem_singleton _))
    exact ⟨P ∩ Q,hP.inter hQ,⟨hp,hq⟩,fun r hr s hs x hx => huv (a := ((r,s),x)) ⟨hsub (a := (r,s)) ⟨hr.1,hs.2⟩,hD hx⟩⟩
  choose U hU hmem hdiff using near
  obtain ⟨S,hS⟩ := hc.elim_finite_subcover U hU (fun a _ => mem_iUnion.mpr ⟨a,hmem a⟩)
  let V (a : A) := {k : F | ∃ r ∈ U a, ∀ x ∈ D, ψ.toChar ((ι k + r)*x) = 1}
  have unique (a : A) : (V a).Subsingleton := by
    rintro k ⟨r,hr,hk⟩ l ⟨s,hs,hl⟩
    apply sub_eq_zero.mp (rational_eq_zero_of_arc ψ rep ?_)
    intro x hx
    have eqn : ψ.toChar (ι (k-l)*x) = ψ.toChar ((s-r)*x) := by
      have elt : ι (k-l)*x = ((ι k+r)*x - (ι l+s)*x) + (s-r)*x := by rw [map_sub]; ring
      rw [elt,AddChar.map_add_eq_mul,AddChar.map_sub_eq_div,hk x hx,hl x hx,div_one,one_mul]
    exact eqn ▸ hdiff a s hs r hr x hx
  apply (S.finite_toSet.biUnion (fun a _ => (unique a).finite)).subset
  rintro k ⟨r,hr,hk⟩
  obtain ⟨a,ha,hu⟩ := mem_iUnion₂.mp (hS hr)
  exact mem_iUnion₂.mpr ⟨a,ha,r,hu,hk⟩

/-- The annihilator of a compact set of representatives of the adelic quotient
is compact for the multiplicative pairing induced by the additive character. -/
theorem isCompact_annihilator_of_representatives (ψ : Character F) {D : Set A} (hc : IsCompact D)
    (rep : ∀ x : A, ∃ b : F, x - ι b ∈ D) :
    IsCompact {a : A | ∀ x ∈ D, ψ.toChar (a*x) = 1} := by
  have hs := finite_annihilating_translates ψ hc rep
  let V (k : F) := (fun r : A => ι k+r) '' D
  have hV (k : F) : IsCompact (V k) := hc.image (continuous_const.add continuous_id)
  apply (hs.isCompact_biUnion (fun k _ => hV k)).of_isClosed_subset
  · simp only [setOf_forall]
    exact isClosed_iInter (fun x => isClosed_iInter (fun _ =>
      isClosed_eq (ψ.continuous_toChar.comp (continuous_id.mul_const x)) continuous_const))
  · intro a ha
    obtain ⟨k,hk⟩ := rep a
    have e : ι k + (a-ι k) = a := by abel
    exact mem_iUnion₂.mpr ⟨k,⟨a-ι k,hk,fun x hx => by rw [e]; exact ha x hx⟩,a-ι k,hk,e⟩

end MetaplecticPoisson.Datum

namespace MetaplecticPoisson
open NumberField Set

/-- Every local component of the adelic character is nontrivial. -/
theorem Character.nontrivial_localValue {F : Type} [Field F] [NumberField F] (χ : Character F) (v : Place F) :
    ∃ t, χ.localValue F v t ≠ 1 := by
  letI : Infinite (LocalField F v) := Infinite.of_injective (diagonal F v) (diagonal F v).injective
  obtain ⟨C,hC,rep⟩ := AdeleLattice.exists_isCompact_forall_exists_sub_mem F
  let D : Set (Adeles F) := C ×ˢ (AdeleLattice.integralFiniteAdeles (𝓞 F) F : Set _)
  have hc : IsCompact D := hC.prod (AdeleLattice.isCompact_integralFiniteAdeles F)
  have hi := (Datum.isCompact_annihilator_of_representatives χ hc rep).image (Datum.continuous_component v)
  by_contra! ht
  apply hi.ne_univ (Set.eq_univ_of_forall fun x => ?_)
  refine ⟨singleAdele F v x,?_,Datum.component_single_self v x⟩
  intro z _
  rw [Datum.singleAdele_mul]
  exact Subtype.ext (ht _)

end MetaplecticPoisson
