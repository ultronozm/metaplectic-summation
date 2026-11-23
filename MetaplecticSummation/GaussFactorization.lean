import MetaplecticSummation.ResidueCRT
import Mathlib.Algebra.Group.Pi.Units

/-! Factorization of the global Gauss sum into the local Gauss–Ramanujan
sums for the scaled character, as used in the product of basic functions. -/

noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField IsDedekindDomain Filter Set
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)
variable {S : Finset (Place F)} (b c : NonzeroInteger S)

private abbrev loc (p : modulusPrimes c) : Place F := Sum.inr p.val
private abbrev modulusUnit (p : modulusPrimes c) : (p.val.adicCompletion F)ˣ :=
  atPlace (loc c p) (fieldUnit c)

private def factor (p : modulusPrimes c) (u : (LocalResidue c p)ˣ) : ℂ :=
  (d.scaled (fieldUnit b)).residueTerm p.val (modulusUnit c p)
    ((Quotient.out u.val : p.val.adicCompletionIntegers F) : p.val.adicCompletion F)

private def crtUnits : (SIntegers S ⧸ Ideal.span {c.val})ˣ ≃* ((p : modulusPrimes c) → (LocalResidue c p)ˣ) :=
  (Units.mapEquiv (residueCRT c).toMulEquiv).trans (MulEquiv.piUnits)

private theorem factor_sum (p : modulusPrimes c) [Fintype (LocalResidue c p)ˣ] :
    (∑ u, d.factor b c p u) =
      (d.scaled (fieldUnit b)).localGauss p.val (modulusUnit c p) := by
  have hnorm : ‖(modulusUnit c p).val‖ < 1 := ((mem_modulusPrimes c p.val).mp p.property).2
  have hmem := (mem_localIntegers_iff p.val _).mpr hnorm.le
  rw [localGauss,if_neg hnorm.ne,dif_pos hmem]
  change _ = ∑ᶠ u : (LocalResidue c p)ˣ, d.factor b c p u
  rw [finsum_eq_sum_of_fintype]

private theorem gauss_term_factorization (hS : d.GoodOutside S)
    (hscaled : (d.scaled (fieldUnit b)).GoodOutside S)
    (u : (SIntegers S ⧸ Ideal.span {c.val})ˣ) (a : SIntegers S) (ha : Ideal.Quotient.mk _ a = u.val) :
    d.residue S a c.val * d.sPsi S ((b.val : F)*a/c.val) =
      ∏ p : modulusPrimes c, d.factor b c p (crtUnits c u p) := by
  let T := modulusPrimes c
  let e (p : T) := toLocalInteger p.val ((mem_modulusPrimes c p.val).mp p.property).1
  let U := crtUnits c u
  have hred (p : T) : localReduction c p a = (U p).val :=
    congrArg (fun z => residueReduction c z p) ha
  have hunit (p : T) : ‖((e p a : p.val.adicCompletionIntegers F) : p.val.adicCompletion F)‖ = 1 :=
    (localResidues_isUnit_iff p.val (localModulus c p) (e p a) ((mem_modulusPrimes c p.val).mp p.property).2).mp
      ((hred p).symm ▸ (U p).isUnit)
  let H (p : T) : ℂ := if ha₀ : (a : F) ≠ 0 then
    d.symbol (loc c p) (modulusUnit c p) (atPlace _ (Units.mk0 _ ha₀)) else 0
  have hres : d.residue S a c.val = ∏ p : T, H p := by
    unfold residue
    rw [finprod_eq_prod_of_mulSupport_subset (s := T) _ (by
      intro p hp
      by_contra h
      exact hp (if_neg (fun hh => h ((mem_modulusPrimes c p).mpr hh))))]
    rw [← Finset.prod_attach T]
    apply Finset.prod_congr rfl
    intro p _
    have hn : (a : F) ≠ 0 := by
      intro hz
      have he : ‖diagonal F (loc c p) (a : F)‖ = 1 := hunit p
      simp [hz] at he
    rw [if_pos ((mem_modulusPrimes c p.val).mp p.property),
      dif_pos ⟨hn,(fieldUnit c).ne_zero,hunit p⟩]
    simp only [H,dif_pos hn]
    rfl
  have hphase := d.sPsi_fraction c hS (b.val*a)
  rw [hres,show d.sPsi S ((b.val : F)*a/c.val) = _ from hphase,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p _
  let r : p.val.adicCompletionIntegers F := Quotient.out (U p).val
  have hr : Ideal.Quotient.mk (Ideal.span {localModulus c p}) r = (U p).val := Quotient.out_eq _
  have hprime := (mem_modulusPrimes c p.val).mp p.property
  have hru := (localResidues_isUnit_iff p.val (localModulus c p) r hprime.2).mp (hr.symm ▸ (U p).isUnit)
  have hcong := (localResidues_eq_iff p.val (localModulus c p) (e p a) r (modulusUnit c p).ne_zero).mp
    ((hred p).trans hr.symm)
  let db := d.scaled (fieldUnit b)
  have hf := db.residueTerm_congr p.val (hS.2.2 p.val hprime.1).1 (hscaled.2.2 p.val hprime.1).2
    (modulusUnit c p) hprime.2 (e p a) r (hunit p) hru hcong
  apply Eq.trans _ hf
  have hn : (a : F) ≠ 0 := by
    intro hz
    have he : ‖diagonal F (loc c p) (a : F)‖ = 1 := hunit p
    simp [hz] at he
  have hl : ((e p a : p.val.adicCompletionIntegers F) : p.val.adicCompletion F) ≠ 0 :=
    (map_ne_zero (diagonal F (loc c p))).mpr hn
  rw [show H p = _ from dif_pos hn, residueTerm, dif_pos hl]
  apply congrArg₂ (· * ·)
  · change d.symbol (loc c p) (modulusUnit c p) _ = d.symbol (loc c p) (modulusUnit c p) _
    apply congrArg
    exact Units.ext rfl
  · dsimp only [db]
    erw [d.scaled_localValue]
    apply congrArg
    change -(diagonal F (loc c p) (((b.val : F)*a)/c.val)) =
      diagonal F (loc c p) (b.val : F) * (-(diagonal F (loc c p) (a : F))/diagonal F (loc c p) c.val)
    rw [map_div₀,map_mul]
    ring

/-- Chinese remainder factorization in the proof of the product-of-basic-functions lemma.
The product runs precisely over the finite primes outside S dividing c. -/
theorem gauss_eq_prod_localGauss (h : d.ClassicalSetting S) :
    d.gauss S b.val c.val = ∏ p : modulusPrimes c,
      (d.scaled (fieldUnit b)).localGauss p.val (atPlace (.inr p.val) (fieldUnit c)) := by
  classical
  letI : Finite (SIntegers S ⧸ Ideal.span {c.val}) := finite_residues S c
  letI : Fintype (SIntegers S ⧸ Ideal.span {c.val})ˣ := Fintype.ofFinite _
  letI (p : modulusPrimes c) : Finite (LocalResidue c p) :=
    finite_local_residues p.val (localModulus c p) (modulusUnit c p).ne_zero
  letI (p : modulusPrimes c) : Fintype (LocalResidue c p)ˣ := Fintype.ofFinite _
  unfold gauss
  rw [finsum_eq_sum_of_fintype]
  simp_rw [d.gauss_term_factorization b c h.good (d.scaled_good h b) _ _ (Quotient.out_eq _)]
  apply ((crtUnits c).toEquiv.sum_comp (fun f => ∏ p, d.factor b c p (f p))).trans
  simp_rw [← d.factor_sum b c]
  simpa only [Fintype.piFinset_univ] using
    (Finset.prod_univ_sum (fun _ => Finset.univ) (d.factor b c)).symm

end MetaplecticPoisson.Datum
