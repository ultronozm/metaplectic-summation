import MetaplecticSummation.TameDegreeCompatibility
import MetaplecticSummation.ResidueCRT

/-! The sextic residue character in Corollary 10.39. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField IsDedekindDomain
open Classical
variable {F : Type} [Field F] [NumberField F]

private def includeRoot {m n : ℕ} (h : m ∣ n) : Mu F m →* Mu F n :=
  Subgroup.inclusion (rootsOfUnity_le_of_dvd h)

private theorem embedding_quadratic (D : Datum F 6) (b : Datum F 2) (w : Mu F 2) :
    D.embedding (includeRoot (by decide : 2 ∣ 6) w) = b.embedding w := by
  let ι := includeRoot (F := F) (by decide : 2 ∣ 6)
  have hι : Function.Injective ι := fun _ _ h => Subtype.ext (congrArg (fun t : Mu F 6 => t.val) h)
  have hw : w^2 = 1 := Subtype.ext w.property
  by_cases hone : w = 1
  · simp [hone]
  have sign (f : Mu F 2 →* ℂˣ) (hf : Function.Injective f) : (f w : ℂ) = -1 := by
    have hpow : (f w)^2 = 1 := by rw [← map_pow,hw,map_one]
    have hs : (f w : ℂ)^2 = 1 := congrArg Units.val hpow
    exact (sq_eq_one_iff.mp hs).resolve_left (fun h => hone (hf (by rw [map_one]; exact Units.ext h)))
  exact Units.ext ((sign (D.embedding.comp ι) (D.injective.comp hι)).trans (sign b.embedding b.injective).symm)

private theorem sextic_symbol_on_units (D : Datum F 6) (a : Datum F 3) (b : Datum F 2)
    (compatible : ∀ w : Mu F 3, D.embedding (includeRoot (by decide : 3 ∣ 6) w) = a.embedding w)
    (p : Prime F) (hp : p.asIdeal.absNorm.Coprime 6) (x u : (p.adicCompletion F)ˣ) (hu : ‖u.val‖ = 1) :
    D.symbol (.inr p) x u = b.symbol (.inr p) x u * a.symbol (.inr p) x u ^ 2 := by
  let z := D.family (.inr p) x u
  have h2 : z^3 = includeRoot (by decide : 2 ∣ 6) (b.family (.inr p) x u) :=
    Subtype.ext (tame_change_degree_on_units p D b 3 rfl hp x u hu)
  have h3 : z^2 = includeRoot (by decide : 3 ∣ 6) (a.family (.inr p) x u) :=
    Subtype.ext (tame_change_degree_on_units p D a 2 rfl hp x u hu)
  have h6 : z^6 = 1 := Subtype.ext z.property
  have he : z^3 * (z^2)^2 = z := by
    rw [← pow_mul, ← pow_add]
    rw [show 3+2*2 = 6+1 from rfl,pow_succ,h6,one_mul]
  have E := congrArg D.embedding he.symm
  rw [map_mul,h2,h3,map_pow,embedding_quadratic D b,compatible] at E
  exact congrArg Units.val E

/-- With compatible embeddings the sextic symbol is the quadratic symbol times
the square of the cubic symbol. This includes numerators sharing a prime with the modulus. -/
theorem sextic_residue (D : Datum F 6) (a : Datum F 3) (b : Datum F 2)
    (compatible : ∀ w : Mu F 3, D.embedding ⟨w.val,rootsOfUnity_le_of_dvd (by decide : 3 ∣ 6) w.property⟩ = a.embedding w)
    {S : Finset (Place F)} (hS : a.GoodOutside S) (awayTwo : ∀ p : Prime F, Sum.inr p ∉ S → Odd p.asIdeal.absNorm)
    (c : Fˣ) (h : NonzeroInteger S) :
    D.residue S c (fieldUnit h) = b.residue S c (fieldUnit h) * (a.residue S c (fieldUnit h))^2 := by
  simp_rw [residue_on_modulus_primes]
  rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hout := ((mem_modulusPrimes h p).mp hp).1
  have ht : p.asIdeal.absNorm.Coprime (2*3) :=
    Nat.coprime_mul_iff_right.mpr ⟨(awayTwo p hout).coprime_two_right, (hS.2.2 p hout).1⟩
  split_ifs with hu
  · exact sextic_symbol_on_units D a b compatible p ht _ _ hu
  · simp

end MetaplecticPoisson.Datum
