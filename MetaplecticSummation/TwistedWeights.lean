import MetaplecticSummation.GaussProduct
import MetaplecticSummation.CharacterScaling

/-! The local conductor factors in the epsilon constant of the twisted formula. -/

noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField MeasureTheory Filter Set
open scoped Topology
open scoped ComplexConjugate
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

def unitGauss (p : Prime F) (θ : Weight (.inr p : Place F)) (α : LocalField F (.inr p)) :=
  d.lineIntegral (.inr p) fun x => if ‖(x : LocalField F (.inr p))‖ = 1 then
    θ x * d.character.localValue F (.inr p) (α*x) else 0

theorem twistedVector (p : Prime F) (hp : p.asIdeal.absNorm.Coprime n) (hψ : d.UnramifiedAt (.inr p))
    (χ : UnitChar p) (hχ : Continuous χ) (e : ℕ) (he : 0 < e)
    (cond : IsLeast {k | trivialAtLevel (χ^n) k} e) (c : (LocalField F (.inr p))ˣ) :
    let q : ℝ := p.asIdeal.absNorm
    let V := d.dualWeight (.inr p) (charWeight χ) c
    (‖(c : LocalField F (.inr p))‖ ≠ q ^ ((n-1)*e) → V = 0) ∧
    (‖(c : LocalField F (.inr p))‖ = q ^ ((n-1)*e) →
      ‖V‖ = 1 ∧ ∀ t : (LocalField F (.inr p))ˣ, ‖(t : LocalField F (.inr p))‖ = q ^ e →
        V = (q : ℂ)^e * d.unitGauss p (charWeight (χ ^ n)) t *
          d.unitGauss p (fun x => conj (charWeight χ x) * d.symbol (.inr p) c x)
            (-((t : LocalField F (.inr p)) ^ n) / c)) := by sorry

private theorem isUnit_of_coprime_local {R : Type*} [CommRing R] [IsLocalRing R] {a b : R}
    (h : IsCoprime a b) (hb : ¬ IsUnit b) : IsUnit a := by
  obtain ⟨x,y,hxy⟩ := h
  exact isUnit_of_mul_isUnit_right ((IsLocalRing.isUnit_or_isUnit_of_add_one hxy).resolve_right
    (fun hy => hb (isUnit_of_mul_isUnit_right hy)))

omit [NeZero n] in
theorem Twist.norm_frequency {S : Finset (Place F)} {f b : NonzeroInteger S}
    (T : Twist (n := n) S f) (hb : IsCoprime b.val f.val) (p : T.primes) :
    ‖(atPlace (.inr p.val) (fieldUnit b)).val‖ = 1 := by
  let e : SIntegers S →+* p.val.adicCompletionIntegers F := toLocalInteger p.val (T.outside _ p.property)
  have hq : 1 < (p.val.asIdeal.absNorm : ℝ) := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm p.val
  have hlt : ‖(atPlace (.inr p.val) (fieldUnit f)).val‖ < 1 :=
    (T.generator p).trans_lt (inv_lt_one_of_one_lt₀ (one_lt_pow₀ hq (T.positive p).ne'))
  have hn : ¬ IsUnit (e f.val) := by
    intro hf
    exact hlt.ne ((localInteger_isUnit_iff p.val (e f.val)).mp hf)
  have hu := isUnit_of_coprime_local (hb.map e) hn
  exact (localInteger_isUnit_iff p.val (e b.val)).mp hu

omit [NeZero n] in
private theorem norm_twist_argument {K : Type*} [NormedField K] (B P : Kˣ) {q : ℝ} {e : ℕ}
    (hB : ‖B.val‖ = 1) (hP : ‖P.val‖ = (q^e)⁻¹) :
    ‖((B*P^(n-1))⁻¹).val‖ = q^((n-1)*e) := by
  rw [Units.val_inv_eq_inv_val,Units.val_mul,Units.val_pow_eq_pow_val,norm_inv,
    norm_mul,norm_pow,hB,hP,one_mul,inv_pow,inv_inv,← pow_mul,mul_comm e]

private theorem symbol_twist_argument (p : Prime F) (hp : p.asIdeal.absNorm.Coprime n)
    (B P x : (LocalField F (.inr p))ˣ) (hB : ‖B.val‖ = 1) (hx : ‖x.val‖ = 1) :
    d.symbol (.inr p) (B*P^(n-1))⁻¹ x = d.symbol (.inr p) P x := by
  have hn : P^(n-1)*P = P^n := by rw [← pow_succ,Nat.sub_add_cancel (NeZero.pos n)]
  have hcp : (B*P^(n-1))⁻¹*B*P^n = P := by rw [← hn]; simp [mul_assoc,mul_comm]
  apply congrArg Units.val
  change d.unitPairing (.inr p) _ x = d.unitPairing (.inr p) P x
  conv_rhs => rw [← hcp]
  rw [map_mul,map_mul,map_pow,MonoidHom.mul_apply,MonoidHom.mul_apply,MonoidHom.pow_apply,
    d.unitPairing_pow,d.unitPairing_tame_units p hp B x hB hx,mul_one,mul_one]

private theorem epsilon_factor {S : Finset (Place F)} (h : d.ClassicalSetting S)
    (f b : NonzeroInteger S) (T : Twist (n := n) S f) (hb : IsCoprime b.val f.val) (p : T.primes) :
    let v : Place F := .inr p.val
    let P := atPlace v (fieldUnit f)
    let C := atPlace v (fieldUnit b * fieldUnit f^(n-1))⁻¹
    let V := d.dualWeight v (charWeight (T.character p)) C
    ‖V‖ = 1 ∧ V = (p.val.asIdeal.absNorm : ℂ)^T.exponent p *
      d.unitGauss p.val (charWeight (T.character p^n)) (P.val⁻¹) *
      d.unitGauss p.val (fun x => conj (charWeight (T.character p) x) * d.symbol v P x)
        (-diagonal F v (fieldUnit b) / P.val) := by
  let v : Place F := .inr p.val
  let B := atPlace v (fieldUnit b)
  let P := atPlace v (fieldUnit f)
  let C := atPlace v (fieldUnit b * fieldUnit f^(n-1))⁻¹
  let q : ℝ := p.val.asIdeal.absNorm
  let e := T.exponent p
  have hB : ‖B.val‖ = 1 := T.norm_frequency hb p
  have hP : ‖P.val‖ = (q^e)⁻¹ := T.generator p
  have hC : C = (B*P^(n-1))⁻¹ := by simp only [C,B,P,atPlace,map_mul,map_inv,map_pow]
  have arg : ‖C.val‖ = q^((n-1)*e) := hC ▸ norm_twist_argument B P hB hP
  have ht : ‖P⁻¹.val‖ = q^e := by rw [Units.val_inv_eq_inv_val,norm_inv,hP,inv_inv]
  have hp := T.outside _ p.property
  have hv := (d.twistedVector p.val (h.good.2.2 p.val hp).1 (h.unramified p.val hp)
    (T.character p) (T.continuous_char p) e (T.positive p) (T.conductor p) C).2 arg
  refine ⟨hv.1,(hv.2 P⁻¹ ht).trans ?_⟩
  have hn : P^(n-1)*P = P^n := by rw [← pow_succ,Nat.sub_add_cancel (NeZero.pos n)]
  have symb (x : (LocalField F v)ˣ) (hx : ‖x.val‖ = 1) : d.symbol v C x = d.symbol v P x :=
    hC ▸ d.symbol_twist_argument p.val (h.good.2.2 p.val hp).1 B P x hB hx
  have phase : -(P⁻¹.val^n)/C.val = -B.val/P.val := by
    rw [hC,Units.val_inv_eq_inv_val,Units.val_inv_eq_inv_val,Units.val_mul,Units.val_pow_eq_pow_val,
      inv_pow,div_inv_eq_mul,← show P.val^(n-1)*P.val = P.val^n from congrArg Units.val hn]
    field_simp
  rw [phase,Units.val_inv_eq_inv_val]
  congr 1
  unfold unitGauss
  congr 1
  funext x
  split_ifs with hx
  · dsimp only
    rw [show d.symbol (.inr p.val) C x = _ from symb x hx]
    rfl
  · rfl

theorem epsilon_norm {S : Finset (Place F)} (h : d.ClassicalSetting S)
    (f b : NonzeroInteger S) (T : Twist (n := n) S f) (hb : IsCoprime b.val f.val) :
    ‖d.epsilon T (fieldUnit b)‖ = 1 := by
  rw [epsilon,norm_prod]
  exact Finset.prod_eq_one fun p _ => (d.epsilon_factor h f b T hb p).1

theorem epsilon_gauss {S : Finset (Place F)} (h : d.ClassicalSetting S)
    (f b : NonzeroInteger S) (T : Twist (n := n) S f) (hb : IsCoprime b.val f.val) :
    d.epsilon T (fieldUnit b) = ∏ p : T.primes,
      let v : Place F := .inr p.val
      let f' := atPlace v (fieldUnit f)
      (p.val.asIdeal.absNorm : ℂ) ^ T.exponent p *
        d.unitGauss p.val (charWeight (T.character p ^ n)) ((f' : LocalField F v)⁻¹) *
        d.unitGauss p.val (fun x => conj (charWeight (T.character p) x) * d.symbol v f' x)
          (-(diagonal F v (fieldUnit b)) / f') := by
  exact Finset.prod_congr rfl fun p _ => (d.epsilon_factor h f b T hb p).2

private theorem charWeight_unit_mul {p : Prime F} (χ : UnitChar p) (u : integralUnits p)
    (x : (LocalField F (.inr p))ˣ) :
    charWeight χ (u.val*x) = (χ u : ℂ) * charWeight χ x := by
  by_cases hx : x ∈ integralUnits p
  · have hux := (integralUnits p).mul_mem u.property hx
    simp only [charWeight,dif_pos hux,dif_pos hx]
    exact (congrArg ((↑) : Circle → ℂ) (χ.map_mul u ⟨x,hx⟩)).trans (Circle.coe_mul _ _)
  · have hux : u.val*x ∉ integralUnits p := fun hm => hx
           (((integralUnits p).mul_mem_cancel_left u.property).mp hm)
    simp only [charWeight,dif_neg hx,dif_neg hux,mul_zero]

omit [NeZero n] in
/-- A unit character whose n-th power is nontrivial has zero moment on
each n-th-power class, as in the paper's twisted-vanishing lemma. -/
theorem twisted_moment_vanishes (p : Prime F) (χ : UnitChar p) (hχ : χ^n ≠ 1)
    (β : PowerClass n (.inr p)) :
    d.lineIntegral (.inr p) (fun x => if (QuotientGroup.mk x : PowerClass n (.inr p)) = β then
      charWeight χ x * (modulus F (.inr p) x.val ^ (1 / (n : ℝ)) : ℝ) else 0) = 0 := by
  obtain ⟨u,hu⟩ : ∃ u : integralUnits p, (χ^n) u ≠ 1 := by
    by_contra! he
    exact hχ (MonoidHom.ext he)
  let a := u.val^n
  let z : ℂ := χ (u^n)
  have hz : z ≠ 1 := by
    intro h
    apply hu
    apply Subtype.ext
    simpa only [z,map_pow,MonoidHom.pow_apply,Circle.coe_one] using h
  let g (x : (LocalField F (.inr p))ˣ) : ℂ :=
    if (QuotientGroup.mk x : PowerClass n (.inr p)) = β then
      charWeight χ x * (modulus F (.inr p) x.val ^ (1/(n : ℝ)) : ℝ) else 0
  have hm (x : (LocalField F (.inr p))ˣ) :
      modulus F (.inr p) (a*x).val = modulus F (.inr p) x.val := by
    change ‖a.val*x.val‖ = ‖x.val‖
    rw [norm_mul,show ‖a.val‖ = 1 from (u^n).property,one_mul]
  have trans (x : (LocalField F (.inr p))ˣ) : g (a*x) = z*g x := by
    have same : (QuotientGroup.mk (a*x) : PowerClass n (.inr p)) = QuotientGroup.mk x :=
      QuotientGroup.eq_iff_div_mem.mpr (show (a*x)/x ∈ (powMonoidHom n : _ →* _).range by
        rw [mul_div_cancel_right]; exact ⟨u.val,rfl⟩)
    simp only [g,same,hm]
    split_ifs
    · rw [show charWeight χ (a*x) = z*charWeight χ x from charWeight_unit_mul χ (u^n) x,mul_assoc]
    · rw [mul_zero]
  have he := d.lineIntegral_mul (.inr p) a g
  simp_rw [trans,d.lineIntegral_const_mul] at he
  change d.lineIntegral (.inr p) g = 0
  exact (mul_eq_zero.mp (show (z-1)*d.lineIntegral (.inr p) g = 0 by
    rw [sub_mul,one_mul,he,sub_self])).resolve_left (sub_ne_zero.mpr hz)

omit [NeZero n] in
/-- A positive conductor exponent gives the nontriviality needed to kill
every power-class term in the adelic line formula. -/
theorem moment_eq_zero_of_twistedComponent {S : Finset (Place F)} (W : Weights S)
    (p : Prime F) (hp : Sum.inr p ∈ S) (χ : UnitChar p) (e : ℕ) (he : 0 < e)
    (cond : IsLeast {k | trivialAtLevel (χ^n) k} e) (hW : W ⟨.inr p,hp⟩ = charWeight χ)
    (β : Classes n S) : d.moment W β = 0 := by
  have hχ : χ^n ≠ 1 := by
    intro h
    have hzero : trivialAtLevel (χ^n) 0 := fun u _ => by rw [h]; rfl
    exact he.not_ge (cond.2 hzero)
  unfold moment
  let v : S := ⟨.inr p,hp⟩
  apply Finset.prod_eq_zero (Finset.mem_univ v)
  change d.lineIntegral (.inr p) (fun x => if (QuotientGroup.mk x : PowerClass n (.inr p)) = β v then
    W ⟨.inr p,hp⟩ x * _ else 0) = 0
  rw [hW]
  exact d.twisted_moment_vanishes p χ hχ (β v)

theorem compact_open_integralUnits (p : Prime F) :
    IsCompact (integralUnits p : Set (LocalField F (.inr p))ˣ) ∧
    IsOpen (integralUnits p : Set (LocalField F (.inr p))ˣ) := by
  let K := p.adicCompletion F
  letI : NontriviallyNormedField K := FinitePlace.nontriviallyNormedCompletion p
  letI : ProperSpace K := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K
  let U : Subgroup Kˣ := integralUnits p
  have hopen : IsOpen (U : Set Kˣ) := by
    have ho := IsUltrametricDist.isOpen_sphere (0 : K) (one_ne_zero : (1 : ℝ) ≠ 0)
    change IsOpen (Units.val ⁻¹' {y : K | ‖y‖ = 1})
    simpa only [Metric.sphere,dist_zero_right] using ho.preimage Units.continuous_val
  have hcomp : IsCompact (U : Set Kˣ) := by
    apply Units.isEmbedding_val₀.isCompact_iff.mpr
    have hi : Units.val '' (U : Set Kˣ) = Metric.sphere (0 : K) 1 := by
      ext y
      rw [Metric.mem_sphere,dist_zero_right]
      refine ⟨fun ⟨a,ha,hy⟩ => hy ▸ ha, fun h => ?_⟩
      exact ⟨Units.mk0 y (norm_ne_zero_iff.mp (h ▸ one_ne_zero)), h,rfl⟩
    rw [hi]
    exact isCompact_sphere _ _
  exact ⟨hcomp,hopen⟩

/-- The unit character extended by zero is a compactly supported, locally constant test weight. -/
theorem charWeight_test (p : Prime F) (χ : UnitChar p) (hχ : Continuous χ)
    (e : ℕ) (he : trivialAtLevel (χ^n) e) : TestWeight (.inr p) (charWeight χ) := by
  let U := integralUnits p
  obtain ⟨hcomp,hopen⟩ := compact_open_integralUnits p
  have hclosed := hcomp.isClosed
  have hval : Continuous (fun x : U => (χ x : ℂ)) := continuous_subtype_val.comp hχ
  let bad := (Polynomial.nthRootsFinset n (1 : ℂ)).erase 1
  have near : ∀ᶠ x : U in 𝓝 1, (χ x : ℂ) ∉ bad := hval.continuousAt.eventually
    (bad.finite_toSet.isClosed.isOpen_compl.mem_nhds (by change (χ (1 : integralUnits p) : ℂ) ∉ bad; rw [map_one,Circle.coe_one]; exact Finset.notMem_erase _ _))
  let q : ℝ := p.asIdeal.absNorm
  have hq : 0 < q := by dsimp only [q]; exact_mod_cast (Nat.zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm p))
  have small : ∀ᶠ x : U in 𝓝 1, ‖((x.val : LocalField F (.inr p))-1)‖ < (q^e)⁻¹ := by
    have hc : Continuous (fun x : U => ‖((x.val : LocalField F (.inr p))-1)‖) :=
      ((Units.continuous_val.comp continuous_subtype_val).sub continuous_const).norm
    exact hc.continuousAt.eventually_lt continuousAt_const (by simpa using inv_pos.mpr (pow_pos hq e))
  have ker : ∀ᶠ x : U in 𝓝 1, χ x = 1 := by
    filter_upwards [small,near] with x hx hbad
    apply Subtype.ext
    change (χ x : ℂ) = 1
    by_contra hne
    apply hbad
    apply Finset.mem_erase.mpr
    refine ⟨hne,(Polynomial.mem_nthRootsFinset (NeZero.pos n) 1).mpr ?_⟩
    exact (Circle.coe_pow _ _).symm.trans (congrArg ((↑) : Circle → ℂ) (show χ x ^ n = 1 from he x (Or.inr hx.le)))
  have lc : IsLocallyConstant χ := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro u
    have ht : Tendsto (fun x : U => x/u) (𝓝 u) (𝓝 1) := by simpa using (continuous_id.div_const u).tendsto u
    filter_upwards [ht.eventually ker] with x hx
    change χ (x/u) = 1 at hx
    rwa [map_div,div_eq_one] at hx
  refine ⟨HasCompactSupport.intro hcomp (fun x hx => dif_neg hx), ?_⟩
  change IsLocallyConstant (charWeight χ)
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x ∈ U
  · let u : U := ⟨x,hx⟩
    rw [← show (Subtype.val u) = x from rfl, ← hopen.isOpenEmbedding_subtypeVal.map_nhds_eq u]
    change ∀ᶠ y : U in 𝓝 u, charWeight χ y.val = charWeight χ u.val
    filter_upwards [lc.eventually_eq u] with y hy
    rw [charWeight,dif_pos (show y.val ∈ integralUnits p from y.property),
      charWeight,dif_pos (show u.val ∈ integralUnits p from u.property)]
    exact congrArg ((↑) : Circle → ℂ) (show χ y = χ u from hy)
  · filter_upwards [hclosed.isOpen_compl.mem_nhds hx] with y hy
    simp only [charWeight,dif_neg (show y ∉ integralUnits p from hy),dif_neg (show x ∉ integralUnits p from hx)]

/-- Unit covariance of the transformed character weight, equation (first-symbol). -/
theorem dual_charWeight_unit (p : Prime F) (hp : p.asIdeal.absNorm.Coprime n) (χ : UnitChar p)
    (hW : TestWeight (.inr p) (charWeight χ)) (a : (LocalField F (.inr p))ˣ) (u : integralUnits p) :
    d.dualWeight (.inr p) (charWeight χ) (a*u.val) =
      d.dualWeight (.inr p) (charWeight χ) a * (χ u : ℂ)⁻¹ * d.symbol (.inr p) a u.val := by
  let v : Place F := .inr p
  let W := charWeight χ
  have scaled : (fun x => W (x/u.val)) = fun x => (χ u : ℂ)⁻¹ * W x := by
    funext x
    simpa only [W,div_eq_mul_inv,mul_comm x,Subgroup.coe_inv, map_inv,Circle.coe_inv] using charWeight_unit_mul χ u⁻¹ x
  have twist : (fun x => W x / d.symbol v x u.val) = W := by
    funext x
    by_cases hx : x ∈ integralUnits p
    · have hs : d.symbol v x u.val = 1 := congrArg Units.val (d.unitPairing_tame_units p hp x u.val hx u.property)
      rw [hs,div_one]
    · simp only [W,charWeight,dif_neg hx,zero_div]
  have sk : d.unitPairing v u.val (-a) * d.unitPairing v (-a) u.val = 1 := by
    apply eq_inv_iff_mul_eq_one.mp
    exact (d.lineSymbol v (d.finite_steinberg p)).skew u.val (-a)
  have neg : d.unitPairing v (-a) u.val = d.unitPairing v a u.val := by
    rw [show -a = (-1)*a by simp,map_mul,MonoidHom.mul_apply,
      d.unitPairing_tame_units p hp (-1) u.val (by simp) u.property,one_mul]
  rw [neg] at sk
  have hs := congrArg Units.val sk
  change d.symbol v u.val (-a) * d.symbol v a u.val = 1 at hs
  have he := d.dual_dilation v W hW u.val a
  rw [scaled,twist,d.dualWeight_const_mul,mul_comm u.val a] at he
  calc
    _ = d.dualWeight v W (a*u.val) * (d.symbol v u.val (-a) * d.symbol v a u.val) := by rw [hs,mul_one]
    _ = (d.symbol v u.val (-a) * d.dualWeight v W (a*u.val)) * d.symbol v a u.val := by ring
    _ = _ := by rw [← he]; ring

/-- The scaled dual weight at a conductor prime, after the change of index
in Theorem 10.34. The extended character on the right also gives the vanishing off units. -/
theorem dual_conductor_factor {S : Finset (Place F)} (h : d.ClassicalSetting S)
    (f b : NonzeroInteger S) (T : Twist (n := n) S f) (hb : IsCoprime b.val f.val)
    (p : T.primes) (x : (LocalField F (.inr p.val))ˣ) :
    let v : Place F := .inr p.val
    let B := atPlace v (fieldUnit b)
    let P := atPlace v (fieldUnit f)
    let W := charWeight (T.character p)
    (d.scaled (fieldUnit b)).dualWeight v W (x/(B^n*P^(n-1))) =
      d.dualWeight v W (B*P^(n-1))⁻¹ * conj (W x) * d.symbol v P x := by
  let v : Place F := .inr p.val
  let B := atPlace v (fieldUnit b)
  let P := atPlace v (fieldUnit f)
  let C := (B*P^(n-1))⁻¹
  let W := charWeight (T.character p)
  let χ := T.character p
  have hp := T.outside p.val p.property
  have tame := (h.good.2.2 p.val hp).1
  have hB : ‖B.val‖ = 1 := T.norm_frequency hb p
  have hW : TestWeight v W := charWeight_test p.val χ (T.continuous_char p) _ (T.conductor p).1
  have trivial : (fun y => W y * d.symbol v y B) = W := by
    funext y
    by_cases hy : y ∈ integralUnits p.val
    · rw [show d.symbol v y B = 1 from congrArg Units.val (d.unitPairing_tame_units p.val tame y B hy hB),mul_one]
    · simp only [W,charWeight,dif_neg hy,zero_mul]
  have hn : B^(n-1)*B = B^n := by rw [← pow_succ,Nat.sub_add_cancel (NeZero.pos n)]
  have arg : B^(n-1)*(x/(B^n*P^(n-1))) = C*x := by
    rw [← hn,mul_assoc (B^(n-1)),← mul_div_assoc,mul_div_mul_left_eq_div,div_eq_inv_mul]
  change (d.scaled (fieldUnit b)).dualWeight v W _ = d.dualWeight v W C * conj (W x) * d.symbol v P x
  rw [d.dual_scaled v W hW]
  change d.dualWeight v (fun y => W y * d.symbol v y B) (B^(n-1)*(x/(B^n*P^(n-1)))) = _
  rw [trivial,arg]
  by_cases hx : x ∈ integralUnits p.val
  · let u : integralUnits p.val := ⟨x,hx⟩
    have he := d.dual_charWeight_unit p.val tame χ hW C u
    change d.dualWeight v W (C*x) = d.dualWeight v W C * (χ u : ℂ)⁻¹ * d.symbol v C x at he
    rw [he,show d.symbol v C x = d.symbol v P x from d.symbol_twist_argument p.val tame B P x hB hx]
    have hval : W x = (χ u : ℂ) := dif_pos hx
    rw [hval,← Circle.coe_inv, Circle.coe_inv_eq_conj]
  · let q : ℝ := p.val.asIdeal.absNorm
    let e := T.exponent p
    have hC : ‖C.val‖ = q^((n-1)*e) := norm_twist_argument B P hB (T.generator p)
    have off : ‖(C*x).val‖ ≠ q^((n-1)*e) := by
      rw [← hC,Units.val_mul,norm_mul]
      exact fun he => hx ((mul_eq_left₀ (norm_ne_zero_iff.mpr C.ne_zero)).mp he)
    have zero := (d.twistedVector p.val tame (h.unramified p.val hp) χ (T.continuous_char p)
      e (T.positive p) (T.conductor p) (C*x)).1 off
    rw [show d.dualWeight v W (C*x) = 0 from zero,show W x = 0 from dif_neg hx,map_zero,mul_zero,zero_mul]

end MetaplecticPoisson.Datum
