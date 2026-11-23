import MetaplecticSummation.PlaceApproximation
import MetaplecticSummation.HilbertTame

/-! Weak approximation at a finite set of finite and infinite places. -/
noncomputable section
namespace MetaplecticPoisson
open NumberField IsDedekindDomain Filter Set
open scoped Topology
variable {F : Type} [Field F] [NumberField F]

private def placeAbs : Place F → AbsoluteValue F ℝ
  | .inl w => w.1
  | .inr p => NumberField.HeightOneSpectrum.adicAbv F p

private theorem infinite_not_equiv_finite (w : InfinitePlace F) (p : HeightOneSpectrum (𝓞 F)) :
    ¬ w.1.IsEquiv (NumberField.HeightOneSpectrum.adicAbv F p) := by
  intro h
  have hh := h.le_one_iff.mpr (NumberField.HeightOneSpectrum.adicAbv_natCast_le_one F p 2)
  change w (2 : ℕ) ≤ 1 at hh
  rw [w.map_natCast] at hh
  norm_num at hh

private theorem placeAbs_inequivalent (v w : Place F) (hn : v ≠ w) :
    ¬ (placeAbs v).IsEquiv (placeAbs w) := by
  cases v with
  | inl i =>
    cases w with
    | inl j => exact fun h => hn (congrArg Sum.inl (InfinitePlace.eq_iff_isEquiv.mpr h))
    | inr q => exact infinite_not_equiv_finite i q
  | inr p =>
    cases w with
    | inl j => exact fun h => infinite_not_equiv_finite j p h.symm
    | inr q => exact FinitePlace.not_isEquiv_adicAbv (fun h => hn (congrArg Sum.inr h))

/-- Simultaneous weak approximation in the precise completion models used by the symbol family. -/
theorem denseRange_diagonal_places (S : Finset (Place F)) :
    DenseRange (fun x : F => fun v : S => diagonal F v.val x) := by
  let φ (v : Place F) : WithAbs (placeAbs v) → LocalField F v :=
    (diagonal F v) ∘ (WithAbs.equiv (placeAbs v))
  have hc (v : Place F) : Continuous (φ v) := by
    cases v with
    | inl w => exact InfinitePlace.Completion.continuous_coe w
    | inr p => exact (FinitePlace.isometry_algebraMap_adicCompletion p).continuous
  have hd (v : Place F) : DenseRange (φ v) := by
    cases v with
    | inl w => exact InfinitePlace.Completion.denseRange_coe w
    | inr p =>
      change DenseRange ((algebraMap F (p.adicCompletion F)) ∘ (WithAbs.equiv (placeAbs (.inr p))))
      have hd := HeightOneSpectrum.denseRange_algebraMap (K := F) p
      unfold DenseRange at hd ⊢
      convert hd using 1
      exact (WithAbs.equiv (placeAbs (.inr p))).surjective.range_comp _
  have hn (v : S) : (placeAbs v.val).IsNontrivial := by
    rcases v with ⟨w|p,_⟩
    · exact w.isNontrivial
    · exact FinitePlace.adicAbv_isNontrivial p
  have ha := AbsoluteValue.denseRange_algebraMap_pi (v := fun v : S => placeAbs v.val) hn
    (fun i j h => placeAbs_inequivalent _ _ (fun he => h (Subtype.ext he)))
  exact (DenseRange.piMap (fun v : S => hd v.val)).comp ha
    (continuous_pi fun v => (hc v.val).comp (continuous_apply v))


private def unitDiagonal (S : Finset (Place F)) (x : Fˣ) (i : S) : (LocalField F i.val)ˣ :=
  Units.map (diagonal F i.val).toMonoidHom x

private theorem denseRange_unitDiagonal (S : Finset (Place F)) (j : S) :
    DenseRange (unitDiagonal S) := by
  classical
  let val (a : ∀ i : S, (LocalField F i.val)ˣ) := fun i => (a i).val
  have hop : IsOpenMap val := (Topology.IsOpenEmbedding.piMap (fun i : S => by
    have he : Topology.IsOpenEmbedding (Units.val : (LocalField F i.val)ˣ → _) := by
      refine ⟨Units.isEmbedding_val₀,?_⟩
      rw [show range (Units.val : (LocalField F i.val)ˣ → _) = {0}ᶜ from
        Set.ext fun x => ⟨fun ⟨u,he⟩ => he ▸ u.ne_zero, fun hx => ⟨Units.mk0 x hx,rfl⟩⟩]
      exact isClosed_singleton.isOpen_compl
    exact he)).isOpenMap
  apply dense_iff_inter_open.mpr
  intro U ho hU
  obtain ⟨x,y,hy,he⟩ := (denseRange_diagonal_places S).exists_mem_open (hop U ho) (hU.image val)
  have hx : x ≠ 0 := by
    intro hz
    exact (y j).ne_zero ((congrFun he j).trans (hz ▸ map_zero _))
  refine ⟨y,hy,Units.mk0 x hx,?_⟩
  exact funext fun i => Units.ext (congrFun he i).symm

namespace IsHilbertFamily
variable {n : ℕ} [NeZero n] {H J : SymbolFamily F n}

/-- A reciprocal family is uniquely determined outside any finite exceptional
set, once its local pairings are continuous. -/
theorem eq_of_agree_off_finset (hH : IsHilbertFamily F n H) (hJ : IsHilbertFamily F n J)
    (S : Finset (Place F)) (outside : ∀ v ∉ S, H v = J v) : H = J := by
  classical
  letI : TopologicalSpace (Mu F n) := ⊥
  letI : DiscreteTopology (Mu F n) := ⟨rfl⟩
  have cont {P : SymbolFamily F n} (hP : IsHilbertFamily F n P) (v : Place F) :
      Continuous (fun z : (LocalField F v)ˣ × (LocalField F v)ˣ => P v z.1 z.2) := by
    let e (z : Mu F n) := diagonal F v (z.val : F)
    have eqTop : TopologicalSpace.induced e inferInstance = (⊥ : TopologicalSpace (Mu F n)) := by
      letI : TopologicalSpace (Mu F n) := TopologicalSpace.induced e inferInstance
      have he : Topology.IsEmbedding e := ⟨⟨rfl⟩,(diagonal F v).injective.comp
        (Units.val_injective.comp Subtype.val_injective)⟩
      letI : T1Space (Mu F n) := he.t1Space
      exact DiscreteTopology.eq_bot
    have hc : @Continuous _ _ _ (TopologicalSpace.induced e inferInstance) (fun z : (LocalField F v)ˣ × (LocalField F v)ˣ => P v z.1 z.2) := continuous_induced_rng.mpr (hP.continuous_pair v)
    rw [eqTop] at hc
    exact hc
  funext v a b
  by_cases hv : v ∈ S
  · let j : S := ⟨v,hv⟩
    let X := (i : S) → (LocalField F i.val)ˣ
    let product (A : X × X) := ∏ i : S, H i.val (A.1 i) (A.2 i) / J i.val (A.1 i) (A.2 i)
    have hc : Continuous product := by
      apply continuous_finsetProd
      intro i _
      have hxy : Continuous (fun z : X × X => (z.1 i,z.2 i)) :=
        ((continuous_apply i).comp continuous_fst).prodMk ((continuous_apply i).comp continuous_snd)
      exact ((cont hH i.val).comp hxy).div' ((cont hJ i.val).comp hxy)
    have dens := denseRange_unitDiagonal S j
    have eqn : product = fun _ => 1 := by
      apply (dens.prodMap dens).equalizer hc continuous_const
      funext z
      let value (P : SymbolFamily F n) (w : Place F) := P w
        (Units.map (diagonal F w).toMonoidHom z.1) (Units.map (diagonal F w).toMonoidHom z.2)
      have hr := finprod_div_distrib (eventually_cofinite.mp (hH.unramified z.1 z.2))
        (eventually_cofinite.mp (hJ.unramified z.1 z.2))
      have one : (∏ᶠ w, value H w / value J w) = 1 := hr.trans (by rw [hH.reciprocity,hJ.reciprocity,div_one])
      rw [finprod_eq_prod_of_mulSupport_subset (s := S) _ (by
        intro w hw
        by_contra h
        exact hw (by simp only [value,outside w h,div_self'])),← Finset.prod_attach] at one
      exact one
    let A : X := Function.update 1 j a
    let B : X := Function.update 1 j b
    have hh := congrFun eqn (A,B)
    change (∏ i : S, H i.val (A i) (B i) / J i.val (A i) (B i)) = 1 at hh
    rw [Finset.prod_eq_single j] at hh
    · exact div_eq_one.mp (by simpa [A,B] using hh)
    · intro i _ hne
      simp only [A,B,Function.update_of_ne hne,Pi.one_apply]
      have h {P : SymbolFamily F n} (hP : IsHilbertFamily F n P) : P i.val 1 1 = 1 :=
        (MonoidHom.mk' (fun x => P i.val x 1) (fun x y => hP.mul_left _ x y _)).map_one
      rw [h hH,h hJ,div_one]
    · simp
  · exact congrFun (congrFun (outside v hv) a) b


private theorem eq_on_tame {ζ : F} (hζ : IsPrimitiveRoot ζ n) (hH : IsHilbertFamily F n H)
    (hJ : IsHilbertFamily F n J) (p : HeightOneSpectrum (𝓞 F)) (hp : p.asIdeal.absNorm.Coprime n) :
    H (.inr p) = J (.inr p) := by
  let v : Place F := .inr p
  let K := p.adicCompletion F
  obtain ⟨π,hπ⟩ := FinitePlace.exists_norm_uniformizer p
  have on_generators (f g : Kˣ →* Mu F n) (hval : f π = g π)
      (hu : ∀ u : Kˣ, ‖u.val‖ = 1 → f u = g u) (a : Kˣ) : f a = g a := by
    obtain ⟨j,hj⟩ := Datum.norm_zpow_residue_card p a
    let b := a / π^(-j)
    have hq : (p.asIdeal.absNorm : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm p)).ne'
    have hb : ‖b.val‖ = 1 := by
      simp [b,Units.val_zpow_eq_zpow_val,norm_zpow,hπ,hj,zpow_ne_zero _ hq]
    have he : a = b * π^(-j) := (div_mul_cancel ..).symm
    rw [he,map_mul,map_mul,map_zpow,map_zpow,hval,hu b hb]
  let left (P : SymbolFamily F n) (hP : IsHilbertFamily F n P) (b : Kˣ) : Kˣ →* Mu F n :=
    MonoidHom.mk' (fun x => P v x b) (fun x y => hP.mul_left v x y b)
  let right (P : SymbolFamily F n) (hP : IsHilbertFamily F n P) (a : Kˣ) : Kˣ →* Mu F n :=
    MonoidHom.mk' (P v a) (hP.mul_right v a)
  have hunit (a b : Kˣ) (hb : ‖b.val‖ = 1) : H v a b = J v a b :=
    on_generators (left H hH b) (left J hJ b) (Datum.tame_uniformizer_value_unique p hζ hH hJ hp π b hπ hb)
      (fun u hu => (hH.tame_units p hp u b hu hb).trans (hJ.tame_units p hp u b hu hb).symm) a
  have hππ : H v π π = J v π π := by
    have neg (P : SymbolFamily F n) (hP : IsHilbertFamily F n P) :
        P v π (-1) * P v π π = 1 := (hP.mul_right v π (-1) π).symm.trans (by
          have he : (-1 : Kˣ) * π = -π := Units.ext (neg_one_mul π.val)
          exact (congrArg (fun x : Kˣ => P v π x) he).trans (hP.neg_self v π))
    apply mul_left_cancel (a := H v π (-1))
    exact (neg H hH).trans ((neg J hJ).symm.trans
      (congrArg (· * J v π π) (hunit π (-1) (by change ‖(-1 : K)‖ = 1; simp)).symm))
  have firstπ (a : Kˣ) : H v π a = J v π a :=
    on_generators (right H hH π) (right J hJ π) hππ (hunit π) a
  funext a b
  apply on_generators (right H hH a) (right J hJ a) _ (hunit a) b
  exact (eq_inv_of_mul_eq_one_left (hH.skew v a π)).trans
    ((congrArg Inv.inv (firstπ a)).trans (eq_inv_of_mul_eq_one_left (hJ.skew v a π)).symm)

/-- Over a number field, tame normalization and reciprocity determine the
entire continuous symbol family, including every wild and infinite place. -/
theorem unique {ζ : F} (hζ : IsPrimitiveRoot ζ n) (hH : IsHilbertFamily F n H)
    (hJ : IsHilbertFamily F n J) : H = J := by
  classical
  let bad := (FinitePlace.finite_places_over_degree (K := F) n).toFinset
  let S : Finset (Place F) := Finset.univ.map (Function.Embedding.inl) ∪ bad.map (Function.Embedding.inr)
  apply eq_of_agree_off_finset hH hJ S
  intro v hv
  cases v with
  | inl w => exact False.elim (hv (by simp [S]))
  | inr p =>
    apply eq_on_tame hζ hH hJ p
    apply FinitePlace.tame_of_degree_not_mem n p
    intro hp
    exact hv (by simp [S,bad,hp])

end IsHilbertFamily

end MetaplecticPoisson
