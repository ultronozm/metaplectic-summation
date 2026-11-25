import MetaplecticSummation.LineSmoothness
import Mathlib.Analysis.Distribution.TemperateGrowth

/-! Derivatives of the archimedean Radon charts in the original line parameter
(Lemma 4.2(iii), "the same holds for all derivatives").

The Radon chart is the linearized line integral composed with (U, V, τ) ↦ (U, V, s τⁿ / U).
The derivatives of this map grow polynomially in τ, uniformly for U in a compact annulus,
and the linearized integral decays rapidly in its last variable with all derivatives. The
Faà di Bruno bound `norm_iteratedFDerivWithin_comp_le` combines the two. -/

noncomputable section
namespace MetaplecticPoisson
open MeasureTheory Set Filter
open scoped Topology ContDiff Nat

section
variable {E F' G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F'] [NormedSpace ℝ F']
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem iteratedFDeriv_comp_clm_of_isOpen' {W : Set F'} (hW : IsOpen W) {f : F' → G}
    (hf : ContDiffOn ℝ ∞ f W) (A : E →L[ℝ] F') {P : E} (hP : A P ∈ W) (k : ℕ) :
    iteratedFDeriv ℝ k (f ∘ A) P = (iteratedFDeriv ℝ k f (A P)).compContinuousLinearMap (fun _ => A) := by
  have hV : IsOpen (A ⁻¹' W) := hW.preimage A.continuous
  have h := A.iteratedFDerivWithin_comp_right hf hW.uniqueDiffOn hV.uniqueDiffOn hP (i := k)
    (by exact_mod_cast le_top)
  rw [iteratedFDerivWithin_of_isOpen k hV hP,iteratedFDerivWithin_of_isOpen k hW hP] at h
  exact h

end

variable {L : Type} [NormedField L] [NormedAlgebra ℝ L]

/-- Derivatives of the inverse are bounded on a compact annulus. -/
theorem inv_deriv_bound_annulus [ProperSpace L] (k : ℕ) {δ B : ℝ} (hδ : 0 < δ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ i ≤ k, ∀ U : L, δ ≤ ‖U‖ → ‖U‖ ≤ B → ‖iteratedFDeriv ℝ i (fun U : L => U⁻¹) U‖ ≤ M := by
  let W : Set L := {U | U ≠ 0}
  have hW : IsOpen W := isOpen_ne
  have hinv : ContDiffOn ℝ ∞ (fun U : L => U⁻¹) W := fun U hU => (contDiffAt_inv ℝ hU).contDiffWithinAt
  let Kₐ : Set L := {U | δ ≤ ‖U‖} ∩ Metric.closedBall 0 B
  have hK : IsCompact Kₐ := (isCompact_closedBall 0 B).inter_left (isClosed_le continuous_const continuous_norm)
  have hKW : Kₐ ⊆ W := fun U hU => norm_pos_iff.mp (hδ.trans_le hU.1)
  have hb (i : ℕ) : ∃ M, ∀ U ∈ Kₐ, ‖iteratedFDeriv ℝ i (fun U : L => U⁻¹) U‖ ≤ M := by
    have hc : ContinuousOn (iteratedFDeriv ℝ i (fun U : L => U⁻¹)) W := by
      have h := hinv.continuousOn_iteratedFDerivWithin (m := i) (by exact_mod_cast le_top) hW.uniqueDiffOn
      exact h.congr fun u hu => (iteratedFDerivWithin_of_isOpen i hW hu).symm
    obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn (hc.mono hKW)
    exact ⟨M,hM⟩
  choose M hM using hb
  refine ⟨∑ i ∈ Finset.range (k+1), max (M i) 0,by positivity,fun i hi U h1 h2 => ?_⟩
  calc _ ≤ max (M i) 0 := (hM i U ⟨h1,by simpa using h2⟩).trans (le_max_left _ _)
    _ ≤ _ := Finset.single_le_sum (f := fun i => max (M i) 0) (fun _ _ => le_max_right _ _)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))

/-- The map (U, V, τ) ↦ (U, V, s τⁿ / U) used to pass from the linearized line integral to the
Radon chart. -/
def reciprocalCoords (n : ℕ) (s : L) (P : L × L × L) : L × L × L := (P.1, P.2.1, s * (P.2.2 ^ n * P.1⁻¹))

theorem contDiffOn_reciprocalCoords (n : ℕ) (s : L) :
    ContDiffOn ℝ ∞ (reciprocalCoords n s) {P | P.1 ≠ 0} := by
  intro P hP
  have hP' : P.1 ≠ 0 := hP
  refine ContDiffAt.contDiffWithinAt ?_
  refine contDiffAt_fst.prodMk (contDiffAt_fst.comp P contDiffAt_snd |>.prodMk ?_)
  exact contDiffAt_const.mul (((contDiffAt_snd.comp P contDiffAt_snd).pow n).mul
    ((contDiffAt_inv ℝ hP').comp P contDiffAt_fst))

/-- The derivatives of `reciprocalCoords` grow at most polynomially in τ, uniformly for U in a
compact annulus and V bounded. -/
theorem reciprocalCoords_deriv_bound [ProperSpace L] (n k : ℕ) (s : L) {δ B : ℝ} (hδ : 0 < δ) :
    ∃ c : ℝ, ∃ q : ℕ, 0 ≤ c ∧ ∀ i ≤ k, ∀ P : L × L × L, δ ≤ ‖P.1‖ → ‖P.1‖ ≤ B → ‖P.2.1‖ ≤ B →
      ‖iteratedFDerivWithin ℝ i (reciprocalCoords n s) {P | P.1 ≠ 0} P‖ ≤ c * (1+‖P.2.2‖)^q := by
  let S : Set (L × L × L) := {P | P.1 ≠ 0}
  have hS : IsOpen S := isOpen_ne_fun continuous_fst continuous_const
  let L₀ : (L × L × L) →L[ℝ] (L × L × L) :=
    (ContinuousLinearMap.fst ℝ L (L × L)).prod (((ContinuousLinearMap.fst ℝ L L).comp
      (ContinuousLinearMap.snd ℝ L (L × L))).prod 0)
  let E : L →L[ℝ] (L × L × L) := (0 : L →L[ℝ] L).prod ((0 : L →L[ℝ] L).prod (ContinuousLinearMap.id ℝ L))
  have hE : ‖E‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun c => ?_
    simp [E,Prod.norm_def]
  let f : L × L × L → L := fun P => s * P.2.2 ^ n
  let g : L × L × L → L := fun P => P.1⁻¹
  have hf : f.HasTemperateGrowth := by
    have hA := ((ContinuousLinearMap.snd ℝ L L).comp (ContinuousLinearMap.snd ℝ L (L × L))).hasTemperateGrowth
    have h := (Function.HasTemperateGrowth.const s).mul (hA.pow n)
    convert h using 1
    funext P; simp [f]
  have hκ : reciprocalCoords n s = L₀ + E ∘ (fun P => f P * g P) := by
    funext P; ext <;> simp [reciprocalCoords,L₀,E,f,g,mul_assoc]
  obtain ⟨k0,C0,hC0,H0⟩ := L₀.hasTemperateGrowth.norm_iteratedFDeriv_le_uniform k
  obtain ⟨k1,C1,hC1,H1⟩ := hf.norm_iteratedFDeriv_le_uniform k
  obtain ⟨Mi,hMi,HMi⟩ := inv_deriv_bound_annulus (L := L) k hδ (B := B)
  have hfS : ContDiffOn ℝ ∞ f S := hf.1.contDiffOn
  have hgS : ContDiffOn ℝ ∞ g S := fun P hP =>
    ((contDiffAt_inv ℝ (show P.1 ≠ 0 from hP)).comp P contDiffAt_fst).contDiffWithinAt
  have hhS : ContDiffOn ℝ ∞ (fun P => f P * g P) S := hfS.mul hgS
  let B' := max B 0
  refine ⟨(C0 + 2^k * C1 * Mi) * (1+B')^(k0+k1),k0+k1,by positivity,fun i hi P h1 h2 h3 => ?_⟩
  have hP : P ∈ S := norm_pos_iff.mp (hδ.trans_le h1)
  have hPnorm : 1 + ‖P‖ ≤ (1+B') * (1+‖P.2.2‖) := by
    have : ‖P‖ ≤ B' + ‖P.2.2‖ := by
      rw [Prod.norm_def,Prod.norm_def]
      refine max_le ?_ (max_le ?_ ?_) <;>
        nlinarith [le_max_left B 0,le_max_right B 0,norm_nonneg P.2.2,norm_nonneg P.1,norm_nonneg P.2.1]
    nlinarith [norm_nonneg P.2.2,le_max_right B 0]
  have hP1 : 1 ≤ 1 + ‖P‖ := le_add_of_nonneg_right (norm_nonneg _)
  -- the linear part
  have hlin : ‖iteratedFDerivWithin ℝ i L₀ S P‖ ≤ C0 * (1+‖P‖)^(k0+k1) := by
    rw [iteratedFDerivWithin_of_isOpen i hS hP]
    exact (H0 i hi P).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hP1 (by omega)) hC0)
  -- the product
  have hprod : ‖iteratedFDerivWithin ℝ i (fun P => f P * g P) S P‖ ≤ 2^k * C1 * Mi * (1+‖P‖)^(k0+k1) := by
    refine (norm_iteratedFDerivWithin_mul_le hfS hgS hS.uniqueDiffOn hP (by exact_mod_cast le_top)).trans ?_
    have hterm (j : ℕ) (hj : j ∈ Finset.range (i+1)) :
        (i.choose j : ℝ) * ‖iteratedFDerivWithin ℝ j f S P‖ * ‖iteratedFDerivWithin ℝ (i-j) g S P‖ ≤
          (i.choose j : ℝ) * (C1 * (1+‖P‖)^(k0+k1) * Mi) := by
      have hj' : j ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      rw [iteratedFDerivWithin_of_isOpen j hS hP,iteratedFDerivWithin_of_isOpen (i-j) hS hP]
      have hg' : iteratedFDeriv ℝ (i-j) g P = (iteratedFDeriv ℝ (i-j) (fun U : L => U⁻¹) P.1).compContinuousLinearMap
          (fun _ => ContinuousLinearMap.fst ℝ L (L × L)) :=
        iteratedFDeriv_comp_clm_of_isOpen' (W := {U : L | U ≠ 0}) isOpen_ne
          (fun U hU => (contDiffAt_inv ℝ hU).contDiffWithinAt) (ContinuousLinearMap.fst ℝ L (L × L)) hP (i-j)
      have hgb : ‖iteratedFDeriv ℝ (i-j) g P‖ ≤ Mi := by
        rw [hg']
        refine ((iteratedFDeriv ℝ (i-j) (fun U : L => U⁻¹) P.1).norm_compContinuousLinearMap_le _).trans ?_
        simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
        have hfst : ‖ContinuousLinearMap.fst ℝ L (L × L)‖ ≤ 1 := ContinuousLinearMap.norm_fst_le ..
        calc _ ≤ ‖iteratedFDeriv ℝ (i-j) (fun U : L => U⁻¹) P.1‖ * 1 :=
              mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hfst) (norm_nonneg _)
          _ ≤ Mi := by rw [mul_one]; exact HMi (i-j) (by omega) P.1 h1 h2
      have hfb : ‖iteratedFDeriv ℝ j f P‖ ≤ C1 * (1+‖P‖)^(k0+k1) :=
        (H1 j (hj'.trans hi) P).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hP1 (by omega)) hC1)
      exact mul_le_mul hfb hgb (norm_nonneg _) (by positivity)
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.sum_mul,← Nat.cast_sum,Nat.sum_range_choose]
    push_cast
    have : (2:ℝ)^i ≤ 2^k := pow_le_pow_right₀ (by norm_num) hi
    nlinarith [mul_nonneg (mul_nonneg hC1 (pow_nonneg (by positivity : (0:ℝ) ≤ 1+‖P‖) (k0+k1))) hMi]
  have hsplit : iteratedFDerivWithin ℝ i (reciprocalCoords n s) S P =
      iteratedFDerivWithin ℝ i L₀ S P + E.compContinuousMultilinearMap
        (iteratedFDerivWithin ℝ i (fun P => f P * g P) S P) := by
    rw [hκ,iteratedFDerivWithin_add_apply (L₀.contDiff.contDiffWithinAt.of_le (by exact_mod_cast le_top))
      ((E.contDiff.comp_contDiffOn hhS P hP).of_le (by exact_mod_cast le_top)) hS.uniqueDiffOn hP,
      E.iteratedFDerivWithin_comp_left (hhS P hP) hS.uniqueDiffOn hP (by exact_mod_cast le_top)]
  rw [hsplit]
  have h1 := norm_add_le (iteratedFDerivWithin ℝ i L₀ S P)
    (E.compContinuousMultilinearMap (iteratedFDerivWithin ℝ i (fun P => f P * g P) S P))
  have h2 := E.norm_compContinuousMultilinearMap_le (iteratedFDerivWithin ℝ i (fun P => f P * g P) S P)
  have h3 : ‖E‖ * ‖iteratedFDerivWithin ℝ i (fun P => f P * g P) S P‖ ≤ 2^k * C1 * Mi * (1+‖P‖)^(k0+k1) := by
    have := mul_le_mul hE hprod (norm_nonneg _) zero_le_one
    linarith
  have h4 : (1+‖P‖)^(k0+k1) ≤ (1+B')^(k0+k1) * (1+‖P.2.2‖)^(k0+k1) := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hPnorm _
  have hcoef : 0 ≤ C0 + 2^k * C1 * Mi := by positivity
  have hsum : ‖iteratedFDerivWithin ℝ i L₀ S P + E.compContinuousMultilinearMap
      (iteratedFDerivWithin ℝ i (fun P => f P * g P) S P)‖ ≤ (C0 + 2^k * C1 * Mi) * (1+‖P‖)^(k0+k1) := by
    linarith
  refine hsum.trans ((mul_le_mul_of_nonneg_left h4 hcoef).trans (le_of_eq ?_))
  ring

/-- Lemma 4.2(iii), "the same holds for all derivatives", in the original line parameter: if R is
smooth for U ≠ 0 with every derivative rapidly decreasing in the last variable, then so is
(U, V, τ) ↦ R(U, V, s τⁿ / U), and every joint derivative decays rapidly in τ, uniformly for
U in a compact annulus and V bounded. -/
theorem reciprocal_comp_decay [ProperSpace L] (n : ℕ) (hn : 0 < n) (s : L) (hs : ‖s‖ = 1)
    {R : L × L × L → ℂ} (hR : ContDiffOn ℝ ∞ R {P | P.1 ≠ 0})
    (hdec : ∀ k M : ℕ, ∀ δ B : ℝ, 0 < δ → ∃ C : ℝ, ∀ P : L × L × L, δ ≤ ‖P.1‖ → ‖P.2.1‖ ≤ B →
      ‖iteratedFDeriv ℝ k R P‖ * (1+‖P.2.2‖)^M ≤ C) :
    ∀ k N : ℕ, ∀ δ B : ℝ, 0 < δ → ∃ C : ℝ, ∀ P : L × L × L, δ ≤ ‖P.1‖ → ‖P.1‖ ≤ B → ‖P.2.1‖ ≤ B →
      ‖iteratedFDeriv ℝ k (R ∘ reciprocalCoords n s) P‖ * (1+‖P.2.2‖)^N ≤ C := by
  intro k N δ B hδ
  let S : Set (L × L × L) := {P | P.1 ≠ 0}
  have hS : IsOpen S := isOpen_ne_fun continuous_fst continuous_const
  obtain ⟨c,q,hc,Hκ⟩ := reciprocalCoords_deriv_bound (L := L) n k s hδ (B := B)
  let M := N + q * k
  have hC := fun i => hdec i M δ B hδ
  choose Ci hCi using hC
  let Cm := ∑ i ∈ Finset.range (k+1), max (Ci i) 0
  have hCm0 : 0 ≤ Cm := by positivity
  let c' := max c 1
  let B' := max B 1
  refine ⟨k ! * Cm * c'^k * (2*B')^M,fun P h1 h2 h3 => ?_⟩
  have hP : P ∈ S := norm_pos_iff.mp (hδ.trans_le h1)
  have hB : 0 < B := hδ.trans_le (h1.trans h2)
  set τ := P.2.2
  set σ := (reciprocalCoords n s P).2.2
  have hσ : ‖τ‖^n ≤ B' * ‖σ‖ := by
    have e : ‖σ‖ = ‖τ‖^n / ‖P.1‖ := by
      simp only [σ,τ,reciprocalCoords,norm_mul,hs,norm_pow,norm_inv,div_eq_mul_inv,one_mul]
    rw [e,mul_div_assoc',le_div_iff₀ (hδ.trans_le h1),mul_comm B']
    exact mul_le_mul_of_nonneg_left (h2.trans (le_max_left _ _)) (pow_nonneg (norm_nonneg _) _)
  -- Faà di Bruno
  let D := c' * (1+‖τ‖)^q
  have hD1 : 1 ≤ D := one_le_mul_of_one_le_of_one_le (le_max_right _ _) (one_le_pow₀ (by simp))
  have hFdB := norm_iteratedFDerivWithin_comp_le (n := k) hR (contDiffOn_reciprocalCoords n s)
    (by exact_mod_cast le_top) hS.uniqueDiffOn hS.uniqueDiffOn
    (fun P hP => show (reciprocalCoords n s P).1 ≠ 0 from hP) hP
    (C := Cm * ((1+‖σ‖)^M)⁻¹) (D := D)
    (fun i hi => by
      rw [iteratedFDerivWithin_of_isOpen i hS (show (reciprocalCoords n s P).1 ≠ 0 from hP)]
      have h := hCi i (reciprocalCoords n s P) h1 h3
      rw [le_mul_inv_iff₀ (by positivity)]
      have hm : Ci i ≤ Cm := (le_max_left _ _).trans (Finset.single_le_sum (f := fun i => max (Ci i) 0)
        (fun _ _ => le_max_right _ _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi)))
      exact h.trans hm)
    (fun i hi1 hi => (Hκ i hi P h1 h2 h3).trans ((mul_le_mul_of_nonneg_right (le_max_left _ _)
      (by positivity)).trans (le_self_pow₀ hD1 (by omega))))
  rw [iteratedFDerivWithin_of_isOpen k hS hP] at hFdB
  have hτσ : 1 + ‖τ‖ ≤ 2 * B' * (1 + ‖σ‖) := by
    have hB'1 : 1 ≤ B' := le_max_right _ _
    have ht1 : 1 + ‖τ‖ ≤ 2 * (1 + ‖τ‖^n) := by
      rcases le_total ‖τ‖ 1 with h|h
      · nlinarith [pow_nonneg (norm_nonneg τ) n]
      · nlinarith [le_self_pow₀ h hn.ne']
    nlinarith [norm_nonneg σ]
  have hpow : (1 + ‖τ‖)^M ≤ (2 * B')^M * (1 + ‖σ‖)^M := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hτσ M
  calc ‖iteratedFDeriv ℝ k (R ∘ reciprocalCoords n s) P‖ * (1+‖τ‖)^N
      ≤ (k ! * (Cm * ((1+‖σ‖)^M)⁻¹) * D^k) * (1+‖τ‖)^N :=
        mul_le_mul_of_nonneg_right hFdB (by positivity)
    _ = k ! * Cm * c'^k * ((1+‖σ‖)^M)⁻¹ * (1+‖τ‖)^M := by
        simp only [D,M,mul_pow,← pow_mul,pow_add]; ring
    _ ≤ k ! * Cm * c'^k * ((1+‖σ‖)^M)⁻¹ * ((2 * B')^M * (1 + ‖σ‖)^M) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = k ! * Cm * c'^k * (2*B')^M := by
        field_simp

end MetaplecticPoisson
