import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import LiquityV2.Defs
import LiquityV2.CooldownFees
import LiquityV2.DesignAStar

namespace LiquityV2

open Finset BigOperators

theorem statusQuo_fee_base_expansion {D Φ m_j : ℝ}
    (hΦ : 0 < Φ) (hm : 0 < m_j) :
    D * m_j < (D + Φ) * m_j ∧ (D + Φ) * m_j - D * m_j = Φ * m_j := by
  have hpos : 0 < Φ * m_j := mul_pos hΦ hm
  constructor <;> linarith

noncomputable def borrowerPrematureHikeGain (p : ProtocolParams)
    (cB Δlam Δr K τ : ℝ) : ℝ :=
  (cB * Δlam - Δr) * (τ / p.Y) - K

noncomputable def managerPrematureHikeGain (p : ProtocolParams)
    (cm αInt αEff Δlam Δr K gPerD τ : ℝ) : ℝ :=
  (cm * Δlam - αInt * Δr) * (τ / p.Y) - (αEff * K + gPerD)

theorem cut_bunching_threshold (p : ProtocolParams)
    {D Δdn rbar τ : ℝ} (hD : 0 < D) (hτ : 0 < τ) :
    D * Δdn * (τ / p.Y) ≤ D * rbar * (p.P / p.Y) ↔ Δdn ≤ rbar * (p.P / τ) := by
  have hY : 0 < p.Y := p.hY
  have hDτY : 0 < D * τ / p.Y := div_pos (mul_pos hD hτ) hY
  have h1 : D * Δdn * (τ / p.Y) = Δdn * (D * τ / p.Y) := by ring
  have h2 : D * rbar * (p.P / p.Y) = (rbar * (p.P / τ)) * (D * τ / p.Y) := by
    have hτne : τ ≠ 0 := ne_of_gt hτ
    have hYne : p.Y ≠ 0 := ne_of_gt hY
    field_simp [hτne, hYne]
  rw [h1, h2]
  exact mul_le_mul_iff_left₀ hDτY

theorem ordinary_cut_waits_for_cooldown (p : ProtocolParams)
    {D Δdn rbar τ : ℝ} (hD : 0 < D) (hrbar : 0 < rbar) (hτ0 : 0 < τ) (hτP : τ < p.P)
    (hord : Δdn ≤ rbar) :
    D * Δdn * (τ / p.Y) < D * rbar * (p.P / p.Y) := by
  have h1 : D * Δdn * (τ / p.Y) ≤ D * rbar * (τ / p.Y) := by
    have hnn : 0 ≤ D * (τ / p.Y) := mul_nonneg (le_of_lt hD) (div_nonneg (le_of_lt hτ0) (le_of_lt p.hY))
    have hrew1 : D * Δdn * (τ / p.Y) = Δdn * (D * (τ / p.Y)) := by ring
    have hrew2 : D * rbar * (τ / p.Y) = rbar * (D * (τ / p.Y)) := by ring
    rw [hrew1, hrew2]
    exact mul_le_mul_of_nonneg_right hord hnn
  have h2 : D * rbar * (τ / p.Y) < D * rbar * (p.P / p.Y) := by
    have hpos : 0 < D * rbar := mul_pos hD hrbar
    exact mul_lt_mul_of_pos_left (div_lt_div_of_pos_right hτP p.hY) hpos
  linarith

theorem dominated_near_notch_hike_exists (p : ProtocolParams)
    {cB cm αInt αm Δlam Δr K gPerD : ℝ}
    (hK : 0 < K) (hcm : cB ≤ cm) (hΔlam : 0 ≤ Δlam)
    (hαInt : αInt ≤ 1) (hΔr : 0 ≤ Δr)
    (hwedge : αm * K + gPerD < K)
    (hBm_pos : 0 < cm * Δlam - αInt * Δr)
    (hnear : max 0 (αm * K + gPerD) < (cm * Δlam - αInt * Δr) * (p.P / p.Y)) :
    ∃ τ : ℝ, 0 < τ ∧ τ < p.P ∧
      0 < managerPrematureHikeGain p cm αInt αm Δlam Δr K gPerD τ ∧
      borrowerPrematureHikeGain p cB Δlam Δr K τ < 0 := by
  set Bm := cm * Δlam - αInt * Δr
  set Bb := cB * Δlam - Δr
  have hBb_le_Bm : Bb ≤ Bm := by
    dsimp only [Bb, Bm]
    have h1 : cB * Δlam ≤ cm * Δlam := mul_le_mul_of_nonneg_right hcm hΔlam
    have h2 : αInt * Δr ≤ 1 * Δr := mul_le_mul_of_nonneg_right hαInt hΔr
    linarith
  have hBmY_pos : 0 < Bm / p.Y := div_pos hBm_pos p.hY
  let lo : ℝ := max 0 (αm * K + gPerD) / (Bm / p.Y)
  let hi : ℝ := min p.P (K / (Bm / p.Y))
  have hlo_nn : 0 ≤ lo := div_nonneg (le_max_left _ _) (le_of_lt hBmY_pos)
  have hlo_lt_P : lo < p.P := by
    dsimp only [lo]
    rw [div_lt_iff₀ hBmY_pos]
    have hrew : p.P * (Bm / p.Y) = Bm * (p.P / p.Y) := by ring
    linarith [hnear]
  have hlo_lt_KBm : lo < K / (Bm / p.Y) := by
    dsimp only [lo]
    apply div_lt_div_of_pos_right _ hBmY_pos
    exact max_lt hK hwedge
  have hlo_lt_hi : lo < hi := lt_min hlo_lt_P hlo_lt_KBm
  let τ : ℝ := (lo + hi) / 2
  have hτ_gt_lo : lo < τ := by dsimp only [τ]; linarith
  have hτ_lt_hi : τ < hi := by dsimp only [τ]; linarith
  have hτ_pos : 0 < τ := lt_of_le_of_lt hlo_nn hτ_gt_lo
  have hτ_lt_P : τ < p.P := lt_of_lt_of_le hτ_lt_hi (min_le_left _ _)
  have hτ_lt_KBm : τ < K / (Bm / p.Y) := lt_of_lt_of_le hτ_lt_hi (min_le_right _ _)
  refine ⟨τ, hτ_pos, hτ_lt_P, ?_, ?_⟩
  · unfold managerPrematureHikeGain
    have hmul : max 0 (αm * K + gPerD) < (Bm / p.Y) * τ := by
      have h1 := mul_lt_mul_of_pos_left hτ_gt_lo hBmY_pos
      have h2 : (Bm / p.Y) * lo = max 0 (αm * K + gPerD) := by
        dsimp only [lo]
        exact mul_div_cancel₀ _ (ne_of_gt hBmY_pos)
      linarith
    have hrew : Bm * (τ / p.Y) = (Bm / p.Y) * τ := by ring
    have hle : αm * K + gPerD ≤ max 0 (αm * K + gPerD) := le_max_right _ _
    linarith
  · unfold borrowerPrematureHikeGain
    have h1 : (Bm / p.Y) * τ < K := by
      have hmul := mul_lt_mul_of_pos_left hτ_lt_KBm hBmY_pos
      have h2 : (Bm / p.Y) * (K / (Bm / p.Y)) = K := mul_div_cancel₀ _ (ne_of_gt hBmY_pos)
      linarith
    have hrew_b : Bb * (τ / p.Y) ≤ Bm * (τ / p.Y) :=
      mul_le_mul_of_nonneg_right hBb_le_Bm (div_nonneg (le_of_lt hτ_pos) (le_of_lt p.hY))
    have hrew_m : Bm * (τ / p.Y) = (Bm / p.Y) * τ := by ring
    linarith

theorem designAStar_dominates_statusQuo_staircase (p : ProtocolParams) {K : ℕ}
    {D rbar dt0 : ℝ} (hD : 0 < D) (hdt0 : dt0 < p.P)
    (r : Fin (K + 1) → ℝ) (dt : Fin K → ℝ)
    (hr : ∀ k : Fin K, r k.castSucc < r k.succ)
    (hdt : ∀ k : Fin K, dt k < p.P)
    (hsmall : r (Fin.last K) - r 0 < (K : ℝ) * rbar) :
    let phiSQ := ∑ k : Fin K, statusQuoFee p D (r k.castSucc) (r k.succ) rbar (dt k)
    let phiAStar := ∑ k : Fin K, designAStarFee p D (r k.castSucc) (r k.succ) (dt k)
    phiSQ - phiAStar = D * ((K : ℝ) * rbar - (r (Fin.last K) - r 0)) * (p.P / p.Y) ∧
    phiAStar < phiSQ := by
  dsimp only
  have hSQ := statusQuo_staircase_inflation p D rbar r dt hr hdt
  have hAS := designAStar_staircase_additive_K p D dt0 r dt (fun k => le_of_lt (hr k)) hdt hdt0
  have hmono : r 0 ≤ r (Fin.last K) := Fin.monotone_iff_le_succ.mpr (fun k => le_of_lt (hr k)) (Fin.zero_le _)
  have hAS_val : designAStarFee p D (r 0) (r (Fin.last K)) dt0 =
      D * (r (Fin.last K) - r 0) * (p.P / p.Y) := by
    by_cases heq : r (Fin.last K) = r 0
    · unfold designAStarFee
      simp [heq]
    · have hlt : r 0 < r (Fin.last K) := lt_of_le_of_ne hmono (Ne.symm heq)
      unfold designAStarFee
      have hnot : ¬ (dt0 ≥ p.P ∨ r (Fin.last K) = r 0) := by push Not; exact ⟨hdt0, heq⟩
      simp [hnot, hlt]
  rw [hSQ, hAS, hAS_val]
  have hid :
      (K : ℝ) * (D * rbar * (p.P / p.Y)) - D * (r (Fin.last K) - r 0) * (p.P / p.Y) =
        D * ((K : ℝ) * rbar - (r (Fin.last K) - r 0)) * (p.P / p.Y) := by
    ring
  have hpos : 0 < D * ((K : ℝ) * rbar - (r (Fin.last K) - r 0)) * (p.P / p.Y) :=
    mul_pos (mul_pos hD (sub_pos.mpr hsmall)) (div_pos p.hP p.hY)
  exact ⟨hid, by linarith⟩

theorem designAStar_near_notch_attenuation (p : ProtocolParams)
    {D r0 r1 rbar dt : ℝ} (hdtP : dt < p.P) (hr : r0 < r1) (hrbar : 0 < rbar) :
    designAStarFee p D r0 r1 dt =
      ((r1 - r0) / rbar) * statusQuoFee p D r0 r1 rbar dt := by
  have hnot : ¬ (dt ≥ p.P ∨ r1 = r0) := by push Not; exact ⟨hdtP, ne_of_gt hr⟩
  unfold designAStarFee statusQuoFee
  simp only [hnot, ↓reduceIte, hr]
  have hrbar_ne : rbar ≠ 0 := ne_of_gt hrbar
  field_simp [hrbar_ne]

def alphaEff (α0 β : ℝ) : ℝ := β + (1 - β) * α0

noncomputable def betaStarPure (α0 K gPerD : ℝ) : ℝ :=
  max 0 (1 - gPerD / ((1 - α0) * K))

theorem copay_strictly_improves_internalization {α0 β μ_pv : ℝ}
    (hα0 : α0 ≤ 1) (hβ : 0 ≤ β) (hμ : 0 < μ_pv) :
    α0 - μ_pv < alphaEff α0 β := by
  unfold alphaEff
  have hnn : 0 ≤ β * (1 - α0) := mul_nonneg hβ (sub_nonneg.mpr hα0)
  linarith

theorem copay_eliminates_dominated_hikes (p : ProtocolParams)
    {cB α0 β Δlam Δr K gPerD τ : ℝ}
    (hα0 : α0 < 1) (hK : 0 < K)
    (hβ : betaStarPure α0 K gPerD ≤ β)
    (hdom : borrowerPrematureHikeGain p cB Δlam Δr K τ ≤ 0) :
    managerPrematureHikeGain p cB 1 (alphaEff α0 β) Δlam Δr K gPerD τ ≤ 0 := by
  have h1α : 0 < 1 - α0 := sub_pos.mpr hα0
  have hden : 0 < (1 - α0) * K := mul_pos h1α hK
  have hβ_ge : 1 - gPerD / ((1 - α0) * K) ≤ β := le_trans (le_max_right _ _) hβ
  have hmul : (1 - gPerD / ((1 - α0) * K)) * ((1 - α0) * K) ≤ β * ((1 - α0) * K) :=
    mul_le_mul_of_nonneg_right hβ_ge (le_of_lt hden)
  have hlhs : (1 - gPerD / ((1 - α0) * K)) * ((1 - α0) * K) = (1 - α0) * K - gPerD := by
    have hne : (1 - α0) * K ≠ 0 := ne_of_gt hden
    field_simp [hne]
  have hcost_ge : K ≤ alphaEff α0 β * K + gPerD := by
    unfold alphaEff
    linarith
  unfold borrowerPrematureHikeGain at hdom
  unfold managerPrematureHikeGain
  linarith

theorem copay_limited_liability_budget {m_j phiSQ phiStar : ℝ}
    (hm : 0 ≤ m_j) (hstar : 0 < phiStar) (hle : phiStar ≤ phiSQ) :
    m_j / phiSQ ≤ m_j / phiStar := by
  exact div_le_div_of_nonneg_left hm hstar hle

def discreteLIFOCurrPayoff1 (Δ1 ε : ℝ) (k1 k2 : ℕ) (tieBackIs1 : Bool) : ℝ :=
  (if k2 < k1 ∨ (k1 = k2 ∧ tieBackIs1 = true) then Δ1 else 0) - (k1 : ℝ) * ε

def discreteLIFOCurrPayoff2 (Δ2 ε : ℝ) (k1 k2 : ℕ) (tieBackIs1 : Bool) : ℝ :=
  (if k1 < k2 ∨ (k1 = k2 ∧ tieBackIs1 = false) then Δ2 else 0) - (k2 : ℝ) * ε

def discreteLIFODevPayoff (Δ ε : ℝ) (kNew kRival : ℕ) : ℝ :=
  (if kRival < kNew then Δ else 0) - (kNew : ℝ) * ε

def IsDiscreteLIFOPureNash (Δ1 Δ2 ε : ℝ) (k1 k2 : ℕ) (tieBackIs1 : Bool) : Prop :=
  (∀ k1' : ℕ, k1' ≠ k1 →
    discreteLIFODevPayoff Δ1 ε k1' k2 ≤ discreteLIFOCurrPayoff1 Δ1 ε k1 k2 tieBackIs1) ∧
  (∀ k2' : ℕ, k2' ≠ k2 →
    discreteLIFODevPayoff Δ2 ε k2' k1 ≤ discreteLIFOCurrPayoff2 Δ2 ε k1 k2 tieBackIs1)

theorem leapfrogging_discrete_grid_tightness_witness
    {Δ1 Δ2 ε : ℝ} (hε : 0 < ε) (h1_le : Δ1 ≤ 2 * ε) (h2_gt : ε < Δ2) :
    IsDiscreteLIFOPureNash Δ1 Δ2 ε 0 1 false := by
  constructor
  · intro k1' hne
    unfold discreteLIFODevPayoff discreteLIFOCurrPayoff1
    simp only [show ¬ (1 < (0 : ℕ) ∨ ((0 : ℕ) = 1 ∧ false = true)) by decide,
      ↓reduceIte, Nat.cast_zero, zero_mul, sub_zero]
    by_cases hgt : 1 < k1'
    · have hk2 : (2 : ℝ) ≤ (k1' : ℝ) := by exact_mod_cast hgt
      simp only [hgt, ↓reduceIte]
      nlinarith
    · have hk0 : (0 : ℝ) ≤ (k1' : ℝ) := Nat.cast_nonneg _
      simp only [hgt, ↓reduceIte]
      nlinarith
  · intro k2' hne
    unfold discreteLIFODevPayoff discreteLIFOCurrPayoff2
    have hpos01 : (0 : ℕ) < 1 := Nat.zero_lt_one
    simp only [hpos01, true_or, ↓reduceIte, Nat.cast_one, one_mul]
    by_cases h0 : k2' = 0
    · subst h0
      simp only [lt_irrefl, ↓reduceIte, Nat.cast_zero, zero_mul, sub_zero]
      linarith
    · have hgt : 0 < k2' := Nat.pos_of_ne_zero h0
      have hk2 : (2 : ℝ) ≤ (k2' : ℝ) := by
        have : 2 ≤ k2' := by omega
        exact_mod_cast this
      simp only [hgt, ↓reduceIte]
      nlinarith

theorem leapfrogging_discrete_grid_tightness_witness_symm
    {Δ1 Δ2 ε : ℝ} (hε : 0 < ε) (h1_gt : ε < Δ1) (h2_le : Δ2 ≤ 2 * ε) :
    IsDiscreteLIFOPureNash Δ1 Δ2 ε 1 0 true := by
  constructor
  · intro k1' hne
    unfold discreteLIFODevPayoff discreteLIFOCurrPayoff1
    have hpos01 : (0 : ℕ) < 1 := Nat.zero_lt_one
    simp only [hpos01, true_or, ↓reduceIte, Nat.cast_one, one_mul]
    by_cases h0 : k1' = 0
    · subst h0
      simp only [lt_irrefl, ↓reduceIte, Nat.cast_zero, zero_mul, sub_zero]
      linarith
    · have hgt : 0 < k1' := Nat.pos_of_ne_zero h0
      have hk2 : (2 : ℝ) ≤ (k1' : ℝ) := by
        have : 2 ≤ k1' := by omega
        exact_mod_cast this
      simp only [hgt, ↓reduceIte]
      nlinarith
  · intro k2' hne
    unfold discreteLIFODevPayoff discreteLIFOCurrPayoff2
    simp only [show ¬ (1 < (0 : ℕ) ∨ ((1 : ℕ) = 0 ∧ true = false)) by decide,
      ↓reduceIte, Nat.cast_zero, zero_mul, sub_zero]
    by_cases hgt : 1 < k2'
    · have hk2 : (2 : ℝ) ≤ (k2' : ℝ) := by exact_mod_cast hgt
      simp only [hgt, ↓reduceIte]
      nlinarith
    · have hk0 : (0 : ℝ) ≤ (k2' : ℝ) := Nat.cast_nonneg _
      simp only [hgt, ↓reduceIte]
      nlinarith

theorem leapfrogging_discrete_grid_no_pure_nash_iff
    {Δ1 Δ2 ε : ℝ} (hε : 0 < ε) (h1 : ε < Δ1) (h2 : ε < Δ2) :
    (¬ ∃ k1 k2 : ℕ, ∃ b : Bool, IsDiscreteLIFOPureNash Δ1 Δ2 ε k1 k2 b) ↔
      (2 * ε < Δ1 ∧ 2 * ε < Δ2) := by
  constructor
  · intro hno
    constructor
    · by_contra hle
      push Not at hle
      exact hno ⟨0, 1, false, leapfrogging_discrete_grid_tightness_witness hε hle h2⟩
    · by_contra hle
      push Not at hle
      exact hno ⟨1, 0, true, leapfrogging_discrete_grid_tightness_witness_symm hε h1 hle⟩
  · intro ⟨h1_2, h2_2⟩ ⟨k1, k2, b, hne1, hne2⟩
    rcases lt_trichotomy k1 k2 with hlt | heq | hgt
    · by_cases hgap : k1 + 1 < k2
      ·
        have hdev2 := hne2 (k1 + 1) (by omega)
        unfold discreteLIFODevPayoff discreteLIFOCurrPayoff2 at hdev2
        have h1lt2 : k1 < k2 ∨ (k1 = k2 ∧ b = false) := Or.inl hlt
        simp only [Nat.lt_succ_self, h1lt2, ↓reduceIte, Nat.cast_add, Nat.cast_one] at hdev2
        have hstep : (k1 : ℝ) + 2 ≤ (k2 : ℝ) := by exact_mod_cast hgap
        nlinarith
      ·
        have hk2 : k2 = k1 + 1 := by omega
        subst hk2
        have hdev1 := hne1 (k1 + 2) (by omega)
        unfold discreteLIFODevPayoff discreteLIFOCurrPayoff1 at hdev1
        have hnot1 : ¬ (k1 + 1 < k1 ∨ (k1 = k1 + 1 ∧ b = true)) := by omega
        have hgt1 : k1 + 1 < k1 + 2 := by omega
        simp only [hnot1, hgt1, ↓reduceIte, Nat.cast_add, Nat.cast_ofNat] at hdev1
        nlinarith
    ·
      subst heq
      cases b
      · have hdev1 := hne1 (k1 + 1) (by omega)
        unfold discreteLIFODevPayoff discreteLIFOCurrPayoff1 at hdev1
        simp only [Nat.lt_succ_self, lt_irrefl, Bool.false_eq_true, and_false, or_self, ↓reduceIte,
          Nat.cast_add, Nat.cast_one] at hdev1
        nlinarith
      · have hdev2 := hne2 (k1 + 1) (by omega)
        unfold discreteLIFODevPayoff discreteLIFOCurrPayoff2 at hdev2
        simp only [Nat.lt_succ_self, lt_irrefl, Bool.true_eq_false, and_false, or_self, ↓reduceIte,
          Nat.cast_add, Nat.cast_one] at hdev2
        nlinarith
    · by_cases hgap : k2 + 1 < k1
      ·
        have hdev1 := hne1 (k2 + 1) (by omega)
        unfold discreteLIFODevPayoff discreteLIFOCurrPayoff1 at hdev1
        have h2lt1 : k2 < k1 ∨ (k1 = k2 ∧ b = true) := Or.inl hgt
        simp only [Nat.lt_succ_self, h2lt1, ↓reduceIte, Nat.cast_add, Nat.cast_one] at hdev1
        have hstep : (k2 : ℝ) + 2 ≤ (k1 : ℝ) := by exact_mod_cast hgap
        nlinarith
      ·
        have hk1 : k1 = k2 + 1 := by omega
        subst hk1
        have hdev2 := hne2 (k2 + 2) (by omega)
        unfold discreteLIFODevPayoff discreteLIFOCurrPayoff2 at hdev2
        have hnot2 : ¬ (k2 + 1 < k2 ∨ (k2 + 1 = k2 ∧ b = false)) := by omega
        have hgt2 : k2 + 1 < k2 + 2 := by omega
        simp only [hnot2, hgt2, ↓reduceIte, Nat.cast_add, Nat.cast_ofNat] at hdev2
        nlinarith

theorem designAStar_collapses_leapfrog_fee_exact (p : ProtocolParams)
    {n : ℕ} (hn : 1 ≤ n) {D0 rbar r0 ε : ℝ}
    (hD0 : 0 < D0) (hrbar : 0 < rbar) (hε : 0 < ε) :
    let r1End := r0 + ((2 * n - 1 : ℕ) : ℝ) * ε
    let r2End := r0 + ((2 * n : ℕ) : ℝ) * ε
    let phiSQ := ((2 * n : ℕ) : ℝ) * D0 * rbar * (p.P / p.Y)
    let phiAStar := D0 * (r1End - r0) * (p.P / p.Y) + D0 * (r2End - r0) * (p.P / p.Y)
    phiSQ / phiAStar = (2 * (n : ℝ) * rbar) / ((4 * (n : ℝ) - 1) * ε) ∧
    rbar / (2 * ε) < phiSQ / phiAStar := by
  dsimp only
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hcast1 : ((2 * n - 1 : ℕ) : ℝ) = 2 * (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have hcast2 : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  have h4n1_pos : 0 < 4 * (n : ℝ) - 1 := by linarith
  have hPY_pos : 0 < p.P / p.Y := div_pos p.hP p.hY
  have hratio :
      (((2 * n : ℕ) : ℝ) * D0 * rbar * (p.P / p.Y)) /
        (D0 * (r0 + ((2 * n - 1 : ℕ) : ℝ) * ε - r0) * (p.P / p.Y) +
         D0 * (r0 + ((2 * n : ℕ) : ℝ) * ε - r0) * (p.P / p.Y)) =
      (2 * (n : ℝ) * rbar) / ((4 * (n : ℝ) - 1) * ε) := by
    rw [hcast1, hcast2]
    have hden : D0 * (r0 + (2 * (n : ℝ) - 1) * ε - r0) * (p.P / p.Y) +
        D0 * (r0 + 2 * (n : ℝ) * ε - r0) * (p.P / p.Y) =
        D0 * ((4 * (n : ℝ) - 1) * ε) * (p.P / p.Y) := by ring
    rw [hden]
    have hDne : D0 ≠ 0 := ne_of_gt hD0
    have hPne : p.P ≠ 0 := ne_of_gt p.hP
    have hYne : p.Y ≠ 0 := ne_of_gt p.hY
    have hεne : ε ≠ 0 := ne_of_gt hε
    have h4ne : 4 * (n : ℝ) - 1 ≠ 0 := ne_of_gt h4n1_pos
    field_simp [hDne, hPne, hYne, hεne, h4ne]
  refine ⟨hratio, ?_⟩
  rw [hratio]
  have hden1 : 0 < 2 * ε := by linarith
  have hden2 : 0 < (4 * (n : ℝ) - 1) * ε := mul_pos h4n1_pos hε
  rw [div_lt_div_iff₀ hden1 hden2]
  have hmul : 0 < rbar * ε := mul_pos hrbar hε
  nlinarith

theorem designAStar_collapses_leapfrog_fee (p : ProtocolParams)
    {n1 n2 : ℕ} {D0 rbar r0 r1End r2End rCeil : ℝ}
    (hD0 : 0 < D0) (hrbar : 0 ≤ rbar)
    (hr1_le : r1End ≤ rCeil) (hr2_le : r2End ≤ rCeil)
    (hspread : 0 < rCeil - r0) :
    let phiSQ := ((n1 : ℝ) + (n2 : ℝ)) * D0 * rbar * (p.P / p.Y)
    let phiAStar := D0 * (r1End - r0) * (p.P / p.Y) + D0 * (r2End - r0) * (p.P / p.Y)
    phiAStar ≤ 2 * D0 * (rCeil - r0) * (p.P / p.Y) ∧
    (0 < phiAStar →
      (((n1 : ℝ) + (n2 : ℝ)) / 2) * (rbar / (rCeil - r0)) ≤ phiSQ / phiAStar) := by
  dsimp only
  have hPY : 0 < p.P / p.Y := div_pos p.hP p.hY
  have hcap : D0 * (r1End - r0) * (p.P / p.Y) + D0 * (r2End - r0) * (p.P / p.Y) ≤
      2 * D0 * (rCeil - r0) * (p.P / p.Y) := by
    have hsum : (r1End - r0) + (r2End - r0) ≤ 2 * (rCeil - r0) := by linarith
    have hpos : 0 < D0 * (p.P / p.Y) := mul_pos hD0 hPY
    have hlhs : D0 * (r1End - r0) * (p.P / p.Y) + D0 * (r2End - r0) * (p.P / p.Y) =
        ((r1End - r0) + (r2End - r0)) * (D0 * (p.P / p.Y)) := by ring
    have hrhs : 2 * D0 * (rCeil - r0) * (p.P / p.Y) =
        (2 * (rCeil - r0)) * (D0 * (p.P / p.Y)) := by ring
    rw [hlhs, hrhs]
    exact mul_le_mul_of_nonneg_right hsum (le_of_lt hpos)
  refine ⟨hcap, ?_⟩
  intro hposA
  have h1 : (((n1 : ℝ) + (n2 : ℝ)) / 2) * (rbar / (rCeil - r0)) =
      (((n1 : ℝ) + (n2 : ℝ)) * D0 * rbar * (p.P / p.Y)) /
        (2 * D0 * (rCeil - r0) * (p.P / p.Y)) := by
    have hDne : D0 ≠ 0 := ne_of_gt hD0
    have hsne : rCeil - r0 ≠ 0 := ne_of_gt hspread
    have hPne : p.P ≠ 0 := ne_of_gt p.hP
    have hYne : p.Y ≠ 0 := ne_of_gt p.hY
    field_simp [hDne, hsne, hPne, hYne]
  rw [h1]
  have hnum_nn : 0 ≤ ((n1 : ℝ) + (n2 : ℝ)) * D0 * rbar * (p.P / p.Y) := by positivity
  exact div_le_div_of_nonneg_left hnum_nn hposA hcap

end LiquityV2
