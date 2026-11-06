import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import LiquityV2.Defs

namespace LiquityV2

open Finset BigOperators

def SatisfiesCooldownConvention (p : ProtocolParams) (Φ : ℝ → ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ D r0 r1 dt, 0 ≤ D → (dt ≥ p.P ∨ r1 = r0) → Φ D r0 r1 dt = 0

def SatisfiesA1 (p : ProtocolParams) (Φ : ℝ → ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ D r0 r1 dt, 0 ≤ D → 0 ≤ dt → dt < p.P → r0 < r1 →
    D * (r1 - r0) * (dt / p.Y) ≤ Φ D r0 r1 dt

def SatisfiesA1Strong (p : ProtocolParams) (Φ : ℝ → ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ D r0 r1 dt, 0 ≤ D → 0 ≤ dt → dt < p.P → r0 < r1 →
    D * (r1 - r0) * (p.P / p.Y) ≤ Φ D r0 r1 dt

def SatisfiesA2Strict (p : ProtocolParams) (Φ : ℝ → ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ D r0 r1 r2 dt1 dt2,
    0 ≤ D → 0 ≤ dt1 → 0 ≤ dt2 → dt1 + dt2 < p.P →
    r0 < r1 → r1 < r2 →
    Φ D r0 r1 dt1 + Φ D r1 r2 dt2 = Φ D r0 r2 (dt1 + dt2)

def SatisfiesA2 (p : ProtocolParams) (Φ : ℝ → ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ D r0 r1 r2 dt1 dt2,
    0 ≤ D → 0 ≤ dt1 → 0 ≤ dt2 → dt1 + dt2 < p.P →
    r0 ≤ r1 → r1 ≤ r2 →
    Φ D r0 r1 dt1 + Φ D r1 r2 dt2 = Φ D r0 r2 (dt1 + dt2)

def SatisfiesA3 (p : ProtocolParams) (Φ : ℝ → ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ D r0 r1 dt, 0 ≤ D → 0 ≤ dt → dt < p.P → r1 < r0 →
    holdCost p D r0 p.P ≤ spikeCutTotalCost p D r0 r1 dt (Φ D r0 r1 dt)

theorem satisfiesA3_iff_fee_floor (p : ProtocolParams) (Φ : ℝ → ℝ → ℝ → ℝ → ℝ) :
    SatisfiesA3 p Φ ↔
      ∀ D r0 r1 dt, 0 ≤ D → 0 ≤ dt → dt < p.P → r1 < r0 →
        D * (r0 - r1) * ((p.P - dt) / p.Y) ≤ Φ D r0 r1 dt := by
  constructor
  · intro h D r0 r1 dt hD hdt0 hdtP hlt
    have hcost := h D r0 r1 dt hD hdt0 hdtP hlt
    have hdiff := spikeCutTotalCost_sub_holdCost p D r0 r1 dt (Φ D r0 r1 dt)
    linarith
  · intro h D r0 r1 dt hD hdt0 hdtP hlt
    have hfee := h D r0 r1 dt hD hdt0 hdtP hlt
    have hdiff := spikeCutTotalCost_sub_holdCost p D r0 r1 dt (Φ D r0 r1 dt)
    linarith

def SatisfiesA4 (Φ : ℝ → ℝ → ℝ → ℝ → ℝ) : Prop :=
  (∀ lam D r0 r1 dt, 0 ≤ lam → 0 ≤ D → Φ (lam * D) r0 r1 dt = lam * Φ D r0 r1 dt) ∧
  (∀ D1 D2 r0 r1 dt, 0 ≤ D1 → 0 ≤ D2 → Φ (D1 + D2) r0 r1 dt = Φ D1 r0 r1 dt + Φ D2 r0 r1 dt)

theorem statusQuo_staircase_inflation (p : ProtocolParams) {K : ℕ}
    (D rbar : ℝ) (r : Fin (K + 1) → ℝ) (dt : Fin K → ℝ)
    (hr : ∀ k : Fin K, r k.castSucc < r k.succ)
    (hdt : ∀ k : Fin K, dt k < p.P) :
    (∑ k : Fin K, statusQuoFee p D (r k.castSucc) (r k.succ) rbar (dt k)) =
      (K : ℝ) * (D * rbar * (p.P / p.Y)) := by
  have hterm : ∀ k : Fin K,
      statusQuoFee p D (r k.castSucc) (r k.succ) rbar (dt k) = D * rbar * (p.P / p.Y) := by
    intro k
    unfold statusQuoFee
    have hnot : ¬ (dt k ≥ p.P ∨ r k.succ = r k.castSucc) := by
      push Not
      exact ⟨hdt k, ne_of_gt (hr k)⟩
    simp [hnot]
  simp_rw [hterm]
  simp [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul]

theorem statusQuo_violates_staircase_invariance (p : ProtocolParams) {K : ℕ}
    (hK : 2 ≤ K) {D rbar dt0 : ℝ} (hD : 0 < D) (hrbar : 0 < rbar) (hdt0 : dt0 < p.P)
    (r : Fin (K + 1) → ℝ) (dt : Fin K → ℝ)
    (hr : ∀ k : Fin K, r k.castSucc < r k.succ)
    (hdt : ∀ k : Fin K, dt k < p.P) :
    statusQuoFee p D (r 0) (r (Fin.last K)) rbar dt0 <
      ∑ k : Fin K, statusQuoFee p D (r k.castSucc) (r k.succ) rbar (dt k) := by
  rw [statusQuo_staircase_inflation p D rbar r dt hr hdt]
  have hmono : r 0 < r (Fin.last K) := by
    have hstrict : StrictMono r := Fin.strictMono_iff_lt_succ.mpr hr
    have h0K : (0 : Fin (K + 1)) < Fin.last K := by
      rw [Fin.lt_def]
      simp only [Fin.val_zero, Fin.val_last]
      omega
    exact hstrict h0K
  have hsingle : statusQuoFee p D (r 0) (r (Fin.last K)) rbar dt0 = D * rbar * (p.P / p.Y) := by
    unfold statusQuoFee
    have hnot : ¬ (dt0 ≥ p.P ∨ r (Fin.last K) = r 0) := by
      push Not
      exact ⟨hdt0, ne_of_gt hmono⟩
    simp [hnot]
  rw [hsingle]
  have hpos : 0 < D * rbar * (p.P / p.Y) := by
    have hPY : 0 < p.P / p.Y := div_pos p.hP p.hY
    positivity
  have hKreal : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  nlinarith

theorem statusQuo_spike_and_cut_arbitrage (p : ProtocolParams)
    {D rHi rLo rbar dt : ℝ} (hD : 0 < D) (hdtP : dt < p.P) (hlt : rLo < rHi)
    (harb : rbar * p.P < (rHi - rLo) * (p.P - dt)) :
    spikeCutTotalCost p D rHi rLo dt (statusQuoFee p D rHi rLo rbar dt) <
      holdCost p D rHi p.P ∧
    holdCost p D rHi p.P -
      spikeCutTotalCost p D rHi rLo dt (statusQuoFee p D rHi rLo rbar dt) =
      D * ((rHi - rLo) * (p.P - dt) - rbar * p.P) / p.Y := by
  have hfee : statusQuoFee p D rHi rLo rbar dt = D * rbar * (p.P / p.Y) := by
    unfold statusQuoFee
    have hnot : ¬ (dt ≥ p.P ∨ rLo = rHi) := by
      push Not
      exact ⟨hdtP, ne_of_lt hlt⟩
    simp [hnot]
  have hdiff := spikeCutTotalCost_sub_holdCost p D rHi rLo dt (statusQuoFee p D rHi rLo rbar dt)
  rw [hfee] at hdiff
  have hexact :
      holdCost p D rHi p.P -
        spikeCutTotalCost p D rHi rLo dt (statusQuoFee p D rHi rLo rbar dt) =
        D * ((rHi - rLo) * (p.P - dt) - rbar * p.P) / p.Y := by
    rw [hfee]
    have hYne : p.Y ≠ 0 := ne_of_gt p.hY
    field_simp [hYne] at hdiff ⊢
    linarith
  have hpos : 0 < D * ((rHi - rLo) * (p.P - dt) - rbar * p.P) / p.Y := by
    have hnum : 0 < (rHi - rLo) * (p.P - dt) - rbar * p.P := sub_pos.mpr harb
    exact div_pos (mul_pos hD hnum) p.hY
  exact ⟨by linarith, hexact⟩

theorem designA_eq_statusQuo_on_cuts (p : ProtocolParams)
    {D rHi rLo rbar dt : ℝ} (hdtP : dt < p.P) (hlt : rLo < rHi) :
    designAFee p D rHi rLo rbar dt = statusQuoFee p D rHi rLo rbar dt := by
  unfold designAFee statusQuoFee
  have hnot1 : ¬ (dt ≥ p.P ∨ rLo = rHi) := by
    push Not
    exact ⟨hdtP, ne_of_lt hlt⟩
  have hnot2 : ¬ (rHi < rLo) := not_lt.mpr (le_of_lt hlt)
  simp [hnot1, hnot2]

theorem designA_spike_and_cut_failure (p : ProtocolParams)
    {D rHi rLo rbar dt : ℝ} (hD : 0 < D) (hdtP : dt < p.P) (hlt : rLo < rHi)
    (harb : rbar * p.P < (rHi - rLo) * (p.P - dt)) :
    spikeCutTotalCost p D rHi rLo dt (designAFee p D rHi rLo rbar dt) <
      holdCost p D rHi p.P ∧
    holdCost p D rHi p.P -
      spikeCutTotalCost p D rHi rLo dt (designAFee p D rHi rLo rbar dt) =
      D * ((rHi - rLo) * (p.P - dt) - rbar * p.P) / p.Y := by
  rw [designA_eq_statusQuo_on_cuts p hdtP hlt]
  exact statusQuo_spike_and_cut_arbitrage p hD hdtP hlt harb

theorem mainnet_2026_03_06_wstETH_exploit :
    let D : ℝ := 7981691
    let rHi : ℝ := 105 / 1000
    let rLo : ℝ := 7 / 1000
    let rbar : ℝ := 15 / 1000
    let dt : ℝ := 3636
    statusQuoFee mainnetParams D rHi rLo rbar dt <
      (1 / 6) * holdCost mainnetParams D rHi mainnetParams.P ∧
    spikeCutTotalCost mainnetParams D rHi rLo dt (statusQuoFee mainnetParams D rHi rLo rbar dt) <
      (1 / 4) * holdCost mainnetParams D rHi mainnetParams.P ∧
    spikeCutTotalCost mainnetParams D rHi rLo dt (designAFee mainnetParams D rHi rLo rbar dt) <
      (1 / 4) * holdCost mainnetParams D rHi mainnetParams.P := by
  dsimp only
  have heq : designAFee mainnetParams 7981691 (105 / 1000) (7 / 1000) (15 / 1000) 3636 =
      statusQuoFee mainnetParams 7981691 (105 / 1000) (7 / 1000) (15 / 1000) 3636 :=
    designA_eq_statusQuo_on_cuts mainnetParams (by norm_num [mainnetParams]) (by norm_num)
  have hfee : statusQuoFee mainnetParams 7981691 (105 / 1000) (7 / 1000) (15 / 1000) 3636 <
      (1 / 6) * holdCost mainnetParams 7981691 (105 / 1000) mainnetParams.P := by
    unfold holdCost statusQuoFee mainnetParams
    norm_num
  have hsq : spikeCutTotalCost mainnetParams 7981691 (105 / 1000) (7 / 1000) 3636
      (statusQuoFee mainnetParams 7981691 (105 / 1000) (7 / 1000) (15 / 1000) 3636) <
      (1 / 4) * holdCost mainnetParams 7981691 (105 / 1000) mainnetParams.P := by
    unfold spikeCutTotalCost holdCost statusQuoFee mainnetParams
    norm_num
  exact ⟨hfee, hsq, by rw [heq]; exact hsq⟩

theorem designC_same_block_failure (p : ProtocolParams)
    {D r0 r1 rbar : ℝ} (hD : 0 < D) (hr : r0 < r1) (hrbar : 0 < rbar) :
    designCFee p D r0 r1 rbar 0 = 0 ∧
      ∃ dt : ℝ, 0 < dt ∧ dt < p.P ∧
        designCFee p D r0 r1 rbar dt < D * (r1 - r0) * (p.P / p.Y) := by
  constructor
  · unfold designCFee
    split_ifs <;> ring
  · let dt : ℝ := p.P * (r1 - r0) / (2 * (rbar + (r1 - r0)))
    have hdiff : 0 < r1 - r0 := sub_pos.mpr hr
    have hden : 0 < 2 * (rbar + (r1 - r0)) := by linarith
    have hdt0 : 0 < dt := div_pos (mul_pos p.hP hdiff) hden
    have hdtP : dt < p.P := by
      dsimp only [dt]
      rw [div_lt_iff₀ hden]
      nlinarith [p.hP]
    refine ⟨dt, hdt0, hdtP, ?_⟩
    unfold designCFee
    have hnot : ¬ (dt ≥ p.P ∨ r1 = r0) := by
      push Not
      exact ⟨hdtP, ne_of_gt hr⟩
    simp only [hnot, ↓reduceIte]
    have hmul : rbar * dt < (r1 - r0) * p.P := by
      dsimp only [dt]
      have : rbar * (p.P * (r1 - r0) / (2 * (rbar + (r1 - r0)))) < (r1 - r0) * p.P ↔
          rbar * (p.P * (r1 - r0)) < (r1 - r0) * p.P * (2 * (rbar + (r1 - r0))) := by
        rw [← mul_div_assoc, div_lt_iff₀ hden]
      rw [this]
      have hprod_pos : 0 < (r1 - r0) * p.P := mul_pos hdiff p.hP
      have hscale : rbar < 2 * (rbar + (r1 - r0)) := by linarith
      nlinarith
    have hYpos : 0 < p.Y := p.hY
    have hgoal : D * rbar * (dt / p.Y) < D * (r1 - r0) * (p.P / p.Y) := by
      rw [show D * rbar * (dt / p.Y) = (D * (rbar * dt)) / p.Y by ring]
      rw [show D * (r1 - r0) * (p.P / p.Y) = (D * ((r1 - r0) * p.P)) / p.Y by ring]
      exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hmul hD) hYpos
    exact hgoal

theorem designC_violates_A1 (p : ProtocolParams)
    {D r0 r1 rbar dt : ℝ} (hD : 0 < D) (hdt0 : 0 < dt) (hdtP : dt < p.P)
    (hspread : rbar < r1 - r0) (hr : r0 < r1) :
    designCFee p D r0 r1 rbar dt < D * (r1 - r0) * (dt / p.Y) := by
  unfold designCFee
  have hnot : ¬ (dt ≥ p.P ∨ r1 = r0) := by push Not; exact ⟨hdtP, ne_of_gt hr⟩
  simp only [hnot, ↓reduceIte]
  have hdtY : 0 < dt / p.Y := div_pos hdt0 p.hY
  have hmul : D * rbar < D * (r1 - r0) := mul_lt_mul_of_pos_left hspread hD
  exact mul_lt_mul_of_pos_right hmul hdtY

noncomputable def designBTimeCreditTotal (p : ProtocolParams) (D_small rbar : ℝ) : ℝ :=
  D_small * rbar * (p.P / p.Y)

theorem designB_variable_debt_failure (p : ProtocolParams)
    {D_small D_large r0 r1 rbar : ℝ}
    (hjump : D_small * rbar < D_large * (r1 - r0)) :
    designBTimeCreditTotal p D_small rbar < D_large * (r1 - r0) * (p.P / p.Y) := by
  unfold designBTimeCreditTotal
  have hPY : 0 < p.P / p.Y := div_pos p.hP p.hY
  exact mul_lt_mul_of_pos_right hjump hPY

end LiquityV2
