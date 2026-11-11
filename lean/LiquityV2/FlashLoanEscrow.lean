import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import LiquityV2.Defs
import LiquityV2.CooldownFees

namespace LiquityV2

open Finset BigOperators

noncomputable def flashLoanReopenCost (p : ProtocolParams)
    (D rHi rLo dt openFee fFlash gTx : ℝ) : ℝ :=
  holdCost p D rHi dt + openFee + fFlash * D + gTx + holdCost p D rLo (p.P - dt)

theorem flashLoanReopenCost_sub_holdCost (p : ProtocolParams)
    (D rHi rLo dt openFee fFlash gTx : ℝ) :
    holdCost p D rHi p.P - flashLoanReopenCost p D rHi rLo dt openFee fFlash gTx =
      D * (rHi - rLo) * ((p.P - dt) / p.Y) - (openFee + fFlash * D + gTx) := by
  unfold flashLoanReopenCost holdCost
  ring

theorem flash_loan_reopen_impossibility (p : ProtocolParams)
    (Φ_inplace : ℝ → ℝ → ℝ → ℝ → ℝ)
    {D rHi rLo dt openFee fFlash gTx : ℝ}
    (harb : openFee + fFlash * D + gTx < D * (rHi - rLo) * ((p.P - dt) / p.Y)) :
    flashLoanReopenCost p D rHi rLo dt openFee fFlash gTx < holdCost p D rHi p.P ∧
    (∀ penalty : ℝ, Φ_inplace D rHi rLo dt = penalty →
      flashLoanReopenCost p D rHi rLo dt openFee fFlash gTx < holdCost p D rHi p.P) := by
  have hdiff := flashLoanReopenCost_sub_holdCost p D rHi rLo dt openFee fFlash gTx
  have hlt : flashLoanReopenCost p D rHi rLo dt openFee fFlash gTx < holdCost p D rHi p.P := by
    linarith
  exact ⟨hlt, fun _ _ => hlt⟩

theorem flash_loan_reopen_rate_threshold (p : ProtocolParams)
    {D rHi rLo rbar dt fFlash gTx : ℝ} (hD : 0 < D)
    (hspread : rbar * (p.P / p.Y) + fFlash + gTx / D < (rHi - rLo) * ((p.P - dt) / p.Y)) :
    flashLoanReopenCost p D rHi rLo dt (D * rbar * (p.P / p.Y)) fFlash gTx <
      holdCost p D rHi p.P := by
  have hDne : D ≠ 0 := ne_of_gt hD
  have harb : D * rbar * (p.P / p.Y) + fFlash * D + gTx < D * (rHi - rLo) * ((p.P - dt) / p.Y) := by
    have hmul := mul_lt_mul_of_pos_left hspread hD
    have hlhs : D * (rbar * (p.P / p.Y) + fFlash + gTx / D) =
        D * rbar * (p.P / p.Y) + fFlash * D + gTx := by
      field_simp [hDne]
    have hrhs : D * ((rHi - rLo) * ((p.P - dt) / p.Y)) = D * (rHi - rLo) * ((p.P - dt) / p.Y) := by
      ring
    linarith
  exact (flash_loan_reopen_impossibility p (fun _ _ _ _ => 0) harb).1

theorem flash_loan_reopen_mainnet_witness :
    let D : ℝ := 7981691
    let rHi : ℝ := 105 / 1000
    let rLo : ℝ := 7 / 1000
    let rbar : ℝ := 15 / 1000
    let dt : ℝ := 3636
    let openFee := D * rbar * (mainnetParams.P / mainnetParams.Y)
    flashLoanReopenCost mainnetParams D rHi rLo dt openFee 0 50 <
      (1 / 4) * holdCost mainnetParams D rHi mainnetParams.P := by
  dsimp only
  unfold flashLoanReopenCost holdCost mainnetParams
  norm_num

noncomputable def designDBond (p : ProtocolParams) (D rHi rRef : ℝ) : ℝ :=
  D * (rHi - rRef) * (p.P / p.Y)

noncomputable def designDVested (p : ProtocolParams) (B dt : ℝ) : ℝ :=
  B * (min dt p.P / p.P)

noncomputable def designDUnvested (p : ProtocolParams) (B dt : ℝ) : ℝ :=
  B - designDVested p B dt

theorem designDUnvested_eq_remaining_spread (p : ProtocolParams)
    {D rHi rRef dt : ℝ} (hdtP : dt ≤ p.P) :
    designDUnvested p (designDBond p D rHi rRef) dt =
      D * (rHi - rRef) * ((p.P - dt) / p.Y) := by
  unfold designDUnvested designDVested designDBond
  rw [min_eq_left hdtP]
  have hPne : p.P ≠ 0 := ne_of_gt p.hP
  have hYne : p.Y ≠ 0 := ne_of_gt p.hY
  field_simp [hPne, hYne]

theorem designD_honest_hold_zero_extra_cost (p : ProtocolParams)
    {D rHi rRef dt : ℝ} (hdt : p.P ≤ dt) :
    let B := designDBond p D rHi rRef
    designDVested p B dt = B ∧
    designDUnvested p B dt = 0 ∧
    holdCost p D rHi p.P + B - designDVested p B dt = holdCost p D rHi p.P := by
  dsimp only
  have hvest : designDVested p (designDBond p D rHi rRef) dt = designDBond p D rHi rRef := by
    unfold designDVested
    rw [min_eq_right hdt, div_self (ne_of_gt p.hP), mul_one]
  have hunvest : designDUnvested p (designDBond p D rHi rRef) dt = 0 := by
    unfold designDUnvested
    linarith
  exact ⟨hvest, hunvest, by linarith⟩

noncomputable def designDFlashLoanReopenCost (p : ProtocolParams)
    (D rHi rLo dt openFee fFlash gTx : ℝ) : ℝ :=
  let B := designDBond p D rHi p.rMin
  holdCost p D rHi dt + designDUnvested p B dt + openFee + fFlash * D + gTx +
    holdCost p D rLo (p.P - dt)

theorem designD_blocks_flash_loan_reopen (p : ProtocolParams)
    {D rHi rLo dt openFee fFlash gTx : ℝ}
    (hD : 0 ≤ D) (hdtP : dt ≤ p.P) (hrLo : p.rMin ≤ rLo)
    (hopen : 0 ≤ openFee) (hflash : 0 ≤ fFlash) (hgas : 0 ≤ gTx) :
    designDFlashLoanReopenCost p D rHi rLo dt openFee fFlash gTx - holdCost p D rHi p.P =
      D * (rLo - p.rMin) * ((p.P - dt) / p.Y) + openFee + fFlash * D + gTx ∧
    holdCost p D rHi p.P + openFee + fFlash * D + gTx ≤
      designDFlashLoanReopenCost p D rHi rLo dt openFee fFlash gTx ∧
    holdCost p D rHi p.P ≤
      designDFlashLoanReopenCost p D rHi rLo dt openFee fFlash gTx := by
  have hunvest := designDUnvested_eq_remaining_spread p (D := D) (rHi := rHi) (rRef := p.rMin) hdtP
  have hid :
      designDFlashLoanReopenCost p D rHi rLo dt openFee fFlash gTx - holdCost p D rHi p.P =
        D * (rLo - p.rMin) * ((p.P - dt) / p.Y) + openFee + fFlash * D + gTx := by
    unfold designDFlashLoanReopenCost
    dsimp only
    rw [hunvest]
    unfold holdCost
    ring
  have hspread_nn : 0 ≤ D * (rLo - p.rMin) * ((p.P - dt) / p.Y) :=
    mul_nonneg (mul_nonneg hD (sub_nonneg.mpr hrLo))
      (div_nonneg (sub_nonneg.mpr hdtP) (le_of_lt p.hY))
  have hflash_nn : 0 ≤ fFlash * D := mul_nonneg hflash hD
  exact ⟨hid, by linarith, by linarith⟩

theorem designD_strictly_blocks_flash_loan_reopen (p : ProtocolParams)
    {D rHi rLo dt openFee fFlash gTx : ℝ}
    (hD : 0 ≤ D) (hdtP : dt ≤ p.P) (hrLo : p.rMin ≤ rLo)
    (hopen : 0 ≤ openFee) (hflash : 0 ≤ fFlash) (hgas : 0 ≤ gTx)
    (hpos : 0 < openFee + fFlash * D + gTx) :
    holdCost p D rHi p.P <
      designDFlashLoanReopenCost p D rHi rLo dt openFee fFlash gTx := by
  have h := (designD_blocks_flash_loan_reopen p (rHi := rHi) hD hdtP hrLo hopen hflash hgas).2.1
  linarith

theorem designD_blocks_inplace_cut (p : ProtocolParams)
    {D rHi rLo dt : ℝ} (hdtP : dt ≤ p.P) :
    let forfeit := designDUnvested p (designDBond p D rHi rLo) dt
    spikeCutTotalCost p D rHi rLo dt forfeit = holdCost p D rHi p.P := by
  dsimp only
  rw [designDUnvested_eq_remaining_spread p hdtP]
  unfold spikeCutTotalCost holdCost
  ring

theorem designD_staircase_additive (p : ProtocolParams) {K : ℕ}
    (D : ℝ) (r : Fin (K + 1) → ℝ) :
    (∑ k : Fin K, designDBond p D (r k.succ) (r k.castSucc)) =
      designDBond p D (r (Fin.last K)) (r 0) := by
  unfold designDBond
  have htele : (∑ k : Fin K, (r k.succ - r k.castSucc)) = r (Fin.last K) - r 0 := by
    induction K with
    | zero => simp
    | succ m ih =>
      rw [Fin.sum_univ_castSucc]
      have hcast_eq : ∀ k : Fin m, (k.castSucc : Fin (m + 1)).succ = k.succ.castSucc := by
        intro k; ext; simp
      simp_rw [hcast_eq]
      rw [ih (fun i => r i.castSucc)]
      have hlast_succ : (Fin.last m).succ = Fin.last (m + 1) := by ext; simp
      rw [hlast_succ, Fin.castSucc_zero]
      ring
  calc (∑ k : Fin K, D * (r k.succ - r k.castSucc) * (p.P / p.Y))
      = ∑ k : Fin K, (D * (p.P / p.Y)) * (r k.succ - r k.castSucc) := by
        apply Finset.sum_congr rfl; intro k _; ring
    _ = (D * (p.P / p.Y)) * (∑ k : Fin K, (r k.succ - r k.castSucc)) := by
        rw [← Finset.mul_sum]
    _ = (D * (p.P / p.Y)) * (r (Fin.last K) - r 0) := by rw [htele]
    _ = D * (r (Fin.last K) - r 0) * (p.P / p.Y) := by ring

theorem designD_sybil_neutral (p : ProtocolParams) (lam D D1 D2 rHi rRef dt : ℝ) :
    designDBond p (lam * D) rHi rRef = lam * designDBond p D rHi rRef ∧
    designDBond p (D1 + D2) rHi rRef =
      designDBond p D1 rHi rRef + designDBond p D2 rHi rRef ∧
    designDUnvested p (designDBond p (D1 + D2) rHi rRef) dt =
      designDUnvested p (designDBond p D1 rHi rRef) dt +
      designDUnvested p (designDBond p D2 rHi rRef) dt := by
  unfold designDUnvested designDVested designDBond
  refine ⟨by ring, by ring, by ring⟩

structure DesignDState where
  bondedPrincipal : ℝ
  rate : ℝ
  unvestedBond : ℝ
  lastUpdateTime : ℝ
  vestEndTime : ℝ

def DesignDCoverageInvariant (p : ProtocolParams) (s : DesignDState) : Prop :=
  0 ≤ s.bondedPrincipal ∧
  p.rMin ≤ s.rate ∧
  s.lastUpdateTime ≤ s.vestEndTime ∧
  s.unvestedBond = s.bondedPrincipal * (s.rate - p.rMin) * ((s.vestEndTime - s.lastUpdateTime) / p.Y)

lemma designD_unvested_nonneg (p : ProtocolParams) {s : DesignDState}
    (hinv : DesignDCoverageInvariant p s) : 0 ≤ s.unvestedBond := by
  rcases hinv with ⟨hD, hr, hle, hB⟩
  rw [hB]
  exact mul_nonneg (mul_nonneg hD (sub_nonneg.mpr hr))
    (div_nonneg (sub_nonneg.mpr hle) (le_of_lt p.hY))

noncomputable def designDSettleVested (s : DesignDState) (t : ℝ) : ℝ :=
  if s.vestEndTime ≤ t then s.unvestedBond
  else if t ≤ s.lastUpdateTime then 0
  else s.unvestedBond * ((t - s.lastUpdateTime) / (s.vestEndTime - s.lastUpdateTime))

noncomputable def designDSettleState (s : DesignDState) (t : ℝ) : DesignDState :=
  if s.vestEndTime ≤ t then
    { s with unvestedBond := 0, lastUpdateTime := t, vestEndTime := t }
  else if t ≤ s.lastUpdateTime then s
  else
    { s with unvestedBond := s.unvestedBond - designDSettleVested s t, lastUpdateTime := t }

theorem designDSettle_preserves_invariant (p : ProtocolParams) {s : DesignDState} {t : ℝ}
    (hinv : DesignDCoverageInvariant p s) (ht : s.lastUpdateTime ≤ t) :
    DesignDCoverageInvariant p (designDSettleState s t) ∧
    (t ≤ s.vestEndTime →
      designDSettleVested s t =
        s.bondedPrincipal * (s.rate - p.rMin) * ((t - s.lastUpdateTime) / p.Y)) := by
  rcases hinv with ⟨hD, hr, hle, hB⟩
  by_cases hend : s.vestEndTime ≤ t
  · unfold designDSettleState designDSettleVested
    simp only [hend, ↓reduceIte]
    refine ⟨⟨hD, hr, le_rfl, by simp⟩, fun hle_t => ?_⟩
    have heq : t = s.vestEndTime := le_antisymm hle_t hend
    rw [heq, hB]
  · push Not at hend
    by_cases hteq : t ≤ s.lastUpdateTime
    · have heq : t = s.lastUpdateTime := le_antisymm hteq ht
      unfold designDSettleState designDSettleVested
      have hnotend : ¬ s.vestEndTime ≤ t := not_le.mpr hend
      simp only [hnotend, hteq, ↓reduceIte]
      refine ⟨⟨hD, hr, hle, hB⟩, fun _ => ?_⟩
      rw [heq]; ring
    · push Not at hteq
      unfold designDSettleState designDSettleVested
      have hnotend : ¬ s.vestEndTime ≤ t := not_le.mpr hend
      have hnotle : ¬ t ≤ s.lastUpdateTime := not_le.mpr hteq
      simp only [hnotend, hnotle, ↓reduceIte]
      have hspan : s.vestEndTime - s.lastUpdateTime ≠ 0 := ne_of_gt (by linarith)
      have hYne : p.Y ≠ 0 := ne_of_gt p.hY
      have hvest_eq : s.unvestedBond * ((t - s.lastUpdateTime) / (s.vestEndTime - s.lastUpdateTime)) =
          s.bondedPrincipal * (s.rate - p.rMin) * ((t - s.lastUpdateTime) / p.Y) := by
        rw [hB]
        field_simp [hspan, hYne]
      refine ⟨⟨hD, hr, le_of_lt hend, ?_⟩, fun _ => hvest_eq⟩
      rw [hvest_eq, hB]
      ring

noncomputable def designDIncreaseState (p : ProtocolParams)
    (t Dnew rnew : ℝ) : DesignDState where
  bondedPrincipal := Dnew
  rate := rnew
  unvestedBond := Dnew * (rnew - p.rMin) * (p.P / p.Y)
  lastUpdateTime := t
  vestEndTime := t + p.P

theorem designDIncrease_invariant_topup_and_staircase (p : ProtocolParams)
    {s : DesignDState} {t Dnew rnew : ℝ}
    (hinv : DesignDCoverageInvariant p s)
    (ht : s.lastUpdateTime ≤ t) (htP : s.vestEndTime - t ≤ p.P)
    (hDinc : s.bondedPrincipal ≤ Dnew) (hrinc : s.rate ≤ rnew) :
    let sSettle := designDSettleState s t
    let sNext := designDIncreaseState p t Dnew rnew
    DesignDCoverageInvariant p sNext ∧
    sSettle.unvestedBond ≤ sNext.unvestedBond ∧
    (Dnew = s.bondedPrincipal → s.vestEndTime - s.lastUpdateTime = p.P → t ≤ s.vestEndTime →
      (sNext.unvestedBond - sSettle.unvestedBond) - designDSettleVested s t =
        s.bondedPrincipal * (rnew - s.rate) * (p.P / p.Y)) := by
  dsimp only
  have hset := designDSettle_preserves_invariant p hinv ht
  rcases hinv with ⟨hD0, hr0, _, hB0⟩
  have hDnew : 0 ≤ Dnew := le_trans hD0 hDinc
  have hrnew : p.rMin ≤ rnew := le_trans hr0 hrinc
  have hinv_next : DesignDCoverageInvariant p (designDIncreaseState p t Dnew rnew) := by
    unfold designDIncreaseState
    refine ⟨hDnew, hrnew, by dsimp only; linarith [p.hP], by dsimp only; ring⟩
  have htopup : (designDSettleState s t).unvestedBond ≤ (designDIncreaseState p t Dnew rnew).unvestedBond := by
    rcases hset.1 with ⟨hDs, hrs, hles, hBs⟩
    rw [hBs]
    unfold designDIncreaseState
    dsimp only
    have hrem_le : (designDSettleState s t).vestEndTime - (designDSettleState s t).lastUpdateTime ≤ p.P := by
      unfold designDSettleState
      split_ifs with hend hle_t
      · simp [le_of_lt p.hP]
      · linarith
      · linarith
    have hDs_eq : (designDSettleState s t).bondedPrincipal = s.bondedPrincipal := by
      unfold designDSettleState; split_ifs <;> rfl
    have hrs_eq : (designDSettleState s t).rate = s.rate := by
      unfold designDSettleState; split_ifs <;> rfl
    rw [hDs_eq, hrs_eq]
    have h1 : s.bondedPrincipal * (s.rate - p.rMin) ≤ Dnew * (rnew - p.rMin) :=
      mul_le_mul hDinc (sub_le_sub_right hrinc p.rMin) (sub_nonneg.mpr hr0) hDnew
    have h2 : ((designDSettleState s t).vestEndTime - (designDSettleState s t).lastUpdateTime) / p.Y ≤
        p.P / p.Y := div_le_div_of_nonneg_right hrem_le (le_of_lt p.hY)
    exact mul_le_mul h1 h2 (div_nonneg (sub_nonneg.mpr hles) (le_of_lt p.hY))
      (mul_nonneg hDnew (sub_nonneg.mpr hrnew))
  refine ⟨hinv_next, htopup, ?_⟩
  intro hDeq hspan htle
  have hvest := hset.2 htle
  have hBrem : (designDSettleState s t).unvestedBond = s.unvestedBond - designDSettleVested s t := by
    unfold designDSettleState designDSettleVested
    split_ifs with hend hle_t
    · ring
    · ring
    · rfl
  rw [hBrem, hB0, hspan, hDeq]
  unfold designDIncreaseState
  dsimp only
  ring

noncomputable def designDPureCutForfeit (p : ProtocolParams) (s : DesignDState) (t rnew : ℝ) : ℝ :=
  (designDSettleState s t).unvestedBond * ((s.rate - rnew) / (s.rate - p.rMin))

noncomputable def designDPureCutState (p : ProtocolParams) (s : DesignDState) (t rnew : ℝ) : DesignDState :=
  let sSettle := designDSettleState s t
  { sSettle with rate := rnew, unvestedBond := sSettle.unvestedBond - designDPureCutForfeit p s t rnew }

theorem designD_pure_cut_zero_underflow_and_invariant (p : ProtocolParams)
    {s : DesignDState} {t rnew Dcurr : ℝ}
    (hinv : DesignDCoverageInvariant p s)
    (ht0 : s.lastUpdateTime ≤ t) (ht1 : t ≤ s.vestEndTime)
    (hrmin : p.rMin ≤ rnew) (hrlt : rnew < s.rate)
    (_hcomp : s.bondedPrincipal ≤ Dcurr) :
    let Brem := (designDSettleState s t).unvestedBond
    let Fcut := designDPureCutForfeit p s t rnew
    0 ≤ Fcut ∧ Fcut ≤ Brem ∧
    Fcut = s.bondedPrincipal * (s.rate - rnew) * ((s.vestEndTime - t) / p.Y) ∧
    DesignDCoverageInvariant p (designDPureCutState p s t rnew) := by
  dsimp only
  have hset := (designDSettle_preserves_invariant p hinv ht0).1
  have hBrem_nn : 0 ≤ (designDSettleState s t).unvestedBond := designD_unvested_nonneg p hset
  have hden_pos : 0 < s.rate - p.rMin := by linarith
  have hfrac_nn : 0 ≤ (s.rate - rnew) / (s.rate - p.rMin) :=
    div_nonneg (sub_nonneg.mpr (le_of_lt hrlt)) (le_of_lt hden_pos)
  have hfrac_le1 : (s.rate - rnew) / (s.rate - p.rMin) ≤ 1 := by
    rw [div_le_one hden_pos]; linarith
  have hF_nn : 0 ≤ designDPureCutForfeit p s t rnew := mul_nonneg hBrem_nn hfrac_nn
  have hF_le : designDPureCutForfeit p s t rnew ≤ (designDSettleState s t).unvestedBond := by
    unfold designDPureCutForfeit
    calc (designDSettleState s t).unvestedBond * ((s.rate - rnew) / (s.rate - p.rMin))
        ≤ (designDSettleState s t).unvestedBond * 1 := mul_le_mul_of_nonneg_left hfrac_le1 hBrem_nn
      _ = (designDSettleState s t).unvestedBond := mul_one _
  have hBrem_eq : (designDSettleState s t).unvestedBond =
      s.bondedPrincipal * (s.rate - p.rMin) * ((s.vestEndTime - t) / p.Y) := by
    rcases hset with ⟨_, _, _, hBs⟩
    rw [hBs]
    unfold designDSettleState
    split_ifs with hend hle_t
    · have heq : t = s.vestEndTime := le_antisymm ht1 hend
      simp [heq]
    · have heq : t = s.lastUpdateTime := le_antisymm hle_t ht0
      simp [heq]
    · rfl
  have hden_ne : s.rate - p.rMin ≠ 0 := ne_of_gt hden_pos
  have hF_exact : designDPureCutForfeit p s t rnew =
      s.bondedPrincipal * (s.rate - rnew) * ((s.vestEndTime - t) / p.Y) := by
    unfold designDPureCutForfeit
    rw [hBrem_eq]
    field_simp [hden_ne]
  have hinv_after : DesignDCoverageInvariant p (designDPureCutState p s t rnew) := by
    unfold designDPureCutState
    dsimp only
    rcases hset with ⟨hDs, _, hles, _⟩
    have hDs_eq : (designDSettleState s t).bondedPrincipal = s.bondedPrincipal := by
      unfold designDSettleState; split_ifs <;> rfl
    have hspan_eq : (designDSettleState s t).vestEndTime - (designDSettleState s t).lastUpdateTime =
        s.vestEndTime - t := by
      unfold designDSettleState
      split_ifs with hend hle_t
      · have heq : t = s.vestEndTime := le_antisymm ht1 hend
        simp [heq]
      · have heq : t = s.lastUpdateTime := le_antisymm hle_t ht0
        simp [heq]
      · rfl
    refine ⟨hDs, hrmin, hles, ?_⟩
    rw [hBrem_eq, hF_exact, hDs_eq, hspan_eq]
    ring
  exact ⟨hF_nn, hF_le, hF_exact, hinv_after⟩

theorem designD_two_step_pure_cut_exact_preservation (p : ProtocolParams)
    {D rHi rMid rLo dt1 dt2 : ℝ}
    (hD : 0 ≤ D) (hdt1 : 0 ≤ dt1) (hdt2 : 0 ≤ dt2) (hsum : dt1 + dt2 ≤ p.P)
    (hlo : p.rMin ≤ rLo) (hmid : rLo < rMid) (hhi : rMid < rHi) :
    let s0 := designDIncreaseState p 0 D rHi
    let F1 := designDPureCutForfeit p s0 dt1 rMid
    let s1 := designDPureCutState p s0 dt1 rMid
    let F2 := designDPureCutForfeit p s1 (dt1 + dt2) rLo
    let s2 := designDPureCutState p s1 (dt1 + dt2) rLo
    0 ≤ F1 ∧ 0 ≤ F2 ∧ DesignDCoverageInvariant p s2 ∧
    holdCost p D rHi dt1 + F1 + holdCost p D rMid dt2 + F2 +
      holdCost p D rLo (p.P - dt1 - dt2) = holdCost p D rHi p.P := by
  dsimp only
  have hinv0 : DesignDCoverageInvariant p (designDIncreaseState p 0 D rHi) := by
    unfold designDIncreaseState
    refine ⟨hD, by dsimp only; linarith, by dsimp only; linarith [p.hP], by dsimp only; ring⟩
  have hc1 := designD_pure_cut_zero_underflow_and_invariant p (s := designDIncreaseState p 0 D rHi)
    (t := dt1) (rnew := rMid) (Dcurr := D) hinv0 hdt1 (by unfold designDIncreaseState; linarith)
    (by linarith) hhi le_rfl
  have ht1_last : (designDPureCutState p (designDIncreaseState p 0 D rHi) dt1 rMid).lastUpdateTime ≤ dt1 + dt2 := by
    unfold designDPureCutState designDSettleState designDIncreaseState
    split_ifs <;> dsimp only <;> linarith
  have ht1_end : dt1 + dt2 ≤ (designDPureCutState p (designDIncreaseState p 0 D rHi) dt1 rMid).vestEndTime := by
    unfold designDPureCutState designDSettleState designDIncreaseState
    split_ifs <;> dsimp only <;> linarith
  have hD1_eq : (designDPureCutState p (designDIncreaseState p 0 D rHi) dt1 rMid).bondedPrincipal = D := by
    unfold designDPureCutState designDSettleState designDIncreaseState; split_ifs <;> rfl
  have hc2 := designD_pure_cut_zero_underflow_and_invariant p
    (s := designDPureCutState p (designDIncreaseState p 0 D rHi) dt1 rMid)
    (t := dt1 + dt2) (rnew := rLo) (Dcurr := D) hc1.2.2.2 ht1_last ht1_end hlo hmid (by rw [hD1_eq])
  have hF1 : designDPureCutForfeit p (designDIncreaseState p 0 D rHi) dt1 rMid =
      D * (rHi - rMid) * ((p.P - dt1) / p.Y) := by
    rw [hc1.2.2.1]; unfold designDIncreaseState; dsimp only; ring
  have hF2 : designDPureCutForfeit p (designDPureCutState p (designDIncreaseState p 0 D rHi) dt1 rMid)
      (dt1 + dt2) rLo = D * (rMid - rLo) * ((p.P - (dt1 + dt2)) / p.Y) := by
    rw [hc2.2.2.1]
    have hD1 : (designDPureCutState p (designDIncreaseState p 0 D rHi) dt1 rMid).bondedPrincipal = D := by
      unfold designDPureCutState designDSettleState designDIncreaseState; split_ifs <;> rfl
    have hR1 : (designDPureCutState p (designDIncreaseState p 0 D rHi) dt1 rMid).rate = rMid := rfl
    have hE1 : (designDPureCutState p (designDIncreaseState p 0 D rHi) dt1 rMid).vestEndTime = p.P := by
      unfold designDPureCutState designDSettleState designDIncreaseState
      split_ifs with hend hle_t
      · dsimp only; linarith
      · dsimp only; ring
      · dsimp only; ring
    rw [hD1, hR1, hE1]
  refine ⟨hc1.1, hc2.1, hc2.2.2.2, ?_⟩
  rw [hF1, hF2]
  unfold holdCost
  ring

noncomputable def designDRepayCapForfeit (p : ProtocolParams) (s : DesignDState) (t ΔD : ℝ) : ℝ :=
  min (designDSettleState s t).unvestedBond
    (ΔD * (s.rate - p.rMin) * ((s.vestEndTime - t) / p.Y))

noncomputable def designDRepayCapState (p : ProtocolParams) (s : DesignDState) (t ΔD : ℝ) : DesignDState :=
  let sSettle := designDSettleState s t
  { sSettle with
      bondedPrincipal := max 0 (s.bondedPrincipal - ΔD)
      unvestedBond := sSettle.unvestedBond - designDRepayCapForfeit p s t ΔD }

theorem designD_repay_cap_zero_underflow_and_zero_dilution (p : ProtocolParams)
    {s : DesignDState} {t ΔD Dcurr : ℝ}
    (hinv : DesignDCoverageInvariant p s)
    (ht0 : s.lastUpdateTime ≤ t) (ht1 : t ≤ s.vestEndTime)
    (hΔD : 0 ≤ ΔD) (_hcomp : s.bondedPrincipal ≤ Dcurr) :
    let Brem := (designDSettleState s t).unvestedBond
    let Frepay := designDRepayCapForfeit p s t ΔD
    0 ≤ Frepay ∧ Frepay ≤ Brem ∧
    (ΔD ≤ s.bondedPrincipal →
      Frepay = ΔD * (s.rate - p.rMin) * ((s.vestEndTime - t) / p.Y) ∧
      DesignDCoverageInvariant p (designDRepayCapState p s t ΔD)) ∧
    (s.bondedPrincipal ≤ ΔD → Frepay = Brem) := by
  dsimp only
  have hset := (designDSettle_preserves_invariant p hinv ht0).1
  have hBrem_nn : 0 ≤ (designDSettleState s t).unvestedBond := designD_unvested_nonneg p hset
  rcases hinv with ⟨hD0, hr0, _, _⟩
  have hBrem_eq : (designDSettleState s t).unvestedBond =
      s.bondedPrincipal * (s.rate - p.rMin) * ((s.vestEndTime - t) / p.Y) := by
    rcases hset with ⟨_, _, _, hBs⟩
    rw [hBs]
    unfold designDSettleState
    split_ifs with hend hle_t
    · have heq : t = s.vestEndTime := le_antisymm ht1 hend
      simp [heq]
    · have heq : t = s.lastUpdateTime := le_antisymm hle_t ht0
      simp [heq]
    · rfl
  have hfac_nn : 0 ≤ (s.rate - p.rMin) * ((s.vestEndTime - t) / p.Y) :=
    mul_nonneg (sub_nonneg.mpr hr0) (div_nonneg (sub_nonneg.mpr ht1) (le_of_lt p.hY))
  have hcap_nn : 0 ≤ ΔD * (s.rate - p.rMin) * ((s.vestEndTime - t) / p.Y) := by
    have : ΔD * (s.rate - p.rMin) * ((s.vestEndTime - t) / p.Y) =
        ΔD * ((s.rate - p.rMin) * ((s.vestEndTime - t) / p.Y)) := by ring
    rw [this]; exact mul_nonneg hΔD hfac_nn
  refine ⟨le_min hBrem_nn hcap_nn, min_le_left _ _, ?_, ?_⟩
  · intro hpart
    have hle : ΔD * (s.rate - p.rMin) * ((s.vestEndTime - t) / p.Y) ≤
        (designDSettleState s t).unvestedBond := by
      rw [hBrem_eq]
      have h1 : ΔD * (s.rate - p.rMin) * ((s.vestEndTime - t) / p.Y) =
          ΔD * ((s.rate - p.rMin) * ((s.vestEndTime - t) / p.Y)) := by ring
      have h2 : s.bondedPrincipal * (s.rate - p.rMin) * ((s.vestEndTime - t) / p.Y) =
          s.bondedPrincipal * ((s.rate - p.rMin) * ((s.vestEndTime - t) / p.Y)) := by ring
      rw [h1, h2]
      exact mul_le_mul_of_nonneg_right hpart hfac_nn
    have hFeq : designDRepayCapForfeit p s t ΔD =
        ΔD * (s.rate - p.rMin) * ((s.vestEndTime - t) / p.Y) := min_eq_right hle
    refine ⟨hFeq, ?_⟩
    unfold designDRepayCapState
    dsimp only
    rcases hset with ⟨_, hrs, hles, _⟩
    have hrs_eq : (designDSettleState s t).rate = s.rate := by
      unfold designDSettleState; split_ifs <;> rfl
    have hspan_eq : (designDSettleState s t).vestEndTime - (designDSettleState s t).lastUpdateTime =
        s.vestEndTime - t := by
      unfold designDSettleState
      split_ifs with hend hle_t
      · have heq : t = s.vestEndTime := le_antisymm ht1 hend
        simp [heq]
      · have heq : t = s.lastUpdateTime := le_antisymm hle_t ht0
        simp [heq]
      · rfl
    have hmax : max 0 (s.bondedPrincipal - ΔD) = s.bondedPrincipal - ΔD := max_eq_right (sub_nonneg.mpr hpart)
    refine ⟨le_max_left _ _, hrs, hles, ?_⟩
    rw [hmax, hBrem_eq, hFeq, hrs_eq, hspan_eq]
    ring
  · intro hfull
    have hge : (designDSettleState s t).unvestedBond ≤
        ΔD * (s.rate - p.rMin) * ((s.vestEndTime - t) / p.Y) := by
      rw [hBrem_eq]
      have h1 : ΔD * (s.rate - p.rMin) * ((s.vestEndTime - t) / p.Y) =
          ΔD * ((s.rate - p.rMin) * ((s.vestEndTime - t) / p.Y)) := by ring
      have h2 : s.bondedPrincipal * (s.rate - p.rMin) * ((s.vestEndTime - t) / p.Y) =
          s.bondedPrincipal * ((s.rate - p.rMin) * ((s.vestEndTime - t) / p.Y)) := by ring
      rw [h1, h2]
      exact mul_le_mul_of_nonneg_right hfull hfac_nn
    exact min_eq_left hge

theorem designD_partial_repay_blocks_bypass (p : ProtocolParams)
    {s : DesignDState} {t ΔD1 ΔD2 Dcurr : ℝ}
    (hinv : DesignDCoverageInvariant p s)
    (ht0 : s.lastUpdateTime ≤ t) (ht1 : t ≤ s.vestEndTime)
    (h1 : 0 ≤ ΔD1) (h2 : 0 ≤ ΔD2) (hsum : ΔD1 + ΔD2 = s.bondedPrincipal)
    (hcomp : s.bondedPrincipal ≤ Dcurr) :
    let s1 := designDRepayCapState p s t ΔD1
    designDRepayCapForfeit p s t ΔD1 + designDRepayCapForfeit p s1 t ΔD2 =
      (designDSettleState s t).unvestedBond := by
  dsimp only
  have hle1 : ΔD1 ≤ s.bondedPrincipal := by linarith
  have hr1 := (designD_repay_cap_zero_underflow_and_zero_dilution p hinv ht0 ht1 h1 hcomp).2.2.1 hle1
  have ht1_last : (designDRepayCapState p s t ΔD1).lastUpdateTime ≤ t := by
    unfold designDRepayCapState designDSettleState
    split_ifs <;> dsimp only <;> linarith
  have ht1_end : t ≤ (designDRepayCapState p s t ΔD1).vestEndTime := by
    unfold designDRepayCapState designDSettleState
    split_ifs <;> dsimp only <;> linarith
  have hD1_eq : (designDRepayCapState p s t ΔD1).bondedPrincipal = ΔD2 := by
    unfold designDRepayCapState; dsimp only
    rw [max_eq_right (by linarith)]; linarith
  have hr2 := (designD_repay_cap_zero_underflow_and_zero_dilution p hr1.2 ht1_last ht1_end h2
    (by rw [hD1_eq])).2.2.2 (by rw [hD1_eq])
  have hs1_settle : (designDSettleState (designDRepayCapState p s t ΔD1) t).unvestedBond =
      (designDRepayCapState p s t ΔD1).unvestedBond := by
    unfold designDSettleState designDRepayCapState
    split_ifs with hend hle_t
    · dsimp only
      have hB1 : (designDSettleState s t).unvestedBond = 0 := by
        unfold designDSettleState at hend ⊢
        split_ifs at hend ⊢
        · rfl
        · linarith
        · linarith
      have hF1_zero : designDRepayCapForfeit p s t ΔD1 = 0 := by
        have h0 := (designD_repay_cap_zero_underflow_and_zero_dilution p hinv ht0 ht1 h1 hcomp).1
        have hle := (designD_repay_cap_zero_underflow_and_zero_dilution p hinv ht0 ht1 h1 hcomp).2.1
        linarith
      linarith
    · rfl
    · exfalso
      unfold designDSettleState at hle_t
      split_ifs at hle_t <;> dsimp only at hle_t <;> linarith
  rw [hr2, hs1_settle]
  unfold designDRepayCapState
  dsimp only
  ring

theorem designD_withdrawBold_stateful_blocks_bypass (p : ProtocolParams)
    {s : DesignDState} {t ΔD rLo dt2 openFee fFlash gTx : ℝ}
    (hinv : DesignDCoverageInvariant p s)
    (ht : s.lastUpdateTime ≤ t) (htP : s.vestEndTime - t ≤ p.P)
    (hΔD : 0 ≤ ΔD) (hdt2 : dt2 ≤ p.P) (hrLo : p.rMin ≤ rLo)
    (hopen : 0 ≤ openFee) (hflash : 0 ≤ fFlash) (hgas : 0 ≤ gTx) :
    let Dnew := s.bondedPrincipal + ΔD
    let sNext := designDIncreaseState p t Dnew s.rate
    DesignDCoverageInvariant p sNext ∧
    (designDSettleState s t).unvestedBond ≤ sNext.unvestedBond ∧
    holdCost p Dnew s.rate p.P + openFee + fFlash * Dnew + gTx ≤
      designDFlashLoanReopenCost p Dnew s.rate rLo dt2 openFee fFlash gTx := by
  dsimp only
  have hinc := designDIncrease_invariant_topup_and_staircase p (s := s) (t := t)
    (Dnew := s.bondedPrincipal + ΔD) (rnew := s.rate) hinv ht htP (by linarith) le_rfl
  have hDnew : 0 ≤ s.bondedPrincipal + ΔD := add_nonneg hinv.1 hΔD
  have hsec := (designD_blocks_flash_loan_reopen p (rHi := s.rate) hDnew hdt2 hrLo hopen hflash hgas).2.1
  exact ⟨hinc.1, hinc.2.1, hsec⟩

theorem designAStar_batch_join_blocks_bypass (p : ProtocolParams)
    {D rHi rBatch dt openFee : ℝ}
    (hdtP : dt < p.P) :
    let batchJoinFee := max openFee (D * (rHi - rBatch) * ((p.P - dt) / p.Y))
    openFee ≤ batchJoinFee ∧
    holdCost p D rHi p.P ≤ spikeCutTotalCost p D rHi rBatch dt batchJoinFee := by
  dsimp only
  have h1 : openFee ≤ max openFee (D * (rHi - rBatch) * ((p.P - dt) / p.Y)) := le_max_left _ _
  have h2 : D * (rHi - rBatch) * ((p.P - dt) / p.Y) ≤
      max openFee (D * (rHi - rBatch) * ((p.P - dt) / p.Y)) := le_max_right _ _
  have hdiff := spikeCutTotalCost_sub_holdCost p D rHi rBatch dt
    (max openFee (D * (rHi - rBatch) * ((p.P - dt) / p.Y)))
  have _ := hdtP
  exact ⟨h1, by linarith⟩

theorem activation_delay_blocks_atomic_jit {tSubmit tArr deltaAct : ℝ}
    (hdelay : 0 < deltaAct) (hsame : tArr ≤ tSubmit) :
    tArr < tSubmit + deltaAct := by
  linarith

end LiquityV2
