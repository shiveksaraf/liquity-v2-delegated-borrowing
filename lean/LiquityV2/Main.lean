import LiquityV2.Defs
import LiquityV2.ReverseQueue
import LiquityV2.CooldownFees
import LiquityV2.DesignAStar
import LiquityV2.FlashLoanEscrow
import LiquityV2.DelegationAgency

namespace LiquityV2

open Finset BigOperators

theorem main_reverse_queue_ic_and_absorber
    {ι : Type*} {rMin r φ : ℝ} {lamRate : ℝ → ℝ} {τ rAlloc lamAlloc : ι → ℝ}
    (hanti : Antitone lamRate) (hic : IsIC φ τ rAlloc lamAlloc) :
    (∀ t, t ≤ φ → rMin < r → flowCost rMin t φ (lamRate rMin) < flowCost r t φ (lamRate r)) ∧
    (∀ i j, τ i < τ j → lamAlloc j ≤ lamAlloc i) ∧
    (∀ i j, φ < τ i → τ i < τ j → rAlloc i ≤ rAlloc j) ∧
    (∀ i j,
      (τ j - τ i) * lamAlloc j ≤
        indirectCost φ τ rAlloc lamAlloc j - indirectCost φ τ rAlloc lamAlloc i ∧
      indirectCost φ τ rAlloc lamAlloc j - indirectCost φ τ rAlloc lamAlloc i ≤
        (τ j - τ i) * lamAlloc i) :=
  ⟨fun _ ht hr => absorber_strictly_optimal_at_rMin hanti ht hr,
   fun _ _ hτ => ic_hazard_antitone hic hτ,
   fun _ _ hφ hτ => ic_rate_monotone hic hφ hτ,
   fun i j => ic_envelope_bounds hic i j⟩

theorem main_reverse_queue_equilibrium_and_ge
    {n : ℕ} {rMin φ A η : ℝ} {d τ lam : Fin n → ℝ} {ν : ℝ → ℝ}
    (hd : ∀ i, 0 ≤ d i) (hτ : Monotone τ) (hφ : ∀ i, φ < τ i)
    (hlam_strict : StrictAnti lam)
    (hA : 0 < A) (hη : 0 < η)
    (hcont : Continuous ν) (hν_anti : Antitone ν) (hν_nn : ∀ x, 0 ≤ ν x) :
    IsIC φ τ (discreteEqRate rMin φ τ lam) lam ∧
    StrictMono (discreteEqRate rMin φ τ lam) ∧
    (∑ i : Fin n, d i) * (∑ i : Fin n, d i * (τ i - φ) * lam i) ≤
      (∑ i : Fin n, d i * (τ i - φ)) * (∑ i : Fin n, d i * lam i) ∧
    (∃! rStar : ℝ, rMin ≤ rStar ∧ rStar = rMin + A * ν (η * rStar)) :=
  ⟨discreteEqRate_isIC rMin φ hτ hlam_strict.antitone,
   discreteEqRate_strictMono rMin φ hφ hlam_strict,
   sorting_efficiency_weighted_chebyshev φ hd hτ hlam_strict.antitone,
   peg_defense_exists_unique hA hη hcont hν_anti hν_nn⟩

theorem main_gpv_identification {φ τ0 r' lam' : ℝ} {r lam : ℝ → ℝ}
    (hic : IsIC φ id r lam) (hr : HasDerivAt r r' τ0)
    (hlam : HasDerivAt lam lam' τ0) (hlam_neg : lam' < 0) :
    r' = (τ0 - φ) * (-lam') ∧ τ0 = φ + r' / (-lam') :=
  gpv_continuous_identification hic hr hlam hlam_neg

theorem main_prior_mechanisms_failure (p : ProtocolParams) {K : ℕ}
    (hK : 2 ≤ K) {D rbar rHi rLo dt dt0 : ℝ}
    (hD : 0 < D) (hrbar : 0 < rbar) (hdtP : dt < p.P) (hdt0 : dt0 < p.P)
    (hlt : rLo < rHi) (harb : rbar * p.P < (rHi - rLo) * (p.P - dt))
    (r : Fin (K + 1) → ℝ) (dtSeq : Fin K → ℝ)
    (hr : ∀ k : Fin K, r k.castSucc < r k.succ)
    (hdtSeq : ∀ k : Fin K, dtSeq k < p.P) :
    statusQuoFee p D (r 0) (r (Fin.last K)) rbar dt0 <
      ∑ k : Fin K, statusQuoFee p D (r k.castSucc) (r k.succ) rbar (dtSeq k) ∧
    spikeCutTotalCost p D rHi rLo dt (statusQuoFee p D rHi rLo rbar dt) <
      holdCost p D rHi p.P ∧
    spikeCutTotalCost p D rHi rLo dt (designAFee p D rHi rLo rbar dt) <
      holdCost p D rHi p.P :=
  ⟨statusQuo_violates_staircase_invariance p hK hD hrbar hdt0 r dtSeq hr hdtSeq,
   (statusQuo_spike_and_cut_arbitrage p hD hdtP hlt harb).1,
   (designA_spike_and_cut_failure p hD hdtP hlt harb).1⟩

theorem main_designAStar_security_and_uniqueness (p : ProtocolParams) :
    SatisfiesCooldownConvention p (designAStarFee p) ∧
    SatisfiesA1 p (designAStarFee p) ∧
    SatisfiesA2Strict p (designAStarFee p) ∧
    SatisfiesA3 p (designAStarFee p) ∧
    SatisfiesA4 (designAStarFee p) ∧
    HasRightNoOpContinuity p (designAStarFee p) ∧
    (∀ Φ, SatisfiesCooldownConvention p Φ → SatisfiesA1 p Φ → SatisfiesA2Strict p Φ →
      SatisfiesA3 p Φ → HasRightNoOpContinuity p Φ →
      ∀ D r0 r1 dt, 0 ≤ D → 0 ≤ dt → designAStarFee p D r0 r1 dt ≤ Φ D r0 r1 dt) :=
  ⟨designAStar_satisfies_cooldown_convention p,
   designAStar_satisfies_A1 p,
   designAStar_satisfies_A2Strict p,
   designAStar_satisfies_A3 p,
   designAStar_satisfies_A4 p,
   designAStar_has_right_noop_continuity p,
   fun Φ h0 h1 h2s h3 hcont =>
     (designAStar_global_lower_bound_from_strict_micro_hikes p Φ h0 h1 h2s h3 hcont).2⟩

theorem main_designAStar_evm_uint256_bounds {K : ℕ} (hK : 1 ≤ K)
    (debt D1 D2 rHi rLo dt dt0 : Nat)
    (r : Fin (K + 1) → Nat) (dtSeq : Fin K → Nat)
    (hr : ∀ k : Fin K, r k.castSucc ≤ r k.succ)
    (hdtSeq : ∀ k : Fin K, dtSeq k < UPFRONT_INTEREST_PERIOD)
    (hdt : dt < UPFRONT_INTEREST_PERIOD)
    (hdt0 : dt0 < UPFRONT_INTEREST_PERIOD)
    (hlt : rLo < rHi)
    (hD_safe : debt ≤ 7658 * 10 ^ 49)
    (hr_safe : rHi ≤ MAX_ANNUAL_INTEREST_RATE) :
    (∑ k : Fin K, designAStarFeeNat debt (r k.castSucc) (r k.succ) (dtSeq k)) ≤
      designAStarFeeNat debt (r 0) (r (Fin.last K)) dt0 ∧
    designAStarFeeNat debt (r 0) (r (Fin.last K)) dt0 ≤
      (∑ k : Fin K, designAStarFeeNat debt (r k.castSucc) (r k.succ) (dtSeq k)) + (K - 1) ∧
    calcInterestNat (debt * rHi) UPFRONT_INTEREST_PERIOD ≤
      calcInterestNat (debt * rHi) dt +
      designAStarFeeNat debt rHi rLo dt +
      calcInterestNat (debt * rLo) (UPFRONT_INTEREST_PERIOD - dt) + 2 ∧
    calcInterestNat (debt * rHi) UPFRONT_INTEREST_PERIOD ≤
      calcInterestNat (debt * rHi) dt +
      designAStarFeeCeilPlusOneNat debt rHi rLo dt +
      calcInterestNat (debt * rLo) (UPFRONT_INTEREST_PERIOD - dt) ∧
    designAStarFeeNat (D1 + D2) rHi rLo dt ≤
      designAStarFeeNat D1 rHi rLo dt + designAStarFeeNat D2 rHi rLo dt + 1 ∧
    debt * rHi * UPFRONT_INTEREST_PERIOD < 2 ^ 256 := by
  have hst := designAStarFeeNat_staircase_floor_bound hK debt dt0 r dtSeq hr hdtSeq hdt0
  have hcut := designAStarFeeNat_cut_floor_bound debt rHi rLo dt hdt hlt
  have hzero := designAStarFeeCeilPlusOneNat_zero_total_shortfall debt rHi rLo dt hdt hlt
  have hsyb := designAStarFeeNat_sybil_bound D1 D2 rHi rLo dt
  have hovf := calcInterestNat_no_overflow debt rHi UPFRONT_INTEREST_PERIOD hD_safe hr_safe le_rfl
  exact ⟨hst.1, hst.2, hcut, hzero, hsyb.2, hovf⟩

theorem main_flash_loan_impossibility_and_designD (p : ProtocolParams)
    (Φ_inplace : ℝ → ℝ → ℝ → ℝ → ℝ)
    {s : DesignDState} {D rHi rLo dt t rnew Dcurr openFee fFlash gTx : ℝ}
    (hD : 0 ≤ D) (hdtP : dt ≤ p.P) (hrLo : p.rMin ≤ rLo)
    (hopen : 0 ≤ openFee) (hflash : 0 ≤ fFlash) (hgas : 0 ≤ gTx)
    (harb : openFee + fFlash * D + gTx < D * (rHi - rLo) * ((p.P - dt) / p.Y))
    (hinv : DesignDCoverageInvariant p s)
    (ht0 : s.lastUpdateTime ≤ t) (ht1 : t ≤ s.vestEndTime)
    (hrnew : p.rMin ≤ rnew) (hrlt : rnew < s.rate)
    (hcomp : s.bondedPrincipal ≤ Dcurr) :
    flashLoanReopenCost p D rHi rLo dt openFee fFlash gTx < holdCost p D rHi p.P ∧
    holdCost p D rHi p.P + openFee + fFlash * D + gTx ≤
      designDFlashLoanReopenCost p D rHi rLo dt openFee fFlash gTx ∧
    designDUnvested p (designDBond p D rHi p.rMin) p.P = 0 ∧
    0 ≤ designDPureCutForfeit p s t rnew ∧
    designDPureCutForfeit p s t rnew ≤ (designDSettleState s t).unvestedBond ∧
    DesignDCoverageInvariant p (designDPureCutState p s t rnew) := by
  have hcut := designD_pure_cut_zero_underflow_and_invariant p hinv ht0 ht1 hrnew hrlt hcomp
  exact ⟨(flash_loan_reopen_impossibility p Φ_inplace harb).1,
   (designD_blocks_flash_loan_reopen p hD hdtP hrLo hopen hflash hgas).2.1,
   (designD_honest_hold_zero_extra_cost p le_rfl).2.1,
   hcut.1, hcut.2.1, hcut.2.2.2⟩

theorem main_delegation_agency_alignment (p : ProtocolParams)
    {n : ℕ} (hn : 1 ≤ n)
    {D Φ m_j cB α0 β Δlam Δr K gPerD τ Δ1 Δ2 ε D0 rbar r0 : ℝ}
    (hΦ : 0 < Φ) (hm : 0 < m_j)
    (hα0 : α0 < 1) (hK : 0 < K)
    (hβ : betaStarPure α0 K gPerD ≤ β)
    (hdom : borrowerPrematureHikeGain p cB Δlam Δr K τ ≤ 0)
    (hε : 0 < ε) (hΔ1 : ε < Δ1) (hΔ2 : ε < Δ2)
    (hD0 : 0 < D0) (hrbar : 0 < rbar) :
    D * m_j < (D + Φ) * m_j ∧
    managerPrematureHikeGain p cB 1 (alphaEff α0 β) Δlam Δr K gPerD τ ≤ 0 ∧
    ((¬ ∃ k1 k2 : ℕ, ∃ b : Bool, IsDiscreteLIFOPureNash Δ1 Δ2 ε k1 k2 b) ↔
      (2 * ε < Δ1 ∧ 2 * ε < Δ2)) ∧
    rbar / (2 * ε) <
      (((2 * n : ℕ) : ℝ) * D0 * rbar * (p.P / p.Y)) /
        (D0 * (r0 + ((2 * n - 1 : ℕ) : ℝ) * ε - r0) * (p.P / p.Y) +
         D0 * (r0 + ((2 * n : ℕ) : ℝ) * ε - r0) * (p.P / p.Y)) :=
  ⟨(statusQuo_fee_base_expansion hΦ hm).1,
   copay_eliminates_dominated_hikes p hα0 hK hβ hdom,
   leapfrogging_discrete_grid_no_pure_nash_iff hε hΔ1 hΔ2,
   (designAStar_collapses_leapfrog_fee_exact p hn hD0 hrbar hε).2⟩

end LiquityV2
