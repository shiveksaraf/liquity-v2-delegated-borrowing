import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace LiquityV2

def ONE_YEAR : Nat := 31536000

def UPFRONT_INTEREST_PERIOD : Nat := 604800

def WAD : Nat := 1000000000000000000

def MIN_ANNUAL_INTEREST_RATE : Nat := 5000000000000000

def MAX_ANNUAL_INTEREST_RATE : Nat := 2500000000000000000

def MIN_DEBT : Nat := 2000000000000000000000

def MIN_INTEREST_RATE_CHANGE_PERIOD : Nat := 3600

def REDEMPTION_FEE_FLOOR : Nat := 5000000000000000

def SP_YIELD_SPLIT : Nat := 750000000000000000

def INTEREST_DENOM : Nat := ONE_YEAR * WAD

lemma interest_denom_pos : 0 < INTEREST_DENOM := by
  decide

def calcInterestNat (weightedDebt period : Nat) : Nat :=
  weightedDebt * period / ONE_YEAR / WAD

def calcInterestCeilNat (weightedDebt period : Nat) : Nat :=
  (weightedDebt * period + INTEREST_DENOM - 1) / INTEREST_DENOM

def calcInterestCeilSafeNat (weightedDebt period : Nat) : Nat :=
  let num := weightedDebt * period
  if num = 0 then 0 else (num - 1) / INTEREST_DENOM + 1

theorem calcInterestCeilSafeNat_eq_calcInterestCeilNat (weightedDebt period : Nat) :
    calcInterestCeilSafeNat weightedDebt period = calcInterestCeilNat weightedDebt period := by
  unfold calcInterestCeilSafeNat calcInterestCeilNat
  dsimp only
  set x := weightedDebt * period
  set d := INTEREST_DENOM
  have hd : 0 < d := interest_denom_pos
  by_cases hx : x = 0
  · rw [hx]
    simp only [↓reduceIte, zero_add]
    exact (Nat.div_eq_of_lt (by omega)).symm
  · simp only [hx, ↓reduceIte]
    have hrew : x + d - 1 = (x - 1) + d := by omega
    rw [hrew, Nat.add_div_right _ hd]

theorem calcInterestNat_eq_single_div (weightedDebt period : Nat) :
    calcInterestNat weightedDebt period = (weightedDebt * period) / INTEREST_DENOM := by
  unfold calcInterestNat INTEREST_DENOM
  exact Nat.div_div_eq_div_mul (weightedDebt * period) ONE_YEAR WAD

theorem calcInterestNat_mul_le (weightedDebt period : Nat) :
    calcInterestNat weightedDebt period * INTEREST_DENOM ≤ weightedDebt * period := by
  rw [calcInterestNat_eq_single_div]
  exact Nat.div_mul_le_self (weightedDebt * period) INTEREST_DENOM

theorem calcInterestNat_lt_succ (weightedDebt period : Nat) :
    weightedDebt * period < (calcInterestNat weightedDebt period + 1) * INTEREST_DENOM := by
  rw [calcInterestNat_eq_single_div]
  have hmod : weightedDebt * period % INTEREST_DENOM < INTEREST_DENOM :=
    Nat.mod_lt _ interest_denom_pos
  have hdiv : INTEREST_DENOM * (weightedDebt * period / INTEREST_DENOM) +
      weightedDebt * period % INTEREST_DENOM = weightedDebt * period :=
    Nat.div_add_mod (weightedDebt * period) INTEREST_DENOM
  have hrhs : (weightedDebt * period / INTEREST_DENOM + 1) * INTEREST_DENOM =
      INTEREST_DENOM * (weightedDebt * period / INTEREST_DENOM) + INTEREST_DENOM := by
    ring
  omega

theorem mul_le_calcInterestCeilNat_mul (weightedDebt period : Nat) :
    weightedDebt * period ≤ calcInterestCeilNat weightedDebt period * INTEREST_DENOM := by
  unfold calcInterestCeilNat
  set x := weightedDebt * period
  set d := INTEREST_DENOM
  have hd : 0 < d := interest_denom_pos
  have hmod : (x + d - 1) % d < d := Nat.mod_lt _ hd
  have hdiv : d * ((x + d - 1) / d) + (x + d - 1) % d = x + d - 1 :=
    Nat.div_add_mod (x + d - 1) d
  have hcomm : ((x + d - 1) / d) * d = d * ((x + d - 1) / d) := Nat.mul_comm _ _
  omega

theorem calcInterestCeilNat_sub_one_lt (weightedDebt period : Nat)
    (hx : 0 < weightedDebt * period) :
    (calcInterestCeilNat weightedDebt period - 1) * INTEREST_DENOM < weightedDebt * period := by
  unfold calcInterestCeilNat
  set x := weightedDebt * period
  set d := INTEREST_DENOM
  have hd : 0 < d := interest_denom_pos
  have hpos : 1 ≤ (x + d - 1) / d := by
    rw [Nat.le_div_iff_mul_le hd]
    omega
  have hle : ((x + d - 1) / d) * d ≤ x + d - 1 := Nat.div_mul_le_self (x + d - 1) d
  have hmul : ((x + d - 1) / d - 1) * d + d = ((x + d - 1) / d) * d := by
    have : (x + d - 1) / d - 1 + 1 = (x + d - 1) / d := Nat.sub_add_cancel hpos
    calc ((x + d - 1) / d - 1) * d + d
        = ((x + d - 1) / d - 1 + 1) * d := by ring
      _ = ((x + d - 1) / d) * d := by rw [this]
  omega

theorem calcInterestNat_no_overflow (debt rate period : Nat)
    (hD : debt ≤ 7658 * 10 ^ 49)
    (hr : rate ≤ MAX_ANNUAL_INTEREST_RATE)
    (hp : period ≤ UPFRONT_INTEREST_PERIOD) :
    debt * rate * period < 2 ^ 256 := by
  have h1 : debt * rate ≤ (7658 * 10 ^ 49) * MAX_ANNUAL_INTEREST_RATE :=
    Nat.mul_le_mul hD hr
  have h2 : debt * rate * period ≤ (7658 * 10 ^ 49) * MAX_ANNUAL_INTEREST_RATE * UPFRONT_INTEREST_PERIOD :=
    Nat.mul_le_mul h1 hp
  have h3 : (7658 * 10 ^ 49) * MAX_ANNUAL_INTEREST_RATE * UPFRONT_INTEREST_PERIOD < 2 ^ 256 := by
    norm_num [MAX_ANNUAL_INTEREST_RATE, UPFRONT_INTEREST_PERIOD]
  exact Nat.lt_of_le_of_lt h2 h3

def statusQuoFeeNat (debt r0 r1 avgRate dt : Nat) : Nat :=
  if dt ≥ UPFRONT_INTEREST_PERIOD ∨ r1 = r0 then 0
  else calcInterestNat (debt * avgRate) UPFRONT_INTEREST_PERIOD

def designAFeeNat (debt r0 r1 avgRate dt : Nat) : Nat :=
  if dt ≥ UPFRONT_INTEREST_PERIOD ∨ r1 = r0 then 0
  else if r0 < r1 then calcInterestNat (debt * (r1 - r0)) UPFRONT_INTEREST_PERIOD
  else calcInterestNat (debt * avgRate) UPFRONT_INTEREST_PERIOD

def designAStarFeeNat (debt r0 r1 dt : Nat) : Nat :=
  if dt ≥ UPFRONT_INTEREST_PERIOD ∨ r1 = r0 then 0
  else if r0 < r1 then calcInterestNat (debt * (r1 - r0)) UPFRONT_INTEREST_PERIOD
  else calcInterestNat (debt * (r0 - r1)) (UPFRONT_INTEREST_PERIOD - dt)

def designAStarFeeCeilCutNat (debt r0 r1 dt : Nat) : Nat :=
  if dt ≥ UPFRONT_INTEREST_PERIOD ∨ r1 = r0 then 0
  else if r0 < r1 then calcInterestNat (debt * (r1 - r0)) UPFRONT_INTEREST_PERIOD
  else calcInterestCeilNat (debt * (r0 - r1)) (UPFRONT_INTEREST_PERIOD - dt)

def designAStarFeeCeilPlusOneNat (debt r0 r1 dt : Nat) : Nat :=
  if dt ≥ UPFRONT_INTEREST_PERIOD ∨ r1 = r0 then 0
  else if r0 < r1 then calcInterestNat (debt * (r1 - r0)) UPFRONT_INTEREST_PERIOD
  else
    let base := calcInterestCeilNat (debt * (r0 - r1)) (UPFRONT_INTEREST_PERIOD - dt)
    if base = 0 then 0 else base + 1

structure ProtocolParams where

  P : ℝ

  Y : ℝ

  rMin : ℝ

  rMax : ℝ

  phi : ℝ
  hP : 0 < P
  hY : 0 < Y
  hrMin : 0 < rMin
  hrRange : rMin < rMax
  hphi : 0 ≤ phi

noncomputable def mainnetParams : ProtocolParams where
  P := 604800
  Y := 31536000
  rMin := 5 / 1000
  rMax := 25 / 10
  phi := 5 / 1000
  hP := by norm_num
  hY := by norm_num
  hrMin := by norm_num
  hrRange := by norm_num
  hphi := by norm_num

noncomputable def holdCost (p : ProtocolParams) (D r t : ℝ) : ℝ :=
  D * r * (t / p.Y)

noncomputable def statusQuoFee (p : ProtocolParams) (D r0 r1 rbar dt : ℝ) : ℝ :=
  if dt ≥ p.P ∨ r1 = r0 then 0
  else D * rbar * (p.P / p.Y)

noncomputable def designAFee (p : ProtocolParams) (D r0 r1 rbar dt : ℝ) : ℝ :=
  if dt ≥ p.P ∨ r1 = r0 then 0
  else if r0 < r1 then D * (r1 - r0) * (p.P / p.Y)
  else D * rbar * (p.P / p.Y)

noncomputable def designAStarFee (p : ProtocolParams) (D r0 r1 dt : ℝ) : ℝ :=
  if dt ≥ p.P ∨ r1 = r0 then 0
  else if r0 < r1 then D * (r1 - r0) * (p.P / p.Y)
  else D * (r0 - r1) * ((p.P - dt) / p.Y)

noncomputable def designCFee (p : ProtocolParams) (D r0 r1 rbar dt : ℝ) : ℝ :=
  if dt ≥ p.P ∨ r1 = r0 then 0
  else D * rbar * (dt / p.Y)

noncomputable def spikeCutTotalCost (p : ProtocolParams) (D r0 r1 dt fee : ℝ) : ℝ :=
  holdCost p D r0 dt + fee + holdCost p D r1 (p.P - dt)

lemma holdCost_add_time (p : ProtocolParams) (D r t1 t2 : ℝ) :
    holdCost p D r t1 + holdCost p D r t2 = holdCost p D r (t1 + t2) := by
  unfold holdCost
  ring

lemma spikeCutTotalCost_sub_holdCost (p : ProtocolParams) (D r0 r1 dt fee : ℝ) :
    spikeCutTotalCost p D r0 r1 dt fee - holdCost p D r0 p.P =
      fee - D * (r0 - r1) * ((p.P - dt) / p.Y) := by
  unfold spikeCutTotalCost holdCost
  ring

end LiquityV2
