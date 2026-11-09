import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import LiquityV2.Defs
import LiquityV2.CooldownFees

namespace LiquityV2

open Finset BigOperators Filter Topology

theorem designAStar_nonneg (p : ProtocolParams) {D r0 r1 dt : ℝ} (hD : 0 ≤ D) :
    0 ≤ designAStarFee p D r0 r1 dt := by
  unfold designAStarFee
  split_ifs with h1 h2
  · exact le_rfl
  · have hdiff : 0 ≤ r1 - r0 := sub_nonneg.mpr (le_of_lt h2)
    have hPY : 0 ≤ p.P / p.Y := div_nonneg (le_of_lt p.hP) (le_of_lt p.hY)
    exact mul_nonneg (mul_nonneg hD hdiff) hPY
  · push Not at h1 h2
    have hdiff : 0 ≤ r0 - r1 := sub_nonneg.mpr h2
    have hrem : 0 ≤ (p.P - dt) / p.Y := div_nonneg (sub_nonneg.mpr (le_of_lt h1.1)) (le_of_lt p.hY)
    exact mul_nonneg (mul_nonneg hD hdiff) hrem

theorem designAStar_satisfies_cooldown_convention (p : ProtocolParams) :
    SatisfiesCooldownConvention p (designAStarFee p) := by
  intro D r0 r1 dt _ h
  unfold designAStarFee
  simp [h]

theorem designAStar_satisfies_A1Strong (p : ProtocolParams) :
    SatisfiesA1Strong p (designAStarFee p) := by
  intro D r0 r1 dt _ _ hdtP hlt
  unfold designAStarFee
  have hnot : ¬ (dt ≥ p.P ∨ r1 = r0) := by
    push Not
    exact ⟨hdtP, ne_of_gt hlt⟩
  simp [hnot, hlt]

theorem designAStar_satisfies_A1 (p : ProtocolParams) :
    SatisfiesA1 p (designAStarFee p) := by
  intro D r0 r1 dt hD hdt0 hdtP hlt
  have hstrong := designAStar_satisfies_A1Strong p D r0 r1 dt hD hdt0 hdtP hlt
  have hdiff : 0 ≤ D * (r1 - r0) := mul_nonneg hD (sub_nonneg.mpr (le_of_lt hlt))
  have hdiv : dt / p.Y ≤ p.P / p.Y := div_le_div_of_nonneg_right (le_of_lt hdtP) (le_of_lt p.hY)
  have hmul : D * (r1 - r0) * (dt / p.Y) ≤ D * (r1 - r0) * (p.P / p.Y) :=
    mul_le_mul_of_nonneg_left hdiv hdiff
  linarith

theorem designAStar_satisfies_A2 (p : ProtocolParams) :
    SatisfiesA2 p (designAStarFee p) := by
  intro D r0 r1 r2 dt1 dt2 _ h1 h2 hsum hr01 hr12
  have hdt1P : dt1 < p.P := by linarith
  have hdt2P : dt2 < p.P := by linarith
  have heval : ∀ x y t, t < p.P → x ≤ y →
      designAStarFee p D x y t = D * (y - x) * (p.P / p.Y) := by
    intro x y t htP hxy
    by_cases heq : y = x
    · unfold designAStarFee
      simp [heq]
    · have hlt : x < y := lt_of_le_of_ne hxy (Ne.symm heq)
      unfold designAStarFee
      have hnot : ¬ (t ≥ p.P ∨ y = x) := by push Not; exact ⟨htP, heq⟩
      simp [hnot, hlt]
  rw [heval r0 r1 dt1 hdt1P hr01, heval r1 r2 dt2 hdt2P hr12,
      heval r0 r2 (dt1 + dt2) hsum (le_trans hr01 hr12)]
  ring

theorem designAStar_satisfies_A2Strict (p : ProtocolParams) :
    SatisfiesA2Strict p (designAStarFee p) := by
  intro D r0 r1 r2 dt1 dt2 hD h1 h2 hsum hr01 hr12
  exact designAStar_satisfies_A2 p D r0 r1 r2 dt1 dt2 hD h1 h2 hsum (le_of_lt hr01) (le_of_lt hr12)

theorem designAStar_spike_and_cut_exact (p : ProtocolParams)
    {D r0 r1 dt : ℝ} (hdtP : dt < p.P) (hlt : r1 < r0) :
    spikeCutTotalCost p D r0 r1 dt (designAStarFee p D r0 r1 dt) = holdCost p D r0 p.P := by
  have hfee : designAStarFee p D r0 r1 dt = D * (r0 - r1) * ((p.P - dt) / p.Y) := by
    unfold designAStarFee
    have hnot1 : ¬ (dt ≥ p.P ∨ r1 = r0) := by
      push Not
      exact ⟨hdtP, ne_of_lt hlt⟩
    have hnot2 : ¬ (r0 < r1) := not_lt.mpr (le_of_lt hlt)
    simp [hnot1, hnot2]
  have hdiff := spikeCutTotalCost_sub_holdCost p D r0 r1 dt (designAStarFee p D r0 r1 dt)
  rw [hfee] at hdiff ⊢
  linarith

theorem designAStar_satisfies_A3 (p : ProtocolParams) :
    SatisfiesA3 p (designAStarFee p) := by
  intro D r0 r1 dt _ _ hdtP hlt
  rw [designAStar_spike_and_cut_exact p hdtP hlt]

theorem designAStar_staircase_additive_K (p : ProtocolParams) {K : ℕ}
    (D dt0 : ℝ) (r : Fin (K + 1) → ℝ) (dt : Fin K → ℝ)
    (hr : ∀ k : Fin K, r k.castSucc ≤ r k.succ)
    (hdt : ∀ k : Fin K, dt k < p.P)
    (hdt0 : dt0 < p.P) :
    (∑ k : Fin K, designAStarFee p D (r k.castSucc) (r k.succ) (dt k)) =
      designAStarFee p D (r 0) (r (Fin.last K)) dt0 := by
  have hstep : ∀ k : Fin K,
      designAStarFee p D (r k.castSucc) (r k.succ) (dt k) =
        D * (r k.succ - r k.castSucc) * (p.P / p.Y) := by
    intro k
    by_cases heq : r k.succ = r k.castSucc
    · unfold designAStarFee
      simp [heq]
    · have hlt : r k.castSucc < r k.succ := lt_of_le_of_ne (hr k) (Ne.symm heq)
      unfold designAStarFee
      have hnot : ¬ (dt k ≥ p.P ∨ r k.succ = r k.castSucc) := by
        push Not
        exact ⟨hdt k, heq⟩
      simp [hnot, hlt]
  simp_rw [hstep]
  have htele : ∀ (m : ℕ) (f : Fin (m + 1) → ℝ),
      (∑ k : Fin m, (f k.succ - f k.castSucc)) = f (Fin.last m) - f 0 := by
    intro m
    induction m with
    | zero => intro f; simp
    | succ j ih =>
      intro f
      rw [Fin.sum_univ_castSucc]
      have hcast_eq : ∀ k : Fin j, (k.castSucc : Fin (j + 1)).succ = k.succ.castSucc := by
        intro k; ext; simp
      simp_rw [hcast_eq]
      rw [ih (fun i => f i.castSucc)]
      have hlast_succ : (Fin.last j).succ = Fin.last (j + 1) := by ext; simp
      rw [hlast_succ, Fin.castSucc_zero]
      ring
  have hsum_eq :
      (∑ k : Fin K, D * (r k.succ - r k.castSucc) * (p.P / p.Y)) =
        D * (r (Fin.last K) - r 0) * (p.P / p.Y) := by
    calc (∑ k : Fin K, D * (r k.succ - r k.castSucc) * (p.P / p.Y))
        = ∑ k : Fin K, (D * (p.P / p.Y)) * (r k.succ - r k.castSucc) := by
          apply Finset.sum_congr rfl; intro k _; ring
      _ = (D * (p.P / p.Y)) * (∑ k : Fin K, (r k.succ - r k.castSucc)) := by
          rw [← Finset.mul_sum]
      _ = (D * (p.P / p.Y)) * (r (Fin.last K) - r 0) := by rw [htele K r]
      _ = D * (r (Fin.last K) - r 0) * (p.P / p.Y) := by ring
  rw [hsum_eq]
  have hmono : r 0 ≤ r (Fin.last K) := by
    have hmon : Monotone r := Fin.monotone_iff_le_succ.mpr hr
    exact hmon (Fin.zero_le _)
  by_cases heq : r (Fin.last K) = r 0
  · unfold designAStarFee
    simp [heq]
  · have hlt : r 0 < r (Fin.last K) := lt_of_le_of_ne hmono (Ne.symm heq)
    unfold designAStarFee
    have hnot : ¬ (dt0 ≥ p.P ∨ r (Fin.last K) = r 0) := by
      push Not
      exact ⟨hdt0, heq⟩
    simp [hnot, hlt]

theorem designAStar_satisfies_A4 (p : ProtocolParams) :
    SatisfiesA4 (designAStarFee p) := by
  constructor
  · intro lam D r0 r1 dt _ _
    unfold designAStarFee
    split_ifs <;> ring
  · intro D1 D2 r0 r1 dt _ _
    unfold designAStarFee
    split_ifs <;> ring

theorem designAStar_multi_cut_superadditive (p : ProtocolParams)
    {D r0 r1 r2 dt1 dt2 : ℝ} (hD : 0 ≤ D)
    (hdt1 : 0 < dt1) (hdt2 : 0 < dt2) (hsum : dt1 + dt2 < p.P)
    (h01 : r1 < r0) (h12 : r2 < r1) :
    let totalCost :=
      holdCost p D r0 dt1 +
      designAStarFee p D r0 r1 dt1 +
      holdCost p D r1 dt2 +
      designAStarFee p D r1 r2 dt2 +
      holdCost p D r2 (p.P - dt1 - dt2)
    totalCost - holdCost p D r0 p.P = D * (r1 - r2) * (dt1 / p.Y) ∧
    holdCost p D r0 p.P ≤ totalCost := by
  dsimp only
  have hdt1P : dt1 < p.P := by linarith
  have hdt2P : dt2 < p.P := by linarith
  have hf1 : designAStarFee p D r0 r1 dt1 = D * (r0 - r1) * ((p.P - dt1) / p.Y) := by
    unfold designAStarFee
    have hnot1 : ¬ (dt1 ≥ p.P ∨ r1 = r0) := by push Not; exact ⟨hdt1P, ne_of_lt h01⟩
    have hnot2 : ¬ (r0 < r1) := not_lt.mpr (le_of_lt h01)
    simp [hnot1, hnot2]
  have hf2 : designAStarFee p D r1 r2 dt2 = D * (r1 - r2) * ((p.P - dt2) / p.Y) := by
    unfold designAStarFee
    have hnot1 : ¬ (dt2 ≥ p.P ∨ r2 = r1) := by push Not; exact ⟨hdt2P, ne_of_lt h12⟩
    have hnot2 : ¬ (r1 < r2) := not_lt.mpr (le_of_lt h12)
    simp [hnot1, hnot2]
  have hid :
      (holdCost p D r0 dt1 + designAStarFee p D r0 r1 dt1 +
       holdCost p D r1 dt2 + designAStarFee p D r1 r2 dt2 +
       holdCost p D r2 (p.P - dt1 - dt2)) - holdCost p D r0 p.P =
      D * (r1 - r2) * (dt1 / p.Y) := by
    rw [hf1, hf2]
    unfold holdCost
    ring
  have hnn : 0 ≤ D * (r1 - r2) * (dt1 / p.Y) :=
    mul_nonneg (mul_nonneg hD (sub_nonneg.mpr (le_of_lt h12)))
      (div_nonneg (le_of_lt hdt1) (le_of_lt p.hY))
  exact ⟨hid, by linarith⟩

theorem designAStar_oscillation_dominated (p : ProtocolParams)
    {D r0 r1 dt1 dt2 : ℝ} (hD : 0 < D)
    (hdt1 : 0 < dt1) (hdt2 : 0 < dt2) (hsum : dt1 + dt2 < p.P)
    (hlt : r1 < r0) :
    let totalCost :=
      holdCost p D r0 dt1 +
      designAStarFee p D r0 r1 dt1 +
      holdCost p D r1 dt2 +
      designAStarFee p D r1 r0 dt2 +
      holdCost p D r0 (p.P - dt1 - dt2)
    holdCost p D r0 p.P < totalCost := by
  dsimp only
  have hdt1P : dt1 < p.P := by linarith
  have hdt2P : dt2 < p.P := by linarith
  have hf1 : designAStarFee p D r0 r1 dt1 = D * (r0 - r1) * ((p.P - dt1) / p.Y) := by
    unfold designAStarFee
    have hnot1 : ¬ (dt1 ≥ p.P ∨ r1 = r0) := by push Not; exact ⟨hdt1P, ne_of_lt hlt⟩
    have hnot2 : ¬ (r0 < r1) := not_lt.mpr (le_of_lt hlt)
    simp [hnot1, hnot2]
  have hf2 : designAStarFee p D r1 r0 dt2 = D * (r0 - r1) * (p.P / p.Y) := by
    unfold designAStarFee
    have hnot1 : ¬ (dt2 ≥ p.P ∨ r0 = r1) := by push Not; exact ⟨hdt2P, ne_of_gt hlt⟩
    simp [hnot1, hlt]
  have hid :
      (holdCost p D r0 dt1 + designAStarFee p D r0 r1 dt1 +
       holdCost p D r1 dt2 + designAStarFee p D r1 r0 dt2 +
       holdCost p D r0 (p.P - dt1 - dt2)) - holdCost p D r0 p.P =
      D * (r0 - r1) * ((2 * p.P - dt1 - dt2) / p.Y) := by
    rw [hf1, hf2]
    unfold holdCost
    ring
  have hpos : 0 < D * (r0 - r1) * ((2 * p.P - dt1 - dt2) / p.Y) := by
    have hdiff : 0 < r0 - r1 := sub_pos.mpr hlt
    have htime : 0 < 2 * p.P - dt1 - dt2 := by linarith [p.hP]
    exact mul_pos (mul_pos hD hdiff) (div_pos htime p.hY)
  linarith

theorem designAStar_pointwise_lower_bound (p : ProtocolParams)
    (Φ : ℝ → ℝ → ℝ → ℝ → ℝ)
    (h0 : SatisfiesCooldownConvention p Φ) (h1s : SatisfiesA1Strong p Φ) (h3 : SatisfiesA3 p Φ) :
    ∀ D r0 r1 dt, 0 ≤ D → 0 ≤ dt → designAStarFee p D r0 r1 dt ≤ Φ D r0 r1 dt := by
  intro D r0 r1 dt hD hdt0
  by_cases hexp : dt ≥ p.P ∨ r1 = r0
  · rw [designAStar_satisfies_cooldown_convention p D r0 r1 dt hD hexp, h0 D r0 r1 dt hD hexp]
  · push Not at hexp
    rcases lt_trichotomy r0 r1 with hup | heq | hdn
    · have hstar : designAStarFee p D r0 r1 dt = D * (r1 - r0) * (p.P / p.Y) := by
        unfold designAStarFee
        have hnot : ¬ (dt ≥ p.P ∨ r1 = r0) := by push Not; exact hexp
        simp [hnot, hup]
      rw [hstar]
      exact h1s D r0 r1 dt hD hdt0 hexp.1 hup
    · exact absurd heq.symm hexp.2
    · have hstar : designAStarFee p D r0 r1 dt = D * (r0 - r1) * ((p.P - dt) / p.Y) := by
        unfold designAStarFee
        have hnot1 : ¬ (dt ≥ p.P ∨ r1 = r0) := by push Not; exact hexp
        have hnot2 : ¬ (r0 < r1) := not_lt.mpr (le_of_lt hdn)
        simp [hnot1, hnot2]
      rw [hstar]
      exact (satisfiesA3_iff_fee_floor p Φ).mp h3 D r0 r1 dt hD hdt0 hexp.1 hdn

def HasRightNoOpContinuity (p : ProtocolParams) (Φ : ℝ → ℝ → ℝ → ℝ → ℝ) : Prop :=
  (∀ D r0 t1, 0 ≤ D → 0 ≤ t1 → t1 < p.P →
    Tendsto (fun y => Φ D r0 y t1) (𝓝[>] r0) (𝓝 0)) ∧
  (∀ D r0 r1 t2, 0 ≤ D → r0 < r1 → 0 ≤ t2 → t2 < p.P →
    Tendsto (fun y => Φ D y r1 t2) (𝓝[>] r0) (𝓝 (Φ D r0 r1 t2)))

theorem designAStar_has_right_noop_continuity (p : ProtocolParams) :
    HasRightNoOpContinuity p (designAStarFee p) := by
  constructor
  · intro D r0 t1 _ _ ht1P
    have hev : (fun y => designAStarFee p D r0 y t1) =ᶠ[𝓝[>] r0]
        (fun y => D * (y - r0) * (p.P / p.Y)) := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      have hygt : r0 < y := hy
      unfold designAStarFee
      have hnot : ¬ (t1 ≥ p.P ∨ y = r0) := by push Not; exact ⟨ht1P, ne_of_gt hygt⟩
      simp [hnot, hygt]
    rw [tendsto_congr' hev]
    have hcont : Continuous (fun y : ℝ => D * (y - r0) * (p.P / p.Y)) := by fun_prop
    have hlim : Tendsto (fun y : ℝ => D * (y - r0) * (p.P / p.Y)) (𝓝[>] r0)
        (𝓝 (D * (r0 - r0) * (p.P / p.Y))) :=
      (hcont.continuousAt (x := r0)).tendsto.mono_left nhdsWithin_le_nhds
    simpa using hlim
  · intro D r0 r1 t2 _ hr01 _ ht2P
    have hmem : Set.Ioo r0 r1 ∈ 𝓝[>] r0 :=
      inter_mem_nhdsWithin (Set.Ioi r0) (Iio_mem_nhds hr01)
    have hev : (fun y => designAStarFee p D y r1 t2) =ᶠ[𝓝[>] r0]
        (fun y => D * (r1 - y) * (p.P / p.Y)) := by
      filter_upwards [hmem] with y hy
      unfold designAStarFee
      have hnot : ¬ (t2 ≥ p.P ∨ r1 = y) := by push Not; exact ⟨ht2P, ne_of_gt hy.2⟩
      simp [hnot, hy.2]
    rw [tendsto_congr' hev]
    have hval : designAStarFee p D r0 r1 t2 = D * (r1 - r0) * (p.P / p.Y) := by
      unfold designAStarFee
      have hnot : ¬ (t2 ≥ p.P ∨ r1 = r0) := by push Not; exact ⟨ht2P, ne_of_gt hr01⟩
      simp [hnot, hr01]
    rw [hval]
    have hcont : Continuous (fun y : ℝ => D * (r1 - y) * (p.P / p.Y)) := by fun_prop
    exact hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds

lemma time_indep_A1_implies_A1Strong (p : ProtocolParams)
    (Φ : ℝ → ℝ → ℝ → ℝ → ℝ)
    (h1 : SatisfiesA1 p Φ)
    (htime_indep : ∀ D r0 r1 t1 t2, 0 ≤ D → r0 < r1 →
      0 ≤ t1 → t1 < p.P → 0 ≤ t2 → t2 < p.P →
      Φ D r0 r1 t1 = Φ D r0 r1 t2) :
    SatisfiesA1Strong p Φ := by
  intro D r0 r1 dt hD hdt0 hdtP hlt
  by_cases hD0 : D = 0
  · subst hD0
    have hw := h1 0 r0 r1 dt le_rfl hdt0 hdtP hlt
    simpa using hw
  · have hDpos : 0 < D := lt_of_le_of_ne hD (Ne.symm hD0)
    have hdiff : 0 < r1 - r0 := sub_pos.mpr hlt
    have hDr : 0 < D * (r1 - r0) := mul_pos hDpos hdiff
    by_contra hlt_phi
    push Not at hlt_phi
    have hphi_nn : 0 ≤ Φ D r0 r1 dt := by
      have hw := h1 D r0 r1 dt hD hdt0 hdtP hlt
      have hnn : 0 ≤ D * (r1 - r0) * (dt / p.Y) :=
        mul_nonneg (le_of_lt hDr) (div_nonneg hdt0 (le_of_lt p.hY))
      linarith
    let tStar : ℝ := p.Y * Φ D r0 r1 dt / (D * (r1 - r0))
    have htStar_lt : tStar < p.P := by
      dsimp only [tStar]
      rw [div_lt_iff₀ hDr]
      have hYne : p.Y ≠ 0 := ne_of_gt p.hY
      have hmul := mul_lt_mul_of_pos_left hlt_phi p.hY
      have hrhs : p.Y * (D * (r1 - r0) * (p.P / p.Y)) = p.P * (D * (r1 - r0)) := by
        field_simp [hYne]
      linarith
    have htStar_nn : 0 ≤ tStar :=
      div_nonneg (mul_nonneg (le_of_lt p.hY) hphi_nn) (le_of_lt hDr)
    let t' : ℝ := (tStar + p.P) / 2
    have ht'0 : 0 ≤ t' := by dsimp only [t']; linarith [p.hP]
    have ht'P : t' < p.P := by dsimp only [t']; linarith
    have htStar_lt_t' : tStar < t' := by dsimp only [t']; linarith
    have hconst := htime_indep D r0 r1 t' dt hD hlt ht'0 ht'P hdt0 hdtP
    have hweak := h1 D r0 r1 t' hD ht'0 ht'P hlt
    rw [hconst] at hweak
    have hgt : Φ D r0 r1 dt < D * (r1 - r0) * (t' / p.Y) := by
      have h1m : tStar * (D * (r1 - r0)) < t' * (D * (r1 - r0)) :=
        mul_lt_mul_of_pos_right htStar_lt_t' hDr
      have h2m : tStar * (D * (r1 - r0)) = p.Y * Φ D r0 r1 dt := by
        dsimp only [tStar]
        exact div_mul_cancel₀ _ (ne_of_gt hDr)
      have h3m : p.Y * Φ D r0 r1 dt < t' * (D * (r1 - r0)) := by linarith
      have h4m : Φ D r0 r1 dt < (t' * (D * (r1 - r0))) / p.Y := by
        rw [lt_div_iff₀ p.hY]; linarith
      have h5m : (t' * (D * (r1 - r0))) / p.Y = D * (r1 - r0) * (t' / p.Y) := by ring
      linarith
    linarith

theorem designAStar_global_lower_bound_from_strict_micro_hikes (p : ProtocolParams)
    (Φ : ℝ → ℝ → ℝ → ℝ → ℝ)
    (h0 : SatisfiesCooldownConvention p Φ)
    (h1 : SatisfiesA1 p Φ)
    (h2s : SatisfiesA2Strict p Φ)
    (h3 : SatisfiesA3 p Φ)
    (hcont : HasRightNoOpContinuity p Φ) :
    (∀ D r0 r1 t1 t2, 0 ≤ D → r0 < r1 → 0 ≤ t1 → t1 < p.P → 0 ≤ t2 → t2 < p.P →
      Φ D r0 r1 t1 = Φ D r0 r1 t2) ∧
    (∀ D r0 r1 dt, 0 ≤ D → 0 ≤ dt → designAStarFee p D r0 r1 dt ≤ Φ D r0 r1 dt) := by
  have hle_eq : ∀ D r0 r1 a b, 0 ≤ D → r0 < r1 → 0 ≤ a → a ≤ b → b < p.P →
      Φ D r0 r1 a = Φ D r0 r1 b := by
    intro D r0 r1 a b hD hr ha hab hbP
    have hba0 : 0 ≤ b - a := sub_nonneg.mpr hab
    have hbaP : b - a < p.P := by linarith
    have haP : a < p.P := by linarith
    have hsum : (b - a) + a < p.P := by linarith
    have hmem : Set.Ioo r0 r1 ∈ 𝓝[>] r0 :=
      inter_mem_nhdsWithin (Set.Ioi r0) (Iio_mem_nhds hr)
    have hev : (fun y => Φ D r0 y (b - a) + Φ D y r1 a) =ᶠ[𝓝[>] r0] (fun _ => Φ D r0 r1 b) := by
      filter_upwards [hmem] with y hy
      have hstep := h2s D r0 y r1 (b - a) a hD hba0 ha hsum hy.1 hy.2
      have hadd : (b - a) + a = b := by ring
      rwa [hadd] at hstep
    have hlim_add : Tendsto (fun y => Φ D r0 y (b - a) + Φ D y r1 a) (𝓝[>] r0)
        (𝓝 (0 + Φ D r0 r1 a)) :=
      (hcont.1 D r0 (b - a) hD hba0 hbaP).add (hcont.2 D r0 r1 a hD hr ha haP)
    have hlim_const : Tendsto (fun y => Φ D r0 y (b - a) + Φ D y r1 a) (𝓝[>] r0)
        (𝓝 (Φ D r0 r1 b)) :=
      (tendsto_const_nhds (x := Φ D r0 r1 b)).congr' hev.symm
    have heq := tendsto_nhds_unique hlim_add hlim_const
    simpa only [zero_add] using heq
  have htime_indep : ∀ D r0 r1 t1 t2, 0 ≤ D → r0 < r1 →
      0 ≤ t1 → t1 < p.P → 0 ≤ t2 → t2 < p.P → Φ D r0 r1 t1 = Φ D r0 r1 t2 := by
    intro D r0 r1 t1 t2 hD hr ht1 ht1P ht2 ht2P
    rcases le_total t1 t2 with h | h
    · exact hle_eq D r0 r1 t1 t2 hD hr ht1 h ht2P
    · exact (hle_eq D r0 r1 t2 t1 hD hr ht2 h ht1P).symm
  have h1strong := time_indep_A1_implies_A1Strong p Φ h1 htime_indep
  exact ⟨htime_indep, designAStar_pointwise_lower_bound p Φ h0 h1strong h3⟩

theorem designAStar_global_lower_bound_from_weak_axioms (p : ProtocolParams)
    (Φ : ℝ → ℝ → ℝ → ℝ → ℝ)
    (h0 : SatisfiesCooldownConvention p Φ) (h1 : SatisfiesA1 p Φ)
    (h2 : SatisfiesA2 p Φ) (h3 : SatisfiesA3 p Φ) :
    ∀ D r0 r1 dt, 0 ≤ D → 0 ≤ dt → designAStarFee p D r0 r1 dt ≤ Φ D r0 r1 dt := by
  have htime_indep : ∀ D r0 r1 t1 t2, 0 ≤ D → r0 < r1 →
      0 ≤ t1 → t1 < p.P → 0 ≤ t2 → t2 < p.P →
      Φ D r0 r1 t1 = Φ D r0 r1 t2 := by
    have hle_eq : ∀ D r0 r1 a b, 0 ≤ D → r0 < r1 → 0 ≤ a → a ≤ b → b < p.P →
        Φ D r0 r1 a = Φ D r0 r1 b := by
      intro D r0 r1 a b hD hr ha hab hbP
      have hba : 0 ≤ b - a := sub_nonneg.mpr hab
      have hsum : (b - a) + a < p.P := by linarith
      have hstep := h2 D r0 r0 r1 (b - a) a hD hba ha hsum le_rfl (le_of_lt hr)
      have hnoop : Φ D r0 r0 (b - a) = 0 := h0 D r0 r0 (b - a) hD (Or.inr rfl)
      have hadd : (b - a) + a = b := by ring
      rw [hnoop, zero_add, hadd] at hstep
      exact hstep
    intro D r0 r1 t1 t2 hD hr ht1 ht1P ht2 ht2P
    rcases le_total t1 t2 with h | h
    · exact hle_eq D r0 r1 t1 t2 hD hr ht1 h ht2P
    · exact (hle_eq D r0 r1 t2 t1 hD hr ht2 h ht1P).symm
  have h1strong := time_indep_A1_implies_A1Strong p Φ h1 htime_indep
  exact designAStar_pointwise_lower_bound p Φ h0 h1strong h3

theorem designAStar_unique_minimal (p : ProtocolParams)
    (Φ : ℝ → ℝ → ℝ → ℝ → ℝ)
    (h0 : SatisfiesCooldownConvention p Φ) (h1 : SatisfiesA1 p Φ)
    (h2s : SatisfiesA2Strict p Φ) (h3 : SatisfiesA3 p Φ)
    (hcont : HasRightNoOpContinuity p Φ)
    (hmin : ∀ Ψ, SatisfiesCooldownConvention p Ψ → SatisfiesA1 p Ψ →
      SatisfiesA2Strict p Ψ → SatisfiesA3 p Ψ → SatisfiesA4 Ψ →
      HasRightNoOpContinuity p Ψ →
      ∀ D r0 r1 dt, 0 ≤ D → 0 ≤ dt → Φ D r0 r1 dt ≤ Ψ D r0 r1 dt) :
    ∀ D r0 r1 dt, 0 ≤ D → 0 ≤ dt → Φ D r0 r1 dt = designAStarFee p D r0 r1 dt := by
  intro D r0 r1 dt hD hdt0
  have hge := (designAStar_global_lower_bound_from_strict_micro_hikes p Φ h0 h1 h2s h3 hcont).2
    D r0 r1 dt hD hdt0
  have hle := hmin (designAStarFee p)
    (designAStar_satisfies_cooldown_convention p) (designAStar_satisfies_A1 p)
    (designAStar_satisfies_A2Strict p) (designAStar_satisfies_A3 p)
    (designAStar_satisfies_A4 p) (designAStar_has_right_noop_continuity p)
    D r0 r1 dt hD hdt0
  exact le_antisymm hle hge

structure AffineZeroStorageRule (p : ProtocolParams) where
  aUp : ℝ → ℝ
  bUp : ℝ → ℝ
  cUp : ℝ → ℝ
  aDn : ℝ → ℝ
  bDn : ℝ → ℝ
  cDn : ℝ → ℝ

noncomputable def AffineZeroStorageRule.eval {p : ProtocolParams}
    (R : AffineZeroStorageRule p) (D r0 r1 dt : ℝ) : ℝ :=
  if dt ≥ p.P ∨ r1 = r0 then 0
  else if r0 < r1 then D * (R.aUp dt * r1 + R.bUp dt * r0 + R.cUp dt)
  else D * (R.aDn dt * r0 + R.bDn dt * r1 + R.cDn dt)

lemma affine_noop_continuity_forces_cUp_zero (p : ProtocolParams)
    (R : AffineZeroStorageRule p) (hcont : HasRightNoOpContinuity p R.eval) :
    ∀ dt, 0 ≤ dt → dt < p.P → R.cUp dt = 0 := by
  intro dt hdt0 hdtP
  have hev : (fun y => R.eval 1 0 y dt) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun y => R.aUp dt * y + R.cUp dt) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hy0 : (0 : ℝ) < y := hy
    unfold AffineZeroStorageRule.eval
    have hnot : ¬ (dt ≥ p.P ∨ y = 0) := by push Not; exact ⟨hdtP, ne_of_gt hy0⟩
    simp [hnot, hy0]
  have hlim1 : Tendsto (fun y => R.aUp dt * y + R.cUp dt) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    (hcont.1 1 0 dt zero_le_one hdt0 hdtP).congr' hev
  have hlim2 : Tendsto (fun y => R.aUp dt * y + R.cUp dt) (𝓝[>] (0 : ℝ)) (𝓝 (R.cUp dt)) := by
    have hfn : Continuous (fun y : ℝ => R.aUp dt * y + R.cUp dt) := by fun_prop
    have h0 : Tendsto (fun y : ℝ => R.aUp dt * y + R.cUp dt) (𝓝[>] (0 : ℝ))
        (𝓝 (R.aUp dt * 0 + R.cUp dt)) :=
      (hfn.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
    simpa using h0
  exact tendsto_nhds_unique hlim2 hlim1

theorem affine_staircase_forces_homogeneous_increment (p : ProtocolParams)
    (R : AffineZeroStorageRule p)
    (h2s : SatisfiesA2Strict p R.eval)
    (hcont : HasRightNoOpContinuity p R.eval) :
    ∃ a : ℝ, ∀ dt, 0 ≤ dt → dt < p.P →
      R.aUp dt = a ∧ R.bUp dt = -a ∧ R.cUp dt = 0 := by
  have hc0 := affine_noop_continuity_forces_cUp_zero p R hcont
  have heval_up : ∀ r0 r1 dt, 0 ≤ dt → dt < p.P → r0 < r1 →
      R.eval 1 r0 r1 dt = R.aUp dt * r1 + R.bUp dt * r0 := by
    intro r0 r1 dt hdt0 hdtP hlt
    unfold AffineZeroStorageRule.eval
    have hnot : ¬ (dt ≥ p.P ∨ r1 = r0) := by push Not; exact ⟨hdtP, ne_of_gt hlt⟩
    simp only [hnot, ↓reduceIte, hlt, one_mul, hc0 dt hdt0 hdtP, add_zero]
  refine ⟨R.aUp 0, ?_⟩
  intro dt hdt0 hdtP
  have h0P : (0 : ℝ) < p.P := p.hP

  have e1 := h2s 1 0 1 2 0 dt zero_le_one le_rfl hdt0 (by linarith) (by norm_num) (by norm_num)
  have e2 := h2s 1 0 1 3 0 dt zero_le_one le_rfl hdt0 (by linarith) (by norm_num) (by norm_num)
  have e3 := h2s 1 1 2 3 0 dt zero_le_one le_rfl hdt0 (by linarith) (by norm_num) (by norm_num)

  have e4 := h2s 1 0 1 2 dt 0 zero_le_one hdt0 le_rfl (by linarith) (by norm_num) (by norm_num)
  have e5 := h2s 1 0 1 3 dt 0 zero_le_one hdt0 le_rfl (by linarith) (by norm_num) (by norm_num)
  have e6 := h2s 1 1 2 3 dt 0 zero_le_one hdt0 le_rfl (by linarith) (by norm_num) (by norm_num)
  simp only [zero_add, add_zero] at e1 e2 e3 e4 e5 e6
  rw [heval_up 0 1 0 le_rfl h0P (by norm_num), heval_up 1 2 dt hdt0 hdtP (by norm_num),
      heval_up 0 2 dt hdt0 hdtP (by norm_num)] at e1
  rw [heval_up 0 1 0 le_rfl h0P (by norm_num), heval_up 1 3 dt hdt0 hdtP (by norm_num),
      heval_up 0 3 dt hdt0 hdtP (by norm_num)] at e2
  rw [heval_up 1 2 0 le_rfl h0P (by norm_num), heval_up 2 3 dt hdt0 hdtP (by norm_num),
      heval_up 1 3 dt hdt0 hdtP (by norm_num)] at e3
  rw [heval_up 0 1 dt hdt0 hdtP (by norm_num), heval_up 1 2 0 le_rfl h0P (by norm_num),
      heval_up 0 2 dt hdt0 hdtP (by norm_num)] at e4
  rw [heval_up 0 1 dt hdt0 hdtP (by norm_num), heval_up 1 3 0 le_rfl h0P (by norm_num),
      heval_up 0 3 dt hdt0 hdtP (by norm_num)] at e5
  rw [heval_up 1 2 dt hdt0 hdtP (by norm_num), heval_up 2 3 0 le_rfl h0P (by norm_num),
      heval_up 1 3 dt hdt0 hdtP (by norm_num)] at e6
  refine ⟨by linarith, by linarith, hc0 dt hdt0 hdtP⟩

theorem designAStar_unique_affine (p : ProtocolParams)
    (R : AffineZeroStorageRule p)
    (h1 : SatisfiesA1 p R.eval) (h2s : SatisfiesA2Strict p R.eval)
    (h3 : SatisfiesA3 p R.eval) (hcont : HasRightNoOpContinuity p R.eval)
    (hTightUp : ∀ dt, 0 ≤ dt → dt < p.P → R.eval 1 0 1 dt ≤ p.P / p.Y)
    (hTightDn : ∀ dt, 0 ≤ dt → dt < p.P →
      R.eval 1 1 0 dt ≤ (p.P - dt) / p.Y ∧
      R.eval 1 2 1 dt ≤ (p.P - dt) / p.Y ∧
      R.eval 1 2 0 dt ≤ 2 * ((p.P - dt) / p.Y)) :
    ∀ D r0 r1 dt, 0 ≤ D → 0 ≤ dt → R.eval D r0 r1 dt = designAStarFee p D r0 r1 dt := by
  obtain ⟨a, ha⟩ := affine_staircase_forces_homogeneous_increment p R h2s hcont
  have h0 : SatisfiesCooldownConvention p R.eval := by
    intro D r0 r1 dt _ hexp
    unfold AffineZeroStorageRule.eval
    simp [hexp]
  have hglobal := (designAStar_global_lower_bound_from_strict_micro_hikes p R.eval h0 h1 h2s h3 hcont).2
  have hhalf_pos : 0 ≤ p.P / 2 := le_of_lt (half_pos p.hP)
  have hhalf_lt : p.P / 2 < p.P := half_lt_self p.hP
  have ha_eq : a = p.P / p.Y := by
    have hlo := hglobal 1 0 1 (p.P / 2) zero_le_one hhalf_pos
    have hhi := hTightUp (p.P / 2) hhalf_pos hhalf_lt
    unfold AffineZeroStorageRule.eval at hlo hhi
    unfold designAStarFee at hlo
    have hnot : ¬ (p.P / 2 ≥ p.P ∨ (1 : ℝ) = 0) := by push Not; exact ⟨hhalf_lt, by norm_num⟩
    simp only [hnot, ↓reduceIte, zero_lt_one, one_mul, mul_one, mul_zero, add_zero, sub_zero] at hlo hhi
    obtain ⟨ha1, _, hc1⟩ := ha (p.P / 2) hhalf_pos hhalf_lt
    linarith
  intro D r0 r1 dt hD hdt0
  by_cases hexp : dt ≥ p.P ∨ r1 = r0
  · unfold AffineZeroStorageRule.eval designAStarFee
    simp [hexp]
  · push Not at hexp
    rcases lt_trichotomy r0 r1 with hup | heq | hdn
    · obtain ⟨ha1, hb1, hc1⟩ := ha dt hdt0 hexp.1
      unfold AffineZeroStorageRule.eval designAStarFee
      have hnot : ¬ (dt ≥ p.P ∨ r1 = r0) := by push Not; exact hexp
      simp only [hnot, ↓reduceIte, hup]
      rw [ha1, hb1, hc1, ha_eq]
      ring
    · exact absurd heq.symm hexp.2
    · have hfloor := (satisfiesA3_iff_fee_floor p R.eval).mp h3
      have hdn_eval : ∀ x y, y < x →
          R.eval 1 x y dt = R.aDn dt * x + R.bDn dt * y + R.cDn dt := by
        intro x y hxy
        unfold AffineZeroStorageRule.eval
        have hnot1 : ¬ (dt ≥ p.P ∨ y = x) := by push Not; exact ⟨hexp.1, ne_of_lt hxy⟩
        have hnot2 : ¬ (x < y) := not_lt.mpr (le_of_lt hxy)
        simp [hnot1, hnot2]
      have hlo10 := hfloor 1 1 0 dt zero_le_one hdt0 hexp.1 (by norm_num)
      have hlo21 := hfloor 1 2 1 dt zero_le_one hdt0 hexp.1 (by norm_num)
      have hlo20 := hfloor 1 2 0 dt zero_le_one hdt0 hexp.1 (by norm_num)
      obtain ⟨hhi10, hhi21, hhi20⟩ := hTightDn dt hdt0 hexp.1
      rw [hdn_eval 1 0 (by norm_num)] at hlo10 hhi10
      rw [hdn_eval 2 1 (by norm_num)] at hlo21 hhi21
      rw [hdn_eval 2 0 (by norm_num)] at hlo20 hhi20
      have haDn : R.aDn dt = (p.P - dt) / p.Y := by linarith
      have hbDn : R.bDn dt = -((p.P - dt) / p.Y) := by linarith
      have hcDn : R.cDn dt = 0 := by linarith
      unfold AffineZeroStorageRule.eval designAStarFee
      have hnot1 : ¬ (dt ≥ p.P ∨ r1 = r0) := by push Not; exact hexp
      have hnot2 : ¬ (r0 < r1) := not_lt.mpr (le_of_lt hdn)
      simp only [hnot1, ↓reduceIte, hnot2]
      rw [haDn, hbDn, hcDn]
      ring

theorem designAStarFeeNat_staircase_floor_bound {K : ℕ} (hK : 1 ≤ K)
    (debt dt0 : Nat) (r : Fin (K + 1) → Nat) (dt : Fin K → Nat)
    (hr : ∀ k : Fin K, r k.castSucc ≤ r k.succ)
    (hdt : ∀ k : Fin K, dt k < UPFRONT_INTEREST_PERIOD)
    (hdt0 : dt0 < UPFRONT_INTEREST_PERIOD) :
    let sumSteps := ∑ k : Fin K, designAStarFeeNat debt (r k.castSucc) (r k.succ) (dt k)
    let singleJump := designAStarFeeNat debt (r 0) (r (Fin.last K)) dt0
    sumSteps ≤ singleJump ∧ singleJump ≤ sumSteps + (K - 1) := by
  dsimp only
  have hstep : ∀ k : Fin K,
      designAStarFeeNat debt (r k.castSucc) (r k.succ) (dt k) =
        calcInterestNat (debt * (r k.succ - r k.castSucc)) UPFRONT_INTEREST_PERIOD := by
    intro k
    by_cases heq : r k.succ = r k.castSucc
    · unfold designAStarFeeNat calcInterestNat
      simp [heq]
    · have hlt : r k.castSucc < r k.succ := lt_of_le_of_ne (hr k) (Ne.symm heq)
      unfold designAStarFeeNat
      have hnot : ¬ (dt k ≥ UPFRONT_INTEREST_PERIOD ∨ r k.succ = r k.castSucc) := by
        push Not
        exact ⟨hdt k, heq⟩
      simp [hnot, hlt]
  have hmono : r 0 ≤ r (Fin.last K) := Fin.monotone_iff_le_succ.mpr hr (Fin.zero_le _)
  have hsingle :
      designAStarFeeNat debt (r 0) (r (Fin.last K)) dt0 =
        calcInterestNat (debt * (r (Fin.last K) - r 0)) UPFRONT_INTEREST_PERIOD := by
    by_cases heq : r (Fin.last K) = r 0
    · unfold designAStarFeeNat calcInterestNat
      simp [heq]
    · have hlt : r 0 < r (Fin.last K) := lt_of_le_of_ne hmono (Ne.symm heq)
      unfold designAStarFeeNat
      have hnot : ¬ (dt0 ≥ UPFRONT_INTEREST_PERIOD ∨ r (Fin.last K) = r 0) := by
        push Not
        exact ⟨hdt0, heq⟩
      simp [hnot, hlt]
  simp_rw [hstep, hsingle]
  have htele : ∀ (m : ℕ) (f : Fin (m + 1) → Nat),
      (∀ k : Fin m, f k.castSucc ≤ f k.succ) →
      (∑ k : Fin m, (f k.succ - f k.castSucc)) = f (Fin.last m) - f 0 := by
    intro m
    induction m with
    | zero => intro f _; simp
    | succ j ih =>
      intro f hf
      rw [Fin.sum_univ_castSucc]
      have hcast_eq : ∀ k : Fin j, (k.castSucc : Fin (j + 1)).succ = k.succ.castSucc := by
        intro k; ext; simp
      simp_rw [hcast_eq]
      rw [ih (fun i => f i.castSucc) (fun k => hf k.castSucc)]
      have hlast_succ : (Fin.last j).succ = Fin.last (j + 1) := by ext; simp
      rw [hlast_succ, Fin.castSucc_zero]
      have h0j : f 0 ≤ f (Fin.last j).castSucc :=
        Fin.monotone_iff_le_succ.mpr hf (Fin.zero_le _)
      have hjl : f (Fin.last j).castSucc ≤ f (Fin.last (j + 1)) := by
        have := hf (Fin.last j)
        rwa [hlast_succ] at this
      omega
  have hnum_eq :
      (∑ k : Fin K, debt * (r k.succ - r k.castSucc) * UPFRONT_INTEREST_PERIOD) =
        debt * (r (Fin.last K) - r 0) * UPFRONT_INTEREST_PERIOD := by
    have h1 : ∀ k : Fin K,
        debt * (r k.succ - r k.castSucc) * UPFRONT_INTEREST_PERIOD =
          (debt * UPFRONT_INTEREST_PERIOD) * (r k.succ - r k.castSucc) := by
      intro k; ring
    simp_rw [h1, ← Finset.mul_sum, htele K r hr]
    ring
  set S := ∑ k : Fin K, calcInterestNat (debt * (r k.succ - r k.castSucc)) UPFRONT_INTEREST_PERIOD
  set Q := calcInterestNat (debt * (r (Fin.last K) - r 0)) UPFRONT_INTEREST_PERIOD
  have hlow_mul : S * INTEREST_DENOM ≤ debt * (r (Fin.last K) - r 0) * UPFRONT_INTEREST_PERIOD := by
    rw [← hnum_eq]
    dsimp only [S]
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun k _ => calcInterestNat_mul_le _ _
  have hhi_mul : debt * (r (Fin.last K) - r 0) * UPFRONT_INTEREST_PERIOD < (S + K) * INTEREST_DENOM := by
    rw [← hnum_eq]
    have hlt_each : ∀ k : Fin K,
        debt * (r k.succ - r k.castSucc) * UPFRONT_INTEREST_PERIOD <
          (calcInterestNat (debt * (r k.succ - r k.castSucc)) UPFRONT_INTEREST_PERIOD + 1) * INTEREST_DENOM :=
      fun k => calcInterestNat_lt_succ _ _
    have hne : (Finset.univ : Finset (Fin K)).Nonempty := by
      have : Nonempty (Fin K) := ⟨⟨0, by omega⟩⟩
      exact Finset.univ_nonempty
    have hsum_lt := Finset.sum_lt_sum_of_nonempty hne (fun k _ => hlt_each k)
    have hrhs :
        (∑ k : Fin K, (calcInterestNat (debt * (r k.succ - r k.castSucc)) UPFRONT_INTEREST_PERIOD + 1) * INTEREST_DENOM) =
          (S + K) * INTEREST_DENOM := by
      rw [← Finset.sum_mul, Finset.sum_add_distrib]
      simp [S, Finset.sum_const, Fintype.card_fin]
    linarith
  have hQ_le_num : Q * INTEREST_DENOM ≤ debt * (r (Fin.last K) - r 0) * UPFRONT_INTEREST_PERIOD :=
    calcInterestNat_mul_le _ _
  have hnum_lt_Q : debt * (r (Fin.last K) - r 0) * UPFRONT_INTEREST_PERIOD < (Q + 1) * INTEREST_DENOM :=
    calcInterestNat_lt_succ _ _
  have hd : 0 < INTEREST_DENOM := interest_denom_pos
  constructor
  · by_contra hgt
    push Not at hgt
    have hSQ : (Q + 1) * INTEREST_DENOM ≤ S * INTEREST_DENOM := Nat.mul_le_mul_right _ hgt
    omega
  · by_contra hgt
    push Not at hgt
    have hSK : S + K ≤ Q := by omega
    have hmul : (S + K) * INTEREST_DENOM ≤ Q * INTEREST_DENOM := Nat.mul_le_mul_right _ hSK
    omega

theorem designAStarFeeNat_cut_floor_bound
    (debt rHi rLo dt : Nat) (hdt : dt < UPFRONT_INTEREST_PERIOD) (hlt : rLo < rHi) :
    calcInterestNat (debt * rHi) UPFRONT_INTEREST_PERIOD ≤
      calcInterestNat (debt * rHi) dt +
      designAStarFeeNat debt rHi rLo dt +
      calcInterestNat (debt * rLo) (UPFRONT_INTEREST_PERIOD - dt) + 2 := by
  have hfee : designAStarFeeNat debt rHi rLo dt =
      calcInterestNat (debt * (rHi - rLo)) (UPFRONT_INTEREST_PERIOD - dt) := by
    unfold designAStarFeeNat
    have hnot1 : ¬ (dt ≥ UPFRONT_INTEREST_PERIOD ∨ rLo = rHi) := by
      push Not
      exact ⟨hdt, ne_of_lt hlt⟩
    have hnot2 : ¬ (rHi < rLo) := not_lt.mpr (le_of_lt hlt)
    simp [hnot1, hnot2]
  rw [hfee]
  set q0 := calcInterestNat (debt * rHi) UPFRONT_INTEREST_PERIOD
  set q1 := calcInterestNat (debt * rHi) dt
  set q2 := calcInterestNat (debt * (rHi - rLo)) (UPFRONT_INTEREST_PERIOD - dt)
  set q3 := calcInterestNat (debt * rLo) (UPFRONT_INTEREST_PERIOD - dt)
  have h0 : q0 * INTEREST_DENOM ≤ debt * rHi * UPFRONT_INTEREST_PERIOD :=
    calcInterestNat_mul_le _ _
  have h1 : debt * rHi * dt < (q1 + 1) * INTEREST_DENOM := calcInterestNat_lt_succ _ _
  have h2 : debt * (rHi - rLo) * (UPFRONT_INTEREST_PERIOD - dt) < (q2 + 1) * INTEREST_DENOM :=
    calcInterestNat_lt_succ _ _
  have h3 : debt * rLo * (UPFRONT_INTEREST_PERIOD - dt) < (q3 + 1) * INTEREST_DENOM :=
    calcInterestNat_lt_succ _ _
  have hsum_num :
      debt * rHi * dt + debt * (rHi - rLo) * (UPFRONT_INTEREST_PERIOD - dt) +
        debt * rLo * (UPFRONT_INTEREST_PERIOD - dt) =
      debt * rHi * UPFRONT_INTEREST_PERIOD := by
    have hr : rHi - rLo + rLo = rHi := Nat.sub_add_cancel (le_of_lt hlt)
    have ht : dt + (UPFRONT_INTEREST_PERIOD - dt) = UPFRONT_INTEREST_PERIOD :=
      Nat.add_sub_of_le (le_of_lt hdt)
    calc debt * rHi * dt + debt * (rHi - rLo) * (UPFRONT_INTEREST_PERIOD - dt) +
          debt * rLo * (UPFRONT_INTEREST_PERIOD - dt)
        = debt * rHi * dt + debt * (rHi - rLo + rLo) * (UPFRONT_INTEREST_PERIOD - dt) := by ring
      _ = debt * rHi * dt + debt * rHi * (UPFRONT_INTEREST_PERIOD - dt) := by rw [hr]
      _ = debt * rHi * (dt + (UPFRONT_INTEREST_PERIOD - dt)) := by ring
      _ = debt * rHi * UPFRONT_INTEREST_PERIOD := by rw [ht]
  have hstrict : q0 * INTEREST_DENOM < (q1 + q2 + q3 + 3) * INTEREST_DENOM := by
    have hmul_sum : (q1 + 1) * INTEREST_DENOM + (q2 + 1) * INTEREST_DENOM +
        (q3 + 1) * INTEREST_DENOM = (q1 + q2 + q3 + 3) * INTEREST_DENOM := by ring
    omega
  have hd : 0 < INTEREST_DENOM := interest_denom_pos
  by_contra hgt
  push Not at hgt
  have hge : (q1 + q2 + q3 + 3) * INTEREST_DENOM ≤ q0 * INTEREST_DENOM :=
    Nat.mul_le_mul_right _ hgt
  omega

theorem designAStarFeeCeilCutNat_zero_cut_shortfall
    (debt rHi rLo dt : Nat) (hdt : dt < UPFRONT_INTEREST_PERIOD) (hlt : rLo < rHi) :
    debt * (rHi - rLo) * (UPFRONT_INTEREST_PERIOD - dt) ≤
      designAStarFeeCeilCutNat debt rHi rLo dt * INTEREST_DENOM ∧
    calcInterestNat (debt * rHi) UPFRONT_INTEREST_PERIOD ≤
      calcInterestNat (debt * rHi) dt +
      designAStarFeeCeilCutNat debt rHi rLo dt +
      calcInterestNat (debt * rLo) (UPFRONT_INTEREST_PERIOD - dt) + 1 := by
  have hfee : designAStarFeeCeilCutNat debt rHi rLo dt =
      calcInterestCeilNat (debt * (rHi - rLo)) (UPFRONT_INTEREST_PERIOD - dt) := by
    unfold designAStarFeeCeilCutNat
    have hnot1 : ¬ (dt ≥ UPFRONT_INTEREST_PERIOD ∨ rLo = rHi) := by
      push Not
      exact ⟨hdt, ne_of_lt hlt⟩
    have hnot2 : ¬ (rHi < rLo) := not_lt.mpr (le_of_lt hlt)
    simp [hnot1, hnot2]
  rw [hfee]
  have hceil := mul_le_calcInterestCeilNat_mul (debt * (rHi - rLo)) (UPFRONT_INTEREST_PERIOD - dt)
  refine ⟨hceil, ?_⟩
  set q0 := calcInterestNat (debt * rHi) UPFRONT_INTEREST_PERIOD
  set q1 := calcInterestNat (debt * rHi) dt
  set q2 := calcInterestCeilNat (debt * (rHi - rLo)) (UPFRONT_INTEREST_PERIOD - dt)
  set q3 := calcInterestNat (debt * rLo) (UPFRONT_INTEREST_PERIOD - dt)
  have h0 : q0 * INTEREST_DENOM ≤ debt * rHi * UPFRONT_INTEREST_PERIOD :=
    calcInterestNat_mul_le _ _
  have h1 : debt * rHi * dt < (q1 + 1) * INTEREST_DENOM := calcInterestNat_lt_succ _ _
  have h3 : debt * rLo * (UPFRONT_INTEREST_PERIOD - dt) < (q3 + 1) * INTEREST_DENOM :=
    calcInterestNat_lt_succ _ _
  have hsum_num :
      debt * rHi * dt + debt * (rHi - rLo) * (UPFRONT_INTEREST_PERIOD - dt) +
        debt * rLo * (UPFRONT_INTEREST_PERIOD - dt) =
      debt * rHi * UPFRONT_INTEREST_PERIOD := by
    have hr : rHi - rLo + rLo = rHi := Nat.sub_add_cancel (le_of_lt hlt)
    have ht : dt + (UPFRONT_INTEREST_PERIOD - dt) = UPFRONT_INTEREST_PERIOD :=
      Nat.add_sub_of_le (le_of_lt hdt)
    calc debt * rHi * dt + debt * (rHi - rLo) * (UPFRONT_INTEREST_PERIOD - dt) +
          debt * rLo * (UPFRONT_INTEREST_PERIOD - dt)
        = debt * rHi * dt + debt * (rHi - rLo + rLo) * (UPFRONT_INTEREST_PERIOD - dt) := by ring
      _ = debt * rHi * dt + debt * rHi * (UPFRONT_INTEREST_PERIOD - dt) := by rw [hr]
      _ = debt * rHi * (dt + (UPFRONT_INTEREST_PERIOD - dt)) := by ring
      _ = debt * rHi * UPFRONT_INTEREST_PERIOD := by rw [ht]
  have hstrict : q0 * INTEREST_DENOM < (q1 + q2 + q3 + 2) * INTEREST_DENOM := by
    have hmul_sum : (q1 + 1) * INTEREST_DENOM + q2 * INTEREST_DENOM +
        (q3 + 1) * INTEREST_DENOM = (q1 + q2 + q3 + 2) * INTEREST_DENOM := by ring
    omega
  have hd : 0 < INTEREST_DENOM := interest_denom_pos
  by_contra hgt
  push Not at hgt
  have hge : (q1 + q2 + q3 + 2) * INTEREST_DENOM ≤ q0 * INTEREST_DENOM :=
    Nat.mul_le_mul_right _ hgt
  omega

theorem designAStarFeeCeilPlusOneNat_zero_total_shortfall
    (debt rHi rLo dt : Nat) (hdt : dt < UPFRONT_INTEREST_PERIOD) (hlt : rLo < rHi) :
    calcInterestNat (debt * rHi) UPFRONT_INTEREST_PERIOD ≤
      calcInterestNat (debt * rHi) dt +
      designAStarFeeCeilPlusOneNat debt rHi rLo dt +
      calcInterestNat (debt * rLo) (UPFRONT_INTEREST_PERIOD - dt) := by
  by_cases hD0 : debt = 0
  · subst hD0
    unfold calcInterestNat designAStarFeeCeilPlusOneNat
    simp
  · have hnum_pos : 0 < debt * (rHi - rLo) * (UPFRONT_INTEREST_PERIOD - dt) := by
      have h1 : 0 < debt := Nat.pos_of_ne_zero hD0
      have h2 : 0 < rHi - rLo := Nat.sub_pos_of_lt hlt
      have h3 : 0 < UPFRONT_INTEREST_PERIOD - dt := Nat.sub_pos_of_lt hdt
      exact Nat.mul_pos (Nat.mul_pos h1 h2) h3
    have hbase_pos : 0 < calcInterestCeilNat (debt * (rHi - rLo)) (UPFRONT_INTEREST_PERIOD - dt) := by
      have hmul := mul_le_calcInterestCeilNat_mul (debt * (rHi - rLo)) (UPFRONT_INTEREST_PERIOD - dt)
      by_contra h0
      push Not at h0
      have hzero : calcInterestCeilNat (debt * (rHi - rLo)) (UPFRONT_INTEREST_PERIOD - dt) = 0 := by omega
      rw [hzero, zero_mul] at hmul
      omega
    have hfee_eq : designAStarFeeCeilPlusOneNat debt rHi rLo dt =
        designAStarFeeCeilCutNat debt rHi rLo dt + 1 := by
      unfold designAStarFeeCeilPlusOneNat designAStarFeeCeilCutNat
      have hnot1 : ¬ (dt ≥ UPFRONT_INTEREST_PERIOD ∨ rLo = rHi) := by
        push Not; exact ⟨hdt, ne_of_lt hlt⟩
      have hnot2 : ¬ (rHi < rLo) := not_lt.mpr (le_of_lt hlt)
      have hne0 : calcInterestCeilNat (debt * (rHi - rLo)) (UPFRONT_INTEREST_PERIOD - dt) ≠ 0 :=
        ne_of_gt hbase_pos
      simp [hnot1, hnot2, hne0]
    have hbound := (designAStarFeeCeilCutNat_zero_cut_shortfall debt rHi rLo dt hdt hlt).2
    rw [hfee_eq]
    omega

theorem designAStarFeeNat_sybil_bound (D1 D2 r0 r1 dt : Nat) :
    designAStarFeeNat D1 r0 r1 dt + designAStarFeeNat D2 r0 r1 dt ≤
      designAStarFeeNat (D1 + D2) r0 r1 dt ∧
    designAStarFeeNat (D1 + D2) r0 r1 dt ≤
      designAStarFeeNat D1 r0 r1 dt + designAStarFeeNat D2 r0 r1 dt + 1 := by
  have hdiv_add : ∀ a b : Nat,
      a / INTEREST_DENOM + b / INTEREST_DENOM ≤ (a + b) / INTEREST_DENOM ∧
      (a + b) / INTEREST_DENOM ≤ a / INTEREST_DENOM + b / INTEREST_DENOM + 1 := by
    intro a b
    have hd : 0 < INTEREST_DENOM := interest_denom_pos
    have ha1 := Nat.div_mul_le_self a INTEREST_DENOM
    have hb1 := Nat.div_mul_le_self b INTEREST_DENOM
    have hab1 := Nat.div_mul_le_self (a + b) INTEREST_DENOM
    have ha2 : a < (a / INTEREST_DENOM + 1) * INTEREST_DENOM := by
      have hm := Nat.mod_lt a hd
      have hdm := Nat.div_add_mod a INTEREST_DENOM
      have hr : (a / INTEREST_DENOM + 1) * INTEREST_DENOM =
          INTEREST_DENOM * (a / INTEREST_DENOM) + INTEREST_DENOM := by ring
      omega
    have hb2 : b < (b / INTEREST_DENOM + 1) * INTEREST_DENOM := by
      have hm := Nat.mod_lt b hd
      have hdm := Nat.div_add_mod b INTEREST_DENOM
      have hr : (b / INTEREST_DENOM + 1) * INTEREST_DENOM =
          INTEREST_DENOM * (b / INTEREST_DENOM) + INTEREST_DENOM := by ring
      omega
    have hab2 : a + b < ((a + b) / INTEREST_DENOM + 1) * INTEREST_DENOM := by
      have hm := Nat.mod_lt (a + b) hd
      have hdm := Nat.div_add_mod (a + b) INTEREST_DENOM
      have hr : ((a + b) / INTEREST_DENOM + 1) * INTEREST_DENOM =
          INTEREST_DENOM * ((a + b) / INTEREST_DENOM) + INTEREST_DENOM := by ring
      omega
    constructor
    · by_contra hgt
      push Not at hgt
      have h1 : ((a + b) / INTEREST_DENOM + 1) * INTEREST_DENOM ≤
          (a / INTEREST_DENOM + b / INTEREST_DENOM) * INTEREST_DENOM :=
        Nat.mul_le_mul_right _ hgt
      have h2 : (a / INTEREST_DENOM + b / INTEREST_DENOM) * INTEREST_DENOM =
          a / INTEREST_DENOM * INTEREST_DENOM + b / INTEREST_DENOM * INTEREST_DENOM := by ring
      omega
    · by_contra hgt
      push Not at hgt
      have h1 : (a / INTEREST_DENOM + b / INTEREST_DENOM + 2) * INTEREST_DENOM ≤
          ((a + b) / INTEREST_DENOM) * INTEREST_DENOM :=
        Nat.mul_le_mul_right _ hgt
      have h2 : (a / INTEREST_DENOM + 1) * INTEREST_DENOM +
          (b / INTEREST_DENOM + 1) * INTEREST_DENOM =
          (a / INTEREST_DENOM + b / INTEREST_DENOM + 2) * INTEREST_DENOM := by ring
      omega
  unfold designAStarFeeNat
  split_ifs
  · omega
  · simp_rw [calcInterestNat_eq_single_div]
    have hmul : (D1 + D2) * (r1 - r0) * UPFRONT_INTEREST_PERIOD =
        D1 * (r1 - r0) * UPFRONT_INTEREST_PERIOD + D2 * (r1 - r0) * UPFRONT_INTEREST_PERIOD := by ring
    rw [hmul]
    exact hdiv_add _ _
  · simp_rw [calcInterestNat_eq_single_div]
    have hmul : (D1 + D2) * (r0 - r1) * (UPFRONT_INTEREST_PERIOD - dt) =
        D1 * (r0 - r1) * (UPFRONT_INTEREST_PERIOD - dt) +
        D2 * (r0 - r1) * (UPFRONT_INTEREST_PERIOD - dt) := by ring
    rw [hmul]
    exact hdiv_add _ _

end LiquityV2
