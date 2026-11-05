import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import LiquityV2.Defs

namespace LiquityV2

open Finset BigOperators

def netRedemptionCost (τ φ : ℝ) : ℝ := τ - φ

def flowCost (r τ φ lam : ℝ) : ℝ := r + (τ - φ) * lam

theorem absorber_optimal_at_rMin {rMin r τ φ : ℝ} {lam : ℝ → ℝ}
    (hanti : Antitone lam) (hτ : τ ≤ φ) (hr : rMin ≤ r) :
    flowCost rMin τ φ (lam rMin) ≤ flowCost r τ φ (lam r) := by
  unfold flowCost
  have hlam : lam r ≤ lam rMin := hanti hr
  have hc : τ - φ ≤ 0 := sub_nonpos.mpr hτ
  have hmul : (τ - φ) * lam rMin ≤ (τ - φ) * lam r :=
    mul_le_mul_of_nonpos_left hlam hc
  linarith

theorem absorber_strictly_optimal_at_rMin {rMin r τ φ : ℝ} {lam : ℝ → ℝ}
    (hanti : Antitone lam) (hτ : τ ≤ φ) (hr : rMin < r) :
    flowCost rMin τ φ (lam rMin) < flowCost r τ φ (lam r) := by
  unfold flowCost
  have hlam : lam r ≤ lam rMin := hanti (le_of_lt hr)
  have hc : τ - φ ≤ 0 := sub_nonpos.mpr hτ
  have hmul : (τ - φ) * lam rMin ≤ (τ - φ) * lam r :=
    mul_le_mul_of_nonpos_left hlam hc
  linarith

def IsIC {ι : Type*} (φ : ℝ) (τ r lam : ι → ℝ) : Prop :=
  ∀ i j, flowCost (r i) (τ i) φ (lam i) ≤ flowCost (r j) (τ i) φ (lam j)

theorem ic_hazard_antitone {ι : Type*} {φ : ℝ} {τ r lam : ι → ℝ}
    (hic : IsIC φ τ r lam) {i j : ι} (hτ : τ i < τ j) :
    lam j ≤ lam i := by
  have h1 := hic i j
  have h2 := hic j i
  unfold flowCost at h1 h2
  have hprod : (τ j - τ i) * (lam j - lam i) ≤ 0 := by nlinarith
  have hpos : 0 < τ j - τ i := sub_pos.mpr hτ
  nlinarith

theorem ic_rate_monotone {ι : Type*} {φ : ℝ} {τ r lam : ι → ℝ}
    (hic : IsIC φ τ r lam) {i j : ι} (hφ : φ < τ i) (hτ : τ i < τ j) :
    r i ≤ r j := by
  have hlam : lam j ≤ lam i := ic_hazard_antitone hic hτ
  have h1 := hic i j
  unfold flowCost at h1
  have hpos : 0 < τ i - φ := sub_pos.mpr hφ
  nlinarith

theorem ic_rate_strict_monotone {ι : Type*} {φ : ℝ} {τ r lam : ι → ℝ}
    (hic : IsIC φ τ r lam) {i j : ι} (hφ : φ < τ i) (hlam : lam j < lam i) :
    r i < r j := by
  have h1 := hic i j
  unfold flowCost at h1
  have hpos : 0 < τ i - φ := sub_pos.mpr hφ
  nlinarith

def indirectCost {ι : Type*} (φ : ℝ) (τ r lam : ι → ℝ) (i : ι) : ℝ :=
  flowCost (r i) (τ i) φ (lam i)

theorem ic_envelope_bounds {ι : Type*} {φ : ℝ} {τ r lam : ι → ℝ}
    (hic : IsIC φ τ r lam) (i j : ι) :
    (τ j - τ i) * lam j ≤ indirectCost φ τ r lam j - indirectCost φ τ r lam i ∧
      indirectCost φ τ r lam j - indirectCost φ τ r lam i ≤ (τ j - τ i) * lam i := by
  have h1 := hic i j
  have h2 := hic j i
  unfold indirectCost flowCost at *
  constructor <;> linarith

theorem ic_rate_diff_bounds {ι : Type*} {φ : ℝ} {τ r lam : ι → ℝ}
    (hic : IsIC φ τ r lam) (i j : ι) :
    (τ i - φ) * (lam i - lam j) ≤ r j - r i ∧
      r j - r i ≤ (τ j - φ) * (lam i - lam j) := by
  have h1 := hic i j
  have h2 := hic j i
  unfold flowCost at h1 h2
  constructor <;> linarith

theorem gpv_finite_sandwich {ι : Type*} {φ : ℝ} {τ r lam : ι → ℝ}
    (hic : IsIC φ τ r lam) {i j : ι} (hlam : lam j < lam i) :
    τ i ≤ φ + (r j - r i) / (lam i - lam j) ∧
      φ + (r j - r i) / (lam i - lam j) ≤ τ j := by
  have hbounds := ic_rate_diff_bounds hic i j
  have hpos : 0 < lam i - lam j := sub_pos.mpr hlam
  constructor
  · rw [← sub_le_iff_le_add', le_div_iff₀ hpos]
    linarith [hbounds.1]
  · rw [← le_sub_iff_add_le', div_le_iff₀ hpos]
    linarith [hbounds.2]

theorem gpv_continuous_identification {φ τ0 r' lam' : ℝ} {r lam : ℝ → ℝ}
    (hic : IsIC φ id r lam)
    (hr : HasDerivAt r r' τ0)
    (hlam : HasDerivAt lam lam' τ0)
    (hlam_neg : lam' < 0) :
    r' = (τ0 - φ) * (-lam') ∧ τ0 = φ + r' / (-lam') := by
  have hsub : Set.Ioi (0 : ℝ) ⊆ ({0}ᶜ : Set ℝ) := fun _ hx => ne_of_gt hx
  have hslope_r : Filter.Tendsto (fun h : ℝ => (r (τ0 + h) - r τ0) / h)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds r') := by
    have h0 := (hasDerivAt_iff_tendsto_slope_zero.mp hr).mono_left (nhdsWithin_mono 0 hsub)
    refine h0.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h _
    simp [smul_eq_mul, div_eq_inv_mul]
  have hslope_lam : Filter.Tendsto (fun h : ℝ => (lam (τ0 + h) - lam τ0) / h)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds lam') := by
    have h0 := (hasDerivAt_iff_tendsto_slope_zero.mp hlam).mono_left (nhdsWithin_mono 0 hsub)
    refine h0.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h _
    simp [smul_eq_mul, div_eq_inv_mul]
  have hlow_ev : ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (τ0 - φ) * (-((lam (τ0 + h) - lam τ0) / h)) ≤ (r (τ0 + h) - r τ0) / h := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hpos : (0 : ℝ) < h := hh
    have hb := (ic_rate_diff_bounds hic τ0 (τ0 + h)).1
    simp only [id_eq] at hb
    rw [le_div_iff₀ hpos]
    have hmul : (τ0 - φ) * (-((lam (τ0 + h) - lam τ0) / h)) * h =
        (τ0 - φ) * (lam τ0 - lam (τ0 + h)) := by
      field_simp [ne_of_gt hpos]
      ring
    linarith
  have hhi_ev : ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (r (τ0 + h) - r τ0) / h ≤ (τ0 + h - φ) * (-((lam (τ0 + h) - lam τ0) / h)) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hpos : (0 : ℝ) < h := hh
    have hb := (ic_rate_diff_bounds hic τ0 (τ0 + h)).2
    simp only [id_eq] at hb
    rw [div_le_iff₀ hpos]
    have hmul : (τ0 + h - φ) * (-((lam (τ0 + h) - lam τ0) / h)) * h =
        (τ0 + h - φ) * (lam τ0 - lam (τ0 + h)) := by
      field_simp [ne_of_gt hpos]
      ring
    linarith
  have htend_low : Filter.Tendsto
      (fun h : ℝ => (τ0 - φ) * (-((lam (τ0 + h) - lam τ0) / h)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds ((τ0 - φ) * (-lam'))) :=
    (hslope_lam.neg).const_mul (τ0 - φ)
  have htend_lin : Filter.Tendsto (fun h : ℝ => τ0 + h - φ)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (τ0 - φ)) := by
    have h0 : Filter.Tendsto (fun h : ℝ => h) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds Filter.tendsto_id
    simpa using (tendsto_const_nhds.add h0).sub tendsto_const_nhds
  have htend_hi : Filter.Tendsto
      (fun h : ℝ => (τ0 + h - φ) * (-((lam (τ0 + h) - lam τ0) / h)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds ((τ0 - φ) * (-lam'))) :=
    htend_lin.mul hslope_lam.neg
  have hle1 : (τ0 - φ) * (-lam') ≤ r' :=
    le_of_tendsto_of_tendsto htend_low hslope_r hlow_ev
  have hle2 : r' ≤ (τ0 - φ) * (-lam') :=
    le_of_tendsto_of_tendsto hslope_r htend_hi hhi_ev
  have heq : r' = (τ0 - φ) * (-lam') := le_antisymm hle2 hle1
  have hneg_pos : 0 < -lam' := neg_pos.mpr hlam_neg
  refine ⟨heq, ?_⟩
  rw [heq, mul_div_cancel_right₀ _ (ne_of_gt hneg_pos)]
  ring

def discreteEqRate {n : ℕ} (rMin φ : ℝ) (τ lam : Fin n → ℝ) (i : Fin n) : ℝ :=
  rMin + ∑ k ∈ Finset.range i.1,
    if h : k + 1 < n then
      (τ ⟨k, Nat.lt_of_succ_lt h⟩ - φ) * (lam ⟨k, Nat.lt_of_succ_lt h⟩ - lam ⟨k + 1, h⟩)
    else 0

lemma discreteEqRate_zero {n : ℕ} (hn : 0 < n) (rMin φ : ℝ) (τ lam : Fin n → ℝ) :
    discreteEqRate rMin φ τ lam ⟨0, hn⟩ = rMin := by
  unfold discreteEqRate
  simp

lemma discreteEqRate_sub_of_le {n : ℕ} (rMin φ : ℝ) (τ lam : Fin n → ℝ)
    {i j : Fin n} (hij : i.1 ≤ j.1) :
    discreteEqRate rMin φ τ lam j - discreteEqRate rMin φ τ lam i =
      ∑ k ∈ Finset.Ico i.1 j.1,
        if h : k + 1 < n then
          (τ ⟨k, Nat.lt_of_succ_lt h⟩ - φ) * (lam ⟨k, Nat.lt_of_succ_lt h⟩ - lam ⟨k + 1, h⟩)
        else 0 := by
  unfold discreteEqRate
  have hsplit := Finset.sum_range_add_sum_Ico
    (f := fun k => if h : k + 1 < n then
      (τ ⟨k, Nat.lt_of_succ_lt h⟩ - φ) * (lam ⟨k, Nat.lt_of_succ_lt h⟩ - lam ⟨k + 1, h⟩)
    else 0) hij
  linarith

lemma sum_Ico_hazard_telescope {n : ℕ} (lam : Fin n → ℝ) {i j : Fin n} (hij : i.1 ≤ j.1) :
    (∑ k ∈ Finset.Ico i.1 j.1,
      if h : k + 1 < n then lam ⟨k, Nat.lt_of_succ_lt h⟩ - lam ⟨k + 1, h⟩ else 0) =
      lam i - lam j := by
  rcases i with ⟨iv, hi⟩
  rcases j with ⟨jv, hj⟩
  dsimp only at hij ⊢
  induction jv with
  | zero =>
    have hiv : iv = 0 := Nat.eq_zero_of_le_zero hij
    subst hiv
    simp
  | succ m ih =>
    by_cases hEq : iv = m + 1
    · subst hEq
      simp
    · have him : iv ≤ m := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne hij hEq)
      have hm : m < n := Nat.lt_of_succ_lt hj
      rw [Finset.sum_Ico_succ_top him]
      rw [ih hm him]
      simp only [hj, ↓reduceDIte]
      ring

theorem discreteEqRate_isIC {n : ℕ} (rMin φ : ℝ) {τ lam : Fin n → ℝ}
    (hτ : Monotone τ) (hlam : Antitone lam) :
    IsIC φ τ (discreteEqRate rMin φ τ lam) lam := by
  intro i j
  unfold flowCost
  by_cases hij : i.1 ≤ j.1
  · have hdiff := discreteEqRate_sub_of_le rMin φ τ lam hij
    have htele := sum_Ico_hazard_telescope lam hij
    have hsum_ge :
        (τ i - φ) * (lam i - lam j) ≤
          discreteEqRate rMin φ τ lam j - discreteEqRate rMin φ τ lam i := by
      rw [hdiff, ← htele, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro k hk
      have hkm : k < j.1 := (Finset.mem_Ico.mp hk).2
      have hk1 : k + 1 < n := Nat.lt_of_le_of_lt hkm j.2
      have hik : i.1 ≤ k := (Finset.mem_Ico.mp hk).1
      simp only [hk1, ↓reduceDIte]
      have hτik : τ i ≤ τ ⟨k, Nat.lt_of_succ_lt hk1⟩ := hτ (by exact hik)
      have hlam_nn : 0 ≤ lam ⟨k, Nat.lt_of_succ_lt hk1⟩ - lam ⟨k + 1, hk1⟩ := by
        have hstep : lam ⟨k + 1, hk1⟩ ≤ lam ⟨k, Nat.lt_of_succ_lt hk1⟩ :=
          hlam (show (⟨k, Nat.lt_of_succ_lt hk1⟩ : Fin n) ≤ ⟨k + 1, hk1⟩ from Nat.le_succ k)
        linarith
      nlinarith
    linarith
  · have hji : j.1 ≤ i.1 := Nat.le_of_lt (Nat.lt_of_not_ge hij)
    have hdiff := discreteEqRate_sub_of_le rMin φ τ lam hji
    have htele := sum_Ico_hazard_telescope lam hji
    have hsum_le :
        discreteEqRate rMin φ τ lam i - discreteEqRate rMin φ τ lam j ≤
          (τ i - φ) * (lam j - lam i) := by
      rw [hdiff, ← htele, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro k hk
      have hkm : k < i.1 := (Finset.mem_Ico.mp hk).2
      have hk1 : k + 1 < n := Nat.lt_of_le_of_lt hkm i.2
      simp only [hk1, ↓reduceDIte]
      have hτki : τ ⟨k, Nat.lt_of_succ_lt hk1⟩ ≤ τ i := hτ (le_of_lt hkm)
      have hlam_nn : 0 ≤ lam ⟨k, Nat.lt_of_succ_lt hk1⟩ - lam ⟨k + 1, hk1⟩ := by
        have hstep : lam ⟨k + 1, hk1⟩ ≤ lam ⟨k, Nat.lt_of_succ_lt hk1⟩ :=
          hlam (show (⟨k, Nat.lt_of_succ_lt hk1⟩ : Fin n) ≤ ⟨k + 1, hk1⟩ from Nat.le_succ k)
        linarith
      nlinarith
    linarith

theorem discreteEqRate_strictMono {n : ℕ} (rMin φ : ℝ) {τ lam : Fin n → ℝ}
    (hφ : ∀ i, φ < τ i) (hlam : StrictAnti lam) :
    StrictMono (discreteEqRate rMin φ τ lam) := by
  intro i j hij
  have hij_le : i.1 ≤ j.1 := le_of_lt hij
  have hdiff := discreteEqRate_sub_of_le rMin φ τ lam hij_le
  have hpos_sum : 0 < ∑ k ∈ Finset.Ico i.1 j.1,
      if h : k + 1 < n then
        (τ ⟨k, Nat.lt_of_succ_lt h⟩ - φ) * (lam ⟨k, Nat.lt_of_succ_lt h⟩ - lam ⟨k + 1, h⟩)
      else 0 := by
    apply Finset.sum_pos
    · intro k hk
      have hkm : k < j.1 := (Finset.mem_Ico.mp hk).2
      have hk1 : k + 1 < n := Nat.lt_of_le_of_lt hkm j.2
      simp only [hk1, ↓reduceDIte]
      have h1 : 0 < τ ⟨k, Nat.lt_of_succ_lt hk1⟩ - φ := sub_pos.mpr (hφ _)
      have h2 : 0 < lam ⟨k, Nat.lt_of_succ_lt hk1⟩ - lam ⟨k + 1, hk1⟩ :=
        sub_pos.mpr (hlam (show (⟨k, Nat.lt_of_succ_lt hk1⟩ : Fin n) < ⟨k + 1, hk1⟩ from Nat.lt_succ_self k))
      exact mul_pos h1 h2
    · exact ⟨i.1, Finset.mem_Ico.mpr ⟨le_rfl, hij⟩⟩
  linarith

private lemma weighted_chebyshev_expand {n : ℕ} (d c lam : Fin n → ℝ) :
    (∑ i : Fin n, ∑ j : Fin n, d i * d j * (c i - c j) * (lam i - lam j)) =
      2 * ((∑ i : Fin n, d i) * (∑ i : Fin n, d i * c i * lam i) -
        (∑ i : Fin n, d i * c i) * (∑ i : Fin n, d i * lam i)) := by
  have hsplit : ∀ i j : Fin n,
      d i * d j * (c i - c j) * (lam i - lam j) =
        (d i * c i * lam i) * d j + d i * (d j * c j * lam j) -
        (d i * c i) * (d j * lam j) - (d i * lam i) * (d j * c j) := by
    intro i j; ring
  simp_rw [hsplit, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have h1 : (∑ i : Fin n, ∑ j : Fin n, (d i * c i * lam i) * d j) =
      (∑ i : Fin n, d i * c i * lam i) * (∑ j : Fin n, d j) := by
    simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
  have h2 : (∑ i : Fin n, ∑ j : Fin n, d i * (d j * c j * lam j)) =
      (∑ i : Fin n, d i) * (∑ j : Fin n, d j * c j * lam j) := by
    simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
  have h3 : (∑ i : Fin n, ∑ j : Fin n, (d i * c i) * (d j * lam j)) =
      (∑ i : Fin n, d i * c i) * (∑ j : Fin n, d j * lam j) := by
    simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
  have h4 : (∑ i : Fin n, ∑ j : Fin n, (d i * lam i) * (d j * c j)) =
      (∑ i : Fin n, d i * lam i) * (∑ j : Fin n, d j * c j) := by
    simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
  rw [h1, h2, h3, h4]
  ring

theorem sorting_efficiency_weighted_chebyshev {n : ℕ} (φ : ℝ) {d τ lam : Fin n → ℝ}
    (hd : ∀ i, 0 ≤ d i) (hτ : Monotone τ) (hlam : Antitone lam) :
    (∑ i : Fin n, d i) * (∑ i : Fin n, d i * (τ i - φ) * lam i) ≤
      (∑ i : Fin n, d i * (τ i - φ)) * (∑ i : Fin n, d i * lam i) := by
  let c : Fin n → ℝ := fun i => τ i - φ
  have hpair : ∑ i : Fin n, ∑ j : Fin n, d i * d j * (c i - c j) * (lam i - lam j) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i _
    apply Finset.sum_nonpos
    intro j _
    have hdd : 0 ≤ d i * d j := mul_nonneg (hd i) (hd j)
    rcases le_total i j with hij | hji
    · have h1 : c i ≤ c j := sub_le_sub_right (hτ hij) φ
      have h2 : lam j ≤ lam i := hlam hij
      have hprod : (c i - c j) * (lam i - lam j) ≤ 0 := by nlinarith
      nlinarith
    · have h1 : c j ≤ c i := sub_le_sub_right (hτ hji) φ
      have h2 : lam i ≤ lam j := hlam hji
      have hprod : (c i - c j) * (lam i - lam j) ≤ 0 := by nlinarith
      nlinarith
  have hexpand := weighted_chebyshev_expand d c lam
  dsimp only [c] at hexpand hpair
  linarith

theorem sorting_efficiency_chebyshev {n : ℕ} (φ : ℝ) {τ lam : Fin n → ℝ}
    (hτ : Monotone τ) (hlam : Antitone lam) :
    (n : ℝ) * (∑ i : Fin n, (τ i - φ) * lam i) ≤
      (∑ i : Fin n, (τ i - φ)) * (∑ i : Fin n, lam i) := by
  have hw := sorting_efficiency_weighted_chebyshev φ (d := fun _ : Fin n => (1 : ℝ))
    (fun _ => zero_le_one) hτ hlam
  simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin] using hw

theorem sorting_efficiency_chebyshev_strict {n : ℕ} (φ : ℝ) {τ lam : Fin n → ℝ}
    (hτ : Monotone τ) (hlam : Antitone lam)
    {i0 j0 : Fin n} (hτs : τ i0 < τ j0) (hlams : lam j0 < lam i0) :
    (n : ℝ) * (∑ i : Fin n, (τ i - φ) * lam i) <
      (∑ i : Fin n, (τ i - φ)) * (∑ i : Fin n, lam i) := by
  let c : Fin n → ℝ := fun i => τ i - φ
  have hterm_le : ∀ p : Fin n × Fin n,
      (1 : ℝ) * 1 * (c p.1 - c p.2) * (lam p.1 - lam p.2) ≤ 0 := by
    intro ⟨i, j⟩
    rcases le_total i j with hij | hji
    · have h1 : c i ≤ c j := sub_le_sub_right (hτ hij) φ
      have h2 : lam j ≤ lam i := hlam hij
      nlinarith
    · have h1 : c j ≤ c i := sub_le_sub_right (hτ hji) φ
      have h2 : lam i ≤ lam j := hlam hji
      nlinarith
  have hterm_lt : (1 : ℝ) * 1 * (c i0 - c j0) * (lam i0 - lam j0) < 0 := by
    have h1 : c i0 < c j0 := sub_lt_sub_right hτs φ
    nlinarith
  have hpair_lt :
      ∑ p : Fin n × Fin n, (1 : ℝ) * 1 * (c p.1 - c p.2) * (lam p.1 - lam p.2) < 0 := by
    have hsum := Finset.sum_lt_sum (s := (Finset.univ : Finset (Fin n × Fin n)))
      (f := fun p => (1 : ℝ) * 1 * (c p.1 - c p.2) * (lam p.1 - lam p.2))
      (g := fun _ => (0 : ℝ))
      (fun p _ => hterm_le p)
      ⟨(i0, j0), Finset.mem_univ _, hterm_lt⟩
    simpa using hsum
  have hdouble :
      (∑ i : Fin n, ∑ j : Fin n, (1 : ℝ) * 1 * (c i - c j) * (lam i - lam j)) =
        ∑ p : Fin n × Fin n, (1 : ℝ) * 1 * (c p.1 - c p.2) * (lam p.1 - lam p.2) := by
    rw [← Fintype.sum_prod_type']
  have hexpand := weighted_chebyshev_expand (fun _ : Fin n => (1 : ℝ)) c lam
  simp only [one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one] at hexpand hdouble hpair_lt
  dsimp only [c] at hexpand hdouble hpair_lt
  linarith

def discreteEqRatePooled {n : ℕ} (k0 : ℕ) (rMin φ lamPool : ℝ) (τ lam : Fin n → ℝ)
    (i : Fin n) : ℝ :=
  if i.1 < k0 then rMin
  else
    rMin +
    (if hk0 : k0 < n then (τ ⟨k0, hk0⟩ - φ) * (lamPool - lam ⟨k0, hk0⟩) else 0) +
    ∑ k ∈ Finset.Ico k0 i.1,
      if h1 : k + 1 < n then
        (τ ⟨k, Nat.lt_of_succ_lt h1⟩ - φ) * (lam ⟨k, Nat.lt_of_succ_lt h1⟩ - lam ⟨k + 1, h1⟩)
      else 0

def pooledHazard {n : ℕ} (k0 : ℕ) (lamPool : ℝ) (lam : Fin n → ℝ) (i : Fin n) : ℝ :=
  if i.1 < k0 then lamPool else lam i

theorem discreteEqRatePooled_isIC {n : ℕ} (k0 : ℕ) (rMin φ lamPool : ℝ)
    {τ lam : Fin n → ℝ}
    (hτ : Monotone τ) (hlam : Antitone lam)
    (habs : ∀ i : Fin n, i.1 < k0 → τ i ≤ φ)
    (hnonabs : ∀ i : Fin n, k0 ≤ i.1 → φ < τ i)
    (hpool : ∀ i : Fin n, k0 ≤ i.1 → lam i ≤ lamPool) :
    IsIC φ τ (discreteEqRatePooled k0 rMin φ lamPool τ lam) (pooledHazard k0 lamPool lam) := by
  intro i j
  unfold flowCost
  have hge_rMin : ∀ m : Fin n, rMin ≤ discreteEqRatePooled k0 rMin φ lamPool τ lam m := by
    intro m
    unfold discreteEqRatePooled
    split_ifs with hm hk0
    · exact le_rfl
    · have h1 : 0 ≤ (τ ⟨k0, hk0⟩ - φ) * (lamPool - lam ⟨k0, hk0⟩) :=
        mul_nonneg (sub_nonneg.mpr (le_of_lt (hnonabs ⟨k0, hk0⟩ le_rfl)))
          (sub_nonneg.mpr (hpool ⟨k0, hk0⟩ le_rfl))
      have h2 : 0 ≤ ∑ k ∈ Finset.Ico k0 m.1,
          if h1 : k + 1 < n then
            (τ ⟨k, Nat.lt_of_succ_lt h1⟩ - φ) * (lam ⟨k, Nat.lt_of_succ_lt h1⟩ - lam ⟨k + 1, h1⟩)
          else 0 := by
        apply Finset.sum_nonneg
        intro k hk
        split_ifs with h1
        · have hk_ge : k0 ≤ k := (Finset.mem_Ico.mp hk).1
          have ht : 0 ≤ τ ⟨k, Nat.lt_of_succ_lt h1⟩ - φ :=
            sub_nonneg.mpr (le_of_lt (hnonabs ⟨k, Nat.lt_of_succ_lt h1⟩ hk_ge))
          have hl : 0 ≤ lam ⟨k, Nat.lt_of_succ_lt h1⟩ - lam ⟨k + 1, h1⟩ :=
            sub_nonneg.mpr (hlam (show (⟨k, Nat.lt_of_succ_lt h1⟩ : Fin n) ≤ ⟨k + 1, h1⟩ from Nat.le_succ k))
          exact mul_nonneg ht hl
        · exact le_rfl
      linarith
    · omega
  by_cases hi : i.1 < k0
  ·
    have hri : discreteEqRatePooled k0 rMin φ lamPool τ lam i = rMin := by
      unfold discreteEqRatePooled; simp [hi]
    have hli : pooledHazard k0 lamPool lam i = lamPool := by
      unfold pooledHazard; simp [hi]
    have hlj : pooledHazard k0 lamPool lam j ≤ lamPool := by
      unfold pooledHazard
      split_ifs with hj
      · exact le_rfl
      · exact hpool j (Nat.le_of_not_lt hj)
    have hcj : τ i - φ ≤ 0 := sub_nonpos.mpr (habs i hi)
    have hmul : (τ i - φ) * lamPool ≤ (τ i - φ) * pooledHazard k0 lamPool lam j :=
      mul_le_mul_of_nonpos_left hlj hcj
    have hrj := hge_rMin j
    rw [hri, hli]
    linarith
  ·
    have hik0 : k0 ≤ i.1 := Nat.le_of_not_lt hi
    have hk0n : k0 < n := Nat.lt_of_le_of_lt hik0 i.2
    have hli : pooledHazard k0 lamPool lam i = lam i := by
      unfold pooledHazard; simp [hi]
    by_cases hj : j.1 < k0
    ·
      have hrj : discreteEqRatePooled k0 rMin φ lamPool τ lam j = rMin := by
        unfold discreteEqRatePooled; simp [hj]
      have hlj : pooledHazard k0 lamPool lam j = lamPool := by
        unfold pooledHazard; simp [hj]
      have hri : discreteEqRatePooled k0 rMin φ lamPool τ lam i - rMin =
          (τ ⟨k0, hk0n⟩ - φ) * (lamPool - lam ⟨k0, hk0n⟩) +
          ∑ k ∈ Finset.Ico k0 i.1,
            if h1 : k + 1 < n then
              (τ ⟨k, Nat.lt_of_succ_lt h1⟩ - φ) * (lam ⟨k, Nat.lt_of_succ_lt h1⟩ - lam ⟨k + 1, h1⟩)
            else 0 := by
        unfold discreteEqRatePooled
        simp only [hi, ↓reduceIte, ↓reduceDIte, hk0n]
        ring
      have htele := sum_Ico_hazard_telescope lam (i := ⟨k0, hk0n⟩) (j := i) hik0
      have hsum_le :
          (∑ k ∈ Finset.Ico k0 i.1,
            if h1 : k + 1 < n then
              (τ ⟨k, Nat.lt_of_succ_lt h1⟩ - φ) * (lam ⟨k, Nat.lt_of_succ_lt h1⟩ - lam ⟨k + 1, h1⟩)
            else 0) ≤ (τ i - φ) * (lam ⟨k0, hk0n⟩ - lam i) := by
        rw [← htele, Finset.mul_sum]
        apply Finset.sum_le_sum
        intro k hk
        have hkm : k < i.1 := (Finset.mem_Ico.mp hk).2
        have hk1 : k + 1 < n := Nat.lt_of_le_of_lt hkm i.2
        simp only [hk1, ↓reduceDIte]
        have hτki : τ ⟨k, Nat.lt_of_succ_lt hk1⟩ ≤ τ i := hτ (le_of_lt hkm)
        have hlam_nn : 0 ≤ lam ⟨k, Nat.lt_of_succ_lt hk1⟩ - lam ⟨k + 1, hk1⟩ :=
          sub_nonneg.mpr (hlam (show (⟨k, Nat.lt_of_succ_lt hk1⟩ : Fin n) ≤ ⟨k + 1, hk1⟩ from Nat.le_succ k))
        nlinarith
      have hhead_le :
          (τ ⟨k0, hk0n⟩ - φ) * (lamPool - lam ⟨k0, hk0n⟩) ≤
            (τ i - φ) * (lamPool - lam ⟨k0, hk0n⟩) := by
        have hτk0 : τ ⟨k0, hk0n⟩ ≤ τ i := hτ hik0
        have hlp : 0 ≤ lamPool - lam ⟨k0, hk0n⟩ := sub_nonneg.mpr (hpool ⟨k0, hk0n⟩ le_rfl)
        nlinarith
      rw [hrj, hli, hlj]
      linarith
    ·
      have hjk0 : k0 ≤ j.1 := Nat.le_of_not_lt hj
      have hlj : pooledHazard k0 lamPool lam j = lam j := by
        unfold pooledHazard; simp [hj]
      have hdiff_eq : ∀ a b : Fin n, k0 ≤ a.1 → k0 ≤ b.1 → a.1 ≤ b.1 →
          discreteEqRatePooled k0 rMin φ lamPool τ lam b -
            discreteEqRatePooled k0 rMin φ lamPool τ lam a =
          ∑ k ∈ Finset.Ico a.1 b.1,
            if h1 : k + 1 < n then
              (τ ⟨k, Nat.lt_of_succ_lt h1⟩ - φ) * (lam ⟨k, Nat.lt_of_succ_lt h1⟩ - lam ⟨k + 1, h1⟩)
            else 0 := by
        intro a b ha hb hab
        have hna : ¬ a.1 < k0 := not_lt.mpr ha
        have hnb : ¬ b.1 < k0 := not_lt.mpr hb
        unfold discreteEqRatePooled
        simp only [hna, hnb, ↓reduceIte, ↓reduceDIte, hk0n]
        have hsplit := Finset.sum_Ico_consecutive
          (f := fun k => if h1 : k + 1 < n then
            (τ ⟨k, Nat.lt_of_succ_lt h1⟩ - φ) * (lam ⟨k, Nat.lt_of_succ_lt h1⟩ - lam ⟨k + 1, h1⟩)
          else 0) ha hab
        linarith
      rw [hli, hlj]
      by_cases hij : i.1 ≤ j.1
      · have hdiff := hdiff_eq i j hik0 hjk0 hij
        have htele := sum_Ico_hazard_telescope lam hij
        have hge : (τ i - φ) * (lam i - lam j) ≤
            discreteEqRatePooled k0 rMin φ lamPool τ lam j -
              discreteEqRatePooled k0 rMin φ lamPool τ lam i := by
          rw [hdiff, ← htele, Finset.mul_sum]
          apply Finset.sum_le_sum
          intro k hk
          have hkm : k < j.1 := (Finset.mem_Ico.mp hk).2
          have hk1 : k + 1 < n := Nat.lt_of_le_of_lt hkm j.2
          have hik : i.1 ≤ k := (Finset.mem_Ico.mp hk).1
          simp only [hk1, ↓reduceDIte]
          have hτik : τ i ≤ τ ⟨k, Nat.lt_of_succ_lt hk1⟩ := hτ hik
          have hlam_nn : 0 ≤ lam ⟨k, Nat.lt_of_succ_lt hk1⟩ - lam ⟨k + 1, hk1⟩ :=
            sub_nonneg.mpr (hlam (show (⟨k, Nat.lt_of_succ_lt hk1⟩ : Fin n) ≤ ⟨k + 1, hk1⟩ from Nat.le_succ k))
          nlinarith
        linarith
      · have hji : j.1 ≤ i.1 := Nat.le_of_lt (Nat.lt_of_not_ge hij)
        have hdiff := hdiff_eq j i hjk0 hik0 hji
        have htele := sum_Ico_hazard_telescope lam hji
        have hle :
            discreteEqRatePooled k0 rMin φ lamPool τ lam i -
              discreteEqRatePooled k0 rMin φ lamPool τ lam j ≤
            (τ i - φ) * (lam j - lam i) := by
          rw [hdiff, ← htele, Finset.mul_sum]
          apply Finset.sum_le_sum
          intro k hk
          have hkm : k < i.1 := (Finset.mem_Ico.mp hk).2
          have hk1 : k + 1 < n := Nat.lt_of_le_of_lt hkm i.2
          simp only [hk1, ↓reduceDIte]
          have hτki : τ ⟨k, Nat.lt_of_succ_lt hk1⟩ ≤ τ i := hτ (le_of_lt hkm)
          have hlam_nn : 0 ≤ lam ⟨k, Nat.lt_of_succ_lt hk1⟩ - lam ⟨k + 1, hk1⟩ :=
            sub_nonneg.mpr (hlam (show (⟨k, Nat.lt_of_succ_lt hk1⟩ : Fin n) ≤ ⟨k + 1, hk1⟩ from Nat.le_succ k))
          nlinarith
        linarith

theorem pooled_absorber_sorting_loss {m : ℕ} (φ : ℝ) {τ lam : Fin m → ℝ}
    (hm : 0 < m) (hτ : Monotone τ) (hlam : Antitone lam) :
    let lamBar := (∑ i : Fin m, lam i) / (m : ℝ)
    (∑ i : Fin m, (τ i - φ) * lam i) ≤ ∑ i : Fin m, (τ i - φ) * lamBar := by
  dsimp only
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hcheb := sorting_efficiency_chebyshev φ hτ hlam
  have hrhs : (∑ i : Fin m, (τ i - φ) * ((∑ j : Fin m, lam j) / (m : ℝ))) =
      ((∑ i : Fin m, (τ i - φ)) * (∑ j : Fin m, lam j)) / (m : ℝ) := by
    rw [← Finset.sum_mul, mul_div_assoc]
  rw [hrhs, le_div_iff₀ hm_pos]
  linarith

theorem two_sided_sp_recycling_dwl
    (I_rec F_upfront C_lumpy C_pq G_lumpy G_star RP_lumpy RP_star : ℝ)
    (hC : C_pq ≤ C_lumpy) (hG : G_star ≤ G_lumpy) (hRP : RP_star ≤ RP_lumpy)
    (hstrict : C_pq < C_lumpy ∨ G_star < G_lumpy ∨ RP_star < RP_lumpy) :
    let borrowerCostLumpy := I_rec + F_upfront + C_lumpy + G_lumpy + RP_lumpy
    let spPilRevenueLumpy := I_rec + F_upfront
    let borrowerCostClean := I_rec + C_pq + G_star + RP_star
    let spPilRevenueClean := I_rec
    let socialCostLumpy := borrowerCostLumpy - spPilRevenueLumpy
    let socialCostClean := borrowerCostClean - spPilRevenueClean
    socialCostLumpy - socialCostClean =
      (C_lumpy - C_pq) + (G_lumpy - G_star) + (RP_lumpy - RP_star) ∧
    0 < socialCostLumpy - socialCostClean := by
  dsimp only
  constructor
  · ring
  · rcases hstrict with h | h | h <;> linarith

theorem homogeneous_positional_rent {rMin r τ φ lam lam0 : ℝ}
    (hφ : φ < τ) (hlam : lam ≤ lam0)
    (heq : flowCost r τ φ lam = flowCost rMin τ φ lam0) :
    r - rMin = (τ - φ) * (lam0 - lam) ∧ 0 ≤ r - rMin := by
  unfold flowCost at heq
  have hdiff : r - rMin = (τ - φ) * (lam0 - lam) := by linarith
  have hnn : 0 ≤ (τ - φ) * (lam0 - lam) :=
    mul_nonneg (sub_nonneg.mpr (le_of_lt hφ)) (sub_nonneg.mpr hlam)
  exact ⟨hdiff, by linarith⟩

theorem peg_defense_exists_unique {rMin A η : ℝ} {ν : ℝ → ℝ}
    (hA : 0 < A) (hη : 0 < η)
    (hcont : Continuous ν) (hanti : Antitone ν) (hnn : ∀ x, 0 ≤ ν x) :
    ∃! rStar : ℝ, rMin ≤ rStar ∧ rStar = rMin + A * ν (η * rStar) := by
  let g : ℝ → ℝ := fun r => r - (rMin + A * ν (η * r))
  have hg_cont : Continuous g :=
    continuous_id.sub (continuous_const.add (continuous_const.mul
      (hcont.comp (continuous_const.mul continuous_id))))
  have hg_strict : StrictMono g := by
    intro r1 r2 hr
    show r1 - (rMin + A * ν (η * r1)) < r2 - (rMin + A * ν (η * r2))
    have hηr : η * r1 ≤ η * r2 := mul_le_mul_of_nonneg_left (le_of_lt hr) (le_of_lt hη)
    have hν : ν (η * r2) ≤ ν (η * r1) := hanti hηr
    nlinarith
  let rHi : ℝ := rMin + A * ν (η * rMin)
  have hrMin_le_rHi : rMin ≤ rHi := by
    have : 0 ≤ A * ν (η * rMin) := mul_nonneg (le_of_lt hA) (hnn _)
    linarith
  have hg_lo : g rMin ≤ 0 := by
    show rMin - (rMin + A * ν (η * rMin)) ≤ 0
    have : 0 ≤ A * ν (η * rMin) := mul_nonneg (le_of_lt hA) (hnn _)
    linarith
  have hg_hi : 0 ≤ g rHi := by
    show rHi - (rMin + A * ν (η * rHi)) ≥ 0
    have hηr : η * rMin ≤ η * rHi := mul_le_mul_of_nonneg_left hrMin_le_rHi (le_of_lt hη)
    have hν : ν (η * rHi) ≤ ν (η * rMin) := hanti hηr
    dsimp [rHi]
    nlinarith
  have h0_mem : (0 : ℝ) ∈ Set.Icc (g rMin) (g rHi) := ⟨hg_lo, hg_hi⟩
  have hIVT := intermediate_value_Icc hrMin_le_rHi hg_cont.continuousOn h0_mem
  rcases hIVT with ⟨rStar, hrStar_mem, hg_zero⟩
  refine ⟨rStar, ⟨hrStar_mem.1, by linarith [show rStar - (rMin + A * ν (η * rStar)) = 0 from hg_zero]⟩, ?_⟩
  intro r2 hr2
  have hg2 : g r2 = 0 := by
    show r2 - (rMin + A * ν (η * r2)) = 0
    linarith [hr2.2]
  exact hg_strict.injective (hg2.trans hg_zero.symm)

theorem peg_defense_mono_A {rMin A1 A2 η r1 r2 : ℝ} {ν : ℝ → ℝ}
    (hη : 0 < η) (hanti : Antitone ν) (hnn : ∀ x, 0 ≤ ν x)
    (hA2 : 0 ≤ A2) (hA : A1 ≤ A2)
    (hr1 : r1 = rMin + A1 * ν (η * r1))
    (hr2 : r2 = rMin + A2 * ν (η * r2)) :
    r1 ≤ r2 := by
  by_contra hlt
  push Not at hlt
  have hηr : η * r2 ≤ η * r1 := mul_le_mul_of_nonneg_left (le_of_lt hlt) (le_of_lt hη)
  have hν : ν (η * r1) ≤ ν (η * r2) := hanti hηr
  have hA1_le : A1 * ν (η * r1) ≤ A2 * ν (η * r1) :=
    mul_le_mul_of_nonneg_right hA (hnn _)
  have hA2_le : A2 * ν (η * r1) ≤ A2 * ν (η * r2) :=
    mul_le_mul_of_nonneg_left hν hA2
  linarith

theorem peg_defense_mono_rMin {rMin1 rMin2 A η r1 r2 : ℝ} {ν : ℝ → ℝ}
    (hA : 0 ≤ A) (hη : 0 < η) (hanti : Antitone ν)
    (hmin : rMin1 ≤ rMin2)
    (hr1 : r1 = rMin1 + A * ν (η * r1))
    (hr2 : r2 = rMin2 + A * ν (η * r2)) :
    r1 ≤ r2 := by
  by_contra hlt
  push Not at hlt
  have hηr : η * r2 ≤ η * r1 := mul_le_mul_of_nonneg_left (le_of_lt hlt) (le_of_lt hη)
  have hν : ν (η * r1) ≤ ν (η * r2) := hanti hηr
  have hA_le : A * ν (η * r1) ≤ A * ν (η * r2) := mul_le_mul_of_nonneg_left hν hA
  linarith

end LiquityV2
