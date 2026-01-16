/-
Copyright (c) 14.01.2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/

import Mathlib.Tactic

/-
This file formalises a generic, computable binary search implementation.
It finds the largest integer `k` in the range `[low, high]` such that `p k` is true.

Assumptions on `p`:
- `p` must be monotone: if `p k` is true, then `p j` is true for all `j ≤ k`.
- `p low` is assumed to be true.
-/

-- We use a `fuel` argument to satisfy Lean's termination checker for structural recursion.
-- In practice, `fuel` just needs to be larger than `log2(high - low)`.
def binary_search_last_true_aux (p : ℕ → Bool) (low high fuel : ℕ) : ℕ :=
  match fuel with
  | 0 => low -- Should not be reached if fuel is sufficient
  | n + 1 =>
    if low >= high then
      low
    else
      -- We choose mid to bias towards the upper half to avoid infinite loops when low + 1 = high
      let mid := (low + high + 1) / 2
      if p mid then
        -- mid satisfies the property, so the answer is at least mid.
        -- We search in [mid, high]
        binary_search_last_true_aux p mid high n
      else
        -- mid does not satisfy the property, so the answer is strictly less than mid.
        -- We search in [low, mid - 1]
        binary_search_last_true_aux p low (mid - 1) n

/--
  Finds the largest `k` in `[0, bound]` such that `p k` is true.
  Returns 0 if `p 0` is false or if the range is invalid.
-/
def binary_search_last_true (p : ℕ → Bool) (bound : ℕ) (_ : p 0 = true) : ℕ :=
  -- Fuel: bound + 1 is strictly sufficient (linear), though log is enough,
  -- (but this changes nothing in the complexity).
  -- We pass bound + 1 to be safe and simple.
  binary_search_last_true_aux p 0 bound (bound + 1)

-- Correctness lemma for binary_search_last_true: that is
-- it returns the largest k in [0, bound] such that p k is true.
lemma binary_search_last_true_aux_spec (p : ℕ → Bool) (low high fuel : ℕ)
    (h_monotone : ∀ m n, m ≤ n → p n = true → p m = true)
    (h_low : p low = true)
    (h_le : low ≤ high)
    (h_fuel : high - low < fuel) :
    low ≤ binary_search_last_true_aux p low high fuel ∧
    binary_search_last_true_aux p low high fuel ≤ high ∧
    p (binary_search_last_true_aux p low high fuel) = true ∧
    ∀ n, n ≤ high → p n = true → n ≤ binary_search_last_true_aux p low high fuel := by
  induction fuel generalizing low high
  · apply False.elim (Nat.not_lt_zero _ h_fuel)
  · rename_i n ih
    rw [binary_search_last_true_aux]
    split_ifs with h_cond
    · have h_eq : low = high := Nat.le_antisymm h_le h_cond
      subst h_eq
      simp only [le_refl, true_and, h_low]
      intros n hn _
      exact hn
    · push_neg at h_cond
      dsimp only [Lean.Elab.WF.paramLet]
      let mid := (low + high + 1) / 2
      have h_mid_gt_low : low < mid := by
        rw [Nat.lt_div_iff_mul_lt (by decide)]
        simp only [Nat.add_one_sub_one, add_tsub_cancel_right]
        calc
          low * 2 = low + low := Nat.mul_two low
          _ < low + high := Nat.add_lt_add_left h_cond low
      have h_mid_le_high : mid ≤ high := by
        apply Nat.div_le_of_le_mul
        linarith
      split_ifs with h_p_mid
      · specialize ih mid high h_p_mid h_mid_le_high (by omega)
        obtain ⟨h1, h2, h3, h4⟩ := ih
        constructor
        · exact Nat.le_trans h_mid_gt_low.le h1
        · exact ⟨h2, ⟨h3, h4⟩⟩
      · have h_le_mid_1 : low ≤ mid - 1 := Nat.le_pred_of_lt h_mid_gt_low
        have h_mid_sub_1_lt_high : mid - 1 < high :=
          Nat.lt_of_lt_of_le (Nat.pred_lt (Nat.ne_of_gt (Nat.lt_of_le_of_lt (Nat.zero_le _) h_mid_gt_low))) h_mid_le_high
        specialize ih low (mid - 1) h_low h_le_mid_1 (by omega)
        obtain ⟨h1, h2, h3, h4⟩ := ih
        constructor
        · exact h1
        · constructor
          · exact Nat.le_trans h2 (Nat.le_trans (Nat.pred_le mid) h_mid_le_high)
          · constructor
            · exact h3
            · intro n hn_le hpn
              cases Nat.lt_or_ge n mid with
              | inl h_lt =>
                apply h4
                · apply Nat.le_pred_of_lt h_lt
                · exact hpn
              | inr h_ge =>
                have : p mid = true := h_monotone mid n h_ge hpn
                rw [this] at h_p_mid
                contradiction

-- Specialization of the above lemma to binary_search_last_true
lemma binary_search_last_true_spec (p : ℕ → Bool) (bound : ℕ)
    (h_monotone : ∀ m n, m ≤ n → p n = true → p m = true)
    (h_p0 : p 0 = true) :
    let k := binary_search_last_true p bound h_p0
    k ≤ bound ∧ p k = true ∧ ∀ n, n ≤ bound → p n = true → n ≤ k := by
  dsimp [binary_search_last_true]
  have h_fuel : bound - 0 < bound + 1 := by simp only [tsub_zero, lt_add_iff_pos_right, zero_lt_one]
  have h_le : 0 ≤ bound := Nat.zero_le bound
  have spec := binary_search_last_true_aux_spec p 0 bound (bound + 1) h_monotone h_p0 h_le h_fuel
  exact ⟨spec.2.1, spec.2.2⟩
