/-
Copyright (c) 14.01.2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/

import Mathlib.Tactic

/-!
# Klazar's Ackermann Hierarchy

This file defines the specific Ackermann hierarchy used in Klazar's proof for N_5(n).
We cannot use `Mathlib.Computability.Ackermann` because the base cases and recursion
scheme differ (e.g., Klazar uses F_1(n) = 2n, while standard Ackermann is n+2).
-/

namespace KlazarAckermann

/--
The function F_k(n) defined recursively.
Base case: F_1(n) = 2n.
Recursive step: F_k(n) = F_{k-1}^(n) (1) (n applications of F_{k-1}).
-/
def F (k n : ℕ) : ℕ :=
  match k with
  | 0 => 0 -- Arbitrary base for 0, Klazar starts at k=1.
  | 1 => 2 * n
  | k' + 1 => (F k' ·)^[n] 1

-- Check: F_2(n) = 2^n
example (n : ℕ) : F 2 n = 2^n := by
  simp only [F, mul_left_iterate, mul_one]

-- For k ≥ 1, n ≥ 1, 1 ≤ F k n.
lemma F_iterate_ge_one {k n : ℕ} (hk : k ≥ 1) (hn : n ≥ 1) :
    1 ≤ F k n := by
  induction k generalizing n
  · contradiction
  · rename_i k ih
    by_cases hk0 : k = 0
    · subst hk0
      simp [F]
      linarith
    · have k_ge_1 : k ≥ 1 := by omega
      simp [F]
      have iter_ge_one (m : ℕ) : 1 ≤ (F k ·)^[m] 1 := by
        induction m with
        | zero => simp
        | succ m ihm =>
          rw [Function.iterate_succ_apply']
          apply ih k_ge_1 ihm
      apply iter_ge_one

-- From the above result, we deduce that for k ≥ 1 and n ≥ 1, F_k(n) is inflationary (n < F_k(n)).
lemma F_inflationary {k n : ℕ} (hk : k ≥ 1) (hn : n ≥ 1) :
    n < F k n := by
  induction k generalizing n
  · simp_all only [ge_iff_le, nonpos_iff_eq_zero, one_ne_zero]
  · rename_i k ih
    by_cases hk : k = 0
    · simp_all only [ge_iff_le, nonpos_iff_eq_zero, one_ne_zero, IsEmpty.forall_iff,
      zero_add, le_refl, F]
      linarith
    · have k_pos : k ≥ 1 := by omega
      simp_all [F]
      induction n
      · contradiction
      · rename_i n ih_n
        by_cases h_n : n = 0
        · simp_all only [nonpos_iff_eq_zero, one_ne_zero, Function.iterate_zero, id_eq,
          zero_lt_one, implies_true, zero_add, le_refl, Function.iterate_one]
        · have n_pos : n ≥ 1 := by omega
          have : (n < (F k .)^[n] 1) ∧ ((F k .)^[n] 1 < F k ((F k .)^[n] 1)):= by
            constructor
            · apply ih_n n_pos
            · apply ih
              have := @F_iterate_ge_one (k+1) n (by linarith) n_pos
              simp_all only [forall_const, le_add_iff_nonneg_left, zero_le, ge_iff_le, F]
          rw [Function.iterate_succ_apply']
          linarith

-- F k . is monotonic
lemma F_monotonic_n (k n : ℕ) : F k n ≤ F k (n + 1) := by
  cases k with
  | zero => simp only [F, le_refl]
  | succ k' =>
    cases k' with
    | zero => simp only [F, Nat.ofNat_pos, mul_le_mul_iff_right₀, le_add_iff_nonneg_right, zero_le]
    | succ k'' =>
      simp [F, Function.iterate_succ_apply']
      apply le_of_lt
      refine @F_inflationary (k'' + 1) (F (k''+2) n) (by omega) ?_
      change 1 ≤ F (k'' + 2) n
      cases n with
      | zero => simp only [F, Function.iterate_zero, id_eq, le_refl]
      | succ n => apply F_iterate_ge_one (by omega) (by simp only [ge_iff_le,
        le_add_iff_nonneg_left, zero_le])

-- F . n is monotonic for n ≥ 1
lemma F_monotonic_k (k n : ℕ) (h : n ≥ 1) : F k n ≤ F (k + 1) n := by
  cases k with
  | zero => simp [F]
  | succ k =>
    cases n with
    | zero => contradiction
    | succ n =>
      cases n with
      | zero =>
        simp [F]
      | succ n =>
        calc
          F (k + 1) (n + 2) ≤ F (k + 1) (F (k + 2) (n + 1)) := by
            apply monotone_nat_of_le_succ (F_monotonic_n (k+1))
            have := @F_inflationary (k+2) (n+1) (by omega) (by omega)
            linarith
          _ = F (k + 2) (n + 2) := by
            simp [F, Function.iterate_succ_apply']

-- The diagonal Ackermann function F_ω(n) = F_n(n).
def F_omega (n : ℕ) : ℕ := F n n

-- Let the boolean property P(k, n, m) be defined as F_k(m) ≥ n.
def P (k n : ℕ) : ℕ → Prop := λ m => n ≤ F k m

-- This property is decidable because F is computable and ≤ is decidable on ℕ.
instance P_decidable (k n m : ℕ) : Decidable (P k n m) := by
  unfold P
  infer_instance

lemma alpha_exists (k n : ℕ) (hk : k ≥ 1) : ∃ m, n ≤ F k m := by
  induction n
  · use 0; simp only [zero_le]
  · rename_i n _
    use n + 1
    have := @F_inflationary k (n+1) hk (by omega)
    linarith

--The inverse function α_k(n) = min { m : F_k(m) ≥ n }.
def alpha (k n : ℕ) (hk : k ≥ 1) : ℕ :=
  @Nat.find (P k n) (P_decidable k n) (alpha_exists k n hk)

-- Some example evaluations of α_4(n)
#eval alpha 4 10 (by norm_num)
#eval alpha 4 100 (by norm_num)
#eval alpha 4 1000 (by norm_num)
#eval alpha 4 10000 (by norm_num)

-- For k ≥ 1, α_k(n) satisfies F_k(α_k(n)) ≥ n.
lemma alpha_spec (k n : ℕ) (hk : k ≥ 1) : n ≤ F k (alpha k n hk) :=
  Nat.find_spec (alpha_exists k n hk)

-- Let the boolean property P_ω(n, m) be defined as F_ω(m) ≥ n.
def P_omega (n : ℕ) : ℕ → Prop := λ m => n ≤ F_omega m

-- This property is decidable because F_omega is computable and ≤ is decidable on ℕ.
instance P_omega_decidable (n m : ℕ) : Decidable (P_omega n m) := by
  unfold P_omega
  infer_instance

-- The inverse diagonal function α(n) = α_ω(n) = min { m : F_omega (m) ≥ n }.
def alpha_omega (n : ℕ) : ℕ :=
  @Nat.find (P_omega n) (P_omega_decidable n) (by
    have : ∃ m, n ≤ F_omega m := by
      induction n
      · use 0; simp only [zero_le]
      · rename_i n _
        use n + 1
        have := @F_inflationary (n + 1) (n + 1) (by omega) (by omega)
        rw [<- F_omega] at this
        linarith
    exact this)

-- Some example evaluation of α_ω(n)
#eval alpha_omega 10

-- For all n, α_ω(n) satisfies F_ω(α_ω(n)) ≥ n.
lemma alpha_omega_spec (n : ℕ) : n ≤ F_omega (alpha_omega n) :=
  Nat.find_spec (by
    have : ∃ m, n ≤ F_omega m := by
      induction n
      · use 0; simp only [zero_le]
      · rename_i n _
        use n + 1
        have := @F_inflationary (n + 1) (n + 1) (by omega) (by omega)
        rw [<- F_omega] at this
        linarith
    exact this)

-- For k ≥ 1, α k . is monotonic in n.
lemma alpha_monotonic_n (k n: ℕ) (hk : k ≥ 1) :
    alpha k n hk ≤ alpha k (n+1) hk := by
  rw [alpha]
  apply Nat.find_le
  apply le_trans (Nat.le_succ n) (alpha_spec k (n+1) hk)

-- For all n, α . n is monotonic in k for k ≥ 1.
lemma alpha_monotonic_k (k n : ℕ) (hk : k ≥ 1) :
    alpha (k + 1) n (by linarith) ≤ alpha k n hk := by
  rw [alpha]
  apply Nat.find_le
  generalize h_m : alpha k n hk = m
  have h_spec : n ≤ F k m := by
    rw [← h_m]
    exact alpha_spec k n hk
  unfold P
  by_cases hm : m = 0
  · subst hm
    -- Case m = 0: Since k ≥ 1, k+1 ≥ 2, so F (k+1) 0 = 1.
    have F_succ_k_0 : F (k+1) 0 = 1 := by
      cases k
      · contradiction
      · rename_i k'
        simp [F]
    rw [F_succ_k_0]
    cases k
    · contradiction
    · rename_i k'
      cases k'
      · -- k = 1. F 1 0 = 0, so n ≤ 0 implies n = 0. 1 ≥ 0 holds.
        simp [F] at h_spec
        linarith
      · -- k ≥ 2. F k 0 = 1, so n ≤ 1. 1 ≥ n holds.
        simp [F] at h_spec
        exact h_spec
  · -- Case m ≥ 1: Use monotonicity of F in k.
    have m_ge_1 : m ≥ 1 := by omega
    have mono := F_monotonic_k k m m_ge_1
    exact le_trans h_spec mono

-- For example, α 1 n = ⌈n/2⌉
example (n : ℕ) : alpha 1 n (by norm_num) = (n + 1) / 2 := by
  rw [alpha]
  apply (Nat.find_eq_iff (alpha_exists 1 n (by norm_num))).mpr
  constructor
  · simp only [F]
    omega
  · intro m hm
    simp only [F, not_le]
    omega

-- For example, α 2 n = ⌈log2 n⌉.
lemma alpha_two_eq_clog (n : ℕ) : alpha 2 n (by norm_num) = Nat.clog 2 n := by
  rw [alpha]
  apply (Nat.find_eq_iff (alpha_exists 2 n (by norm_num))).mpr
  constructor
  · simp_all only [F, mul_left_iterate, mul_one]
    apply Nat.le_pow_clog (by linarith)
  · intro m hm
    simp_all only [F, not_le, mul_left_iterate, mul_one]
    apply (Nat.lt_clog_iff_pow_lt (by linarith)).1 hm

-- F k m = F (k-1) (F k (m-1)) for k ≥ 2 and m ≥ 1.
lemma F_recurrence (k m : ℕ) (hk : k ≥ 2) (hm : m ≥ 1) :
    F k m = F (k - 1) (F k (m - 1)) := by
  cases k <;> try contradiction
  rename_i k'
  cases k' <;> try contradiction
  rename_i k''
  nth_rw 1 [show m = (m - 1) + 1 by omega]
  simp only [F, Function.iterate_succ_apply']
  simp_all only [ge_iff_le, le_add_iff_nonneg_left, zero_le, add_tsub_cancel_right]

-- For every n ≥ 3 and k ≥ 2, α k (alpha (k-1) n) = (α k n) - 1.
lemma alpha_recursive_relation (n k : ℕ) (hn : n ≥ 3) (hk : k ≥ 2) :
    alpha k (alpha (k - 1) n (by omega)) (by linarith) = alpha k n (by linarith) - 1 := by
  apply le_antisymm
  /-
  We have that α_k(α_{k-1}(n)) is the minimal m such that
  F_k(m) ≥ α_{k-1}(n), so m-1 is maximal for F_k(m-1) < α_{k-1}(n),
  which means F_k(m) = F_{k-1}(F_k(m-1)) < n, so m < α_k(n) and thus m ≤ α_k(n) - 1.
  -/
  · set m := alpha k (alpha (k - 1) n (by omega)) (by linarith)
    have h_alpha_pos : 0 < alpha k n (by linarith) := by
      by_contra h
      simp only [not_lt, nonpos_iff_eq_zero] at h
      have spec := alpha_spec k n (by linarith)
      rw [h] at spec
      -- F k 0 = 1 for k >= 2
      have F0 : F k 0 = 1 := by
        cases k <;> try contradiction
        rename_i k'
        cases k' <;> try contradiction
        simp only [F, Function.iterate_zero, id_eq]
      rw [F0] at spec
      linarith
    by_cases hm : m = 0
    · rw [hm]; omega
    · have m_eq : m = (m - 1) + 1 := by omega
      have h1 : F k (m - 1) < alpha (k - 1) n (by omega) := by
        have prop := Nat.find_min (alpha_exists k (alpha (k - 1) n (by omega))
          (by linarith)) (show m - 1 < m by omega)
        simp only [not_le] at prop
        exact prop
      have h2 : F (k - 1) (F k (m - 1)) < n := by
        have prop := Nat.find_min (alpha_exists (k - 1) n (by omega)) h1
        simp only [not_le] at prop
        exact prop
      have h3 : F k m = F (k - 1) (F k (m - 1)) := by
        apply F_recurrence k m (by linarith) (by omega)
      rw [←h3] at h2
      have m_lt : m < alpha k n (by linarith) := by
        by_contra h_ge
        simp only [not_lt] at h_ge
        have mono := monotone_nat_of_le_succ (F_monotonic_n k)
        have F_ge := mono h_ge
        have spec := alpha_spec k n (by linarith)
        linarith
      omega
  /-
  Conversely, let m = α_k(α_{k-1}(n)). We want to show α_k(n) - 1 ≤ m, i.e., α_k(n) ≤ m + 1.
  It suffices to show that F_k(m + 1) ≥ n. We have F_k(m + 1) = F_{k-1}(F_k(m)).
  By definition of α, because m = α_k(α_{k-1}(n)), we have F_k(m) ≥ α_{k-1}(n).
  Since F_{k-1} is monotonic, F_{k-1}(F_k(m)) ≥ F_{k-1}(α_{k-1}(n)).
  By definition of α, F_{k-1}(α_{k-1}(n)) ≥ n.
  Therefore F_k(m + 1) ≥ n, which implies α_k(n) ≤ m + 1.
  -/
  · set m := alpha k (alpha (k - 1) n (by omega)) (by linarith)
    have h_ineq : alpha k n (by linarith) ≤ m + 1 := by
      rw [alpha]
      apply Nat.find_le
      dsimp [P]
      have recurrence : F k (m + 1) = F (k - 1) (F k m) := by
        cases k <;> try contradiction
        rename_i k'
        cases k' <;> try contradiction
        simp [F, Function.iterate_succ_apply']
      rw [recurrence]
      have h1 : alpha (k - 1) n (by omega) ≤ F k m :=
        alpha_spec k (alpha (k - 1) n (by omega)) (by linarith)
      have h2 : F (k - 1) (alpha (k - 1) n (by omega)) ≤ F (k - 1) (F k m) :=
        monotone_nat_of_le_succ (F_monotonic_n (k - 1)) h1
      have h3 : n ≤ F (k - 1) (alpha (k - 1) n (by omega)) :=
        alpha_spec (k - 1) n (by omega)
      linarith
    omega

#check Nat.lt_pow_self
lemma Nat.le_pow_self_boosted_2 (n : ℕ) (hn : n ≥ 3) : 2^(n-1) ≥ n + 1 := by
  induction' n with d hd
  . contradiction -- n >= 3, so n cannot be 0
  . by_cases h' : d < 3
    . -- Handle base cases n=3 (d=2) : omega handle ranges
      interval_cases d <;> omega
    . -- Inductive step for d >= 3
      rw [Nat.not_lt] at h'
      have IH := hd h'
      calc
        2 ^ d = 2 * 2 ^ (d - 1) := by
          nth_rw 1 [show d = (d - 1) + 1 by omega]
          rw [pow_succ']
        _ ≥ 2 * (d + 1)         := by
          simp_all only [ge_iff_le, imp_self, Nat.reduceLeDiff, Nat.ofNat_pos,
            mul_le_mul_iff_right₀]
        _ = 2 * d + 2           := by ring
        _ ≥ d + 1 + 1           := by omega -- d >= 3 implies 2d+2 >= d+2

-- For k ≥ 1 and n ≥ 3 it holds F k+1 n ≥ F k n+ 1.
lemma F_succ_ge (k n : ℕ) (hk : k ≥ 1) (hn : n ≥ 3) :
    F (k + 1) n ≥ F k (n + 1) := by
  -- F (k+1) n = F k (F (k+1) (n-1))
  have h_rec : F (k + 1) n = F k (F (k + 1) (n - 1)) := by
    apply F_recurrence (k + 1) n (by omega) (by omega)
  rw [h_rec]
  -- Applying monotonicity of F k
  apply monotone_nat_of_le_succ (F_monotonic_n k)
  have n_ge_1 : n - 1 ≥ 1 := by omega
  -- Show F (k+1) (n-1) >= 2^(n-1)
  have h_mono_k : Monotone (fun i => F i (n - 1)) :=
    monotone_nat_of_le_succ (fun i => F_monotonic_k i (n - 1) n_ge_1)
  have h_k_ge_2 : 2 ≤ k + 1 := by omega
  have h_ge_F2 : F (k + 1) (n - 1) ≥ F 2 (n - 1) := h_mono_k h_k_ge_2
  rw [show F 2 (n - 1) = 2 ^ (n - 1) by simp [F, mul_left_iterate, mul_one]] at h_ge_F2
  -- Show 2^(n-1) >= n+1
  have h_exp : 2 ^ (n - 1) ≥ n + 1 := by apply Nat.le_pow_self_boosted_2 n hn
  exact le_trans h_exp h_ge_F2

-- We thus have the chain of inequalities
-- F (k+1) n ≥ F k (n+1) ≥ F (k-1) (n+2) ≥ ... ≥ F 1 (k+n)
lemma F_chain_ineq (k n : ℕ) (hk : k ≥ 1) (hn : n ≥ 3) : F (k + 1) n ≥ F 1 (k + n) := by
  induction k generalizing n
  · contradiction
  · rename_i k ih
    cases k
    · rw [add_comm 1 n]
      apply F_succ_ge 1 n (by norm_num) hn
    · rename_i k'
      have k_ge_1 : k' + 1 ≥ 1 := by omega
      specialize ih (n + 1) k_ge_1 (by omega)
      calc
        F (k' + 3) n ≥ F (k' + 2) (n + 1) := F_succ_ge (k' + 2) n (by omega) hn
        _            ≥ F 1 (k' + 1 + (n + 1)) := ih
        _            = F 1 (k' + 2 + n) := by congr 1; omega

-- For every n ≥ 1, α_{α(n)+1}(n) ≤ 4.
lemma alpha_nested_bound (n : ℕ) (hn : n ≥ 1) :
    alpha ((alpha_omega n) + 1) n (by omega) ≤ 4 := by
  let k := alpha_omega n
  have hk : k ≥ 1 := by
    unfold k
    by_contra h_contra
    simp only [ge_iff_le, not_le, Nat.lt_one_iff] at h_contra
    have h_spec := alpha_omega_spec n
    rw [h_contra] at h_spec
    simp only [F_omega, F] at h_spec
    linarith
  have h : F (k + 1) 3 > k := by
    calc k < k + 3 := by linarith
      _ ≤ F 1 (k + 3) := by
        simp [F]
      _ ≤ F (k + 1) 3 := by
        apply F_chain_ineq k 3 hk (by norm_num)
  have : F (k + 1) 4 ≥ F k k := by
    calc F (k + 1) 4 = F k (F (k + 1) 3) := by simp only [F_recurrence (k + 1) 4 (by omega)
        (by norm_num),
      add_tsub_cancel_right, Nat.add_one_sub_one]
      _ ≥ F k k := by
        apply monotone_nat_of_le_succ (F_monotonic_n k)
        omega
  rw [alpha]
  apply Nat.find_le
  dsimp [P]
  suffices n ≤ F k k from by linarith
  rw [← F_omega]
  unfold k
  exact alpha_omega_spec n

end KlazarAckermann
