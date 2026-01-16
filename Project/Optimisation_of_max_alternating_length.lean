/-
Copyright (c) 14.01.2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/

import Project.Generic_Binary_Search
import Project.Basic_Definitions_and_Lemmas

/-
This file formalises an "optimised" computation of the maximum length of an
alternating subsequence. Although Lean is not focused on efficiency of computation.
-/

/-
  OPTIMIZATION EXPLANATION:
  -------------------------
  We wish to compute the length of the longest alternating subsequence in
  a more efficient way and prove its correctness.

0. Trivial version:
    Computing all alternating subsequences (using sublists and filtering)
    and then taking the maximum length. This is clearly correct but the
    number of subsequences is exponential in the length of the list.
    This algorithm runs in time Ω(2^n).

1.  BINARY SEARCH:
    While the property of "existence of an alternating subsequence of length k" is
    indeed downward closed, using binary search here is not the optimal version.
    The problem is in the binary search (which takes o(log(v.length)))
    to check if an alternating subsequence of length `k` for any (0 ≤ k ≤ v.length)
    exists (the check function) requires O(v.length^2) time in the worst case
    (if I am not mistaken). The total complexity becomes O(v.length^2 * log v.length).

2.  Dynamic Programming Approach:
    We use a dynamic programming approach equivalent to iterating all pairs:
    The idea (eliminating trivial cases) is to maintain for every pair of distinct
    symbols (a, b) the length of the longest alternating subsequence ending with a
    (resp. b). The maximum over all pairs (a, b) will give the answer. The complexity
    is O(v.length * U) where U is the number of unique symbols
    because for each of the v.length elements of the list we update O(U) pairs (a, b): that is
    we check if the current element is a or b and update accordingly the length of the
    longest alternating subsequence ending with a (resp. b).
    - If U is small (e.g. alphabet), this is effectively O(v.length).
    - If U is large (all unique), this is O(v.length^2).

    Although the dynamic programming approach is more efficient in practice,
    its implementation and proof of correctness is more involved compared
    to the Binary Search approach. Moreover, we will use these computations
    for Davenport-Schinzel sequences where U can be v.length so it will run in
    O(v.length^2) in the worst case, and binary search will again be used in the
    future (to find the maximum length of a Davenport-Schinzel sequence)
-/

-- The predicate for binary search: exists alternating subsequence of length k.
-- It checks if there exists a sublist of length k which is alternating.
-- We use `List.any` which short-circuits: it returns `true` as soon as it finds
-- one alternating sublist, without checking the rest.
-- However, note that `v.sublistsLen k` constructs all sublists upfront (eager evaluation).
-- The worst-case complexity (when the answer is false) involves checking all (v.length choose k) sublists.
-- so a complexity of O((v.length choose k) * cost of is_alternating_b) in the worst case.
def exists_alternating_of_length_b {α : Type} [DecidableEq α] (v : List α) (k : ℕ) : Bool :=
  (v.sublistsLen k).any is_alternating_b

-- Correctness of the predicate
lemma exists_alternating_of_length_b_iff {α : Type} [DecidableEq α] (v : List α) (k : ℕ) :
  exists_alternating_of_length_b v k = true ↔ ∃ u, u ∈ alternating_subsequences v ∧ u.length = k := by
  unfold exists_alternating_of_length_b
  simp only [List.any_eq_true, List.mem_sublistsLen]
  constructor
  · intro h
    obtain ⟨u, ⟨h_sub, h_len⟩, h_alt_b⟩ := h
    use u
    constructor
    · unfold alternating_subsequences
      rw [is_alternating_b_iff] at h_alt_b
      exact ⟨h_sub, h_alt_b⟩
    · exact h_len
  · intro h
    obtain ⟨u, h_mem, h_len⟩ := h
    use u
    constructor
    · constructor
      · exact h_mem.1
      · exact h_len
    · rw [is_alternating_b_iff]
      exact h_mem.2

-- Monotonicity of the predicate
lemma exists_alternating_of_length_monotonic {α : Type} [DecidableEq α] (v : List α)
  (m n : ℕ) (h_le : m ≤ n) (h_n : exists_alternating_of_length_b v n = true) :
  exists_alternating_of_length_b v m = true := by
  rw [exists_alternating_of_length_b_iff] at h_n ⊢
  obtain ⟨u, h_mem, h_len⟩ := h_n
  obtain ⟨h_u_sub, h_u_alt⟩ := h_mem
  have h_m_le_len : m ≤ u.length := by rw [h_len]; exact h_le
  let w := u.take m
  have h_w_alt_len := alternating_subsequence_of_smaller_length u h_u_alt m h_m_le_len
  use w
  constructor
  · unfold alternating_subsequences
    constructor
    · exact List.Sublist.trans (List.take_sublist m u) h_u_sub
    · exact h_w_alt_len.left
  · exact h_w_alt_len.right

-- p 0 is true because the empty list is an alternating subsequence of length 0
lemma exists_alternating_of_length_b_0 {α : Type} [DecidableEq α] (v : List α) :
  exists_alternating_of_length_b v 0  = true := by
  rw [exists_alternating_of_length_b_iff]
  exact ⟨[], empty_mem_alternating_subsequences v, rfl⟩

-- Optimised computation using binary search
def max_alternating_length_b_opt {α : Type} [DecidableEq α] (v : List α) : ℕ :=
  binary_search_last_true (exists_alternating_of_length_b v) v.length
    (exists_alternating_of_length_b_0 v)

-- Correctness of the optimised computation
lemma max_alternating_length_eq_max_alternating_length_b_opt {α : Type} [DecidableEq α] (v : List α) :
  max_alternating_length_b_opt v = max_alternating_length v := by
  let p := exists_alternating_of_length_b v
  have h_mono : ∀ m n, m ≤ n → p n = true → p m = true := exists_alternating_of_length_monotonic v
  have h_p0 : p 0 = true := exists_alternating_of_length_b_0 v
  let k := binary_search_last_true p v.length h_p0
  -- By definition `max_alternating_length_b_opt` is equal to our local call
  have h_eq : max_alternating_length_b_opt v = k := by rfl
  have spec := binary_search_last_true_spec p v.length h_mono h_p0
  dsimp only [p] at spec
  simp only [exists_alternating_of_length_b_iff] at spec
  -- spec now contains the existential for k, and the implication for other n
  unfold max_alternating_length
  apply le_antisymm
  · -- k ≤ max
    apply Finset.le_max'
    simp only [Set.Finite.mem_toFinset]
    unfold alternating_subsequences_lengths
    simp only [Set.mem_setOf_eq]
    exact spec.2.1
  · -- max ≤ k
    apply Finset.max'_le
    intro n hn
    simp only [Set.Finite.mem_toFinset] at hn
    unfold alternating_subsequences_lengths at hn
    simp only [Set.mem_setOf_eq] at hn
    obtain ⟨u, h_mem, h_len⟩ := hn
    have h_n_le_len : n ≤ v.length := by
      rw [← h_len]
      exact length_le_sublist h_mem.left
    apply spec.2.2 n h_n_le_len
    use u

#eval max_alternating_length_b_opt ([] : List ℕ) -- expected 0
#eval max_alternating_length_b_opt [1,2,1,2,3,1,2] -- expected 6
#eval max_alternating_length_b_opt [1,1,1,1,1] -- expected 1

--#eval max_alternating_length_b_opt [3,1,4,1,5,9,2,6,5,3,5,3,1,4,1,5,9,2,6,5,3,5] -- expected 8 (running time ∼  6.37s)
--#eval max_alternating_length_b [3,1,4,1,5,9,2,6,5,3,5,3,1,4,1,5,9,2,6,5,3,5] -- expected 8 (running time ∼ 11s)
