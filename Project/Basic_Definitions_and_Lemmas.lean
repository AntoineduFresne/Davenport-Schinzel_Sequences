/-
Copyright (c) 14.01.2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/

import Mathlib.Tactic
import Mathlib.Data.List.Dedup
import Mathlib.Data.Finset.Card

/-
This file formalises basic definitions and lemmas about sequences.
-/

/-
Sequences will be seen as lists over a type α. We define basic properties of sequences:
- length
- number of distinct symbols
- being a chain (all symbols distinct)
- being sparse (no two consecutive symbols equal)
- being alternating (sparse and at most two distinct symbols)
We define the set of all alternating subsequences of a given sequence, and the maximum length
of such an alternating subsequence. We also prove some basic lemmas about these definitions.
-/

-- Length of a sequence
#check List.length

section Distinct_Symbols_and_Chains

/-- Number of distinct symbols in a sequence -/
-- The first definition uses deduplication (complexity O(length^2))
def distinct_count_by_dedup {α : Type} [DecidableEq α] (u : List α) : ℕ := u.dedup.length

-- The second definition uses finsets
def distinct_count_by_finset {α : Type} [DecidableEq α] (u : List α) : ℕ := u.toFinset.card

-- Both definition give the same number
lemma distinct_count_by_dedup_eq_distinct_count_by_finset {α : Type} [DecidableEq α] (u : List α) :
  distinct_count_by_dedup u = distinct_count_by_finset u := by
  induction u
  · unfold distinct_count_by_dedup distinct_count_by_finset
    simp only [List.dedup_nil, List.length_nil, List.toFinset_nil, Finset.card_empty]
  · rename_i x xs ih
    unfold distinct_count_by_dedup distinct_count_by_finset
    by_cases h_mem : x ∈ xs
    · have : (x :: xs).dedup = xs.dedup := by
        apply List.dedup_cons_of_mem h_mem
      rw [this]
      have : (x :: xs).toFinset = xs.toFinset := by
        simp only [List.toFinset_cons, List.mem_toFinset, h_mem, Finset.insert_eq_of_mem]
      rw [this]
      exact ih
    · have : (x :: xs).dedup = x :: xs.dedup := by
        apply List.dedup_cons_of_notMem h_mem
      rw [this]
      have : (x :: xs).toFinset = insert x xs.toFinset := by
        simp only [List.toFinset_cons]
      rw [this, Finset.card_insert_of_notMem (by simp only [List.mem_toFinset, h_mem,
        not_false_eq_true])]
      simp only [List.length_cons, Nat.add_right_cancel_iff]
      unfold distinct_count_by_dedup distinct_count_by_finset at ih
      linarith

-- Number of elements is always smaller or equal than the length
lemma distinct_count_le_length {α : Type} [DecidableEq α] (u : List α) :
  distinct_count_by_dedup u ≤ u.length := by
  apply @List.Sublist.length_le α u.dedup u
  exact List.dedup_sublist u

-- In the case of equality, the sequence is called a chain (not to be confused with List.Chain)
def is_chain {α : Type} [DecidableEq α] (u : List α) : Prop :=
  distinct_count_by_dedup u = u.length

-- x :: xs is a chain iff x ∉ xs and xs is a chain
lemma is_chain_cons_iff {α : Type} [DecidableEq α] (x : α) (xs : List α) :
  is_chain (x :: xs) ↔ (x ∉ xs ∧ is_chain xs) := by
  unfold is_chain distinct_count_by_dedup
  constructor
  · intro h
    have : x ∉ xs := by
      by_contra h_mem
      rw [List.dedup_cons_of_mem h_mem] at h
      simp only [List.length_cons] at h
      have : xs.dedup.length ≤ xs.length := by
        apply distinct_count_le_length
      linarith
    constructor
    · exact this
    · have h0 : (x :: xs).dedup = x :: xs.dedup := by
        apply List.dedup_cons_of_notMem this
      rw [h0] at h
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      exact h
  · intro h
    obtain ⟨h_notMem, h_chain_xs⟩ := h
    have : (x :: xs).dedup = x :: xs.dedup := by
      apply List.dedup_cons_of_notMem h_notMem
    rw [this]
    simp only [List.length_cons, Nat.add_right_cancel_iff]
    exact h_chain_xs

-- This permits to define chains in a computable way (complexity O(length^2))
def is_chain_b {α : Type} [DecidableEq α] : List α → Bool
  | [] => true
  | x :: xs => (¬ (xs.contains x)) && is_chain_b xs

-- The boolean version matches the propositional version
lemma is_chain_b_iff {α : Type} [DecidableEq α] (u : List α) :
  is_chain_b u = true ↔ is_chain u := by
  induction u
  unfold is_chain is_chain_b distinct_count_by_dedup
  · simp only [List.dedup_nil, List.length_nil]
  · rename_i x xs ih
    simp only [is_chain_b, List.contains_eq_mem, decide_eq_true_eq, decide_not, Bool.and_eq_true,
      Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, ih, is_chain_cons_iff]

-- The empty list is a chain
lemma is_empty_chain {α : Type} [DecidableEq α] : is_chain ([] : List α) := by
  simp only [is_chain, distinct_count_by_dedup, List.dedup_nil, List.length_nil]

-- Singleton lists are chains
lemma singleton_is_chain {α : Type} [DecidableEq α] (a : α) : is_chain [a] := by
  unfold is_chain distinct_count_by_dedup
  simp only [List.not_mem_nil, not_false_eq_true, List.dedup_cons_of_notMem, List.dedup_nil,
    List.length_cons, List.length_nil]

end Distinct_Symbols_and_Chains

section Sparse_and_Alternating_Sequences

-- A sequence is sparse if no two consecutive elements are equal,
-- we use List.Chain' with the relation "not equal"
def is_sparse {α : Type} [DecidableEq α] (u : List α) : Prop := @List.IsChain α (· ≠ ·) u

-- For deciding/automation, we do the Boolean version of is_sparse:
-- checks that no two consecutive elements are equal (complexity O(length))
def is_sparse_b {α : Type} [DecidableEq α] : List α → Bool
  | [] => true
  | [_] => true
  | a :: b :: t => (a ≠ b) && is_sparse_b (b :: t)

-- The boolean version matches the propositional version
lemma is_sparse_b_iff {α : Type} [DecidableEq α] (u : List α) :
  is_sparse_b u = true ↔ is_sparse u := by
  induction u with
  | nil => simp_all [is_sparse_b, is_sparse]
  | cons x xs ih =>
    cases xs with
    | nil => simp only [is_sparse_b, is_sparse, ne_eq, List.isChain_singleton]
    | cons y ys =>
      simp only [is_sparse_b, Bool.and_eq_true, decide_eq_true_eq, ne_eq]
      rw [ih]
      simp only [is_sparse, ne_eq, List.isChain_cons_cons]

-- A chain is sparse (and hence the empty list is sparse and
-- singleton lists are sparse)
lemma is_chain_implies_is_sparse {α : Type} [DecidableEq α] {u : List α}
  (h : is_chain u) : is_sparse u := by
  dsimp [is_sparse]
  induction u with
  | nil => exact List.isChain_nil
  | cons x xs ih =>
    obtain ⟨h_notMem, h_chain_xs⟩ := (is_chain_cons_iff x xs).1 h
    cases xs with
    | nil => exact List.isChain_singleton x
    | cons y ys =>
      rw [List.isChain_cons_cons]
      constructor
      · intro he
        apply h_notMem
        rw [he]
        apply List.mem_cons_self
      · exact ih h_chain_xs

-- If two sequences are sparse, their concatenation is also sparse provided the last element of the first
-- is different from the first element of the second.
lemma concat_is_sparse {α : Type} [DecidableEq α] (u v : List α)
    (h_u : is_sparse u) (h_v : is_sparse v) (h_diff : u.getLast? ≠ v.head?) :
    is_sparse (u ++ v) := by
  rw [is_sparse, List.isChain_append]
  refine ⟨h_u, h_v, ?_⟩
  intros x hx y hy
  rw [Option.mem_def] at hx hy
  rw [hx, hy] at h_diff
  simp only [ne_eq, Option.some.injEq] at h_diff
  exact h_diff

/-- Checks if the number of distinct elements is at most 2 in linear time O(n) -/
def distinct_count_le_2_aux {α : Type} [DecidableEq α] : List α → List α → Bool
  | [], _ => true
  | x :: xs, seen =>
    if x ∈ seen then distinct_count_le_2_aux xs seen
    else match seen with
         | [] => distinct_count_le_2_aux xs [x]
         | [a] => distinct_count_le_2_aux xs [a, x]
         | _ => false

def distinct_count_le_2_b {α : Type} [DecidableEq α] (u : List α) : Bool :=
  distinct_count_le_2_aux u []

lemma distinct_count_le_2_aux_iff {α : Type} [DecidableEq α] (l seen : List α)
    (h_seen_uniq : seen.Nodup) (h_seen_len : seen.length ≤ 2) :
    distinct_count_le_2_aux l seen = true ↔ (l ++ seen).toFinset.card ≤ 2 := by
  induction l generalizing seen with
  | nil =>
    simp only [distinct_count_le_2_aux, List.nil_append, List.toFinset_card_of_nodup h_seen_uniq,
      h_seen_len]
  | cons x xs ih =>
    unfold distinct_count_le_2_aux
    split_ifs with h_mem
    · rw [ih seen h_seen_uniq h_seen_len]
      simp_all only [List.toFinset_append, List.cons_append, List.toFinset_cons, Finset.mem_union, List.mem_toFinset,
        or_true, Finset.insert_eq_of_mem]
    · match seen with
      | [] =>
        have h_eq : ((x :: xs) ++ []).toFinset = (xs ++ [x]).toFinset := by ext; simp only [List.append_nil,
          List.toFinset_cons, Finset.mem_insert, List.mem_toFinset, List.toFinset_append,
          List.toFinset_nil, insert_empty_eq, Finset.mem_union, Finset.mem_singleton, or_comm]
        rw [h_eq]
        rw [ih [x] (by simp) (by simp)]
      | [a] =>
        rw [show ((x :: xs) ++ [a]).toFinset = (xs ++ [a, x]).toFinset by
             ext y; simp only [List.cons_append, List.toFinset_cons, List.toFinset_append,
               List.toFinset_nil, insert_empty_eq, Finset.mem_insert, Finset.mem_union,
               List.mem_toFinset, Finset.mem_singleton, or_comm, Finset.union_insert, or_left_comm]]
        rw [ih [a, x]]
        · simp only [List.nodup_cons, List.mem_singleton]
          simp only [List.mem_singleton] at h_mem
          exact ⟨Ne.symm h_mem, by simp⟩
        · simp
      | a :: b :: bs =>
        have h3 : ({x, a, b} : Finset α) ⊆ ((x :: xs) ++ (a :: b :: bs)).toFinset := by
          intro y hy
          simp only [Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with rfl | rfl | rfl <;> simp
        have h_card : ({x, a, b} : Finset α).card = 3 := by
          simp only [List.mem_cons, not_or] at h_mem
          simp only [List.nodup_cons, List.mem_cons, not_or] at h_seen_uniq
          rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
          · rw [Finset.mem_singleton]; exact h_seen_uniq.1.1
          · simp only [Finset.mem_insert, h_mem.1, Finset.mem_singleton, h_mem.2.1, or_self,
            not_false_eq_true]
        have : 3 ≤ ((x :: xs) ++ (a :: b :: bs)).toFinset.card :=
          h_card ▸ Finset.card_le_card h3
        simp only [Bool.false_eq_true, List.cons_append, List.toFinset_cons, List.toFinset_append,
          Finset.union_insert, false_iff, not_le, gt_iff_lt]
        simp only [List.cons_append, List.toFinset_cons, List.toFinset_append,
          Finset.union_insert] at this
        linarith

lemma distinct_count_le_2_b_iff {α : Type} [DecidableEq α] (u : List α) :
  distinct_count_le_2_b u = true ↔ distinct_count_by_dedup u ≤ 2 := by
  rw [distinct_count_by_dedup_eq_distinct_count_by_finset]
  unfold distinct_count_le_2_b distinct_count_by_finset
  rw [distinct_count_le_2_aux_iff u [] List.nodup_nil (by simp only [List.length_nil, zero_le])]
  simp only [List.append_nil]

-- A sequence is alternating if it is sparse and contains at most two distinct symbols
-- (and hence the empty list and singleton lists are also alternating)
def is_alternating {α : Type} [DecidableEq α] (u : List α) : Prop :=
  is_sparse u ∧ distinct_count_by_dedup u ≤ 2

-- For deciding/automation, we do the Boolean version of is_alternating (complexity O(length))
def is_alternating_b {α : Type} [DecidableEq α] : List α → Bool :=
  fun u => (is_sparse_b u) && (distinct_count_le_2_b u)

-- The Boolean version matches the propositional version
lemma is_alternating_b_iff {α : Type} [DecidableEq α] (u : List α) :
  is_alternating_b u = true ↔ is_alternating u := by
  constructor
  · intro h
    unfold is_alternating
    unfold is_alternating_b at h
    simp only [Bool.and_eq_true] at h
    constructor
    · apply (is_sparse_b_iff u).1
      exact h.left
    · rw [<- distinct_count_le_2_b_iff]
      exact h.right
  · intro h
    unfold is_alternating at h
    unfold is_alternating_b
    simp only [Bool.and_eq_true]
    constructor
    · apply (is_sparse_b_iff u).2
      exact h.left
    · rw [distinct_count_le_2_b_iff]
      exact h.right

end Sparse_and_Alternating_Sequences

/-
Subsequences are exactly sublist (because of the way sublist are defined in
Lean i.e. a list l is a sublist of a list l' means one can obtain l from l'
by erasing at least 0 elements of l' without reordering).
-/
#check List.Sublist

section Properties_of_Subsequences

-- Length of sublist is less than or equal to length of the list
lemma length_le_sublist {α : Type} {u v : List α} (h : u.Sublist v) :
  u.length ≤ v.length:= by
  apply @List.Sublist.length_le α u v
  exact h

-- Remark: Sublist.dedup is not necessarily a sublist of List.dedup
#eval [1,3].Sublist [1,3,1]
#eval ([1,3].dedup).Sublist ([1,3,1].dedup)

-- Sublist of list which doesn't contain an element of the list has strictly fewer distinct elements
lemma distinct_count_by_dedup_sublist_notMem {α : Type} [DecidableEq α] {u v : List α}
  (h : u.Sublist v) (z : α) (h_notMem : z ∉ u) (h_mem : z ∈ v) :
  distinct_count_by_dedup u < distinct_count_by_dedup v := by
  -- we prove this by switching to finsets using the equivalence lemma
  rw [distinct_count_by_dedup_eq_distinct_count_by_finset u,
    distinct_count_by_dedup_eq_distinct_count_by_finset v]
  unfold distinct_count_by_finset
  have : u.toFinset ⊂ v.toFinset := by
    apply Finset.ssubset_iff.mpr
    use z
    constructor
    · simp only [List.mem_toFinset]
      exact h_notMem
    · apply Finset.subset_iff.mpr
      simp only [Finset.mem_insert, List.mem_toFinset, forall_eq_or_imp]
      constructor
      · exact h_mem
      · intro x h_mem_x
        apply List.Sublist.subset at h
        apply h
        simp_all only
  apply Finset.card_lt_card this

-- Sublist of list has less distinct elements
lemma distinct_count_sublist {α : Type} [DecidableEq α] {u v : List α}
  (h : u.Sublist v) : distinct_count_by_dedup u ≤ distinct_count_by_dedup v := by
   -- we prove this by swtiching to finsets
  rw [distinct_count_by_dedup_eq_distinct_count_by_finset u,
    distinct_count_by_dedup_eq_distinct_count_by_finset v]
  unfold distinct_count_by_finset
  have : u.toFinset ⊆ v.toFinset := by
    apply Finset.subset_iff.mpr
    simp only [List.mem_toFinset]
    grind only [=_ List.contains_iff_mem, List.contains_eq_mem, → List.Sublist.subset, =
      List.subset_def]
  apply Finset.card_le_card this

-- Sublist of a chain is a chain
lemma sublist_of_chain_is_chain {α : Type} [DecidableEq α] {u v : List α}
  (h_sublist : u.Sublist v) (h_chain : is_chain v) : is_chain u := by
  unfold is_chain distinct_count_by_dedup at *
  have h_nodup_v : v.Nodup := by
    rw [← List.dedup_eq_self]
    exact List.Sublist.eq_of_length (List.dedup_sublist v) h_chain
  have h_nodup_u : u.Nodup := List.Nodup.sublist h_sublist h_nodup_v
  rw [List.dedup_eq_self.mpr h_nodup_u]

-- A Sublist of an alternating list is not necessarily sparse!
-- In particular sublist of sparse list are not necessarily sparse.
#eval [1,1].Sublist [1,2,1]
#eval is_alternating_b [1,2,1]
#eval is_alternating_b [1,1]

-- However, if v is sparse, then for any length n smaller than v.length,
-- the sublist of v formed by taking the first element n is a sparse
-- sequence of length n (Downward closed property of sparse sequences).
lemma sparse_subsequence_of_smaller_length {α : Type} [DecidableEq α] (v : List α)
    (h_sparse : is_sparse v) (n : ℕ) (h_len : n ≤ v.length) :
    is_sparse (v.take n) ∧ (v.take n).length = n := by
  constructor
  · exact List.IsChain.take h_sparse n
  · exact List.length_take_of_le h_len

-- The same goes for alternating subsequences
-- (Downward closed property of alternating subsequences).
lemma alternating_subsequence_of_smaller_length {α : Type} [DecidableEq α] (v : List α)
    (h_alt : is_alternating v) (n : ℕ) (h_len : n ≤ v.length) :
    is_alternating (v.take n) ∧ (v.take n).length = n := by
  constructor
  · unfold is_alternating at *
    constructor
    · exact (sparse_subsequence_of_smaller_length v h_alt.left n h_len).left
    · exact le_trans (distinct_count_sublist (List.take_sublist n v)) h_alt.right
  · exact List.length_take_of_le h_len

-- Helper lemma for splitting sublists over append
lemma exists_sublist_split_of_sublist_append {α} {l l1 l2 : List α} (h : l.Sublist (l1 ++ l2)) :
    ∃ s1 s2, s1.Sublist l1 ∧ s2.Sublist l2 ∧ l = s1 ++ s2 := by
  induction l1 generalizing l with
  | nil =>
    simp at h
    exact ⟨[], l, List.Sublist.slnil, h, rfl⟩
  | cons x xs ih =>
    simp only [List.cons_append] at h
    cases h with
    | cons _ h_sub => -- l <+ xs ++ l2 (skip x)
      obtain ⟨s1, s2, hs1, hs2, heq⟩ := ih h_sub
      exact ⟨s1, s2, List.Sublist.cons x hs1, hs2, heq⟩
    | cons₂ _ h_sub => -- l = x::l', l' <+ xs ++ l2 (keep x)
      rename_i l'
      obtain ⟨s1, s2, hs1, hs2, heq⟩ := ih h_sub
      exact ⟨x :: s1, s2, List.Sublist.cons₂ x hs1, hs2, by rw [heq, List.cons_append]⟩

end Properties_of_Subsequences

section Maximum_Length_of_Alternating_Subsequences

-- The set of all alternating subsequences of a sequence v
def alternating_subsequences {α : Type} [DecidableEq α] (v : List α) : Set (List α) :=
  {u | u.Sublist v ∧ is_alternating u}

-- We want to show that this set is finite to take the maximum length later on.
-- Thus we define the finite list of all alternating subsequences of a sequence defined
-- using the Boolean version.
def alternating_subsequences_b {α : Type} [DecidableEq α] (v : List α) : List (List α) :=
  ((v.sublists).filter (λ u => is_alternating_b u))

-- Membership in alternating_subsequences_b matches the propositional definition
lemma mem_alternating_subsequences_iff {α : Type} [DecidableEq α] (v u : List α) :
    u ∈ (alternating_subsequences_b v) ↔ u ∈ alternating_subsequences v := by
    unfold alternating_subsequences_b alternating_subsequences
    simp only [List.mem_filter, List.mem_sublists, Set.mem_setOf_eq, and_congr_right_iff]
    intro h
    apply is_alternating_b_iff

-- Thus alternating_subsequences_b and alternating_subsequences define the same set
lemma alternating_subsequences_eq_alternating_subsequences_b {α : Type} [DecidableEq α] (v : List α) :
  (alternating_subsequences_b v).toFinset = alternating_subsequences v := by
  ext u
  simp only [List.coe_toFinset, Set.mem_setOf_eq]
  exact mem_alternating_subsequences_iff v u

-- In particular, the set of alternating subsequences is finite
lemma alternating_subsequences_finite {α : Type} [DecidableEq α] (v : List α) :
    Set.Finite (alternating_subsequences v) := by
  rw [<- alternating_subsequences_eq_alternating_subsequences_b v]
  apply Finset.finite_toSet

-- The empty list is always an alternating subsequence
lemma empty_mem_alternating_subsequences {α : Type} [DecidableEq α] (v : List α) :
    [] ∈ alternating_subsequences v := by
  unfold alternating_subsequences
  simp only [Set.mem_setOf_eq, List.nil_sublist, true_and]
  unfold is_alternating is_sparse distinct_count_by_dedup
  simp only [ne_eq, List.isChain_nil, List.dedup_nil, List.length_nil, zero_le, and_self]

-- Definition of the set of length of alternating subsequences
def alternating_subsequences_lengths {α : Type} [DecidableEq α] (v : List α) : Set ℕ :=
  {n | ∃ u : List α, u ∈ alternating_subsequences v ∧ u.length = n}

-- Boolean version of the set of lengths of alternating subsequences
def alternating_subsequences_lengths_b {α : Type} [DecidableEq α] (v : List α) : List ℕ :=
  ((alternating_subsequences_b v).map (λ u => u.length))

-- Such a set is nonempty
lemma alternating_subsequences_lengths_nonempty {α : Type} [DecidableEq α] (v : List α) :
    (alternating_subsequences_lengths v).Nonempty := by
  refine ⟨0, ?_⟩
  refine ⟨[], ?_⟩
  simp only [List.length_nil, and_true]
  apply empty_mem_alternating_subsequences

-- Boolean version of non-emptyness
lemma alternating_subsequences_lengths_b_nonempty {α : Type} [DecidableEq α] (v : List α) :
    0 ∈ alternating_subsequences_lengths_b v := by
  unfold alternating_subsequences_lengths_b alternating_subsequences_b is_alternating_b
  unfold is_sparse_b distinct_count_le_2_b distinct_count_le_2_aux
  simp only [ne_eq, decide_not, List.mem_map, List.mem_filter, List.mem_sublists,
    Bool.and_eq_true, List.length_eq_zero_iff, exists_eq_right, List.nil_sublist,
    and_self]

-- Such a set is finite because the set of subsequences is finite
-- (we could also prove it by bounding the lengths by the length of v)
lemma alternating_subsequences_lengths_finite {α : Type} [DecidableEq α] (v : List α) :
    (alternating_subsequences_lengths v).Finite := by
  apply Set.Finite.image (λ u => u.length) (alternating_subsequences_finite v)

-- The maximum length of an alternating subsequence
noncomputable def max_alternating_length {α : Type} [DecidableEq α] (v : List α) : ℕ :=
  (alternating_subsequences_lengths_finite v).toFinset.max' (by
    unfold Finset.Nonempty
    let h_finset_non := alternating_subsequences_lengths_nonempty v
    simp_all only [Set.Finite.mem_toFinset]
    exact h_finset_non)

-- We also define it in a computable way for deciding/automation.
def max_alternating_length_b {α : Type} [DecidableEq α] (v : List α) : ℕ :=
  (alternating_subsequences_lengths_b v).toFinset.max' (by
    unfold Finset.Nonempty
    use 0
    simp only [List.mem_toFinset, alternating_subsequences_lengths_b_nonempty v])

-- The two definition give the same number
lemma max_alternating_length_eq_max_alternating_length_b {α : Type} [DecidableEq α] (v : List α) :
    max_alternating_length v = max_alternating_length_b v := by
  unfold max_alternating_length max_alternating_length_b
  congr 1
  ext n
  simp only [alternating_subsequences_lengths, Set.Finite.mem_toFinset, Set.mem_setOf_eq,
    alternating_subsequences_lengths_b, List.mem_toFinset, List.mem_map,
    mem_alternating_subsequences_iff]

#eval max_alternating_length_b ([] : List ℕ) -- expected 0
#eval max_alternating_length_b [1,2,1,2,3,1,2] -- expected 6
#eval max_alternating_length_b [1,1,1,1,1] -- expected 1

-- Every alternating subsequence has length ≤ max_alternating_length
lemma le_max_alternating_length {α : Type} [DecidableEq α] (u v : List α)
    (h_alt : u ∈ alternating_subsequences v) :
    u.length ≤ max_alternating_length v := by
  unfold max_alternating_length
  apply Finset.le_max' _ u.length
  simp only [Set.Finite.mem_toFinset]
  unfold alternating_subsequences_lengths
  simp only [Set.mem_setOf_eq]
  exact ⟨u, h_alt, rfl⟩

-- There exists an alternating subsequence with length = max_alternating_length
lemma exists_max_alternating_length {α : Type} [DecidableEq α] (v : List α) :
    ∃ u : List α, u ∈ alternating_subsequences v ∧ u.length = max_alternating_length v := by
  unfold max_alternating_length
  have := Finset.max'_mem (alternating_subsequences_lengths_finite v).toFinset
    (by
      unfold Finset.Nonempty
      let h_finset_non := alternating_subsequences_lengths_nonempty v
      unfold Set.Nonempty at h_finset_non
      simp_all only [Set.Finite.mem_toFinset])
  unfold alternating_subsequences_lengths at this
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at this
  exact this

-- The maximum alternating length is bounded by the original list's length
lemma max_alternating_length_le_length {α : Type} [DecidableEq α] (v : List α) :
    max_alternating_length v ≤ v.length := by
  obtain ⟨_, hu_mem, hu_eq⟩ := exists_max_alternating_length v
  rw [<- hu_eq]
  apply length_le_sublist hu_mem.left

-- Alternating sequences have maximum alternating length equal to their length
lemma max_alternating_length_of_alternating {α : Type} [DecidableEq α] {u : List α}
    (h : is_alternating u) : max_alternating_length u = u.length := by
  apply le_antisymm
  · apply max_alternating_length_le_length u
  · apply le_max_alternating_length u u
    unfold alternating_subsequences
    constructor
    · exact List.Sublist.refl u
    · exact h

-- If u is a sublist of v, then max_alternating_length u ≤ max_alternating_length v
lemma max_alternating_length_monotonic {α : Type} [DecidableEq α] {u v : List α}
    (h : u.Sublist v) : max_alternating_length u ≤ max_alternating_length v := by
  obtain ⟨u_max, hu_mem, hu_eq⟩ := exists_max_alternating_length u
  rw [<- hu_eq]
  -- u_max is an alternating subsequence of v
  have : u_max ∈ alternating_subsequences v := by
    unfold alternating_subsequences
    constructor
    · apply List.Sublist.trans hu_mem.left h
    · exact hu_mem.right
  apply le_max_alternating_length u_max v this

end Maximum_Length_of_Alternating_Subsequences
