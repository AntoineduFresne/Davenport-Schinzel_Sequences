/-
Copyright (c) 14.01.2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/

import Project.ExtremalFunction

/-
This file formalises some exact computations on the extremal function (s ∈ {1, 2, 3, 4}).
-/

/-
From our previous discussion, we can fix the decidable
type to be ℕ without loss of generality.
-/

/-
We will prove some exact computations on the extremal function.
-/
--Longest_DS_func(n, 1) = 0 for all n.
theorem Comp1 (n : ℕ) :
    @Longest_DS_func ℕ _ n 1 (by linarith) = 0 := by
    /-
    Proof:
    The extremal function for s=1 is 0.
    1. Lower bound (≥ 0): Trivial as length is a natural number.
    2. Upper bound (≤ 0): Assume there is a sequence of length ≥ 1.
       It must contain at least one element 'x'.
       The subsequence [x] is alternating of length 1.
       However, the condition for s=1 requires max_alternating_length < 1.
       Contradiction. Thus, only the empty sequence is allowed.
    -/
  apply le_antisymm _ (Nat.zero_le _)
  apply Finset.max'_le
  intro l hl
  rw [Set.Finite.mem_toFinset] at hl
  obtain ⟨u, hu, rfl⟩ := hl
  cases u
  · rfl
  · rename_i x xs
    exfalso
    rw [Davenport_Schinzel_sequences] at hu
    have : 1 ≤ max_alternating_length (x :: xs) := by
      apply Finset.le_max'
      rw [Set.Finite.mem_toFinset, alternating_subsequences_lengths, Set.mem_setOf_eq]
      use [x]
      constructor
      · constructor
        · simp_all only [Set.mem_setOf_eq, List.cons_sublist_cons, List.nil_sublist]
        · rw [is_alternating]
          constructor
          · exact is_chain_implies_is_sparse (singleton_is_chain x)
          · apply le_trans (distinct_count_le_length _)
            norm_num
      · rfl
    linarith [hu.2.2]

--Longest_DS_func(n, 2) = 1 for all n ≥ 1, and 0 for n = 0.
theorem Comp2 (n : ℕ) :
    @Longest_DS_func ℕ _ n 2 (by linarith) = if n ≥ 1 then 1 else 0 := by
    /-
    Proof:
    Case n ≥ 1:
      1. Upper bound (≤ 1): Any sequence of length ≥ 2 contains at least two adjacent elements a, b.
         By sparsity a ≠ b, so [a, b] is an alternating subsequence of length 2.
         This contradicts the condition max_alternating_length < 2.
      2. Lower bound (≥ 1): The sequence [0] is a valid (n, 2)-DS sequence of length 1.
    Case n = 0:
      The maximum length is 0 by computation.
    -/
  by_cases h : n ≥ 1
  · simp [h]; apply le_antisymm
    · apply Finset.max'_le; intro l hl
      rw [Set.Finite.mem_toFinset] at hl
      obtain ⟨u, hu, rfl⟩ := hl
      cases u with | nil => simp | cons a as =>
      cases as with | nil => simp | cons b cs =>
      rw [Davenport_Schinzel_sequences, Set.mem_setOf_eq, is_Davenport_Schinzel_sequence] at hu
      have : 2 ≤ max_alternating_length (a :: b :: cs) := by
        apply Finset.le_max'
        rw [Set.Finite.mem_toFinset, alternating_subsequences_lengths,
            Set.mem_setOf_eq]
        use [a, b]; constructor; swap; rfl
        constructor
        · simp_all only [ge_iff_le, List.cons_sublist_cons, List.nil_sublist]
        · rw [is_alternating]; constructor
          · rw [is_sparse, List.isChain_pair]
            exact (List.isChain_cons_cons.1 hu.2.1).1
          · exact le_trans (distinct_count_le_length _) (by norm_num)
      linarith [hu.2.2]
    · apply Finset.le_max'
      rw [Set.Finite.mem_toFinset]
      exact ⟨[0], singleton_is_Davenport_Schinzel_sequence 0 n 2 h (by norm_num), rfl⟩
  · simp at h; subst h; rw [Longest_DS_func_eq_Longest_DS_func_b]
    · rfl
    · simp only [CharP.cast_eq_zero, Cardinal.mk_eq_aleph0, zero_le]

-- Longest_DS_func(n, 3) = n for all n.
theorem Comp3 (n : ℕ) :
    @Longest_DS_func ℕ _ n 3 (by linarith) = n := by
    /-
    Proof:
    1. Lower bound (≥ n):
       The sequence [0, 1, ..., n-1] has length n, is clearly sparse,
       and contains no aba pattern (since all elements are distinct, any subseq of length 3 has 3 distinct elements or doesn't exist).
    2. Upper bound (≤ n):
       Suppose a sequence u has length > n.
       By Pigeonhole Principle, some element 'x' must appear at least twice since there are only n symbols.
       Let the occurrences be at indices i < j.
       u[i] = x, u[j] = x.
       Since u is sparse, u[i+1] ≠ x. Let y = u[i+1].
       Then x, y, x form an alternating subsequence of length 3.
       This contradicts the condition for s=3.
       Thus, no element can appear more than once.
       The maximum length of a sequence with distinct elements over size n is n.
    -/
  apply le_antisymm
  · apply Finset.max'_le; rintro l hl; rw [Set.Finite.mem_toFinset] at hl
    obtain ⟨u, hu, rfl⟩ := hl
    rw [Davenport_Schinzel_sequences, Set.mem_setOf_eq] at hu
    -- Show that all elements in u are distinct
    have h_nodup : u.Nodup := by
      induction u with | nil => simp | cons x xs ih =>
      obtain ⟨hd, hs, hm⟩ := hu
      rw [is_sparse] at hs
      have hs_tail : is_sparse xs := by cases xs <;>
      simp [is_sparse, List.isChain_cons_cons] at hs ⊢; exact hs.2
      refine List.nodup_cons.2 ⟨λ hx => ?_, ih ⟨le_trans (Finset.card_le_card (λ a h =>
        List.mem_toFinset.2 (List.Sublist.subset (List.Sublist.cons _
        (List.Sublist.refl _)) (List.mem_toFinset.1 h)))) hd, hs_tail,
        lt_of_le_of_lt (max_alternating_length_monotonic
        (List.Sublist.cons _ (List.Sublist.refl _))) hm⟩⟩
      obtain ⟨y, ys, rfl⟩ : ∃ y ys, xs = y :: ys := match xs, hx with
        | [], h => by contradiction | y::ys, _ => ⟨y, ys, rfl⟩
      simp only [ne_eq, List.isChain_cons_cons] at hs
      have h_abc : List.Sublist [x, y, x] (x :: y :: ys) :=
        List.Sublist.cons₂ _ (List.Sublist.cons₂ _
        (List.singleton_sublist.2 (List.mem_of_ne_of_mem hs.1 hx)))
      have h_alt : is_alternating [x, y, x] := by
        simp only [is_alternating, is_sparse, ne_eq, List.isChain_cons_cons, hs.1, not_false_eq_true,
          Ne.symm hs.1, List.isChain_singleton, and_self, distinct_count_by_dedup, List.mem_cons,
          List.not_mem_nil, or_false, or_true, List.dedup_cons_of_mem, or_self,
          List.dedup_cons_of_notMem, List.dedup_nil, List.length_cons, List.length_nil, zero_add,
          Nat.reduceAdd, le_refl]
      exact lt_irrefl 3 (lt_of_le_of_lt (le_max_alternating_length [x, y, x] (x :: y :: ys)
        (by dsimp only [alternating_subsequences, Set.mem_setOf_eq]; exact ⟨h_abc, h_alt⟩)) hm)
    rw [← List.toFinset_card_of_nodup h_nodup]
    change distinct_count_by_finset u ≤ n
    rw [← distinct_count_by_dedup_eq_distinct_count_by_finset]
    exact hu.1
  · refine Finset.le_max' _ n ?_
    rw [Set.Finite.mem_toFinset]
    use List.range n; constructor
    · dsimp only
      refine ⟨?_, List.nodup_range.isChain, ?_⟩
      · simp only [distinct_count_by_dedup, List.dedup_eq_self.2 List.nodup_range,
        List.length_range, le_refl]
      · have h_non := (alternating_subsequences_lengths_finite (List.range n)).toFinset_nonempty.mpr
          (alternating_subsequences_lengths_nonempty _)
        apply (Finset.max'_lt_iff _ h_non).2
        intro len h_len
        rw [Set.Finite.mem_toFinset] at h_len
        simp only [alternating_subsequences_lengths, Set.mem_setOf_eq,
                   alternating_subsequences] at h_len
        obtain ⟨w, ⟨hw_sub, hw_alt⟩, rfl⟩ := h_len
        rw [is_alternating] at hw_alt
        rw [distinct_count_by_dedup,
            List.dedup_eq_self.2 (List.nodup_range.sublist hw_sub)] at hw_alt
        linarith [hw_alt.2]
    · simp only [List.length_range]

-- Longest_DS_func(n, 4) = 2n - 1 for all n.
/-
This computation is more involved.
Proof:
    1. Lower bound (≥ 2n - 1):
      Consider the sequence 1, 2, ..., n-1, n, n-1, ..., 2, 1.
      This sequence has length 2n - 1.
      It contains no subsequence of type abab.
      If a occurs before b in the first half, it occurs after b in the second half.
      So we can have a...b...b...a, but not a...b...a...b.

    2. Upper bound (≤ 2n - 1):

      The first proof (due to Davenport and Schinzel):
      We proceed by induction on n. Base case n=1 is trivial (length 1) (we use computation).
      Let u be a DS sequence on n symbols. Without loss of generality, let 1 be the first element.
      We can decompose u as:
      u = 1 S₁ 1 S₂ ... 1 Sₖ (1)
      where each Sᵢ is a non-empty sequence of symbols from {2, ..., n} (since immediate repetitions
      11 are forbidden).
      Claim: The sets of symbols appearing in Sᵢ are pairwise disjoint.
      If a symbol x appeared in Sᵢ and Sⱼ with i < j, we would have a subsequence 1...x...1...x,
      which is an alternating subsequence of length 4.
      Let nᵢ be the number of distinct symbols in Sᵢ. Then ∑ nᵢ ≤ n - 1.
      Since each Sᵢ is a DS sequence, |Sᵢ| ≤ N(nᵢ).
      The number of 1s is at most k + 1.
      So |u| ≤ (k + 1) + ∑ |Sᵢ| ≤ k + 1 + ∑ (2nᵢ - 1)   (by IH)
               = k + 1 + 2(∑ nᵢ) - k
               = 1 + 2(∑ nᵢ)
               ≤ 1 + 2(n - 1)
               = 2n - 1.

      The second proof (due to Mrs. Turan) (this is the one we formalise):
      We begin with an observation that (among the integers occuring in the sequence) there is some
      integer which occurs only once in the sequence.
      Indeed, suppose by contradiction that every integer occurs at least twice. Let a be any integer
      in the sequence which occurs twice in the sequence, say at indices j₁ < j₂, with j₁ maximal.
      Since the sequence is sparse, j₂ ≥ j₁ + 2 and so there must be some integer b which occurs
      between (by sparsity), say at j₃ with j₁ < j₃ < j₂, because b occurs at least twice. There is
      an integer j₄∉{ j₁, j₃, j₂} where it occurs. By maximality of j₁, j₄ cannot be after j₁
      (because then we would have j₁ < j₄ < j₃ or j₁ < j₃ < j₄ so j₃ would be greater than j₁).
      So j₄ < j₁. But then we have an alternating subsequence of length 4 b a b a, a contradiction.

      Now remove the unique letter t which appears once. We obtain a sequence on n-1 letters.
      This sequence may have at most one immediate repetition, namely if the neighbours of the unique
      letter are equal: ..., x, n', t, n', y, ... (possibly empty on the left/right if t is the
      first/last one).
      So we remove one of the two n' as well. This immediate
      repetition disappears if we delete also one of the two terms n', since x ≠ n' and y ≠ n'. Hence by
      deleting at most two terms (t and possibly one n') we can obtain an admissible
      sequence whose terms are formed from 1, ..., n-1.
      It follows that Longest_DS_func(n, 4) ≤ Longest_DS_func(n-1, 4) + 2, and this
      gives Longest_DS_func(n, 4) ≤ 2n - 1 by induction (because Longest_DS_func(0, 4) = 0).
    -/

-- Helper definitions for Comp4

--For the lower bound:
-- Lower bound construction
def lower_bound_seq (n : ℕ) : List ℕ :=
  (List.range n) ++ (List.drop 1 (List.range n).reverse)

-- The length of the lower bound sequence is 2n - 1
lemma lower_bound_len (n : ℕ) : (lower_bound_seq n).length = 2 * n - 1 := by
  unfold lower_bound_seq
  cases n
  · simp
  · simp_all only [List.drop_one, List.tail_reverse, List.length_append, List.length_range,
    List.length_reverse, List.length_dropLast, add_tsub_cancel_right]
    omega

-- The number of distinct symbols in the lower bound sequence is at most n
lemma lower_bound_symbols (n : ℕ) :
    distinct_count_by_dedup (lower_bound_seq n) ≤ n := by
  rw [distinct_count_by_dedup_eq_distinct_count_by_finset, distinct_count_by_finset,
    lower_bound_seq]
  have h_subset : (List.range n ++ (List.range n).reverse.drop 1).toFinset ⊆ (List.range n).toFinset := by
    intro x hx
    simp only [List.mem_toFinset, List.mem_append] at hx
    rcases hx with h | h
    · simp only [List.mem_toFinset, h]
    · apply List.mem_toFinset.mpr
      apply List.mem_reverse.mp
      apply (List.drop_sublist 1 _).subset h
  convert Finset.card_le_card h_subset
  rw [List.toFinset_card_of_nodup List.nodup_range]
  simp_all only [List.drop_one, List.tail_reverse, List.toFinset_append, List.toFinset_reverse, List.length_range]

-- The lower bound sequence is sparse
lemma lower_bounds_sparse (n : ℕ) :
    is_sparse (lower_bound_seq n) := by
  cases n
  · simp [lower_bound_seq, is_sparse]
  · rename_i n
    apply concat_is_sparse
    · apply is_chain_implies_is_sparse
      rw [is_chain, distinct_count_by_dedup, List.dedup_eq_self.2 List.nodup_range, List.length_range]
    · apply is_chain_implies_is_sparse
      rw [is_chain, distinct_count_by_dedup]
      rw [List.dedup_eq_self.2 (List.Nodup.sublist (List.drop_sublist 1 _) (List.nodup_reverse.2 List.nodup_range))]
    · conv_lhs => rw [List.range_succ, List.getLast?_concat]
      rw [show (List.drop 1 (List.range (n + 1)).reverse).head? = (List.drop 1 (List.range (n + 1)).reverse)[0]? by cases (List.drop 1 (List.range (n + 1)).reverse) <;> rfl]
      rw [List.getElem?_drop, Nat.add_zero]
      cases n with
      | zero => simp
      | succ n =>
        rw [List.getElem?_reverse]
        · simp only [List.length_range]
          simp only [add_tsub_cancel_right, add_zero, ne_eq]
          have h_range_eq : n + 1 + 1 = n + 2 := by omega
          rw [h_range_eq]
          have h_idx : n < (List.range (n+2)).length := by simp only [List.length_range]; linarith
          rw [List.getElem?_eq_getElem h_idx, List.getElem_range]
          simp
        · simp only [List.length_range]; linarith

-- No alternating subsequence of length 4 in increasing ++ decreasing
lemma no_abab_in_increasing_append_decreasing {n : ℕ} (u : List ℕ)
    (h_sub : u.Sublist ((List.range n) ++ (List.drop 1 (List.range n).reverse)))
    (h_alt : is_alternating u)
    (h_len : u.length = 4) : False := by
  obtain ⟨s1, s2, hs1, hs2, rfl⟩ := exists_sublist_split_of_sublist_append h_sub
  -- s1 is increasing, s2 is decreasing
  have h_mono : s1.Pairwise (· < ·) ∧ s2.Pairwise (· > ·) := by
    constructor
    · exact List.Pairwise.sublist hs1 List.pairwise_lt_range
    · apply List.Pairwise.sublist hs2; apply List.Pairwise.sublist (List.drop_sublist _ _)
      rw [List.pairwise_reverse]
      exact List.pairwise_lt_range
  -- Lengths of s1 and s2 are both 2
  have : s1.length = 2 ∧ s2.length = 2 := by
    rw [List.length_append] at h_len
    have h1 := distinct_count_sublist (List.sublist_append_left s1 s2)
    have h2 := distinct_count_sublist (List.sublist_append_right s1 s2)
    rw [distinct_count_by_dedup, List.dedup_eq_self.2 (h_mono.1.imp ne_of_lt)] at h1
    rw [distinct_count_by_dedup, List.dedup_eq_self.2 (h_mono.2.imp ne_of_gt)] at h2
    have := h_alt.right; omega
  -- Extract elements
  obtain ⟨a, b, rfl⟩ : ∃ a b, s1 = [a, b] := by
    rcases s1 with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩ <;> try simp at this
    exact ⟨a, b, rfl⟩
  obtain ⟨c, d, rfl⟩ : ∃ c d, s2 = [c, d] := by
    rcases s2 with _ | ⟨c, _ | ⟨d, _ | ⟨_, _⟩⟩⟩ <;> try simp at this
    exact ⟨c, d, rfl⟩
  -- Now we have u = [a, b, c, d] with a < b and c > d
  unfold is_alternating at h_alt
  simp only [distinct_count_by_dedup_eq_distinct_count_by_finset] at h_alt
  rw [List.cons_append, List.cons_append, List.nil_append] at h_alt
  have hab : a < b := (List.pairwise_cons.1 h_mono.1).1 _ (List.mem_singleton.2 rfl)
  have h_card : ({a, b, c, d} : Finset ℕ).card ≤ 2 := by
    convert h_alt.right
    simp [distinct_count_by_finset]
  have h_eq : ({a, b} : Finset ℕ) = {a, b, c, d} := by
    apply Finset.eq_of_subset_of_card_le (by simp [Finset.subset_iff, Finset.mem_insert, Finset.mem_singleton])
    rw [Finset.card_pair (ne_of_lt hab)]
    exact h_card
  have : c ∈ ({a, b} : Finset ℕ) ∧ d ∈ ({a, b} : Finset ℕ) := by rw [h_eq]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  have hcd : c > d := (List.pairwise_cons.1 h_mono.2).1 _ (List.mem_singleton.2 rfl)
  have hbc : b ≠ c := by
      have := h_alt.1
      rw [is_sparse] at this
      simp [List.isChain_cons_cons, ne_eq] at this
      exact this.2.1
  rcases this with ⟨(rfl|rfl), (rfl|rfl)⟩
  · exact lt_irrefl _ hcd
  · linarith
  · contradiction
  · exact lt_irrefl _ hcd

-- The maximal alternating length of the lower bound sequence is < 4
lemma lower_bound_no_abab (n : ℕ) :
    max_alternating_length (lower_bound_seq n) < 4 := by
  by_contra h_ge
  push_neg at h_ge
  obtain ⟨u, h_u, h_len⟩ := exists_max_alternating_length (lower_bound_seq n)
  let v := u.take 4
  unfold alternating_subsequences at h_u
  simp at h_u
  have h_len_ge : 4 ≤ u.length := by simp_all only
  have h_v_len : v.length = 4 := by
      rw [List.length_take];
      exact min_eq_left h_len_ge
  have h_v_alt_and_len := alternating_subsequence_of_smaller_length u h_u.2 4 h_len_ge
  have h_v_alt : is_alternating v := h_v_alt_and_len.left
  have h_v_sub : v.Sublist (lower_bound_seq n) := List.Sublist.trans (List.take_sublist 4 u) h_u.1
  apply no_abab_in_increasing_append_decreasing v h_v_sub h_v_alt h_v_len

-- The lower bound sequence is a (n, 4)-Davenport-Schinzel sequence
lemma lower_bound_is_DS (n : ℕ) : is_Davenport_Schinzel_sequence n 4 (lower_bound_seq n) := by
  refine ⟨?_, ?_, ?_⟩
  · exact lower_bound_symbols n
  · exact lower_bounds_sparse n
  · exact lower_bound_no_abab n

-- For the upper bound:
-- The main helper lemma for findIdx
theorem findIdx_le {α : Type} [DecidableEq α]
    {l : List α} {p : α → Bool} {i : ℕ}
    (hi : i < l.length) (h : p (l.get ⟨i, hi⟩)) :
    l.findIdx p ≤ i := by
  induction l generalizing i
  · contradiction
  · rename_i head tail ih
    simp only [List.findIdx_cons]
    by_cases hp : p head
    · -- Case: p head is true. The expression reduces to 0.
      simp [hp]
    · -- Case: p head is false. The expression reduces to findIdx tail + 1.
      simp [hp]
      cases i
      · -- i = 0. We have p head = true (from h) and p head = false (from hp).
        simp at h
        contradiction
      · -- i = j + 1. We need findIdx tail ≤ j.
        apply Nat.succ_le_succ
        apply ih (Nat.lt_of_succ_lt_succ hi)
        -- Simplify the hypothesis h: (head :: tail)[j+1] becomes tail[j]
        simp at h
        exact h

-- The main lemma: idxOf x ≤ i if l[i] = x
theorem idxOf_le  {α : Type} [DecidableEq α]
{l : List α} {x : α} {i : ℕ} (hi : i < l.length) (h : l[i] = x) : l.idxOf x ≤ i := by
  unfold List.idxOf
  apply findIdx_le hi
  subst h
  simp_all only [List.get_eq_getElem, BEq.rfl]

-- If idxOf x ≥ i, then x ∉ l.take i
lemma not_mem_take_of_idxOf_le {α : Type} [DecidableEq α]
    {l : List α} {x : α} {i : ℕ} (h : i ≤ l.idxOf x) :
    x ∉ l.take i := by
  intro h_mem
  rw [List.mem_iff_getElem] at h_mem
  rcases h_mem with ⟨j, hj_len, h_val⟩
  -- 1. Establish j < i
  -- Used later for the final contradiction
  have hj_lt_i : j < i := Nat.lt_of_lt_of_le hj_len (List.length_take_le i l)
  -- 2. Establish j < l.length (CORRECTED STEP)
  -- We need this to show j is a valid index in 'l' so we can apply idxOf_le
  have hj_lt_l : j < l.length :=
    Nat.lt_of_lt_of_le hj_len (length_le_sublist (List.take_sublist i l))
  -- 3. The value at index j in the taken list is the same as in l
  rw [List.getElem_take] at h_val
  -- 4. Apply idxOf_le
  -- Since l[j] == x, the first occurrence (idxOf x) must be ≤ j
  have h_idx_le_j : l.idxOf x ≤ j := by
    apply idxOf_le hj_lt_l
    subst h_val
    simp_all only
  -- 5. Contradiction: idxOf x ≤ j < i ≤ idxOf x
  have : l.idxOf x < i := Nat.lt_of_le_of_lt h_idx_le_j hj_lt_i
  linarith

-- There exists an element in a (n, 4)-Davenport-Schinzel sequence that appears exactly once
lemma exists_unique_element_of_DS4 {n : ℕ} {u : List ℕ}
    (h_ds : is_Davenport_Schinzel_sequence n 4 u)
    (h_ne : u ≠ []) :
    ∃ x ∈ u, u.count x = 1 := by
  by_contra h_neg
  push_neg at h_neg
  -- Proof by contradiction: Assume that every element appearing in the sequence appears at least twice.
  -- Meaning, there are no unique elements in the sequence.
  have h_count_ge_2 : ∀ x ∈ u, 2 ≤ u.count x := fun x hx =>
    let h := h_neg x hx
    have : u.count x ≠ 0 := by
      intro hc; rw [List.count_eq_zero] at hc; contradiction
    by omega
  -- Choose an element 'a' whose first occurrence is at the latest possible position in the sequence.
  -- Let j₁ be the index of this first occurrence. We enable this by maximizing the index of the first occurrence.
  let f := fun x => u.idxOf x
  have h_finset_non : u.toFinset.Nonempty := by
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil u h_ne
    exact ⟨x, List.mem_toFinset.mpr hx⟩
  obtain ⟨a, ha_mem_fin, ha_max⟩ := Finset.exists_max_image u.toFinset f h_finset_non
  have ha_mem : a ∈ u := List.mem_toFinset.mp ha_mem_fin
  let j1 := u.idxOf a
  let L := u.take j1
  let R := u.drop (j1 + 1)
  have h_lt : j1 < u.length := List.idxOf_lt_length_iff.mpr ha_mem
  have hu_eq : u = L ++ [a] ++ R := by
    rw [←List.take_append_drop (j1+1) u]
    have : u.take (j1 + 1) = u.take j1 ++ [a] := by
       rw [List.take_add_one, List.getElem?_eq_getElem h_lt, Option.toList_some, List.getElem_idxOf h_lt]
    rw [this]
  have ha_not_in_L : a ∉ L := not_mem_take_of_idxOf_le (le_refl _)
  have ha_in_R : a ∈ R := by
    have hc := h_count_ge_2 a ha_mem
    rw [hu_eq] at hc
    simp only [List.count_append, List.count_singleton, beq_self_eq_true, reduceIte] at hc
    rw [List.count_eq_zero.mpr ha_not_in_L] at hc
    simp only [zero_add] at hc
    exact List.count_pos_iff.mp (by omega)
  have h_R_ne : R ≠ [] := List.ne_nil_of_mem ha_in_R
  let b := R.head h_R_ne
  -- Since the sequence is sparse (no adjacent identical elements), the element 'b' immediately following the first occurrence of 'a' must be distinct from 'a'.
  -- This uses the sparsity property of Davenport-Schinzel sequences.
  have hab : a ≠ b := by
    unfold is_Davenport_Schinzel_sequence at h_ds
    have h_sparse := h_ds.2.1
    unfold is_sparse at h_sparse
    rw [hu_eq, List.isChain_append] at h_sparse
    have h_adj := h_sparse.2.2
    have h_last : (L ++ [a]).getLast? = some a := List.getLast?_append_of_ne_nil _ (by simp only [ne_eq,
      List.cons_ne_self, not_false_eq_true])
    obtain ⟨headR, tailR, hR_eq⟩ := List.exists_cons_of_ne_nil h_R_ne
    have h_head : R.head? = some b := by simp only [hR_eq, List.head?_cons, List.head_cons, b]
    apply h_adj a
    · rw [Option.mem_def]; exact h_last
    · rw [Option.mem_def]; exact h_head
  have hb_mem_R : b ∈ R := List.head_mem h_R_ne
  have hb_mem : b ∈ u := by rw [hu_eq]; simp only [List.append_assoc, List.cons_append,
    List.nil_append, List.mem_append, List.mem_cons, hb_mem_R, or_true]
  -- Since 'b' appears in the sequence, it must appear at least twice.
  -- By our choice of 'a' (maximality of its first index j₁), the first occurrence of 'b' cannot be after j₁.
  -- Therefore, the first occurrence of 'b' must be at or before j₁.
  have h_b_idx_le : u.idxOf b ≤ j1 := ha_max b (List.mem_toFinset.mpr hb_mem)

  have hb_in_L : b ∈ L := by
    by_contra h_notin
    have : u.idxOf b = j1 + 1 + R.idxOf b := by
      rw [hu_eq]
      grind
    have : u.idxOf b ≥ j1 + 1 := by omega
    omega
  -- With 'b' appearing before 'a' (in L), then 'a', then 'b' again (head of R), then 'a' again (somewhere in R),
  -- we have found an alternating subsequence b...a...b...a of length 4.
  -- This contradicts the forbidden subsequence property.
  have h_sub : [b, a, b, a].Sublist u := by
    obtain ⟨headR, tailR, hR_eq⟩ := List.exists_cons_of_ne_nil h_R_ne
    have ha_in_tail : a ∈ tailR := by
       rw [hR_eq] at ha_in_R
       cases List.mem_cons.mp ha_in_R with
       | inl h =>
        exfalso
        simp_all only [List.append_assoc, List.cons_append, List.nil_append, ne_eq,
          List.append_eq_nil_iff, reduceCtorEq, and_false, not_false_eq_true, List.mem_append,
          List.mem_cons, or_self_left, List.count_append, List.toFinset_append, List.toFinset_cons,
          Finset.mem_insert, List.mem_toFinset, true_or, Finset.insert_eq_of_mem,
          Finset.union_insert, Finset.insert_nonempty, Finset.mem_union, forall_eq_or_imp, le_refl,
          true_and, or_self, or_true, List.length_append, List.length_cons]
        grind
       | inr h => exact h

    rw [hu_eq, List.append_assoc]
    have : [b, a, b, a] = [b] ++ ([a] ++ [b, a]) := rfl
    rw [this]
    apply List.Sublist.append (List.singleton_sublist.mpr hb_in_L)
    apply List.Sublist.append (List.Sublist.refl [a])
    rw [hR_eq]
    have : headR = b := by simp [b, hR_eq]
    rw [this]
    apply List.Sublist.cons₂
    exact List.singleton_sublist.mpr ha_in_tail
  -- The existence of the alternating subsequence [b, a, b, a] implies that the maximum alternating length of the sequence is at least 4.
  have h_len_bad : max_alternating_length u ≥ 4 := by
    apply Finset.le_max'
    simp only [Set.Finite.mem_toFinset, alternating_subsequences_lengths, Set.mem_setOf_eq]
    use [b, a, b, a]
    constructor
    · unfold alternating_subsequences
      constructor
      · simp_all
      · unfold is_alternating
        constructor
        · unfold is_sparse
          simp [hab, hab.symm]
        · rw [distinct_count_by_dedup_eq_distinct_count_by_finset]
          unfold distinct_count_by_finset
          simp only [List.toFinset_cons, List.toFinset_nil, insert_empty_eq, Finset.mem_insert,
            Finset.mem_singleton, or_true, Finset.insert_eq_of_mem, true_or]
          rw [Finset.card_pair hab.symm]
    · simp_all
  -- This contradicts the property of being a Davenport-Schinzel sequence of order 4 (which requires max alternating length < 4).
  obtain ⟨_, _, h_max_len⟩ := h_ds
  linarith [h_max_len]

-- By removing an element that appears exactly once in a (n, 4)-Davenport-Schinzel sequence,
-- we can obtain a (n-1, 4)-Davenport-Schinzel sequence
-- whose length is at least the original length minus 2.
lemma remove_one_and_bound {n : ℕ} {u : List ℕ} (x : ℕ)
    (h_ds : is_Davenport_Schinzel_sequence n 4 u)
    (hx : u.count x = 1) :
    ∃ v, @is_Davenport_Schinzel_sequence ℕ _ (n - 1) 4 v ∧ u.length ≤ v.length + 2 := by
  let j := u.idxOf x; let L := u.take j; let R := u.drop (j + 1)
  have hu : u = L ++ [x] ++ R := by
    rw [←List.take_append_drop (j + 1) u]
    have : u.take (j + 1) = u.take j ++ [x] := by
       rw [List.take_add_one, List.getElem?_eq_getElem (List.idxOf_lt_length_iff.2 (List.count_pos_iff.1 (by rw [hx]; norm_num))), Option.toList_some, List.getElem_idxOf]
    rw [this]
  have hx_LR : x ∉ L ∧ x ∉ R := by
    have c := hx; rw [hu] at c; simp only [List.count_append, List.count_singleton] at c
    have : x ∉ L := not_mem_take_of_idxOf_le (le_refl _)
    rw [List.count_eq_zero.2 this] at c; simp at c
    exact ⟨this, List.count_eq_zero.1 c⟩
  let v := if h : L.getLast? = R.head? ∧ L.getLast?.isSome then L ++ R.drop 1 else L ++ R
  have hv_sub : v.Sublist u := by
    dsimp [v]; split_ifs <;> rw [hu, List.append_assoc]
    · exact List.Sublist.append (List.Sublist.refl L) (List.Sublist.trans (List.drop_sublist 1 R) (List.Sublist.cons x (List.Sublist.refl R)))
    · exact List.Sublist.append (List.Sublist.refl L) (List.Sublist.cons x (List.Sublist.refl R))
  refine ⟨v, ⟨?_, ?_, lt_of_le_of_lt (max_alternating_length_monotonic hv_sub) h_ds.2.2⟩, ?_⟩
  -- Distinct Count
  · obtain ⟨h_u_distinct, -⟩ := h_ds
    rw [distinct_count_by_dedup_eq_distinct_count_by_finset] at h_u_distinct ⊢
    calc v.toFinset.card
      _ ≤ (u.toFinset.erase x).card := Finset.card_le_card (by
          intro a ha; rw [Finset.mem_erase, List.mem_toFinset]
          refine ⟨?_, List.Sublist.subset hv_sub (List.mem_toFinset.1 ha)⟩
          -- Prove a != x
          by_contra neq
          subst neq
          -- if a == x, then x \in v.
          rw [List.mem_toFinset] at ha
          dsimp [v] at ha; split_ifs at ha <;> rw [List.mem_append] at ha
          · rcases ha with (h1|h2)
            · exact hx_LR.1 (List.mem_toFinset.1 (List.mem_toFinset.2 h1))
            · exact hx_LR.2 (List.mem_of_mem_drop h2)
          · rcases ha with (h1|h2)
            · exact hx_LR.1 (List.mem_toFinset.1 (List.mem_toFinset.2 h1))
            · exact hx_LR.2 (List.mem_toFinset.1 (List.mem_toFinset.2 h2)))
      _ = u.toFinset.card - 1 := Finset.card_erase_of_mem (List.mem_toFinset.2 (by rw [hu]; simp))
      _ ≤ n - 1 := Nat.sub_le_sub_right h_u_distinct 1
  -- Sparse
  · obtain ⟨_, h_sparse, -⟩ := h_ds
    dsimp [is_sparse] at h_sparse ⊢
    rw [hu, List.append_assoc, List.isChain_append, List.isChain_append] at h_sparse
    obtain ⟨hL, ⟨-, hR, -⟩, -⟩ := h_sparse
    dsimp [v]; split_ifs with h_merge
    · rw [List.isChain_append]; refine ⟨hL, ?_, ?_⟩
      · cases hR_eq : R with | nil => simp | cons y ys =>
        rw [hR_eq] at h_merge hR; simp only [List.drop_one]; exact List.IsChain.tail hR
      · intro l hl r hr
        rcases h_merge with ⟨heq, ha_some⟩
        rw [Option.isSome_iff_exists] at ha_some; obtain ⟨a, ha⟩ := ha_some
        rw [ha] at hl; rw [Option.mem_def] at hl
        have hl_eq : l = a := Option.some_inj.1 hl.symm
        rw [hl_eq]
        cases hR_eq : R
        · simp_all
        · rename_i y ys
          rw [hR_eq] at hR heq hr
          simp only [List.head?_cons] at heq
          rw [ha] at heq
          have hay : a = y := Option.some_inj.1 heq
          subst hay
          dsimp at hr
          cases ys
          · cases hr
          · rename_i z zs
            rw [List.isChain_cons_cons] at hR
            rw [List.head?_cons] at hr
            cases hr
            exact hR.1
    · rw [List.isChain_append]; refine ⟨hL, hR, ?_⟩
      intro l hl r hr
      by_contra heq
      subst heq
      apply h_merge;
      constructor
      · simp_all only [List.append_assoc, List.cons_append, List.nil_append, List.count_append,
        List.count_cons_self, List.getLast?_isSome, ne_eq, not_and, Decidable.not_not,
        Option.mem_def]
      · simp_all only [List.append_assoc, List.cons_append, List.nil_append, List.count_append,
        List.count_cons_self, List.getLast?_isSome, ne_eq, not_and, Decidable.not_not,
        Option.mem_def, Option.isSome_some]
  -- Length
  · dsimp [v]; split_ifs with h <;> rw [hu] <;> simp <;> (try cases R <;> simp_all) <;> omega

-- We then obtain the following recurrence for Longest_DS_func(n, 4):
lemma recurrence_Comp4 (n : ℕ) :
    @Longest_DS_func ℕ _ (n + 1) 4 (by linarith) ≤
    @Longest_DS_func ℕ _ n 4 (by linarith) + 2 := by
  obtain ⟨u, h_ds, h_len⟩ := @Longest_DS_func_attained ℕ _ (n+1) 4 (by linarith)
  by_cases h_nil : u = []
  · rw [h_nil] at h_len; simp at h_len; linarith
  · obtain ⟨x, _, hx_count⟩ := exists_unique_element_of_DS4 h_ds h_nil
    obtain ⟨v, hv_ds, hv_len⟩ := remove_one_and_bound x h_ds hx_count
    have : n - 1 ≥ 0 := by linarith
    have len_v_le : v.length ≤ @Longest_DS_func ℕ _ n 4 (by linarith) := by
      apply Finset.le_max'
      rw [Set.Finite.mem_toFinset]
      exact ⟨v, hv_ds, rfl⟩
    rw [<- h_len]
    calc
      u.length ≤ v.length + 2 := hv_len
      _ ≤ @Longest_DS_func ℕ _ n 4 (by linarith) + 2 := Nat.add_le_add_right len_v_le 2

-- The main theorem: Longest_DS_func(n, 4) = 2n - 1
theorem Comp4 (n : ℕ) :
    @Longest_DS_func ℕ _ n 4 (by linarith) = 2 * n - 1 := by
    apply le_antisymm
    · induction n
      · -- We compute (using the boolean version of the function) Longest_DS_func(0,4) = 0
        simp_all only [mul_zero, zero_tsub, nonpos_iff_eq_zero]
        rw [@Longest_DS_func_eq_Longest_DS_func_b ℕ _ 0 4 (by linarith) (by simp)]
        rfl
      · rename_i n ih
        by_cases h : n = 0
        · -- We compute (using the boolean version of the function) Longest_DS_func(1,4) = 1
          simp_all only [mul_zero, zero_tsub, nonpos_iff_eq_zero, zero_add, mul_one,
            Nat.add_one_sub_one]
          rw [@Longest_DS_func_eq_Longest_DS_func_b ℕ _ 1 4 (by linarith) (by simp)]
          rfl
        · calc
            @Longest_DS_func ℕ _ (n + 1) 4 (by linarith)
              ≤ @Longest_DS_func ℕ _ n 4 (by linarith) + 2 := recurrence_Comp4 n
            _ ≤  (2 * n - 1) + 2 := by omega
            _ = 2 * (n + 1) - 1 := by omega -- This required n ≥ 1
    · unfold Longest_DS_func
      apply Finset.le_max'
      rw [Set.Finite.mem_toFinset]
      unfold Davenport_Schinzel_sequences_lengths
      rw [Set.mem_setOf_eq]
      use lower_bound_seq n
      exact ⟨lower_bound_is_DS n, lower_bound_len n⟩
