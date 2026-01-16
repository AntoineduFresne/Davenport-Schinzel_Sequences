/-
Copyright (c) 14.01.2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/

import Project.Finiteness_of_Davenport_Schinzel_Sequences_Lengths

/-
This file formalises the extremal function associated to Davenport-Schinzel sequences
-/

/-
We can now define the extremal function of Davenport-Schinzel sequences.
It consists in taking the maximum length of all (n,s)-Davenport-Schinzel sequences,
Since we know that this set is finite, this maximum exists as long as the set is non-empty
which happens if and only if s ≥ 1. Since all definiton were dependent on the type α,
we make the extremal function depend on α as well (clearly if α is too small, the extremal function
will be small as well, but this is not an issue because α is modulable).
-/
noncomputable def Longest_DS_func {α : Type} [DecidableEq α] (n s : ℕ) (h : s ≥ 1) : ℕ :=
  (@finite_Davenport_Schinzel_sequence_lengths α _ n s).toFinset.max' (by
    unfold Finset.Nonempty
    let h_finset_non :=
      @Davenport_Schinzel_sequences_lengths_nonempty α _ n s (by linarith) h
    simp_all only [Set.Finite.mem_toFinset]
    exact h_finset_non)

-- The extremal bound is attained
lemma Longest_DS_func_attained {α : Type} [DecidableEq α]
    (n s : ℕ) (h : s ≥ 1) :
    ∃ u : List α, is_Davenport_Schinzel_sequence n s u ∧
      u.length = @Longest_DS_func α _ n s h := by
  unfold Longest_DS_func
  let finset_lengths := (@finite_Davenport_Schinzel_sequence_lengths α _ n s).toFinset
  have h_nonempty : finset_lengths.Nonempty := by
    unfold Finset.Nonempty finset_lengths
    let h_finset_non :=
      @Davenport_Schinzel_sequences_lengths_nonempty α _ n s (by linarith) h
    simp_all only [Set.Finite.mem_toFinset]
    exact h_finset_non
  let max_length := finset_lengths.max' h_nonempty
  have h_mem := Finset.max'_mem finset_lengths h_nonempty
  simp_all only [Set.Finite.mem_toFinset, finset_lengths]
  exact h_mem

/-
We wish to do a computable version of this function and prove that it gives the
same number as the non-computable one.

Recall that we have seen:

1. If α is a type with decidable equality and n ≤ |α| (α does not need to be finite)
then for all s len : ℕ there is a (n,s)-Davenport-Schinzel sequence of length len over
α if and only if there is a (n,s)-Davenport-Schinzel sequence of length len over ℕ.
This means that the extremal function (for s ≥ 1) does not depend on the type α as
long as it is large enough. This is formalised in the following lemma:
-/
lemma Longest_DS_func_type_independence {α : Type}
    [DecidableEq α]
    (n : ℕ) (s : ℕ) (h1 : s ≥ 1)
    (h2 : n ≤ Cardinal.mk α) :
    @Longest_DS_func α _ n s h1 = @Longest_DS_func ℕ _ n s h1 := by
    unfold Longest_DS_func
    congr 1
    ext x
    simp_all [Davenport_Schinzel_sequences_length_indep_of_type]

/-
Hence as long as the type α is large enough (has at least n elements),
the extremal function at (n,_) does not depend on the type α.

This mean that we can restrict ourselves to an infinite type with decidable equality, which we
may take as ℕ because it is the simplest infinite type with decidable equality and satisfies
important ordered properties (that can be useful in our context: for example computation:
Lean may have to do choices based on order).

Now, lets recap what we already have as computable:
1. We can computably check if a sequence is a (n,s)-Davenport-Schinzel sequence:
   `is_Davenport_Schinzel_sequence_b`.
2. We can computably enumerate all (n,s)-Davenport-Schinzel sequences of a certain length N:
    `Davenport_Schinzel_sequences_b n s N`
  by enumerating all sequences of length N and filtering those that are (n,s)-Davenport-Schinzel sequences.

Additionnaly:
1. we know an upper bound on the maximum length of such (n,s)-Davenport-Schinzel
sequences, specifically
   `((s - 1) / 2) * n * (n - 1) + 1`.
2. The property of being a (n,s)-Davenport-Schinzel sequence is monotone.

Hence, we will again apply binary search to find the maximum length of a (n,s)-Davenport-Schinzel
sequence over ℕ.
-/

-- The predicate for binary search: exists a (n,s)-Davenport-Schinzel sequence of length k.
-- We check existence over the alphabet [0, ..., n-1].
def exists_Davenport_Schinzel_sequence_of_length_b (n s k : ℕ) : Bool :=
  -- We can restrict strictly to the alphabet [0, ..., n-1] without loss of generality
  (all_lists_of_length (List.range n).dedup k).any
    (is_Davenport_Schinzel_sequence_b n s)

-- Correctness of the predicate (relates to existence over ℕ)
lemma exists_Davenport_Schinzel_sequence_of_length_b_iff (n s k : ℕ) :
  exists_Davenport_Schinzel_sequence_of_length_b n s k = true ↔
  ∃ u : List ℕ, is_Davenport_Schinzel_sequence n s u ∧ u.length = k := by
  unfold exists_Davenport_Schinzel_sequence_of_length_b
  rw [List.any_eq_true]
  constructor
  · -- Direction ->
    rintro ⟨u, h_mem, h_ds_b⟩
    rw [mem_all_lists_of_length_iff] at h_mem
    rw [is_Davenport_Schinzel_sequence_b_iff] at h_ds_b
    exact ⟨u, h_ds_b, h_mem.1⟩
  · -- Direction <-
    intro h
    change k ∈ @Davenport_Schinzel_sequences_lengths ℕ _ n s at h
    rw [← Davenport_Schinzel_sequences_length_indep_of_type n (by simp) s k (α := Fin n)] at h
    obtain ⟨v, h_ds, h_len⟩ := h
    let u := v.map (λ x => x.val)
    use u
    constructor
    · rw [mem_all_lists_of_length_iff]
      constructor
      · rw [length_map, h_len]
      · intro x hx
        obtain ⟨y, _, rfl⟩ := List.mem_map.1 hx
        simp only [List.mem_dedup, List.mem_range]
        exact y.isLt
    · rw [is_Davenport_Schinzel_sequence_b_iff]
      rw [← is_Davenport_Schinzel_sequence_map_of_injective (λ x : Fin n => x.val) v n s]
      · exact h_ds
      · intro x _ y _ h; exact Fin.eq_of_val_eq h

-- Monotonicity of the predicate
lemma exists_Davenport_Schinzel_sequence_of_length_monotonic (n s m k : ℕ)
  (h_le : m ≤ k) (h_k : exists_Davenport_Schinzel_sequence_of_length_b n s k = true) :
  exists_Davenport_Schinzel_sequence_of_length_b n s m = true := by
  rw [exists_Davenport_Schinzel_sequence_of_length_b_iff] at h_k ⊢
  obtain ⟨u, h_ds, h_len⟩ := h_k
  have h_m_le_len : m ≤ u.length := by rw [h_len]; exact h_le
  use u.take m
  apply Davenport_Schinzel_subsequence_of_smaller_length n s m h_ds h_m_le_len

-- p 0 is true because the empty sequence is a (n,s)-Davenport-Schinzel sequence for s ≥ 1.
lemma exists_Davenport_Schinzel_sequence_of_length_b_zero (n s : ℕ)
  (h : s ≥ 1) :
  exists_Davenport_Schinzel_sequence_of_length_b n s 0 = true := by
  rw [exists_Davenport_Schinzel_sequence_of_length_b_iff]
  use []
  constructor
  · apply empty_is_Davenport_Schinzel_sequence n s (by apply Nat.zero_le) h
  · rfl

-- The computable extremal function using binary search
def Longest_DS_func_b (n s : ℕ) (h : s ≥ 1) : ℕ :=
  let p := exists_Davenport_Schinzel_sequence_of_length_b n s
  -- We use the trivial upper bound derived in Finiteness...
  let bound := ((s - 1) / 2) * n * (n - 1) + 1
  have p0 : p 0 = true := by
    apply exists_Davenport_Schinzel_sequence_of_length_b_zero n s h
  binary_search_last_true p bound p0

-- Finally, we can prove that the computable extremal function
-- gives the same result as the non-computable one.
theorem Longest_DS_func_eq_Longest_DS_func_b {α : Type}
    [DecidableEq α]
    (n s : ℕ)
    (h1 : s ≥ 1)
    (h2 : n ≤ Cardinal.mk α) :
    @Longest_DS_func α _ n s h1 = Longest_DS_func_b n s h1 := by
  rw [Longest_DS_func_type_independence n s h1 h2]
  have spec := binary_search_last_true_spec _ (((s - 1) / 2) * n * (n - 1) + 1)
    (exists_Davenport_Schinzel_sequence_of_length_monotonic n s) (exists_Davenport_Schinzel_sequence_of_length_b_zero n s h1)
  apply le_antisymm
  · apply Finset.max'_le; intro x hx
    simp only [Set.Finite.mem_toFinset, Davenport_Schinzel_sequences_lengths,
      Davenport_Schinzel_sequences, Set.mem_setOf_eq] at hx
    obtain ⟨u, h, rfl⟩ := hx
    apply spec.2.2 _ (trivial_upper_bound_Davenport_Schinzel_sequence_length n s u h)
    rw [exists_Davenport_Schinzel_sequence_of_length_b_iff]
    exact ⟨u, h, rfl⟩
  · apply Finset.le_max'
    simp only [Set.Finite.mem_toFinset, Davenport_Schinzel_sequences_lengths, Davenport_Schinzel_sequences, Set.mem_setOf_eq]
    rw [← exists_Davenport_Schinzel_sequence_of_length_b_iff]
    exact spec.2.1

-- Examples
#eval Longest_DS_func_b 2 1 (by linarith)
#eval Longest_DS_func_b 2 2 (by linarith)
