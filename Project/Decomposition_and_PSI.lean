/-
Copyright (c) 14.01.2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/

import Project.Basic_Definitions_and_Lemmas
import Project.Ackermann_Function

/-!
# m-Decomposition and the function ψ(m, n)

This file formalises the structural decomposition of sequences used in Klazar's proof.
-/

section Definitions

/--
First appearance F(u): The subsequence formed by the first occurrence of each symbol in u.
In Lean, `List.dedup` keeps the first occurrence of each element.
-/
def first_appearance {α : Type} [DecidableEq α] (u : List α) :
List α := (u.reverse.dedup).reverse

/--
Last appearance L(u): The subsequence formed by the last occurrence of each symbol in u.
Computationally equivalent to reversing, deduplicating, and reversing back.
-/
def last_appearance {α : Type} [DecidableEq α] (u : List α) : List α := u.dedup

#eval first_appearance [3,1,4,1,5,9,2,6,5,3,5] -- [3,1,4,5,9,2,6]
#eval last_appearance [3,1,4,1,5,9,2,6,5,3,5]  -- [4,1,9,2,6,3,5]


-- The set of all symbols appearing in u, S(u).
def symbols_of {α : Type} [DecidableEq α] (u : List α) : Finset α := u.toFinset

/--
Normal order S(u, ≺): x ≺ y iff the first appearance of x precedes the first appearance of y.
Since `first_appearance u` is the list of unique elements in order of appearance,
this corresponds to the index in `first_appearance u`.
-/
def normal_order {α : Type} [DecidableEq α] (u : List α) (x y : α) : Prop :=
  (first_appearance u).idxOf x < (first_appearance u).idxOf y

/-
Checks if a list is decreasing with respect to the normal order of a parent list `u`.
"decreasing (going from left to right) with respect to the normal order" that is,
for elements x, y appearing in sub, if x appears before y in sub, then y < x in normal order
in u. This means that the first appearance of y precedes that of x in u altough x appears
before y in sub.
-/
def is_decreasing_normal_order {α : Type} [DecidableEq α] (u : List α)
(sub : List α) : Prop :=
  sub.IsChain (fun x y => normal_order u y x) -- y < x means decreasing

/-
m-decomposition:
A sequence u m-decomposes if one can split u into m possibly empty chains u = u₁...u_m
such that each u_i \ F(u) is decreasing with respect to the normal order of u, where
u_i \ F(u) is the list formed by removing from u_i all symbols that appear in F(u).

Def: u_i \ F(u)

 This represents the chunk 'u_i' with all "First Appearances" removed.
 Essentially: Filter 'u_i' to keep ONLY the symbols that have
 appeared previously in the full sequence 'u'.

EXAMPLE:
Full Sequence (u):   a b c b a
Chunk (u_i):         b a   (the second part of the sequence)
First Apps (F(u)):   The very first 'a', 'b', and 'c'.
Calculation:
The 'b' in u_i is a repeat (not the first). -> KEEP
The 'a' in u_i is a repeat (not the first). -> KEEP

Result (u_i \ F(u)): b a

That is: if a b are in u_i and not in F(u), then a will appear after b in u_i \ F(u), if
and only if normal_order u b a holds, i.e., the first appearance of b precedes that of a in u.

For this definition, we use some helper `process_chunk_remove_first` to process each chunk
and `remove_first_appearances_splits` to remove first appearances.
-/

/--
Helper: Process a chunk to remove first appearances (if not in seen), updating seen.
-/
def process_chunk_remove_first {α : Type} [DecidableEq α]
    (chunk : List α) (seen : List α) : List α × List α :=
  match chunk with
  | [] => ([], seen)
  | x :: xs =>
    if x ∈ seen then
      let (res, new_seen) := process_chunk_remove_first xs seen
      (x :: res, new_seen)
    else
      let (res, new_seen) := process_chunk_remove_first xs (x :: seen)
      (res, new_seen)

/--
Helper: Recursively process splits.
-/
def remove_first_appearances_splits_aux {α : Type} [DecidableEq α]
    (splits : List (List α)) (seen : List α) : List (List α) :=
  match splits with
  | [] => []
  | chunk :: rest =>
    let (filtered_chunk, new_seen) := process_chunk_remove_first chunk seen
    filtered_chunk :: remove_first_appearances_splits_aux rest new_seen

def remove_first_appearances_splits {α : Type} [DecidableEq α] (splits : List (List α)) : List (List α) :=
  remove_first_appearances_splits_aux splits []

#eval remove_first_appearances_splits [[1,2,3], [2,1]] -- [[], [2,1]] as desired

-- We can now define m-decomposition.
def m_decomposes {α : Type} [DecidableEq α] (m : ℕ) (u : List α) : Prop :=
  ∃ (splits : List (List α)),
    splits.length = m ∧
    splits.flatten = u ∧
    (∀ sub ∈ splits, is_chain sub) ∧
    (∀ sub ∈ remove_first_appearances_splits splits, is_decreasing_normal_order u sub)

end Definitions

section Psi_Function

/-
The function ψ(m, n) is defined as the maximum length of a sequence u such that:
1. u m-decomposes
2. max_alternating_length u < 5 (al(u) < 5 in text)
3. distinct_count u ≤ n (||u|| ≤ n in text)
-/

/-
The set of valid sequences for the definition of ψ(m, n).
We restrict the alphabet to ℕ to make the set of sequences well-defined and countable
(though bounded length implies finiteness).
-/
def psi_sequences {α : Type} [DecidableEq α] (m n : ℕ) : Set (List ℕ) :=
  { u | m_decomposes m u ∧ max_alternating_length u < 5 ∧ distinct_count_by_dedup u ≤ n }

-- The set of lengths of valid sequences for ψ(m, n).
def psi_sequences_lengths {α : Type} [DecidableEq α] (m n : ℕ) : Set ℕ :=
  (@psi_sequences α _ m n).image List.length
/-
The finiteness of lengths for the valid sequences.
Necessary to define the maximum.
-/
lemma psi_sequences_lengths_finite {α : Type} [DecidableEq α] (m n : ℕ) :
   (@psi_sequences_lengths α _ m n).Finite := by
    -- we skip this proof due to time constraints
  sorry

-- Non-emptiness condition for ψ(m, n).
lemma psi_sequences_nonempty {α : Type} [DecidableEq α] (m n : ℕ) :
  (@psi_sequences α _ m n).Nonempty := by
  /-
  We can use the empty sequence as a valid sequence. Indeed, it m-decomposes for any m,
  because we can split it into m empty chains. Its max_alternating_length is 0 < 5,
  and its distinct_count_by_dedup is also 0 ≤ n for any n.
  -/
  use []
  simp only [psi_sequences, Set.mem_setOf_eq]
  refine ⟨?_, ?_, ?_⟩
  · unfold m_decomposes
    use List.replicate m []
    simp only [List.length_replicate, List.flatten_replicate_nil, true_and]
    constructor
    · intro sub hsub
      rw [List.mem_replicate] at hsub
      rcases hsub with ⟨_, rfl⟩
      unfold is_chain distinct_count_by_dedup
      rfl
    · have h_remove : remove_first_appearances_splits (List.replicate m ([] : List ℕ))
      = List.replicate m [] := by
        unfold remove_first_appearances_splits
        induction m with
        | zero => rfl
        | succ k ih =>
            simp only [List.replicate, remove_first_appearances_splits_aux, process_chunk_remove_first]
            rw [ih]
      intro sub hsub
      rw [h_remove, List.mem_replicate] at hsub
      rcases hsub with ⟨_, rfl⟩
      exact List.isChain_nil
  · rw [max_alternating_length_eq_max_alternating_length_b]
    trivial
  · unfold distinct_count_by_dedup
    simp only [List.dedup_nil, List.length_nil, zero_le]

-- This implies that the set of lengths is also non-empty.
lemma psi_sequences_lengths_nonempty {α : Type} [DecidableEq α] (m n : ℕ) :
  (@psi_sequences_lengths α _ m n).Nonempty := by
  unfold psi_sequences_lengths
  exact Set.Nonempty.image _ (psi_sequences_nonempty m n)

-- The function ψ(m, n).
noncomputable def psi {α : Type} [DecidableEq α] (m n : ℕ) : ℕ :=
  (@psi_sequences_lengths_finite α _ m n).toFinset.max' (by
    unfold Finset.Nonempty
    let h_finset_non := @psi_sequences_lengths_nonempty α _ m n
    simp_all only [Set.Finite.mem_toFinset]
    exact h_finset_non)

/-
Recursive inequality for ψ(m, n):
Let  m, n, m_1, m_2, ... , m_j be positive integers, j ≥ 2, such that m = m_1 + ... + m_j.
Then there exist nonnegative integers n_0, n_1, ..., n_j such that n = n_0 + n_1 + ... + n_j
and
ψ(m, n) ≤ ∑_{i=1}^j ψ(m_i, n_i) + 2m + 2n_0 + ψ(j-1, n_0).
-/
lemma psi_recursive_inequality {α : Type} [DecidableEq α] (m n j : ℕ) (ms : List ℕ)
    (h_m_sum : m = ms.sum)
    (h_j_len : ms.length = j)
    (h_j_ge_2 : j ≥ 2)
    (h_ms_pos : ∀ x ∈ ms, 0 < x)
    (h_n_pos : 0 < n) :
    ∃ (ns : List ℕ),
      ns.length = j + 1 ∧
      n = ns.sum ∧
      @psi α _ m n ≤ (List.zipWith (fun mi ni => @psi α _ mi ni) ms ns.tail).sum
      + 2 * m + 2 * (ns[0]!) + @psi α _ (j - 1) (ns[0]!) := by
    -- we skip this proof due to time constraints
  sorry

/-
Upper bound for ψ involving ackermann function:
For all k ≥ 2, m ≥ 1, n ≥ 1,
ψ(m, n) ≤ 2k( (α k m)m + n)
-/
lemma psi_upper_bound {α : Type} [DecidableEq α]
  (k m n : ℕ) (hk : k ≥ 2) (hm : m ≥ 1) (hn : n ≥ 1):
    @psi α _ m n ≤ 2 * k * ((KlazarAckermann.alpha k m (by linarith)) * m + n) := by
    -- we skip this proof due to time constraints
  sorry

-- Specialised upper bound: for all m ≥ 1, n ≥ 1, ψ(m,n) ≤ 8mα(m) + 8m+ 2nα(m) + 2n.
lemma specialised_psi_upper_bound (m n : ℕ) (hm : m ≥ 1) (hn : n ≥ 1) :
    @psi ℕ _ m n ≤ 8 * m * KlazarAckermann.alpha_omega m
    + 8 * m + 2 * n * KlazarAckermann.alpha_omega m + 2 * n := by
  let A := KlazarAckermann.alpha_omega m
  let k := A + 1
  have hA : A ≥ 1 := by
    by_contra h
    simp only [not_le, Nat.lt_one_iff] at h
    have spec := KlazarAckermann.alpha_omega_spec m
    unfold A KlazarAckermann.alpha_omega at h spec
    rw [h] at spec
    simp [KlazarAckermann.F_omega, KlazarAckermann.F] at spec
    linarith
  have hk : k ≥ 2 := by omega
  have h_alpha : KlazarAckermann.alpha k m (by linarith) ≤ 4 := by
    convert KlazarAckermann.alpha_nested_bound m hm
  calc
    @psi ℕ _ m n
      ≤ 2 * k * ((KlazarAckermann.alpha k m (by linarith)) * m + n) :=
      psi_upper_bound k m n hk hm hn
    _ = 2 * (A + 1) * ((KlazarAckermann.alpha k m (by linarith)) * m + n) := rfl
    _ ≤ 2 * (A + 1) * (4 * m + n) := by
      gcongr
    _ = 8 * m * A + 8 * m + 2 * n * A + 2 * n := by ring

end Psi_Function
