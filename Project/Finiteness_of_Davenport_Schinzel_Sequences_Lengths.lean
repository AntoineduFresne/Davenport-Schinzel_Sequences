/-
Copyright (c) 14.01.2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/

import Project.Davenport_Schinzel_Sequences

/-
This file formalises the boundedness of Davenport-Schinzel sequences lengths.
-/

/-
The main goal is to show that this set is finite.
This follows from the following lemma showing that we can bound "trivially"
the lengths of (n,s)-Davenport-Schinzel sequences by ⌊(s-1)/2⌋ * n * (n - 1) + 1 (where ⌊_<0⌋ = 0).

Theorem: Trivial Upper Bound for Davenport-Schinzel Sequences N_s(n)

  Proof Argument:

1. Counting Adjacent Pairs:
     Let the sequence be S = [x_0, x_1, ..., x_{N-1}].
     For each 0 ≤ i ≤ N-2 there is an adjacent pair (xᵢ, xᵢ₊₁) (there are N-1 of them).

2. Sparse Property:
     By definition, a Davenport-Schinzel sequence is "sparse," meaning xᵢ ≠ xᵢ₊₁ for all i.
     Therefore, every adjacent pair (u, v) in S consists of distinct symbols u ≠ v. The
     total number of possible distinct ordered pairs (u, v) from an alphabet of size n is n(n - 1).

3. Bounding Multiplicity of a Single Pair:
     Consider a specific pair of distinct symbols (a, b) (among all possible n(n-1) ones).
     Let k be the number of times the pair (a, b) appears in S.

     These k occurrences imply the existence of a subsequence:
       a, b, a, b, ..., a, b

     The length of this alternating subsequence is 2k.
     By definition, S does not contain any alternating subsequence of length s.
     Therefore, we must have:
       2k < s
       2k ≤ s - 1
       k  ≤ ⌊(s - 1) / 2⌋

      So ⌊(s - 1) / 2⌋ is the maximum number of times any such pair (a, b) can appear.

4. Summation:
     The total number of adjacent pairs in the sequence is the sum of the counts of each unique pair type.

     (N - 1) = ∑_{u≠v} count(u, v)

     Since count(u, v) ≤ ⌊(s - 1) / 2⌋ for all distinct u, v:
     (N - 1) ≤ n*(n - 1) * ⌊(s - 1) / 2⌋

5. Conclusion:
     Substituting d back into the inequality:
     N - 1 ≤ n(n - 1) * ⌊(s - 1) / 2⌋
     N     ≤ n(n - 1) * ⌊(s - 1) / 2⌋ + 1
-/

-- This requires multiple lemmas and constructions...

/-
First, given u v : α, we count the number of occurrences
of each adjacent pair (u,v) in a sequence l : List α. We also define
a computable version, show that it gives the same result,
and provide an example.
-/
-- Mathematical definition of the count of occurrences of the adjacent pair `(u, v)` in list `l`.
-- It iterates over all valid indices `i` where `l[i] = u` and `l[i+1] = v`.
def count_adjacent_pair {α : Type} [DecidableEq α] (u v : α) (l : List α) : ℕ :=
  ((List.range (l.length - 1)).filter (fun i => l[i]? = some u ∧ l[i + 1]? = some v)).length

-- Computable (recursive) definition of the count of occurrences of the adjacent pair `(u, v)` in list `l`.
def count_adjacent_pair_b {α : Type} [DecidableEq α] (u v : α) (l : List α) : ℕ :=
  match l with
  | [] => 0
  | [_] => 0
  | x :: y :: tail => (if x = u ∧ y = v then 1 else 0) + count_adjacent_pair_b u v (y :: tail)

-- The two definitions of counting adjacent pairs give the same number.
lemma count_adjacent_pair_eq_count_adjacent_pair_b {α : Type} [DecidableEq α] (u v : α) (l : List α) :
    count_adjacent_pair u v l = count_adjacent_pair_b u v l := by
  induction l
  · rfl
  · rename_i x tail ih
    cases tail
    · rfl
    · rename_i y tail'
      unfold count_adjacent_pair_b count_adjacent_pair
      rw [← ih]
      simp only [List.length_cons, Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
      rw [List.range_succ_eq_map, List.filter_cons]
      split
      · next h =>
          rw [if_pos]
          · simp only [List.length_cons]
            rw [add_comm]
            congr 1
            rw [List.filter_map, List.length_map]
            apply congr_arg
            apply List.filter_congr
            intro i _
            simp only [Function.comp_apply, Nat.succ_eq_add_one,
            List.getElem?_cons_succ, Bool.decide_and]
          · simpa only [List.length_cons, lt_add_iff_pos_left, add_pos_iff,
            Nat.ofNat_pos, or_true, getElem?_pos, List.getElem_cons_zero,
            Option.some.injEq, zero_add, zero_lt_one, List.getElem_cons_succ,
            Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq] using h
      · next h =>
          rw [if_neg]
          · simp only [zero_add]
            rw [List.filter_map, List.length_map]
            apply congr_arg
            apply List.filter_congr
            intro i _
            simp only [Function.comp_apply,
            Nat.succ_eq_add_one, List.getElem?_cons_succ, Bool.decide_and]
          · simpa only [not_and, List.length_cons, lt_add_iff_pos_left,
            add_pos_iff, Nat.ofNat_pos, or_true, getElem?_pos,
            List.getElem_cons_zero, Option.some.injEq, zero_add, zero_lt_one,
            List.getElem_cons_succ, Bool.decide_and, Bool.and_eq_true,
            decide_eq_true_eq] using h

-- Example of evaluation:
#eval count_adjacent_pair_b 1 2 [1, 2, 1, 2, 3] -- Expected: 2
#eval count_adjacent_pair_b 2 3 [1, 2, 1, 2, 3] -- Expected: 1
#eval count_adjacent_pair_b 1 1 [1, 1, 1]       -- Expected: 2

-- Helper lemma: The sum of the counts of all adjacent pairs
-- (where it suffices to take the letters in the list l) is equal to length - 1,
lemma sum_counts_adjacent_pairs_eq_length_sub_one_of_subset {α : Type} [DecidableEq α] (l : List α) :
    (l.toFinset ×ˢ l.toFinset).sum (fun p => count_adjacent_pair p.1 p.2 l) = l.length - 1 := by
  -- The proof is simply by rewriting the definition of counting adjacent pairs as a sum,
  -- using fubini for sums and rewriting.
  let n := l.length - 1
  -- 1. Convert counting definition to sum over indices
  have h_count (u v : α) :
      count_adjacent_pair u v l = ∑ i ∈ Finset.range n,
        if (l[i]? = some u ∧ l[i + 1]? = some v) then 1 else 0 := by
    unfold count_adjacent_pair
    rw [Finset.sum_boole, ← List.toFinset_card_of_nodup]
    · congr 1
      rw [List.toFinset_filter]
      ext x
      simp only [Finset.mem_filter, List.mem_toFinset, List.mem_range,
      Finset.mem_range,decide_eq_true_eq, n]
    · exact List.nodup_range.filter _
  simp_rw [h_count]
  rw [Finset.sum_comm]
  -- 2. Evaluate inner sum
  trans ∑ i ∈ Finset.range n, 1
  · apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_range] at hi
    -- Indices bounds
    have hi_lt : i < l.length := Nat.lt_of_lt_of_le hi (Nat.sub_le _ _)
    have hi_succ_lt : i + 1 < l.length := by
        simp only [n] at hi
        apply Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hi)
        apply Nat.sub_one_lt
        intro h
        simp only [h, zero_tsub, not_lt_zero'] at hi
    -- Let's extract values
    rw [List.getElem?_eq_getElem hi_lt, List.getElem?_eq_getElem hi_succ_lt]
    simp only [Option.some.injEq]
    -- Term is 1 if p.1 = l[i] and p.2 = l[i+1].
    let u := l[i]
    let v := l[i+1]
    rw [Finset.sum_ite]
    simp only [Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
    have h_mem : (u, v) ∈ l.toFinset ×ˢ l.toFinset := by
        rw [Finset.mem_product, List.mem_toFinset, List.mem_toFinset]
        exact ⟨List.getElem_mem hi_lt, List.getElem_mem hi_succ_lt⟩
    have h_filter_eq : {x ∈ l.toFinset ×ˢ l.toFinset | l[i] = x.1 ∧ l[i + 1] = x.2} =
                       {x ∈ l.toFinset ×ˢ l.toFinset | x = (u, v)} := by
       ext ⟨x1, x2⟩
       simp only [eq_comm, Finset.mem_filter, Finset.mem_product, List.mem_toFinset,
       Prod.ext_iff, u, v]
    rw [h_filter_eq, Finset.filter_eq' _ (u,v), if_pos h_mem]
    simp only [Finset.card_singleton]
    rfl
  · simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
    Nat.cast_tsub, Nat.cast_id, Nat.cast_one, n]

-- Helper: Decomposition of a pattern: that is the flattening of k copies of [u, v]
-- is either empty (if k = 0) or of the form u :: v :: rest for a list rest.
lemma replicate_pair_flatten_eq {α : Type} (k : ℕ) (u v : α) :
  (List.replicate k [u, v]).flatten = []
  ∨ ∃ rest, (List.replicate k [u, v]).flatten = u :: v :: rest := by
  cases k
  · simp only [List.replicate_zero, List.flatten_nil, List.nil_eq, reduceCtorEq, exists_const,
    or_false]
  · right
    apply Exists.intro
    · rfl

-- Helper: if k is the count of adjacent pairs (u, v) in l, assuming u ≠ v
-- then the pattern generated by repeating [u, v] k times is a sublist of l.
-- The fact that u ≠ v is necessary otherwise [1,1,1] would be a counterexample
-- (the count is 2) but [1,1,1,1] is not a sublist of [1,1,1].
lemma pattern_sublist_of_count_adjacent_pair_b {α : Type} [DecidableEq α]
    (u v : α) (l : List α) (h_neq : u ≠ v) :
    (List.replicate (count_adjacent_pair_b u v l) [u, v]).flatten.Sublist l := by
  induction l
  · simp [count_adjacent_pair_b]
  · rename_i x tail ih
    cases tail
    · simp only [count_adjacent_pair_b, List.replicate_zero, List.flatten_nil, List.Sublist.refl,
      List.Sublist.cons]
    · rename_i y tail'
      dsimp only [count_adjacent_pair_b]
      split
      · next h =>
          obtain ⟨rfl, rfl⟩ := h
          rw [Nat.add_comm, List.replicate_succ]
          simp [List.cons_append, List.nil_append]
          have h_decomp := replicate_pair_flatten_eq (count_adjacent_pair_b x y (y :: tail')) x y
          rcases h_decomp with h_nil | ⟨rest, h_cons⟩
          · rw [h_nil]
            apply List.nil_sublist
          · rw [h_cons] at ih ⊢
            rw [List.sublist_cons_iff] at ih
            rcases ih with ⟨rfl, _⟩ | h_sub
            · simp_all only [ne_eq, List.Sublist.cons]
            · simp_all only [ne_eq, List.cons_sublist_cons]
            simp_all only [ne_eq, List.cons.injEq, false_and, exists_const]
      · simp only [zero_add]
        apply List.Sublist.cons
        exact ih

-- Helper: The pattern [u, v, u, v, ...] is alternating and of length 2*k
lemma pattern_is_alternating {α : Type} [DecidableEq α] (k : ℕ) (u v : α) (h_neq : u ≠ v) :
    let pattern := (List.replicate k [u, v]).flatten
    is_alternating (pattern) ∧ pattern.length = 2 * k := by
  intro pattern
  constructor
  · constructor
    · -- is_sparse
      dsimp only [pattern]
      unfold is_sparse
      induction k
      · simp only [ne_eq, List.replicate_zero, List.flatten_nil, List.isChain_nil]
      · rename_i n ih
        simp only [List.replicate_succ, List.flatten_cons, List.isChain_append, List.isChain_cons, ne_eq]
        constructor
        · simp only [List.head?_cons, Option.mem_def, Option.some.injEq, forall_eq',
          List.head?_nil, reduceCtorEq, IsEmpty.forall_iff, implies_true, List.IsChain.nil,
          and_self, h_neq, not_false_eq_true, and_self]
        · simp only [ih, true_and]
          cases n
          · simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.mem_def,
            Option.some.injEq, List.replicate_zero, List.flatten_nil, List.head?_nil, reduceCtorEq,
            IsEmpty.forall_iff, implies_true]
          · simp only [List.replicate_succ, List.flatten_cons,
            List.getLast?_cons_cons, List.getLast?_singleton, Option.mem_def,
              Option.some.injEq, List.cons_append, List.nil_append, List.head?_cons, forall_eq',
              h_neq.symm, not_false_eq_true]
    · -- distinct count
      dsimp only [pattern]
      have h_subset : ((List.replicate k [u, v]).flatten).toFinset ⊆ {u, v} := by
        intro x hx
        rw [List.mem_toFinset, List.mem_flatten] at hx
        obtain ⟨_, hl', hx'⟩ := hx
        rw [List.mem_replicate] at hl'
        obtain ⟨_, rfl⟩ := hl'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx'
        simp only [Finset.mem_insert, Finset.mem_singleton, hx']
      rw [distinct_count_by_dedup_eq_distinct_count_by_finset]
      apply le_trans (Finset.card_le_card h_subset)
      rw [Finset.card_insert_of_notMem]
      · rewrite [Finset.card_singleton]
        norm_num
      · simp only [Finset.mem_singleton, h_neq, not_false_eq_true]
  · -- length
    simp_all only [ne_eq, List.length_flatten, List.map_replicate, List.length_cons,
      List.length_nil, zero_add, Nat.reduceAdd, List.sum_replicate, smul_eq_mul, pattern]
    rw [mul_comm]

-- Helper lemma: For sequences forbidding alternating subsequences of length s,
-- each distinct adjacent pair can appear at most ⌊(s-1)/2⌋ times (if s ≥ 1)
-- otherwise it is 0 when s = 0. In Lean all quantities are encapsulated in (s - 1)/2
-- because when s = 0, (s - 1)/2 = 0 (as a - b = 0 when a < b in Nat) and in
-- Nat "/" rounds downwards.
lemma count_adjacent_pair_le {α : Type} [DecidableEq α]
    (u v : α) (l : List α) (s : ℕ)  (h_neq : u ≠ v) (h_max_alt : max_alternating_length l < s) :
    count_adjacent_pair u v l ≤ (s - 1) / 2 := by
  rw [count_adjacent_pair_eq_count_adjacent_pair_b]
  let k := count_adjacent_pair_b u v l
  let pattern := (List.replicate k [u, v]).flatten
  have h_sub : pattern.Sublist l := pattern_sublist_of_count_adjacent_pair_b u v l h_neq
  obtain ⟨h_alt, h_len⟩ := pattern_is_alternating k u v h_neq
  have h_mem : pattern ∈ alternating_subsequences l := ⟨h_sub, h_alt⟩
  have h_len_le : 2 * k ≤ max_alternating_length l := by
    rw [← h_len]
    apply le_max_alternating_length pattern l h_mem
    -- Finish
  rw [Nat.le_div_iff_mul_le Nat.zero_lt_two, mul_comm]
    -- 2 * k <= s - 1
  apply Nat.le_pred_of_lt
  apply lt_of_le_of_lt h_len_le h_max_alt

-- The second construction is to build the list of all distinct adjacent pairs
-- in a sequence u : List α (so we remove the duplicates).
def distinct_adjacent_pairs {α : Type} [DecidableEq α] (u : List α) : List (α × α) :=
  ((List.range (u.length - 1)).filterMap (fun i =>
    match u[i]?, u[i+1]? with
    | some a, some b => some (a, b)
    | _, _ => none)).dedup

-- We also define a boolean version as well:
def distinct_adjacent_pairs_b {α : Type} [DecidableEq α] (u : List α) : List (α × α) :=
  (u.zip u.tail).dedup

-- show that this gives the same result
lemma distinct_adjacent_pairs_eq_distinct_adjacent_pairs_b {α : Type} [DecidableEq α] (u : List α) :
    distinct_adjacent_pairs u = distinct_adjacent_pairs_b u := by
  unfold distinct_adjacent_pairs distinct_adjacent_pairs_b
  congr 1
  by_cases h_u : u = []
  · simp only [h_u, List.length_nil, not_lt_zero', not_false_eq_true, getElem?_neg, zero_tsub,
    List.range_zero, List.filterMap_nil, List.tail_nil, List.zip_nil_right]
  · rw [List.zip_eq_zipWith]
    let default_val : α := u.head h_u
    let f (i : ℕ) : α × α := match u[i]?, u[i+1]? with
                             | some a, some b => (a, b)
                             | _, _ => (default_val, default_val)
    have h_fm : ((List.range (u.length - 1)).filterMap (fun i =>
         match u[i]?, u[i+1]? with
         | some a, some b => some (a, b)
         | _, _ => none)) = (List.range (u.length - 1)).map f := by
       trans (List.range (u.length - 1)).filterMap (some ∘ f)
       · apply List.filterMap_congr
         intro i hi
         rw [List.mem_range] at hi
         simp only [Function.comp_apply]
         have h1 : i < u.length := Nat.lt_of_lt_of_le hi (Nat.sub_le _ _)
         have h2 : i + 1 < u.length := Nat.succ_lt_of_lt_pred hi
         dsimp only [f]
         rw [List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2]
       · rw [List.filterMap_eq_map]
    rw [h_fm]
    apply List.ext_getElem
    · simp only [List.length_map, List.length_range, List.length_zipWith, List.length_tail]
      rw [min_eq_right]
      apply Nat.sub_le
    · intro i h1 h2
      simp only [List.length_map, List.length_range] at h1
      rw [List.getElem_map, List.getElem_zipWith, List.getElem_tail]
      simp only [List.getElem_range]
      dsimp only [f]
      have hi_lt : i < u.length := Nat.lt_of_lt_of_le h1 (Nat.sub_le _ _)
      have hi_succ : i + 1 < u.length := Nat.succ_lt_of_lt_pred h1
      rw [List.getElem?_eq_getElem hi_lt, List.getElem?_eq_getElem hi_succ]

-- and make an example of evaluation.
#eval distinct_adjacent_pairs_b [1, 2, 1, 3, 2] -- Expected: [(1,2), (2,1), (1,3), (3,2)]

-- we also make two lemma that states that the length of this list is at most n^2 and
-- for sparse sequence it is at most n*(n-1).
-- But for this we need a helper lemma first: this is a characterization of membership
-- in a zipped list in terms of getElem.
lemma List.mem_zip_iff_getElem {α β : Type} {l₁ : List α} {l₂ : List β} {x : α × β} :
    x ∈ l₁.zip l₂ ↔ ∃ i : ℕ, ∃ h₁ : i < l₁.length, ∃ h₂ : i < l₂.length,
      l₁[i] = x.1 ∧ l₂[i] = x.2 := by
  induction l₁ generalizing l₂
  · simp_all only [zip_nil_left, not_mem_nil, exists_and_left, length_nil, not_lt_zero', IsEmpty.exists_iff,
    exists_const]
  · cases l₂
    · simp_all only [exists_and_left, exists_and_right, zip_nil_right, not_mem_nil, length_nil, not_lt_zero',
      IsEmpty.exists_iff, length_cons, exists_false]
    · simp_all only [zip_cons_cons, mem_cons, length_cons, exists_and_left, exists_and_right]
      obtain ⟨fst, snd⟩ := x
      simp_all only [Prod.mk.injEq]
      apply Iff.intro
      · intro a
        cases a with
        | inl h =>
          obtain ⟨left, right⟩ := h
          subst right left
          use 0
          simp_all only [getElem_cons_zero, lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true,
            exists_const, and_self]
        | inr h_1 =>
          obtain ⟨w, _, _, _, _⟩ := h_1
          use w + 1
          simp_all only [getElem_cons_succ, add_lt_add_iff_right, exists_const, and_self]
      · intro a
        obtain ⟨w, _, _, _, _⟩ := a
        cases w with
        | zero =>
          left
          simp_all only [getElem_cons_zero, lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true,
            exists_const, and_self]
        | succ n =>
          right
          simp_all only [getElem_cons_succ, add_lt_add_iff_right]
          use n
          simp_all only [exists_prop, and_true, true_and]
          grind only

-- We can now prove the lemmas about the length of adjacent pairs.
lemma length_distinct_adjacent_pairs_le_sq {α : Type} [DecidableEq α] (u : List α) :
    (distinct_adjacent_pairs u).length ≤ (distinct_count_by_dedup u)^2 := by
  rw [distinct_adjacent_pairs_eq_distinct_adjacent_pairs_b]
  unfold distinct_adjacent_pairs_b
  -- Convert list length to finset card
  rw [← List.toFinset_card_of_nodup (List.nodup_dedup _)]
  rw [distinct_count_by_dedup_eq_distinct_count_by_finset]
  unfold distinct_count_by_finset
  rw [sq, ← Finset.card_product]
  apply Finset.card_le_card
  intro x hx
  rw [List.mem_toFinset, List.mem_dedup, List.mem_zip_iff_getElem] at hx
  rcases hx with ⟨i, hi, htail, eq1, eq2⟩
  rw [Finset.mem_product]
  constructor <;> rw [List.mem_toFinset]
  · rw [← eq1]; apply List.getElem_mem
  · rw [← eq2]; apply List.mem_of_mem_tail; apply List.getElem_mem

-- Sparse version (distinct adjacent pairs)
lemma length_distinct_adjacent_pairs_le_mul_sparse {α : Type} [DecidableEq α] (u : List α) (h : is_sparse u) :
    (distinct_adjacent_pairs u).length ≤ (distinct_count_by_dedup u) * ((distinct_count_by_dedup u) - 1) := by
  rw [distinct_adjacent_pairs_eq_distinct_adjacent_pairs_b]
  unfold distinct_adjacent_pairs_b
  rw [← List.toFinset_card_of_nodup (List.nodup_dedup _)]
  simp only [distinct_count_by_dedup_eq_distinct_count_by_finset]
  unfold distinct_count_by_finset
  rw [Nat.mul_sub, mul_one, ← Finset.offDiag_card]
  apply Finset.card_le_card
  intro x hx
  rw [List.mem_toFinset, List.mem_dedup, List.mem_zip_iff_getElem] at hx
  rcases hx with ⟨_, _, htail, eq1, eq2⟩
  rw [Finset.mem_offDiag]
  simp only [List.length_tail] at htail
  constructor
  · rw [← eq1, List.mem_toFinset]; apply List.getElem_mem
  · constructor
    · rw [← eq2, List.mem_toFinset]; apply List.mem_of_mem_tail; apply List.getElem_mem
    · -- Not equal
      unfold is_sparse at h
      rw [List.isChain_iff_getElem] at h
      rw [← eq1, ← eq2]
      rw [List.getElem_tail]
      apply h

-- We can now prove the main theorem: the trivial upper bound on the length
-- of (n,s)-Davenport-Schinzel sequences.
theorem trivial_upper_bound_Davenport_Schinzel_sequence_length {α : Type} [DecidableEq α]
    (n s : ℕ) (u : List α) (h_ds : is_Davenport_Schinzel_sequence n s u) :
    u.length ≤ ((s - 1) / 2) * n * (n - 1) + 1 := by
    obtain ⟨h_bounded, h_sparse, h_max_alt⟩ := h_ds
    have : u.length - 1 ≤ ((s - 1) / 2) * n * (n - 1) := by
      calc u.length - 1
            = (u.toFinset ×ˢ u.toFinset).sum (fun p => count_adjacent_pair p.1 p.2 u) := by
            rw [sum_counts_adjacent_pairs_eq_length_sub_one_of_subset u]
          _ = ∑ p ∈ (distinct_adjacent_pairs u).toFinset, count_adjacent_pair p.1 p.2 u := by
            symm
            apply Finset.sum_subset
            · intro p hp
              simp [List.mem_toFinset,
              distinct_adjacent_pairs_eq_distinct_adjacent_pairs_b] at hp
              unfold distinct_adjacent_pairs_b at hp
              rw [List.mem_dedup, List.mem_zip_iff_getElem] at hp
              rcases hp with ⟨i, hi, _, eq1, eq2⟩
              rw [Finset.mem_product, List.mem_toFinset, List.mem_toFinset]
              constructor
              · rw [← eq1]; apply List.getElem_mem
              · rw [← eq2]; apply List.mem_of_mem_tail; apply List.getElem_mem
            · intro p _ h_not_mem
              rw [List.mem_toFinset, distinct_adjacent_pairs_eq_distinct_adjacent_pairs_b]
                at h_not_mem
              unfold distinct_adjacent_pairs_b at h_not_mem
              rw [List.mem_dedup, List.mem_zip_iff_getElem] at h_not_mem
              simp only [not_exists, not_and] at h_not_mem
              unfold count_adjacent_pair
              rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
              intro i hi
              rw [List.mem_range] at hi
              rename_i a
              simp_all only [Finset.mem_product, List.mem_toFinset, List.length_tail, List.getElem_tail,
                Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq, not_and]
              intro a_1
              obtain ⟨fst, snd⟩ := p
              obtain ⟨left, right⟩ := a
              simp_all only
              apply Aesop.BuiltinRules.not_intro
              intro a
              grind only [= List.getElem?_eq_none, =_ List.contains_iff_mem, List.contains_eq_mem,
                List.getElem_mem, → List.getElem_of_getElem?, getElem?_pos, getElem?_neg, usr
                List.length_pos_of_mem]
          _ ≤ ∑ p ∈ (distinct_adjacent_pairs u).toFinset,
                (s - 1) / 2 := by
            apply Finset.sum_le_sum
            intro p hp
            rw [List.mem_toFinset] at hp
            rw [distinct_adjacent_pairs_eq_distinct_adjacent_pairs_b] at hp
            unfold distinct_adjacent_pairs_b at hp
            rw [List.mem_dedup] at hp
            rw [List.mem_zip_iff_getElem] at hp
            rcases hp with ⟨i, hi, htail, eq1, eq2⟩
            have h_neq : p.1 ≠ p.2 := by
              unfold is_sparse at h_sparse
              rw [List.isChain_iff_getElem] at h_sparse
              rw [← eq1, ← eq2]
              rw [List.getElem_tail]
              apply h_sparse
            apply count_adjacent_pair_le p.1 p.2 u s h_neq h_max_alt
          _ = ((s - 1) / 2) * (distinct_adjacent_pairs u).length := by
            rw [Finset.sum_const, nsmul_eq_mul]
            have h_nodup : (distinct_adjacent_pairs u).Nodup := by
               unfold distinct_adjacent_pairs
               apply List.nodup_dedup
            rw [List.toFinset_card_of_nodup h_nodup]
            apply mul_comm
          _ ≤ ((s - 1) / 2) * (distinct_count_by_dedup u * (distinct_count_by_dedup u - 1)) := by
            apply Nat.mul_le_mul_left
            apply length_distinct_adjacent_pairs_le_mul_sparse u h_sparse
          _ ≤ ((s - 1) / 2) * (n * (n - 1)) := by
            apply Nat.mul_le_mul_left
            apply Nat.mul_le_mul h_bounded
            apply Nat.sub_le_sub_right h_bounded 1
          _ = ((s - 1) / 2) * n * (n - 1) := by ring
    omega

-- Corollary: the set of lengths of (n,s)-Davenport-Schinzel sequences is finite.
lemma finite_Davenport_Schinzel_sequence_lengths {α : Type} [DecidableEq α]
    (n s : ℕ) : (@Davenport_Schinzel_sequences_lengths α _ n s).Finite := by
    apply @Set.Finite.subset ℕ (Set.Icc 0 (((s - 1) / 2) * n * (n - 1) + 1))
    · apply Set.finite_Icc
    · intro l hl
      obtain ⟨u, ⟨h_DS, eq_len⟩⟩ := hl
      have h_len := trivial_upper_bound_Davenport_Schinzel_sequence_length n s u h_DS
      rw [eq_len] at h_len
      simp only [Set.mem_Icc, zero_le, h_len, and_self]
