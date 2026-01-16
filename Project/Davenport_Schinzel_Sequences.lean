/-
Copyright (c) 14.01.2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/

import Project.Optimisation_of_max_alternating_length

/-
This file formalises the definition of Davenport-Schinzel sequences and some basic lemmas.
-/

section Davenport_Schinzel_sequences
/-
We now introduce the first non basic definition namely Davenport-Schinzel sequences.
A (n,s)-Davenport-Schinzel sequence (for n,s ∈ ℕ) is a sequence over an n-symbol
alphabet which is sparse and does not contain the subsequence a b a b ... of length s
for any two distinct symbols a and b: i.e. no alternating subsequence of length s.
Obviously, if it contains an alternating subsequence of length bigger than s,
then we have seen previously that it contains an alternating subsequence of length s.
Thus we can define a (n,s)-Davenport-Schinzel sequence as a sequence over an n-symbol
alphabet which is sparse and whose maximum alternating subsequence length is strictly
smaller than s.
--------------------------------------------------------------------------------
ORIGIN: LINEAR DIFFERENTIAL EQUATIONS & UPPER ENVELOPES
--------------------------------------------------------------------------------
The study of Davenport-Schinzel sequences began with Davenport and Schinzel (1965),
who were investigating a problem posed by Malanowski regarding the "upper envelope"
of solutions to a homogeneous linear differential equation.

THE ODE SETTING
Consider a homogeneous (so without constant term) linear differential equation of order
s ∈ ℕ_{≥1} (the case where s = 0 is of obviously of no interest) on ℝ with coefficients c_j ∈ ℂ:

    F(D)y = D^s y+ c₁ D^{s-1} y + ... + cₙy = 0 (where D = d/dx is the differentiation operator).

A fundamental result in the theory of linear ODEs (crucially on ℝ) states that any solution
f : ℝ → ℂ of it is of the form

    f(x) = Σ (k=0 to m) P_k(x) e^{r_k x}

  where r_k are all the distinct roots of F(x) = x^s + c₁ x^{s-1} + ... + cₙ ∈ ℂ[x], and P_k(x) ∈ ℂ[x]
  are any polynomials of degree strictly less than the multiplicity of r_k in F(x) (resp.).

Assume now that the coefficients cᵢ are real numbers and the polynomial F(x) has only real roots.
Then all solutions f(x) are non oscillatory (i.e. no sine or cosine terms because the r_k are real).
We get the bound on the number of zeros: one can show that non-zero solution to such a linear ODE can
have at most s−1 zeros on ℝ. The proof relies on a lemma that applying a term of the sort (D−r_k) to
any differentiable function with at least l distinct zeros (possibly infinite) gives a function with at least
l−1 distinct zeros (possibly infinite) via a variation of Rolle's Theorem (we use the function exp(±r_kx)).
Using this and the fact that the differential operator F(D) factors completely into s first-order terms
(D−r_k), we can prove (by induction on s ≥ 1) the result. The base case being trivial by directly solving
the equation, if we assume the result hold for s ≥ 1 then if we let y be a non zero solution to a
homogeneous linear ODE of order s+1 and we suppose it had a number ≥ s+1 ≥ 2 of zeros (possibly infinite),
then applying one first order operators (D-r_m) coming from F(D) would produce a solution to another
homogeneous linear ODE of order s and hence must have at most s-1 zeros (by our inductive hypothesis),
yielding a contradiction because it should have had at least s zeros (possibly infinite) by our lemma.

Suppose now we are given F = {f₁, ..., fₙ} a set of n distinct (not necessarily independent)
solutions to this equation. We are interested in the "upper envelope" function
g(x) = max {f₁(x), ..., fₙ(x)}. Notice that solutions of such ODE are continuous (even C^∞),
so all functions fᵢ are continuous on ℝ.

Moreover the differential operator F(D) is clearly linear, if fᵢ and fⱼ are distinct solutions,
their difference h = fᵢ - fⱼ is also a solution to the same ODE (F(D)(fᵢ - fⱼ) = F(D)fᵢ - F(D)fⱼ = 0).
Therefore, by the previous result, the functions fᵢ and fⱼ can intersect at most s-1 times (i.e.
h can have at most s-1 zeros) (because they are distinct so the difference is a non zero solutions)
so eventually (towards +∞) one of fᵢ or fⱼ dominates strictly the other
and towards -∞ as well. This implies in general that eventually (towards +∞) one of the functions dominates all
other and towards -∞ as well (since n is finite). Furthermore this implies in general that at each points
x ∈ ℝ (apart finitely many since n is finite), g(x) is determined uniquely by one of the functions fᵢ
(so fᵢ(x)>max{fⱼ(x) | j ≠ i}) and because each function is continuous, fᵢ must dominates strictly all others
function in an open interval around that point x. Hence, we can decompose the real line uniquely into finitely
many non empty disjoint open intervals I_0 = (-∞,a_0), I_1 = (a_0,a_1), ..., I_t = (a_t, +∞) (where if t=0 we
take ℝ) maximal for the property that g(x) = f_{i_k}(x) for some index i_k ∈ {1, ..., n} (so f_i_k dominates
strictly all other function on I_k apart at finitely many points in I_k and so is uniquely determined because
the interval is non empty and open so infinite). Notice that as the intervals are open, non empty and maximal
we also must have i_k ≠ i_{k+1}.

In total we obtain a sequence of the maximal enveloppe on the alphabet {1,...,n}: (i_0, i_1, ..., i_t) which
must be sparse. We can say something more about this sequence: since zeros correspond to intersections
fᵢ(x) = fⱼ(x) ↔ (fᵢ - fⱼ)(x) = 0 which can happen at most s-1 times, the functions fᵢ and fⱼ can alternate dominance
at most s times. Therefore the sequence (i_0, i_1, ..., i_t) cannot contain an alternating subsequence of the form
a, b, a, b, ... of length s+1 (because that would imply s switches/intervals, requiring s roots of fᵢ - fⱼ by continuity).

Thus we have shown that:
The sequence of indices generated by the upper envelope of solutions to a s-th order linear ODE is an
(n, s+1)-Davenport-Schinzel sequence.

Note: the problem asked by Malanowski (in a slightly different way) was to bound the number of intervals
t+1 in terms of n and s. As seen above, any bound on the length of (n, s+1)-Davenport-Schinzel sequences
in terms of n and s will gives us a bound for the original problem. For now, we do not even know if the length
is bounded: it could be that for some n,s there are (n, s)-Davenport-Schinzel sequences of arbitrary length.
--------------------------------------------------------------------------------

In another geometric setting (when s ≥ 2), these sequences could also describe the combinatorial complexity
of the lower envelope of a set of $n$ distinct continuous functions where every pair of functions
intersects in at most $s-2$ points: If F = {f_1, ..., f_n} is a collection of real-valued continuous
functions defined on a common interval I ⊂ ℝ. The lower envelope L_F of F is defined as the pointwise
minimum of the functions f_i, 1 ≤ i ≤ n, over I. Suppose that any pair f_i, f_j (i ≠ j) intersects in
at most s-2 points. Then one can show as before that I can be decomposed into a finite sequence
I_1, ..., I_ℓ of (maximal connected) intervals (where sup I_j = inf Is_{j+1} and inf I_1 = inf I,
sup I_ℓ = sup I) on each of which a unique function from F defines L_F. Define the word of integer in
{1,...,n} φ(F) = (φ_1, ..., φ_ℓ), where f_{φ_i} is the function from F which defines L_F on I_i. One
can make as before the observation that φ(F) is an (n, s)-Davenport-Schinzel sequence over the integer
alphabet {1,...,n}. Why is it the right definition in this context ? Because one can also show that any
(n, s)-Davenport-Schinzel sequence can be realised as the lower envelope of a suitable set of n
distinct continuous functions from ℝ to ℝ where every pair intersects in at most s-2 points.
-/
def is_Davenport_Schinzel_sequence {α : Type} [DecidableEq α]
    (n s : ℕ) (u : List α) : Prop :=
  distinct_count_by_dedup u ≤ n ∧ is_sparse u ∧ max_alternating_length u < s

-- We again do a boolean version for deciding/automation
-- (we use the optimised version for max_alternating_length)
def is_Davenport_Schinzel_sequence_b {α : Type} [DecidableEq α]
    (n s : ℕ) (u : List α) : Bool :=
  (distinct_count_by_dedup u ≤ n) && (is_sparse_b u) && (max_alternating_length_b_opt u < s)

-- The boolean version matches the propositional version
lemma is_Davenport_Schinzel_sequence_b_iff {α : Type} [DecidableEq α]
    (n s : ℕ) (u : List α) :
    is_Davenport_Schinzel_sequence_b n s u = true ↔ is_Davenport_Schinzel_sequence n s u := by
  unfold is_Davenport_Schinzel_sequence_b is_Davenport_Schinzel_sequence
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rw [is_sparse_b_iff, max_alternating_length_eq_max_alternating_length_b_opt]
  simp only [and_assoc]

-- The empty list is a (n,s)-Davenport-Schinzel sequence for any n ≥ 0, s ≥ 1
lemma empty_is_Davenport_Schinzel_sequence {α : Type} [DecidableEq α] (n s : ℕ)
    (h_n : n ≥ 0) (h_s : s ≥ 1) :
    is_Davenport_Schinzel_sequence n s ([] : List α) := by
  unfold is_Davenport_Schinzel_sequence
  constructor
  · trivial
  · constructor
    · unfold is_sparse
      simp only [List.isChain_nil]
    · rw [max_alternating_length_eq_max_alternating_length_b []]
      exact h_s

-- Sequences cannot be (n,0)-Davenport-Schinzel sequences
lemma Davenport_Schinzel_sequence_s_eq_zero {α : Type} [DecidableEq α]
    (n : ℕ) (u : List α) :
    ¬ is_Davenport_Schinzel_sequence n 0 u := by
    unfold is_Davenport_Schinzel_sequence
    intro h_ds
    obtain ⟨h_distinct, h_sparse, h_max_alt⟩ := h_ds
    linarith

-- singleton lists are (n,s)-Davenport-Schinzel sequences for any n ≥ 1, s ≥ 2
lemma singleton_is_Davenport_Schinzel_sequence {α : Type} [DecidableEq α]
    (a : α) (n s : ℕ) (h_n : n ≥ 1) (h_s : s ≥ 2) :
    is_Davenport_Schinzel_sequence n s [a] := by
    unfold is_Davenport_Schinzel_sequence
    constructor
    · trivial
    · constructor
      · apply is_chain_implies_is_sparse
        apply singleton_is_chain
      · rw [max_alternating_length_eq_max_alternating_length_b [a]]
        exact h_s

-- Some examples
#eval is_Davenport_Schinzel_sequence_b 3 6 [1,2,3,2,1,3,2]
#eval is_Davenport_Schinzel_sequence_b 3 5 [1,2,3,2,1,3,2]

-- We define the set of all (n,s)-Davenport-Schinzel sequences over an alphabet α
-- which is infinite when α is infinite and n ≥ 1 and s ≥ 2 (since we don't care
-- what are the letters in the words, only about their adjacency relations, so from
-- one non empty sequence we can create infinitely many).
def Davenport_Schinzel_sequences {α : Type} [DecidableEq α]
    (n s : ℕ) : Set (List α) := {u | is_Davenport_Schinzel_sequence n s u}

/-
As always, we want to do a boolean version for deciding/automation. To define
the computable set of Davenport-Schinzel sequences, we need a finite universe of
candidates. The set of all Davenport-Schinzel sequences is as said potentially
infinite. To create a finite, computable `Finset`, we must parameterise the
definition by a specific length `len` on a finite alphabet: so that we only
consider sequences of that length which are in finite number since the alphabet
is finite. We will see later how to lift these restrictions.
-/

/-
--------------------------------------------------------------------------------
DESIGN CHOICE: COMPUTABLE DEFINITION OF DAVENPORT-SCHINZEL SEQUENCES
--------------------------------------------------------------------------------

To define the set of Davenport-Schinzel sequences in a way that is executable
(computable) by Lean's `#eval`, we make specific design choices distinct from
the propositional logic sections:

1. EXPLICIT ALPHABET AS `List α` INSTEAD OF `[Fintype α]`
   We pass the alphabet explicitly as a `List` rather than relying on Fintype
   class inference for two key reasons:
   a) Computability: Converting a `Finset` (unordered set) to a `List` (ordered)
      is noncomputable in Lean without the Axiom of Choice:

      The Determinism Problem:
      Although in classical logic selecting elements from a finite set does not
      strictly require the Axiom of Choice, computation requires determinism.
      A computable function must produce identical output for identical input.
      Mathematically, the set `{1, 2}` is identical to `{2, 1}`. However, as lists,
      `[1, 2]` ≠ `[2, 1]`.

      To convert a `Finset` to a `List`, the computer must "pick" an order.
      In Lean, making an arbitrary selection requires
      `Classical.choice`. Since `Classical.choice` is an axiom and not an algorithm,
      it is marked `noncomputable`. This prevents `#eval`
      from executing the code. Passing a `List` directly provides the order
      upfront, solving this determinism issue.

      One could say; "just add `[LinearOrder α]` instance to enforce a
      canonical sort (e.g., "smallest first")" but we avoid requiring `LinearOrder`
      because Davenport-Schinzel properties rely only on equality (`DecidableEq`),
      not ordering. Passing a `List` provides directly a pre-determined order easier
      to define rather than showing the type α admits a linear order.

   b) Flexibility: `[Fintype α]` forces the alphabet to be the entire universe
      of the type (e.g., all of `Fin 10`). Using `List` allows us to easily test
      subsets (e.g., only symbols `[0, 1]`) without defining new subtypes.

2. RESTRICTION BY LENGTH
   The set of all Davenport-Schinzel sequences is as said potentially infinite.
   To create a finite, computable `Finset`, we must parameterise the definition by a
   specific length `len`.
--------------------------------------------------------------------------------
-/

/-
Helper: Generate all lists of length `len` using symbols from a list `alphabet`
over the type. We use `List.replicate` and `mapM` (Cartesian product) to build this.
-/
def all_lists_of_length {α : Type} (alphabet : List α) (len : ℕ) : List (List α) :=
  (List.replicate len alphabet).mapM id

lemma mem_all_lists_of_length_iff {α : Type} (alphabet : List α) (len : ℕ) (u : List α) :
  u ∈ all_lists_of_length alphabet len ↔ u.length = len ∧ ∀ x ∈ u, x ∈ alphabet := by
  unfold all_lists_of_length
  induction len generalizing u with
  | zero =>
    simp_all only [List.replicate_zero, List.mapM_nil, List.pure_def, List.mem_cons, List.not_mem_nil, or_false,
      List.length_eq_zero_iff, iff_self_and, IsEmpty.forall_iff, implies_true]
  | succ n ih =>
    rw [List.replicate_succ, List.mapM_cons]
    simp only [List.pure_def, id_eq, List.bind_eq_flatMap, List.mem_flatMap,
      List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro ⟨a, ha, v, hv, rfl⟩
      rw [ih] at hv
      constructor
      · simp [hv.1]
      · intro x hx
        simp at hx
        cases hx with
        | inl h => rw [h]; exact ha
        | inr h => exact hv.2 _ h
    · intro h
      cases u with
      | nil => simp at h
      | cons head tail =>
        simp only [List.length_cons, Nat.succ.injEq, List.mem_cons, forall_eq_or_imp] at h
        refine ⟨head, h.2.1, tail, ?_, rfl⟩
        rw [ih]
        exact ⟨h.1, h.2.2⟩

-- Example usage (notice the duplicates when alphabet has duplicates):
#eval all_lists_of_length [0,1] 2
#eval all_lists_of_length [0, 1, 1] 2

/-
We now define the computable set of (n,s)-Davenport-Schinzel sequences of exactly length `len`.
Mathematically, an alphabet is a set. Computationally, a `List` may contain duplicates
(e.g., `[1, 1, 2]`). If the list is not clean, the helper function will waste
time generating duplicates (as seen above), but the final .toFinset will merge them into a single
result. So to make the design robust and efficient we deduplicate the alphabet first.
-/
def Davenport_Schinzel_sequences_b {α : Type} [DecidableEq α]
    (alphabet : List α) (n s len : ℕ) : List (List α) :=
  ((all_lists_of_length alphabet.dedup len).filter (is_Davenport_Schinzel_sequence_b n s))

/-
We connect the computable definition of this set to the propositional one. If the input
list covers the whole type (without duplicates) (so the type is finite), it matches the
logical definition for that specific length.
-/
lemma mem_Davenport_Schinzel_sequences_b_iff {α : Type} [DecidableEq α] [Fintype α]
    (n s len : ℕ) (u : List α) :
    u ∈ Davenport_Schinzel_sequences_b (Finset.univ.toList) n s len ↔
    u ∈ Davenport_Schinzel_sequences n s ∧ u.length = len := by
  unfold Davenport_Schinzel_sequences_b Davenport_Schinzel_sequences all_lists_of_length
  simp only [List.mem_filter, Set.mem_setOf_eq]
  rw [and_comm, and_congr]
  · exact is_Davenport_Schinzel_sequence_b_iff n s u
  · erw [mem_all_lists_of_length_iff]
    simp only [List.mem_dedup, Finset.mem_toList, Finset.mem_univ, implies_true, and_true]

/-
The set of all (n,s)-Davenport-Schinzel sequences over an alphabet α is nonempty as long as
n ≥ 0 and s ≥ 1.
-/
lemma Davenport_Schinzel_sequences_nonempty {α : Type} [DecidableEq α]
(n s : ℕ) (h_n : n ≥ 0) (h_s : s ≥ 1) : (@Davenport_Schinzel_sequences α _ n s).Nonempty := by
  unfold Set.Nonempty
  use ([] : List α)
  apply empty_is_Davenport_Schinzel_sequence n s h_n h_s

lemma Davenport_Schinzel_sequences_s_eq_zero_is_empty {α : Type} [DecidableEq α]
    (n : ℕ) :
    (@Davenport_Schinzel_sequences α _ n 0) = ∅ := by
    unfold Davenport_Schinzel_sequences
    simp only [Davenport_Schinzel_sequence_s_eq_zero, Set.setOf_false]

end Davenport_Schinzel_sequences

section Davenport_Schinzel_sequences_lengths
-- We now define the set of lengths of all (n,s)-Davenport-Schinzel sequences over an alphabet α.
def Davenport_Schinzel_sequences_lengths {α : Type} [DecidableEq α] (n s : ℕ) : Set ℕ :=
  {len | ∃ u : List α, u ∈ Davenport_Schinzel_sequences n s ∧ u.length = len}

-- Such a set is nonempty as long as n ≥ 0 and s ≥ 1
lemma Davenport_Schinzel_sequences_lengths_nonempty {α : Type} [DecidableEq α]
(n s : ℕ) (h_n : n ≥ 0) (h_s : s ≥ 1) :
  (@Davenport_Schinzel_sequences_lengths α _ n s).Nonempty := by
  unfold Set.Nonempty
  obtain ⟨u, hu_mem⟩ := @Davenport_Schinzel_sequences_nonempty α _ n s h_n h_s
  use u.length
  exact ⟨u, hu_mem, rfl⟩

-- The property of being a (n,s)-Davenport-Schinzel sequence is montone
-- (again by taking the first n elements).
lemma Davenport_Schinzel_subsequence_of_smaller_length {α : Type} [DecidableEq α]
    (n s k : ℕ) {v : List α} (h_ds : is_Davenport_Schinzel_sequence n s v)
    (h_len : k ≤ v.length) :
    is_Davenport_Schinzel_sequence n s (v.take k) ∧ (v.take k).length = k := by
    unfold is_Davenport_Schinzel_sequence at h_ds ⊢
    obtain ⟨h_distinct, h_sparse, h_max_alt⟩ := h_ds
    constructor
    · constructor
      · calc distinct_count_by_dedup (v.take k)
          ≤ distinct_count_by_dedup v := distinct_count_sublist (List.take_sublist k v)
        _ ≤ n := h_distinct
      · constructor
        · exact (sparse_subsequence_of_smaller_length v h_sparse k h_len).1
        · calc max_alternating_length (List.take k v)
              ≤ max_alternating_length v := by
                apply max_alternating_length_monotonic
                apply List.take_sublist
            _ < s := h_max_alt
    · exact List.length_take_of_le h_len

end Davenport_Schinzel_sequences_lengths

section Type_Independence_of_Davenport_Schinzel_Sequences_Lengths

/-
We wish to show the following:
If α is a type with decidable equality and n ≤ |α| then for all s len : ℕ
there is a (n,s)-Davenport-Schinzel sequence of length len over α if and only if
there is a (n,s)-Davenport-Schinzel sequence of length len over ℕ.
-/

/-
We first prove some lemmas about the behavior of mapping list
through an injective function.
-/

-- The number of distinct elements after deduplication is preserved.
lemma distinct_count_by_dedup_map_of_injective {α β : Type}
    [DecidableEq α] [DecidableEq β]
    (f : α → β) (u : List α)
    (h_inj : ∀ x ∈ u, ∀ y ∈ u, f x = f y → x = y) :
    distinct_count_by_dedup (u.map f) = distinct_count_by_dedup u := by
  simp only [distinct_count_by_dedup_eq_distinct_count_by_finset]
  unfold distinct_count_by_finset
  have h_eq : (u.map f).toFinset = u.toFinset.image f := by
     ext y
     simp only [List.mem_toFinset, Finset.mem_image, List.mem_map]
  rw [h_eq]
  apply Finset.card_image_of_injOn
  intro x hx y hy hxy
  apply h_inj x (List.mem_toFinset.1 hx) y (List.mem_toFinset.1 hy) hxy

-- The length is also preserved.
lemma length_map {α β : Type} (f : α → β) (u : List α) :
    (u.map f).length = u.length := by
  induction u
  · simp only [List.map_nil, List.length_nil]
  · rename_i _ _ ih
    simp only [List.map_cons, List.length_cons, ih]

-- The sparsity property is also preserved.
lemma is_sparse_map_of_injective {α β : Type}
    [DecidableEq α] [DecidableEq β]
    (f : α → β) (u : List α)
    (h_inj : ∀ x ∈ u, ∀ y ∈ u, f x = f y → x = y) :
    is_sparse (u.map f) ↔ is_sparse u := by
  dsimp [is_sparse]
  rw [List.isChain_map]
  rw [List.IsChain.iff_mem (R := fun x y => f x ≠ f y), List.IsChain.iff_mem (R := (· ≠ ·))]
  apply List.IsChain.iff
  intro x y
  constructor
  · intro ⟨hx, hy, h_neq⟩
    have : f x ≠ f y → x ≠ y := by
      grind
    simp_all only [ne_eq, not_false_eq_true, this h_neq, imp_self, and_self]
  · intro ⟨hx, hy, h_neq⟩
    have : x ≠ y → f x ≠ f y := by
      contrapose!
      exact h_inj x hx y hy
    simp_all only [ne_eq, not_false_eq_true, this h_neq, imp_self, and_self]

-- Thus the alternating property is also preserved.
lemma is_alternating_map_of_injective {α β : Type}
    [DecidableEq α] [DecidableEq β]
    (f : α → β) (u : List α)
    (h_inj : ∀ x ∈ u, ∀ y ∈ u, f x = f y → x = y) :
    is_alternating (u.map f) ↔ is_alternating u := by
  unfold is_alternating
  rw [is_sparse_map_of_injective f u h_inj]
  rw [distinct_count_by_dedup_map_of_injective f u h_inj]

-- The maximum alternating length is also preserved.
lemma max_alternating_length_map_of_injective {α β : Type}
    [DecidableEq α] [DecidableEq β]
    (f : α → β) (v : List α)
    (h_inj : ∀ x ∈ v, ∀ y ∈ v, f x = f y → x = y) :
    max_alternating_length (v.map f) = max_alternating_length v := by
  apply le_antisymm
  · apply Finset.max'_le
    intro n hn
    rw [Set.Finite.mem_toFinset] at hn
    obtain ⟨u', hu'_mem, hu'_len⟩ := hn
    unfold alternating_subsequences at hu'_mem
    obtain ⟨h_sub', h_alt'⟩ := hu'_mem
    rw [List.sublist_map_iff] at h_sub'
    obtain ⟨u, h_sub, rfl⟩ := h_sub'
    rw [List.length_map] at hu'_len
    rw [← hu'_len]
    have h_inj_u : ∀ x ∈ u, ∀ y ∈ u, f x = f y → x = y := by
      intro x hx y hy h
      apply h_inj x (List.Sublist.subset h_sub hx) y (List.Sublist.subset h_sub hy) h
    rw [is_alternating_map_of_injective f u h_inj_u] at h_alt'
    apply le_max_alternating_length u v ⟨h_sub, h_alt'⟩
  · apply Finset.max'_le
    intro n hn
    rw [Set.Finite.mem_toFinset] at hn
    obtain ⟨u, hu_mem, hu_len⟩ := hn
    unfold alternating_subsequences at hu_mem
    obtain ⟨h_sub, h_alt⟩ := hu_mem
    let u' := u.map f
    have h_sub' : List.Sublist u' (v.map f) := List.Sublist.map f h_sub
    have h_inj_u : ∀ x ∈ u, ∀ y ∈ u, f x = f y → x = y := by
       intro x hx y hy h
       apply h_inj x (List.Sublist.subset h_sub hx) y (List.Sublist.subset h_sub hy) h
    rw [← is_alternating_map_of_injective f u h_inj_u] at h_alt
    rw [← hu_len, ← List.length_map f]
    apply le_max_alternating_length u' (v.map f) ⟨h_sub', h_alt⟩

-- We can show the type-independence of being a
-- (n,s)-Davenport-Schinzel sequence.
lemma is_Davenport_Schinzel_sequence_map_of_injective {α β : Type}
    [DecidableEq α] [DecidableEq β]
    (f : α → β) (v : List α) (n s : ℕ)
    (h_inj : ∀ x ∈ v, ∀ y ∈ v, f x = f y → x = y) :
    is_Davenport_Schinzel_sequence n s v ↔ is_Davenport_Schinzel_sequence n s (v.map f) := by
  unfold is_Davenport_Schinzel_sequence
  rw [distinct_count_by_dedup_map_of_injective f v h_inj,
  is_sparse_map_of_injective f v h_inj,
  max_alternating_length_map_of_injective f v h_inj]

-- We need a construction of a function from ℕ to a type α of large
-- enough cardinality, injective on a given list of natural numbers.
noncomputable def functionFromList {α : Type} [DecidableEq α]
    (l : List ℕ) (n : ℕ) (hn : n ≥ 1)
    (h_distinct : distinct_count_by_dedup l ≤ n)
    (h_card : n ≤ Cardinal.mk α) : ℕ → α := by
  have : Cardinal.mk { x // x ∈ l.toFinset } ≤ Cardinal.mk α := by
    calc Cardinal.mk { x // x ∈ l.toFinset }
          = ↑(distinct_count_by_finset l) := by
            unfold distinct_count_by_finset
            rw [Cardinal.mk_coe_finset]
        _ ≤ ↑n := by
            rw [distinct_count_by_dedup_eq_distinct_count_by_finset] at h_distinct
            simp_all only [ge_iff_le, Nat.cast_le]
        _ ≤ Cardinal.mk α := h_card
  -- Obtain the embedding from the inequality
  let embedding : l.toFinset ↪ α := Classical.choice ((Cardinal.le_def l.toFinset α).1 this)
  -- Define the function
  have : Nonempty α := by
    -- this is because n ≥ 1 and n ≤ |α| so |α| ≥ 1 so α is nonempty
    by_contra h
    simp only [not_nonempty_iff] at h
    simp_all only [ge_iff_le, Cardinal.mk_eq_zero, nonpos_iff_eq_zero, Nat.cast_eq_zero,
      one_ne_zero]
  exact fun x =>
    if h : x ∈ l.toFinset then
      embedding ⟨x, h⟩
    else
      Classical.choice inferInstance

-- We get the desired result.
lemma Davenport_Schinzel_sequences_length_indep_of_type {α : Type} [DecidableEq α]
    (n : ℕ) (h1 : n ≤ Cardinal.mk α)
    (s : ℕ) (len : ℕ) :
    (len ∈ @Davenport_Schinzel_sequences_lengths α _ n s) ↔
    (len ∈ @Davenport_Schinzel_sequences_lengths ℕ _ n s) := by
    constructor
    · intro h
      obtain ⟨u, hu_ds, hu_len⟩ := h
      -- Construct the injective map from the symbols in u to ℕ
      let f : α → ℕ := λ x => u.dedup.idxOf x
      use u.map f
      constructor
      · apply (is_Davenport_Schinzel_sequence_map_of_injective f u n s _).mp hu_ds
        intro x hx y hy hxy
        dsimp [f] at hxy
        apply (List.idxOf_inj (List.mem_dedup.2 hx)).mp hxy
      · rw [length_map, hu_len]
    · intro ⟨v, hv_ds, hv_len⟩
      -- we do a case analysis on whether v is empty or not
      by_cases h_empty : v = []
      · rw [h_empty] at hv_len
        rw [← hv_len]
        use []
        rw [h_empty] at hv_ds
        have hs : s > 0 := by
          by_contra h
          simp only [gt_iff_lt, not_lt, nonpos_iff_eq_zero] at h
          simp_all only [Davenport_Schinzel_sequences_s_eq_zero_is_empty, Set.mem_empty_iff_false]
        constructor
        · apply empty_is_Davenport_Schinzel_sequence n s (by linarith) hs
        · rfl
      · have hk_pos : n ≥ 1 := by
          calc n ≥ distinct_count_by_dedup v := hv_ds.1
            _ ≥ 1 := by
              apply Nat.succ_le_of_lt
              apply List.length_pos_of_ne_nil
              simp [h_empty]
        -- Construct the injective map from the symbols in v to α
        let g := functionFromList v n hk_pos hv_ds.1 h1
        -- g is injective on the symbols in v
        have h_inj : ∀ x ∈ v, ∀ y ∈ v, g x = g y → x = y := by
          intro x hx y hy hxy
          unfold g functionFromList at hxy
          simp_all only [List.mem_toFinset, ↓reduceDIte,
            EmbeddingLike.apply_eq_iff_eq, Subtype.mk.injEq]
        use v.map g
        constructor
        · apply (is_Davenport_Schinzel_sequence_map_of_injective g v n s h_inj).mp hv_ds
        · rw [length_map, hv_len]

end Type_Independence_of_Davenport_Schinzel_Sequences_Lengths
