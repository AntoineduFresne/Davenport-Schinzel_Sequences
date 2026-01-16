/-
Copyright (c) 14.01.2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/

import Project.ExtremalFunction
import Project.Decomposition_and_PSI

/-
This file formalises some bounds on the extremal function.
-/

/-
From our previous discussion, we can fix the decidable
type to be ℕ without loss of generality.
-/

/-
We prove the general bound (that we used to prove finiteness of the extremal function).
-/
-- Longest_DS_func(n, s) ≤ ((s - 1)/2) * n * (n - 1) + 1 for all n,s (with s ≥ 1).
theorem General_Bound (n s : ℕ) (h : s ≥ 1) :
    @Longest_DS_func ℕ _ n s h ≤ ((s - 1) / 2) * n * (n-1) + 1 := by
  apply Finset.max'_le
  intro l hl
  rw [Set.Finite.mem_toFinset] at hl
  obtain ⟨u, hu, rfl⟩ := hl
  exact trivial_upper_bound_Davenport_Schinzel_sequence_length n s u hu

/-
We now prove a non-trivial bound on the extremal function for s = 5:

∃ C ≥ 0, ∀ n ∈ ℕ, Longest_DS_func(n, 5) < 2nα_{ω}(n) + Cnα_{ω}(n)^{1/2}

where α_{ω} is the inverse Ackermann function. Simply:

Longest_DS_func(n, 5) is in 2nα_{ω}(n) + O(n α_{ω}(n)^{1/2}).

For this we utilise two helper lemmas. The first one is very precise:
-/
lemma Precise_Bound5 (n l : ℕ) (hl : l ≥ 2) (hn : n ≥ 1) :
    @Longest_DS_func ℕ _ n 5 (by norm_num) ≤
      @psi ℕ _ (Nat.ceil (2 * n)/ l) n + 2 * l * (l - 1) * (Nat.ceil (2 * n)/ l) := by
    -- we skip this proof due to time constraints
  sorry

-- Specializing this precise bound using the upper bound on psi we proved earlier:
lemma Specialised_Precise_Bound5 (n l : ℕ) (hl : l ≥ 2) (hn : n ≥ 1) (h : l ≤ 2 * n) :
    let n_l := Nat.ceil (2 * n) / l
    @Longest_DS_func ℕ _ n 5 (by norm_num) ≤
      8 * n_l * KlazarAckermann.alpha_omega n_l
      + 8 * n_l
      + 2 * n * KlazarAckermann.alpha_omega n_l
      + 2 * n
      + 2 * l * (l - 1) * n_l := by
  intro n_l
  have : n_l ≥ 1 := by
    unfold n_l
    by_contra h_contra
    simp_all only [ge_iff_le, Nat.ceil_nat, id_eq, not_le, Nat.lt_one_iff, Nat.div_eq_zero_iff]
    cases h_contra with
    | inl h_1 =>
      subst h_1
      simp_all only [nonpos_iff_eq_zero, OfNat.ofNat_ne_zero]
    | inr h_2 => linarith
  have bound1 := Precise_Bound5 n l hl hn
  have bound2 := specialised_psi_upper_bound n_l n this hn
  calc
    @Longest_DS_func ℕ _ n 5 (by norm_num)
      ≤ @psi ℕ _ n_l n + 2 * l * (l - 1) * n_l := bound1
    _ ≤ (8 * n_l * KlazarAckermann.alpha_omega n_l + 8 * n_l + 2 * n * KlazarAckermann.alpha_omega n_l + 2 * n)
        + 2 * l * (l - 1) * n_l := by linarith


-- Finally we can prove the desired bound by specializing l appropriately
theorem Bound5 : ∃ C, ∀ n ≥ 1,
    @Longest_DS_func ℕ _ n 5 (by norm_num) ≤
    2 * n * KlazarAckermann.alpha_omega n + C * n * (KlazarAckermann.alpha_omega n).sqrt := by
  /-
  One can assume n is large enough such that alpha_omega(n) ≥ 4 otherwise n is bounded and so is Longest_DS_func(n, 5).
  so we can pick C large enough to cover these small 1 ≤ n ≤ F_omega(4). At the end we will take the max of
  this constant and the one we get for large n. Now that we have n such that alpha_omega(n) ≥ 4, we can pick
  l = ⌊alpha_omega(n)^{1/2}⌋ ≥ 2. Clearly α_omega(n)^{1/2} ≤ 2n. So we get the bound by specializing
  the previous lemma and regrouping terms. One will need to do some inequalities on the Ackermann function
  to show that KlazarAckermann.alpha_omega(ceil(2n/l)) ≤ KlazarAckermann.alpha_omega(n) and other similar
  inequalities.
  -/
  -- we skip this proof due to time constraints
  sorry
