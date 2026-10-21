/-
Copyright (c) 2026 Daniel Veljjanoski. Released under the MIT license.
-/
import FormalConjectures.ErdosProblems.«588»

/-!
# Erdős Problem 588: the trivial upper bound

A proof of `Erdos588.erdos_588.variants.trivial_upper` from
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures): for $k \geq 2$,
$f_k(n) \cdot k(k-1) \leq n(n-1)$, where $f_k(n)$ is `Erdos588.numLinesWithPointsMax k n`.

The proof counts ordered pairs of distinct points. A line with exactly $k$ points of $S$ contains
$k(k-1)$ such pairs, and two different lines share no pair, since two distinct points span only
one line.
-/

open EuclideanGeometry
open scoped Finset

namespace Erdos588Proof

open Erdos588

/-- For finite `S`, `linesWithPointsFor k S` is finite: each of its lines is spanned by a pair of
points of `S`. -/
theorem linesWithPointsFor_finite (k : ℕ) {S : Set ℝ²} (hS : S.Finite) :
    (linesWithPointsFor k S).Finite := by
  refine (hS.image2 (fun p q ↦ affineSpan ℝ {p, q}) hS).subset ?_
  rintro L ⟨⟨p, hp, q, hq, -, rfl⟩, -⟩
  exact ⟨p, hp, q, hq, rfl⟩

/-- Double counting of ordered pairs: a line with exactly `k` points of `S` contains `k(k-1)`
ordered pairs of distinct points of `S`, and two different lines share no such pair. -/
theorem ncard_linesWithPointsFor_mul_le (k : ℕ) {S : Set ℝ²} (hS : S.Finite) :
    (linesWithPointsFor k S).ncard * (k * (k - 1)) ≤ S.ncard * (S.ncard - 1) := by
  classical
  have hfin := linesWithPointsFor_finite k hS
  set T := hS.toFinset
  set 𝓛 := hfin.toFinset
  let pairs : AffineSubspace ℝ ℝ² → Finset (ℝ² × ℝ²) :=
    fun L ↦ T.offDiag.filter fun pq ↦ pq.1 ∈ L ∧ pq.2 ∈ L
  have hcard : ∀ L ∈ 𝓛, #(pairs L) = k * (k - 1) := by
    intro L hL
    rw [Set.Finite.mem_toFinset] at hL
    have hU : #(T.filter (· ∈ L)) = k := by
      rw [← hL.2, ← Set.ncard_coe_finset]
      congr 1
      ext x
      simp [T, and_comm]
    have hpairs : pairs L = (T.filter (· ∈ L)).offDiag := by
      ext ⟨x, y⟩
      simp only [pairs, Finset.mem_filter, Finset.mem_offDiag]
      tauto
    rw [hpairs, Finset.offDiag_card, hU, Nat.mul_sub_one]
  have hdisj : ∀ L ∈ 𝓛, ∀ L' ∈ 𝓛, L ≠ L' → Disjoint (pairs L) (pairs L') := by
    intro L hL L' hL' hne
    rw [Finset.disjoint_left]
    rintro ⟨p, q⟩ h1 h2
    simp only [pairs, Finset.mem_filter, Finset.mem_offDiag] at h1 h2
    obtain ⟨⟨-, -, hpq⟩, hpL, hqL⟩ := h1
    obtain ⟨-, hpL', hqL'⟩ := h2
    rw [Set.Finite.mem_toFinset] at hL hL'
    obtain ⟨⟨a, -, b, -, -, rfl⟩, -⟩ := hL
    obtain ⟨⟨a', -, b', -, -, rfl⟩, -⟩ := hL'
    exact hne ((affineSpan_pair_eq_of_mem_of_mem_of_ne hpL hqL hpq).symm.trans
      (affineSpan_pair_eq_of_mem_of_mem_of_ne hpL' hqL' hpq))
  have hsum : #(𝓛.biUnion pairs) = #𝓛 * (k * (k - 1)) := by
    rw [Finset.card_biUnion hdisj, Finset.sum_congr rfl hcard, Finset.sum_const, smul_eq_mul]
  have hsub : 𝓛.biUnion pairs ⊆ T.offDiag :=
    Finset.biUnion_subset.2 fun L _ ↦ Finset.filter_subset _ _
  have hle := Finset.card_le_card hsub
  rw [hsum, Finset.offDiag_card, ← Nat.mul_sub_one] at hle
  rwa [Set.ncard_eq_toFinset_card _ hfin, Set.ncard_eq_toFinset_card _ hS]

/-- The trivial upper bound of Erdős Problem 588: for $k \geq 2$,
$f_k(n) \cdot k(k-1) \leq n(n-1)$.

The per-set bound `ncard_linesWithPointsFor_mul_le` holds for every finite `S`, without the
hypothesis that no $k+1$ points are on a line; `2 ≤ k` is only used to divide by $k(k-1)$. -/
theorem trivial_upper (k n : ℕ) (hk : 2 ≤ k) :
    numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1) := by
  have hpos : 0 < k * (k - 1) := Nat.mul_pos (by omega) (by omega)
  rw [← Nat.le_div_iff_mul_le hpos]
  apply csSup_le'
  rintro _ ⟨S, rfl, hS, -, rfl⟩
  rw [Nat.le_div_iff_mul_le hpos]
  exact ncard_linesWithPointsFor_mul_le k hS

/-- The statement proved above is exactly the repository statement. -/
example : type_of% Erdos588.erdos_588.variants.trivial_upper := trivial_upper

end Erdos588Proof
