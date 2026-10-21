/-
Copyright (c) 2026 Daniel Veljjanoski. Released under the MIT license.
-/
import FormalConjectures.ErdosProblems.«670»

/-!
# Erdős Problem 670: the trivial lower bound

A proof of `Erdos670.erdos_670.variants.choose_two` from
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures): if a set $A$ of
$n \neq 2$ points in $\mathbb{R}^d$ has all pairwise distances at least $1$ apart, then its
diameter is at least $\binom{n}{2}$.

For $n \geq 3$, every distance is at least $1$: given $a \neq b$ and a third point $c$,
$1 \leq \lvert d(a, c) - d(b, c)\rvert \leq d(a, b)$. The $\binom{n}{2}$ distances are then
distinct reals that are at least $1$ and at least $1$ apart, so the largest is at least
$\binom{n}{2}$.
-/

open scoped Finset

namespace Erdos670Proof

open Erdos670

/-- A nonempty finite set of reals that are at least `1` and pairwise at least `1` apart has an
element at least its cardinality. -/
theorem exists_card_le (D : Finset ℝ) (hD : D.Nonempty) (h1 : ∀ x ∈ D, 1 ≤ x)
    (hsep : ∀ x ∈ D, ∀ y ∈ D, x < y → x + 1 ≤ y) : ∃ x ∈ D, (#D : ℝ) ≤ x := by
  induction D using Finset.induction_on_max with
  | empty => exact absurd hD Finset.not_nonempty_empty
  | insert a s ha ih =>
    have has : a ∉ s := fun h ↦ lt_irrefl a (ha a h)
    rw [Finset.card_insert_of_notMem has]
    rcases s.eq_empty_or_nonempty with rfl | hs
    · exact ⟨a, by simp, by simpa using h1 a (by simp)⟩
    · obtain ⟨x, hx, hxs⟩ := ih hs (fun x hx ↦ h1 x (by simp [hx]))
        (fun x hx y hy ↦ hsep x (by simp [hx]) y (by simp [hy]))
      have hxa := hsep x (by simp [hx]) a (by simp) (ha x hx)
      exact ⟨a, by simp, by push_cast; linarith⟩

variable {d : ℕ}

/-- With at least three points and separated distances, every distance is at least `1`. -/
theorem one_le_dist {A : Finset (EuclideanSpace ℝ (Fin d))} (hA : HasSeparatedDistances A)
    (h3 : 3 ≤ #A) {a b : EuclideanSpace ℝ (Fin d)} (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b) :
    1 ≤ dist a b := by
  have hpos : 0 < #((A.erase a).erase b) := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hab.symm, hb⟩),
      Finset.card_erase_of_mem ha]
    omega
  obtain ⟨c, hc⟩ := Finset.card_pos.1 hpos
  simp only [Finset.mem_erase] at hc
  obtain ⟨hcb, hca, hcA⟩ := hc
  have hne : s(a, c) ≠ s(b, c) := by
    intro h
    rcases Sym2.eq_iff.1 h with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact hab h1
    · exact hca h1.symm
  calc 1 ≤ |dist a c - dist b c| := hA a ha c hcA b hb c hcA (Ne.symm hca) (Ne.symm hcb) hne
    _ ≤ dist a b := abs_dist_sub_le a b c

/-- The trivial lower bound of Erdős Problem 670: a set of $n \neq 2$ points with separated
distances has diameter at least $\binom{n}{2}$. -/
theorem choose_two (d : ℕ) (A : Finset (EuclideanSpace ℝ (Fin d)))
    (hA : HasSeparatedDistances A) (hn : A.card ≠ 2) :
    (A.card.choose 2 : ℝ) ≤ Metric.diam (A : Set (EuclideanSpace ℝ (Fin d))) := by
  classical
  have hbdd : Bornology.IsBounded (A : Set (EuclideanSpace ℝ (Fin d))) :=
    A.finite_toSet.isBounded
  rcases Nat.lt_or_ge A.card 3 with h | h3
  · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
    exact Metric.diam_nonneg
  -- unordered pairs of distinct points, and their distances
  set U := A.offDiag.image Sym2.mk.uncurry with hU
  let δ : Sym2 (EuclideanSpace ℝ (Fin d)) → ℝ := Sym2.lift ⟨fun a b ↦ dist a b, dist_comm⟩
  have hmem : ∀ z ∈ U, ∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧ z = s(a, b) := by
    intro z hz
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.1 hz
    obtain ⟨ha, hb, hne⟩ := Finset.mem_offDiag.1 hab
    exact ⟨a, ha, b, hb, hne, rfl⟩
  have hsep : ∀ z ∈ U, ∀ w ∈ U, z ≠ w → 1 ≤ |δ z - δ w| := by
    intro z hz w hw hzw
    obtain ⟨a, ha, b, hb, hab, rfl⟩ := hmem z hz
    obtain ⟨c, hc, e, he, hce, rfl⟩ := hmem w hw
    exact hA a ha b hb c hc e he hab hce hzw
  have hinj : Set.InjOn δ U := by
    intro z hz w hw hzw
    by_contra hne
    have := hsep z hz w hw hne
    rw [hzw, sub_self, abs_zero] at this
    norm_num at this
  set D := U.image δ
  have hcard : #D = A.card.choose 2 := by
    rw [Finset.card_image_of_injOn hinj, hU]
    exact Sym2.card_image_offDiag A
  have hDne : D.Nonempty := by
    rw [← Finset.card_pos, hcard]
    exact Nat.choose_pos (by omega)
  obtain ⟨x, hxD, hx⟩ := exists_card_le D hDne
    (by
      intro x hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨a, ha, b, hb, hab, rfl⟩ := hmem z hz
      exact one_le_dist hA h3 ha hb hab)
    (by
      intro x hx y hy hxy
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hy
      have := hsep z hz w hw (fun h ↦ hxy.ne (h ▸ rfl))
      rw [abs_sub_comm, abs_of_pos (sub_pos.2 hxy)] at this
      linarith)
  rw [hcard] at hx
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hxD
  obtain ⟨a, ha, b, hb, -, rfl⟩ := hmem z hz
  exact hx.trans (Metric.dist_le_diam_of_mem hbdd ha hb)

/-- The statement proved above is exactly the repository statement. -/
example : type_of% Erdos670.erdos_670.variants.choose_two := choose_two

end Erdos670Proof
