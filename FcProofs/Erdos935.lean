/-
Copyright (c) 2026 Daniel Veljjanoski. Released under the MIT license.
-/
import FormalConjectures.ErdosProblems.«935»

/-!
# Erdős Problem 935: powerful parts of products of consecutive integers

Proofs of `Erdos935.erdos_935.parts.ii`, `Erdos935.erdos_935.variants.ell_two` and
`Erdos935.erdos_935.variants.mahler` from
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures). Here
$Q_2(m)$ = `Erdos367.B 2 m` is the powerful part of $m$.

All three use solutions of the Pell equation $x^2 = 8y^2 + 1$. Starting from $(3, 1)$ and cubing
$x + y\sqrt 8$ gives $x' = x(x^2 + 24y^2)$, $y' = y(3x^2 + 8y^2)$, and each step multiplies the
power of $3$ dividing $x$ by at least $3$.
* `mahler`: as in Erdős [Er76d, pp. 31-32], for $n = 8y^2$ the number $n(n+1) = 8x^2y^2$ is
  powerful, so $Q_2(n(n+1)\cdots(n+\ell)) \geq n(n+1) > n^2$.
* `parts_ii`: for $n = x - 1$ we have $n(n+2) = 8y^2$ and $3^{k+1} \mid n + 1$, so for $k \geq 1$
  the powerful number $8y^2 \cdot 3^{k+1}$ divides $n(n+1)(n+2)$, giving $Q_2 \geq 3^{k+1} n^2$.
  The constructions credited in the formal-conjectures docstring (van Doorn for Problem 367, and
  Aletheia [Fe26, §4.2]) instead take $n = 8y^2$ and find large square factors of $n + 2$; the
  argument here uses the same Pell equation with $n = x - 1$.
* `ell_two` is the case $\ell = 2$ of `parts_ii`.

A number $d$ is powerful when no prime appears in it exactly once, i.e.
`∀ p, d.factorization p ≠ 1`; such a $d$ dividing $N \neq 0$ is at most $Q_2(N)$ (`le_B_two`).

*References:*
- [Er76d] Erdős, P., *Problems and results on number theoretic properties of consecutive integers
  and related questions*. Proceedings of the Fifth Manitoba Conference on Numerical Mathematics
  (1976), 25-44.
- [Fe26] Feng, T. et al., *Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on the
  Erdős Problems*. [arXiv:2601.22401](https://arxiv.org/abs/2601.22401) (2026). Aletheia is the
  Gemini-based agent of this paper.
-/

open Filter

namespace Erdos935Proof

/-- A product of two nonzero powerful numbers is powerful. -/
theorem factorization_mul_ne_one {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (ha1 : ∀ p, a.factorization p ≠ 1) (hb1 : ∀ p, b.factorization p ≠ 1) (p : ℕ) :
    (a * b).factorization p ≠ 1 := by
  rw [Nat.factorization_mul ha hb, Finsupp.add_apply]
  have := ha1 p
  have := hb1 p
  omega

/-- A `k`-th power with `k ≥ 2` is powerful. -/
theorem factorization_pow_ne_one (a : ℕ) {k : ℕ} (hk : 2 ≤ k) (p : ℕ) :
    (a ^ k).factorization p ≠ 1 := by
  rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  intro h
  have := Nat.eq_one_of_mul_eq_one_right h
  omega

/-- A powerful divisor `d` of `N ≠ 0` is at most the powerful part of `N`. -/
theorem le_B_two {d N : ℕ} (hN : N ≠ 0) (hdN : d ∣ N) (hd : ∀ p, d.factorization p ≠ 1) :
    d ≤ Erdos367.B 2 N := by
  have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero hN hdN
  have hle := (Nat.factorization_le_iff_dvd hd0 hN).2 hdN
  calc d = ∏ p ∈ d.factorization.support, p ^ d.factorization p :=
        (Nat.prod_factorization_pow_eq_self hd0).symm
    _ ≤ ∏ p ∈ d.factorization.support, p ^ N.factorization p :=
        Finset.prod_le_prod' fun p hp ↦
          Nat.pow_le_pow_right (Nat.pos_of_mem_primeFactors (by simpa using hp)) (hle p)
    _ ≤ Erdos367.B 2 N := by
        unfold Erdos367.B
        refine Finset.prod_le_prod_of_subset_of_one_le' (fun p hp ↦ ?_) fun p hp _ ↦ ?_
        · have h1 := hd p
          have h2 := hle p
          rw [Finsupp.mem_support_iff] at hp
          rw [Finset.mem_filter, Finsupp.mem_support_iff]
          omega
        · exact Nat.one_le_pow _ _
            (Nat.pos_of_mem_primeFactors (by simpa using (Finset.mem_filter.1 hp).1))

/-- Solutions of $x^2 = 8y^2 + 1$ with $3^{k+1} \mid x$ and $y > k$. -/
theorem exists_pell (k : ℕ) :
    ∃ x y : ℕ, x ^ 2 = 8 * y ^ 2 + 1 ∧ 3 ^ (k + 1) ∣ x ∧ k < y := by
  induction k with
  | zero => exact ⟨3, 1, by norm_num, by norm_num, by norm_num⟩
  | succ k ih =>
    obtain ⟨x, y, h, hx, hy⟩ := ih
    refine ⟨x * (x ^ 2 + 24 * y ^ 2), y * (3 * x ^ 2 + 8 * y ^ 2), ?_, ?_, ?_⟩
    · have hz : (x : ℤ) ^ 2 = 8 * (y : ℤ) ^ 2 + 1 := by exact_mod_cast h
      -- the norm of $(x + y\sqrt 8)^3$ is the cube of the norm of $x + y\sqrt 8$
      have : ((x : ℤ) * (x ^ 2 + 24 * y ^ 2)) ^ 2 =
          8 * ((y : ℤ) * (3 * x ^ 2 + 8 * y ^ 2)) ^ 2 + 1 := by
        linear_combination (((x : ℤ) ^ 2 - 8 * y ^ 2) ^ 2 + ((x : ℤ) ^ 2 - 8 * y ^ 2) + 1) * hz
      exact_mod_cast this
    · have h3 : 3 ∣ x := (dvd_pow_self 3 k.succ_ne_zero).trans hx
      rw [pow_succ]
      exact mul_dvd_mul hx
        (Nat.dvd_add (dvd_pow h3 two_ne_zero) (Dvd.dvd.mul_right (by norm_num) _))
    · have hy2 : 1 ≤ y ^ 2 := Nat.one_le_pow _ _ (by omega)
      have h8 : 8 ≤ 3 * x ^ 2 + 8 * y ^ 2 := by omega
      exact (by omega : k + 1 < y * 8).trans_le (Nat.mul_le_mul_left y h8)

/-- The second part of Erdős Problem 935: for $\ell \geq 2$,
$\limsup Q_2(n(n+1)\cdots(n+\ell))/n^2 = \infty$. -/
theorem parts_ii : ∀ ℓ : ℕ, 2 ≤ ℓ → ∀ C : ℝ, ∃ᶠ n : ℕ in atTop,
    C * (n : ℝ) ^ 2 < ((Erdos367.B 2 (∏ m ∈ Finset.Icc n (n + ℓ), m) : ℕ) : ℝ) := by
  intro ℓ hℓ C
  rw [frequently_atTop]
  intro N
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt C (by norm_num : (1 : ℝ) < 3)
  obtain ⟨x, y, h, hx, hy⟩ := exists_pell (N + K + 1)
  have hyx : y < x := lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) (by omega)
  obtain ⟨n, rfl⟩ : ∃ n, x = n + 1 := ⟨x - 1, by omega⟩
  have hn2 : 2 ^ 3 * y ^ 2 = n * (n + 2) := by nlinarith [h]
  have hsub : ({n, n + 1, n + 2} : Finset ℕ) ⊆ Finset.Icc n (n + ℓ) := by
    intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rw [Finset.mem_Icc]
    omega
  have hprod := Finset.prod_dvd_prod_of_subset _ _ (fun m : ℕ ↦ m) hsub
  rw [Finset.prod_insert (by simp), Finset.prod_insert (by simp), Finset.prod_singleton] at hprod
  have hdvd : 2 ^ 3 * y ^ 2 * 3 ^ (N + K + 2) ∣ ∏ m ∈ Finset.Icc n (n + ℓ), m := by
    refine dvd_trans ?_ hprod
    rw [hn2]
    calc n * (n + 2) * 3 ^ (N + K + 2) ∣ n * (n + 2) * (n + 1) := mul_dvd_mul_left _ hx
      _ = n * ((n + 1) * (n + 2)) := by ring
  have hP : ∏ m ∈ Finset.Icc n (n + ℓ), m ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun m hm ↦ by rw [Finset.mem_Icc] at hm; omega
  have hy0 : y ^ 2 ≠ 0 := pow_ne_zero _ (by omega)
  have hpow : ∀ p, (2 ^ 3 * y ^ 2 * 3 ^ (N + K + 2)).factorization p ≠ 1 :=
    factorization_mul_ne_one (mul_ne_zero (by norm_num) hy0) (by positivity)
      (factorization_mul_ne_one (by norm_num) hy0
        (factorization_pow_ne_one 2 (by norm_num)) (factorization_pow_ne_one y le_rfl))
      (factorization_pow_ne_one 3 (by omega))
  have hB := le_B_two hP hdvd hpow
  refine ⟨n, by omega, ?_⟩
  have hd : ((2 ^ 3 * y ^ 2 * 3 ^ (N + K + 2) : ℕ) : ℝ) = n * (n + 2) * 3 ^ (N + K + 2) := by
    rw [hn2]
    push_cast
    ring
  have hK' : C < 3 ^ (N + K + 2) := hK.trans_le (pow_le_pow_right₀ (by norm_num) (by omega))
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have h3 : (0 : ℝ) < 3 ^ (N + K + 2) := by positivity
  calc C * (n : ℝ) ^ 2 < 3 ^ (N + K + 2) * (n : ℝ) ^ 2 :=
        mul_lt_mul_of_pos_right hK' (pow_pos (by linarith) 2)
    _ ≤ n * (n + 2) * 3 ^ (N + K + 2) := by nlinarith
    _ = ((2 ^ 3 * y ^ 2 * 3 ^ (N + K + 2) : ℕ) : ℝ) := hd.symm
    _ ≤ _ := by exact_mod_cast hB

/-- The case $\ell = 2$ of `parts_ii`. -/
theorem ell_two : ∀ C : ℝ, ∃ᶠ n : ℕ in atTop,
    C * (n : ℝ) ^ 2 < ((Erdos367.B 2 (∏ m ∈ Finset.Icc n (n + 2), m) : ℕ) : ℝ) :=
  parts_ii 2 le_rfl

/-- The bound implied by a result of Mahler: for $\ell \geq 1$,
$\limsup Q_2(n(n+1)\cdots(n+\ell))/n^2 \geq 1$. -/
theorem mahler : ∀ ℓ : ℕ, 1 ≤ ℓ → ∀ ε : ℝ, 0 < ε → ∃ᶠ n : ℕ in atTop,
    (1 - ε) * (n : ℝ) ^ 2 <
      ((Erdos367.B 2 (∏ m ∈ Finset.Icc n (n + ℓ), m) : ℕ) : ℝ) := by
  intro ℓ hℓ ε hε
  rw [frequently_atTop]
  intro N
  obtain ⟨x, y, h, -, hy⟩ := exists_pell N
  have hyx : y < x := lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) (by omega)
  obtain ⟨n, hn⟩ : ∃ n, n = 8 * y ^ 2 := ⟨_, rfl⟩
  have hy2 : y ≤ y ^ 2 := by nlinarith
  have hsub : ({n, n + 1} : Finset ℕ) ⊆ Finset.Icc n (n + ℓ) := by
    intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rw [Finset.mem_Icc]
    omega
  have hprod := Finset.prod_dvd_prod_of_subset _ _ (fun m : ℕ ↦ m) hsub
  rw [Finset.prod_pair (by omega)] at hprod
  have hd : 2 ^ 3 * y ^ 2 * x ^ 2 = n * (n + 1) := by rw [h, hn]; ring
  have hP : ∏ m ∈ Finset.Icc n (n + ℓ), m ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun m hm ↦ by rw [Finset.mem_Icc] at hm; omega
  have hy0 : y ^ 2 ≠ 0 := pow_ne_zero _ (by omega)
  have hpow : ∀ p, (2 ^ 3 * y ^ 2 * x ^ 2).factorization p ≠ 1 :=
    factorization_mul_ne_one (mul_ne_zero (by norm_num) hy0) (pow_ne_zero _ (by omega))
      (factorization_mul_ne_one (by norm_num) hy0
        (factorization_pow_ne_one 2 (by norm_num)) (factorization_pow_ne_one y le_rfl))
      (factorization_pow_ne_one x le_rfl)
  have hdvd : 2 ^ 3 * y ^ 2 * x ^ 2 ∣ ∏ m ∈ Finset.Icc n (n + ℓ), m := by
    rw [hd]
    exact hprod
  have hB := le_B_two hP hdvd hpow
  rw [hd] at hB
  refine ⟨n, by omega, ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  calc (1 - ε) * (n : ℝ) ^ 2 < (n : ℝ) * (n + 1) := by
        nlinarith [mul_pos hε (pow_pos (show (0 : ℝ) < n by linarith) 2)]
    _ = ((n * (n + 1) : ℕ) : ℝ) := by push_cast; ring
    _ ≤ _ := by exact_mod_cast hB

example : type_of% Erdos935.erdos_935.parts.ii := parts_ii
example : type_of% Erdos935.erdos_935.variants.ell_two := ell_two
example : type_of% Erdos935.erdos_935.variants.mahler := mahler

end Erdos935Proof
