/-
Copyright (c) 2026 Daniel Veljjanoski. Released under the MIT license.
-/
import FormalConjectures.OEIS.«60841»

/-!
# OEIS A060841: when is `1 / det (1 / lcm (i, j))` an integer?

A proof of `OeisA60841.conjecture1` from
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures): for $n \geq 1$ the
reciprocal of the determinant of the $n \times n$ matrix with entries $1/\operatorname{lcm}(i,j)$ is
an integer if and only if $n \in \{1, \dots, 34\} \cup \{36, 38\}$ (R. G. Wilson v, 2015).

Since $1/\operatorname{lcm}(i,j) = \gcd(i,j)/(ij)$ and, by Gauss's identity
$\sum_{d \mid m} \varphi(d) = m$, the gcd matrix factors as
$E \cdot \operatorname{diag}(\varphi) \cdot E^{\mathsf T}$ with $E$ the unitriangular divisibility
matrix $E_{id} = [d \mid i]$ (Smith's determinant), we get
$1/\det = (n!)^2 / \prod_{k \leq n} \varphi(k)$. For $n \leq 38$ the divisibility is decided by
computation. For the other $n$ the obstruction is $2$-adic: from
$v_2(\varphi(k)) = \max(v_2(k) - 1, 0) + \sum_{p \mid k \text{ odd}} v_2(p - 1)$, the odd primes up
to $97$ and the powers $4, \dots, 128$ give $v_2(\prod \varphi(k)) \geq c(n)$ with
$c(n) = \sum_p v_2(p-1) \lfloor n/p \rfloor + \sum_{j=2}^{7} \lfloor n/2^j \rfloor$, while
$v_2((n!)^2) = 2 \sum_{j \geq 1} \lfloor n/2^j \rfloor$; for $n = 35, 37$ and $39 \leq n < 100$ the
inequality $c(n) > 2 v_2(n!)$ is decided numerically, and for $n \geq 100$ it follows from
$\lfloor n/m \rfloor \geq (n + 1 - m)/m$ and $v_2(n!) \leq n$.
-/

open Nat Finset Matrix

namespace OeisA060841Proof

open OeisA60841

-- ### The product of totients and the divisibility matrix

/-- `∏_{k = 1}^{n} φ(k)`. -/
def totientProd (n : ℕ) : ℕ := ∏ i ∈ range n, φ (i + 1)

lemma totientProd_pos (n : ℕ) : 0 < totientProd n :=
  Finset.prod_pos fun i _ ↦ totient_pos.2 (Nat.succ_pos i)

/-- The divisibility matrix: `E i d = 1` if `d + 1 ∣ i + 1`, else `0`. -/
def divMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun i d ↦ if (d : ℕ) + 1 ∣ (i : ℕ) + 1 then 1 else 0

/-- The gcd matrix `gcd (i + 1) (j + 1)`. -/
def gcdMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun i j ↦ (Nat.gcd ((i : ℕ) + 1) ((j : ℕ) + 1) : ℚ)

lemma divMatrix_isLowerTriangular (n : ℕ) : (divMatrix n).IsLowerTriangular := by
  intro i d hid
  have hlt : i < d := OrderDual.toDual_lt_toDual.mp hid
  simp only [divMatrix, Matrix.of_apply]
  rw [if_neg]
  intro h
  have := Nat.le_of_dvd (Nat.succ_pos _) h
  have : (i : ℕ) < d := hlt
  omega

lemma det_divMatrix (n : ℕ) : (divMatrix n).det = 1 := by
  rw [det_of_isLowerTriangular _ (divMatrix_isLowerTriangular n)]
  simp [divMatrix]

/-- Gauss's identity in the form needed: `∑_{d < n, d + 1 ∣ g} φ (d + 1) = g` for `1 ≤ g ≤ n`. -/
lemma sum_totient_range {n g : ℕ} (hg : 1 ≤ g) (hgn : g ≤ n) :
    ∑ d ∈ range n, (if d + 1 ∣ g then (φ (d + 1) : ℚ) else 0) = g := by
  have h1 : ∑ d ∈ range n, (if d + 1 ∣ g then (φ (d + 1) : ℚ) else 0)
      = ∑ m ∈ Ico 1 (n + 1), (if m ∣ g then (φ m : ℚ) else 0) := by
    rw [Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr (by simp) fun d _ ↦ ?_
    rw [Nat.add_comm 1 d]
  rw [h1, ← Finset.sum_filter]
  have h2 : (Ico 1 (n + 1)).filter (· ∣ g) = g.divisors := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Ico, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨_, _⟩, hm⟩
      exact ⟨hm, by omega⟩
    · rintro ⟨hm, -⟩
      have := Nat.le_of_dvd (by omega) hm
      exact ⟨⟨Nat.pos_of_dvd_of_pos hm (by omega), by omega⟩, hm⟩
  rw [h2]
  exact_mod_cast Nat.sum_totient g

/-- Smith's factorisation: the gcd matrix is `E · diag φ · Eᵀ`. -/
lemma gcdMatrix_eq (n : ℕ) :
    gcdMatrix n =
      divMatrix n * diagonal (fun d : Fin n ↦ (φ ((d : ℕ) + 1) : ℚ)) * (divMatrix n)ᵀ := by
  ext i j
  rw [gcdMatrix, Matrix.of_apply, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, divMatrix, Matrix.of_apply]
  have key : ∀ d : Fin n,
      ((if (d : ℕ) + 1 ∣ (i : ℕ) + 1 then (1 : ℚ) else 0) * (φ ((d : ℕ) + 1) : ℚ)) *
        (if (d : ℕ) + 1 ∣ (j : ℕ) + 1 then (1 : ℚ) else 0)
      = if (d : ℕ) + 1 ∣ Nat.gcd ((i : ℕ) + 1) ((j : ℕ) + 1) then (φ ((d : ℕ) + 1) : ℚ)
        else 0 := by
    intro d
    by_cases hi : (d : ℕ) + 1 ∣ (i : ℕ) + 1 <;> by_cases hj : (d : ℕ) + 1 ∣ (j : ℕ) + 1 <;>
      simp [hi, hj, Nat.dvd_gcd_iff]
  simp only [key]
  rw [Fin.sum_univ_eq_sum_range (fun d ↦ if d + 1 ∣ Nat.gcd ((i : ℕ) + 1) ((j : ℕ) + 1)
    then (φ (d + 1) : ℚ) else 0) n]
  refine (sum_totient_range (Nat.gcd_pos_of_pos_left _ (Nat.succ_pos _)) ?_).symm
  exact (Nat.gcd_le_left _ (Nat.succ_pos _)).trans (by omega)

lemma det_gcdMatrix (n : ℕ) : (gcdMatrix n).det = totientProd n := by
  rw [gcdMatrix_eq, det_mul, det_mul, det_transpose, det_divMatrix, det_diagonal, one_mul, mul_one,
    totientProd, Nat.cast_prod, Fin.prod_univ_eq_prod_range (fun d ↦ (φ (d + 1) : ℚ)) n]

-- ### The closed form of the determinant

lemma lcmMatrix_eq (n : ℕ) :
    lcmMatrix n = diagonal (fun i : Fin n ↦ (1 / ((i : ℕ) + 1 : ℚ))) * gcdMatrix n *
      diagonal (fun j : Fin n ↦ (1 / ((j : ℕ) + 1 : ℚ))) := by
  ext i j
  simp only [lcmMatrix, Matrix.of_apply, mul_diagonal, diagonal_mul, gcdMatrix]
  have h := Nat.gcd_mul_lcm ((i : ℕ) + 1) ((j : ℕ) + 1)
  have hl : (0 : ℚ) < (Nat.lcm ((i : ℕ) + 1) ((j : ℕ) + 1) : ℚ) := by
    exact_mod_cast Nat.lcm_pos (Nat.succ_pos _) (Nat.succ_pos _)
  have hq : (Nat.gcd ((i : ℕ) + 1) ((j : ℕ) + 1) : ℚ) * (Nat.lcm ((i : ℕ) + 1) ((j : ℕ) + 1) : ℚ)
      = ((i : ℕ) + 1 : ℚ) * ((j : ℕ) + 1 : ℚ) := by exact_mod_cast h
  field_simp
  linarith [hq]

lemma prod_fin_succ (n : ℕ) : ∏ i : Fin n, ((i : ℕ) + 1 : ℚ) = (n ! : ℚ) := by
  rw [Fin.prod_univ_eq_prod_range (fun i ↦ ((i : ℕ) + 1 : ℚ)) n]
  exact_mod_cast Finset.prod_range_add_one_eq_factorial n

lemma det_lcmMatrix (n : ℕ) : (lcmMatrix n).det = (totientProd n : ℚ) / ((n ! : ℚ) ^ 2) := by
  rw [lcmMatrix_eq, det_mul, det_mul, det_diagonal, det_gcdMatrix]
  have h : ∏ i : Fin n, (1 / ((i : ℕ) + 1 : ℚ)) = 1 / (n ! : ℚ) := by
    rw [Finset.prod_div_distrib, Finset.prod_const_one, prod_fin_succ]
  rw [h]
  have : (n ! : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  field_simp

lemma inv_det_lcmMatrix (n : ℕ) :
    ((lcmMatrix n).det)⁻¹ = ((n ! : ℚ) ^ 2) / (totientProd n : ℚ) := by
  rw [det_lcmMatrix, inv_div]

/-- The denominator of `a / b` is `1` iff `b ∣ a` (for `0 < b`). -/
lemma den_div_eq_one_iff (a b : ℕ) (hb : 0 < b) : ((a : ℚ) / (b : ℚ)).den = 1 ↔ b ∣ a := by
  have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  constructor
  · intro h
    rw [Rat.den_eq_one_iff] at h
    have h1 : ((a : ℚ) / b).num * (b : ℚ) = a := by
      rw [h]; field_simp
    have h2 : (((a : ℚ) / b).num * (b : ℤ) : ℤ) = (a : ℤ) := by exact_mod_cast h1
    exact Int.natCast_dvd_natCast.mp (Dvd.intro_left _ h2)
  · rintro ⟨c, rfl⟩
    rw [Nat.cast_mul, mul_div_cancel_left₀ _ hb', Rat.den_natCast]

-- ### The small cases: direct computation

lemma totientProd_dvd_small : ∀ n < 39, (n ≤ 34 ∨ n = 36 ∨ n = 38) → totientProd n ∣ (n !) ^ 2 := by
  decide +kernel

lemma totientProd_dvd_of_mem {n : ℕ} (h : n ∈ integerDetN) : totientProd n ∣ (n !) ^ 2 := by
  simp only [integerDetN, Set.mem_union, Set.mem_Icc, Set.mem_insert_iff,
    Set.mem_singleton_iff] at h
  exact totientProd_dvd_small n (by omega) (by omega)

-- ### The `2`-adic obstruction

/-- The odd primes up to `97`. -/
def P : Finset ℕ := {3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73,
  79, 83, 89, 97}

/-- `w p = v₂(p - 1)` for `p ∈ P`. -/
def w : ℕ → ℕ
  | 3 => 1 | 5 => 2 | 7 => 1 | 11 => 1 | 13 => 2 | 17 => 4 | 19 => 1 | 23 => 1 | 29 => 2 | 31 => 1
  | 37 => 2 | 41 => 3 | 43 => 1 | 47 => 1 | 53 => 2 | 59 => 1 | 61 => 2 | 67 => 1 | 71 => 1
  | 73 => 3 | 79 => 1 | 83 => 1 | 89 => 3 | 97 => 5
  | _ => 0

lemma P_prime : ∀ p ∈ P, p.Prime := by decide
lemma P_not_dvd_two : ∀ p ∈ P, ¬ p ∣ 2 := by decide
lemma two_pow_w_dvd : ∀ p ∈ P, 2 ^ w p ∣ p - 1 := by decide

/-- The exponent of `2` that the primes of `P` and the powers `4, …, 128` force into `φ k`. -/
def e (k : ℕ) : ℕ :=
  ∑ p ∈ P.filter (· ∣ k), w p + ((Icc 2 7).filter fun j ↦ 2 ^ j ∣ k).card

/-- `c n = ∑_{k < n} e (k + 1)`, in closed form. -/
def c (n : ℕ) : ℕ := ∑ p ∈ P, w p * (n / p) + ∑ j ∈ Icc 2 7, n / 2 ^ j

lemma sum_e_eq_c (n : ℕ) : ∑ k ∈ range n, e (k + 1) = c n := by
  unfold e c
  rw [Finset.sum_add_distrib]
  refine congrArg₂ (· + ·) ?_ ?_
  · simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, Nat.card_multiples, mul_comm]
  · simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← Finset.card_filter, Nat.card_multiples]

/-- The odd part: for `m ≠ 0`, `∏_{p ∈ P, p ∣ m} (p - 1) ∣ φ m`. -/
lemma prod_sub_one_dvd_totient {m : ℕ} (hm : m ≠ 0) :
    ∏ p ∈ P.filter (· ∣ m), (p - 1) ∣ φ m := by
  rw [Nat.totient_eq_prod_factorization hm, Nat.prod_factorization_eq_prod_primeFactors]
  refine (Finset.prod_dvd_prod_of_subset _ _ _ ?_).trans
    (Finset.prod_dvd_prod_of_dvd _ _ fun p _ ↦ Dvd.intro_left _ rfl)
  intro p hp
  simp only [Finset.mem_filter] at hp
  exact Nat.mem_primeFactors.2 ⟨P_prime p hp.1, hp.2, hm⟩

lemma two_pow_oddPart_dvd {m : ℕ} (hm : m ≠ 0) :
    2 ^ (∑ p ∈ P.filter (· ∣ m), w p) ∣ φ m := by
  rw [← Finset.prod_pow_eq_pow_sum]
  exact (Finset.prod_dvd_prod_of_dvd _ _ fun p hp ↦
    two_pow_w_dvd p (Finset.mem_filter.1 hp).1).trans (prod_sub_one_dvd_totient hm)

/-- Each `k ≥ 1` has `2 ^ e k ∣ φ k`. -/
lemma two_pow_e_dvd_totient {k : ℕ} (hk : k ≠ 0) : 2 ^ e k ∣ φ k := by
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hk
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have h2m : Nat.Coprime 2 m :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 fun h ↦
      (Nat.not_even_iff_odd.2 hm) (even_iff_two_dvd.2 h)
  have hcop : Nat.Coprime (2 ^ a) m := Nat.Coprime.pow_left _ h2m
  rw [Nat.totient_mul hcop, mul_comm (φ (2 ^ a)) (φ m), e, pow_add]
  refine mul_dvd_mul ?_ ?_
  · -- the odd primes of `P` dividing `2 ^ a * m` divide `m`
    have hfilt : P.filter (· ∣ 2 ^ a * m) = P.filter (· ∣ m) := by
      ext p
      simp only [Finset.mem_filter, and_congr_right_iff]
      intro hp
      constructor
      · intro h
        exact Nat.Coprime.dvd_of_dvd_mul_left
          (Nat.Coprime.pow_right _ ((P_prime p hp).coprime_iff_not_dvd.2 (P_not_dvd_two p hp))) h
      · exact fun h ↦ h.trans (Dvd.intro_left _ rfl)
    rw [hfilt]
    exact two_pow_oddPart_dvd hm0
  · -- `2 ^ j ∣ 2 ^ a * m` iff `j ≤ a`: at most `a - 1` such `j ∈ [2, 7]`
    have hcount : ((Icc 2 7).filter fun j ↦ 2 ^ j ∣ 2 ^ a * m).card ≤ a - 1 := by
      have hsub : (Icc 2 7).filter (fun j ↦ 2 ^ j ∣ 2 ^ a * m) ⊆ Icc 2 a := by
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_Icc] at hj ⊢
        refine ⟨hj.1.1, ?_⟩
        have h2 : 2 ^ j ∣ 2 ^ a :=
          Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_left _ h2m) hj.2
        exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h2
      exact (Finset.card_le_card hsub).trans (by simp)
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · have : ((Icc 2 7).filter fun j ↦ 2 ^ j ∣ 2 ^ 0 * m).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro j hj h
        simp only [Finset.mem_Icc] at hj
        have h2 : 2 ∣ m := (dvd_pow_self 2 (by omega : j ≠ 0)).trans (by simpa using h)
        exact (Nat.not_even_iff_odd.2 hm) (even_iff_two_dvd.2 h2)
      rw [this]; simp
    · rw [Nat.totient_prime_pow Nat.prime_two ha]
      exact (pow_dvd_pow 2 hcount).trans (dvd_mul_right _ _)

lemma two_pow_c_dvd_totientProd (n : ℕ) : 2 ^ c n ∣ totientProd n := by
  rw [← sum_e_eq_c, ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_dvd_prod_of_dvd _ _ fun k _ ↦ two_pow_e_dvd_totient (Nat.succ_ne_zero k)

/-- The closed form `c` as an explicit arithmetic expression. -/
lemma c_eq (n : ℕ) : c n =
    n/3 + 2*(n/5) + n/7 + n/11 + 2*(n/13) + 4*(n/17) + n/19 + n/23 + 2*(n/29) + n/31 + 2*(n/37)
    + 3*(n/41) + n/43 + n/47 + 2*(n/53) + n/59 + 2*(n/61) + n/67 + n/71 + 3*(n/73) + n/79 + n/83
    + 3*(n/89) + 5*(n/97) + (n/4 + n/8 + n/16 + n/32 + n/64 + n/128) := by
  norm_num [c, P, w, show Icc 2 7 = {2, 3, 4, 5, 6, 7} from rfl]
  ring

/-- `v₂(n!)` for `n < 128`. -/
lemma padicValNat_two_factorial {n : ℕ} (hn : n < 128) :
    padicValNat 2 n ! = n/2 + n/4 + n/8 + n/16 + n/32 + n/64 := by
  rw [padicValNat_factorial (b := 7) (Nat.log_lt_of_lt_pow' (by norm_num) (by norm_num; omega))]
  simp [Finset.sum_Ico_succ_top]

lemma c_gt_small : ∀ n, n < 100 → (n = 35 ∨ n = 37 ∨ 39 ≤ n) →
    2 * (n/2 + n/4 + n/8 + n/16 + n/32 + n/64) + 1 ≤
    n/3 + 2*(n/5) + n/7 + n/11 + 2*(n/13) + 4*(n/17) + n/19 + n/23 + 2*(n/29) + n/31 + 2*(n/37)
    + 3*(n/41) + n/43 + n/47 + 2*(n/53) + n/59 + 2*(n/61) + n/67 + n/71 + 3*(n/73) + n/79 + n/83
    + 3*(n/89) + 5*(n/97) + (n/4 + n/8 + n/16 + n/32 + n/64 + n/128) := by
  intro n hn h
  interval_cases n <;> simp_all

/-- `m * (n / m) ≥ n + 1 - m` as rationals. -/
lemma div_bound (n m : ℕ) (hm : 0 < m) :
    (n : ℚ) + 1 - m ≤ (m : ℚ) * ((n / m : ℕ) : ℚ) := by
  have h1 := Nat.div_add_mod n m
  have h2 := Nat.mod_lt n hm
  have h3 : (m : ℚ) * ((n / m : ℕ) : ℚ) + ((n % m : ℕ) : ℚ) = n := by exact_mod_cast h1
  have h4 : ((n % m : ℕ) : ℚ) + 1 ≤ m := by exact_mod_cast h2
  linarith

lemma c_gt_large {n : ℕ} (hn : 100 ≤ n) : 2 * n + 1 ≤ c n := by
  rw [c_eq]
  have := div_bound n 3 (by norm_num); have := div_bound n 5 (by norm_num)
  have := div_bound n 7 (by norm_num); have := div_bound n 11 (by norm_num)
  have := div_bound n 13 (by norm_num); have := div_bound n 17 (by norm_num)
  have := div_bound n 19 (by norm_num); have := div_bound n 23 (by norm_num)
  have := div_bound n 29 (by norm_num); have := div_bound n 31 (by norm_num)
  have := div_bound n 37 (by norm_num); have := div_bound n 41 (by norm_num)
  have := div_bound n 43 (by norm_num); have := div_bound n 47 (by norm_num)
  have := div_bound n 53 (by norm_num); have := div_bound n 59 (by norm_num)
  have := div_bound n 61 (by norm_num); have := div_bound n 67 (by norm_num)
  have := div_bound n 71 (by norm_num); have := div_bound n 73 (by norm_num)
  have := div_bound n 79 (by norm_num); have := div_bound n 83 (by norm_num)
  have := div_bound n 89 (by norm_num); have := div_bound n 97 (by norm_num)
  have := div_bound n 4 (by norm_num); have := div_bound n 8 (by norm_num)
  have := div_bound n 16 (by norm_num); have := div_bound n 32 (by norm_num)
  have := div_bound n 64 (by norm_num); have := div_bound n 128 (by norm_num)
  have hn' : (100 : ℚ) ≤ n := by exact_mod_cast hn
  have key : ((2 * n + 1 : ℕ) : ℚ) ≤
      ((n/3 : ℕ) : ℚ) + 2*((n/5 : ℕ) : ℚ) + ((n/7 : ℕ) : ℚ) + ((n/11 : ℕ) : ℚ)
      + 2*((n/13 : ℕ) : ℚ) + 4*((n/17 : ℕ) : ℚ) + ((n/19 : ℕ) : ℚ) + ((n/23 : ℕ) : ℚ)
      + 2*((n/29 : ℕ) : ℚ) + ((n/31 : ℕ) : ℚ) + 2*((n/37 : ℕ) : ℚ) + 3*((n/41 : ℕ) : ℚ)
      + ((n/43 : ℕ) : ℚ) + ((n/47 : ℕ) : ℚ) + 2*((n/53 : ℕ) : ℚ) + ((n/59 : ℕ) : ℚ)
      + 2*((n/61 : ℕ) : ℚ) + ((n/67 : ℕ) : ℚ) + ((n/71 : ℕ) : ℚ) + 3*((n/73 : ℕ) : ℚ)
      + ((n/79 : ℕ) : ℚ) + ((n/83 : ℕ) : ℚ) + 3*((n/89 : ℕ) : ℚ) + 5*((n/97 : ℕ) : ℚ)
      + (((n/4 : ℕ) : ℚ) + ((n/8 : ℕ) : ℚ) + ((n/16 : ℕ) : ℚ) + ((n/32 : ℕ) : ℚ)
        + ((n/64 : ℕ) : ℚ) + ((n/128 : ℕ) : ℚ)) := by
    push_cast
    linarith
  exact_mod_cast key

lemma not_totientProd_dvd {n : ℕ} (hn : 1 ≤ n) (h : n ∉ integerDetN) :
    ¬ totientProd n ∣ (n !) ^ 2 := by
  intro hdvd
  have h2 : 2 ^ c n ∣ (n !) ^ 2 := (two_pow_c_dvd_totientProd n).trans hdvd
  rw [padicValNat_dvd_iff_le (pow_ne_zero _ (Nat.factorial_ne_zero n)), padicValNat.pow] at h2
  simp only [integerDetN, Set.mem_union, Set.mem_Icc, Set.mem_insert_iff, Set.mem_singleton_iff,
    not_or, not_and, not_le] at h
  by_cases hlt : n < 100
  · -- the two `omega` calls come before `h2` is unfolded into its 30 division terms
    have h128 : n < 128 := by omega
    have h3 : n = 35 ∨ n = 37 ∨ 39 ≤ n := by omega
    rw [padicValNat_two_factorial h128, c_eq] at h2
    exact absurd h2 (not_le.2 (c_gt_small n hlt h3))
  · have := padicValNat_factorial_le (p := 2) n
    have := c_gt_large (not_lt.1 hlt)
    omega

-- ### The theorem

theorem conjecture1 :
    ∀ n : ℕ, 1 ≤ n → (((lcmMatrix n).det)⁻¹.den = 1 ↔ n ∈ integerDetN) := by
  intro n hn
  rw [inv_det_lcmMatrix]
  have : ((n ! : ℚ) ^ 2) = (((n !) ^ 2 : ℕ) : ℚ) := by push_cast; ring
  rw [this, den_div_eq_one_iff _ _ (totientProd_pos n)]
  exact ⟨fun h ↦ by_contra fun hmem ↦ not_totientProd_dvd hn hmem h, totientProd_dvd_of_mem⟩

example : type_of% OeisA60841.conjecture1 := conjecture1

end OeisA060841Proof
