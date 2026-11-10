import FcProofs.OeisA100475.Tables

/-!
# OEIS A100475: the reverse-prime map never loops

`OeisA100475.conjecture` asks for a start `x > 1` whose orbit under `y ↦ reverse (p_y)` (with `p_1 = 2`)
is ultimately periodic. There is none.

Write `f y = reverseDigits (nth Prime (y - 1))` for `y ≥ 1`. Since `p_y > y` and a prime never ends in the
digit `0`, the number of decimal digits never decreases along an orbit. On a cycle it is therefore constant,
say `D`, so every cycle element `v` satisfies `p_v < 10 ^ D ≤ 10 v`. For `D ≤ 4` this forces `v ≤ 1229`, and a
finite computation shows that every orbit starting at `v ≤ 1229` leaves `{1, …, 1229}`. For `D ≥ 5` it
contradicts `π(10 ^ D) < 10 ^ (D - 1)`, which is checked by Legendre's sieve count (evaluated by the kernel)
for `D = 5, …, 8` and follows from Chebyshev's bound `θ x ≤ x log 4` for `D ≥ 9`.
-/

open Nat Function

namespace OeisA100475Proof

open OeisA100475

open Chebyshev in
/-- `π(x) log y ≤ x log 4 + y log y` for `1 ≤ y ≤ x` (after Mathlib's proof of
`Chebyshev.pi_le_log4_mul_div`, with a general split point `y`). -/
lemma pi_mul_log_le {x y : ℝ} (hy : 1 ≤ y) (hxy : y ≤ x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) * Real.log y ≤ Real.log 4 * x + y * Real.log y := calc
  (Nat.primeCounting ⌊x⌋₊ : ℝ) * Real.log y = ∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log y := by
    rw [Finset.sum_const, nsmul_eq_mul, Nat.primesLE_card_eq_primeCounting]
  _ ≤ ∑ p ∈ Nat.primesLE ⌊x⌋₊, (Real.log p + (if (p : ℝ) ≤ y then Real.log y else 0)) := by
    refine Finset.sum_le_sum fun p _ => ?_
    split_ifs with h
    · linarith [Real.log_natCast_nonneg p]
    · have : Real.log y < Real.log p := Real.log_lt_log (by linarith) (not_le.mp h)
      linarith
  _ ≤ Real.log 4 * x + y * Real.log y := by
    rw [Finset.sum_add_distrib]
    gcongr ?_ + ?_
    · calc ∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p = θ x := by
            rw [theta_eq_theta_coe_floor, theta_eq_sum_primesLE_log]
        _ ≤ Real.log 4 * x := theta_le_log4_mul_x (by linarith)
    · rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul]
      gcongr
      · exact Real.log_nonneg hy
      refine le_trans ?_ (Nat.floor_le (by linarith : (0 : ℝ) ≤ y))
      norm_cast
      rw [show ⌊y⌋₊ = (Finset.Icc 1 ⌊y⌋₊).card by simp]
      refine Finset.card_le_card fun p hp => ?_
      simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_primesLE] at hp ⊢
      exact ⟨hp.1.2.one_le, Nat.le_floor hp.2⟩

lemma log_four_lt : Real.log 4 < 1.3863 := by
  have h := Real.log_two_lt_d9
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  rw [h4]; linarith

lemma log_ten_gt : (2.2794 : ℝ) < Real.log 10 := by
  have h2 := Real.log_two_gt_d9
  have h10 : Real.log 10 = 3 * Real.log 2 + Real.log (5 / 4) := by
    rw [show (10 : ℝ) = 2 ^ 3 * (5 / 4) by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]; push_cast; ring
  have h54 : (1 : ℝ) - (5 / 4)⁻¹ ≤ Real.log (5 / 4) := Real.one_sub_inv_le_log_of_pos (by norm_num)
  rw [h10]; norm_num at h54 ⊢; linarith

lemma primeCounting_pow_lt_of_nine_le {D : ℕ} (hD : 9 ≤ D) :
    Nat.primeCounting (10 ^ D) < 10 ^ (D - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, D = k + 2 := ⟨D - 2, by omega⟩
  have hk : 7 ≤ k := by omega
  have hx : ⌊((10 : ℝ) ^ (k + 2))⌋₊ = 10 ^ (k + 2) := by
    rw [show ((10 : ℝ) ^ (k + 2)) = ((10 ^ (k + 2) : ℕ) : ℝ) by push_cast; ring, Nat.floor_natCast]
  have hy1 : (1 : ℝ) ≤ (10 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have hxy : (10 : ℝ) ^ k ≤ (10 : ℝ) ^ (k + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
  have key := pi_mul_log_le hy1 hxy
  rw [hx, Real.log_pow] at key
  have hl4 := log_four_lt
  have hl10 := log_ten_gt
  by_contra hcon
  push Not at hcon
  have hcon' : ((10 : ℝ) ^ (k + 2 - 1)) ≤ (Nat.primeCounting (10 ^ (k + 2)) : ℝ) := by
    exact_mod_cast hcon
  have e1 : (10 : ℝ) ^ (k + 2) = 100 * (10 : ℝ) ^ k := by rw [pow_add]; ring
  have e2 : (10 : ℝ) ^ (k + 2 - 1) = 10 * (10 : ℝ) ^ k := by
    rw [show k + 2 - 1 = k + 1 by omega, pow_succ]; ring
  set Y := (10 : ℝ) ^ k with hY
  set L := (k : ℝ) * Real.log 10 with hL
  have hYpos : 0 < Y := by positivity
  have hk' : (7 : ℝ) ≤ k := by exact_mod_cast hk
  have hLge : 7 * 2.2794 ≤ L := by
    have : (0 : ℝ) < Real.log 10 := by linarith
    nlinarith
  have hπ : 10 * Y * L ≤ Real.log 4 * (100 * Y) + Y * L := by
    have hL0 : 0 ≤ L := by linarith
    calc 10 * Y * L = (10 * Y) * L := by ring
      _ ≤ (Nat.primeCounting (10 ^ (k + 2)) : ℝ) * L := by
          rw [← e2]; exact mul_le_mul_of_nonneg_right hcon' hL0
      _ ≤ _ := by rw [← e1]; exact key
  have h9 : 9 * L ≤ 100 * Real.log 4 := by
    refine le_of_mul_le_mul_left ?_ hYpos
    nlinarith [hπ]
  linarith

lemma primeCounting'_nth_add_one {v : ℕ} (hv : 1 ≤ v) :
    Nat.primeCounting' (Nat.nth Nat.Prime (v - 1) + 1) = v := by
  unfold Nat.primeCounting'
  rw [Nat.count_succ, if_pos (Nat.prime_nth_prime _)]
  have := Nat.primeCounting'_nth_eq (v - 1)
  unfold Nat.primeCounting' at this
  omega

/-- Fewer than `10 ^ (D - 1)` primes below `10 ^ D`, for every `D ≥ 5`. -/
lemma primeCounting'_pow_lt {D : ℕ} (hD : 5 ≤ D) :
    Nat.primeCounting' (10 ^ D) < 10 ^ (D - 1) := by
  rcases Nat.lt_or_ge D 9 with h | h
  · interval_cases D
    · simpa using primeCounting'_1e5
    · simpa using primeCounting'_1e6
    · simpa using primeCounting'_1e7
    · simpa using primeCounting'_1e8
  · calc Nat.primeCounting' (10 ^ D) = Nat.primeCounting (10 ^ D - 1) :=
          (Nat.primeCounting_sub_one _).symm
      _ ≤ Nat.primeCounting (10 ^ D) := Nat.monotone_primeCounting (Nat.sub_le _ _)
      _ < 10 ^ (D - 1) := primeCounting_pow_lt_of_nine_le h

/- ## Main theorem -/

/-- On a cycle, every element `v` satisfies `p_v < 10 ^ D v`. -/
lemma nth_prime_lt_of_cycle {w P : ℕ} (hw : w ≠ 0) (hP : 0 < P) (hcyc : f^[P] w = w) (k : ℕ) :
    Nat.nth Nat.Prime (f^[k] w - 1) < 10 ^ D (f^[k] w) := by
  have hk : D (f^[k + 1] w) = D (f^[k] w) := by
    rw [D_iterate_eq_of_cycle hw hP hcyc (k + 1), D_iterate_eq_of_cycle hw hP hcyc k]
  rw [iterate_succ_apply', D_f (iterate_ne_zero hw k)] at hk
  rw [← hk]
  unfold D
  exact Nat.lt_base_pow_length_digits (by norm_num)

/-- Every element of a cycle is at most `1229`. -/
lemma cycle_le_1229 {w P : ℕ} (hw : w ≠ 0) (hP : 0 < P) (hcyc : f^[P] w = w) (k : ℕ) :
    f^[k] w ≤ 1229 := by
  have hlt := nth_prime_lt_of_cycle hw hP hcyc k
  set v := f^[k] w with hv
  have hv1 : 1 ≤ v := Nat.one_le_iff_ne_zero.2 (iterate_ne_zero hw k)
  rcases Nat.lt_or_ge (D v) 5 with hd | hd
  · apply le_1229_of_nth_prime_lt hv1
    calc Nat.nth Nat.Prime (v - 1) < 10 ^ D v := hlt
      _ ≤ 10 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 10000 := by norm_num
  · exfalso
    have hge : 10 ^ (D v - 1) ≤ v := by
      have h := Nat.base_pow_length_digits_le 10 v (by norm_num) (by omega)
      unfold D at hd ⊢
      rw [show (Nat.digits 10 v).length = (Nat.digits 10 v).length - 1 + 1 by omega,
        pow_succ] at h
      omega
    have h1 := primeCounting'_nth_add_one hv1
    have h2 : Nat.primeCounting' (Nat.nth Nat.Prime (v - 1) + 1) ≤
        Nat.primeCounting' (10 ^ D v) := Nat.monotone_primeCounting' hlt
    have h3 := primeCounting'_pow_lt hd
    omega

theorem conjecture_false :
    ¬ ∃ x : ℕ, 0 < x ∧ x ≠ 1 ∧ IsUltimatelyPeriodic (aStartAt x) := by
  rintro ⟨x, hx, -, N, P, hP, hper⟩
  have hw : f^[P] (f^[N] x) = f^[N] x := by
    have h := hper N le_rfl
    rw [aStartAt_eq_iterate, aStartAt_eq_iterate, add_comm, iterate_add_apply] at h
    exact h
  have hw0 : f^[N] x ≠ 0 := iterate_ne_zero (by omega) N
  exact no_small_cycle (Nat.one_le_iff_ne_zero.2 hw0) hP hw (cycle_le_1229 hw0 hP hw)

end OeisA100475Proof

/-- The statement `OeisA100475.conjecture` of formal-conjectures is false: no positive start other
than `1` (and in fact not even `1`) ever enters a loop. -/
theorem OeisA100475.conjecture_false :
    ¬ ∃ x : ℕ, 0 < x ∧ x ≠ 1 ∧ OeisA100475.IsUltimatelyPeriodic (OeisA100475.aStartAt x) :=
  OeisA100475Proof.conjecture_false

example : ¬ (type_of% OeisA100475.conjecture) := OeisA100475.conjecture_false
