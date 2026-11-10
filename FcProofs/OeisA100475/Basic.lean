import FormalConjectures.OEIS.«100475»

/-!
# OEIS A100475, part 1: digit counts, cycles and Legendre's sieve

See `FcProofs.OeisA100475` for the overview. This module proves that the digit count never
decreases along an orbit of the reverse-prime map, that it is constant on a cycle, and the sieve
bounds `π'(10^5) < 10^4` and `π'(10^6) < 10^5` via Legendre's recursion evaluated by the kernel.
-/

open Nat Function

namespace OeisA100475Proof

open OeisA100475

/-- The step map of the recurrence; `f 0 = 0` only to make it total. -/
noncomputable def f (y : ℕ) : ℕ :=
  if y = 0 then 0 else reverseDigits (Nat.nth Nat.Prime (y - 1))

lemma aStartAt_eq_iterate (x n : ℕ) : aStartAt x n = f^[n] x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterate_succ_apply', ← ih]; rfl

/-- Number of decimal digits. -/
def D (n : ℕ) : ℕ := (Nat.digits 10 n).length

lemma prime_mod_ten_ne_zero {p : ℕ} (hp : p.Prime) : p % 10 ≠ 0 := by
  intro h
  have h10 : 10 ∣ p := Nat.dvd_of_mod_eq_zero h
  have h2 : 2 ∣ p := dvd_trans ⟨5, rfl⟩ h10
  have h5 : 5 ∣ p := dvd_trans ⟨2, rfl⟩ h10
  rcases hp.eq_one_or_self_of_dvd 2 h2 with h | h <;>
    rcases hp.eq_one_or_self_of_dvd 5 h5 with h' | h' <;> omega

lemma digits_reverseDigits {p : ℕ} (hp0 : p ≠ 0) (hp : p % 10 ≠ 0) :
    Nat.digits 10 (reverseDigits p) = (Nat.digits 10 p).reverse := by
  unfold reverseDigits
  refine Nat.digits_ofDigits 10 (by norm_num) _ ?_ ?_
  · intro l hl
    exact Nat.digits_lt_base (by norm_num) (List.mem_reverse.mp hl)
  · intro h
    have hd : Nat.digits 10 p = p % 10 :: Nat.digits 10 (p / 10) :=
      Nat.digits_def' (by norm_num) (Nat.pos_of_ne_zero hp0)
    simpa [List.getLast_reverse, hd] using hp

lemma length_digits_mono {m n : ℕ} (h : m ≤ n) : D m ≤ D n := by
  unfold D
  rw [Nat.digits_length_le_iff (by norm_num)]
  exact lt_of_le_of_lt h (Nat.lt_base_pow_length_digits (by norm_num))

lemma D_f {y : ℕ} (hy : y ≠ 0) : D (f y) = D (Nat.nth Nat.Prime (y - 1)) := by
  have hp := Nat.prime_nth_prime (y - 1)
  simp only [f, hy, if_false, D]
  rw [digits_reverseDigits hp.ne_zero (prime_mod_ten_ne_zero hp), List.length_reverse]

lemma f_ne_zero {y : ℕ} (hy : y ≠ 0) : f y ≠ 0 := by
  have hp := Nat.prime_nth_prime (y - 1)
  rw [← Nat.digits_ne_nil_iff_ne_zero (b := 10)]
  simp only [f, hy, if_false]
  rw [digits_reverseDigits hp.ne_zero (prime_mod_ten_ne_zero hp)]
  intro h
  exact (Nat.digits_ne_nil_iff_ne_zero.mpr hp.ne_zero) (List.reverse_eq_nil_iff.mp h)

lemma lt_nth_prime (y : ℕ) : y < Nat.nth Nat.Prime (y - 1) := by
  have := Nat.add_two_le_nth_prime (y - 1)
  omega

lemma D_le_D_f {y : ℕ} (hy : y ≠ 0) : D y ≤ D (f y) := by
  rw [D_f hy]
  exact length_digits_mono (lt_nth_prime y).le

lemma iterate_ne_zero {y : ℕ} (hy : y ≠ 0) (k : ℕ) : f^[k] y ≠ 0 := by
  induction k with
  | zero => simpa
  | succ k ih => rw [iterate_succ_apply']; exact f_ne_zero ih

lemma D_le_D_iterate {y : ℕ} (hy : y ≠ 0) (k : ℕ) : D y ≤ D (f^[k] y) := by
  induction k with
  | zero => simp
  | succ k ih => rw [iterate_succ_apply']; exact ih.trans (D_le_D_f (iterate_ne_zero hy k))

lemma D_iterate_le_D_iterate {y : ℕ} (hy : y ≠ 0) {j k : ℕ} (h : j ≤ k) :
    D (f^[j] y) ≤ D (f^[k] y) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [add_comm, iterate_add_apply]
  exact D_le_D_iterate (iterate_ne_zero hy j) m

/-- On a cycle (`f^[P] w = w`, `P > 0`) the digit count is constant. -/
lemma D_iterate_eq_of_cycle {w P : ℕ} (hw : w ≠ 0) (hP : 0 < P) (hcyc : f^[P] w = w) (k : ℕ) :
    D (f^[k] w) = D w := by
  -- reduce `k` modulo `P`
  have hmul : ∀ q, f^[P * q] w = w := by
    intro q
    induction q with
    | zero => simp
    | succ q ih => rw [Nat.mul_succ, iterate_add_apply, hcyc, ih]
  have hk : f^[k] w = f^[k % P] w := by
    conv_lhs => rw [← Nat.mod_add_div k P, iterate_add_apply, hmul]
  rw [hk]
  apply le_antisymm
  · have h1 : D (f^[k % P] w) ≤ D (f^[P] w) :=
      D_iterate_le_D_iterate hw (Nat.mod_lt k hP).le
    rwa [hcyc] at h1
  · exact D_le_D_iterate hw _

/- ## Sieve bounds on the prime-counting function (Legendre's recursion) -/
/-- The primes up to `300` in descending order, so that the head is the largest remaining prime. -/
def primesDesc : List ℕ :=
  [293, 283, 281, 277, 271, 269, 263, 257, 251, 241, 239, 233, 229, 227, 223, 211, 199, 197, 193,
   191, 181, 179, 173, 167, 163, 157, 151, 149, 139, 137, 131, 127, 113, 109, 107, 103, 101, 97, 89,
   83, 79, 73, 71, 67, 61, 59, 53, 47, 43, 41, 37, 31, 29, 23, 19, 17, 13, 11, 7, 5, 3, 2]

/-- Legendre's `φ` along a descending prime list, with the pruning `φ(x) = 1` for `1 ≤ x < p`.
Written with `List.rec` directly so that the kernel evaluates it efficiently. -/
def phiList (ps : List ℕ) (x : ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun x => x)
    (fun p _ ih x => if x < p then (if x = 0 then 0 else 1) else ih x - ih (x / p)) ps x

theorem phiList_nil (x : ℕ) : phiList [] x = x := rfl

theorem phiList_cons (p : ℕ) (ps : List ℕ) (x : ℕ) :
    phiList (p :: ps) x = (if x < p then (if x = 0 then 0 else 1)
      else phiList ps x - phiList ps (x / p)) := rfl

/-- The numbers in `[1, x]` divisible by no element of `ps`. -/
def sieveSet (ps : List ℕ) (x : ℕ) : Finset ℕ :=
  (Finset.Icc 1 x).filter (fun n => ∀ p ∈ ps, ¬ p ∣ n)

lemma mem_sieveSet {ps : List ℕ} {x n : ℕ} :
    n ∈ sieveSet ps x ↔ (1 ≤ n ∧ n ≤ x) ∧ ∀ p ∈ ps, ¬ p ∣ n := by
  simp [sieveSet]

lemma sieveSet_nil (x : ℕ) : sieveSet [] x = Finset.Icc 1 x := by
  ext n; simp [sieveSet]

/-- Legendre's recursion step. -/
lemma card_sieveSet_cons {p : ℕ} {ps : List ℕ} (hp : p.Prime) (hps : ∀ q ∈ ps, q.Prime ∧ q ≠ p)
    (x : ℕ) :
    (sieveSet (p :: ps) x).card = (sieveSet ps x).card - (sieveSet ps (x / p)).card := by
  have hsplit : sieveSet (p :: ps) x = (sieveSet ps x).filter (fun n => ¬ p ∣ n) := by
    ext n; simp [sieveSet, List.mem_cons]; tauto
  have himage : (sieveSet ps x).filter (fun n => p ∣ n) = (sieveSet ps (x / p)).image (p * ·) := by
    ext n
    simp only [Finset.mem_filter, mem_sieveSet, Finset.mem_image]
    constructor
    · rintro ⟨⟨⟨h1, hx⟩, hq⟩, ⟨m, rfl⟩⟩
      refine ⟨m, ⟨⟨?_, ?_⟩, ?_⟩, rfl⟩
      · rcases Nat.eq_zero_or_pos m with rfl | hm
        · simp at h1
        · exact hm
      · exact (Nat.le_div_iff_mul_le hp.pos).2 (by rw [mul_comm]; exact hx)
      · intro q hq' hdvd
        exact hq q hq' (dvd_mul_of_dvd_right hdvd p)
    · rintro ⟨m, ⟨⟨h1, hm⟩, hq⟩, rfl⟩
      refine ⟨⟨⟨?_, ?_⟩, ?_⟩, dvd_mul_right p m⟩
      · exact Nat.one_le_iff_ne_zero.2 (mul_ne_zero hp.ne_zero (by omega))
      · rw [mul_comm]; exact (Nat.le_div_iff_mul_le hp.pos).1 hm
      · intro q hq' hdvd
        obtain ⟨hqp, hqne⟩ := hps q hq'
        rcases (Nat.Prime.dvd_mul hqp).1 hdvd with h | h
        · exact hqne ((Nat.prime_dvd_prime_iff_eq hqp hp).1 h)
        · exact hq q hq' h
  have hcard := Finset.card_filter_add_card_filter_not (s := sieveSet ps x) (fun n => p ∣ n)
  rw [himage, Finset.card_image_of_injective _ (mul_right_injective₀ hp.ne_zero)] at hcard
  rw [hsplit]
  omega

/-- Pruning: below `p`, only `1` survives the sieve by all primes less than `p`. -/
lemma card_sieveSet_of_lt {p : ℕ} {ps : List ℕ} (hps : ∀ q ∈ ps, q.Prime)
    (hcomplete : ∀ q, q.Prime → q < p → q ∈ ps) {x : ℕ} (hx : x < p) :
    (sieveSet (p :: ps) x).card = if x = 0 then 0 else 1 := by
  split_ifs with h0
  · subst h0; simp [sieveSet]
  · have : sieveSet (p :: ps) x = {1} := by
      ext n
      simp only [mem_sieveSet, Finset.mem_singleton, List.mem_cons, forall_eq_or_imp]
      constructor
      · rintro ⟨⟨h1, hnx⟩, -, hq⟩
        by_contra hne
        have hn1 : n ≠ 1 := hne
        have hmf := Nat.minFac_prime hn1
        have hlt : Nat.minFac n < p := lt_of_le_of_lt (Nat.minFac_le (by omega)) (by omega)
        exact hq _ (hcomplete _ hmf hlt) (Nat.minFac_dvd n)
      · rintro rfl
        refine ⟨⟨le_rfl, by omega⟩, ?_, ?_⟩
        · intro h
          have := Nat.le_of_dvd one_pos h
          omega
        · intro q hq; exact Nat.Prime.not_dvd_one (hps q hq)
    rw [this, Finset.card_singleton]

/-- Trial-division primality test; the kernel can evaluate it for small numbers. -/
def isPrimeTD (q : ℕ) : Bool := 2 ≤ q && (List.range q).all (fun d => d < 2 || q % d != 0)

lemma isPrimeTD_iff (q : ℕ) : isPrimeTD q = true ↔ q.Prime := by
  rw [Nat.prime_def_lt]
  simp only [isPrimeTD, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, bne_iff_ne, ne_eq]
  constructor
  · rintro ⟨h2, h⟩
    refine ⟨h2, fun m hmq hdvd => ?_⟩
    rcases h m hmq with h' | h'
    · have hm : m = 0 ∨ m = 1 := by omega
      rcases hm with rfl | rfl
      · rw [zero_dvd_iff] at hdvd; omega
      · rfl
    · exact absurd (Nat.mod_eq_zero_of_dvd hdvd) h'
  · rintro ⟨h2, h⟩
    refine ⟨h2, fun d hd => ?_⟩
    by_cases hd2 : d < 2
    · exact Or.inl hd2
    · exact Or.inr fun h0 => by have := h d hd (Nat.dvd_of_mod_eq_zero h0); omega

/-- The hypotheses of Legendre's recursion along a list: descending primes, each suffix complete. -/
def GoodList : List ℕ → Prop
  | [] => True
  | p :: ps => p.Prime ∧ (∀ q ∈ ps, q.Prime ∧ q ≠ p) ∧ (∀ q, q.Prime → q < p → q ∈ ps) ∧ GoodList ps

lemma goodList_of_sorted : ∀ (l : List ℕ), l.Pairwise (· > ·) → (∀ q ∈ l, q.Prime) →
    (∀ p ∈ l, ∀ q, q.Prime → q < p → q ∈ l) → GoodList l
  | [], _, _, _ => trivial
  | p :: ps, hsort, hprime, hcomp => by
    rw [List.pairwise_cons] at hsort
    refine ⟨hprime p (List.mem_cons_self), fun q hq => ⟨hprime q (List.mem_cons_of_mem p hq),
      (hsort.1 q hq).ne⟩, fun q hq hqp => ?_, ?_⟩
    · rcases List.mem_cons.1 (hcomp p List.mem_cons_self q hq hqp) with rfl | h
      · exact absurd hqp (lt_irrefl _)
      · exact h
    · refine goodList_of_sorted ps hsort.2 (fun q hq => hprime q (List.mem_cons_of_mem p hq))
        fun p' hp' q hq hqp' => ?_
      have hp'p : p' < p := hsort.1 p' hp'
      rcases List.mem_cons.1 (hcomp p' (List.mem_cons_of_mem p hp') q hq hqp') with rfl | h
      · exact absurd (hqp'.trans hp'p) (lt_irrefl _)
      · exact h

lemma phiList_eq_card : ∀ {ps : List ℕ}, GoodList ps → ∀ x, phiList ps x = (sieveSet ps x).card
  | [], _, x => by simp [phiList_nil, sieveSet_nil]
  | p :: ps, ⟨hp, hps, hcomp, hgood⟩, x => by
    rw [phiList_cons]
    by_cases hx : x < p
    · rw [if_pos hx, card_sieveSet_of_lt (fun q hq => (hps q hq).1) hcomp hx]
    · rw [if_neg hx, card_sieveSet_cons hp hps x, phiList_eq_card hgood x,
        phiList_eq_card hgood (x / p)]

lemma goodList_primesDesc : GoodList primesDesc := by
  have hsort : primesDesc.Pairwise (· > ·) := by decide +kernel
  have hprime : ∀ q ∈ primesDesc, isPrimeTD q = true := by decide +kernel
  have hcomp : ∀ q < 294, isPrimeTD q = true → q ∈ primesDesc := by decide +kernel
  have hle : ∀ p ∈ primesDesc, p ≤ 293 := by decide +kernel
  refine goodList_of_sorted _ hsort (fun q hq => (isPrimeTD_iff q).1 (hprime q hq)) ?_
  intro p hp q hq hqp
  exact hcomp q (by have := hle p hp; omega) ((isPrimeTD_iff q).2 hq)

/-- Every prime below `N` is either one of the listed small primes or survives the sieve. -/
lemma primeCounting'_le_sieve (N : ℕ) (hN : 2 ≤ N) :
    Nat.primeCounting' N ≤ primesDesc.length + ((sieveSet primesDesc (N - 1)).card - 1) := by
  have hcomp : ∀ q, q.Prime → q ≤ 293 → q ∈ primesDesc := by
    have h : ∀ q < 294, isPrimeTD q = true → q ∈ primesDesc := by decide +kernel
    intro q hq hq'
    exact h q (by omega) ((isPrimeTD_iff q).2 hq)
  have hprime : ∀ q ∈ primesDesc, q.Prime := by
    have h : ∀ q ∈ primesDesc, isPrimeTD q = true := by decide +kernel
    intro q hq; exact (isPrimeTD_iff q).1 (h q hq)
  have hle : ∀ p ∈ primesDesc, p ≤ 293 := by decide +kernel
  unfold Nat.primeCounting'
  rw [Nat.count_eq_card_filter_range]
  set S := (Finset.range N).filter Nat.Prime with hS
  have hsplit : S = S.filter (fun q => q ≤ 293) ∪ S.filter (fun q => ¬ q ≤ 293) := by
    ext q
    simp only [Finset.mem_union, Finset.mem_filter]
    by_cases hq : q ≤ 293 <;> simp [hq]
  rw [hsplit]
  refine (Finset.card_union_le _ _).trans (Nat.add_le_add ?_ ?_)
  · refine (Finset.card_le_card (fun q hq => ?_)).trans (List.toFinset_card_le primesDesc)
    simp only [hS, Finset.mem_filter, Finset.mem_range] at hq
    exact List.mem_toFinset.2 (hcomp q hq.1.2 hq.2)
  · have h1 : (1 : ℕ) ∈ sieveSet primesDesc (N - 1) := by
      rw [mem_sieveSet]
      exact ⟨⟨le_rfl, by omega⟩, fun p hp => Nat.Prime.not_dvd_one (hprime p hp)⟩
    rw [← Finset.card_erase_of_mem h1]
    refine Finset.card_le_card fun q hq => ?_
    simp only [hS, Finset.mem_filter, Finset.mem_range, not_le] at hq
    obtain ⟨⟨hqN, hq⟩, h293⟩ := hq
    rw [Finset.mem_erase, mem_sieveSet]
    refine ⟨hq.one_lt.ne', ⟨hq.one_le, by omega⟩, fun p hp hdvd => ?_⟩
    have hp' := hprime p hp
    have := (Nat.prime_dvd_prime_iff_eq hp' hq).1 hdvd
    have := hle p hp
    omega

theorem primeCounting'_1e5 : Nat.primeCounting' 100000 < 10000 := by
  have h := primeCounting'_le_sieve 100000 (by norm_num)
  have hphi : phiList primesDesc 99999 = 9540 := by decide +kernel
  rw [← phiList_eq_card goodList_primesDesc] at h
  simp only [show (100000 : ℕ) - 1 = 99999 from rfl, hphi,
    show primesDesc.length = 62 from rfl] at h
  omega

theorem primeCounting'_1e6 : Nat.primeCounting' 1000000 < 100000 := by
  have h := primeCounting'_le_sieve 1000000 (by norm_num)
  have hphi : phiList primesDesc 999999 = 94794 := by decide +kernel
  rw [← phiList_eq_card goodList_primesDesc] at h
  simp only [show (1000000 : ℕ) - 1 = 999999 from rfl, hphi,
    show primesDesc.length = 62 from rfl] at h
  omega

end OeisA100475Proof
