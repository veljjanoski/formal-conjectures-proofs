/-
Copyright (c) 2026 Daniel Veljjanoski. Released under the MIT license.
-/
import FormalConjectures.Wikipedia.CongruentNumber

/-!
# 1 is not a congruent number

A proof of `CongruentNumber.not_congruentNumber_1` from
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures): there is no right
triangle with rational sides and area $1$ (Fermat).

**Reduction.** Let $a^2 + b^2 = c^2$ and $ab = 2$ with rational $a, b, c$. Clearing denominators
gives integers $A, B, C$ and $D > 0$ with $A^2 + B^2 = C^2$ and $AB = 2D^2$, and then
$$C^4 - (2D)^4 = (A^2 + B^2)^2 - 4A^2B^2 = (A^2 - B^2)^2.$$
Here $C \neq 0$, since otherwise $A = B = 0$, contradicting $AB = 2D^2 > 0$. Also
$A^2 \neq B^2$: $a = b$ would give $a^2 = 2$, and $2$ is not a rational square, while $a = -b$
would give $-a^2 = 2$. So it is enough to prove Fermat's right triangle theorem in the form:
$x^4 - y^4 = z^2$ has no solution in nonzero integers.

**Descent.** Use strong induction on $|x|$. If $x$ and $y$ have a common factor $g > 1$, then
$g^2 \mid z$ and dividing gives a smaller solution. Otherwise $(z, y^2, x^2)$ is a primitive
Pythagorean triple, so $x^2 = m^2 + n^2$ with $m, n$ coprime of opposite parity, and one of two
cases holds.

* $z = 2mn$ and $y^2 = m^2 - n^2$. Then $m^4 - n^4 = (xy)^2$, with $m, n \neq 0$ because
  $z \neq 0$, is a solution with $|m| < |x|$.
* $z = m^2 - n^2$ and $y^2 = 2mn$. Say $m$ is even. Then $(m/2) \cdot n$ is a square with coprime
  factors, so $m/2 = \pm u^2$ and $n = \pm v^2$, and $(2u^2, v^2, x)$ is again a primitive
  Pythagorean triple, with $v$ odd. Since $v^2$ is odd, $v^2 = 2MN$ is impossible, so $u^2 = MN$
  and $v^2 = M^2 - N^2$ with $M, N$ coprime. Then $M = \pm R^2$ and $N = \pm S^2$, and
  $R^4 - S^4 = v^2$ is a solution with $|R| < |x|$.

Mathlib has the analogous statement for $a^4 + b^4 = c^2$ (`not_fermat_42`), proved by a similar
descent.
-/

namespace CongruentNumberOneProof

/-- Descent step. From `y ≠ 0`, `x ^ 2 = m ^ 2 + n ^ 2` and `y ^ 2 = 2 * m * n` with `m` even,
`n` odd and `m`, `n` coprime, we get a solution of `R ^ 4 - S ^ 4 = v ^ 2` in nonzero integers
with `R ^ 2 < x ^ 2`. -/
theorem descent_step {x y m n : ℤ} (hy : y ≠ 0)
    (h1 : x ^ 2 = m ^ 2 + n ^ 2) (h2 : y ^ 2 = 2 * m * n) (hg : Int.gcd m n = 1)
    (hm : m % 2 = 0) (hn : n % 2 = 1) :
    ∃ R S v : ℤ, R ≠ 0 ∧ S ≠ 0 ∧ v ≠ 0 ∧ R ^ 4 - S ^ 4 = v ^ 2 ∧ R ^ 2 < x ^ 2 := by
  obtain ⟨m', rfl⟩ : ∃ m', m = 2 * m' := ⟨m / 2, by omega⟩
  have hye : Even y := (Int.even_pow' two_ne_zero).mp ⟨2 * m' * n, by rw [h2]; ring⟩
  obtain ⟨y', rfl⟩ := hye
  have hy' : y' ≠ 0 := by
    rintro rfl
    exact hy (by simp)
  -- `m' * n` is a square and `m'`, `n` are coprime, so both are squares up to sign
  have h3 : m' * n = y' ^ 2 := by
    have : 4 * (m' * n) = 4 * y' ^ 2 := by linear_combination (-1 : ℤ) * h2
    linarith
  have hc : IsCoprime m' n := (Int.isCoprime_iff_gcd_eq_one.mpr hg).of_mul_left_right
  obtain ⟨u, hu⟩ := Int.sq_of_gcd_eq_one (Int.isCoprime_iff_gcd_eq_one.mp hc) h3
  obtain ⟨v, hv⟩ := Int.sq_of_gcd_eq_one (Int.isCoprime_iff_gcd_eq_one.mp hc.symm)
    (by rw [mul_comm]; exact h3)
  have hm2 : m' ^ 2 = u ^ 4 := by rcases hu with h | h <;> rw [h] <;> ring
  have hn2 : n ^ 2 = v ^ 4 := by rcases hv with h | h <;> rw [h] <;> ring
  have hy2 : y' ^ 2 ≠ 0 := pow_ne_zero 2 hy'
  have hm'0 : m' ≠ 0 := by
    rintro rfl
    exact hy2 (by rw [← h3]; ring)
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hy2 (by rw [← h3]; ring)
  have hu0 : u ≠ 0 := by
    rintro rfl
    rcases hu with h | h <;> exact hm'0 (by rw [h]; ring)
  have hv0 : v ≠ 0 := by
    rintro rfl
    rcases hv with h | h <;> exact hn0 (by rw [h]; ring)
  have hv2odd : v ^ 2 % 2 = 1 := by rcases hv with h | h <;> omega
  -- `x ^ 2 = (2 * u ^ 2) ^ 2 + (v ^ 2) ^ 2` is a second primitive Pythagorean triple
  have hpt : PythagoreanTriple (2 * u ^ 2) (v ^ 2) x := by
    show 2 * u ^ 2 * (2 * u ^ 2) + v ^ 2 * v ^ 2 = x * x
    linear_combination (-1 : ℤ) * h1 - 4 * hm2 - hn2
  have hgcd2 : Int.gcd (2 * u ^ 2) (v ^ 2) = 1 := by
    have e1 : (2 * u ^ 2) ^ 2 = (2 * m') ^ 2 := by linear_combination (-4 : ℤ) * hm2
    have e2 : (v ^ 2) ^ 2 = n ^ 2 := by linear_combination (-1 : ℤ) * hn2
    have hc2 : IsCoprime ((2 * u ^ 2) ^ 2) ((v ^ 2) ^ 2) := by
      rw [e1, e2]
      exact (Int.isCoprime_iff_gcd_eq_one.mpr hg).pow
    exact Int.isCoprime_iff_gcd_eq_one.mp
      ((IsCoprime.pow_iff (by norm_num) (by norm_num)).mp hc2)
  obtain ⟨M, N, hcase, hxMN, hMN, -⟩ :=
    PythagoreanTriple.coprime_classification.mp ⟨hpt, hgcd2⟩
  rcases hcase with ⟨-, h⟩ | ⟨h21, h22⟩
  · exfalso
    have : v ^ 2 = 2 * (M * N) := by rw [h]; ring
    omega
  -- `M * N = u ^ 2` with `M`, `N` coprime, so both are squares up to sign
  have h4 : M * N = u ^ 2 := by linarith
  obtain ⟨R, hR⟩ := Int.sq_of_gcd_eq_one hMN h4
  obtain ⟨S, hS⟩ := Int.sq_of_gcd_eq_one (by rwa [Int.gcd_comm]) (by rw [mul_comm]; exact h4)
  have hM2 : M ^ 2 = R ^ 4 := by rcases hR with h | h <;> rw [h] <;> ring
  have hN2 : N ^ 2 = S ^ 4 := by rcases hS with h | h <;> rw [h] <;> ring
  have hu2 : u ^ 2 ≠ 0 := pow_ne_zero 2 hu0
  have hM0 : M ≠ 0 := by
    rintro rfl
    exact hu2 (by rw [← h4]; ring)
  have hN0 : N ≠ 0 := by
    rintro rfl
    exact hu2 (by rw [← h4]; ring)
  have hR0 : R ≠ 0 := by
    rintro rfl
    rcases hR with h | h <;> exact hM0 (by rw [h]; ring)
  have hS0 : S ≠ 0 := by
    rintro rfl
    rcases hS with h | h <;> exact hN0 (by rw [h]; ring)
  refine ⟨R, S, v, hR0, hS0, hv0, by linear_combination (-1 : ℤ) * hM2 + hN2 - h22, ?_⟩
  -- size: `R ^ 2 ≤ R ^ 4 = M ^ 2 < M ^ 2 + N ^ 2 ≤ (M ^ 2 + N ^ 2) ^ 2 = x ^ 2`
  have hx2 : x ^ 2 = (M ^ 2 + N ^ 2) ^ 2 := by
    rcases hxMN with h | h
    · rw [h]
    · rw [h]
      ring
  have hR1 : 1 ≤ R ^ 2 := by
    have : 0 < R ^ 2 := by positivity
    omega
  have hN1 : 1 ≤ N ^ 2 := by
    have : 0 < N ^ 2 := by positivity
    omega
  have hR4 : R ^ 2 ≤ R ^ 4 := by nlinarith
  have ht : R ^ 2 + 1 ≤ M ^ 2 + N ^ 2 := by linarith
  have ht2 : M ^ 2 + N ^ 2 ≤ (M ^ 2 + N ^ 2) ^ 2 := by nlinarith
  linarith

/-- Strong induction on `|x|` for Fermat's right triangle theorem. -/
theorem fermat_right_triangle_aux : ∀ N : ℕ, ∀ x y z : ℤ, x.natAbs = N → x ≠ 0 → y ≠ 0 → z ≠ 0 →
    x ^ 4 - y ^ 4 ≠ z ^ 2 := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro x y z hxN hx hy hz heq
    by_cases hg : Int.gcd x y = 1
    · -- Coprime case: `(z, y ^ 2, x ^ 2)` is a primitive Pythagorean triple.
      have hpt : PythagoreanTriple z (y ^ 2) (x ^ 2) := by
        show z * z + y ^ 2 * y ^ 2 = x ^ 2 * x ^ 2
        linear_combination (-1 : ℤ) * heq
      have hgz : Int.gcd z (y ^ 2) = 1 := by
        have hc : IsCoprime (x ^ 4) (y ^ 2) := (Int.isCoprime_iff_gcd_eq_one.mpr hg).pow
        have hc' : IsCoprime (x ^ 4 + y ^ 2 * (-(y ^ 2))) (y ^ 2) := hc.add_mul_left_left _
        have e : x ^ 4 + y ^ 2 * (-(y ^ 2)) = z ^ 2 := by linear_combination heq
        rw [e] at hc'
        exact Int.isCoprime_iff_gcd_eq_one.mp ((IsCoprime.pow_left_iff (by norm_num)).mp hc')
      obtain ⟨m, n, hcase, hx2, hmn, hpar⟩ :=
        PythagoreanTriple.coprime_classification.mp ⟨hpt, hgz⟩
      have hxpos : 0 < x ^ 2 := by positivity
      have hx2' : x ^ 2 = m ^ 2 + n ^ 2 := by
        rcases hx2 with h | h
        · exact h
        · exfalso
          linarith [sq_nonneg m, sq_nonneg n]
      rcases hcase with ⟨-, hy2⟩ | ⟨hz', hy2⟩
      · -- `y ^ 2 = 2 * m * n`: the descent step gives a smaller solution.
        have key : ∃ R S v : ℤ, R ≠ 0 ∧ S ≠ 0 ∧ v ≠ 0 ∧ R ^ 4 - S ^ 4 = v ^ 2 ∧
            R ^ 2 < x ^ 2 := by
          rcases hpar with ⟨hm, hn⟩ | ⟨hm, hn⟩
          · exact descent_step hy hx2' hy2 hmn hm hn
          · exact descent_step hy (by rw [hx2']; ring) (by rw [hy2]; ring)
              (by rwa [Int.gcd_comm]) hn hm
        obtain ⟨R, S, v, hR, hS, hv, hRS, hlt⟩ := key
        exact ih R.natAbs (by rw [← hxN]; exact Int.natAbs_lt_iff_sq_lt.mpr hlt) R S v rfl
          hR hS hv hRS
      · -- `z = 2 * m * n` and `y ^ 2 = m ^ 2 - n ^ 2`: then `m ^ 4 - n ^ 4 = (x * y) ^ 2`.
        have hm0 : m ≠ 0 := by
          rintro rfl
          exact hz (by rw [hz']; ring)
        have hn0 : n ≠ 0 := by
          rintro rfl
          exact hz (by rw [hz']; ring)
        have hn1 : 0 < n ^ 2 := by positivity
        refine ih m.natAbs (by rw [← hxN]; exact Int.natAbs_lt_iff_sq_lt.mpr (by linarith))
          m n (x * y) rfl hm0 hn0 (mul_ne_zero hx hy) ?_
        linear_combination (-(y ^ 2)) * hx2' - (m ^ 2 + n ^ 2) * hy2
    · -- Common factor `g`: divide it out.
      have hg0 : Int.gcd x y ≠ 0 := fun h => hx (Int.gcd_eq_zero_iff.mp h).1
      obtain ⟨g, hgdef⟩ : ∃ g : ℤ, g = (Int.gcd x y : ℤ) := ⟨_, rfl⟩
      obtain ⟨x', hx'⟩ : g ∣ x := hgdef ▸ Int.gcd_dvd_left ..
      obtain ⟨y', hy'⟩ : g ∣ y := hgdef ▸ Int.gcd_dvd_right ..
      have hgne : g ≠ 0 := by
        rw [hgdef]
        exact_mod_cast hg0
      have hdvd : g ^ 2 ∣ z := by
        have h : (g ^ 2) ^ 2 ∣ z ^ 2 := ⟨x' ^ 4 - y' ^ 4, by rw [← heq, hx', hy']; ring⟩
        exact (Int.pow_dvd_pow_iff (by norm_num)).mp h
      obtain ⟨z', hz'⟩ := hdvd
      have hx'0 : x' ≠ 0 := by
        rintro rfl
        exact hx (by rw [hx']; ring)
      have hy'0 : y' ≠ 0 := by
        rintro rfl
        exact hy (by rw [hy']; ring)
      have hz'0 : z' ≠ 0 := by
        rintro rfl
        exact hz (by rw [hz']; ring)
      have heq' : x' ^ 4 - y' ^ 4 = z' ^ 2 := by
        have h : g ^ 4 * (x' ^ 4 - y' ^ 4) = g ^ 4 * z' ^ 2 := by
          have h0 := heq
          rw [hx', hy', hz'] at h0
          linear_combination h0
        exact mul_left_cancel₀ (pow_ne_zero 4 hgne) h
      have hlt : x'.natAbs < N := by
        have h1 : x.natAbs = Int.gcd x y * x'.natAbs := by
          conv_lhs => rw [hx']
          rw [Int.natAbs_mul, hgdef, Int.natAbs_natCast]
        have h2 : 0 < x'.natAbs := Int.natAbs_pos.mpr hx'0
        have h3 : 2 ≤ Int.gcd x y := by omega
        rw [← hxN, h1]
        nlinarith
      exact ih x'.natAbs hlt x' y' z' rfl hx'0 hy'0 hz'0 heq'

/-- **Fermat's right triangle theorem**, in the form: `x ^ 4 - y ^ 4 = z ^ 2` has no solution in
nonzero integers. -/
theorem fermat_right_triangle (x y z : ℤ) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    x ^ 4 - y ^ 4 ≠ z ^ 2 :=
  fermat_right_triangle_aux x.natAbs x y z rfl hx hy hz

/-- `2` is not the square of a rational number. -/
theorem not_exists_sq_eq_two_rat : ¬ ∃ q : ℚ, q ^ 2 = 2 := by
  rintro ⟨q, hq⟩
  have h : IsSquare ((2 : ℕ) : ℚ) := ⟨q, by push_cast; rw [← hq]; ring⟩
  rw [Rat.isSquare_natCast_iff] at h
  exact absurd h (by norm_num)

/-- **1 is not a congruent number**: no right triangle with rational sides has area `1`. -/
theorem not_congruentNumber_one : ¬ CongruentNumber.congruentNumber 1 := by
  rintro ⟨a, b, c, habc, hab⟩
  have hab2 : a * b = 2 := by
    have h : (1 : ℚ) = 2⁻¹ * a * b := by exact_mod_cast hab
    linarith
  -- `a ^ 2 ≠ b ^ 2`: `a = b` gives `a ^ 2 = 2`, and `a = -b` gives `a * b ≤ 0`
  have hne : a ^ 2 ≠ b ^ 2 := by
    intro h
    have h' : (a - b) * (a + b) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h' with h1 | h1
    · exact not_exists_sq_eq_two_rat ⟨a, by linear_combination a * h1 + hab2⟩
    · nlinarith [sq_nonneg b]
  -- clear denominators
  set D : ℤ := ((a.den * b.den * c.den : ℕ) : ℤ) with hD
  have hDpos : 0 < D := by positivity
  have hDq : (D : ℚ) = (a.den : ℚ) * b.den * c.den := by simp [hD]
  have ha := Rat.mul_den_eq_num a
  have hb := Rat.mul_den_eq_num b
  have hc := Rat.mul_den_eq_num c
  set A : ℤ := a.num * (b.den * c.den) with hA
  set B : ℤ := b.num * (a.den * c.den) with hB
  set C : ℤ := c.num * (a.den * b.den) with hC
  have hAq : (A : ℚ) = a * D := by rw [hDq, hA]; push_cast; rw [← ha]; ring
  have hBq : (B : ℚ) = b * D := by rw [hDq, hB]; push_cast; rw [← hb]; ring
  have hCq : (C : ℚ) = c * D := by rw [hDq, hC]; push_cast; rw [← hc]; ring
  have e1 : A ^ 2 + B ^ 2 = C ^ 2 := by
    have : (A : ℚ) ^ 2 + (B : ℚ) ^ 2 = (C : ℚ) ^ 2 := by
      rw [hAq, hBq, hCq]; linear_combination (D : ℚ) ^ 2 * habc
    exact_mod_cast this
  have e2 : A * B = 2 * D ^ 2 := by
    have : (A : ℚ) * (B : ℚ) = 2 * (D : ℚ) ^ 2 := by
      rw [hAq, hBq]; linear_combination (D : ℚ) ^ 2 * hab2
    exact_mod_cast this
  have hC0 : C ≠ 0 := by
    rintro h
    rw [h] at e1
    have hA0 : A = 0 := by nlinarith [sq_nonneg A, sq_nonneg B]
    rw [hA0] at e2
    nlinarith
  have hZ : A ^ 2 - B ^ 2 ≠ 0 := by
    intro h
    apply hne
    have h' : ((A ^ 2 - B ^ 2 : ℤ) : ℚ) = 0 := by rw [h]; simp
    push_cast at h'
    rw [hAq, hBq] at h'
    have hD0 : (D : ℚ) ^ 2 ≠ 0 := by positivity
    have : (a ^ 2 - b ^ 2) * (D : ℚ) ^ 2 = 0 := by linear_combination h'
    rcases mul_eq_zero.mp this with h1 | h1
    · linarith
    · exact absurd h1 hD0
  exact fermat_right_triangle C (2 * D) (A ^ 2 - B ^ 2) hC0 (by omega) hZ
    (by linear_combination (-(C ^ 2 + A ^ 2 + B ^ 2)) * e1 + 4 * (A * B + 2 * D ^ 2) * e2)

example : type_of% CongruentNumber.not_congruentNumber_1 := not_congruentNumber_one

end CongruentNumberOneProof
