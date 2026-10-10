import MathProof.Basic

/-!
# Challenge C0040 — Erdős #672 / Euler: product of a 4-term AP is never a perfect square

**Status:** ✅ SOLVED — `sorry`-free, clean axioms (`#print axioms ap4_prod_ne_sq` =
`[propext, Classical.choice, Quot.sound]`; verify with `scripts/check-proof.sh
C0040Erdos672EulerFourTermAPProductNotSquare --all`).

The full theorem `ap4_prod_ne_sq` (Euler: the product of a 4-term AP of positive integers with
coprime common difference is never a perfect square) is proved end to end:
* `d = 1` case is direct (consecutive-integers sandwich); both parity branches of `d ≥ 2`
  (`sg7d_descent_core` odd, `sg7e_even_branch` even) reduce — with no `sorry` — through
  `concordant_forms_core` / `concordant_forms_gcd3` to `no_four_squares_in_ap`; the concordant
  system `e²+P²=2Q²`, `f²+Q²=2P²` is certified *equivalent* to `e², Q², P², f²` being a 4-term AP
  of squares with common difference `Q²-e² ≠ 0`.
* `no_four_squares_in_ap` (Fermat's "no four squares in arithmetic progression", 1640) is reduced
  (sign trichotomy → `..._pos` → pass to |·|, rule out a zero root) to the clean positive,
  strictly-ordered case `four_squares_ap_descent`, proved by strong induction on `u.natAbs` via the
  descent step `four_squares_ap_descent_step` (non-primitive gcd-reduction + primitive core).
* The **primitive Fermat descent core** `four_squares_ap_descent_step_primitive` is the genuine
  crux — Mathlib has NO anchor (no four-squares-in-AP, no `x⁴−y⁴=z²` right-triangle theorem, no
  congruent-number theorem; the only nearby result `not_fermat_42` is the parallel `+`-descent, not
  a usable reduction). It is closed here from scratch: halve to two equal-*area* Pythagorean
  triangles → Euler four-number factorisation `P·Q = P'·Q'` → the concordant `(1,4)` form
  (`X²+Y²=□`, `X²+4Y²=□`) → infinite descent on `|X|·|Y|` via
  `PythagoreanTriple.coprime_classification'` (twice), with the residual cofactor `k ∣ 3` killed
  mod 3. (NB: equal-*area* ≠ square-*area*, so this is strictly harder than Fermat's right-triangle
  descent — no single square-extraction shortcut.) This lemma is a genuine Mathlib gap → a Mathlib-PR
  candidate.
per the INFRA-LEMMA decomposition (see the C0031 pattern).

This is the ℕ-core arithmetic fact underlying Erdős #672 / Euler's theorem: the product of
four terms of an arithmetic progression of positive integers with coprime common difference is
never a perfect square. The Finset/ENat plumbing that turns this into the literal `Erdos672With`
statement is a separate, later step.

Workflow:
1. build it:  `lake build MathProof.Challenges.C0040Erdos672EulerFourTermAPProductNotSquare`
2. verify done (no sorry, clean axioms):  `scripts/check-proof.sh C0040Erdos672EulerFourTermAPProductNotSquare`
-/

namespace MathProof.Challenges.C0040Erdos672EulerFourTermAPProductNotSquare

/-- **Euler's theorem, `d = 1` case.** Four consecutive positive integers starting at `n`
never have a product that is a perfect square.

Proof idea: `n(n+1)(n+2)(n+3) + 1 = (n² + 3n + 1)²` (a pure `ring` identity, no subtraction
needed since `d⁴ = 1`). Writing `x := n² + 3n + 1`, the product `P` satisfies `P + 1 = x²`, i.e.
`P = x² - 1`. Since `n ≥ 1` forces `x ≥ 5 > 1`, `P` lies strictly between the consecutive squares
`(x-1)²` and `x²`, hence cannot itself be a perfect square. -/
theorem ap4_prod_ne_sq_d_eq_one (n q : ℕ) (hn : 0 < n) :
    n * (n + 1) * (n + 1 + 1) * (n + 1 + 1 + 1) ≠ q ^ 2 := by
  intro heq
  set x := n ^ 2 + 3 * n + 1 with hx_def
  have hkey : n * (n + 1) * (n + 1 + 1) * (n + 1 + 1 + 1) + 1 = x ^ 2 := by
    rw [hx_def]; ring
  have hxq : q ^ 2 + 1 = x ^ 2 := by rw [← heq]; exact hkey
  have hx5 : 5 ≤ x := by rw [hx_def]; nlinarith
  have hqx : q < x := by
    by_contra h
    have hle : x ≤ q := by omega
    have : x ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hle 2
    omega
  have hqx' : q + 1 ≤ x := by omega
  have hstep : (q + 1) ^ 2 ≤ x ^ 2 := Nat.pow_le_pow_left hqx' 2
  nlinarith [hxq, hx5, hstep]

/-! ## Reduction lemmas for the `d ≥ 2` crux (Euler's infinite descent)

These are leaves in the `proof-strategist` decomposition of `ap4_prod_ne_sq_d_ge_two`. Given
the anchor `x := n² + 3nd + d²` with `P + d⁴ = x²`, `gcd(x,d) = 1`, and `q² + d⁴ = x²`, set
`a := x - q`, `b := x + q` (so `a*b = d⁴` in `ℤ`). The lemmas below establish: `gcd(x,q) = 1`
(sg-coprime), `1 ≤ a ≤ d² - 1` (sg5), `gcd(a,b) ∣ 2` (sg7a), the odd-branch 4th-power
extraction `a = e⁴, b = f⁴, e*f = d` (sg7b), the algebra bridge to `(f²-e²)² = 2n(n+3d)`
(sg7c), and the two summit lemmas — the descent core (sg7d) and the even-`d` branch (sg7e) —
now both fully proved (they reduce to `concordant_forms_core` / `no_four_squares_in_ap`). -/

/-- **sg-coprime.** If `q² + d⁴ = x²` and `gcd(x,d) = 1`, then `gcd(x,q) = 1`.
Proof: `g := gcd(x,q)` divides `x² - q² = d⁴`; since `g ∣ x` and `Coprime x d`, `Coprime g d`,
hence `Coprime g (d⁴)`; combined with `g ∣ d⁴` this forces `g = 1`. -/
theorem coprime_of_sq_sub_sq_eq_pow4 (x q d : ℕ) (hxq : q ^ 2 + d ^ 4 = x ^ 2)
    (hcop : Nat.Coprime x d) : Nat.Coprime x q := by
  set g := Nat.gcd x q with hg_def
  have hgx : g ∣ x := Nat.gcd_dvd_left x q
  have hgq : g ∣ q := Nat.gcd_dvd_right x q
  have hgx2 : g ∣ x ^ 2 := dvd_pow hgx two_ne_zero
  have hgq2 : g ∣ q ^ 2 := dvd_pow hgq two_ne_zero
  have hgd4 : g ∣ d ^ 4 := by
    have hsub : g ∣ x ^ 2 - q ^ 2 := Nat.dvd_sub hgx2 hgq2
    have heqsub : x ^ 2 - q ^ 2 = d ^ 4 := by omega
    rwa [heqsub] at hsub
  have hcop_gd : Nat.Coprime g d := hcop.coprime_dvd_left hgx
  have hcop_gd4 : Nat.Coprime g (d ^ 4) := hcop_gd.pow_right 4
  have hg1 : g = 1 := by
    have := hcop_gd4
    unfold Nat.Coprime at this
    rwa [Nat.gcd_eq_left hgd4] at this
  show Nat.gcd x q = 1
  rw [← hg_def, hg1]

/-- **sg7a.** If `x` and `q` are coprime integers, then `Int.gcd (x - q) (x + q) ∣ 2`.
Proof: any common divisor `g` of `a := x - q`, `b := x + q` divides `a + b = 2x` and
`b - a = 2q`; Bézout on `gcd x q = 1` gives `1 = x·A + q·B` (`Int.gcd_eq_gcd_ab`), so
`g ∣ 2 = 2x·A + 2q·B`. -/
theorem gcd_sub_add_dvd_two_of_coprime (x q : ℤ) (hcop : Int.gcd x q = 1) :
    Int.gcd (x - q) (x + q) ∣ 2 := by
  have hga : (↑(Int.gcd (x - q) (x + q)) : ℤ) ∣ (x - q) := Int.gcd_dvd_left (x - q) (x + q)
  have hgb : (↑(Int.gcd (x - q) (x + q)) : ℤ) ∣ (x + q) := Int.gcd_dvd_right (x - q) (x + q)
  have hg2x : (↑(Int.gcd (x - q) (x + q)) : ℤ) ∣ 2 * x := by
    have hsum : (x - q) + (x + q) = 2 * x := by ring
    rw [← hsum]; exact dvd_add hga hgb
  have hg2q : (↑(Int.gcd (x - q) (x + q)) : ℤ) ∣ 2 * q := by
    have hdiff : (x + q) - (x - q) = 2 * q := by ring
    rw [← hdiff]; exact dvd_sub hgb hga
  have hbez : (1 : ℤ) = x * Int.gcdA x q + q * Int.gcdB x q := by
    have := Int.gcd_eq_gcd_ab x q
    rwa [hcop, Nat.cast_one] at this
  have h2 : (2 : ℤ) = (2 * x) * Int.gcdA x q + (2 * q) * Int.gcdB x q := by
    linear_combination 2 * hbez
  have hgdvd2 : (↑(Int.gcd (x - q) (x + q)) : ℤ) ∣ (2 : ℤ) := by
    rw [h2]
    exact dvd_add (hg2x.mul_right _) (hg2q.mul_right _)
  exact_mod_cast hgdvd2

/-- Even powers only see the absolute value: `y ^ 4 = (|y|.toNat) ^ 4` cast to `ℤ`. -/
private theorem pow_four_natAbs (y : ℤ) : y ^ 4 = ((y.natAbs : ℤ)) ^ 4 := by
  have h1 : (|y| : ℤ) ^ 2 = y ^ 2 := sq_abs y
  have h2 : (y.natAbs : ℤ) = |y| := (Int.abs_eq_natAbs y).symm
  calc y ^ 4 = (y ^ 2) ^ 2 := by ring
    _ = ((|y| : ℤ) ^ 2) ^ 2 := by rw [h1]
    _ = (|y| : ℤ) ^ 4 := by ring
    _ = ((y.natAbs : ℤ)) ^ 4 := by rw [h2]

/-- The companion fact in `|y|` form: `|y| ^ 4 = y ^ 4`. -/
private theorem abs_pow_four (y : ℤ) : (|y| : ℤ) ^ 4 = y ^ 4 := by
  rw [pow_four_natAbs y, Int.abs_eq_natAbs]

/-- **sg7b (odd branch).** If `a * b = d ^ 4` with `Int.gcd a b = 1` and `a, b > 0`, then `a, b`
are each a positive integer's 4th power, with the two roots multiplying to `d`.
Proof: `exists_associated_pow_of_mul_eq_pow` applied to `a*b = d^4` (and, by symmetry, to
`b*a = d^4`) gives `d1, d2` with `a` associated to `d1^4` and `b` associated to `d2^4`; since
`d1^4, d2^4 ≥ 0` and `a, b > 0`, the associating unit must be `1` (not `-1`) in each case, so
`a = d1^4, b = d2^4`; take `e := |d1|, f := |d2|` (even powers ignore sign) and recover
`e * f = d` from `(e*f)^4 = a*b = d^4` by injectivity of `(·)^4` on `ℕ`. -/
theorem sg7b_odd_branch (d : ℕ) (a b : ℤ) (hab : a * b = (d : ℤ) ^ 4)
    (hgcd1 : Int.gcd a b = 1) (ha_pos : 0 < a) (hb_pos : 0 < b) :
    ∃ e f : ℕ, a = (e : ℤ) ^ 4 ∧ b = (f : ℤ) ^ 4 ∧ e * f = d := by
  have hunit_ab : IsUnit (GCDMonoid.gcd a b) := by
    rw [← Int.coe_gcd, hgcd1, Nat.cast_one]; exact isUnit_one
  obtain ⟨d1, hd1⟩ := exists_associated_pow_of_mul_eq_pow hunit_ab hab
  have hunit_ba : IsUnit (GCDMonoid.gcd b a) := (gcd_comm' a b).isUnit_iff.mp hunit_ab
  have hab' : b * a = (d : ℤ) ^ 4 := by rw [mul_comm]; exact hab
  obtain ⟨d2, hd2⟩ := exists_associated_pow_of_mul_eq_pow hunit_ba hab'
  obtain ⟨u1, hu1⟩ := hd1
  obtain ⟨u2, hu2⟩ := hd2
  have hd1_nonneg : (0 : ℤ) ≤ d1 ^ 4 := by positivity
  have hd2_nonneg : (0 : ℤ) ≤ d2 ^ 4 := by positivity
  have hu1_one : u1 = 1 := by
    rcases Int.units_eq_one_or u1 with h | h
    · exact h
    · exfalso; rw [h] at hu1; simp only [Units.val_neg, Units.val_one, mul_neg, mul_one] at hu1
      omega
  have hu2_one : u2 = 1 := by
    rcases Int.units_eq_one_or u2 with h | h
    · exact h
    · exfalso; rw [h] at hu2; simp only [Units.val_neg, Units.val_one, mul_neg, mul_one] at hu2
      omega
  rw [hu1_one, Units.val_one, mul_one] at hu1
  rw [hu2_one, Units.val_one, mul_one] at hu2
  refine ⟨d1.natAbs, d2.natAbs, ?_, ?_, ?_⟩
  · rw [← hu1]; exact pow_four_natAbs d1
  · rw [← hu2]; exact pow_four_natAbs d2
  · have hz : ((d1.natAbs * d2.natAbs : ℕ) : ℤ) ^ 4 = (d : ℤ) ^ 4 := by
      push_cast
      rw [mul_pow, abs_pow_four d1, abs_pow_four d2, hu1, hu2, hab]
    have hz' : (d1.natAbs * d2.natAbs) ^ 4 = d ^ 4 := by exact_mod_cast hz
    exact Nat.pow_left_injective (by norm_num) hz'

/-- **sg7c.** The algebra bridge: if `e * f = d` and `e⁴ + f⁴ = 2*(n² + 3nd + d²)`
(the latter being `a + b = 2x` once `a = e⁴, b = f⁴`), then `(f² - e²)² = 2n(n + 3d)`. -/
theorem sg7c_bridge (n d e f : ℕ) (hef : e * f = d)
    (hsum : (e : ℤ) ^ 4 + (f : ℤ) ^ 4 = 2 * ((n : ℤ) ^ 2 + 3 * n * d + d ^ 2)) :
    ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) ^ 2 = 2 * (n : ℤ) * ((n : ℤ) + 3 * d) := by
  have hefz : (e : ℤ) * (f : ℤ) = (d : ℤ) := by exact_mod_cast hef
  linear_combination hsum - 2 * ((d : ℤ) + (e : ℤ) * (f : ℤ)) * hefz

/-- A perfect square is `0` or `1` mod `4`. -/
private theorem sq_mod_four (m : ℕ) : m ^ 2 % 4 = 0 ∨ m ^ 2 % 4 = 1 := by
  have h : m % 4 < 4 := Nat.mod_lt m (by norm_num)
  have hpm : m ^ 2 % 4 = (m % 4) ^ 2 % 4 := by rw [Nat.pow_mod]
  rw [hpm]
  interval_cases (m % 4) <;> decide

/-- Odd squares are `1` mod `8`: for `m` odd, `m² % 8 = 1`.
Proof: `m = 2k+1`, so `m² = 4·k(k+1) + 1`; `k(k+1)` is even (`Nat.even_mul_succ_self`), say
`= j + j`, giving `m² = 8j + 1`. -/
private theorem odd_sq_mod_eight (m : ℕ) (hm : Odd m) : m ^ 2 % 8 = 1 := by
  obtain ⟨k, hk⟩ := hm
  subst hk
  obtain ⟨j, hj⟩ := Nat.even_mul_succ_self k
  have heq : (2 * k + 1) ^ 2 = 4 * (k * (k + 1)) + 1 := by ring
  rw [hj] at heq
  omega

/-- **Auxiliary (√2 irrationality, ℕ form).** No positive `b` satisfies `a² = 2·b²`.
Proof: infinite descent on `b` — `a² = 2b²` forces `a` even, `a = 2k`, hence `b² = 2k²` with
`k < b`, so the strong induction hypothesis gives `k = 0`, whence `b = 0`. -/
private theorem eq_zero_of_sq_eq_two_mul_sq_nat :
    ∀ b : ℕ, ∀ a : ℕ, a ^ 2 = 2 * b ^ 2 → b = 0 := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro a hab
    rcases Nat.eq_zero_or_pos b with hb | hb
    · exact hb
    · exfalso
      rcases Nat.even_or_odd a with hae | hao
      · obtain ⟨k, hk⟩ := hae
        have hb2 : b ^ 2 = 2 * k ^ 2 := by subst hk; nlinarith
        have hkb : k < b := by nlinarith [hb2, sq_nonneg k, hb]
        have hk0 := ih k hkb b hb2
        subst hk0; simp at hb2; omega
      · obtain ⟨k, hk⟩ := hao
        subst hk
        have hexp : (2 * k + 1) ^ 2 = 2 * (2 * k ^ 2 + 2 * k) + 1 := by ring
        rw [hexp] at hab; omega

/-- **Auxiliary (√2 irrationality, ℤ form).** `a² = 2·b²` over `ℤ` forces `b = 0`. -/
private theorem eq_zero_of_sq_eq_two_mul_sq (a b : ℤ) (h : a ^ 2 = 2 * b ^ 2) : b = 0 := by
  have hnat : a.natAbs ^ 2 = 2 * b.natAbs ^ 2 := by
    have h1 : (a.natAbs : ℤ) ^ 2 = 2 * (b.natAbs : ℤ) ^ 2 := by
      rw [Int.natAbs_sq, Int.natAbs_sq]; exact h
    exact_mod_cast h1
  have := eq_zero_of_sq_eq_two_mul_sq_nat b.natAbs a.natAbs hnat
  simpa using this

/-! ## The Fermat descent for the primitive case

The primitive configuration is shown to be **contradictory** (so the descent step holds
vacuously — a strictly stronger conclusion than producing a smaller AP). The route:
1. primitivity ⇒ `r, s, t, u` odd and `gcd r t = gcd s u = 1`;
2. halving, `t = P + Q`, `r = P − Q`, `u = P' + Q'`, `s = P' − Q'`, turns the two relations into
   two Pythagorean triples `(P, Q, s)`, `(P', Q', t)` of **equal area** `P Q = P' Q'`;
3. the four-way factorisation `P = g p, Q = h q, P' = g q, Q' = h p` gives
   `2 g h p q = (g² − h²)(q² − p²)`, whose cofactors multiply to `2`, yielding a coprime pair
   `(X, Y)` with `X² + Y²` and `X² + 4Y²` both squares (Euler's concordant form `(1, 4)`);
4. that concordant form has no nontrivial solution — an infinite descent on `|X|·|Y|` via two
   applications of `PythagoreanTriple.coprime_classification'` and one more four-way
   factorisation, with the residual cofactor `k ∣ 3` killed by squares mod `3`. -/

/-- Squares mod 3 are `0,1`, so `3 ∣ a² + b²` forces `3 ∣ a` and `3 ∣ b`. -/
private theorem fsap_three_dvd_of_sq_add_sq (a b : ℤ) (h : (3 : ℤ) ∣ a ^ 2 + b ^ 2) :
    (3 : ℤ) ∣ a ∧ (3 : ℤ) ∣ b := by
  have key : ∀ x y : ZMod 3, x ^ 2 + y ^ 2 = 0 → x = 0 ∧ y = 0 := by decide
  have hz : ((a ^ 2 + b ^ 2 : ℤ) : ZMod 3) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast h
  push_cast at hz
  obtain ⟨ha, hb⟩ := key _ _ hz
  constructor
  · exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd a 3).mp ha
  · exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd b 3).mp hb

/-- Descent core for the concordant form `(1,4)`: from `x² − y² = a² − b²`, `x y = 2 a b`
(coprime pairs, `y` even) extract a smaller concordant pair. -/
private theorem fsap_descent_core (x y a b : ℤ) (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : IsCoprime x y) (hab : IsCoprime a b) (hy2 : 2 ∣ y)
    (h1 : x ^ 2 - y ^ 2 = a ^ 2 - b ^ 2) (h2 : x * y = 2 * (a * b)) :
    ∃ X Y : ℤ, X ≠ 0 ∧ Y ≠ 0 ∧ IsCoprime X Y ∧ (∃ Z, X ^ 2 + Y ^ 2 = Z ^ 2) ∧
      (∃ W, X ^ 2 + 4 * Y ^ 2 = W ^ 2) ∧ X.natAbs * Y.natAbs * 2 ≤ x.natAbs * y.natAbs := by
  obtain ⟨y', rfl⟩ := hy2
  have hy' : y' ≠ 0 := by rintro rfl; simp at hy
  have h2' : x * y' = a * b := by
    have : 2 * (x * y') = 2 * (a * b) := by linear_combination h2
    exact mul_left_cancel₀ two_ne_zero this
  have hxab : x ∣ a * b := Dvd.intro y' h2'
  obtain ⟨x₁, x₂, hx₁a, hx₂b, hx12⟩ := exists_dvd_and_dvd_of_dvd_mul hxab
  obtain ⟨y₁, hy₁⟩ := hx₁a
  obtain ⟨y₂, hy₂⟩ := hx₂b
  have hx₁ : x₁ ≠ 0 := by rintro rfl; simp at hx12; exact hx hx12
  have hx₂ : x₂ ≠ 0 := by rintro rfl; simp at hx12; exact hx hx12
  have hy12 : y' = y₁ * y₂ := by
    have : x₁ * x₂ * y' = x₁ * x₂ * (y₁ * y₂) := by
      rw [← hx12, h2', hy₁, hy₂, hx12]; ring
    exact mul_left_cancel₀ (mul_ne_zero hx₁ hx₂) this
  have hy₁ne : y₁ ≠ 0 := by rintro rfl; simp at hy12; exact hy' hy12
  have hy₂ne : y₂ ≠ 0 := by rintro rfl; simp at hy12; exact hy' hy12
  subst hx12 hy₁ hy₂ hy12
  have hkey : x₂ ^ 2 * (x₁ ^ 2 + y₂ ^ 2) = y₁ ^ 2 * (x₁ ^ 2 + 4 * y₂ ^ 2) := by
    linear_combination h1
  have hc21 : IsCoprime x₂ y₁ :=
    hxy.mono ⟨x₁, by ring⟩ ⟨2 * y₂, by ring⟩
  have hc12 : IsCoprime x₁ y₂ :=
    hab.mono ⟨y₁, by ring⟩ ⟨x₂, by ring⟩
  have hdvd : y₁ ^ 2 ∣ x₁ ^ 2 + y₂ ^ 2 :=
    (hc21.symm.pow (m := 2) (n := 2)).dvd_of_dvd_mul_left (Dvd.intro _ hkey.symm)
  obtain ⟨k, hk⟩ := hdvd
  have hk' : x₁ ^ 2 + 4 * y₂ ^ 2 = x₂ ^ 2 * k := by
    have : y₁ ^ 2 * (x₁ ^ 2 + 4 * y₂ ^ 2) = y₁ ^ 2 * (x₂ ^ 2 * k) := by
      rw [← hkey, hk]; ring
    exact mul_left_cancel₀ (pow_ne_zero 2 hy₁ne) this
  have hkpos : 0 < k := by
    have h1pos : 0 < x₁ ^ 2 + y₂ ^ 2 := by positivity
    by_contra hneg
    have : y₁ ^ 2 * k ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (not_lt.mp hneg)
    linarith
  have hk3 : k ∣ 3 := by
    obtain ⟨u, v, huv⟩ := hc12.pow (m := 2) (n := 2)
    exact ⟨u * (4 * y₁ ^ 2 - x₂ ^ 2) + v * (x₂ ^ 2 - y₁ ^ 2), by
      linear_combination (-3) * huv + (4 * u - v) * hk + (v - u) * hk'⟩
  have hkle : k ≤ 3 := Int.le_of_dvd (by norm_num) hk3
  rcases (by omega : k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl
  · refine ⟨x₁, y₂, hx₁, hy₂ne, hc12, ⟨y₁, by rw [hk]; ring⟩, ⟨x₂, by rw [hk']; ring⟩, ?_⟩
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_mul]
    have h2n : (2 : ℤ).natAbs = 2 := rfl
    rw [h2n]
    have hx₂p : 0 < x₂.natAbs := Int.natAbs_pos.mpr hx₂
    have hy₁p : 0 < y₁.natAbs := Int.natAbs_pos.mpr hy₁ne
    have e : x₁.natAbs * x₂.natAbs * (2 * (y₁.natAbs * y₂.natAbs)) =
        x₁.natAbs * y₂.natAbs * 2 * (x₂.natAbs * y₁.natAbs) := by ring
    rw [e]
    exact Nat.le_mul_of_pos_right _ (Nat.mul_pos hx₂p hy₁p)
  · exact absurd hk3 (by norm_num)
  · exfalso
    have h3 : (3 : ℤ) ∣ x₁ ^ 2 + y₂ ^ 2 := ⟨y₁ ^ 2, by rw [hk]; ring⟩
    obtain ⟨h3a, h3b⟩ := fsap_three_dvd_of_sq_add_sq x₁ y₂ h3
    have hu := hc12.isUnit_of_dvd' h3a h3b
    rw [Int.isUnit_iff] at hu
    omega

/-- One descent step for the concordant form `(1,4)` when `X` is odd. -/
private theorem fsap_concordant_descent_odd (X Y : ℤ) (hX : X ≠ 0) (hY : Y ≠ 0)
    (hXY : IsCoprime X Y) (hXodd : X % 2 = 1)
    (hZ : ∃ Z, X ^ 2 + Y ^ 2 = Z ^ 2) (hW : ∃ W, X ^ 2 + 4 * Y ^ 2 = W ^ 2) :
    ∃ X' Y' : ℤ, X' ≠ 0 ∧ Y' ≠ 0 ∧ IsCoprime X' Y' ∧ (∃ Z, X' ^ 2 + Y' ^ 2 = Z ^ 2) ∧
      (∃ W, X' ^ 2 + 4 * Y' ^ 2 = W ^ 2) ∧ X'.natAbs * Y'.natAbs < X.natAbs * Y.natAbs := by
  obtain ⟨Z, hZ⟩ := hZ
  obtain ⟨W, hW⟩ := hW
  have hX2 : 0 < X ^ 2 := by positivity
  have hZpos : 0 < |Z| := by
    rw [abs_pos]; rintro rfl; nlinarith [sq_nonneg Y]
  have hPT1 : PythagoreanTriple X Y |Z| := by
    show X * X + Y * Y = |Z| * |Z|
    have : |Z| * |Z| = Z ^ 2 := by rw [← sq, sq_abs]
    rw [this, ← hZ]; ring
  obtain ⟨m, n, hXmn, hYmn, hZmn, hmn, hpar, hm0⟩ :=
    PythagoreanTriple.coprime_classification' hPT1 (Int.isCoprime_iff_gcd_eq_one.mp hXY) hXodd hZpos
  have hm : m ≠ 0 := by rintro rfl; simp at hYmn; exact hY hYmn
  have hn : n ≠ 0 := by rintro rfl; simp at hYmn; exact hY hYmn
  have hcmn : IsCoprime m n := Int.isCoprime_iff_gcd_eq_one.mpr hmn
  have hWpos : 0 < |W| := by
    rw [abs_pos]; rintro rfl; nlinarith [sq_nonneg Y]
  have hPT2 : PythagoreanTriple (m ^ 2 - n ^ 2) (4 * m * n) |W| := by
    show (m ^ 2 - n ^ 2) * (m ^ 2 - n ^ 2) + (4 * m * n) * (4 * m * n) = |W| * |W|
    have : |W| * |W| = W ^ 2 := by rw [← sq, sq_abs]
    rw [this, ← hW, hXmn, hYmn]; ring
  have hX2' : IsCoprime X 2 := by
    obtain ⟨k, hk⟩ := Int.odd_iff.mpr hXodd
    exact ⟨1, -k, by rw [hk]; ring⟩
  have hcop2 : Int.gcd (m ^ 2 - n ^ 2) (4 * m * n) = 1 := by
    rw [← Int.isCoprime_iff_gcd_eq_one]
    have hc4 : IsCoprime (m ^ 2 - n ^ 2) 4 := by
      rw [← hXmn]
      have := hX2'.pow_right (n := 2)
      norm_num at this
      exact this
    have hc1 : IsCoprime (m ^ 2 - n ^ 2) m := by
      have e : m ^ 2 - n ^ 2 = -n ^ 2 + m * m := by ring
      rw [e]; exact (hcmn.symm.pow_left (m := 2)).neg_left.add_mul_left_left m
    have hc2 : IsCoprime (m ^ 2 - n ^ 2) n := by
      have e : m ^ 2 - n ^ 2 = m ^ 2 + n * (-n) := by ring
      rw [e]; exact (hcmn.pow_left (m := 2)).add_mul_left_left (-n)
    exact (hc4.mul_right hc1).mul_right hc2
  have hpar2 : (m ^ 2 - n ^ 2) % 2 = 1 := by rw [← hXmn]; exact hXodd
  obtain ⟨a, b, hab1, hab2, hWab, hgab, hpar', ha0⟩ :=
    PythagoreanTriple.coprime_classification' hPT2 hcop2 hpar2 hWpos
  have hab : a * b = 2 * (m * n) := by linarith
  have hcab : IsCoprime a b := Int.isCoprime_iff_gcd_eq_one.mpr hgab
  have hmn0 : m * n ≠ 0 := mul_ne_zero hm hn
  have hab0 : a * b ≠ 0 := by rw [hab]; exact mul_ne_zero two_ne_zero hmn0
  have ha : a ≠ 0 := left_ne_zero_of_mul hab0
  have hb : b ≠ 0 := right_ne_zero_of_mul hab0
  have hcore : ∃ X' Y' : ℤ, X' ≠ 0 ∧ Y' ≠ 0 ∧ IsCoprime X' Y' ∧ (∃ Z, X' ^ 2 + Y' ^ 2 = Z ^ 2) ∧
      (∃ W, X' ^ 2 + 4 * Y' ^ 2 = W ^ 2) ∧ X'.natAbs * Y'.natAbs * 2 ≤ a.natAbs * b.natAbs := by
    rcases hpar' with ⟨ha2, hb2⟩ | ⟨ha2, hb2⟩
    · obtain ⟨X', Y', h1, h2, h3, h4, h5, h6⟩ := fsap_descent_core b a n m hb ha hcab.symm
        hcmn.symm (Int.dvd_of_emod_eq_zero ha2) (by linear_combination hab1)
        (by linear_combination hab)
      exact ⟨X', Y', h1, h2, h3, h4, h5, by rw [mul_comm a.natAbs]; exact h6⟩
    · exact fsap_descent_core a b m n ha hb hcab hcmn (Int.dvd_of_emod_eq_zero hb2) hab1.symm hab
  obtain ⟨X', Y', h1, h2, h3, h4, h5, h6⟩ := hcore
  refine ⟨X', Y', h1, h2, h3, h4, h5, ?_⟩
  have habn : a.natAbs * b.natAbs = 2 * (m.natAbs * n.natAbs) := by
    have := congrArg Int.natAbs hab
    simpa [Int.natAbs_mul] using this
  have hYn : Y.natAbs = 2 * (m.natAbs * n.natAbs) := by
    rw [hYmn, Int.natAbs_mul, Int.natAbs_mul, mul_assoc]; rfl
  have hXpos : 0 < X.natAbs := Int.natAbs_pos.mpr hX
  have hmnpos : 0 < m.natAbs * n.natAbs :=
    Nat.mul_pos (Int.natAbs_pos.mpr hm) (Int.natAbs_pos.mpr hn)
  rw [hYn]
  have : 2 * (m.natAbs * n.natAbs) ≤ X.natAbs * (2 * (m.natAbs * n.natAbs)) :=
    Nat.le_mul_of_pos_left _ hXpos
  omega

/-- One descent step for the concordant form `(1,4)` (general parity). -/
private theorem fsap_concordant_descent (X Y : ℤ) (hX : X ≠ 0) (hY : Y ≠ 0)
    (hXY : IsCoprime X Y)
    (hZ : ∃ Z, X ^ 2 + Y ^ 2 = Z ^ 2) (hW : ∃ W, X ^ 2 + 4 * Y ^ 2 = W ^ 2) :
    ∃ X' Y' : ℤ, X' ≠ 0 ∧ Y' ≠ 0 ∧ IsCoprime X' Y' ∧ (∃ Z, X' ^ 2 + Y' ^ 2 = Z ^ 2) ∧
      (∃ W, X' ^ 2 + 4 * Y' ^ 2 = W ^ 2) ∧ X'.natAbs * Y'.natAbs < X.natAbs * Y.natAbs := by
  rcases Int.even_or_odd X with hXe | hXo
  · obtain ⟨X₀, hX₀⟩ := hXe
    obtain ⟨Z, hZ⟩ := hZ
    obtain ⟨W, hW⟩ := hW
    have hX₀ne : X₀ ≠ 0 := by rintro rfl; simp at hX₀; exact hX hX₀
    have h2X : (2 : ℤ) ∣ X := ⟨X₀, by rw [hX₀]; ring⟩
    have hYo : Y % 2 = 1 := by
      rcases Int.even_or_odd Y with hYe | hYo
      · exfalso
        have hu := hXY.isUnit_of_dvd' h2X hYe.two_dvd
        rw [Int.isUnit_iff] at hu
        omega
      · exact Int.odd_iff.mp hYo
    have hWe : Even W := by
      have : Even (W ^ 2) := ⟨2 * X₀ ^ 2 + 2 * Y ^ 2, by rw [← hW, hX₀]; ring⟩
      exact (Int.even_pow' two_ne_zero).mp this
    obtain ⟨W₀, hW₀⟩ := hWe
    have hcop : IsCoprime Y X₀ := hXY.symm.of_isCoprime_of_dvd_right ⟨2, by rw [hX₀]; ring⟩
    have hZ' : ∃ Z, Y ^ 2 + X₀ ^ 2 = Z ^ 2 := by
      refine ⟨W₀, ?_⟩
      have h4 : 4 * (Y ^ 2 + X₀ ^ 2) = 4 * W₀ ^ 2 := by
        rw [hX₀, hW₀] at hW; linear_combination hW
      exact mul_left_cancel₀ (by norm_num) h4
    have hW' : ∃ W, Y ^ 2 + 4 * X₀ ^ 2 = W ^ 2 := ⟨Z, by rw [hX₀] at hZ; linear_combination hZ⟩
    obtain ⟨X', Y', h1, h2, h3, h4, h5, h6⟩ :=
      fsap_concordant_descent_odd Y X₀ hY hX₀ne hcop hYo hZ' hW'
    refine ⟨X', Y', h1, h2, h3, h4, h5, ?_⟩
    have hXn : X.natAbs = 2 * X₀.natAbs := by rw [hX₀]; omega
    rw [hXn]
    have e : 2 * X₀.natAbs * Y.natAbs = 2 * (Y.natAbs * X₀.natAbs) := by ring
    rw [e]; omega
  · exact fsap_concordant_descent_odd X Y hX hY hXY (Int.odd_iff.mp hXo) hZ hW

/-- **No nontrivial solution of Euler's concordant form `(1,4)`:** there is no coprime pair of
nonzero integers `X, Y` with both `X² + Y²` and `X² + 4Y²` perfect squares (infinite descent on
`|X|·|Y|`). -/
private theorem fsap_no_concordant_pair : ∀ N : ℕ, ∀ X Y : ℤ, X.natAbs * Y.natAbs = N →
    X ≠ 0 → Y ≠ 0 → IsCoprime X Y → (∃ Z, X ^ 2 + Y ^ 2 = Z ^ 2) →
    (∃ W, X ^ 2 + 4 * Y ^ 2 = W ^ 2) → False := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro X Y hN hX hY hXY hZ hW
    obtain ⟨X', Y', hX', hY', hXY', hZ', hW', hlt⟩ := fsap_concordant_descent X Y hX hY hXY hZ hW
    exact ih _ (hN ▸ hlt) X' Y' rfl hX' hY' hXY' hZ' hW'

/-- Parity bookkeeping: a primitive 4-term AP of squares has all four roots odd. -/
private theorem fsap_four_ap_all_odd (r s t u : ℤ) (h1 : r ^ 2 + t ^ 2 = 2 * s ^ 2)
    (h2 : s ^ 2 + u ^ 2 = 2 * t ^ 2) (hprim : Int.gcd (Int.gcd r s) (Int.gcd t u) = 1) :
    Odd r ∧ Odd s ∧ Odd t ∧ Odd u := by
  have hro : Odd r := by
    by_contra hre
    rw [Int.not_odd_iff_even] at hre
    obtain ⟨k, hk⟩ := hre
    have hr4 : r ^ 2 = 4 * k ^ 2 := by rw [hk]; ring
    have ht2 : t ^ 2 % 2 = 0 := by omega
    have hte : Even t := (Int.even_pow' two_ne_zero).mp (Int.even_iff.mpr ht2)
    obtain ⟨l, hl⟩ := hte
    have ht4 : t ^ 2 = 4 * l ^ 2 := by rw [hl]; ring
    have hs2 : s ^ 2 % 2 = 0 := by omega
    have hse : Even s := (Int.even_pow' two_ne_zero).mp (Int.even_iff.mpr hs2)
    obtain ⟨j, hj⟩ := hse
    have hs4 : s ^ 2 = 4 * j ^ 2 := by rw [hj]; ring
    have hu2 : u ^ 2 % 2 = 0 := by omega
    have hue : Even u := (Int.even_pow' two_ne_zero).mp (Int.even_iff.mpr hu2)
    have h2r : (2 : ℤ) ∣ r := ⟨k, by rw [hk]; ring⟩
    have h2t : (2 : ℤ) ∣ t := ⟨l, by rw [hl]; ring⟩
    have h2s : (2 : ℤ) ∣ s := ⟨j, by rw [hj]; ring⟩
    have h2u : (2 : ℤ) ∣ u := hue.two_dvd
    have hg1 : (2 : ℕ) ∣ Int.gcd r s := Int.dvd_gcd (by exact_mod_cast h2r) (by exact_mod_cast h2s)
    have hg2 : (2 : ℕ) ∣ Int.gcd t u := Int.dvd_gcd (by exact_mod_cast h2t) (by exact_mod_cast h2u)
    have hg : (2 : ℕ) ∣ Int.gcd (Int.gcd r s : ℤ) (Int.gcd t u : ℤ) :=
      Int.dvd_gcd (Int.natCast_dvd_natCast.mpr hg1) (Int.natCast_dvd_natCast.mpr hg2)
    rw [hprim] at hg
    omega
  have hr2 : r ^ 2 % 2 = 1 := Int.odd_iff.mp hro.pow
  have hto : Odd t := by
    have : t ^ 2 % 2 = 1 := by omega
    exact (Int.odd_pow' two_ne_zero).mp (Int.odd_iff.mpr this)
  have hr4 : r ^ 2 % 4 = 1 := Int.sq_mod_four_eq_one_of_odd hro
  have ht4 : t ^ 2 % 4 = 1 := Int.sq_mod_four_eq_one_of_odd hto
  have hso : Odd s := by
    have : s ^ 2 % 2 = 1 := by omega
    exact (Int.odd_pow' two_ne_zero).mp (Int.odd_iff.mpr this)
  have hs2 : s ^ 2 % 2 = 1 := Int.odd_iff.mp hso.pow
  have huo : Odd u := by
    have : u ^ 2 % 2 = 1 := by omega
    exact (Int.odd_pow' two_ne_zero).mp (Int.odd_iff.mpr this)
  exact ⟨hro, hso, hto, huo⟩

/-- In a primitive 4-term AP of squares (`r` odd), the outer roots of the first sub-AP are
coprime: `gcd r t = 1` (a common divisor propagates to `s`, then `u`, then to the whole gcd). -/
private theorem fsap_four_ap_coprime (r s t u : ℤ) (hro : Odd r) (h1 : r ^ 2 + t ^ 2 = 2 * s ^ 2)
    (h2 : s ^ 2 + u ^ 2 = 2 * t ^ 2) (hprim : Int.gcd (Int.gcd r s) (Int.gcd t u) = 1) :
    IsCoprime r t := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  set d := Int.gcd r t with hd
  have hdr : (d : ℤ) ∣ r := Int.gcd_dvd_left r t
  have hdt : (d : ℤ) ∣ t := Int.gcd_dvd_right r t
  have hdo : Odd (d : ℤ) := by
    by_contra hde
    rw [Int.not_odd_iff_even] at hde
    have : Even r := even_iff_two_dvd.mpr (hde.two_dvd.trans hdr)
    exact (Int.not_even_iff_odd.mpr hro) this
  have hd2 : IsCoprime ((d : ℤ) ^ 2) 2 := by
    obtain ⟨k, hk⟩ := hdo
    have hd1 : IsCoprime (d : ℤ) 2 := ⟨1, -k, by rw [hk]; ring⟩
    exact hd1.pow_left
  have hd_s : (d : ℤ) ∣ s := by
    have h2s : (d : ℤ) ^ 2 ∣ 2 * s ^ 2 := by
      rw [← h1]; exact dvd_add (pow_dvd_pow_of_dvd hdr 2) (pow_dvd_pow_of_dvd hdt 2)
    have : (d : ℤ) ^ 2 ∣ s ^ 2 := hd2.dvd_of_dvd_mul_left h2s
    exact (Int.pow_dvd_pow_iff two_ne_zero).mp this
  have hd_u : (d : ℤ) ∣ u := by
    have hu2 : u ^ 2 = 2 * t ^ 2 - s ^ 2 := by linarith
    have : (d : ℤ) ^ 2 ∣ u ^ 2 := by
      rw [hu2]
      exact dvd_sub (dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hdt 2) 2) (pow_dvd_pow_of_dvd hd_s 2)
    exact (Int.pow_dvd_pow_iff two_ne_zero).mp this
  have hg1 : d ∣ Int.gcd r s := Int.dvd_gcd hdr hd_s
  have hg2 : d ∣ Int.gcd t u := Int.dvd_gcd hdt hd_u
  have hg : d ∣ Int.gcd (Int.gcd r s : ℤ) (Int.gcd t u : ℤ) :=
    Int.dvd_gcd (Int.natCast_dvd_natCast.mpr hg1) (Int.natCast_dvd_natCast.mpr hg2)
  rw [hprim] at hg
  exact Nat.dvd_one.mp hg

/-- Four-way factorisation of `P Q = P' Q'` with `gcd P Q = gcd P' Q' = 1`:
`P = g p, Q = h q, P' = g q, Q' = h p` with `g, h, p, q` pairwise coprime. -/
private theorem fsap_four_way_factor (P Q P' Q' : ℤ) (hP : P ≠ 0)
    (hPQ : IsCoprime P Q) (hP'Q' : IsCoprime P' Q') (h : P * Q = P' * Q') :
    ∃ g h p q : ℤ, P = g * p ∧ Q = h * q ∧ P' = g * q ∧ Q' = h * p ∧
      IsCoprime g h ∧ IsCoprime p q ∧ IsCoprime g p ∧ IsCoprime g q ∧
      IsCoprime h p ∧ IsCoprime h q := by
  have hdvd : P ∣ P' * Q' := Dvd.intro Q h
  obtain ⟨g, p, hgP', hpQ', hPgp⟩ := exists_dvd_and_dvd_of_dvd_mul hdvd
  obtain ⟨q, hq⟩ := hgP'
  obtain ⟨h', hh'⟩ := hpQ'
  have hg : g ≠ 0 := by rintro rfl; simp at hPgp; exact hP hPgp
  have hp : p ≠ 0 := by rintro rfl; simp at hPgp; exact hP hPgp
  have hQ' : Q = h' * q := by
    have : g * p * Q = g * p * (h' * q) := by rw [← hPgp, h, hq, hh', hPgp]; ring
    exact mul_left_cancel₀ (mul_ne_zero hg hp) this
  subst hPgp hq hh' hQ'
  refine ⟨g, h', p, q, rfl, rfl, rfl, by ring, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hPQ.of_mul_left_left.of_mul_right_left
  · exact hPQ.of_mul_left_right.of_mul_right_right
  · exact hP'Q'.of_mul_left_left.of_mul_right_left
  · exact hPQ.of_mul_left_left.of_mul_right_right
  · exact hPQ.of_mul_left_right.of_mul_right_left.symm
  · exact hP'Q'.of_mul_left_right.of_mul_right_right.symm

/-- Assemble a concordant pair from squared data: `X² = (gh)²`, `Y² = (pq)²`,
`(q²−p²)² = X²`, `(g²−h²)² = 4Y²` with `g² − h²` even. -/
private theorem fsap_concordant_of_params (X Y p q g h : ℤ) (hXsq : X ^ 2 = (g * h) ^ 2)
    (hYsq : Y ^ 2 = (p * q) ^ 2) (hA : (q ^ 2 - p ^ 2) ^ 2 = X ^ 2)
    (hB : (g ^ 2 - h ^ 2) ^ 2 = 4 * Y ^ 2) (heven : Even (g ^ 2 - h ^ 2)) :
    (∃ Z, X ^ 2 + Y ^ 2 = Z ^ 2) ∧ ∃ W, X ^ 2 + 4 * Y ^ 2 = W ^ 2 := by
  obtain ⟨c, hc⟩ := heven
  have hZ : g ^ 2 + h ^ 2 = 2 * (c + h ^ 2) := by linarith
  refine ⟨⟨c + h ^ 2, ?_⟩, ⟨q ^ 2 + p ^ 2, ?_⟩⟩
  · have h4 : 4 * (X ^ 2 + Y ^ 2) = 4 * (c + h ^ 2) ^ 2 := by
      linear_combination 4 * hXsq - hB + (g ^ 2 + h ^ 2 + 2 * (c + h ^ 2)) * hZ
    exact mul_left_cancel₀ (by norm_num) h4
  · linear_combination -hA + 4 * hYsq

/-- From pairwise-coprime `g h p q` with `2ghpq = (g²−h²)(q²−p²)` produce a nontrivial
concordant pair `(X, Y)`: `X² + Y²` and `X² + 4Y²` both squares. -/
private theorem fsap_concordant_of_four_params (g h p q : ℤ) (hg : g ≠ 0) (hh : h ≠ 0)
    (hp : p ≠ 0) (hq : q ≠ 0)
    (hgh : IsCoprime g h) (hpq : IsCoprime p q) (hgp : IsCoprime g p) (hgq : IsCoprime g q)
    (hhp : IsCoprime h p) (hhq : IsCoprime h q)
    (key : 2 * (g * h * p * q) = (g ^ 2 - h ^ 2) * (q ^ 2 - p ^ 2)) :
    ∃ X Y : ℤ, X ≠ 0 ∧ Y ≠ 0 ∧ IsCoprime X Y ∧ (∃ Z, X ^ 2 + Y ^ 2 = Z ^ 2) ∧
      ∃ W, X ^ 2 + 4 * Y ^ 2 = W ^ 2 := by
  have hc1 : IsCoprime (g * h) (g ^ 2 - h ^ 2) := by
    have e : g ^ 2 - h ^ 2 = -h ^ 2 + g * g := by ring
    have e' : g ^ 2 - h ^ 2 = g ^ 2 + h * (-h) := by ring
    apply IsCoprime.mul_left
    · rw [e]; exact (hgh.pow_right (n := 2)).neg_right.add_mul_left_right g
    · rw [e']; exact (hgh.symm.pow_right (n := 2)).add_mul_left_right (-h)
  have hc2 : IsCoprime (p * q) (q ^ 2 - p ^ 2) := by
    have e : q ^ 2 - p ^ 2 = q ^ 2 + p * (-p) := by ring
    have e' : q ^ 2 - p ^ 2 = -p ^ 2 + q * q := by ring
    apply IsCoprime.mul_left
    · rw [e]; exact (hpq.pow_right (n := 2)).add_mul_left_right (-p)
    · rw [e']; exact (hpq.symm.pow_right (n := 2)).neg_right.add_mul_left_right q
  have hd1 : g * h ∣ q ^ 2 - p ^ 2 :=
    hc1.dvd_of_dvd_mul_left (Dvd.intro (2 * (p * q)) (by linear_combination key))
  have hd2 : p * q ∣ g ^ 2 - h ^ 2 :=
    hc2.dvd_of_dvd_mul_left (Dvd.intro (2 * (g * h)) (by linear_combination key))
  obtain ⟨A, hA⟩ := hd1
  obtain ⟨B, hB⟩ := hd2
  have hne : g * h * p * q ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero hg hh) hp) hq
  have hAB : A * B = 2 := by
    have : g * h * p * q * (A * B) = g * h * p * q * 2 := by
      rw [hA, hB] at key; linear_combination -key
    exact mul_left_cancel₀ hne this
  have hABn : A.natAbs * B.natAbs = 2 := by
    have := congrArg Int.natAbs hAB
    rwa [Int.natAbs_mul] at this
  have hAn : A.natAbs = 1 ∨ A.natAbs = 2 := by
    have hdv : A.natAbs ∣ 2 := Dvd.intro _ hABn
    have h2 := Nat.le_of_dvd (by norm_num) hdv
    have h0 : A.natAbs ≠ 0 := by intro h0; rw [h0] at hABn; simp at hABn
    omega
  have hA2 : A ^ 2 = (A.natAbs : ℤ) ^ 2 := (Int.natAbs_sq A).symm
  have hB2 : B ^ 2 = (B.natAbs : ℤ) ^ 2 := (Int.natAbs_sq B).symm
  have hXY : IsCoprime (g * h) (p * q) := (hgp.mul_right hgq).mul_left (hhp.mul_right hhq)
  rcases hAn with hA1 | hA1
  · have hB1 : B.natAbs = 2 := by rw [hA1] at hABn; omega
    have hA2' : A ^ 2 = 1 := by rw [hA2, hA1]; norm_num
    have hB2' : B ^ 2 = 4 := by rw [hB2, hB1]; norm_num
    have hBeven : Even (g ^ 2 - h ^ 2) := by
      have : B = 2 ∨ B = -2 := by omega
      rcases this with rfl | rfl
      · exact ⟨p * q, by rw [hB]; ring⟩
      · exact ⟨-(p * q), by rw [hB]; ring⟩
    refine ⟨g * h, p * q, mul_ne_zero hg hh, mul_ne_zero hp hq, hXY, ?_⟩
    exact fsap_concordant_of_params (g * h) (p * q) p q g h rfl rfl
      (by rw [hA]; linear_combination (g * h) ^ 2 * hA2')
      (by rw [hB]; linear_combination (p * q) ^ 2 * hB2') hBeven
  · have hB1 : B.natAbs = 1 := by rw [hA1] at hABn; omega
    have hA2' : A ^ 2 = 4 := by rw [hA2, hA1]; norm_num
    have hB2' : B ^ 2 = 1 := by rw [hB2, hB1]; norm_num
    have hAeven : Even (q ^ 2 - p ^ 2) := by
      have : A = 2 ∨ A = -2 := by omega
      rcases this with rfl | rfl
      · exact ⟨g * h, by rw [hA]; ring⟩
      · exact ⟨-(g * h), by rw [hA]; ring⟩
    refine ⟨p * q, g * h, mul_ne_zero hp hq, mul_ne_zero hg hh, hXY.symm, ?_⟩
    exact fsap_concordant_of_params (p * q) (g * h) h g q p (by ring) (by ring)
      (by rw [hB]; linear_combination (p * q) ^ 2 * hB2')
      (by rw [hA]; linear_combination (g * h) ^ 2 * hA2') hAeven

/-- **Primitive descent step** — the genuine irreducible Fermat infinite-descent kernel.
`four_squares_ap_descent_step` under the extra hypothesis that the configuration is *primitive*
(`gcd (gcd r s) (gcd t u) = 1`). The non-primitive case is handled by the homogeneous
gcd-reduction in `four_squares_ap_descent_step` below.

**Proved** (no `sorry`): the primitive hypotheses are shown to be *contradictory* — strictly
stronger than the stated conclusion, which then follows by `exfalso`. The argument is the
Fermat descent laid out in the section header above: `fsap_four_ap_all_odd` and
`fsap_four_ap_coprime` (parity + coprimality from primitivity), the halving
`t = P + Q, r = P − Q, u = P' + Q', s = P' − Q'` giving equal-area Pythagorean triples
`P Q = P' Q'`, `fsap_four_way_factor`, `fsap_concordant_of_four_params` (the cofactor
`A·B = 2` split producing the concordant pair `X² + Y² = □`, `X² + 4Y² = □`), and finally
`fsap_no_concordant_pair` (strong induction on `|X|·|Y|` through `fsap_concordant_descent`).

Mathlib exposes **no** anchor (no four-squares-in-AP, no `x⁴−y⁴=z²`, no congruent-number theorem;
`not_fermat_42` is the parallel `+`-descent, not a reduction), so the descent is built here from
`PythagoreanTriple.coprime_classification'` alone. -/
private theorem four_squares_ap_descent_step_primitive (r s t u : ℤ)
    (hr : 0 < r) (hrs : r < s) (hst : s < t) (htu : t < u)
    (h1 : r ^ 2 + t ^ 2 = 2 * s ^ 2) (h2 : s ^ 2 + u ^ 2 = 2 * t ^ 2)
    (hprim : Int.gcd (Int.gcd r s) (Int.gcd t u) = 1) :
    ∃ r' s' t' u' : ℤ, 0 < r' ∧ r' < s' ∧ s' < t' ∧ t' < u' ∧
      r' ^ 2 + t' ^ 2 = 2 * s' ^ 2 ∧ s' ^ 2 + u' ^ 2 = 2 * t' ^ 2 ∧
      u'.natAbs < u.natAbs := by
  exfalso
  obtain ⟨hro, hso, hto, huo⟩ := fsap_four_ap_all_odd r s t u h1 h2 hprim
  have hcrt : IsCoprime r t := fsap_four_ap_coprime r s t u hro h1 h2 hprim
  have hcsu : IsCoprime s u := by
    have hprim' : Int.gcd (Int.gcd u t) (Int.gcd s r) = 1 := by
      rw [Int.gcd_comm u t, Int.gcd_comm s r, Int.gcd_comm]; exact hprim
    exact (fsap_four_ap_coprime u t s r huo (by linear_combination h2) (by linear_combination h1)
      hprim').symm
  obtain ⟨P, hP⟩ : Even (t + r) := hto.add_odd hro
  obtain ⟨Q, hQ⟩ : Even (t - r) := hto.sub_odd hro
  obtain ⟨P', hP'⟩ : Even (u + s) := huo.add_odd hso
  obtain ⟨Q', hQ'⟩ : Even (u - s) := huo.sub_odd hso
  have ht : t = P + Q := by linarith
  have hrPQ : r = P - Q := by linarith
  have hu : u = P' + Q' := by linarith
  have hs : s = P' - Q' := by linarith
  subst ht hrPQ hu hs
  have hPpos : 0 < P := by linarith
  have hQpos : 0 < Q := by linarith
  have hP'pos : 0 < P' := by linarith
  have hQ'pos : 0 < Q' := by linarith
  have hcPQ : IsCoprime P Q := by
    obtain ⟨a, b, hab⟩ := hcrt
    exact ⟨a + b, b - a, by linear_combination hab⟩
  have hcP'Q' : IsCoprime P' Q' := by
    obtain ⟨a, b, hab⟩ := hcsu
    exact ⟨a + b, b - a, by linear_combination hab⟩
  have hprod : P * Q = P' * Q' := by
    have : 4 * (P * Q) = 4 * (P' * Q') := by linear_combination -h1 - h2
    exact mul_left_cancel₀ (by norm_num) this
  obtain ⟨g, h, p, q, hPg, hQh, hP'g, hQ'h, hgh, hpq, hgp, hgq, hhp, hhq⟩ :=
    fsap_four_way_factor P Q P' Q' hPpos.ne' hcPQ hcP'Q' hprod
  have hg : g ≠ 0 := by rintro rfl; simp at hPg; exact hPpos.ne' hPg
  have hp : p ≠ 0 := by rintro rfl; simp at hPg; exact hPpos.ne' hPg
  have hh : h ≠ 0 := by rintro rfl; simp at hQh; exact hQpos.ne' hQh
  have hq : q ≠ 0 := by rintro rfl; simp at hQh; exact hQpos.ne' hQh
  have key : 2 * (g * h * p * q) = (g ^ 2 - h ^ 2) * (q ^ 2 - p ^ 2) := by
    subst hPg hQh hP'g hQ'h
    have : 2 * (2 * (g * h * p * q)) = 2 * ((g ^ 2 - h ^ 2) * (q ^ 2 - p ^ 2)) := by
      linear_combination -h2
    exact mul_left_cancel₀ two_ne_zero this
  obtain ⟨X, Y, hX, hY, hXY, hZ, hW⟩ :=
    fsap_concordant_of_four_params g h p q hg hh hp hq hgh hpq hgp hgq hhp hhq key
  exact fsap_no_concordant_pair _ X Y rfl hX hY hXY hZ hW

/-- **Descent step** — the pure Fermat infinite-descent core. From a strictly increasing positive
4-term AP of squares (`0<r<s<t<u`, `r²+t²=2s²`, `s²+u²=2t²`) produce a *strictly smaller* one, with
smaller largest root (`u'.natAbs < u.natAbs`). Wrapping this in strong induction on `u.natAbs`
closes `four_squares_ap_descent` (done, below).

Attack (strategist DAG): if `Int.gcd (Int.gcd r s) (Int.gcd t u) > 1`, divide it out → smaller AP.
Otherwise primitive: the two overlapping sub-APs `r²,s²,t²` and `s²,t²,u²` are Pythagorean triples
(`x²+y²=2z² ⟺ ((x+y)/2)²+((x−y)/2)²=z²`); `PythagoreanTriple.coprime_classification'` parametrises
each as `(m²−n², 2mn, m²+n²)`. Now **proved**: the non-primitive case divides out the common gcd;
the primitive case is `four_squares_ap_descent_step_primitive`, an Euler concordant-forms descent
(equal-area triangles → four-number factorisation → `(1,4)` concordant form → descent on `|X|·|Y|`),
mirroring `Mathlib.NumberTheory.FLT.Four.Fermat42.not_minimal`. -/
private theorem four_squares_ap_descent_step (r s t u : ℤ)
    (hr : 0 < r) (hrs : r < s) (hst : s < t) (htu : t < u)
    (h1 : r ^ 2 + t ^ 2 = 2 * s ^ 2) (h2 : s ^ 2 + u ^ 2 = 2 * t ^ 2) :
    ∃ r' s' t' u' : ℤ, 0 < r' ∧ r' < s' ∧ s' < t' ∧ t' < u' ∧
      r' ^ 2 + t' ^ 2 = 2 * s' ^ 2 ∧ s' ^ 2 + u' ^ 2 = 2 * t' ^ 2 ∧
      u'.natAbs < u.natAbs := by
  by_cases hprim : Int.gcd (Int.gcd r s) (Int.gcd t u) = 1
  · -- Primitive configuration: the genuine Fermat descent.
    exact four_squares_ap_descent_step_primitive r s t u hr hrs hst htu h1 h2 hprim
  · -- Non-primitive: divide out `g := gcd (gcd r s) (gcd t u) ≥ 2`. The two relations are
    -- homogeneous of degree 2, so they persist; ordering and positivity persist; and the largest
    -- root strictly shrinks.
    have hrs_ne : Int.gcd r s ≠ 0 := by
      intro h; rw [Int.gcd_eq_zero_iff] at h; exact (ne_of_gt hr) h.1
    have hg_ne : Int.gcd (Int.gcd r s) (Int.gcd t u) ≠ 0 := by
      intro h; rw [Int.gcd_eq_zero_iff] at h; exact hrs_ne (by exact_mod_cast h.1)
    have hg_ge2 : 2 ≤ Int.gcd (Int.gcd r s) (Int.gcd t u) := by omega
    have hgz_pos : (0 : ℤ) < (Int.gcd (Int.gcd r s) (Int.gcd t u) : ℤ) := by
      exact_mod_cast (by omega : 0 < Int.gcd (Int.gcd r s) (Int.gcd t u))
    have hgz_ge2 : (2 : ℤ) ≤ (Int.gcd (Int.gcd r s) (Int.gcd t u) : ℤ) := by exact_mod_cast hg_ge2
    -- Divisibility of all four by `g`.
    have hdvd_r : (Int.gcd (Int.gcd r s) (Int.gcd t u) : ℤ) ∣ r :=
      (Int.gcd_dvd_left _ _).trans (Int.gcd_dvd_left r s)
    have hdvd_s : (Int.gcd (Int.gcd r s) (Int.gcd t u) : ℤ) ∣ s :=
      (Int.gcd_dvd_left _ _).trans (Int.gcd_dvd_right r s)
    have hdvd_t : (Int.gcd (Int.gcd r s) (Int.gcd t u) : ℤ) ∣ t :=
      (Int.gcd_dvd_right _ _).trans (Int.gcd_dvd_left t u)
    have hdvd_u : (Int.gcd (Int.gcd r s) (Int.gcd t u) : ℤ) ∣ u :=
      (Int.gcd_dvd_right _ _).trans (Int.gcd_dvd_right t u)
    obtain ⟨r0, hr0⟩ := hdvd_r
    obtain ⟨s0, hs0⟩ := hdvd_s
    obtain ⟨t0, ht0⟩ := hdvd_t
    obtain ⟨u0, hu0⟩ := hdvd_u
    set g : ℤ := (Int.gcd (Int.gcd r s) (Int.gcd t u) : ℤ) with hg_def
    -- Positivity of the reduced roots.
    have hr0pos : 0 < r0 := by
      rcases mul_pos_iff.mp (hr0 ▸ hr : 0 < g * r0) with ⟨_, h⟩ | ⟨h, _⟩
      · exact h
      · exact absurd h (not_lt.mpr (le_of_lt hgz_pos))
    -- Ordering of the reduced roots.
    have hr0s0 : r0 < s0 :=
      lt_of_mul_lt_mul_left (by rw [← hr0, ← hs0]; exact hrs) (le_of_lt hgz_pos)
    have hs0t0 : s0 < t0 :=
      lt_of_mul_lt_mul_left (by rw [← hs0, ← ht0]; exact hst) (le_of_lt hgz_pos)
    have ht0u0 : t0 < u0 :=
      lt_of_mul_lt_mul_left (by rw [← ht0, ← hu0]; exact htu) (le_of_lt hgz_pos)
    -- The two relations persist (cancel `g²`).
    have hgsq_ne : g ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hgz_pos)
    have h1' : r0 ^ 2 + t0 ^ 2 = 2 * s0 ^ 2 := by
      have hsub : (g * r0) ^ 2 + (g * t0) ^ 2 = 2 * (g * s0) ^ 2 := by
        rw [← hr0, ← ht0, ← hs0]; exact h1
      have hg2 : g ^ 2 * (r0 ^ 2 + t0 ^ 2) = g ^ 2 * (2 * s0 ^ 2) := by linear_combination hsub
      exact mul_left_cancel₀ hgsq_ne hg2
    have h2' : s0 ^ 2 + u0 ^ 2 = 2 * t0 ^ 2 := by
      have hsub : (g * s0) ^ 2 + (g * u0) ^ 2 = 2 * (g * t0) ^ 2 := by
        rw [← hs0, ← hu0, ← ht0]; exact h2
      have hg2 : g ^ 2 * (s0 ^ 2 + u0 ^ 2) = g ^ 2 * (2 * t0 ^ 2) := by linear_combination hsub
      exact mul_left_cancel₀ hgsq_ne hg2
    -- The largest root strictly shrinks.
    have hu0pos : 0 < u0 := lt_trans hr0pos (lt_trans hr0s0 (lt_trans hs0t0 ht0u0))
    have hu0_lt_u : u0 < u := by
      rw [hu0]; nlinarith [hgz_ge2, hu0pos, mul_le_mul_of_nonneg_right hgz_ge2 (le_of_lt hu0pos)]
    have hshrink : u0.natAbs < u.natAbs := by
      rw [Int.natAbs_lt_iff_sq_lt]; nlinarith [hu0pos, hu0_lt_u]
    exact ⟨r0, s0, t0, u0, hr0pos, hr0s0, hs0t0, ht0u0, h1', h2', hshrink⟩

/-- **Descent kernel for four squares in AP** — the isolated Fermat infinite-descent residual.
For strictly increasing *positive* integers `r < s < t < u` whose squares satisfy the two
concordant relations `r² + t² = 2s²` and `s² + u² = 2t²` (equivalently: `r², s², t², u²` is a
nonconstant 4-term arithmetic progression of squares), we have a contradiction.

This is Fermat's "no four squares in arithmetic progression" reduced (certified, see
`no_four_squares_in_ap`) to the clean positive, strictly-ordered case — exactly the state from
which a Pythagorean-classification descent proceeds (cf.
`Mathlib.NumberTheory.FLT.Four.Fermat42.not_minimal`, which mirrors this shape for `a⁴+b⁴=c²`).
Mathlib exposes **no** direct anchor: no four-squares-in-AP, no `x⁴−y⁴=z²` right-triangle theorem,
no congruent-number theorem; `not_fermat_42` is the parallel `+`-descent and does **not** reduce to
this one in finitely many steps (each primitive-Pythagorean split reproduces its own equation).
Now **proved** by strong induction on `u.natAbs` via the descent step
`four_squares_ap_descent_step` (now itself fully proved). -/
theorem four_squares_ap_descent (r s t u : ℤ)
    (hr : 0 < r) (hrs : r < s) (hst : s < t) (htu : t < u)
    (h1 : r ^ 2 + t ^ 2 = 2 * s ^ 2) (h2 : s ^ 2 + u ^ 2 = 2 * t ^ 2) : False := by
  suffices H : ∀ N : ℕ, ∀ r s t u : ℤ, u.natAbs = N →
      0 < r → r < s → s < t → t < u →
      r ^ 2 + t ^ 2 = 2 * s ^ 2 → s ^ 2 + u ^ 2 = 2 * t ^ 2 → False by
    exact H u.natAbs r s t u rfl hr hrs hst htu h1 h2
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro r s t u hN hr hrs hst htu h1 h2
    obtain ⟨r', s', t', u', hr', hrs', hst', htu', h1', h2', hlt⟩ :=
      four_squares_ap_descent_step r s t u hr hrs hst htu h1 h2
    exact ih u'.natAbs (hN ▸ hlt) r' s' t' u' rfl hr' hrs' hst' htu' h1' h2'

/-- **Positive-common-difference case of `no_four_squares_in_ap`.** With `D > 0` the four squares
are strictly increasing, so passing to absolute values yields strictly increasing roots `R<S<T<U`;
the smallest is nonzero (else `t² = 2s²`, impossible by `eq_zero_of_sq_eq_two_mul_sq`), reducing to
`four_squares_ap_descent`. -/
private theorem no_four_squares_in_ap_pos (r s t u D : ℤ) (hD : 0 < D)
    (h1 : s ^ 2 = r ^ 2 + D) (h2 : t ^ 2 = s ^ 2 + D) (h3 : u ^ 2 = t ^ 2 + D) : False := by
  have c1 : r ^ 2 + t ^ 2 = 2 * s ^ 2 := by linarith
  have c2 : s ^ 2 + u ^ 2 = 2 * t ^ 2 := by linarith
  have hsq_rs : r ^ 2 < s ^ 2 := by linarith
  have hsq_st : s ^ 2 < t ^ 2 := by linarith
  have hsq_tu : t ^ 2 < u ^ 2 := by linarith
  set R := (r.natAbs : ℤ) with hRdef
  set S := (s.natAbs : ℤ) with hSdef
  set T := (t.natAbs : ℤ) with hTdef
  set U := (u.natAbs : ℤ) with hUdef
  have hRsq : R ^ 2 = r ^ 2 := by rw [hRdef, Int.natAbs_sq]
  have hSsq : S ^ 2 = s ^ 2 := by rw [hSdef, Int.natAbs_sq]
  have hTsq : T ^ 2 = t ^ 2 := by rw [hTdef, Int.natAbs_sq]
  have hUsq : U ^ 2 = u ^ 2 := by rw [hUdef, Int.natAbs_sq]
  have hRnn : 0 ≤ R := by positivity
  have hSnn : 0 ≤ S := by positivity
  have hTnn : 0 ≤ T := by positivity
  have hUnn : 0 ≤ U := by positivity
  have hRS : R < S := by nlinarith [hRsq, hSsq, hsq_rs, hRnn, hSnn]
  have hST : S < T := by nlinarith [hSsq, hTsq, hsq_st, hSnn, hTnn]
  have hTU : T < U := by nlinarith [hTsq, hUsq, hsq_tu, hTnn, hUnn]
  have hRpos : 0 < R := by
    rcases lt_or_eq_of_le hRnn with h | h
    · exact h
    · exfalso
      have hr0 : r ^ 2 = 0 := by rw [← hRsq, ← h]; ring
      have hs2 : s ^ 2 = D := by linarith
      have ht2 : t ^ 2 = 2 * s ^ 2 := by linarith
      have hs0 := eq_zero_of_sq_eq_two_mul_sq t s ht2
      rw [hs0] at hs2; simp at hs2; omega
  have c1' : R ^ 2 + T ^ 2 = 2 * S ^ 2 := by rw [hRsq, hTsq, hSsq]; exact c1
  have c2' : S ^ 2 + U ^ 2 = 2 * T ^ 2 := by rw [hSsq, hUsq, hTsq]; exact c2
  exact four_squares_ap_descent R S T U hRpos hRS hST hTU c1' c2'

/-- **No four squares in a nonconstant arithmetic progression** (Fermat, 1640).
Four perfect squares `r², s², t², u²` cannot form an arithmetic progression with nonzero common
difference `D`.

This is the genuine irreducible descent kernel. It admits **no** congruence / local obstruction
(so the mod-4 / mod-8 arguments used elsewhere in this file provably cannot touch it): it is a
*global* fact of the exact same difficulty class as `not_fermat_42` (`a⁴+b⁴ ≠ c²`,
`Mathlib.NumberTheory.FLT.Four`). The classical proof is a Fermat infinite descent, realised by
parametrising the two overlapping three-term sub-APs (`r²,s²,t²` and `s²,t²,u²`) as Pythagorean
triples and producing a strictly smaller four-square AP (Dickson, *History of the Theory of
Numbers* II, ch. XIV; Mordell, *Diophantine Equations* ch. 4).

Mathlib (checked) exposes **no** four-squares-in-AP, Fermat right-triangle (`x⁴ - y⁴ ≠ z²`), or
congruent-number theorem, and `not_fermat_42` is reachable only through a birational/descent map,
not a short algebraic identity.

**This pass:** the statement is **certified-reduced** to the clean positive, strictly-ordered case
`four_squares_ap_descent` — normalize the sign of `D` (trichotomy; `D < 0` reverses the progression),
pass to absolute values, derive the two concordant relations, and rule out a zero smallest root via
`eq_zero_of_sq_eq_two_mul_sq`. `four_squares_ap_descent` is then proved by strong induction on
`u.natAbs` via the descent step (non-primitive gcd-reduction + the primitive Euler concordant-forms
descent core) — fully `sorry`-free. -/
theorem no_four_squares_in_ap (r s t u D : ℤ) (hD : D ≠ 0)
    (h1 : s ^ 2 = r ^ 2 + D) (h2 : t ^ 2 = s ^ 2 + D) (h3 : u ^ 2 = t ^ 2 + D) : False := by
  rcases lt_trichotomy D 0 with hneg | hzero | hpos
  · -- `D < 0`: `u², t², s², r²` is an AP with positive common difference `-D`.
    exact no_four_squares_in_ap_pos u t s r (-D) (by linarith)
      (by linarith) (by linarith) (by linarith)
  · exact hD hzero
  · exact no_four_squares_in_ap_pos r s t u D hpos h1 h2 h3

/-- **Concordant-forms `g = 3` branch — three squares in arithmetic progression.**
For coprime `e ≠ f`, both odd, no `P, Q` satisfy `e² + P² = 2Q²` and `f² + Q² = 2P²`
simultaneously.

**This pass (escalation): fully reduced — no residual `sorry` of its own.** The two equations are
*equivalent* to saying the four squares `e², Q², P², f²` form an arithmetic progression with
common difference `D := Q² - e²`: indeed `h1 ⟺ P² = 2Q² - e² ⟺ P² - Q² = Q² - e²` and
`h2 ⟺ f² = 2P² - Q² ⟺ f² - P² = P² - Q²`, so the consecutive gaps `Q²-e², P²-Q², f²-P²` are all
equal to `D`. And `D ≠ 0` (else `Q = e`, forcing `P = e` then `f = e`, contradicting `e ≠ f`).
So the statement is exactly **Fermat's "no four squares in arithmetic progression"**, discharged
here by `no_four_squares_in_ap`. (The coprimality/oddness/positivity hypotheses are not needed for
this reduction — the AP structure alone is the obstruction.) -/
theorem concordant_forms_gcd3 (e f P Q : ℕ) (_he : 0 < e) (_hf : 0 < f) (hne : e ≠ f)
    (_hcop : Nat.Coprime e f) (_heo : Odd e) (_hfo : Odd f)
    (h1 : e ^ 2 + P ^ 2 = 2 * Q ^ 2) (h2 : f ^ 2 + Q ^ 2 = 2 * P ^ 2) : False := by
  -- Cast the two concordant-forms equations to `ℤ`.
  have h1z : (e : ℤ) ^ 2 + (P : ℤ) ^ 2 = 2 * (Q : ℤ) ^ 2 := by exact_mod_cast h1
  have h2z : (f : ℤ) ^ 2 + (Q : ℤ) ^ 2 = 2 * (P : ℤ) ^ 2 := by exact_mod_cast h2
  -- The four squares `e², Q², P², f²` form an AP with common difference `D := Q² - e²`.
  set D : ℤ := (Q : ℤ) ^ 2 - (e : ℤ) ^ 2 with hD_def
  -- `D ≠ 0`: otherwise `Q² = e²`, forcing `P² = e²` (h1) and `f² = e²` (h2), so `f = e`.
  have hD_ne : D ≠ 0 := by
    intro hD0
    have hQe : (Q : ℤ) ^ 2 = (e : ℤ) ^ 2 := by rw [hD_def] at hD0; linarith
    have hPe : (P : ℤ) ^ 2 = (e : ℤ) ^ 2 := by linarith [h1z, hQe]
    have hfe : (f : ℤ) ^ 2 = (e : ℤ) ^ 2 := by linarith [h2z, hQe, hPe]
    have hfe_nat : f ^ 2 = e ^ 2 := by exact_mod_cast hfe
    exact hne (Nat.pow_left_injective (by norm_num) hfe_nat).symm
  -- The three AP-step equations (all gaps equal `D`).
  have hs1 : (Q : ℤ) ^ 2 = (e : ℤ) ^ 2 + D := by rw [hD_def]; ring
  have hs2 : (P : ℤ) ^ 2 = (Q : ℤ) ^ 2 + D := by rw [hD_def]; linarith [h1z]
  have hs3 : (f : ℤ) ^ 2 = (P : ℤ) ^ 2 + D := by rw [hD_def]; linarith [h1z, h2z]
  exact no_four_squares_in_ap (e : ℤ) (Q : ℤ) (P : ℤ) (f : ℤ) D hD_ne hs1 hs2 hs3

/-- **Concordant-forms descent core — ODD case, `g = 1` and `g = 3` split.** For coprime
`e ≠ f`, both **odd**, the product `(2f² + e²)(f² + 2e²)` is never a perfect square.

This is the *irreducible* Euler/Beeger infinite-descent kernel of the `d ≥ 2` crux; the full
`concordant_forms_core` reduces to it (the even/opposite-parity cases die by a `mod 4` argument,
here fully certified). Everything else in `sg7d_descent_core` is elementary algebra + coprimality
bookkeeping that provably reduces to **this** one 2-variable, both-odd statement.

Equivalent formulation (Euler's *concordant forms*): `x² + 2y² = z²` has no solution with
`x = e·f`, `y = e² + f²`, since the ℚ(√-2) norm identity gives
`(2f² + e²)(f² + 2e²) = (ef)² + 2(e² + f²)²`.

**Proof (this pass — `g = 1` closed, `g = 3` delegated).** `A := 2f²+e²`, `B := f²+2e²` are both
odd. `g := gcd(A,B) ∣ 3` (a Bézout-free `g ∣ 2A−B = 3f²` and `g ∣ 2B−A = 3e²`, then `g ∣
gcd(3e²,3f²) = 3·gcd(e²,f²) = 3` using `gcd(e,f)=1`), so `g ∈ {1,3}` (`g` prime-divisor split).
* `g = 1`: `A·B = W²` with `gcd(A,B)=1` gives `A = P²` (`exists_eq_pow_of_mul_eq_pow`, valid on
  `ℕ` since it's a `GCDMonoid` with trivial units), but `A` odd forces `P` odd, so
  `P² ≡ 1 (mod 8)` (`odd_sq_mod_eight`) while `A = 2f²+e² ≡ 3 (mod 8)` for odd `e,f` — contradiction.
* `g = 3`: write `A = 3A'`, `B = 3B'` with `gcd(A',B') = 1` (cancel the `3` from
  `gcd(3A',3B') = 3·gcd(A',B') = gcd(A,B) = 3`); `9 ∣ W²` forces `3 ∣ W = 3W'`, and
  `9W'² = 9A'B'` cancels to `W'² = A'B'`, giving `A' = P²`, `B' = Q²` the same way. Then
  `2A−B=3f²` and `2B−A=3e²` become (after dividing by `3`) `f²+Q² = 2P²` and `e²+P² = 2Q²` —
  **three squares in arithmetic progression**, delegated to `concordant_forms_gcd3`. -/
theorem concordant_forms_core_odd (e f W : ℕ) (he : 0 < e) (hf : 0 < f) (hne : e ≠ f)
    (hcop : Nat.Coprime e f) (heo : Odd e) (hfo : Odd f) :
    W ^ 2 ≠ (2 * f ^ 2 + e ^ 2) * (f ^ 2 + 2 * e ^ 2) := by
  intro hW
  set A := 2 * f ^ 2 + e ^ 2 with hA_def
  set B := f ^ 2 + 2 * e ^ 2 with hB_def
  -- `A` is odd (`2f²` even, `e²` odd).
  have hesq_odd : Odd (e ^ 2) := heo.pow
  have hfsq_odd : Odd (f ^ 2) := hfo.pow
  have hAodd : Odd A := by rw [hA_def]; exact (even_two_mul (f ^ 2)).add_odd hesq_odd
  -- `g := gcd A B` divides `3`.
  have hg_dvd_A : Nat.gcd A B ∣ A := Nat.gcd_dvd_left A B
  have hg_dvd_B : Nat.gcd A B ∣ B := Nat.gcd_dvd_right A B
  have hg_dvd_2A : Nat.gcd A B ∣ 2 * A := hg_dvd_A.mul_left 2
  have hg_dvd_2B : Nat.gcd A B ∣ 2 * B := hg_dvd_B.mul_left 2
  have heq3f : 2 * A - B = 3 * f ^ 2 := by rw [hA_def, hB_def]; omega
  have heq3e : 2 * B - A = 3 * e ^ 2 := by rw [hA_def, hB_def]; omega
  have hg_dvd_3f2 : Nat.gcd A B ∣ 3 * f ^ 2 := by
    rw [← heq3f]; exact Nat.dvd_sub hg_dvd_2A hg_dvd_B
  have hg_dvd_3e2 : Nat.gcd A B ∣ 3 * e ^ 2 := by
    rw [← heq3e]; exact Nat.dvd_sub hg_dvd_2B hg_dvd_A
  have hcop_sq' : Nat.gcd (e ^ 2) (f ^ 2) = 1 := hcop.pow 2 2
  have hgcd3ef : Nat.gcd (3 * e ^ 2) (3 * f ^ 2) = 3 := by
    rw [Nat.gcd_mul_left, hcop_sq', mul_one]
  have hg_dvd3 : Nat.gcd A B ∣ 3 := by
    rw [← hgcd3ef]; exact Nat.dvd_gcd hg_dvd_3e2 hg_dvd_3f2
  rcases (Nat.dvd_prime (by norm_num)).mp hg_dvd3 with hg1 | hg3
  · -- `g = 1`: `A` is a perfect square (coprime factors of `W²`), but `A ≡ 3 (mod 8)`.
    have hunit : IsUnit (gcd A B) := by rw [gcd_eq_nat_gcd, hg1]; exact isUnit_one
    obtain ⟨P, hP⟩ := exists_eq_pow_of_mul_eq_pow hunit hW.symm
    have hPodd : Odd P := by
      rcases Nat.even_or_odd P with hPe | hPo
      · exfalso
        obtain ⟨k, hk⟩ := hPe
        have hAeven : Even A := by rw [hP, hk]; exact ⟨2 * k ^ 2, by ring⟩
        exact (Nat.not_even_iff_odd.mpr hAodd) hAeven
      · exact hPo
    have hPsq8 : P ^ 2 % 8 = 1 := odd_sq_mod_eight P hPodd
    have hA8 : A % 8 = 3 := by
      rw [hA_def]
      have he8 : e ^ 2 % 8 = 1 := odd_sq_mod_eight e heo
      have hf8 : f ^ 2 % 8 = 1 := odd_sq_mod_eight f hfo
      omega
    rw [hP] at hA8
    omega
  · -- `g = 3`: extract `A = 3P²`, `B = 3Q²`, derive the AP identities, delegate the descent.
    have h3A : (3 : ℕ) ∣ A := by rw [← hg3]; exact hg_dvd_A
    have h3B : (3 : ℕ) ∣ B := by rw [← hg3]; exact hg_dvd_B
    obtain ⟨A', hA'⟩ := h3A
    obtain ⟨B', hB'⟩ := h3B
    have h3gcd : (3 : ℕ) * Nat.gcd A' B' = 3 := by
      rw [← Nat.gcd_mul_left, ← hA', ← hB']; exact hg3
    have hgcdA'B' : Nat.gcd A' B' = 1 := by omega
    have hWsq9 : W ^ 2 = 9 * (A' * B') := by rw [hW, hA', hB']; ring
    have hp3 : Nat.Prime 3 := by norm_num
    have h9dvdWsq : (9 : ℕ) ∣ W ^ 2 := ⟨A' * B', hWsq9⟩
    have h3dvdWsq : (3 : ℕ) ∣ W ^ 2 := dvd_trans (by norm_num : (3 : ℕ) ∣ 9) h9dvdWsq
    obtain ⟨W', hW'⟩ := hp3.dvd_of_dvd_pow h3dvdWsq
    have hWsq9' : (3 * W') ^ 2 = 9 * (A' * B') := by rw [← hW']; exact hWsq9
    have hexpand : (3 * W') ^ 2 = 9 * W' ^ 2 := by ring
    rw [hexpand] at hWsq9'
    have hW'sq : W' ^ 2 = A' * B' := by omega
    have hunitA'B' : IsUnit (gcd A' B') := by rw [gcd_eq_nat_gcd, hgcdA'B']; exact isUnit_one
    obtain ⟨P, hP'⟩ := exists_eq_pow_of_mul_eq_pow hunitA'B' hW'sq.symm
    have hgcdB'A' : Nat.gcd B' A' = 1 := by rw [Nat.gcd_comm]; exact hgcdA'B'
    have hunitB'A' : IsUnit (gcd B' A') := by rw [gcd_eq_nat_gcd, hgcdB'A']; exact isUnit_one
    have hW'sq' : B' * A' = W' ^ 2 := by rw [mul_comm]; exact hW'sq.symm
    obtain ⟨Q, hQ'⟩ := exists_eq_pow_of_mul_eq_pow hunitB'A' hW'sq'
    have hAeq : A = 3 * P ^ 2 := by rw [hA', hP']
    have hBeq : B = 3 * Q ^ 2 := by rw [hB', hQ']
    have hf_eq : f ^ 2 + Q ^ 2 = 2 * P ^ 2 := by
      have h1 := heq3f; rw [hAeq, hBeq] at h1; omega
    have he_eq : e ^ 2 + P ^ 2 = 2 * Q ^ 2 := by
      have h2 := heq3e; rw [hAeq, hBeq] at h2; omega
    exact concordant_forms_gcd3 e f P Q he hf hne hcop heo hfo he_eq hf_eq

/-- **Concordant-forms descent core.** For coprime `e ≠ f` (both positive), `(2f² + e²)(f² + 2e²)`
is never a perfect square. The parity reduction is certified here: both-even contradicts
coprimality, and each opposite-parity case forces the product `≡ 2 (mod 4)` — impossible for a
square. The surviving both-odd case is `concordant_forms_core_odd`. -/
theorem concordant_forms_core (e f W : ℕ) (he : 0 < e) (hf : 0 < f) (hne : e ≠ f)
    (hcop : Nat.Coprime e f) :
    W ^ 2 ≠ (2 * f ^ 2 + e ^ 2) * (f ^ 2 + 2 * e ^ 2) := by
  intro hW
  rcases Nat.even_or_odd e with hee | heo
  · rcases Nat.even_or_odd f with hfe | hfo
    · -- both even contradicts `gcd e f = 1`
      have hg : Nat.gcd e f = 1 := hcop
      have : (2 : ℕ) ∣ 1 := hg ▸ Nat.dvd_gcd hee.two_dvd hfe.two_dvd
      norm_num at this
    · -- `e` even, `f` odd ⟹ RHS ≡ 2 (mod 4)
      obtain ⟨a, rfl⟩ := hee
      obtain ⟨b, rfl⟩ := hfo
      have hfac : (2 * (2 * b + 1) ^ 2 + (a + a) ^ 2) * ((2 * b + 1) ^ 2 + 2 * (a + a) ^ 2)
          = 16 * ((2 * b ^ 2 + 2 * b + a ^ 2) * (b ^ 2 + b + 2 * a ^ 2))
            + 4 * (2 * b ^ 2 + 2 * b + a ^ 2) + 8 * (b ^ 2 + b + 2 * a ^ 2) + 2 := by ring
      rw [hfac] at hW
      rcases sq_mod_four W with h | h <;> omega
  · rcases Nat.even_or_odd f with hfe | hfo
    · -- `e` odd, `f` even ⟹ RHS ≡ 2 (mod 4)
      obtain ⟨a, rfl⟩ := heo
      obtain ⟨b, rfl⟩ := hfe
      have hfac : (2 * (b + b) ^ 2 + (2 * a + 1) ^ 2) * ((b + b) ^ 2 + 2 * (2 * a + 1) ^ 2)
          = 16 * ((2 * b ^ 2 + a ^ 2 + a) * (b ^ 2 + 2 * a ^ 2 + 2 * a))
            + 8 * (2 * b ^ 2 + a ^ 2 + a) + 4 * (b ^ 2 + 2 * a ^ 2 + 2 * a) + 2 := by ring
      rw [hfac] at hW
      rcases sq_mod_four W with h | h <;> omega
    · -- both odd: the genuine descent kernel
      exact concordant_forms_core_odd e f W he hf hne hcop heo hfo hW

/-- **sg7d (descent core).** The genuine descent contradiction: from `(f² - e²)² = 2n(n + 3d)`,
`2q = f⁴ - e⁴`, `e·f = d`, and `gcd(n,d) = 1`, derive `False`.

**Reduction (this pass, fully certified except the isolated kernel):** the whole statement
collapses to `concordant_forms_core`. Concretely:
* `e, f ≥ 1` and `e ≠ f` (else the bridge forces `2n(n+3d) = 0`, impossible for `n ≥ 1`);
* `gcd(e,f) = 1` — any `g ∣ e, f` gives `g² ∣ (f²-e²)² = 2n(n+3d)` while `g ∣ d` makes `g`
  coprime to both `n` and `n+3d`, so `g² ∣ 2`, i.e. `g = 1`;
* the algebra bridge `(2n + 3d)² = (2f² + e²)(f² + 2e²)` (a `linear_combination` of `hbridge`
  and `ef = d`), exhibiting `(2f²+e²)(f²+2e²)` as the perfect square `(2n+3d)²`;
* `concordant_forms_core` then rules that out. -/
theorem sg7d_descent_core (n d e f q : ℕ) (hn : 0 < n) (hd : 2 ≤ d) (hcop : Nat.Coprime n d)
    (hef : e * f = d) (_h2q : (2 * q : ℤ) = (f : ℤ) ^ 4 - (e : ℤ) ^ 4)
    (hbridge : ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) ^ 2 = 2 * (n : ℤ) * ((n : ℤ) + 3 * d)) : False := by
  -- `e, f ≥ 1`, else `d = e·f = 0` contradicts `d ≥ 2`.
  have hepos : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · rw [h, zero_mul] at hef; omega
    · exact h
  have hfpos : 0 < f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · rw [h, mul_zero] at hef; omega
    · exact h
  -- `e ≠ f`, else `(f²-e²)² = 0 = 2n(n+3d)` with `n ≥ 1`, `d ≥ 2`.
  have hne : e ≠ f := by
    intro hh
    have hzero : ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) = 0 := by rw [hh]; ring
    rw [hzero] at hbridge
    have hnpos : (0 : ℤ) < (n : ℤ) := by exact_mod_cast hn
    have hd0 : (0 : ℤ) < (d : ℤ) := by
      have : 0 < d := by omega
      exact_mod_cast this
    nlinarith [hbridge, hnpos, hd0,
      mul_pos hnpos (show (0 : ℤ) < (n : ℤ) + 3 * (d : ℤ) by linarith)]
  -- `gcd(e,f) = 1`.
  have hcop_ef : Nat.Coprime e f := by
    -- `g := gcd e f` divides `d = e·f`, and `g ∣ f²-e²` so `g² ∣ 2n(n+3d)`.
    have hgd : Nat.gcd e f ∣ d := hef ▸ (Nat.gcd_dvd_left e f).mul_right f
    have hgf2 : Nat.gcd e f ∣ f ^ 2 := (Nat.gcd_dvd_right e f).trans (dvd_pow_self f two_ne_zero)
    have hge2 : Nat.gcd e f ∣ e ^ 2 := (Nat.gcd_dvd_left e f).trans (dvd_pow_self e two_ne_zero)
    have hgD : ((Nat.gcd e f : ℤ)) ∣ ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) := by
      have h1 : ((Nat.gcd e f : ℤ)) ∣ ((f : ℤ) ^ 2) := by exact_mod_cast hgf2
      have h2 : ((Nat.gcd e f : ℤ)) ∣ ((e : ℤ) ^ 2) := by exact_mod_cast hge2
      exact dvd_sub h1 h2
    have hg2D : ((Nat.gcd e f : ℤ)) ^ 2 ∣ ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) ^ 2 :=
      pow_dvd_pow_of_dvd hgD 2
    rw [hbridge] at hg2D
    have hg2N : (Nat.gcd e f) ^ 2 ∣ 2 * n * (n + 3 * d) := by
      have hcast : (((Nat.gcd e f) ^ 2 : ℕ) : ℤ) ∣ ((2 * n * (n + 3 * d) : ℕ) : ℤ) := by
        push_cast; exact hg2D
      exact_mod_cast hcast
    -- `g` coprime to `n` and to `n + 3d`.
    have hcop_gn : Nat.Coprime (Nat.gcd e f) n := (hcop.coprime_dvd_right hgd).symm
    have hcop_gn3d : Nat.Coprime (Nat.gcd e f) (n + 3 * d) := by
      obtain ⟨k, hk⟩ := hgd.mul_left 3
      have hrw : n + 3 * d = n + k * Nat.gcd e f := by rw [mul_comm k, ← hk]
      rw [hrw]
      exact (Nat.coprime_add_mul_right_right (Nat.gcd e f) n k).mpr hcop_gn
    have hcop_g2 : Nat.Coprime ((Nat.gcd e f) ^ 2) (n * (n + 3 * d)) :=
      Nat.Coprime.pow_left 2 (hcop_gn.mul_right hcop_gn3d)
    -- Hence `g² ∣ 2`, forcing `g = 1`.
    have hdvd2 : (Nat.gcd e f) ^ 2 ∣ 2 := by
      have h2 : (Nat.gcd e f) ^ 2 ∣ 2 * (n * (n + 3 * d)) := by rw [← mul_assoc]; exact hg2N
      exact Nat.Coprime.dvd_of_dvd_mul_right hcop_g2 h2
    have hgdvd2 : Nat.gcd e f ∣ 2 := (dvd_pow_self (Nat.gcd e f) two_ne_zero).trans hdvd2
    have hle : Nat.gcd e f ≤ 2 := Nat.le_of_dvd (by norm_num) hgdvd2
    have hpos : 0 < Nat.gcd e f := by
      apply Nat.pos_of_ne_zero
      intro h; rw [Nat.gcd_eq_zero_iff] at h; omega
    rcases (by omega : Nat.gcd e f = 1 ∨ Nat.gcd e f = 2) with h | h
    · exact h
    · exfalso; rw [h] at hdvd2; norm_num at hdvd2
  -- The algebra bridge exhibits `(2f²+e²)(f²+2e²)` as the perfect square `(2n+3d)²`.
  have hefz : (e : ℤ) * (f : ℤ) = (d : ℤ) := by exact_mod_cast hef
  have hWsq : (2 * n + 3 * d) ^ 2 = (2 * f ^ 2 + e ^ 2) * (f ^ 2 + 2 * e ^ 2) := by
    have hZ : ((2 * n + 3 * d : ℕ) : ℤ) ^ 2
        = (((2 * f ^ 2 + e ^ 2) * (f ^ 2 + 2 * e ^ 2) : ℕ) : ℤ) := by
      push_cast
      linear_combination -2 * hbridge - 9 * ((d : ℤ) + (e : ℤ) * (f : ℤ)) * hefz
    exact_mod_cast hZ
  exact concordant_forms_core e f (2 * n + 3 * d) hepos hfpos hne hcop_ef hWsq

/-- Coprime factors of a perfect square: if `Coprime a b` and `a * b = c ^ 2`, then `a` is a
perfect square. (`ℕ` is a `GCDMonoid` with trivial units, so `exists_eq_pow_of_mul_eq_pow`
applies.) -/
private theorem isUnit_gcd_of_coprime {a b : ℕ} (h : Nat.Coprime a b) :
    IsUnit (GCDMonoid.gcd a b) := by
  rw [gcd_eq_nat_gcd]
  have hg : Nat.gcd a b = 1 := h
  rw [hg]; exact isUnit_one

private theorem sq_of_coprime_mul_left {a b c : ℕ} (h : Nat.Coprime a b)
    (habc : a * b = c ^ 2) : ∃ p, a = p ^ 2 :=
  exists_eq_pow_of_mul_eq_pow (isUnit_gcd_of_coprime h) habc

private theorem sq_of_coprime_mul_right {a b c : ℕ} (h : Nat.Coprime a b)
    (habc : a * b = c ^ 2) : ∃ p, b = p ^ 2 :=
  sq_of_coprime_mul_left h.symm (by rw [mul_comm]; exact habc)

/-- **sg7e (even-`d` branch).** The even companion of the odd-`d` descent, closed by the same
shared kernels (`no_four_squares_in_ap` / `concordant_forms_core`) — no new residual.

**Proof.** Because `Coprime x d` and `d` is even, `x` is odd, so `x - d²` and `x + d²` are both
odd. Their `gcd` divides `(x-d²)+(x+d²) = 2x` and `(x+d²)-(x-d²) = 2d²`, but being odd it in
fact divides `x` and `d²`, hence `gcd(x,d²) = 1`: **`x - d²` and `x + d²` are coprime**. Their
product is `x² - d⁴ = q²`, a perfect square, so each factor is a perfect square:
`n(n+3d) = x - d² = □` and `(n+d)(n+2d) = x + d² = □` (the two anchor identities). The middle
factor `(n+d)(n+2d)` has coprime terms (`gcd(n+d,n+2d) = gcd(n,d) = 1`), so `n+d = T₁²`,
`n+2d = T₂²`. Split on `3 ∣ n`:
* `3 ∤ n`: then `gcd(n,n+3d) = gcd(n,3) = 1`, so `n = u²` and `n+3d = v²` as well; the four AP
  terms `n, n+d, n+2d, n+3d` are all squares — four squares in a nonconstant AP, ruled out by
  `no_four_squares_in_ap`.
* `3 ∣ n`: write `n = 3n'`; then `n(n+3d) = 9·n'(n'+d)` a square forces `n'(n'+d) = □` with
  `Coprime n' (n'+d)`, so `n' = s₁²`, `n'+d = s₂²`. Substituting into `n+d = T₁²`, `n+2d = T₂²`
  gives the concordant-forms system `T₁² = 2s₁² + s₂²`, `T₂² = s₁² + 2s₂²`, i.e.
  `(2s₁²+s₂²)(s₁²+2s₂²) = (T₁T₂)²` — ruled out by `concordant_forms_core`.

No 2-adic power-stripping is needed: evenness of `d` enters only to make `x` (hence `x ± d²`)
odd, which is exactly what yields the coprime split. -/
theorem sg7e_even_branch (n d x q : ℕ) (hn : 0 < n) (hd : 2 ≤ d) (hcop : Nat.Coprime n d)
    (heven : Even d) (hx_def : x = n ^ 2 + 3 * n * d + d ^ 2) (hxq : q ^ 2 + d ^ 4 = x ^ 2)
    (hgcd_xd : Nat.Coprime x d) : False := by
  -- `x` is odd: `Coprime x d` with `2 ∣ d`.
  have hx_odd_mod : x % 2 = 1 := by
    rcases Nat.even_or_odd x with he | ho
    · exfalso
      have hg : Nat.gcd x d = 1 := hgcd_xd
      have : (2 : ℕ) ∣ 1 := hg ▸ Nat.dvd_gcd he.two_dvd heven.two_dvd
      omega
    · exact Nat.odd_iff.mp ho
  have hd2_even_mod : d ^ 2 % 2 = 0 := by
    have : Even (d ^ 2) := by rw [pow_two]; exact heven.mul_right d
    exact Nat.even_iff.mp this
  -- `d² < x`.
  have hd2_lt_x : d ^ 2 < x := by
    have hn2 : 0 < n ^ 2 := Nat.pos_of_ne_zero (pow_ne_zero 2 (by omega))
    rw [hx_def]; omega
  have hd2_le_x : d ^ 2 ≤ x := le_of_lt hd2_lt_x
  -- The two coprime factors `A = x - d² = n(n+3d)`, `B = x + d² = (n+d)(n+2d)`.
  set A := x - d ^ 2 with hA_def
  set B := x + d ^ 2 with hB_def
  have hApd : A + d ^ 2 = x := by omega
  have hAeq : A = n * (n + 3 * d) := by
    have hx2 : x = n * (n + 3 * d) + d ^ 2 := by rw [hx_def]; ring
    omega
  have hBeq : B = (n + d) * (n + 2 * d) := by rw [hB_def, hx_def]; ring
  -- `A * B = q²`.
  have hAB : A * B = q ^ 2 := by
    have hP : n * (n + 3 * d) * ((n + d) * (n + 2 * d)) + d ^ 4 = x ^ 2 := by rw [hx_def]; ring
    have hval : A * B = n * (n + 3 * d) * ((n + d) * (n + 2 * d)) := by rw [hAeq, hBeq]
    omega
  -- `A`, `B` are both odd.
  have hA_odd_mod : A % 2 = 1 := by omega
  have hB_odd_mod : B % 2 = 1 := by omega
  -- `Coprime A B`.
  have hcopAB : Nat.Coprime A B := by
    have hgA : Nat.gcd A B ∣ A := Nat.gcd_dvd_left A B
    have hgB : Nat.gcd A B ∣ B := Nat.gcd_dvd_right A B
    have hsum : A + B = 2 * x := by omega
    have hg2x : Nat.gcd A B ∣ 2 * x := by rw [← hsum]; exact dvd_add hgA hgB
    have hdiff : B - A = 2 * d ^ 2 := by omega
    have hg2d2 : Nat.gcd A B ∣ 2 * d ^ 2 := by rw [← hdiff]; exact Nat.dvd_sub hgB hgA
    have hg_cop2 : Nat.Coprime (Nat.gcd A B) 2 := by
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
      intro h2g
      have : 2 ∣ A := h2g.trans hgA
      omega
    have hgx : Nat.gcd A B ∣ x := hg_cop2.dvd_of_dvd_mul_left hg2x
    have hgd2 : Nat.gcd A B ∣ d ^ 2 := hg_cop2.dvd_of_dvd_mul_left hg2d2
    have hxd2_one : Nat.gcd x (d ^ 2) = 1 := hgcd_xd.pow_right 2
    have hg_dvd : Nat.gcd A B ∣ Nat.gcd x (d ^ 2) := Nat.dvd_gcd hgx hgd2
    rw [hxd2_one] at hg_dvd
    exact Nat.dvd_one.mp hg_dvd
  -- Extract `A = P²`, `B = R²`.
  obtain ⟨P, hP⟩ := sq_of_coprime_mul_left hcopAB hAB
  obtain ⟨R, hR⟩ := sq_of_coprime_mul_right hcopAB hAB
  -- Split `B = (n+d)(n+2d) = R²` into two squares.
  have hcop_ndd : Nat.Coprime (n + d) (n + 2 * d) := by
    have e1 : n + 2 * d = (n + d) + d := by ring
    rw [e1, Nat.coprime_self_add_right]
    exact Nat.coprime_add_self_left.mpr hcop
  have hBsq_split : (n + d) * (n + 2 * d) = R ^ 2 := by rw [← hBeq]; exact hR
  obtain ⟨T1, hT1⟩ := sq_of_coprime_mul_left hcop_ndd hBsq_split
  obtain ⟨T2, hT2⟩ := sq_of_coprime_mul_right hcop_ndd hBsq_split
  -- Split on `3 ∣ n`.
  by_cases h3n : 3 ∣ n
  · -- `3 ∣ n`: concordant-forms contradiction.
    obtain ⟨n', hn'⟩ := h3n
    have hn'_pos : 0 < n' := by omega
    have hn'_dvd : n' ∣ n := ⟨3, by rw [hn']; ring⟩
    have hcop_n'd : Nat.Coprime n' d := Nat.Coprime.coprime_dvd_left hn'_dvd hcop
    have hcop_n'n'd : Nat.Coprime n' (n' + d) := Nat.coprime_self_add_right.mpr hcop_n'd
    -- `n(n+3d) = 9·n'(n'+d) = P²` ⟹ `n'(n'+d) = P'²`.
    have hA9 : A = 9 * (n' * (n' + d)) := by rw [hAeq, hn']; ring
    have hP9 : P ^ 2 = 9 * (n' * (n' + d)) := by rw [← hP]; exact hA9
    have h3P2 : 3 ∣ P ^ 2 := ⟨3 * (n' * (n' + d)), by rw [hP9]; ring⟩
    obtain ⟨P', hP'⟩ := Nat.prime_three.dvd_of_dvd_pow h3P2
    have hP'sq : n' * (n' + d) = P' ^ 2 := by
      have h := hP9
      rw [hP'] at h
      have h2 : 9 * P' ^ 2 = 9 * (n' * (n' + d)) := by rw [← h]; ring
      omega
    obtain ⟨s1, hs1⟩ := sq_of_coprime_mul_left hcop_n'n'd hP'sq
    obtain ⟨s2, hs2⟩ := sq_of_coprime_mul_right hcop_n'n'd hP'sq
    -- The concordant system `T₁² = 2s₁² + s₂²`, `T₂² = s₁² + 2s₂²`.
    have hT1eq : T1 ^ 2 = 2 * s1 ^ 2 + s2 ^ 2 := by omega
    have hT2eq : T2 ^ 2 = s1 ^ 2 + 2 * s2 ^ 2 := by omega
    have hs1_pos : 0 < s1 := by
      have h2 : 0 < s1 ^ 2 := hs1 ▸ hn'_pos
      exact Nat.pos_of_ne_zero (fun h => by simp [h] at h2)
    have hs2_pos : 0 < s2 := by
      have h2 : 0 < s2 ^ 2 := by rw [← hs2]; omega
      exact Nat.pos_of_ne_zero (fun h => by simp [h] at h2)
    have hs_ne : s2 ≠ s1 := by
      intro h; rw [h] at hs2; omega
    have hcop_s : Nat.Coprime s2 s1 := by
      have hc : Nat.Coprime (s1 ^ 2) (s2 ^ 2) := by rw [← hs1, ← hs2]; exact hcop_n'n'd
      have h1 : Nat.Coprime s1 (s2 ^ 2) :=
        Nat.Coprime.coprime_dvd_left (dvd_pow_self s1 (by norm_num)) hc
      exact (Nat.Coprime.coprime_dvd_right (dvd_pow_self s2 (by norm_num)) h1).symm
    have hprod_sq : (T1 * T2) ^ 2 = (2 * s1 ^ 2 + s2 ^ 2) * (s1 ^ 2 + 2 * s2 ^ 2) := by
      rw [mul_pow, hT1eq, hT2eq]
    exact absurd hprod_sq (concordant_forms_core s2 s1 (T1 * T2) hs2_pos hs1_pos hs_ne hcop_s)
  · -- `3 ∤ n`: the four AP terms are all squares.
    have hcop_n3 : Nat.Coprime n 3 :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3n).symm
    have hcop_n3d : Nat.Coprime n (3 * d) := hcop_n3.mul_right hcop
    have hcop_n_n3d : Nat.Coprime n (n + 3 * d) := Nat.coprime_self_add_right.mpr hcop_n3d
    have hAsq : n * (n + 3 * d) = P ^ 2 := by rw [← hAeq]; exact hP
    obtain ⟨u, hu⟩ := sq_of_coprime_mul_left hcop_n_n3d hAsq
    obtain ⟨v, hv⟩ := sq_of_coprime_mul_right hcop_n_n3d hAsq
    -- `n = u²`, `n+d = T₁²`, `n+2d = T₂²`, `n+3d = v²`: four squares in AP, step `d ≠ 0`.
    have zu : (u : ℤ) ^ 2 = (n : ℤ) := by exact_mod_cast hu.symm
    have zT1 : (T1 : ℤ) ^ 2 = (n : ℤ) + (d : ℤ) := by exact_mod_cast hT1.symm
    have zT2 : (T2 : ℤ) ^ 2 = (n : ℤ) + 2 * (d : ℤ) := by exact_mod_cast hT2.symm
    have zv : (v : ℤ) ^ 2 = (n : ℤ) + 3 * (d : ℤ) := by exact_mod_cast hv.symm
    refine no_four_squares_in_ap (u : ℤ) (T1 : ℤ) (T2 : ℤ) (v : ℤ) (d : ℤ) ?_ ?_ ?_ ?_
    · exact Nat.cast_ne_zero.mpr (by omega)
    · linear_combination zT1 - zu
    · linear_combination zT2 - zT1
    · linear_combination zv - zT2

/-- **Euler's theorem, `d ≥ 2` case** — the genuine number-theoretic crux (infinite descent).
Isolated as its own lemma so it can be attacked/escalated independently of the `d = 1` case.

The reduction is fully proved (no `sorry` in this lemma or its two branch lemmas
`sg7d_descent_core` / `sg7e_even_branch`); both branches bottom out at the single shared kernel
`no_four_squares_in_ap`:
* `x := n² + 3nd + d²` satisfies `P + d⁴ = x²` (the anchor identity, `ring`).
* Assuming `P = q²` gives `q² + d⁴ = x²`, i.e. `(x-q)(x+q) = d⁴` in `ℤ`.
* `gcd(n,d) = 1 ⟹ gcd(x,d) = 1` (since `x ≡ n² (mod d)`), and hence `gcd(x,q) = 1`
  (`coprime_of_sq_sub_sq_eq_pow4`).
* Set `a := x - q, b := x + q`. Then `1 ≤ a ≤ d² - 1` (sg5, from the sandwich
  `(x-d²)² < P < x²`) and `Int.gcd a b ∣ 2` (sg7a).
* On `d` odd: `a, b` are odd (their product `d⁴` is odd), so `Int.gcd a b` is an odd divisor
  of `2`, i.e. `= 1`; coprimality + `a*b = d⁴` + `a,b > 0` gives `a = e⁴, b = f⁴, e*f = d`
  (`exists_associated_pow_of_mul_eq_pow`), and the algebra bridge (sg7c) turns this into
  `(f²-e²)² = 2n(n+3d)`, feeding the descent core `sg7d_descent_core` → `concordant_forms_core`.
* On `d` even: `x` is odd, so `x ± d²` are coprime odd squares, giving a 4-term AP of squares
  (`no_four_squares_in_ap`) or a concordant system (`concordant_forms_core`) via
  `sg7e_even_branch`.

This matches the classical multi-step proof (Beeger 1917 / Mordell, *Diophantine Equations*
ch. 4, cf. `not_fermat_42` in `Mathlib.NumberTheory.FLT.Four` for the same order of
difficulty). The whole file is `sorry`-free: `no_four_squares_in_ap` is fully proved, its Fermat
descent core `four_squares_ap_descent_step_primitive` closed from scratch. -/
theorem ap4_prod_ne_sq_d_ge_two (n d q : ℕ) (hn : 0 < n) (hd : 2 ≤ d) (hcop : n.gcd d = 1) :
    n * (n + d) * (n + 2 * d) * (n + 3 * d) ≠ q ^ 2 := by
  intro heq
  set x := n ^ 2 + 3 * n * d + d ^ 2 with hx_def
  have hkey : n * (n + d) * (n + 2 * d) * (n + 3 * d) + d ^ 4 = x ^ 2 := by
    rw [hx_def]; ring
  have hxq : q ^ 2 + d ^ 4 = x ^ 2 := by rw [← heq]; exact hkey
  -- `gcd(x, d) = 1`: `x = n² + (3n+d)*d`, so `x ≡ n² (mod d)` and `gcd(n,d) = 1`.
  have hx_eq : x = n ^ 2 + (3 * n + d) * d := by rw [hx_def]; ring
  have hcop_n2 : Nat.Coprime (n ^ 2) d := Nat.Coprime.pow_left 2 hcop
  have hgcd_xd : Nat.Coprime x d := by
    rw [hx_eq]
    exact (Nat.coprime_add_mul_right_left (n ^ 2) d (3 * n + d)).mpr hcop_n2
  -- Difference of squares over `ℤ`: `(x - q) * (x + q) = d ^ 4`.
  have hint : (x : ℤ) ^ 2 - (q : ℤ) ^ 2 = (d : ℤ) ^ 4 := by
    have := hxq
    zify at this
    linarith
  have hfactor : ((x : ℤ) - q) * ((x : ℤ) + q) = (d : ℤ) ^ 4 := by nlinarith [hint]
  -- `P > 0`, hence `q > 0`.
  have hP_pos : 0 < n * (n + d) * (n + 2 * d) * (n + 3 * d) := by positivity
  have hq_pos : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h0 | h0
    · rw [h0] at heq; simp at heq; omega
    · exact h0
  -- `q < x`.
  have hd4_ge : (16 : ℕ) ≤ d ^ 4 := by
    calc (16 : ℕ) = 2 ^ 4 := by norm_num
    _ ≤ d ^ 4 := Nat.pow_le_pow_left hd 4
  have hqx : q < x := by
    have hq2x2 : q ^ 2 < x ^ 2 := by omega
    by_contra h
    have hle : x ≤ q := by omega
    have : x ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hle 2
    omega
  -- `d² < x`.
  have hd2_lt_x : d ^ 2 < x := by rw [hx_def]; nlinarith
  -- `x - d² < q` (the sandwich `(x-d²)² < P < x²`, via `(q+d²)² ≤ x²` contradiction).
  have hlow : x - d ^ 2 < q := by
    by_contra hcon
    have hle : q + d ^ 2 ≤ x := by omega
    have hsq : (q + d ^ 2) ^ 2 ≤ x ^ 2 := Nat.pow_le_pow_left hle 2
    nlinarith [hxq, hsq, hq_pos, hd]
  -- `gcd(x,q) = 1`.
  have hcop_xq : Nat.Coprime x q := coprime_of_sq_sub_sq_eq_pow4 x q d hxq hgcd_xd
  -- Move to `a := x - q, b := x + q` in `ℤ`.
  set az : ℤ := (x : ℤ) - (q : ℤ) with haz_def
  set bz : ℤ := (x : ℤ) + (q : ℤ) with hbz_def
  have hab : az * bz = (d : ℤ) ^ 4 := hfactor
  -- sg5 : `1 ≤ a ≤ d² - 1`.
  have hcast_hqx : (q : ℤ) < (x : ℤ) := by exact_mod_cast hqx
  have haz_ge1 : 1 ≤ az := by rw [haz_def]; omega
  have hcast_hlow : (x : ℤ) - (d : ℤ) ^ 2 < (q : ℤ) := by
    have hle' : d ^ 2 ≤ x := le_of_lt hd2_lt_x
    zify [hle'] at hlow
    linarith
  have haz_le : az ≤ (d : ℤ) ^ 2 - 1 := by rw [haz_def]; omega
  -- sg7a : `gcd(a,b) ∣ 2`.
  have hcop_xq_z : Int.gcd (x : ℤ) (q : ℤ) = 1 := by
    rw [Int.gcd_natCast_natCast]; exact hcop_xq
  have hgcd_ab : Int.gcd az bz ∣ 2 := by
    rw [haz_def, hbz_def]
    exact gcd_sub_add_dvd_two_of_coprime (x : ℤ) (q : ℤ) hcop_xq_z
  -- Positivity of `a, b`.
  have haz_pos : 0 < az := by linarith
  have hbz_pos : 0 < bz := by
    have : (0 : ℤ) ≤ (x : ℤ) := Int.natCast_nonneg x
    have hqz_pos : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hq_pos
    rw [hbz_def]; linarith
  -- Split on the parity of `d`.
  rcases Nat.even_or_odd d with hde | hdo
  · exact sg7e_even_branch n d x q hn hd hcop hde hx_def hxq hgcd_xd
  · -- `d` odd: `a, b` odd, so `gcd(a,b)` is an odd divisor of `2`, i.e. `1`.
    have hd4odd : Odd ((d : ℤ) ^ 4) := by
      have : Odd (d : ℤ) := by exact_mod_cast hdo
      exact this.pow
    have habodd : Odd (az * bz) := hab ▸ hd4odd
    have haz_odd : Odd az := (Int.odd_mul.mp habodd).1
    have hgcd_eq_one : Int.gcd az bz = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hgcd_ab with h1 | h2
      · exact h1
      · exfalso
        have hdvd2 : (2 : ℤ) ∣ az := by
          have := Int.gcd_dvd_left az bz
          rw [h2] at this
          exact_mod_cast this
        exact (Int.not_even_iff_odd.mpr haz_odd) (even_iff_two_dvd.mpr hdvd2)
    -- sg7b : `a = e⁴, b = f⁴, e*f = d`.
    obtain ⟨e, f, hae, hbf, hefd⟩ := sg7b_odd_branch d az bz hab hgcd_eq_one haz_pos hbz_pos
    -- sg7c : the algebra bridge `(f²-e²)² = 2n(n+3d)`.
    have hxc : (x : ℤ) = (n : ℤ) ^ 2 + 3 * n * d + d ^ 2 := by rw [hx_def]; push_cast; ring
    have hsum : (e : ℤ) ^ 4 + (f : ℤ) ^ 4 = 2 * ((n : ℤ) ^ 2 + 3 * n * d + d ^ 2) := by
      have hstep : (e : ℤ) ^ 4 + (f : ℤ) ^ 4 = 2 * (x : ℤ) := by
        rw [← hae, ← hbf, haz_def, hbz_def]; ring
      rw [hstep, hxc]
    have hbridge : ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) ^ 2 = 2 * (n : ℤ) * ((n : ℤ) + 3 * d) :=
      sg7c_bridge n d e f hefd hsum
    have h2q : (2 * (q : ℤ)) = (f : ℤ) ^ 4 - (e : ℤ) ^ 4 := by
      rw [← hbf, ← hae, hbz_def, haz_def]; ring
    exact sg7d_descent_core n d e f q hn hd hcop hefd h2q hbridge

/-- **Euler's theorem.** The product of a 4-term arithmetic progression of positive integers
with coprime common difference is never a perfect square. -/
theorem ap4_prod_ne_sq (n d q : ℕ) (hn : 0 < n) (hd : 0 < d) (hcop : n.gcd d = 1) :
    n * (n + d) * (n + 2 * d) * (n + 3 * d) ≠ q ^ 2 := by
  rcases Nat.lt_or_ge d 2 with h1 | h2
  · have hd1 : d = 1 := by omega
    subst hd1
    simpa using ap4_prod_ne_sq_d_eq_one n q hn
  · exact ap4_prod_ne_sq_d_ge_two n d q hn h2 hcop

end MathProof.Challenges.C0040Erdos672EulerFourTermAPProductNotSquare
