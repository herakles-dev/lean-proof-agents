import MathProof.Basic

/-!
# Challenge C0043 — Fermat's "no four squares in arithmetic progression" (1640)

**Status:** ✅ SOLVED — `sorry`-free, clean axioms
(`#print axioms no_four_squares_in_ap` = `[propext, Classical.choice, Quot.sound]`; verify with
`scripts/check-proof.sh C0043FermatRightTriangleTheorem --all`).

## What this module proves

`no_four_squares_in_ap` : **four perfect squares can never form a nonconstant arithmetic
progression** — Fermat's theorem of 1640, equivalent to his right-triangle theorem (no Pythagorean
triangle has square area) and to the congruent-number-1 obstruction.

This is a **genuine Mathlib gap**: Mathlib (checked) exposes *no* four-squares-in-AP theorem, *no*
`x⁴ − y⁴ ≠ z²` (Fermat right-triangle) theorem, and *no* congruent-number theorem. The only nearby
result is `not_fermat_42` (`a⁴ + b⁴ ≠ c²`, `Mathlib/NumberTheory/FLT/Four.lean`), which is the
*parallel* `+`-descent — not reachable from this one by a short algebraic identity. Hence this is a
Mathlib-PR candidate (headline lemma + the Euler concordant-`(1,4)` descent engine).

## Provenance & scope

The proof is the self-contained descent chain extracted verbatim from C0040 (Erdős #672 / Euler),
where it was developed and adversarially audited. Extraction is a pure lift of the transitive
closure of `no_four_squares_in_ap` (17 declarations) — all Erdős-specific machinery
(`ap4_prod_ne_sq*`, `sg7*`, `concordant_forms_*`) is intentionally dropped so the module is a
minimal, upstream-portable unit.

## Deferred (follow-up challenge)

The explicit right-triangle form `x⁴ − y⁴ ≠ z²` is **equivalent** but not a `ring`-identity
corollary of the above: a solution yields only *three* squares in AP (the Pythagorean triple
`(y², z, x²)`); producing the fourth is itself a Fermat descent step. So `x⁴ − y⁴ ≠ z²` needs its
own descent and is scoped as a separate challenge, not forced onto this one.

## Proof architecture (bottom-up)

* `eq_zero_of_sq_eq_two_mul_sq` — `a² = 2b² → b = 0` (√2 descent), rules out a zero smallest root.
* `fsap_*` — the primitive **Euler concordant-`(1,4)`** descent: two equal-area Pythagorean
  triangles → four-number factorisation `P·Q = P'·Q'` → concordant pair `X²+Y²=□ ∧ X²+4Y²=□` →
  infinite descent on `|X|·|Y|` (residual cofactor `k ∣ 3` killed mod 3).
* `four_squares_ap_descent` — strong induction on `u.natAbs` via the descent step
  (non-primitive gcd-reduction + primitive core).
* `no_four_squares_in_ap` — sign trichotomy on `D`, pass to `|·|`, rule out a zero root.
-/

namespace MathProof.Challenges.C0043FermatRightTriangleTheorem

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

/-- **Headline (AP form).** Four perfect squares `a², b², c², d²` cannot form a nonconstant
arithmetic progression: if the consecutive gaps are equal (`b²-a² = c²-b² = d²-c²`) and the
progression is nonconstant (`a² ≠ b²`), we get a contradiction. This is the clean user-facing
statement of `no_four_squares_in_ap`. -/
theorem four_squares_not_in_ap (a b c d : ℤ)
    (hab : b ^ 2 - a ^ 2 = c ^ 2 - b ^ 2) (hbc : c ^ 2 - b ^ 2 = d ^ 2 - c ^ 2)
    (hne : a ^ 2 ≠ b ^ 2) : False := by
  refine no_four_squares_in_ap a b c d (b ^ 2 - a ^ 2) ?_ ?_ ?_ ?_
  · intro h; exact hne (by linarith)
  · ring
  · linarith
  · linarith

end MathProof.Challenges.C0043FermatRightTriangleTheorem
