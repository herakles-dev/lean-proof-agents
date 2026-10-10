import MathProof.Basic

/-!
# MathProof.Certify.Reflect — verified checkers by reflection (Certify v2)

Part of `MathProof.Certify` (the witness→Lean-certificate "moat"). Where v1 (`Certify.Sup` etc.)
bridges a *decided* `Finset` scan to an `iSup`/`Set` fact, v2 replaces the scan itself by a
**Bool program over `Nat`** plus a **soundness theorem** — proof by reflection. `decide +kernel`
then evaluates the checker with GMP-accelerated `Nat` arithmetic instead of unfolding
`Finset`/`Multiset`, raising the kernel-certified range by ~50× for Erdős #647 (v2 certifies the
sweep out to N=3000, where the v1 `Finset` scan had already become intractable). See
`MathProof/Challenges/C0044Erdos647ReflectedSweep.lean` for the #647 certification run.

**Never `native_decide`. Never widen `TRUSTED_AXIOMS`.** Every theorem here must depend only on
`[propext, Classical.choice, Quot.sound]`; the checker is only as trustworthy as the kernel proof
of its soundness lemma.

**Kernel-reduction discipline:** `tauSqrtAux`/`sweepS` are written with *structural* recursion
(`| 0 | (k+1)`) so they compile to `brecOn`, which `decide +kernel` reduces. Do NOT rewrite them
with well-founded recursion / `termination_by` on `n` — the kernel gets stuck on the accessibility
proof.
-/

set_option autoImplicit false

open ArithmeticFunction ArithmeticFunction.sigma

namespace MathProof.Certify.Reflect

/-- Trial-division divisor counter (auxiliary). Sums over `d ∈ [1, bound]`, counting each `d ∣ n`
with weight `2` for a strict pair `d < n/d` and weight `1` when `d*d = n`. Called with
`bound = Nat.sqrt n`, `tauSqrtAux n (Nat.sqrt n)` counts every divisor exactly once via the
`d ↦ n/d` pairing. Structural on `bound` (→ `brecOn`, kernel-reducible). -/
def tauSqrtAux (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | (d + 1) =>
      (if n % (d + 1) == 0 then (if (d + 1) * (d + 1) == n then 1 else 2) else 0)
        + tauSqrtAux n d

/-- Fast divisor count `τ(n)` = number of divisors of `n`, by trial division up to `√n`. -/
def tauS (n : ℕ) : ℕ := tauSqrtAux n (Nat.sqrt n)

/-- Kernel-friendly Bool prefix-max sweep for Erdős #647 over indices `[i, i + s)`:
`pm` is the running maximum of `m + tauS m` for `m < i`; for each index `i ≥ 25` it asserts
`i + 2 < pm` (⟺ `∃ m < i, i + 2 < m + τ(m)`, i.e. `i` is not a #647 witness). Structural on the
fuel `s` (→ `brecOn`, kernel-reducible). Invoke as `sweepS 0 0 N` to cover `[0, N)`. -/
def sweepS (i pm : ℕ) : ℕ → Bool
  | 0 => true
  | (s + 1) =>
      (if 25 ≤ i then decide (i + 2 < pm) else true) && sweepS (i + 1) (max pm (i + tauS i)) s

/-- **CRUX (sg1).** The trial-division counter equals Mathlib's `σ 0` (the number of divisors).
Proof: `sigma_zero_apply` reduces `σ 0 n` to `n.divisors.card`; an induction helper rewrites
`tauSqrtAux n (√n)` as the indicator sum `∑_{d ∈ Icc 1 √n} (2·[d²<n] + [d²=n])` (the `b ≤ √n` bound
forces `d² ≤ n`); `Nat.le_sqrt` bridges the `Icc`-filters to genuine divisor-filters; then the
`d ↦ n/d` involution card-split of `n.divisors` by `d*d < n / = n / > n` matches those weights. -/
theorem tauS_eq (n : ℕ) : tauS n = σ 0 n := by
  rw [sigma_zero_apply]
  -- Step 1: counting helper for the auxiliary trial-division sum. For `b ≤ √n` every `d ≤ b`
  -- has `d*d ≤ n`, so `tauSqrtAux n b` weights each divisor `d` by `2` when `d*d < n` and `1`
  -- when `d*d = n` — expressed here as a sum of indicators over `Icc 1 b`.
  have haux : ∀ b, b ≤ n.sqrt →
      tauSqrtAux n b
        = ∑ d ∈ Finset.Icc 1 b,
            (2 * (if d ∣ n ∧ d * d < n then 1 else 0)
              + (if d ∣ n ∧ d * d = n then 1 else 0)) := by
    intro b
    induction b with
    | zero => intro _; simp [tauSqrtAux]
    | succ k ih =>
        intro hk
        have hk' : k ≤ n.sqrt := Nat.le_of_succ_le hk
        have hle : (k + 1) * (k + 1) ≤ n := Nat.le_sqrt.mp hk
        have hw : (if n % (k + 1) == 0 then (if (k + 1) * (k + 1) == n then (1:ℕ) else 2) else 0)
            = 2 * (if (k + 1) ∣ n ∧ (k + 1) * (k + 1) < n then 1 else 0)
              + (if (k + 1) ∣ n ∧ (k + 1) * (k + 1) = n then 1 else 0) := by
          by_cases hd : (k + 1) ∣ n
          · have hmod : n % (k + 1) = 0 := Nat.dvd_iff_mod_eq_zero.mp hd
            by_cases he : (k + 1) * (k + 1) = n
            · simp [hmod, he, hd]
            · have hlt : (k + 1) * (k + 1) < n := lt_of_le_of_ne hle he
              simp [hmod, he, hlt, hd]
          · have hmod : n % (k + 1) ≠ 0 := fun h => hd (Nat.dvd_iff_mod_eq_zero.mpr h)
            simp [hmod, hd]
        rw [Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ k + 1), ← ih hk']
        simp only [tauSqrtAux]
        rw [hw]; ring
  -- instantiate at `b = √n` and rewrite the indicator sum as two filter cardinalities
  rw [tauS, haux n.sqrt (le_refl _), Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.card_filter, ← Finset.card_filter]
  -- bridge `Icc 1 √n`-filters to genuine divisor-filters (`d ≤ √n ↔ d*d ≤ n`)
  have hA : (Finset.Icc 1 n.sqrt).filter (fun d => d ∣ n ∧ d * d < n)
      = n.divisors.filter (fun d => d * d < n) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨_, _⟩, hdvd, hlt⟩; exact ⟨⟨hdvd, by omega⟩, hlt⟩
    · rintro ⟨⟨hdvd, hn0⟩, hlt⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hdvd (Nat.pos_of_ne_zero hn0),
        Nat.le_sqrt.mpr (le_of_lt hlt)⟩, hdvd, hlt⟩
  have hB : (Finset.Icc 1 n.sqrt).filter (fun d => d ∣ n ∧ d * d = n)
      = n.divisors.filter (fun d => d * d = n) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨h1, _⟩, hdvd, heq⟩
      refine ⟨⟨hdvd, ?_⟩, heq⟩
      rintro rfl; rw [Nat.mul_eq_zero] at heq; omega
    · rintro ⟨⟨hdvd, hn0⟩, heq⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hdvd (Nat.pos_of_ne_zero hn0),
        Nat.le_sqrt.mpr (le_of_eq heq)⟩, hdvd, heq⟩
  rw [hA, hB]
  -- Step 3: partition `n.divisors` by `d*d {<,=,>} n`; the `d ↦ n/d` involution pairs `<` with `>`.
  have hpart1 : (n.divisors.filter (fun d => d * d < n)).card
      + (n.divisors.filter (fun d => ¬ d * d < n)).card = n.divisors.card :=
    Finset.card_filter_add_card_filter_not (s := n.divisors) (fun d => d * d < n)
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := n.divisors.filter (fun d => ¬ d * d < n)) (fun d => d * d = n)
  have e1 : (n.divisors.filter (fun d => ¬ d * d < n)).filter (fun d => d * d = n)
      = n.divisors.filter (fun d => d * d = n) := by
    rw [Finset.filter_filter]; exact Finset.filter_congr (fun x _ => by omega)
  have e2 : (n.divisors.filter (fun d => ¬ d * d < n)).filter (fun d => ¬ d * d = n)
      = n.divisors.filter (fun d => n < d * d) := by
    rw [Finset.filter_filter]; exact Finset.filter_congr (fun x _ => by omega)
  rw [e1, e2] at hsplit
  -- the `d ↦ n/d` involution: `#{d : d*d < n} = #{d : n < d*d}`
  have hbij : (n.divisors.filter (fun d => d * d < n)).card
      = (n.divisors.filter (fun d => n < d * d)).card := by
    apply Finset.card_bij' (fun d _ => n / d) (fun d _ => n / d)
    · intro d hd
      simp only [Finset.mem_filter, Nat.mem_divisors] at hd ⊢
      obtain ⟨⟨hdvd, hn0⟩, hlt⟩ := hd
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd (Nat.pos_of_ne_zero hn0)
      have hdle : d ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdvd
      have hq : n = d * (n / d) := (Nat.mul_div_cancel' hdvd).symm
      have hqpos : 0 < n / d := Nat.div_pos hdle hdpos
      have hd_lt : d < n / d := Nat.lt_of_mul_lt_mul_left (by rw [← hq]; exact hlt)
      refine ⟨⟨Nat.div_dvd_of_dvd hdvd, hn0⟩, ?_⟩
      calc n = d * (n / d) := hq
        _ < (n / d) * (n / d) := (Nat.mul_lt_mul_right hqpos).mpr hd_lt
    · intro d hd
      simp only [Finset.mem_filter, Nat.mem_divisors] at hd ⊢
      obtain ⟨⟨hdvd, hn0⟩, hgt⟩ := hd
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd (Nat.pos_of_ne_zero hn0)
      have hdle : d ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdvd
      have hq : n = d * (n / d) := (Nat.mul_div_cancel' hdvd).symm
      have hqpos : 0 < n / d := Nat.div_pos hdle hdpos
      have hlt_d : n / d < d := Nat.lt_of_mul_lt_mul_left (by rw [← hq]; exact hgt)
      refine ⟨⟨Nat.div_dvd_of_dvd hdvd, hn0⟩, ?_⟩
      calc (n / d) * (n / d) < d * (n / d) := (Nat.mul_lt_mul_right hqpos).mpr hlt_d
        _ = n := hq.symm
    · intro d hd
      simp only [Finset.mem_filter, Nat.mem_divisors] at hd
      exact Nat.div_div_self hd.1.1 hd.1.2
    · intro d hd
      simp only [Finset.mem_filter, Nat.mem_divisors] at hd
      exact Nat.div_div_self hd.1.1 hd.1.2
  omega

/-- Prefix-max accumulator matching the `pm` argument threaded through `sweepS`:
`pmax i = max_{m < i} (m + tauS m)`, with `pmax 0 = 0` as the (unused) base case. Structural on `i`
so it unfolds the same way `sweepS`/`tauSqrtAux` do. -/
private def pmax : ℕ → ℕ
  | 0 => 0
  | (i + 1) => max (pmax i) (i + tauS i)

/-- Every prefix max (for `i > 0`) is achieved by some earlier index `m < i`. -/
private lemma exists_achieves_pmax : ∀ i, 0 < i → ∃ m ∈ Finset.range i, pmax i ≤ m + tauS m := by
  intro i
  induction i with
  | zero => intro h; exact absurd h (lt_irrefl 0)
  | succ k ih =>
      intro _
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · subst hk0
        exact ⟨0, Finset.mem_range.mpr Nat.one_pos, by simp only [pmax]; omega⟩
      · obtain ⟨m, hm, hle⟩ := ih hkpos
        rcases le_total (pmax k) (k + tauS k) with hcmp | hcmp
        · exact ⟨k, Finset.mem_range.mpr (Nat.lt_succ_self k), by simp only [pmax]; omega⟩
        · exact ⟨m, Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp hm)),
            by simp only [pmax]; omega⟩

/-- The invariant driving the fuel recursion of `sweepS`: if `pm` is the true prefix max at `i`
and the sweep from `i` with fuel `s` returns `true`, then every checked index `n ∈ [i, i+s)` with
`25 ≤ n` really has `n + 2 < pmax n` (i.e. is not a #647 witness). -/
private lemma sweepS_gen : ∀ s i pm, pm = pmax i → sweepS i pm s = true →
    ∀ n, i ≤ n → n < i + s → 25 ≤ n → n + 2 < pmax n := by
  intro s
  induction s with
  | zero =>
      intro i pm hpm h n hin hlt h25
      omega
  | succ s ih =>
      intro i pm hpm h n hin hlt h25
      simp only [sweepS, Bool.and_eq_true] at h
      obtain ⟨hcheck, htail⟩ := h
      by_cases heq : i = n
      · have hi25 : 25 ≤ i := by omega
        rw [if_pos hi25] at hcheck
        have hlt2 : i + 2 < pm := of_decide_eq_true hcheck
        rw [hpm] at hlt2
        rw [heq] at hlt2
        exact hlt2
      · have hpm' : max pm (i + tauS i) = pmax (i + 1) := by simp only [hpm, pmax]
        exact ih (i + 1) (max pm (i + tauS i)) hpm' htail n (by omega) (by omega) h25

/-- **Soundness (sg2).** A `true` sweep certifies the Erdős #647 no-witness fact over `[25, N)`:
every `n` in that window has some `m < n` with `n + 2 < m + σ 0 m`. Proof: generalize the fuel
recursion with the invariant `pm = pmax i` (`sweepS_gen`) and discharge the ∃-witness via
`exists_achieves_pmax`; swap `tauS ↔ σ 0` by `tauS_eq`. -/
theorem sweepS_sound (N : ℕ) (h : sweepS 0 0 N = true) :
    ∀ n ∈ Finset.Ico 25 N, ∃ m ∈ Finset.range n, n + 2 < m + σ 0 m := by
  intro n hn
  simp only [Finset.mem_Ico] at hn
  obtain ⟨h25, hN⟩ := hn
  have hpm0 : (0 : ℕ) = pmax 0 := rfl
  have key : n + 2 < pmax n :=
    sweepS_gen N 0 0 hpm0 h n (by omega) (by omega) h25
  obtain ⟨m, hm, hle⟩ := exists_achieves_pmax n (by omega)
  refine ⟨m, hm, ?_⟩
  have hstep : n + 2 < m + tauS m := lt_of_lt_of_le key hle
  rwa [tauS_eq] at hstep

end MathProof.Certify.Reflect
