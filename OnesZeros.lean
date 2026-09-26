/-!
# Every number has a nonzero multiple written only with the digits 0 and 1

**Theorem.** For every natural number `n` there is a natural number `k > 0` such that
every decimal digit of `n * k` is `0` or `1`. For `n > 0` the product is itself
positive, so the multiple is not the trivial `0`.

**Proof idea (pigeonhole).** Look at the repunits `R 0 = 0, R 1 = 1, R 2 = 11, R 3 = 111, …`.
Among the `n + 1` numbers `R 0, …, R n` two have the same remainder mod `n`, say `R a`
and `R b` with `a < b`. Their difference `R b - R a = R (b - a) * 10 ^ a` looks like
`11…100…0`, it is positive, and `n` divides it.

This file uses only core Lean 4 (no Mathlib) and no `sorry`.
Check it with `lean OnesZeros.lean`.
-/

namespace OnesZeros

/-- The `i`-th decimal digit of `m`, counting from the right starting at `0`. -/
def digit (m i : Nat) : Nat := m / 10 ^ i % 10

/-- Every decimal digit of `m` is `0` or `1`. -/
def ZeroOne (m : Nat) : Prop := ∀ i, digit m i ≤ 1

/-! ## Digits -/

/-- Adding a digit `d ≤ 1` on the right keeps a `0`/`1` number `0`/`1`. -/
theorem zeroOne_append {m d : Nat} (hm : ZeroOne m) (hd : d ≤ 1) :
    ZeroOne (10 * m + d) := by
  intro i
  cases i with
  | zero => simp [digit]; omega
  | succ i =>
    have h : (10 * m + d) / 10 = m := by omega
    have := hm i
    simp only [digit] at this ⊢
    rw [Nat.pow_succ', ← Nat.div_div_eq_div_mul, h]
    exact this

theorem zeroOne_zero : ZeroOne 0 := by
  intro i; simp [digit]

/-- The repunit with `j` ones: `R 0 = 0`, `R 1 = 1`, `R 2 = 11`, … -/
def R : Nat → Nat
  | 0 => 0
  | j + 1 => 10 * R j + 1

theorem zeroOne_R (j : Nat) : ZeroOne (R j) := by
  induction j with
  | zero => exact zeroOne_zero
  | succ j ih => exact zeroOne_append ih (by omega)

/-- Shifting left by `a` places (appending `a` zeros) keeps a `0`/`1` number `0`/`1`. -/
theorem zeroOne_shift {m : Nat} (hm : ZeroOne m) (a : Nat) : ZeroOne (m * 10 ^ a) := by
  induction a with
  | zero => simpa using hm
  | succ a ih =>
    have := zeroOne_append ih (d := 0) (by omega)
    rw [Nat.pow_succ', Nat.mul_left_comm]
    simpa using this

theorem R_pos {j : Nat} (h : 0 < j) : 0 < R j := by
  cases j with
  | zero => omega
  | succ j => simp [R]

/-- `R c` has exactly `c` digits: `R c < 10 ^ c`. -/
theorem R_lt (c : Nat) : R c < 10 ^ c := by
  induction c with
  | zero => simp [R]
  | succ c ih => rw [R, Nat.pow_succ']; omega

/-- `R (a + c) = R c * 10 ^ a + R a`, e.g. `11111 = 111 * 100 + 11`. -/
theorem R_add (a c : Nat) : R (a + c) = R c * 10 ^ a + R a := by
  induction a with
  | zero => simp [R]
  | succ a ih =>
    rw [Nat.add_right_comm, R, ih, R, Nat.pow_succ', Nat.mul_add, Nat.mul_left_comm]
    omega

/-! ## Pigeonhole -/

/-- If `f` sends each of `0, 1, …, n` below `n`, two of them collide. -/
theorem pigeonhole (n : Nat) (f : Nat → Nat) (hf : ∀ i, i ≤ n → f i < n) :
    ∃ i j, i < j ∧ j ≤ n ∧ f i = f j := by
  induction n generalizing f with
  | zero => have := hf 0 (Nat.le_refl 0); omega
  | succ n ih =>
    by_cases hc : ∃ i, i ≤ n ∧ f i = f (n + 1)
    · obtain ⟨i, hi, he⟩ := hc
      exact ⟨i, n + 1, by omega, Nat.le_refl _, he⟩
    · have hne : ∀ i, i ≤ n → f i ≠ f (n + 1) := fun i hi he => hc ⟨i, hi, he⟩
      -- Redirect the value `n` to the unused value `f (n + 1)`.
      let g := fun i => if f i = n then f (n + 1) else f i
      have hg : ∀ i, i ≤ n → g i < n := by
        intro i hi
        have h1 := hf i (by omega)
        have h2 := hf (n + 1) (Nat.le_refl _)
        have h3 := hne i hi
        simp only [g]
        split <;> omega
      obtain ⟨i, j, hij, hjn, he⟩ := ih g hg
      refine ⟨i, j, hij, by omega, ?_⟩
      have hi' := hne i (by omega)
      have hj' := hne j hjn
      simp only [g] at he
      split at he <;> split at he <;> omega

/-! ## Main theorem -/

/-- Every positive `n` has a positive multiple whose decimal digits are all `0` or `1`. -/
theorem exists_zeroOne_multiple (n : Nat) (hn : 0 < n) :
    ∃ k, 0 < k ∧ 0 < n * k ∧ ZeroOne (n * k) := by
  obtain ⟨a, b, hab, -, he⟩ :=
    pigeonhole n (fun j => R j % n) (fun _ _ => Nat.mod_lt _ hn)
  obtain ⟨c, rfl⟩ : ∃ c, b = a + c := ⟨b - a, by omega⟩
  have hc : 0 < c := by omega
  let P := R c * 10 ^ a
  have hdiff : R (a + c) - R a = P := by rw [R_add]; omega
  have hdvd : n ∣ P := by
    rw [← hdiff]
    exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq he.symm)
  have hP : 0 < P := Nat.mul_pos (R_pos hc) (Nat.pow_pos (by omega))
  have hnk : n * (P / n) = P := Nat.mul_div_cancel' hdvd
  refine ⟨P / n, ?_, ?_, ?_⟩
  · apply Nat.pos_of_ne_zero
    intro h0
    rw [h0, Nat.mul_zero] at hnk
    omega
  · omega
  · rw [hnk]; exact zeroOne_shift (zeroOne_R c) a

/-- The statement for *every* natural number, `0` included (there `0 * 1 = 0`). -/
theorem every_number_has_zeroOne_multiple (n : Nat) :
    ∃ k, 0 < k ∧ ZeroOne (n * k) := by
  cases n with
  | zero => exact ⟨1, by omega, by simpa using zeroOne_zero⟩
  | succ n =>
    obtain ⟨k, hk, -, hz⟩ := exists_zeroOne_multiple (n + 1) (by omega)
    exact ⟨k, hk, hz⟩

/-! ## Secondary theorem: numbers ending in 1, 3, 7, 9 divide a repunit -/

/-- Every digit of `R c` is `1` (for `i < c`); so `R c` is literally `11…1`. -/
theorem digit_R {c i : Nat} (h : i < c) : digit (R c) i = 1 := by
  induction c generalizing i with
  | zero => omega
  | succ c ih =>
    cases i with
    | zero => simp only [digit, R, Nat.pow_zero, Nat.div_one]; omega
    | succ i =>
      have hd : (10 * R c + 1) / 10 = R c := by omega
      simp only [digit, R] at ih ⊢
      rw [Nat.pow_succ', ← Nat.div_div_eq_div_mul, hd]
      exact ih (by omega)

/-- A number ending in 1, 3, 7 or 9 can be cancelled against a factor 10:
if `n ∣ 10 * m` then `n ∣ m`. (Core Lean has no `Coprime`, so we argue with
remainders mod 2 and mod 5 directly.) -/
theorem dvd_of_dvd_ten_mul {n m : Nat} (hn : n % 10 = 1 ∨ n % 10 = 3 ∨ n % 10 = 7 ∨ n % 10 = 9)
    (h : n ∣ 10 * m) : n ∣ m := by
  obtain ⟨t, ht⟩ := h
  -- `t` is even, because `n` is odd and `n * t = 10 * m` is even.
  have h2 : t % 2 = 0 := by
    have key : ∀ a, a < 2 → ∀ b, b < 2 → a * b % 2 = 0 → a = 0 ∨ b = 0 := by decide
    have hm : n % 2 * (t % 2) % 2 = 0 := by rw [← Nat.mul_mod, ← ht]; omega
    have := key (n % 2) (Nat.mod_lt _ (by omega)) (t % 2) (Nat.mod_lt _ (by omega)) hm
    omega
  obtain ⟨t', rfl⟩ : ∃ t', t = 2 * t' := ⟨t / 2, by omega⟩
  -- `t'` is a multiple of 5, because `5 ∤ n` and `n * t' = 5 * m`.
  have h5 : t' % 5 = 0 := by
    have key : ∀ a, a < 5 → ∀ b, b < 5 → a * b % 5 = 0 → a = 0 ∨ b = 0 := by decide
    have hm : n % 5 * (t' % 5) % 5 = 0 := by
      rw [← Nat.mul_mod, Nat.mul_left_comm] at *
      omega
    have := key (n % 5) (Nat.mod_lt _ (by omega)) (t' % 5) (Nat.mod_lt _ (by omega)) hm
    omega
  obtain ⟨u, rfl⟩ : ∃ u, t' = 5 * u := ⟨t' / 5, by omega⟩
  refine ⟨u, ?_⟩
  rw [Nat.mul_left_comm n 2, Nat.mul_left_comm n 5] at ht
  omega

/-- If `n` ends in 1, 3, 7 or 9, some multiple of `n` is a repunit `11…1`
(with at least one digit): every digit below position `c` is `1`, and every
digit from position `c` on is `0`. -/
theorem exists_repunit_multiple (n : Nat)
    (hn : n % 10 = 1 ∨ n % 10 = 3 ∨ n % 10 = 7 ∨ n % 10 = 9) :
    ∃ c k, 0 < c ∧ n * k = R c := by
  have hn0 : 0 < n := by omega
  obtain ⟨a, b, hab, -, he⟩ :=
    pigeonhole n (fun j => R j % n) (fun _ _ => Nat.mod_lt _ hn0)
  obtain ⟨c, rfl⟩ : ∃ c, b = a + c := ⟨b - a, by omega⟩
  have hdiff : R (a + c) - R a = R c * 10 ^ a := by rw [R_add]; omega
  have hdvd : n ∣ R c * 10 ^ a := by
    rw [← hdiff]
    exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq he.symm)
  -- Strip the trailing zeros one factor of 10 at a time.
  have strip : ∀ a, n ∣ R c * 10 ^ a → n ∣ R c := by
    intro a
    induction a with
    | zero => simp
    | succ a ih =>
      intro h
      apply ih
      apply dvd_of_dvd_ten_mul hn
      rwa [Nat.pow_succ', Nat.mul_left_comm] at h
  obtain ⟨k, hk⟩ := strip a hdvd
  exact ⟨c, k, by omega, hk.symm⟩

/-- The repunit statement phrased with digits: `n * k` is positive, its digits below
position `c` are all `1`, and it has no digits from position `c` on. -/
theorem exists_all_ones_multiple (n : Nat)
    (hn : n % 10 = 1 ∨ n % 10 = 3 ∨ n % 10 = 7 ∨ n % 10 = 9) :
    ∃ c k, 0 < c ∧ (∀ i, i < c → digit (n * k) i = 1) ∧ n * k < 10 ^ c := by
  obtain ⟨c, k, hc, hk⟩ := exists_repunit_multiple n hn
  refine ⟨c, k, hc, fun i hi => hk ▸ digit_R hi, hk ▸ R_lt c⟩

/-! ## Sanity checks -/

-- `digit` reads decimal digits right to left: 1203 has digits 3, 0, 2, 1, 0, 0, …
example : (List.range 6).map (digit 1203) = [3, 0, 2, 1, 0, 0] := by decide

-- `ZeroOne` rejects numbers with other digits: the last digit of 12 is 2.
example : ¬ ZeroOne 12 := fun h => absurd (h 0) (by decide)

-- Concrete instances: 7 * 1443 = 10101, and 7 * 15873 = 111111 = R 6.
example : 7 * 1443 = 10101 := by decide
example : 7 * 15873 = R 6 := by decide

end OnesZeros
