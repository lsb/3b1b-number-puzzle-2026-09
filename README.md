# Every number has a multiple made only of 0s and 1s

Machine-checked proofs in Lean 4 of two facts about decimal digits:

1. **Main theorem.** Every natural number `n > 0` has a multiple `n * k` (with `k > 0`) whose
   decimal digits are all 0 or 1.
2. **Secondary theorem.** If `n` ends in 1, 3, 7 or 9, some multiple of `n` is a *repunit*
   `11…1` (only ones).

There are two independent formalizations:

| File | Depends on | Digits defined as | Theorems |
|---|---|---|---|
| [`OnesZeros.lean`](OnesZeros.lean) | Lean core only | `m / 10^i % 10` | `exists_zeroOne_multiple`, `exists_repunit_multiple`, `exists_all_ones_multiple` |
| [`OnesZerosMathlib.lean`](OnesZerosMathlib.lean) | Mathlib | Mathlib's `Nat.digits 10` | `exists_zeroOne_multiple`, `exists_repunit_multiple` |

Neither uses `sorry`; both depend only on Lean's standard axioms (`propext`, `Classical.choice`,
`Quot.sound`).

## Checking the proofs

```
lean OnesZeros.lean     # core only, a few seconds
lake build              # both files; fetches Mathlib
```

`lake build` downloads Mathlib's prebuilt cache when it can reach it. Without it (e.g. if the
cache host is blocked), Lake builds the needed part of Mathlib from source. Only
`Mathlib.Data.Nat.Digits.Defs` and `Mathlib.Data.Finset.Card` are imported, so this is a
subset of Mathlib, not the whole library.

## Proof sketch

1. Repunits `R j = 11…1` (j ones), with `R 0 = 0`.
2. Pigeonhole: `R 0, …, R n` are n + 1 numbers, and there are only n remainders mod n,
   so two of them, `R a` and `R b` with `a < b`, leave the same remainder.
3. So `n` divides `R b − R a = R (b − a) · 10^a = 11…100…0`, which is positive and has
   only the digits 0 and 1. That proves the main theorem.
4. If `n` ends in 1, 3, 7 or 9 it shares no factor with 10, so from `n ∣ R (b − a) · 10^a`
   we can cancel the `10^a` and get `n ∣ R (b − a)`. That proves the secondary theorem.

## Finding the multiplier

[`find_multiplier.py`](find_multiplier.py) finds the multipliers. Each method works on
remainders mod `n`, so it takes at most about `n` cheap steps:

```
$ python3 find_multiplier.py 7 12
n = 7
  smallest 0/1    k = 143   n*k = 1001
  pigeonhole 0/1  k = 15873   n*k = 111111
  smallest 1s     k = 15873   n*k = 111111
n = 12
  smallest 0/1    k = 925   n*k = 11100
  pigeonhole 0/1  k = 925   n*k = 11100
  smallest 1s     none (n is divisible by 2 or 5)
```

* **smallest 0/1**: breadth-first search over remainders. It tries 1, 10, 11, 100, 101, …
  in increasing order and only follows each remainder once, so it finds the *smallest* 0/1
  multiple.
* **pigeonhole 0/1**: exactly the number the Lean proof constructs.
* **smallest 1s**: iterates `r ↦ (10r + 1) mod n` until it hits 0. The number of steps is
  the length of the repunit, at most `n`.

These are different multiples of `n`, and their sizes can differ enormously. Take the prime
`n = 999983`:

* Allowing zeros, the smallest answer is short:
  `999983 × 10100282705817 = 10100111001011001111` (20 digits).
* Allowing only ones, the smallest answer is the repunit with 999982 ones, so its multiplier
  `k` has 999976 digits. Zeros are what let the short answer exist.

For huge answers like that, the script prints only the digit count instead of the number.

## Why this puzzle is interesting

* **It is true for every number, with no exceptions.** Pick any `n`, even 2026 or 999983, and
  some multiple of it is written with only 0s and 1s. The proof explains why without searching.
  Knowing how the multiple is built also gives you a way to find it.
* **The proof is pure pigeonhole.** No number theory is needed for the main theorem. There are
  only `n` possible remainders, so among `n + 1` repunits two must collide, and subtracting them
  gives the answer. It is the same idea as "among 13 people, two share a birth month".
* **Ones only is a genuinely different question.** A multiple of 2 or 5 must end in an even digit
  or in 0 or 5, so it can never end in 1. So repunits are possible exactly when `n` ends in 1, 3,
  7 or 9. For those `n`, the only new step is cancelling the factor `10^a`, which needs `n` to
  share no factor with 10.
* **It connects to repeating decimals.** `n` divides the repunit with `L` ones exactly when
  `9n` divides `10^L − 1`, which is what makes `1/(9n)` repeat every `L` digits. For example,
  `1/7 = 0.142857 142857 …` repeats every 6 digits, and `111111 = 7 × 15873` is the first
  repunit divisible by 7. By Fermat's little theorem, every prime `p` other than 2, 3 and 5
  divides the repunit with `p − 1` ones. For 999983 that repunit is the smallest one, which is
  why its all-ones multiple is so long.
* **The search is a neat algorithm.** Looking for "the smallest number made of 0s and 1s
  divisible by `n`" seems to require trying up to `2^digits` candidates. Working with
  remainders instead turns it into a search over at most `n` states. The same trick is behind
  many shortest-path puzzles.
* **It is a good first formal proof.** The informal argument fits in three lines, but a proof
  assistant makes you settle every detail: what a "digit" is, why `0` does not count as an
  answer, and why the pigeonhole principle holds at all (the core-Lean file proves it from
  scratch). Two independent formalizations, one of them using Mathlib's standard `Nat.digits`,
  leave little room for a mistake in how the statement is written down.
