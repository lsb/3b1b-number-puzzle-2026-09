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

The smallest 0/1 multiple is usually short (for n = 999983 it has 20 digits). The repunit
can be very long (for the prime 999983 it has 999982 ones), so the script prints only its
length when it is huge.
