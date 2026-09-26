# Every number has a multiple made only of 0s and 1s

A machine-checked proof (Lean 4, core only, no Mathlib) that for every natural number `n`
there is a `k > 0` such that every decimal digit of `n * k` is 0 or 1. For `n > 0` the
product is positive, so it is not the trivial 0.

Main result: `OnesZeros.exists_zeroOne_multiple` in [`OnesZeros.lean`](OnesZeros.lean).

Check it with:

```
lean OnesZeros.lean
```

## Proof sketch

1. Repunits `R j = 11…1` (j ones), with `R 0 = 0`.
2. Pigeonhole: `R 0, …, R n` are n + 1 numbers, and there are only n remainders mod n,
   so two of them, `R a` and `R b` with `a < b`, leave the same remainder.
3. So `n` divides `R b − R a = R (b − a) · 10^a = 11…100…0`, which is positive and has
   only the digits 0 and 1.
