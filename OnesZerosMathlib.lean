import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Finset.Card

/-!
# The same theorems, stated with Mathlib's `Nat.digits`

`Nat.digits 10 m` is Mathlib's standard list of the decimal digits of `m`, least
significant first (`Nat.digits 10 1203 = [3, 0, 2, 1]`). Stating the results with it
means the reader does not have to trust a home-made definition of "digit".

* `exists_zeroOne_multiple`: every `n > 0` has a multiple `n * k` with `k > 0` whose
  digits are all `0` or `1`. In fact the digits are `a` zeros followed by `c ≥ 1` ones.
* `exists_repunit_multiple`: if `n` ends in 1, 3, 7 or 9, some `n * k` is `11…1`.

The proof is the same pigeonhole argument as in `OnesZeros.lean`.
-/

namespace OnesZerosMathlib

open Nat

/-- The repunit with `c` ones, `11…1`. -/
def R (c : ℕ) : ℕ := ofDigits 10 (List.replicate c 1)

theorem R_add (a c : ℕ) : R (a + c) = R a + 10 ^ a * R c := by
  simp [R, List.replicate_add, ofDigits_append]

/-- `ofDigits` inverts `digits` for a list of `a` zeros followed by `c ≥ 1` ones. -/
theorem digits_zeros_ones (a c : ℕ) (hc : 0 < c) :
    digits 10 (ofDigits 10 (List.replicate a 0 ++ List.replicate c 1)) =
      List.replicate a 0 ++ List.replicate c 1 := by
  obtain ⟨c, rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
  apply digits_ofDigits _ (by norm_num)
  · intro l hl
    simp only [List.mem_append, List.mem_replicate] at hl
    omega
  · intro _
    simp [List.replicate_succ', ← List.append_assoc]

theorem ofDigits_zeros_ones (a c : ℕ) :
    ofDigits 10 (List.replicate a 0 ++ List.replicate c 1) = 10 ^ a * R c := by
  simp [R, ofDigits_append]

/-- Pigeonhole on `R 0, …, R n` mod `n`: `n` divides some `10 ^ a * R c` with `c > 0`. -/
theorem exists_dvd (n : ℕ) (hn : 0 < n) : ∃ a c, 0 < c ∧ n ∣ 10 ^ a * R c := by
  obtain ⟨x, -, y, -, hxy, he⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.range (n + 1)) (t := Finset.range n) (f := fun j => R j % n)
    (by simp) (fun j _ => by simpa using Nat.mod_lt _ hn)
  -- Whichever of `x`, `y` is smaller plays the role of `a`.
  have key : ∀ a b, a < b → R a % n = R b % n → ∃ a c, 0 < c ∧ n ∣ 10 ^ a * R c := by
    intro a b hab he
    obtain ⟨c, rfl⟩ : ∃ c, b = a + c := ⟨b - a, by omega⟩
    refine ⟨a, c, by omega, ?_⟩
    have hsub : R (a + c) - R a = 10 ^ a * R c := by rw [R_add]; omega
    rw [← hsub]
    exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq he.symm)
  rcases Nat.lt_or_gt_of_ne hxy with h | h
  · exact key x y h he
  · exact key y x h he.symm

/-- **Main theorem.** Every positive `n` has a positive multiple whose decimal digits
are all `0` or `1`. -/
theorem exists_zeroOne_multiple (n : ℕ) (hn : 0 < n) :
    ∃ k, 0 < k ∧ ∀ d ∈ digits 10 (n * k), d = 0 ∨ d = 1 := by
  obtain ⟨a, c, hc, hdvd⟩ := exists_dvd n hn
  have hP : 0 < 10 ^ a * R c := by
    obtain ⟨c, rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    simp [R, List.replicate_succ, ofDigits_cons]
  have hnk : n * (10 ^ a * R c / n) = 10 ^ a * R c := Nat.mul_div_cancel' hdvd
  refine ⟨10 ^ a * R c / n, ?_, ?_⟩
  · apply Nat.pos_of_ne_zero
    intro h0
    rw [h0, Nat.mul_zero] at hnk
    omega
  · intro d hd
    rw [hnk, ← ofDigits_zeros_ones, digits_zeros_ones a c hc] at hd
    simp only [List.mem_append, List.mem_replicate] at hd
    omega

/-- A number ending in 1, 3, 7 or 9 shares no factor with 10. -/
theorem coprime_ten {n : ℕ} (hn : n % 10 = 1 ∨ n % 10 = 3 ∨ n % 10 = 7 ∨ n % 10 = 9) :
    Coprime n 10 := by
  unfold Coprime
  rw [Nat.gcd_comm, Nat.gcd_rec]
  rcases hn with h | h | h | h <;> rw [h] <;> rfl

/-- **Secondary theorem.** If `n` ends in 1, 3, 7 or 9, some multiple of `n` is written
with ones only: its digits are exactly `c ≥ 1` ones. -/
theorem exists_repunit_multiple (n : ℕ)
    (hn : n % 10 = 1 ∨ n % 10 = 3 ∨ n % 10 = 7 ∨ n % 10 = 9) :
    ∃ c k, 0 < c ∧ digits 10 (n * k) = List.replicate c 1 := by
  obtain ⟨a, c, hc, hdvd⟩ := exists_dvd n (by omega)
  -- `n` is coprime to `10 ^ a`, so it divides `R c` itself.
  obtain ⟨k, hk⟩ := ((coprime_ten hn).pow_right a).dvd_of_dvd_mul_left hdvd
  refine ⟨c, k, hc, ?_⟩
  rw [← hk]
  simpa [ofDigits_zeros_ones] using digits_zeros_ones 0 c hc

/-- Sanity check on the definition: `digits` lists decimal digits, last digit first. -/
example : digits 10 1203 = [3, 0, 2, 1] := by norm_num

end OnesZerosMathlib
