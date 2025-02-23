import Mathlib

theorem even_of_even_sqr {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m := by
  rw [pow_two, Nat.prime_two.dvd_mul] at h
  cases h <;> assumption

example {n k : ℕ} (h : n = 4 * k + 1) : ∃ z, n^2 = 4 * z + 1  := by
 rw [h]
 use 4 * k^2 + 2 * k
 ring

example {n k : ℕ} (h : n = 4 * k + 3) : ∃ z, n^2 = 4 * z + 1  := by
 rw [h]
 use 4 * k^2 + 6 * k + 2
 ring

example {n k : ℕ} (h : n = 4 * k + 2) : ∃ z, n^2 = 4 * z  := by
 rw [h]
 use 4 * k^2 + 4 * k + 1
 ring

 example {n k : ℕ} (h : n = 4 * k) : ∃ z, n^2 = 4 * z  := by
 rw [h]
 use 4 * k^2
 ring
