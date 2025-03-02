import Mathlib

theorem factorial_positive (n : ℕ) : ((Nat.factorial n) > 0) := by
  induction' n with d hd
  tauto
  rw [Nat.factorial]
  simp
  exact hd


theorem prime_factor {n : ℕ} (h : 2 ≤ n): ∃ p : ℕ, Nat.Prime p ∧ p ∣ n := by
  by_cases hw : Nat.Prime n
  use n
  refine Nat.exists_prime_and_dvd ?_
  exact Ne.symm (Nat.ne_of_lt h)

theorem geq_two {n : ℕ} (h : 1 ≤ n) : n + 1 ≥ 2 := by
  exact Nat.le_add_of_sub_le h

theorem infinitely_many_primes : ∀n : ℕ, ∃ p : ℕ, Nat.Prime p ∧ p > n := by
    intro n
    have fp : (Nat.factorial n) ≥ 1 := by
      apply factorial_positive
    have fg2 : 2 ≤ (Nat.factorial n + 1) := by
      apply geq_two
      exact fp

    obtain ⟨q, hp, pdiv⟩ := prime_factor fg2
    obtain ⟨k, hk⟩ := pdiv
    have hl : ∃ l : ℕ, k = l + 1 := by
      cases' k with z hz
      rw[mul_zero] at hk
      tauto
      use z
    obtain ⟨l, hl⟩ := hl
    have im : q * l + q = Nat.factorial n + 1:= by
      rw [hk]
      rw [hl]
      ring

    have qg : 1 < q := by
      exact Nat.Prime.one_lt hp


    have lb : q * l < Nat.factorial n := by
      linarith


    have ub : Nat.factorial n < q * (l + 1) := by
      rw [<- hl]
      rw [<- hk]
      exact lt_add_one (Nat.factorial n)


    have cp : ¬ q ∣ Nat.factorial n := by
      apply Nat.not_dvd_of_between_consec_multiples lb ub
    use q
    constructor
    exact hp
    obtain h_le | h_gt : q ≤ n ∨ n < q := le_or_lt q n
    have cv: q ∣ (Nat.factorial n) := by
      exact (Nat.Prime.dvd_factorial hp).mpr h_le
    contradiction
    exact h_gt
