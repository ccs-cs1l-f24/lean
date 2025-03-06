import Mathlib

--n factorial is positive (will be used later)
theorem factorial_positive (n : ℕ) : ((Nat.factorial n) > 0) := by
  induction' n with d hd
  tauto
  rw [Nat.factorial]
  simp
  exact hd

--every number has a prime factor
theorem prime_factor {n : ℕ} (h : 2 ≤ n): ∃ p : ℕ, Nat.Prime p ∧ p ∣ n := by
  by_cases hw : Nat.Prime n
  use n
  refine Nat.exists_prime_and_dvd ?_
  exact Ne.symm (Nat.ne_of_lt h)

--useful lemma for later: if n ≥ 1, then n + 1 ≥ 2
theorem geq_two {n : ℕ} (h : 1 ≤ n) : n + 1 ≥ 2 := by
  exact Nat.le_add_of_sub_le h

--proof
theorem infinitely_many_primes : ∀n : ℕ, ∃ p : ℕ, Nat.Prime p ∧ p > n := by
    --first, choose an arbitrary n. We will show that there is a prime greater than n.
    intro n
    --We note that n! ≥ 1
    have fp : (Nat.factorial n) ≥ 1 := by
      apply factorial_positive
    --This implies that n! + 1 ≥ 2 by our lemma
    have fg2 : 2 ≤ (Nat.factorial n + 1) := by
      apply geq_two
      exact fp
    --since n! + 1 ≥ 2, it has a prime divisor q
    obtain ⟨q, hp, pdiv⟩ := prime_factor fg2
    --we can rephrase divisibility by stating that ∃ k such that k * q = n! + 1
    obtain ⟨k, hk⟩ := pdiv
    --now, we show that k = l + 1 for some natural number l. 
    --note that this follows from the fact that k ≠ 0.
    have hl : ∃ l : ℕ, k = l + 1 := by
      cases' k with z hz
      rw[mul_zero] at hk
      tauto
      use z
    --since such an l exists, we can declare it unambiguously.
    obtain ⟨l, hl⟩ := hl
    --we do some algebra to conclude that q * (l + 1) = n! + 1 → q * l + q = n! + 1.
    have im : q * l + q = Nat.factorial n + 1:= by
      rw [hk]
      rw [hl]
      ring
    --since q is prime it is at least 2.
    have qg : 1 < q := by
      exact Nat.Prime.one_lt hp

    --now, we wish to bound n! between two multiples of q, to show that these numbers are coprime.
    --first, we establish a lower bound, that q * l < n!.
    --we can use our previous lemmas to show that q * l + (q - 1) = n!
    --since 1 < q, we have that q - 1 > 0 so q * l < n!
    have lb : q * l < Nat.factorial n := by
      linarith

    --next, we establish an upper bound, that q * (l + 1) > n!. 
    --Note that we already have that q * (l + 1) = n! + 1 by definition, so this is pretty clear.
    have ub : Nat.factorial n < q * (l + 1) := by
      rw [<- hl]
      rw [<- hk]
      exact lt_add_one (Nat.factorial n)

    --next we show that q does not divide n!.
    --this follows from the fact that n! lies between consecutive multiples of q.
    have cp : ¬ q ∣ Nat.factorial n := by
      apply Nat.not_dvd_of_between_consec_multiples lb ub
    --to complete the proof, we have to show that q is the prime that we are looking for
    --it follows that we have to show that q > n, since we already know q is prime
    use q
    constructor
    exact hp
    --we split into two cases: either q ≤ n or q > n.
    --we want to establish a contradiction in the first case.
    obtain h_le | h_gt : q ≤ n ∨ n < q := le_or_lt q n
    --in the case where q ≤ n, q divides n!, so we have our contradiction.
    have cv: q ∣ (Nat.factorial n) := by
      exact (Nat.Prime.dvd_factorial hp).mpr h_le
    contradiction
    --it follows that q > n, so q is such a prime and thus we are done.
    exact h_gt
