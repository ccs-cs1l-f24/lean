import Mathlib

--if the square of a number is even then it is also even
theorem even_of_even_sqr {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m := by
  rw [pow_two, Nat.prime_two.dvd_mul] at h
  tauto

--a square cannot be 2 times another square, e.g. m^2/n^2 = (m/n)^2 ≠ 2 so √2 ≠ m/n
--important: the fraction is in "simplest form", eg gcd(m,n) = 1
theorem sqrt_two_irrational {m n : ℕ} (coprime_mn : m.Coprime n) : m ^ 2 ≠ 2 * n ^ 2 := by
  --introduce hypothesis for proof by contradiction
  intro sqr_eq
  
  --show that m must be even
  have hm : 2 ∣ m := by
    refine even_of_even_sqr ?_
    use n^2

  --replace the statement 2 | m with an equivalent statement m = 2 * k
  obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp hm

  
  have : 2 * (2 * k ^ 2) = 2 * n ^ 2 := by
    --write 2 * n^2 = m^2, then m = 2 * k implies m^2 = (2*k)^2 = 2 * (2 * k^2)
    rw [← sqr_eq, meq]
    ring

  have : 2 * k ^ 2 = n ^ 2 := by
    --cancel out the 2 from the previous equation
    apply Nat.mul_left_cancel at this
    exact this
    tauto
  --show that n is also even
  have hn : 2 ∣ n := by
    refine even_of_even_sqr ?_
    symm at this
    use k^2
  --show that the gcd of m and n is actually 2 * something
  have ht: 2 ∣ m.gcd n :=
    Nat.dvd_gcd hm hn
  --use the coprime hypothesis to establish a contradiction
  have : 2 ∣ 1 := by
    rw [coprime_mn] at ht
    exact ht
  norm_num at this
  --we are done!
