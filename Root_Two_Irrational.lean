import Mathlib

theorem even_of_even_sqr {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m := by
  rw [pow_two, Nat.prime_two.dvd_mul] at h
  cases h <;> assumption

example {m n : ℕ} (coprime_mn : m.Coprime n) : m ^ 2 ≠ 2 * n ^ 2 := by
  intro sqr_eq

  have hm : 2 ∣ m := by
    refine even_of_even_sqr ?_
    exact Dvd.intro (n ^ 2) (id (Eq.symm sqr_eq))

  obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp hm
  have : 2 * (2 * k ^ 2) = 2 * n ^ 2 := by
    rw [← sqr_eq, meq]
    ring
  have : 2 * k ^ 2 = n ^ 2 := by
    apply Nat.mul_left_cancel at this
    exact this
    tauto
  have hn : 2 ∣ n := by
    refine even_of_even_sqr ?_
    symm at this
    use k^2
  have ht: 2 ∣ m.gcd n :=
    Nat.dvd_gcd hm hn
  have : 2 ∣ 1 := by
    rw [coprime_mn] at ht
    exact ht
  norm_num at this
