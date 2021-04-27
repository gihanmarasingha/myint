import tactic data.rat data.nat.prime

open rat

lemma aux {x y : ℕ} (h : x * x = 2 * y) : 2 ∣ x :=
(or_self (2 ∣ x)).mp $ (nat.prime.dvd_mul nat.prime_two).mp ⟨y, h⟩

example (a b : ℕ) (cop : nat.coprime a b) : ¬(a^2 = 2*b^2) :=
begin
  simp only [pow_two],
  intro h,
  have twodiva : 2 ∣ a := aux h,
  have twodiva' := twodiva, -- make a copy!
  cases twodiva' with m hm,
  rw [hm, mul_assoc] at h,
  have hdiv : m * (2* m) = b * b, from mul_left_cancel' two_ne_zero h,
  rw [mul_comm, mul_assoc] at hdiv,
  have twodivb : 2 ∣ b := aux hdiv.symm,
  exact nat.not_coprime_of_dvd_of_dvd one_lt_two twodiva twodivb cop,
end




/- example : ¬(∃ x : ℚ, x * x= 2) :=
λ h, exists.elim h $ λ x, num_denom_cases_on' x
(λ n d dne0 cop, _


) -/

/- example : ¬(∃ x : ℚ, x * x= 2) :=
λ h, exists.elim h $ λ x, (
  or.elim (em (x = 0))
  (λ hx0, by { rw [hx0, mul_zero], intro z2, exact two_ne_zero z2.symm, })
  (λ hxne0, num_denom_cases_on' x _)


) -/
