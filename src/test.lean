import tactic data.rat data.nat.prime data.real.irrational
import analysis.special_functions.pow

section sqrt2

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

end sqrt2

--noncomputable theory

--open_locale classical real topological_space nnreal ennreal 

open real

example : irrational (sqrt 2) := irrational_sqrt_two

example : sqrt 2 ≥ 0:= sqrt_nonneg 2

example : (sqrt 2) ^2 = 2 := sqr_sqrt zero_le_two

#check pow_two

--set_option pp.all true

example : ∃ a b : ℝ, irrational a ∧ irrational b ∧ ¬(irrational (a^b)) :=
begin
  have irrs2 := irrational_sqrt_two,
  by_cases h : irrational ((sqrt 2)^(sqrt 2)),
  { use [(sqrt 2)^(sqrt 2), sqrt 2],
    split, { exact h }, clear h,  split, { exact irrs2 },
    rw [←(rpow_mul (sqrt_nonneg 2)), ←pow_two, sqr_sqrt zero_le_two],
    intro h₂,
    apply (rat.not_irrational 2),
    convert h₂,
    have sqr_sqrt2 : (sqrt 2)^(2 : ℝ) = 2,
    { have h₃ := sqr_sqrt zero_le_two,
      rw ←rpow_nat_cast at h₃,
      conv_rhs { rw ←h₃ }, simp, },
    simp [sqr_sqrt2], },
  { use [sqrt 2, sqrt 2], tauto, }
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
