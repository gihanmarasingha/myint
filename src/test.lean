import tactic data.rat data.nat.prime data.real.irrational
import analysis.special_functions.pow

section sqrt2

open rat

/-
We prove that sqrt 2 is irrational. To make things simple, we work with natural numbers instead
of rational numbers. The idea is to derive a contradiction from the assumption that
`(a^2 = 2 * (b ^ 2))` for coprime natural nubmers `a` and `b`.
-/

-- First an auxiliary result to show `2 ∣ x` if `x * x = 2 * y`.
lemma aux {x y : ℕ} (h : x * x = 2 * y) : 2 ∣ x :=
(or_self (2 ∣ x)).mp $ (nat.prime.dvd_mul nat.prime_two).mp ⟨y, h⟩

-- Proof of the irrationality of sqrt 2.
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

end sqrt2

section irr_pow_irr

open real

/-
We show there exist irrational numbers `a` and `b` such that `a ^ b` is rational.
-/

-- A proof using `convert`.
example : ∃ a b : ℝ, irrational a ∧ irrational b ∧ ¬(irrational (a ^ b)) :=
begin
  have irrs2 := irrational_sqrt_two,
  by_cases h : irrational ((sqrt 2)^(sqrt 2)),
  { use [(sqrt 2)^(sqrt 2), sqrt 2],
    split, { exact h }, clear h,  split, { exact irrs2 },
    have ss_nat : sqrt 2 ^ 2 = 2 := sqr_sqrt zero_le_two,
    rw [←rpow_mul (sqrt_nonneg 2), ←pow_two, ss_nat],
    intro h₂,
    apply rat.not_irrational 2,
    convert h₂,
    have sqr_sqrt2 : (sqrt 2)^(2 : ℝ) = 2,
    { conv_rhs { rw ←ss_nat}, simp [←rpow_nat_cast], },
    simp [sqr_sqrt2], },
  { use [sqrt 2, sqrt 2], tauto, }
end

-- A proof without `convert`.
example : ∃ a b : ℝ, irrational a ∧ irrational b ∧ ¬(irrational (a ^ b)) :=
begin
  have irrs2 := irrational_sqrt_two,
  by_cases h : irrational ((sqrt 2)^(sqrt 2)),
  { use [(sqrt 2)^(sqrt 2), sqrt 2],
    split, { exact h }, clear h,  split, { exact irrs2 },
    have ss_nat : sqrt 2 ^ 2 = 2 := sqr_sqrt zero_le_two,
    rw [←rpow_mul (sqrt_nonneg 2), ←pow_two, ss_nat],
    rw (show (sqrt 2)^(2 : ℝ) = 2, by { conv_rhs { rw ←ss_nat}, simp [←rpow_nat_cast], } ),
    have := rat.not_irrational 2, simpa, },
  { use [sqrt 2, sqrt 2], tauto, }
end

-- A short proof.
example : ∃ a b : ℝ, irrational a ∧ irrational b ∧ ¬(irrational (a ^ b)) :=
begin
  have irrs2 := irrational_sqrt_two,
  by_cases h : irrational ((sqrt 2)^(sqrt 2)),
  { use [(sqrt 2)^(sqrt 2), sqrt 2],
    split, { exact h }, clear h,  split, { exact irrs2 },
    have ss_nat : sqrt 2 ^ 2 = 2 := sqr_sqrt zero_le_two,
    rw [←rpow_mul (sqrt_nonneg 2), ←pow_two, ss_nat],
    rw (show (sqrt 2)^(2 : ℝ) = 2, by { conv_rhs { rw ←ss_nat}, simp [←rpow_nat_cast], } ),
    convert rat.not_irrational 2, simp, },
  { use [sqrt 2, sqrt 2], tauto, }
end

end irr_pow_irr