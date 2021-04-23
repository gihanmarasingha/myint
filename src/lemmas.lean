import basic

namespace myint

lemma add_pair_eq {a b : ℕ × ℕ} : ⟦a⟧ + ⟦b⟧ = add_pair a b := rfl

protected lemma add_comm : ∀ n m : myint, n + m = m + n :=
begin
  apply quotient.ind₂,
  intros,
  repeat { rw add_pair_eq },
  dsimp [add_pair],
  congr' 1; apply nat.add_comm,
end

protected lemma zero_add : ∀ a : myint, 0 + a = a :=
begin
  apply quotient.ind,
  rintros ⟨a₁, a₂⟩,
  dsimp [myint.has_zero_myint],
  unfold mk,
  rw add_pair_eq,
  dsimp [add_pair],
  congr'; apply nat.zero_add,
end

protected lemma add_zero : ∀ a : myint, a + 0 = a :=
by { intro, rw [myint.add_comm, myint.zero_add], }

def nsmul : ℕ → myint → myint 
| 0 x            := 0
| (nat.succ n) x := x + (nsmul n x)

protected lemma add_left_neg : ∀ a : myint, -a + a = 0 :=
begin
  apply quotient.ind,
  rintro ⟨a₁, a₂⟩,
  dsimp [myint.has_zero_myint, myint.has_neg_myint, neg, myint.neg_pair],
  unfold mk,
  repeat { rw add_pair_eq, },
  dsimp [add_pair], unfold mk,
  apply quot.sound,
  dsimp [setoid.r, myintrel],
  rw [add_zero, zero_add, add_comm],
end

namespace quotient

section
variables {α β γ φ : Type*}
variables [s₁ : setoid α] [s₂ : setoid β] [s₃ : setoid γ]
include s₁ s₂ s₃

protected lemma ind₃ {φ : quotient s₁ → quotient s₂ → quotient s₃ → Prop}
  (h : ∀ a b c, φ ⟦a⟧ ⟦b⟧ ⟦c⟧) (q₁ : quotient s₁) (q₂ : quotient s₂) (q₃ : quotient s₃): φ q₁ q₂ q₃ :=
    quotient.ind (λ a₁, quotient.ind (λ a₂, quotient.ind (λ a₃, h a₁ a₂ a₃) q₃) q₂) q₁

end

end quotient

protected lemma add_assoc : ∀ n m k: myint, n + m + k = n + (m + k) :=
begin
  apply quotient.ind₃,
  intros,
  repeat { rw add_pair_eq },
  dsimp [add_pair],
  unfold mk,
  repeat { rw add_pair_eq },
  dsimp [add_pair],
  congr' 1; apply nat.add_assoc,
end

instance add_semigroup_myint : add_semigroup myint :=
{ add := add,
  add_assoc := myint.add_assoc }

instance add_monoid_myint : add_monoid myint :=
{ zero := myint.has_zero_myint.zero,
  zero_add := myint.zero_add,
  add_zero := myint.add_zero,
  nsmul := nsmul,
  nsmul_zero' := λ _, rfl,
  nsmul_succ' := λ _ _, rfl,
  ..myint.add_semigroup_myint }

instance add_comm_semigroup_myint : add_comm_semigroup myint :=
{ add_comm := myint.add_comm,
  ..myint.add_semigroup_myint }

instance sub_neg_monoid_myint : sub_neg_monoid myint :=
{  ..myint.add_monoid_myint, ..myint.has_neg_myint, ..myint.has_sub_myint }

instance add_group_myint : add_group myint :=
{ add_left_neg := myint.add_left_neg, ..myint.sub_neg_monoid_myint }

instance add_comm_monoid_myint : add_comm_monoid myint :=
{ ..myint.add_comm_semigroup_myint, ..myint.add_monoid_myint }

instance add_comm_group_myint : add_comm_group myint :=
{ ..myint.add_group_myint, ..myint.add_comm_monoid_myint }

end myint