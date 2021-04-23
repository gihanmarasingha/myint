import basic

namespace myint

lemma add_pair_eq {a b : ℕ × ℕ} : ⟦a⟧ + ⟦b⟧ = add_pair a b := rfl

/-
`quotient.ind` gives the correspondence between elements of a quotient type and equivalence classes
of the underlying type. It states that to prove `β q` for every `q` in a quotient type, it suffices
to prove `β ⟦a⟧` for every `a` in the underlying type. 
-/

protected lemma add_comm : ∀ n m : myint, n + m = m + n :=
by { apply quotient.ind₂, intros, simp [add_pair_eq, add_pair], congr' 1; apply nat.add_comm }

protected lemma zero_add : ∀ a : myint, 0 + a = a :=
begin
  apply quotient.ind, rintros ⟨a₁, a₂⟩, dsimp [myint.has_zero_myint, mk], rw add_pair_eq,
  dsimp [add_pair], congr'; apply nat.zero_add,
end

protected lemma add_zero : ∀ a : myint, a + 0 = a :=
by { intro, rw [myint.add_comm, myint.zero_add], }

protected lemma add_left_neg : ∀ a : myint, -a + a = 0 :=
begin
  apply quotient.ind, rintro ⟨a₁, a₂⟩,
  dsimp [myint.has_zero_myint, myint.has_neg_myint, neg, myint.neg_pair, mk], simp [add_pair_eq, add_pair],
  apply quot.sound, dsimp [setoid.r, myintrel], rw [add_zero, zero_add, add_comm],
end

-- Proving `add_assoc` requires three applications of `quotient.ind`.
protected lemma add_assoc (n m k: myint) : n + m + k = n + (m + k) :=
quotient.ind (λ a₁, quotient.ind (λ a₂, quotient.ind
  (λ a₃, by { simp [add_pair_eq, add_pair, mk], congr' 3; simp [nat.add_assoc] } ) k) m) n 

-- Here, `nsmul` is multiplication of a `myint` on the left by a `nat`.
def nsmul : ℕ → myint → myint 
| 0 x            := 0
| (nat.succ n) x := x + (nsmul n x)

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

-- Having proved that `myint` is a `add_comm_group`, we can use the simplifier to prove theorems
-- auomatically!
example (a b : myint) : a + b - a = b := by simp

-- Replacing `simp` above with `squeeze_simp` shows exactly which lemmas are needed. I used this
-- to get the following.
example (a b : myint) : a + b - a = b := by simp only [add_sub_cancel']

-- The `ac_refl` tactic proves results that need only associativity and commutativity.
example (a b c d : myint) : (a + b) + (c + d) = b + (c + a) + d := by ac_refl 

-- The `•` symbol below is written `\smul` and represents the scalar multiplication `nsmul`.
example : 3 • (-7 : myint) = -21 := dec_trivial

@[simp] lemma nonneg_or_neg (a : myint) :
  ∃ n : ℕ, a = [[n, 0]] ∨ a = [[0, n]] :=
begin
  revert a,
  apply quotient.ind,
  rintro ⟨a₁, a₂⟩,
  cases (le_total a₁ a₂) with neg nonneg,
  { use a₂ - a₁, right, apply quot.sound,
    dsimp [setoid.r, myintrel], simp [nat.add_sub_of_le, neg], },
  { use a₁ - a₂, left, apply quot.sound,
    dsimp [setoid.r, myintrel], simp [nat.sub_add_cancel, nonneg], },
end

example (a : myint) : ∃ n : ℕ, a = [[n, 0]] ∨ a = [[0, n]] := by simp

end myint