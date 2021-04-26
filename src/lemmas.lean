import basic
import group_theory.order_of_element
import data.zmod.basic

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
protected lemma add_assoc (n m k : myint) : n + m + k = n + (m + k) :=
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

lemma nonneg_or_neg : ∀ a : myint, ∃ n : ℕ, a = [[n, 0]] ∨ a = [[0, n.succ]] :=
begin
  apply quotient.ind,
  rintro ⟨a₁, a₂⟩,
  cases (le_or_lt a₂ a₁) with nonneg neg,
  { use a₁ - a₂, left, apply quot.sound,
    dsimp [setoid.r, myintrel], simp [nat.sub_add_cancel, nonneg], },
  { use (a₂ - a₁).pred, right, apply quot.sound,
    dsimp [setoid.r, myintrel], simp [nat.add_sub_of_le, neg],
    rw nat.succ_pred_eq_of_pos,
    { exact nat.add_sub_of_le (le_of_lt neg) },
    { exact nat.sub_pos_of_lt neg }, },
end

def prod_nat_to_int (n : ℕ × ℕ) : ℤ := n.1 - n.2

/-- A funtion from myint to int. -/
def myint_to_int (n : myint) : ℤ :=
begin
  apply quotient.lift_on n prod_nat_to_int, intros a b h,
  dsimp [has_equiv.equiv, setoid.r, myintrel] at h,
  dsimp [prod_nat_to_int], linarith,
end

lemma myint_to_int_of_pair (n m : ℕ) : myint_to_int [[n, m]] = n - m := rfl

example : myint_to_int [[6,13]] = -7 := rfl

/-- The function `myint_to_int` is additive. -/
protected lemma map_add_myint_to_int : ∀ n m : myint, myint_to_int (n + m) = myint_to_int n + myint_to_int m :=
begin
  apply quotient.ind₂,
  rintro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩,
  rw [add_pair_eq, add_pair, ←mk, ←mk],
  repeat { rw myint_to_int_of_pair },
  push_cast, linarith,
end

/-- Wwe define `myint_to_int_hom`, an (additve group) homomorphism from `myint` to `int`. -/
def myint_to_int_add_monoid_hom : myint →+ ℤ :=
{ to_fun := myint_to_int,
  map_zero' := rfl,
  map_add' := myint.map_add_myint_to_int }

/-- The function `myint_to_int` has an inverse function. We first define a function `int_to_prod_nat` -/
def int_to_prod_nat : ℤ → ℕ × ℕ
| (int.of_nat n)          := (n, 0)
| (int.neg_succ_of_nat n) := (0, nat.succ n)

example : int_to_prod_nat (-5) = (0,5) := rfl

/-- `int_my_myint` is the composite of `quotient.mk` and `int_to_prod_nat`.-/
def int_to_myint (n : ℤ) :  myint := ⟦int_to_prod_nat n⟧

example : int_to_myint (-5) = [[0, 5]] := rfl

/-- We show that `myint_to_int` is an equivalence. Here, `myint ≃ int` is notation for `equiv myint int`. -/
def myint_to_int_equiv : myint ≃ int := 
{ to_fun := myint_to_int,
  inv_fun := int_to_myint,
  left_inv :=
  by { intro n, rcases (nonneg_or_neg n) with ⟨a, rfl | rfl⟩; { rw myint_to_int_of_pair, norm_cast, }, },
  right_inv := by {rintro ⟨_, _⟩; refl, }, }

/-
For free, we have an additive equivalence (i.e. a group isomomorphism) from `myint` to `int`.
Here, `myint ≃+ int` is notation for `add_equiv myint int`.
-/
def myint_to_int_add_equiv : myint ≃+ int :=
{ ..myint_to_int_equiv, ..myint_to_int_add_monoid_hom }

/-
Using this equivalence, we get (for free) that the equivalence respects orders of elements.
-/
example (a : myint) : add_order_of (myint_to_int a) = add_order_of a :=
let f := myint_to_int_add_equiv in add_order_of_injective (f.to_add_monoid_hom) (f.injective) a

def twice : ℤ →+ ℤ :=
{ to_fun := λ x, 2 * x,
  map_zero' := by simp,
  map_add' := by simp [mul_add], }

def five_z : add_subgroup int := add_subgroup.closure ({5} : set ℤ)

def five_mint : add_subgroup myint := add_subgroup.closure ({5} : set myint)

example : five_z.comap myint_to_int_add_monoid_hom = five_mint :=
begin
  sorry
end

end myint