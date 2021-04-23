import tactic

@[derive decidable_rel]
protected def myintrel : ℕ × ℕ → ℕ × ℕ → Prop := λ a b, a.1 + b.2 = b.1 + a.2

local infix `~` := myintrel

protected theorem myintrel.refl : ∀ n : ℕ × ℕ, n ~ n := λ n, rfl

protected theorem myintrel.symm : ∀ n m : ℕ × ℕ, n ~ m → m ~ n :=
  λ n m h, by { dsimp [myintrel] at *, symmetry, rw h, }

protected theorem myintrel.trans : ∀ n m k : ℕ × ℕ, n ~ m → m ~ k → n ~ k :=
  by { dsimp [myintrel], intros n m k h₁ h₂, linarith, }

protected theorem is_equivalence :
  equivalence myintrel := mk_equivalence myintrel myintrel.refl myintrel.symm myintrel.trans

instance myint.setoid : setoid (ℕ × ℕ) := setoid.mk myintrel is_equivalence

def myint := quotient myint.setoid

namespace myint

def mk (a₁ a₂ : ℕ) : myint := ⟦(a₁, a₂)⟧

notation `[[` a₁ `,` a₂ `]]` := mk a₁ a₂

example : [[1, 6]] = [[10, 15]] := dec_trivial

@[derive decidable] private def is_nonneg' (n : ℕ × ℕ) : Prop := n.1 ≥ n.2

example : is_nonneg' (10,8) := dec_trivial

def prod_nat_to_prod_nat (n : ℕ × ℕ) : ℕ × ℕ := if is_nonneg' n then (n.1-n.2, 0) else (0, n.2-n.1)

example : prod_nat_to_prod_nat (5,7) = (0, 2) := rfl

example : prod_nat_to_prod_nat (13, 4) = (9, 0) := rfl

def prod_nat_to_string (n : ℕ × ℕ) : string :=
  if is_nonneg' n then to_string (n.1-n.2) else  "-" ++ to_string (n.2 - n.1)

lemma prod_nat_of_is_nonneg {n : ℕ × ℕ} (h : is_nonneg' n) :
  prod_nat_to_prod_nat n = (n.1 - n.2, 0) := if_pos h

lemma prod_nat_of_is_neg {n : ℕ × ℕ} (h : ¬(is_nonneg' n)) :
  prod_nat_to_prod_nat n = (0, n.2 - n.1) := if_neg h

-- An auxiliary lemma needed only in the proof of `myint_to_prod_nat`.
private lemma aux {x y u v : nat} (h : x + v = u + y) (k : x ≥ y) : x - y = u - v :=
begin
  have h₂ : u = x - y + v := (nat.add_sub_cancel u y) ▸ h ▸ (nat.sub_add_comm k),
  rw [h₂, nat.add_sub_cancel],
end

/-
`myint_to_prod_nat` is our main workhorse. Given `n : myint`, it produces a canonical representative
of type `ℕ × ℕ`. To do this, we use `quotient.lift` - a result that shows a function of type `α → β`
can be lifted to a function of type `quotient s → β` as long as the function respects the
equivalence relation that defines `quotient s`.
-/
def myint_to_prod_nat (n : myint) : ℕ × ℕ :=
quotient.lift_on n prod_nat_to_prod_nat
( λ a b h,
  if hnna : (is_nonneg' a) then
  begin
    dsimp [has_equiv.equiv, setoid.r, myintrel] at h,  dsimp [is_nonneg'] at hnna,
    rw [prod_nat_of_is_nonneg hnna, prod_nat_of_is_nonneg (show is_nonneg' b, by { dsimp [is_nonneg'], linarith, })],
    ext, { dsimp, exact aux h hnna, }, { refl, },
  end
  else
  begin
    dsimp [has_equiv.equiv, setoid.r, myintrel] at h,  dsimp [is_nonneg'] at hnna,
    rw [prod_nat_of_is_neg hnna, prod_nat_of_is_neg (show ¬is_nonneg' b, by { dsimp [is_nonneg'], linarith, })],
    ext, { refl, }, { dsimp, apply aux; linarith, },
  end )

example : myint_to_prod_nat [[10, 4]] = (6,0) := rfl

@[derive decidable]
def is_nonneg : myint → Prop := is_nonneg' ∘ myint_to_prod_nat

example : is_nonneg [[10, 3]] := dec_trivial

def myint_to_string : myint → string := prod_nat_to_string ∘ myint_to_prod_nat

instance myint_repr : has_repr myint := ⟨myint_to_string⟩

instance has_coe_to_myint : has_coe nat (quotient myint.setoid) := ⟨λ n, [[n,0]]⟩

instance has_one_myint : has_one myint := ⟨[[1, 0]]⟩

instance has_zero_myint : has_zero myint := ⟨[[0, 0]]⟩

protected def neg_pair (n : ℕ × ℕ) : myint := [[n.2, n.1]]

/-
The definition `neg` below uses `quot.sound`. This result states that two elements `⟦a⟧` and `⟦b⟧`
of a quotient type are equal if their representatives are equivalent. That is, `a ≈ b → ⟦a⟧ = ⟦b⟧`.
-/
def neg (n : myint) : quotient myint.setoid :=
quotient.lift_on n myint.neg_pair
( λ a b h, quotient.sound (by {dsimp [has_equiv.equiv, setoid.r, myintrel] at h ⊢,
    simp only [add_comm, h], })) 

instance has_neg_myint : has_neg myint := ⟨neg⟩

example : - [[5, 9]] = [[9, 5]] := rfl

def add_pair (n m : ℕ × ℕ) : myint := [[n.1 + m.1, n.2 + m.2]]

def add : myint → myint → myint :=
quotient.lift₂ add_pair
( λ a₁ a₂ b₁ b₂ h₁ h₂, quot.sound (by {dsimp [has_equiv.equiv, setoid.r, myintrel] at *, linarith,}))

instance has_add_myint : has_add myint := ⟨add⟩

instance has_add_myint' : has_add (quotient myint.setoid) := ⟨add⟩

instance has_sub_myint : has_sub myint := ⟨λ a b, a + -b⟩

example : is_nonneg (10 : myint) := dec_trivial

example : ¬(is_nonneg (-10 : myint)) := dec_trivial

example : [[6, 8]] + [[5, 1]] = [[2, 0]] := dec_trivial

#eval [[6, 8]] + [[5, 36]] -- outputs `-33`.

#eval ((5 - 78) : myint) -- outputs `-73`.

end myint
