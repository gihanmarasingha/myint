import tactic

@[derive decidable_rel]
private def myintrel : ℕ × ℕ → ℕ × ℕ → Prop := λ a b, a.1 + b.2 = b.1 + a.2

local infix `~` := myintrel

private theorem myintrel.refl : ∀ n : ℕ × ℕ, n ~ n := λ n, rfl

private theorem myintrel.symm : ∀ n m : ℕ × ℕ, n ~ m → m ~ n :=
  λ n m h, by { dsimp [myintrel] at *, symmetry, rw h, }

private theorem myintrel.trans : ∀ n m k : ℕ × ℕ, n ~ m → m ~ k → n ~ k :=
  by { dsimp [myintrel], intros n m k h₁ h₂, linarith, }

private theorem is_equivalence :
  equivalence myintrel := mk_equivalence myintrel myintrel.refl myintrel.symm myintrel.trans

instance myint.setoid : setoid (ℕ × ℕ) := setoid.mk myintrel is_equivalence

def myint := quotient myint.setoid

namespace myint

definition mk (a₁ a₂ : ℕ) : myint := ⟦(a₁, a₂)⟧

local notation `[[` a₁ `,` a₂ `]]` := mk a₁ a₂

example : [[1, 6]] = [[10, 15]] := dec_trivial

@[derive decidable] private def is_nonneg' (n : ℕ × ℕ) : Prop := n.1 ≥ n.2

example : is_nonneg' (10,8) := dec_trivial

/- def is_nonneg (n : myint) : Prop :=
begin
  apply quotient.lift is_nonneg' _ n,
  dsimp [has_equiv.equiv, setoid.r, myintrel, is_nonneg'],
  intros a b h, ext,
  split;
  { intro k, linarith, },
end -/

def prod_nat_to_prod_nat (n : ℕ × ℕ) : ℕ × ℕ := if is_nonneg' n then (n.1-n.2, 0) else (0, n.2-n.1)

example : prod_nat_to_prod_nat (5,7) = (0, 2) := rfl

example : prod_nat_to_prod_nat (13, 4) = (9, 0) := rfl

def prod_nat_to_string (n : ℕ × ℕ) : string :=
  if is_nonneg' n then to_string (n.1-n.2) else  "-" ++ to_string (n.2 - n.1)

lemma prod_nat_of_is_nonneg {n : ℕ × ℕ} (h : is_nonneg' n) :
  prod_nat_to_prod_nat n = (n.1 - n.2, 0) := if_pos h

lemma prod_nat_of_is_neg {n : ℕ × ℕ} (h : ¬(is_nonneg' n)) :
  prod_nat_to_prod_nat n = (0, n.2 - n.1) := if_neg h
  
private lemma aux1 {x y u v : ℕ} (h : y ≤ x) (k : x + v = u + y) : u = x - y + v :=
  (nat.add_sub_cancel u y) ▸ k ▸ (nat.sub_add_comm h)

private lemma aux4 {x y u v : nat} (h : x + v = u + y) (k : x ≥ y) : x - y = u - v :=
by rw [aux1 k h, nat.add_sub_cancel]

/- private lemma aux2 {x y u v : ℕ} (h : y ≤ x) (k : x + v = u + y) : u = v + (x -y) :=
  (aux1 h k).symm ▸ add_comm _ _
 -/
/- def foo (n : myint) : Prop :=
  quotient.lift_on n is_nonneg'
  (λ a b h,
    have k : a.1 + b.2 = b.1 + a.2, from h,
    propext $ iff.intro
    (λ ha, le_iff_exists_add.mpr (exists.intro (a.1-a.2) (aux2 ha k)))
    (λ hb, le_iff_exists_add.mpr (exists.intro (b.1-b.2) (aux2 hb k.symm)))) -/

def myint_to_prod_nat (n : myint) : ℕ × ℕ :=
  quotient.lift_on n prod_nat_to_prod_nat
  ( λ a b h,
    if hnna : (is_nonneg' a) then
    begin
      rw prod_nat_of_is_nonneg hnna,
      dsimp [has_equiv.equiv, setoid.r, myintrel] at h,  dsimp [is_nonneg'] at hnna,
      have hnnb : (is_nonneg' b), by { dsimp [is_nonneg'], linarith, },
      rw prod_nat_of_is_nonneg hnnb,
      ext, { dsimp, exact aux4 h hnna, }, { refl, },
    end
    else
    begin
      rw prod_nat_of_is_neg hnna,
      dsimp [has_equiv.equiv, setoid.r, myintrel] at h,  dsimp [is_nonneg'] at hnna,
      have hnnb : (¬is_nonneg' b), by { dsimp [is_nonneg'], linarith, },
      rw prod_nat_of_is_neg hnnb,
      ext, { refl, }, { dsimp, apply aux4; linarith, },
    end )

example : myint_to_prod_nat [[10, 4]] = (6,0) := rfl

@[derive decidable]
def is_nonneg : myint → Prop := is_nonneg' ∘ myint_to_prod_nat

example : is_nonneg [[10, 3]] := dec_trivial

def myint_to_string : myint → string := prod_nat_to_string ∘ myint_to_prod_nat

instance myint_repr : has_repr myint := ⟨myint_to_string⟩

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

instance has_coe_to_myint : has_coe nat (quotient myint.setoid) := ⟨λ n, [[n,0]]⟩

instance has_one_myint : has_one myint := ⟨[[1, 0]]⟩

instance has_zero_myint : has_zero myint := ⟨[[0, 0]]⟩

private def neg_pair (n : ℕ × ℕ) : myint := [[n.2, n.1]]

@[simp] def neg (n : myint) : quotient myint.setoid :=
begin
  refine quot.lift neg_pair _ _,
  { exact myintrel },
  { intros a b h,
    unfold neg_pair,
    apply quot.sound,
    dsimp [setoid.r, myintrel] at h ⊢,
    linarith [h], },
  { exact n, }
end

instance has_neg_myint' : has_neg myint := ⟨neg⟩

example : - [[5, 9]] = [[9, 5]] := rfl

private def add_pair (n m : ℕ × ℕ) : myint := [[n.1 + m.1, n.2 + m.2]]

def add : myint → myint → myint :=
begin
  apply quotient.lift₂ add_pair,
  dsimp [has_equiv.equiv, setoid.r, myintrel, add_pair],
  intros,
  apply quotient.sound,
  dsimp [has_equiv.equiv, setoid.r, myintrel],
  linarith,
end

instance has_add_myint : has_add myint := ⟨add⟩

instance has_sub_myint : has_sub myint := ⟨λ a b, a + -b⟩

example : is_nonneg (10 : myint) := dec_trivial

example : ¬(is_nonneg (-10 : myint)) := dec_trivial

example : [[6, 8]] + [[5, 1]] = [[2, 0]] := dec_trivial

#eval [[6, 8]] + [[5, 36]] -- outputs `-33`.

#eval ((5 - 78) : myint) -- outputs `-73`.

end myint
