# Myint

## Constructing the `myint` type

In this Lean project, we construct a type `myint` of integers as a quotient of pairs of natural numbers defined via the equivalence relation `~` where
`(x, y) ~ (u, v)` means `x + v = u + y`.

One should think of the pair `(x, y)` of natural numbers as representing the integer `x - y`. This justifies the use of the relation above. Indeed, if we treat `x`, `y`, `u`, and
`v` as integers, then the equation can be rewritten as `x - y = u - v`.

The relation is expressed in Lean as:
```lean
@[derive decidable_rel]
private def myintrel : ℕ × ℕ → ℕ × ℕ → Prop := λ a b, a.1 + b.2 = b.1 + a.2
```

This can be shown to be an equivalence relation via
```lean
local infix `~` := myintrel

private theorem myintrel.refl : ∀ n : ℕ × ℕ, n ~ n := λ n, rfl

private theorem myintrel.symm : ∀ n m : ℕ × ℕ, n ~ m → m ~ n :=
  λ n m h, by { dsimp [myintrel] at *, symmetry, rw h, }

private theorem myintrel.trans : ∀ n m k : ℕ × ℕ, n ~ m → m ~ k → n ~ k :=
  by { dsimp [myintrel], intros n m k h₁ h₂, linarith, }
  
private theorem is_equivalence :
  equivalence myintrel := mk_equivalence myintrel myintrel.refl myintrel.symm myintrel.trans
```

This equivalence relation provides a new instance of the `setoid` class, this being a class that bundles a set and and equivalence relation on the set.
```lean
instance myint.setoid : setoid (ℕ × ℕ) := setoid.mk myintrel is_equivalence
```

With this setoid in hand, we define the type `myint` to be the quotient of `ℕ × ℕ` by the equivalence relation `myintrel`.
```lean
def myint := quotient myint.setoid
```

## Operations on `myint`

To come ...
