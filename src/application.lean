import lemmas basic

namespace myint

example (a : nat) : a • (0 : myint) = (0 : myint) := smul_zero a

def five_z : add_subgroup int := add_subgroup.closure ({5} : set ℤ)

def five_mint : add_subgroup myint := add_subgroup.closure ({5} : set myint)

example (a b : int) : (-a - b) = -(a+b) := (neg_add' a b).symm

-- `f` is the `add_monoid` homomorphism from `mint` to `int` induced by the equivalence
-- `myint_to_int_add_equiv`.
abbreviation f := add_equiv.to_add_monoid_hom myint_to_int_add_equiv -- abbreviate the homom to `f`.

/-
The pullback of `five_z` along `f`  is `five_mint`.
-/
example : five_z.comap f = five_mint :=
begin
  have five_eq : (5 : myint) = [[5,0]] := rfl,
  convert add_subgroup.comap_map_eq f five_mint, swap,
  { rw (add_monoid_hom.ker_eq_bot_iff f).mpr (by apply add_equiv.injective),
    rw [sup_bot_eq], },
  simp only [←add_subgroup.gmultiples_eq_closure,five_z, five_mint],
  ext, split,
  { --  Want to show that if `x : ℤ` is in `five_z`, then `x` is in the image of `five_mint` under `f`.      
    rintro ⟨a | b, rfl⟩, -- There are two cases to consider. Either `x` 'is' `a • 5` or it is `-(1+b) • 5` for `a b : ℕ`.
    { use a • [[5,0]], -- We'll show `a • 5` is `f (a • [[5, 0]])`
      split,
      { use a, rw ←five_eq, conv_lhs { change (a) •ℤ (5 : myint)}, norm_num, },
      { rw nsmul_myint_pair, rw (show [[a • 5, a • 0]] = [[a * 5, 0]], from rfl), 
        dsimp [myint_to_int_add_equiv, myint_to_int_equiv],
        rw myint_to_int_of_pair, conv_rhs { change (a) •ℤ (5 : int)}, simp, } },
    { use (1 + b) • [[0,5]], -- We'll show `-(1+b) • 5` is `f ((1+b) • [[0, 5]])`
      split, 
      { use (int.neg_succ_of_nat b), -- We first show `(1+b) • [[0,5]]` is in `five_myint`.
        conv_lhs { change (int.neg_succ_of_nat b) •ℤ (5 : myint)},
        rw gsmul_neg_succ_of_nat,
        rw [five_eq, nat.succ_eq_add_one, add_comm],
        simp only [nsmul_myint_pair, myint.neg_pair'], }, 
      
      { conv_rhs { change ((int.neg_succ_of_nat b) •ℤ (5 : int)) },  -- Now we show equality.
        rw [gsmul_neg_succ_of_nat, add_comm, nsmul_myint_pair],
        dsimp [myint_to_int_add_equiv, myint_to_int_equiv, myint_to_int_of_pair],
        simp only [zero_sub, int.coe_nat_zero, mul_eq_mul_left_iff, nsmul_eq_mul, bit1_eq_bit1, int.coe_nat_succ,
          neg_inj, zero_add, int.nat_cast_eq_coe_nat, mul_zero, int.coe_nat_bit1, int.coe_nat_mul], -- found by `squeeze_simp`.
        left, refl, }, }, },
  { --  Want to show that if `x : ℤ` is in the image of `five_mint` under `f`, then `x ∈ five_z`.   
    -- `x : ℤ` is written as `f (w • 5)` for some `w : ℤ`. We must show `f (w • 5) ∈ five_z`.
    rintro ⟨_, ⟨a | b, rfl⟩, rfl⟩, -- Split into cases where `w` 'equals' `a` or `-(1+b)` for `a b : ℕ`.
    { use a, conv_lhs { change (a •ℤ (5 :int)) },
      rw five_eq,
      simp only [add_equiv.coe_to_add_monoid_hom, int.coe_nat_eq_zero, mul_eq_mul_left_iff, nsmul_eq_mul, int.of_nat_eq_coe,
          gsmul_coe_nat, int.nat_cast_eq_coe_nat, add_monoid_hom.map_nsmul], -- found using `squeeze_simp`.
      left, dsimp [myint_to_int_add_equiv, myint_to_int_equiv, myint_to_int_of_pair], refl, },
    { use (-(1+b)), conv_lhs { change (-(1+b) •ℤ (5 :int)) }, 
      simp only [gsmul_int_int, gsmul_neg_succ_of_nat, add_equiv.coe_to_add_monoid_hom, add_equiv.map_neg, neg_add_rev, int.add_neg_one], -- found using `squeeze_simp`.
      rw [five_eq, nat.succ_eq_add_one, nsmul_myint_pair], 
      dsimp [myint_to_int_add_equiv, myint_to_int_equiv, myint_to_int_of_pair],
      rw [←neg_add', mul_zero, sub_zero], refl, }, },
end

end myint