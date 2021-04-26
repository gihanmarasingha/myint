import lemmas basic

namespace myint

def five_z : add_subgroup int := add_subgroup.closure ({5} : set ℤ)

def five_mint : add_subgroup myint := add_subgroup.closure ({5} : set myint)

example : five_z.comap (add_equiv.to_add_monoid_hom myint_to_int_add_equiv) = five_mint :=
begin
  let f := add_equiv.to_add_monoid_hom myint_to_int_add_equiv,
  have five_eq : (5 : myint) = [[5,0]] := rfl,
  convert add_subgroup.comap_map_eq f five_mint,
  { simp only [←add_subgroup.gmultiples_eq_closure,five_z, five_mint],
    ext, split,
    { --  Want to show that if `x : ℤ` is in `five_z`, then `x` is in the image of `five_mint`
      --  under `f`.      
      -- There are two cases to consider. Either `x` 'is' `a • 5` or it is `-(1+b) • 5` for `a b : ℕ`.
      rintro ⟨a | b, rfl⟩,
      { use a • [[5,0]], -- We'll show `a • 5` is `f (a • [[5, 0]])`
        split,
        { use a, rw (show [[5,0]] = 5, from dec_trivial), norm_num, },
        { rw nsmul_myint_pair,
          dsimp [myint_to_int_add_equiv, myint_to_int_equiv],
          rw myint_to_int_of_pair, norm_num, } },
      { use (1 + b) • [[0,5]], -- We'll show `-(1+b) • 5` is `f ((1+b) • [[0, 5]])`
        split, 
        { use (int.neg_succ_of_nat b), -- We first show `(1+b) • [[0,5]]` is in `five_myint`.
          conv_lhs { change (int.neg_succ_of_nat b) •ℤ (5 : myint)},
          rw gsmul_neg_succ_of_nat,
          rw [five_eq, nat.succ_eq_add_one, add_comm],
          simp only [nsmul_myint_pair, myint.neg_pair'], }, 
        
        { conv_rhs { change ((int.neg_succ_of_nat b) •ℤ (5 : int)) },  -- Now we show equality.
          rw [gsmul_neg_succ_of_nat, add_comm],
          rw nsmul_myint_pair,
          dsimp [myint_to_int_add_equiv, myint_to_int_equiv], rw myint_to_int_of_pair,
          norm_num, }, }, },
    { --  Want to show that if `x : ℤ` is in the image of `five_mint` under `f`, then
      --  `x ∈ five_z`.   
      -- `x : ℤ` is written as `f (w • 5)` for some `w : ℤ`.
      rintro ⟨_, ⟨w, rfl⟩, rfl⟩, -- We must show `f (w • 5) ∈ five_z`.
      cases w with a b, -- split into cases where `w` 'equals' `a` or `-(1+b)` for `a b : ℕ`.
      { use a,
        dsimp, norm_num,
        rw five_eq, rw nsmul_myint_pair,
        simp [add_monoid.nsmul_zero'],
        dsimp [myint_to_int_add_equiv, myint_to_int_equiv, myint_to_int_of_pair], norm_num,
      },
      { use (-(1+b)),
        dsimp, norm_num, rw [five_eq, nat.succ_eq_add_one, nsmul_myint_pair],
        dsimp [myint_to_int_add_equiv, myint_to_int_equiv, myint_to_int_of_pair], norm_num,
        linarith, }, }, },
  { rw (add_monoid_hom.ker_eq_bot_iff f).mpr (by apply add_equiv.injective),
    rw [sup_bot_eq], },
end










end myint