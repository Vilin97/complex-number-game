/-
Copyright (c) 2020 The Xena project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard.
Thanks: Imperial College London, leanprover-community
-/

-- import the definition and basic properties of ℂ
import complex.Level_00_basic

/-! # Level 1 : the map from ℝ to ℂ

This file sets up the coercion from the reals to the complexes,
sending `r` to `⟨r, 0⟩`. Mathematically it is straightforward.

All the proofs below are sorried. You can try them in tactic mode
by replacing `sorry` with `begin sorry end` and then starting to write 
tactics in the `begin end` block.

-/

namespace complex

-- fill in the definition of the map below,
-- sending the real number r to the complex number ⟨r, 0⟩

/-- The canonical map from ℝ to ℂ. -/
def of_real (r : ℝ) : ℂ := ⟨r, 0⟩

/-
We make this map into a *coercion*, which means that if `(r : ℝ)` is a real
number, then `(r : ℂ)` or `(↑r : ℂ)` will indicate the corresponding
complex number with no imaginary part. This is the notation we shall
use in our `simp` lemmas.
-/

/-- The coercion from ℝ to ℂ sending `r` to the complex number `⟨r, 0⟩` -/
instance : has_coe ℝ ℂ := ⟨of_real⟩

/-
As usual, we need to train the `simp` tactic. But we also need to train
the `norm_cast` tactic. The `norm_cast` tactic enables Lean to prove
results like r^2=2*s for reals `r` and `s`, if it knows that
`(r : ℂ)^2 = 2*(s : ℂ)`. Such results are intuitive for matheamticians
but involve "invisible maps" in Lean
-/

@[simp, norm_cast] lemma of_real_re (r : ℝ) : (r : ℂ).re = r := rfl
@[simp, norm_cast] lemma of_real_im (r : ℝ) : (r : ℂ).im = 0 := rfl

-- The map from the reals to the complexes is injective, something we
-- write in iff form so `simp` can use it; `simp` also works on `iff` goals.

@[simp, norm_cast] theorem of_real_inj {r s : ℝ} : (r : ℂ) = s ↔ r = s := 
begin
  split,
  {intro h,
  cases h,
  refl},
  {intro h,
  ext,
  simp,
  exact h,
  simp},
end

-- what does norm_cast do?? Here are two examples of usage:



example (r s : ℝ) (h : (r : ℂ) = s) : r = s :=
begin
  norm_cast at h,
  exact h,
end

example (r s : ℝ) (h : r = s) : (r : ℂ) = (s : ℂ) :=
begin
  norm_cast,
  exact h,
end



/-
We now go through all the basic constants and constructions we've defined so
far, namely 0, 1, +, -, *, and tell the simplifier how they behave with respect
to this new function. 
-/

/-! ## zero -/

@[simp, norm_cast] lemma of_real_zero : ((0 : ℝ) : ℂ) = 0 := rfl

@[simp] theorem of_real_eq_zero {r : ℝ} : (r : ℂ) = 0 ↔ r = 0 := 
begin
  norm_cast,
end

theorem of_real_ne_zero {r : ℝ} : (r : ℂ) ≠ 0 ↔ r ≠ 0 := 
begin
  norm_cast,
end

/-! ## one -/

@[simp, norm_cast] lemma of_real_one : ((1 : ℝ) : ℂ) = 1 := 
begin
  refl,
end

/-! ## add -/

@[simp, norm_cast] lemma of_real_add (r s : ℝ) : ((r + s : ℝ) : ℂ) = r + s :=
begin
  ext,
  simp,
  simp,
end

/-! ## neg -/

@[simp, norm_cast] lemma of_real_neg (r : ℝ) : ((-r : ℝ) : ℂ) = -r :=
begin
  sorry
end

/-! ## mul -/

@[simp, norm_cast] lemma of_real_mul (r s : ℝ) : ((r * s : ℝ) : ℂ) = r * s :=
begin
  sorry
end

/-- The canonical ring homomorphism from ℝ to ℂ -/
def Of_real : ℝ →+* ℂ :=
{ to_fun := coe, -- use the coercion from ℝ to ℂ
  map_zero' := of_real_zero,
  map_one' := of_real_one,
  map_add' := of_real_add,
  map_mul' := of_real_mul,
}

/-! ## numerals.

This is quite a computer-sciency bit.

These last two lemmas are to do with the canonical map from numerals
into the complexes, e.g. `(23 : ℂ)`. Lean stores the numeral in binary.
See for example

set_option pp.numerals false
#check (37 : ℂ)-- bit1 (bit0 (bit1 (bit0 (bit0 has_one.one)))) : ℂ

`bit0 x` is defined to be `x + x`, and `bit1 x` is defined to be `bit0 x + 1`.

We need these results so that `norm_cast` can prove results such
as (↑(37 : ℝ) : ℂ) = 37 : ℂ (i.e. coercion commutes with numerals)

-/

@[simp, norm_cast] lemma of_real_bit0 (r : ℝ) : ((bit0 r : ℝ) : ℂ) = bit0 r :=
sorry
@[simp, norm_cast] lemma of_real_bit1 (r : ℝ) : ((bit1 r : ℝ) : ℂ) = bit1 r :=
sorry

end complex

/-! ## norm_cast examples 

The idea is that the "invisible map" from the reals to the complexes should not
create any trouble to mathematicians who just want things to work as normal

https://xenaproject.wordpress.com/2020/04/30/the-invisible-map/



example (a b c : ℝ) : ((a * b : ℝ) : ℂ) * c = (a : ℂ) * b * c :=
begin
  norm_cast,
end

example (a b c : ℝ) : ((a : ℂ) + b) * c = ((a + b) * c : ℝ) :=
begin
  norm_cast,
end

example : (37 : ℂ) = (37 : ℝ) :=
begin
  norm_cast,
end

-/
