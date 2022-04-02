/-
Copyright (c) 2020 The Xena project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard.
Thanks: Imperial College London, leanprover-community
-/

-- Import levels 1 to 3
import complex.Level_03_conj

/-! 

# Level 4: Norms

Define `norm_sq : ℂ → ℝ` by defining `norm_sq(z)` to be
`re(z)*re(z)+im(z)*im(z)` and see what you can prove about it.

-/

namespace complex

/-- The real number which is the squared norm of z -/
def norm_sq (z : ℂ) : ℝ := re(z)*re(z)+im(z)*im(z)

/-! ## Behaviour with respect to 0, 1 and I -/

@[simp] lemma norm_sq_zero : norm_sq 0 = 0 := 
begin
  rw norm_sq,
  simp,
end
@[simp] lemma norm_sq_one : norm_sq 1 = 1 := 
begin
  rw norm_sq,
  simp,
end
@[simp] lemma norm_sq_I : norm_sq I = 1 := 
begin
  rw norm_sq,
  simp,
end

/-! ## Behaviour with respect to *, + and - -/

@[simp] lemma norm_sq_mul (z w : ℂ) : norm_sq (z * w) = norm_sq z * norm_sq w :=
begin
  rw norm_sq,
  rw norm_sq,
  rw norm_sq,
  simp,
  ring,
end

lemma norm_sq_add (z w : ℂ) : norm_sq (z + w) =
  norm_sq z + norm_sq w + 2 * (z * conj w).re :=
begin
  rw norm_sq,
  rw norm_sq,
  rw norm_sq,
  simp,
  ring,
end

@[simp] lemma norm_sq_neg (z : ℂ) : norm_sq (-z) = norm_sq z :=
begin
  rw norm_sq,
  rw norm_sq,
  simp,
end

/-! ## Behaviour with respect to `conj` -/

@[simp] lemma norm_sq_conj (z : ℂ) : norm_sq (conj z) = norm_sq z :=
begin
  rw norm_sq,
  rw norm_sq,
  simp,
end

/-! ## Behaviour with respect to real numbers` -/

@[simp] lemma norm_sq_of_real (r : ℝ) : norm_sq r = r * r :=
begin
  rw norm_sq,
  simp,
end

theorem mul_conj (z : ℂ) : z * conj z = norm_sq z :=
begin
  rw norm_sq,
  ext,
  simp,
  simp,
  ring,
end

/-! ## Behaviour with respect to real 0, ≤, < and so on -/

-- Warning: you will have to know something about Lean's API for
-- real numbers to solve these ones. If you turn the statements about
-- complex numbers into statements about real numbers, you'll find
-- they're of the form "prove $$x^2+y^2\geq0$$" with `x` and `y` real.

lemma norm_nonneg (x y : ℝ) : 0 ≤ x * x + y * y :=
begin
  nlinarith,
end

lemma norm_sq_nonneg (z : ℂ) : 0 ≤ norm_sq z := 
begin
  rw norm_sq,
  exact (norm_nonneg z.re z.im),
end

lemma norm_zero (x y : ℝ) : x*x + y*y = 0 → x = 0 ∧ y = 0 :=
begin
  intro h,
  split,
  nlinarith,
  nlinarith,
end

@[simp] lemma norm_sq_eq_zero {z : ℂ} : norm_sq z = 0 ↔ z = 0 :=
begin
  split,
  intro h,
  rw norm_sq at h,
  ext,
  simp [h],
  exact (norm_zero z.re z.im h).left,
  exact (norm_zero z.re z.im h).right,

  intro h,
  simp [h],
end

@[simp] lemma norm_sq_pos {z : ℂ} : 0 < norm_sq z ↔ z ≠ 0 :=
begin
  split,
  intros h h',
  rw h' at h,
  simp * at h,
  linarith [h],
  intro h,
  refine not_le.mp _,
  intro h',
  apply h,
  have h'' := (norm_sq_nonneg z),
  have h''' : norm_sq z = 0,
  linarith [h', h''],

  rw ← norm_sq_eq_zero,
  exact h''',
end

lemma re_sq_le_norm_sq (z : ℂ) : z.re * z.re ≤ norm_sq z :=
begin
  rw norm_sq,
  nlinarith,
end

lemma im_sq_le_norm_sq (z : ℂ) : z.im * z.im ≤ norm_sq z :=
begin
  rw norm_sq,
  nlinarith,
end

end complex
