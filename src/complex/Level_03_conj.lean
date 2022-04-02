/-
Copyright (c) 2020 The Xena project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Kevin Buzzard
Thanks: Imperial College London, leanprover-community
-/

-- import levels 1 and 2
import complex.Level_02_I

/-! # Level 3: Complex conjugation -/

namespace complex

-- First complete the definition using `complex.mk` or `⟨x, y⟩` notation

/-- The complex conjugate of a complex number -/
def conj (z : ℂ) : ℂ := ⟨re z, -im z⟩

-- Now prove how it interacts with everything else

/-! ## Real and imaginary parts -/

@[simp] lemma conj_re (z : ℂ) : re(conj z) = re(z) := rfl
@[simp] lemma conj_im (z : ℂ) : im(conj z) = -im(z) := rfl

/-! ## Behaviour with respect to 0, 1 and I -/

@[simp] lemma conj_zero : conj 0 = 0 := 
begin
  unfold conj,
  simp,
  refl,
end
@[simp] lemma conj_one : conj 1 = 1 := 
begin
  unfold conj,
  simp,
  refl,
end
@[simp] lemma conj_I : conj I = -I := 
begin
  unfold conj,
  simp,
  ext,
  simp,
  simp,
end
@[simp] lemma conj_neg_I : conj (-I) = I := 
begin
  ext,
  simp,
  simp,
end

/-! ## Behaviour with respect to +, - and * -/

@[simp] lemma conj_add (z w : ℂ) : conj (z + w) = conj z + conj w :=
begin
  ext,
  simp,
  simp,
  ring,
end

@[simp] lemma conj_neg (z : ℂ) : conj (-z) = -conj z := 
begin
  ext,
  simp,
  simp,
end


@[simp] lemma conj_mul (z w : ℂ) : conj (z * w) = conj z * conj w :=
begin
  ext,
  simp,
  simp,
  ring,
end

/-! ## Behaviour with respect to real numbers -/

@[simp] lemma conj_of_real (r : ℝ) : conj r = r := 
begin
  ext,
  simp,
  simp,
end

lemma im_eq_zero_of_eq_conj {z : ℂ} : conj z = z → im z = 0 := 
begin
  intro h,
  unfold conj at h,
  rw ext_iff at h,
  cases h with h1 h2,
  simp * at h2,
  linarith,
end

lemma eq_conj_iff_real {z : ℂ} : conj z = z ↔ ∃ r : ℝ, z = r :=
begin
  split,
  intro h,
  use re z,
  have h' := im_eq_zero_of_eq_conj h,
  ext,
  simp,
  simp,
  exact h',

  intro h,
  cases h with x h',
  rw h',
  simp,
end

lemma eq_conj_iff_re {z : ℂ} : conj z = z ↔ (z.re : ℂ) = z :=
begin
  split,
  intro h,
  have h' := im_eq_zero_of_eq_conj h,
  ext,
  simp,
  simp,
  rw eq_comm,
  exact h',

  intro h,
  ext,
  simp,
  simp,
  rw ext_iff at h,
  cases h with h1 h2,
  have h' : im z = 0,
  exact h2.symm,

  linarith,
end

theorem add_conj (z : ℂ) : z + conj z = (2 * z.re : ℝ) :=
begin
  ext,
  simp,
  ring,
  exact mul_comm 2 z.re,

  simp,
  left,
  exact bit0_zero,
end


/-! ## Properties of the `conj` map -/

@[simp] lemma conj_conj (z : ℂ) : conj (conj z) = z :=
begin
  ext,
  simp,
  simp,
end

lemma conj_inj {z w : ℂ} : conj z = conj w ↔ z = w :=
begin 
  split,
  intro h,
  rw ext_iff at h,
  simp at h,
  ext,
  exact h.left,
  exact h.right,

  intro h,
  simp [h],
end

@[simp] lemma conj_eq_zero {z : ℂ} : conj z = 0 ↔ z = 0 :=
begin
  split,
  intro h,
  rw ext_iff at h,
  unfold conj at h,
  ext,
  simp [h],
  simp * at h,
  simp [h],

  intro h,
  ext,
  simp [h],
  simp [h],
end

/-

A ring homomorphism in Lean is the following collection
of data: a map, and the proof that it commutes with
the ring structures in the obvious way. Here we observe
that the work we've done is enough to define the
ring homomorphism complex conjugation.

-/

/-- the ring homomorphism complex conjugation -/
def Conj : ℂ →+* ℂ :=
{ to_fun := conj,
  map_zero' := conj_zero,
  map_one' := conj_one,
  map_add' := conj_add,
  map_mul' := conj_mul
}

-- Two optional lemmas which computer scientists like,
-- giving us easy access to some basic properties
-- of conj

open function

lemma conj_involutive : involutive conj := 
begin 
  unfold involutive,
  intro z,
  simp,
end

lemma conj_bijective : bijective conj := 
begin
  unfold bijective,
  split,
  unfold injective,
  intros z1 z2 h,
  rw ext_iff at h,
  simp at h,
  ext,
  simp [h],
  simp [h],

  unfold surjective,
  intro z,
  use conj z,
  simp,
end

end complex
