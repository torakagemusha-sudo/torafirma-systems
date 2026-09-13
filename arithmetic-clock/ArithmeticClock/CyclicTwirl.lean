import ArithmeticClock.CyclicCharacters
import Mathlib.Data.Matrix.ConjTranspose

set_option autoImplicit false
open scoped BigOperators
open ArithmeticClock.CyclicCharacters

namespace ArithmeticClock.CyclicTwirl

section Characters

variable (N : ℕ) [NeZero N]

/-- Exact multiplicative order survives the faithful standard cyclic character. -/
theorem stdAddChar_orderOf (a : ZMod N) :
    orderOf (ZMod.stdAddChar a) = addOrderOf a := by
  have hinj : Function.Injective (ZMod.stdAddChar (N := N)).toMonoidHom := by
    intro x y h
    exact ZMod.injective_stdAddChar h
  simpa only [AddChar.toMonoidHom_apply,
    orderOf_ofAdd_eq_addOrderOf] using
    orderOf_injective (ZMod.stdAddChar (N := N)).toMonoidHom hinj (Multiplicative.ofAdd a)

/-- Source modulus stays `N`; the stride changes the sampled character order. -/
theorem cyclicCharacter_orderOf_nat (a stride : ℕ) :
    orderOf (cyclicCharacter N (a : ZMod N) (stride : ZMod N)) =
      N / N.gcd (a * stride) := by
  rw [cyclicCharacter_apply, ← Nat.cast_mul, stdAddChar_orderOf,
    ZMod.addOrderOf_coe _ (NeZero.ne N)]

/-- The corresponding phase is a primitive root of its exact sampled order. -/
theorem cyclicCharacter_primitive_nat (a stride : ℕ) :
    IsPrimitiveRoot (cyclicCharacter N (a : ZMod N) (stride : ZMod N))
      (N / N.gcd (a * stride)) := by
  rw [← cyclicCharacter_orderOf_nat]
  exact IsPrimitiveRoot.orderOf _

/-- All returns, not only one proposed period, are characterized exactly. -/
theorem cyclicCharacter_pow_eq_one_iff (a stride k : ℕ) :
    cyclicCharacter N (a : ZMod N) (stride : ZMod N) ^ k = 1 ↔
      N / N.gcd (a * stride) ∣ k := by
  rw [← orderOf_dvd_iff_pow_eq_one, cyclicCharacter_orderOf_nat]

/-- Frequency subtraction is the phase acquired by a conjugated matrix entry. -/
theorem cyclicCharacter_frequency_sub (a b t : ZMod N) :
    cyclicCharacter N a t * (starRingEnd ℂ) (cyclicCharacter N b t) =
      cyclicCharacter N (a - b) t := by
  simpa only [cyclicCharacter_apply, mul_comm] using
    (CyclicCharacters.cyclicCharacter_sub N t a b).symm

/-- Reuses the cyclic orthogonality theorem with time and frequency exchanged. -/
theorem cyclicCharacter_difference_sum (a b : ZMod N) :
    (∑ t : ZMod N, cyclicCharacter N (a - b) t) =
      if a = b then (N : ℂ) else 0 := by
  simpa only [cyclicCharacter_apply, mul_comm] using
    cyclicCharacter_orthogonality N a b

end Characters

section Matrices

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (N : ℕ) [NeZero N]

/-- The actual diagonal cyclic representation on the chosen character basis. -/
noncomputable def diagonalClock (w : ι → ZMod N) (t : ZMod N) : Matrix ι ι ℂ :=
  Matrix.diagonal (fun i => cyclicCharacter N (w i) t)

/-- Matrix conjugation by the diagonal clock and its conjugate transpose. -/
noncomputable def conjugation (w : ι → ZMod N) (t : ZMod N)
    (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  diagonalClock N w t * A * (diagonalClock N w t).conjTranspose

/-- Average over all source-clock times, normalized by the source modulus. -/
noncomputable def twirl (w : ι → ZMod N) (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (N : ℂ)⁻¹ • ∑ t : ZMod N, conjugation N w t A

omit [Fintype ι] in
theorem diagonalClock_zero (w : ι → ZMod N) : diagonalClock N w 0 = 1 := by
  ext i j
  simp [diagonalClock, AddChar.map_zero_eq_one]

theorem diagonalClock_add (w : ι → ZMod N) (s t : ZMod N) :
    diagonalClock N w (s + t) = diagonalClock N w s * diagonalClock N w t := by
  simp only [diagonalClock, Matrix.diagonal_mul_diagonal, AddChar.map_add_eq_mul]

omit [Fintype ι] in
theorem diagonalClock_conjTranspose (w : ι → ZMod N) (t : ZMod N) :
    (diagonalClock N w t).conjTranspose = diagonalClock N w (-t) := by
  simp only [diagonalClock, Matrix.diagonal_conjTranspose,
    CyclicCharacters.cyclicCharacter_neg]
  rfl

/-- The adjoint used in conjugation really is the inverse of the clock. -/
theorem diagonalClock_mul_conjTranspose (w : ι → ZMod N) (t : ZMod N) :
    diagonalClock N w t * (diagonalClock N w t).conjTranspose = 1 := by
  rw [diagonalClock_conjTranspose, ← diagonalClock_add, add_neg_cancel,
    diagonalClock_zero]

theorem conjugation_apply (w : ι → ZMod N) (t : ZMod N)
    (A : Matrix ι ι ℂ) (i j : ι) :
    conjugation N w t A i j = cyclicCharacter N (w i - w j) t * A i j := by
  classical
  simp only [conjugation, diagonalClock, Matrix.diagonal_conjTranspose,
    Matrix.mul_diagonal, Matrix.diagonal_mul, Pi.star_apply]
  change cyclicCharacter N (w i) t * A i j *
    (starRingEnd ℂ) (cyclicCharacter N (w j) t) = _
  rw [← cyclicCharacter_frequency_sub]
  ring

/-- Twirling is exactly the projection onto blocks of equal cyclic characters. -/
theorem twirl_apply (w : ι → ZMod N) (A : Matrix ι ι ℂ) (i j : ι) :
    twirl N w A i j = if w i = w j then A i j else 0 := by
  classical
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  simp only [twirl, Matrix.smul_apply, Matrix.sum_apply, conjugation_apply,
    smul_eq_mul, ← Finset.sum_mul, cyclicCharacter_difference_sum]
  by_cases h : w i = w j
  · simp only [if_pos h]
    rw [← mul_assoc, inv_mul_cancel₀ hN, one_mul]
  · simp only [if_neg h, zero_mul, mul_zero]

/-- Applying the finite average twice changes nothing. -/
theorem twirl_idempotent (w : ι → ZMod N) (A : Matrix ι ι ℂ) :
    twirl N w (twirl N w A) = twirl N w A := by
  ext i j
  simp only [twirl_apply]
  split_ifs <;> rfl

/-- Distinct weights leave precisely the matrix diagonal. -/
theorem twirl_of_injective (w : ι → ZMod N) (hw : Function.Injective w)
    (A : Matrix ι ι ℂ) :
    twirl N w A = Matrix.diagonal (fun i => A i i) := by
  ext i j
  simp only [twirl_apply, hw.eq_iff]
  by_cases h : i = j
  · subst j
    simp
  · simp [h, Matrix.diagonal_apply]

/-- A unit diagonal becomes the identity under a distinct-weight twirl. -/
theorem twirl_eq_one_of_diagonal_one (w : ι → ZMod N) (hw : Function.Injective w)
    (A : Matrix ι ι ℂ) (hdiag : ∀ i, A i i = 1) : twirl N w A = 1 := by
  rw [twirl_of_injective N w hw A]
  simp [hdiag]

/-- The stationary matrices are exactly those supported on equal-weight blocks. -/
theorem stationary_iff_equal_weight_blocks (w : ι → ZMod N) (A : Matrix ι ι ℂ) :
    (∀ t, conjugation N w t A = A) ↔
      ∀ i j, w i ≠ w j → A i j = 0 := by
  constructor
  · intro h i j hij
    have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    have havg : twirl N w A i j = A i j := by
      simp only [twirl, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
      simp only [h, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ hN, one_mul]
    have hz := twirl_apply N w A i j
    rw [if_neg hij] at hz
    exact havg.symm.trans hz
  · intro h t
    ext i j
    rw [conjugation_apply]
    by_cases hij : w i = w j
    · simp [hij, cyclicCharacter_apply, AddChar.map_zero_eq_one]
    · simp only [h i j hij, mul_zero]

end Matrices

section Sixty

/-- The sorted signed eigenweights of the six intrinsic divisor planes for source 60. -/
def weights60 : Fin 12 → ZMod 60 := ![1, 4, 7, 11, 17, 28, 32, 43, 49, 53, 56, 59]

theorem weights60_injective : Function.Injective weights60 := by decide

theorem weights60_ne_zero : ∀ i, weights60 i ≠ 0 := by decide

theorem weights60_ne_half : ∀ i, weights60 i ≠ 30 := by decide

theorem weights60_negation_closed : ∀ i, ∃ j, weights60 j = -weights60 i := by decide

theorem weights60_difference_29 : weights60 0 - weights60 6 = 29 := by decide

theorem weights60_difference_13 : weights60 4 - weights60 1 = 13 := by decide

/-- Weight one makes the actual 60-clock representation faithful in time. -/
theorem diagonalClock60_injective : Function.Injective (diagonalClock 60 weights60) := by
  intro s t h
  have he := congrArg (fun A : Matrix (Fin 12) (Fin 12) ℂ => A 0 0) h
  simp only [diagonalClock, Matrix.diagonal_apply_eq, weights60,
    Matrix.cons_val_zero, cyclicCharacter_apply, one_mul] at he
  exact ZMod.injective_stdAddChar he

/-- Actual frequency 29 at source 60 has exact sampled periods 60, 30, 15. -/
theorem frequency29_sampled_orders :
    orderOf (cyclicCharacter 60 29 1) = 60 ∧
    orderOf (cyclicCharacter 60 29 2) = 30 ∧
    orderOf (cyclicCharacter 60 29 4) = 15 := by
  exact ⟨by simpa using cyclicCharacter_orderOf_nat 60 29 1,
    by simpa using cyclicCharacter_orderOf_nat 60 29 2,
    by simpa using cyclicCharacter_orderOf_nat 60 29 4⟩

/-- Frequency 13 has the same exact three sampled orders. -/
theorem frequency13_sampled_orders :
    orderOf (cyclicCharacter 60 13 1) = 60 ∧
    orderOf (cyclicCharacter 60 13 2) = 30 ∧
    orderOf (cyclicCharacter 60 13 4) = 15 := by
  exact ⟨by simpa using cyclicCharacter_orderOf_nat 60 13 1,
    by simpa using cyclicCharacter_orderOf_nat 60 13 2,
    by simpa using cyclicCharacter_orderOf_nat 60 13 4⟩

theorem frequency29_primitive_roots :
    IsPrimitiveRoot (cyclicCharacter 60 29 1) 60 ∧
    IsPrimitiveRoot (cyclicCharacter 60 29 2) 30 ∧
    IsPrimitiveRoot (cyclicCharacter 60 29 4) 15 := by
  rcases frequency29_sampled_orders with ⟨h1, h2, h4⟩
  exact ⟨by simpa only [h1] using IsPrimitiveRoot.orderOf (cyclicCharacter 60 29 1),
    by simpa only [h2] using IsPrimitiveRoot.orderOf (cyclicCharacter 60 29 2),
    by simpa only [h4] using IsPrimitiveRoot.orderOf (cyclicCharacter 60 29 4)⟩

theorem frequency13_primitive_roots :
    IsPrimitiveRoot (cyclicCharacter 60 13 1) 60 ∧
    IsPrimitiveRoot (cyclicCharacter 60 13 2) 30 ∧
    IsPrimitiveRoot (cyclicCharacter 60 13 4) 15 := by
  rcases frequency13_sampled_orders with ⟨h1, h2, h4⟩
  exact ⟨by simpa only [h1] using IsPrimitiveRoot.orderOf (cyclicCharacter 60 13 1),
    by simpa only [h2] using IsPrimitiveRoot.orderOf (cyclicCharacter 60 13 2),
    by simpa only [h4] using IsPrimitiveRoot.orderOf (cyclicCharacter 60 13 4)⟩

theorem twirl60_diagonal (A : Matrix (Fin 12) (Fin 12) ℂ) :
    twirl 60 weights60 A = Matrix.diagonal (fun i => A i i) :=
  twirl_of_injective 60 weights60 weights60_injective A

theorem twirl60_eq_one (A : Matrix (Fin 12) (Fin 12) ℂ)
    (hdiag : ∀ i, A i i = 1) : twirl 60 weights60 A = 1 :=
  twirl_eq_one_of_diagonal_one 60 weights60 weights60_injective A hdiag

end Sixty

section FiniteField

/-- This prime certifies that `ZMod 61` is a finite field; source 60 itself is not. -/
theorem prime61 : Nat.Prime 61 := by decide

/-- The multiplicative element 2 has exact order 60 in the field with 61 elements. -/
theorem field61_two_order : orderOf (2 : ZMod 61) = 60 := by
  apply (orderOf_eq_iff (by decide : 0 < 60)).mpr
  refine ⟨by decide, ?_⟩
  have hsmall : ∀ m : Fin 60, 0 < m.val → (2 : ZMod 61) ^ m.val ≠ 1 := by decide
  intro m hm hpos
  exact hsmall ⟨m, hm⟩ hpos

theorem field61_two_primitive : IsPrimitiveRoot (2 : ZMod 61) 60 := by
  simpa only [field61_two_order] using IsPrimitiveRoot.orderOf (2 : ZMod 61)

/-- The same multiplicative clock as an explicit unit, with inverse 31 modulo 61. -/
def field61Generator : (ZMod 61)ˣ := ⟨2, 31, by decide, by decide⟩

theorem field61Generator_order : orderOf field61Generator = 60 := by
  rw [← orderOf_units]
  exact field61_two_order

end FiniteField

end ArithmeticClock.CyclicTwirl
