import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Tactic

set_option autoImplicit false
open scoped BigOperators

namespace ArithmeticClock.CyclicCharacters

variable (N : ℕ) [NeZero N]

/-- The frequency `a` on the cyclic group of order `N`. -/
noncomputable def cyclicCharacter (a : ZMod N) : AddChar (ZMod N) ℂ :=
  ZMod.stdAddChar.mulShift a

theorem cyclicCharacter_apply (a x : ZMod N) :
    cyclicCharacter N a x = ZMod.stdAddChar (a * x) := rfl

theorem cyclicCharacter_intCast (a x : ℤ) :
    cyclicCharacter N (a : ZMod N) (x : ZMod N) =
      Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * (x : ℂ) / (N : ℂ)) := by
  rw [cyclicCharacter_apply, ← Int.cast_mul, ZMod.stdAddChar_coe, Int.cast_mul]
  congr 1
  ring

theorem cyclicCharacter_orthogonality (x y : ZMod N) :
    (∑ a : ZMod N, cyclicCharacter N a (x - y)) = if x = y then (N : ℂ) else 0 := by
  classical
  simpa only [cyclicCharacter, AddChar.mulShift_apply, sub_eq_zero,
    ZMod.card, Nat.cast_ite, Nat.cast_zero] using
      AddChar.sum_mulShift (x - y) (ZMod.isPrimitive_stdAddChar N)

theorem cyclicCharacter_sub (a x y : ZMod N) :
    cyclicCharacter N a (x - y) =
      cyclicCharacter N a x * (starRingEnd ℂ) (cyclicCharacter N a y) := by
  rw [AddChar.map_sub_eq_div, div_eq_mul_inv, AddChar.inv_apply_eq_conj]

theorem cyclicCharacter_neg (a x : ZMod N) :
    cyclicCharacter N a (-x) = (starRingEnd ℂ) (cyclicCharacter N a x) := by
  rw [AddChar.map_neg_eq_inv, AddChar.inv_apply_eq_conj]

end ArithmeticClock.CyclicCharacters
