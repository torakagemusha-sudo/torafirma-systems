import Mathlib.Data.Real.Sqrt
import Mathlib.NumberTheory.Divisors
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic

set_option autoImplicit false

namespace ArithmeticClock.DenseCarrier

noncomputable section

/-- The actual positive-divisor count, including its conventional value at zero. -/
def divisorCount (n : ℕ) : ℕ := n.divisors.card

/-- The divisor-correlation carrier. Our concrete entries all have positive indices. -/
def kernel (a b : ℕ) : ℝ :=
  (divisorCount (Nat.gcd a b) : ℝ) /
    Real.sqrt ((divisorCount a : ℝ) * (divisorCount b : ℝ))

/-- Ordered crossblock of the actual arithmetic carrier. -/
def crossBlock (r c : ℕ × ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![kernel r.1 c.1, kernel r.1 c.2; kernel r.2 c.1, kernel r.2 c.2]

def normSq (A : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  A 0 0 ^ 2 + A 0 1 ^ 2 + A 1 0 ^ 2 + A 1 1 ^ 2

def inner (A B : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  A 0 0 * B 0 0 + A 0 1 * B 0 1 + A 1 0 * B 1 0 + A 1 1 * B 1 1

def differenceWeight (A : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  (A 0 0 + A 1 1) ^ 2 + (A 1 0 - A 0 1) ^ 2

def sumWeight (A : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  (A 0 0 - A 1 1) ^ 2 + (A 1 0 + A 0 1) ^ 2

def rotation (c s : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![c, -s; s, c]

/-- Independent left and right plane rotations, with the right transpose. -/
def rotateBlock (c s d t : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ) :=
  rotation c s * A * (rotation d t).transpose

theorem normSq_sub (A B : Matrix (Fin 2) (Fin 2) ℝ) :
    normSq (A - B) = normSq A + normSq B - 2 * inner B A := by
  simp only [normSq, inner, Matrix.sub_apply]
  ring

theorem weights_sum (A : Matrix (Fin 2) (Fin 2) ℝ) :
    differenceWeight A + sumWeight A = 2 * normSq A := by
  unfold differenceWeight sumWeight normSq
  ring

theorem differenceWeight_nonneg (A : Matrix (Fin 2) (Fin 2) ℝ) :
    0 ≤ differenceWeight A := by
  exact add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem sumWeight_nonneg (A : Matrix (Fin 2) (Fin 2) ℝ) :
    0 ≤ sumWeight A := by
  exact add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem normSq_rotateBlock (c s d t : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    normSq (rotateBlock c s d t A) =
      (c ^ 2 + s ^ 2) * (d ^ 2 + t ^ 2) * normSq A := by
  simp [normSq, rotateBlock, rotation, Matrix.mul_apply, Matrix.vecMul, dotProduct,
    Fin.sum_univ_two]
  ring

theorem inner_rotateBlock (c s d t : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    2 * inner A (rotateBlock c s d t A) =
      differenceWeight A * (c * d + s * t) + sumWeight A * (c * d - s * t) := by
  simp [inner, rotateBlock, rotation, differenceWeight, sumWeight,
    Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  ring

/-- Exact two-frequency decomposition of the squared Frobenius block displacement. -/
theorem displacement_decomposition (α β : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    normSq (rotateBlock (Real.cos α) (Real.sin α) (Real.cos β) (Real.sin β) A - A) =
      differenceWeight A * (1 - Real.cos (α - β)) +
        sumWeight A * (1 - Real.cos (α + β)) := by
  rw [normSq_sub, normSq_rotateBlock, Real.cos_sq_add_sin_sq,
    Real.cos_sq_add_sin_sq, one_mul, one_mul]
  rw [inner_rotateBlock, Real.cos_sub, Real.cos_add]
  have hw := weights_sum A
  nlinarith

/-- The common N=60 crossblock in the ordered divisor-plane bases. -/
def block60 : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 / Real.sqrt 2, 1 / (2 * Real.sqrt 2);
    1 / Real.sqrt 6, 2 / Real.sqrt 6]

theorem kernel_nonneg (a b : ℕ) : 0 ≤ kernel a b := by
  unfold kernel
  positivity

theorem kernel_one_two : kernel 1 2 = 1 / Real.sqrt 2 := by
  have h1 : divisorCount 1 = 1 := by decide
  have h2 : divisorCount 2 = 2 := by decide
  norm_num [kernel, h1, h2]

theorem reciprocal_sqrt_two : 1 / Real.sqrt 2 = Real.sqrt 2 / 2 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hn : Real.sqrt 2 ≠ 0 := by positivity
  field_simp

theorem reciprocal_sqrt_six : 1 / Real.sqrt 6 = Real.sqrt 6 / 6 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num)
  have hn : Real.sqrt 6 ≠ 0 := by positivity
  field_simp

theorem sqrt_two_mul_sqrt_six : Real.sqrt 2 * Real.sqrt 6 = 2 * Real.sqrt 3 := by
  rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num
  rw [show (12 : ℝ) = 4 * 3 by norm_num, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
  norm_num

theorem block60_differenceWeight : differenceWeight block60 = 35 / 24 + Real.sqrt 3 / 2 := by
  have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have h6 := Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num)
  have h26 := sqrt_two_mul_sqrt_six
  have hr2 := reciprocal_sqrt_two
  have hr6 := reciprocal_sqrt_six
  have hr22 : 1 / (2 * Real.sqrt 2) = Real.sqrt 2 / 4 := by
    calc
      1 / (2 * Real.sqrt 2) = (1 / Real.sqrt 2) / 2 := by ring
      _ = Real.sqrt 2 / 4 := by rw [hr2]; ring
  have hr62 : 2 / Real.sqrt 6 = Real.sqrt 6 / 3 := by
    calc
      2 / Real.sqrt 6 = 2 * (1 / Real.sqrt 6) := by ring
      _ = Real.sqrt 6 / 3 := by rw [hr6]; ring
  change (1 / Real.sqrt 2 + 2 / Real.sqrt 6) ^ 2 +
    (1 / Real.sqrt 6 - 1 / (2 * Real.sqrt 2)) ^ 2 = _
  rw [hr2, hr22, hr6, hr62]
  nlinarith

theorem block60_sumWeight : sumWeight block60 = 35 / 24 - Real.sqrt 3 / 2 := by
  have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have h6 := Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num)
  have h26 := sqrt_two_mul_sqrt_six
  have hr2 := reciprocal_sqrt_two
  have hr6 := reciprocal_sqrt_six
  have hr22 : 1 / (2 * Real.sqrt 2) = Real.sqrt 2 / 4 := by
    calc
      1 / (2 * Real.sqrt 2) = (1 / Real.sqrt 2) / 2 := by ring
      _ = Real.sqrt 2 / 4 := by rw [hr2]; ring
  have hr62 : 2 / Real.sqrt 6 = Real.sqrt 6 / 3 := by
    calc
      2 / Real.sqrt 6 = 2 * (1 / Real.sqrt 6) := by ring
      _ = Real.sqrt 6 / 3 := by rw [hr6]; ring
  change (1 / Real.sqrt 2 - 2 / Real.sqrt 6) ^ 2 +
    (1 / Real.sqrt 6 + 1 / (2 * Real.sqrt 2)) ^ 2 = _
  rw [hr2, hr22, hr6, hr62]
  nlinarith

theorem block60_differenceWeight_pos : 0 < differenceWeight block60 := by
  rw [block60_differenceWeight]
  positivity

theorem block60_sumWeight_pos : 0 < sumWeight block60 := by
  rw [block60_sumWeight]
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hn := Real.sqrt_nonneg (3 : ℝ)
  nlinarith

/-- A uniform positive active coefficient, without assumptions on the other two entries. -/
theorem differenceWeight_ge_half (A : Matrix (Fin 2) (Fin 2) ℝ)
    (ha : A 0 0 = 1 / Real.sqrt 2) (hd : 0 ≤ A 1 1) :
    (1 : ℝ) / 2 ≤ differenceWeight A := by
  have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hn := Real.sqrt_nonneg (2 : ℝ)
  rw [reciprocal_sqrt_two] at ha
  have hap : 0 ≤ A 0 0 := by rw [ha]; positivity
  have hprod := mul_nonneg hap hd
  unfold differenceWeight
  nlinarith [sq_nonneg (A 1 1), sq_nonneg (A 1 0 - A 0 1)]

/-- The actual dense carrier supplies the uniform coefficient for every such ordered pair. -/
theorem differenceWeight_crossBlock_one_ge_half (n m : ℕ) :
    (1 : ℝ) / 2 ≤ differenceWeight (crossBlock (1, n) (2, m)) := by
  apply differenceWeight_ge_half
  · simpa [crossBlock] using kernel_one_two
  · simpa [crossBlock] using kernel_nonneg n m

theorem divisorCounts60 :
    divisorCount 1 = 1 ∧ divisorCount 2 = 2 ∧ divisorCount 3 = 2 ∧
      divisorCount 6 = 4 ∧ divisorCount 10 = 4 ∧ divisorCount 20 = 6 ∧
        divisorCount 30 = 8 ∧ divisorCount 60 = 12 := by
  decide

theorem crossBlock_1_60_2_30 : crossBlock (1, 60) (2, 30) = block60 := by
  obtain ⟨h1, h2, h3, h6, h10, h20, h30, h60⟩ := divisorCounts60
  have hs8 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
    rw [show (8 : ℝ) = 4 * 2 by norm_num, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  have hs24 : Real.sqrt 24 = 2 * Real.sqrt 6 := by
    rw [show (24 : ℝ) = 4 * 6 by norm_num, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  have hs96 : Real.sqrt 96 = 4 * Real.sqrt 6 := by
    rw [show (96 : ℝ) = 16 * 6 by norm_num, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16)]
    norm_num
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [crossBlock, kernel, block60, h1, h2, h30, h60, hs8, hs24, hs96] <;> ring

theorem crossBlock_3_20_6_10 : crossBlock (3, 20) (6, 10) = block60 := by
  obtain ⟨h1, h2, h3, h6, h10, h20, h30, h60⟩ := divisorCounts60
  have hs8 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
    rw [show (8 : ℝ) = 4 * 2 by norm_num, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  have hs24 : Real.sqrt 24 = 2 * Real.sqrt 6 := by
    rw [show (24 : ℝ) = 4 * 6 by norm_num, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [crossBlock, kernel, block60, h1, h2, h3, h6, h10, h20, hs8, hs24] <;> ring

theorem block60_displacement (α β : ℝ) :
    normSq (rotateBlock (Real.cos α) (Real.sin α) (Real.cos β) (Real.sin β) block60 - block60) =
      (35 / 24 + Real.sqrt 3 / 2) * (1 - Real.cos (α - β)) +
        (35 / 24 - Real.sqrt 3 / 2) * (1 - Real.cos (α + β)) := by
  rw [displacement_decomposition, block60_differenceWeight, block60_sumWeight]

theorem normSq_nonneg (A : Matrix (Fin 2) (Fin 2) ℝ) : 0 ≤ normSq A := by
  unfold normSq
  positivity

theorem normSq_eq_zero_iff (A : Matrix (Fin 2) (Fin 2) ℝ) : normSq A = 0 ↔ A = 0 := by
  constructor
  · intro h
    unfold normSq at h
    have h00 : A 0 0 = 0 := (sq_eq_zero_iff).mp (by
      nlinarith [sq_nonneg (A 0 1), sq_nonneg (A 1 0), sq_nonneg (A 1 1)])
    have h01 : A 0 1 = 0 := (sq_eq_zero_iff).mp (by
      nlinarith [sq_nonneg (A 0 0), sq_nonneg (A 1 0), sq_nonneg (A 1 1)])
    have h10 : A 1 0 = 0 := (sq_eq_zero_iff).mp (by
      nlinarith [sq_nonneg (A 0 0), sq_nonneg (A 0 1), sq_nonneg (A 1 1)])
    have h11 : A 1 1 = 0 := (sq_eq_zero_iff).mp (by
      nlinarith [sq_nonneg (A 0 0), sq_nonneg (A 0 1), sq_nonneg (A 1 0)])
    ext i j
    fin_cases i <;> fin_cases j <;> simp_all
  · rintro rfl
    norm_num [normSq]

/-- Two strictly positive active weights determine the block stabilizer exactly. -/
theorem rotateBlock_eq_iff (α β : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hd : 0 < differenceWeight A) (hs : 0 < sumWeight A) :
    rotateBlock (Real.cos α) (Real.sin α) (Real.cos β) (Real.sin β) A = A ↔
      Real.cos (α - β) = 1 ∧ Real.cos (α + β) = 1 := by
  have hminus : 0 ≤ 1 - Real.cos (α - β) := sub_nonneg.mpr (Real.cos_le_one _)
  have hplus : 0 ≤ 1 - Real.cos (α + β) := sub_nonneg.mpr (Real.cos_le_one _)
  constructor
  · intro h
    have he := displacement_decomposition α β A
    rw [h, sub_self] at he
    norm_num [normSq] at he
    have hdp := mul_nonneg hd.le hminus
    have hsp := mul_nonneg hs.le hplus
    have hdz : differenceWeight A * (1 - Real.cos (α - β)) = 0 := by linarith
    have hsz : sumWeight A * (1 - Real.cos (α + β)) = 0 := by linarith
    exact ⟨by linarith [(mul_eq_zero.mp hdz).resolve_left (ne_of_gt hd)],
      by linarith [(mul_eq_zero.mp hsz).resolve_left (ne_of_gt hs)]⟩
  · rintro ⟨hminus, hplus⟩
    apply sub_eq_zero.mp
    apply (normSq_eq_zero_iff _).mp
    rw [displacement_decomposition, hminus, hplus]
    ring

/-- Unconditional exact stabilizer of the concrete N=60 crossblock. -/
theorem block60_stabilizer (α β : ℝ) :
    rotateBlock (Real.cos α) (Real.sin α) (Real.cos β) (Real.sin β) block60 = block60 ↔
      Real.cos (α - β) = 1 ∧ Real.cos (α + β) = 1 := by
  exact rotateBlock_eq_iff α β block60 block60_differenceWeight_pos block60_sumWeight_pos

theorem crossBlock_1_60_2_30_stabilizer (α β : ℝ) :
    rotateBlock (Real.cos α) (Real.sin α) (Real.cos β) (Real.sin β)
        (crossBlock (1, 60) (2, 30)) = crossBlock (1, 60) (2, 30) ↔
      Real.cos (α - β) = 1 ∧ Real.cos (α + β) = 1 := by
  rw [crossBlock_1_60_2_30]
  exact block60_stabilizer α β

theorem crossBlock_3_20_6_10_stabilizer (α β : ℝ) :
    rotateBlock (Real.cos α) (Real.sin α) (Real.cos β) (Real.sin β)
        (crossBlock (3, 20) (6, 10)) = crossBlock (3, 20) (6, 10) ↔
      Real.cos (α - β) = 1 ∧ Real.cos (α + β) = 1 := by
  rw [crossBlock_3_20_6_10]
  exact block60_stabilizer α β

end

end ArithmeticClock.DenseCarrier
