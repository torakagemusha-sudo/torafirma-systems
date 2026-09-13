import ArithmeticClock.DenseCarrier
import ArithmeticClock.CyclicTwirl
import Mathlib.Data.Matrix.Block

set_option autoImplicit false
open scoped BigOperators

namespace ArithmeticClock.DenseTwirl

noncomputable section

def low : Fin 6 → ℕ := ![1, 2, 3, 4, 5, 6]
def high : Fin 6 → ℕ := ![60, 30, 20, 15, 12, 10]
def divisor (i : Fin 6 × Fin 2) : ℕ := if i.2 = 0 then low i.1 else high i.1
def phase : Fin 6 → ZMod 60 := ![59, 28, 17, 11, 7, 4]
def weights (i : Fin 6 × Fin 2) : ZMod 60 := if i.2 = 0 then phase i.1 else -phase i.1

def carrier : Matrix (Fin 6 × Fin 2) (Fin 6 × Fin 2) ℂ :=
  fun i j => (DenseCarrier.kernel (divisor i) (divisor j) : ℂ)

def planeBasis : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.sqrt 2 / 2 : ℝ), (Real.sqrt 2 / 2 : ℝ);
    -Complex.I * (Real.sqrt 2 / 2 : ℝ), Complex.I * (Real.sqrt 2 / 2 : ℝ)]

def basis : Matrix (Fin 6 × Fin 2) (Fin 6 × Fin 2) ℂ :=
  fun i j => if i.1 = j.1 then planeBasis i.2 j.2 else 0

def spectralCarrier : Matrix (Fin 6 × Fin 2) (Fin 6 × Fin 2) ℂ :=
  fun i j => ∑ x : Fin 2, ∑ y : Fin 2,
    star (planeBasis x i.2) * carrier (i.1, x) (j.1, y) * planeBasis y j.2

theorem weights_injective : Function.Injective weights := by decide

theorem divisorCount_pos : ∀ i, 0 < DenseCarrier.divisorCount (divisor i) := by decide

theorem carrier_diagonal (i : Fin 6 × Fin 2) : carrier i i = 1 := by
  have hp : (0 : ℝ) < DenseCarrier.divisorCount (divisor i) := by
    exact_mod_cast divisorCount_pos i
  have hk : DenseCarrier.kernel (divisor i) (divisor i) = 1 := by
    simp [DenseCarrier.kernel, Real.sqrt_mul_self hp.le, ne_of_gt hp]
  simpa [carrier] using congrArg (fun r : ℝ => (r : ℂ)) hk

theorem carrier_symmetric (i j : Fin 6 × Fin 2) : carrier i j = carrier j i := by
  unfold carrier DenseCarrier.kernel
  rw [Nat.gcd_comm, mul_comm]

theorem planeBasis_unitary : planeBasis.conjTranspose * planeBasis = 1 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  ext i j
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
    simp [planeBasis, Matrix.mul_apply, Fin.sum_univ_two, Complex.mul_re, Complex.mul_im,
      Matrix.conjTranspose_apply, map_ofNat] <;> nlinarith

theorem planeBasis_diagonalizes (c s : ℝ) :
    (DenseCarrier.rotation c s).map Complex.ofReal * planeBasis =
      planeBasis * Matrix.diagonal ![(c : ℂ) + Complex.I * s, (c : ℂ) - Complex.I * s] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [planeBasis, DenseCarrier.rotation, Matrix.mul_apply, Matrix.map_apply,
      Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;> ring_nf <;> norm_num

theorem spectralCarrier_basis_change : spectralCarrier = basis.conjTranspose * carrier * basis := by
  ext i j
  simp [spectralCarrier, basis, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum, apply_ite, ite_mul, mul_ite]
  ring

theorem basis_unitary : basis.conjTranspose * basis = 1 := by
  ext i j
  rcases i with ⟨p, x⟩
  rcases j with ⟨q, y⟩
  by_cases hpq : p = q
  · subst q
    have hs := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A x y) planeBasis_unitary
    simpa [basis, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
      Matrix.one_apply] using hs
  · simp [basis, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
      hpq, Ne.symm hpq]

theorem spectralCarrier_diagonal (i : Fin 6 × Fin 2) : spectralCarrier i i = 1 := by
  rcases i with ⟨p, x⟩
  have h0 := carrier_diagonal (p, 0)
  have h1 := carrier_diagonal (p, 1)
  have h01 := carrier_symmetric (p, 0) (p, 1)
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  fin_cases x <;>
    simp [spectralCarrier, Fin.sum_univ_two, planeBasis, h0, h1, h01, map_ofNat] <;>
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> nlinarith

theorem actual_dense_twirl : CyclicTwirl.twirl 60 weights spectralCarrier = 1 := by
  exact CyclicTwirl.twirl_eq_one_of_diagonal_one 60 weights weights_injective
    spectralCarrier spectralCarrier_diagonal

theorem spectralCarrier_entry_re (p q : Fin 6) :
    (spectralCarrier (p, 0) (q, 0)).re =
      (DenseCarrier.kernel (low p) (low q) + DenseCarrier.kernel (high p) (high q)) / 2 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  simp [spectralCarrier, carrier, divisor, planeBasis, Fin.sum_univ_two,
    map_ofNat, Complex.mul_re, Complex.mul_im]
  ring_nf
  rw [hs]
  ring

theorem spectralCarrier_entry_ne_zero : spectralCarrier (0, 0) (1, 0) ≠ 0 := by
  have hre := spectralCarrier_entry_re 0 1
  have hpos : 0 < DenseCarrier.kernel 1 2 := by
    rw [DenseCarrier.kernel_one_two]
    positivity
  have hnonneg := DenseCarrier.kernel_nonneg 60 30
  simp only [low, high, Matrix.cons_val_zero, Matrix.cons_val_one] at hre
  intro hz
  rw [hz] at hre
  norm_num at hre
  linarith

/-- Every return of the actual dense carrier in the unitary character basis. -/
theorem actual_dense_return_iff (t : ZMod 60) :
    CyclicTwirl.conjugation 60 weights t spectralCarrier = spectralCarrier ↔ t = 0 := by
  constructor
  · intro h
    have he := congrArg (fun A : Matrix (Fin 6 × Fin 2) (Fin 6 × Fin 2) ℂ =>
      A (0, 0) (1, 0)) h
    dsimp only at he
    rw [CyclicTwirl.conjugation_apply] at he
    have hw : weights (0, 0) - weights (1, 0) = (31 : ZMod 60) := by decide
    rw [hw] at he
    have hchar : CyclicCharacters.cyclicCharacter 60 31 t = 1 := by
      apply mul_right_cancel₀ spectralCarrier_entry_ne_zero
      simpa using he
    have hz : (31 : ZMod 60) * t = 0 := by
      apply ZMod.injective_stdAddChar
      simpa [CyclicCharacters.cyclicCharacter_apply, AddChar.map_zero_eq_one] using hchar
    have hi : (31 : ZMod 60) * 31 = 1 := by decide
    calc
      t = ((31 : ZMod 60) * 31) * t := by rw [hi, one_mul]
      _ = 31 * (31 * t) := by ring
      _ = 0 := by rw [hz, mul_zero]
  · rintro rfl
    simp [CyclicTwirl.conjugation, CyclicTwirl.diagonalClock_zero]

theorem actual_dense_nat_return_iff (k : ℕ) :
    CyclicTwirl.conjugation 60 weights (k : ZMod 60) spectralCarrier = spectralCarrier ↔
      60 ∣ k := by
  rw [actual_dense_return_iff, ZMod.natCast_zmod_eq_zero_iff_dvd]

/-- Exact complete return sets for strides one, two and four of source sixty. -/
theorem actual_dense_sampled_returns (k : ℕ) :
    (CyclicTwirl.conjugation 60 weights (k : ZMod 60) spectralCarrier = spectralCarrier ↔ 60 ∣ k) ∧
    (CyclicTwirl.conjugation 60 weights ((2 * k : ℕ) : ZMod 60) spectralCarrier = spectralCarrier ↔
      30 ∣ k) ∧
    (CyclicTwirl.conjugation 60 weights ((4 * k : ℕ) : ZMod 60) spectralCarrier = spectralCarrier ↔
      15 ∣ k) := by
  refine ⟨actual_dense_nat_return_iff k, ?_, ?_⟩
  · rw [actual_dense_nat_return_iff, show 60 = 2 * 30 by decide]
    exact Nat.mul_dvd_mul_iff_left (by decide : 0 < 2)
  · rw [actual_dense_nat_return_iff, show 60 = 4 * 15 by decide]
    exact Nat.mul_dvd_mul_iff_left (by decide : 0 < 4)

end

end ArithmeticClock.DenseTwirl
