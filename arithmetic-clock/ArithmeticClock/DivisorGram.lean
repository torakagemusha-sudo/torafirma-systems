import ArithmeticClock.DenseCarrier
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Real.StarOrdered
import Mathlib.NumberTheory.ArithmeticFunction

set_option autoImplicit false
open scoped BigOperators

namespace ArithmeticClock.DivisorGram

/-- Positive divisors, with the finite ordering inherited from the natural numbers. -/
abbrev Divisor (N : ℕ) := {d : ℕ // d ∈ N.divisors}

noncomputable section

variable (N : ℕ)

def incidence : Matrix (Divisor N) (Divisor N) ℝ :=
  fun a d => if d.val ∣ a.val then 1 else 0

def normalizer : Matrix (Divisor N) (Divisor N) ℝ :=
  Matrix.diagonal (fun a => (Real.sqrt (DenseCarrier.divisorCount a.val))⁻¹)

def feature : Matrix (Divisor N) (Divisor N) ℝ := normalizer N * incidence N

/-- The actual arithmetic kernel, not a Gram matrix substituted for its definition. -/
def kernelMatrix : Matrix (Divisor N) (Divisor N) ℝ :=
  fun a b => DenseCarrier.kernel a.val b.val

theorem divisor_pos (a : Divisor N) : 0 < a.val := Nat.pos_of_mem_divisors a.property

theorem divisorCount_pos (a : Divisor N) : 0 < DenseCarrier.divisorCount a.val := by
  apply Finset.card_pos.mpr
  exact ⟨1, Nat.one_mem_divisors.mpr (ne_of_gt (divisor_pos N a))⟩

theorem sqrt_divisorCount_pos (a : Divisor N) :
    0 < Real.sqrt (DenseCarrier.divisorCount a.val) := by
  exact Real.sqrt_pos.mpr (by exact_mod_cast divisorCount_pos N a)

theorem incidence_diagonal (a : Divisor N) : incidence N a a = 1 := by
  simp [incidence]

theorem incidence_lowerTriangular :
    (incidence N).BlockTriangular OrderDual.toDual := by
  intro a d had
  have hlt : a.val < d.val := had
  have hnd : ¬ d.val ∣ a.val := by
    intro hdiv
    exact (not_le_of_gt hlt) (Nat.le_of_dvd (divisor_pos N a) hdiv)
  simp [incidence, hnd]

/-- Divisibility incidence is unit lower triangular in the natural divisor order. -/
theorem incidence_det : (incidence N).det = 1 := by
  rw [Matrix.det_of_lowerTriangular _ (incidence_lowerTriangular N)]
  simp [incidence_diagonal]

/-- The entry of the unnormalized incidence Gram matrix counts common divisors. -/
theorem incidence_gram_apply (a b : Divisor N) :
    (incidence N * (incidence N).transpose) a b =
      (DenseCarrier.divisorCount (Nat.gcd a.val b.val) : ℝ) := by
  have hN : N ≠ 0 := (Nat.mem_divisors.mp a.property).2
  have hg : Nat.gcd a.val b.val ∣ N :=
    (Nat.gcd_dvd_left a.val b.val).trans (Nat.dvd_of_mem_divisors a.property)
  simp only [Matrix.mul_apply, Matrix.transpose_apply, incidence]
  have hterm : ∀ d : Divisor N,
      (if d.val ∣ a.val then (1 : ℝ) else 0) *
        (if d.val ∣ b.val then 1 else 0) =
      if d.val ∣ Nat.gcd a.val b.val then 1 else 0 := by
    intro d
    simp only [Nat.dvd_gcd_iff]
    split_ifs <;> simp_all
  simp_rw [hterm]
  rw [Finset.sum_coe_sort (s := N.divisors)
    (f := fun d : ℕ => if d ∣ Nat.gcd a.val b.val then (1 : ℝ) else 0)]
  rw [← Finset.sum_filter]
  rw [Nat.divisors_filter_dvd_of_dvd hN hg]
  simp [DenseCarrier.divisorCount]

theorem feature_apply (a d : Divisor N) :
    feature N a d = (Real.sqrt (DenseCarrier.divisorCount a.val))⁻¹ * incidence N a d := by
  exact Matrix.diagonal_mul _ _ _ _

/-- Normalized divisor incidence exactly factors the author's arithmetic kernel. -/
theorem kernel_gram_factorization :
    kernelMatrix N = feature N * (feature N).transpose := by
  ext a b
  have hpos : (0 : ℝ) ≤ DenseCarrier.divisorCount a.val := Nat.cast_nonneg _
  have he : feature N * (feature N).transpose =
      normalizer N * (incidence N * (incidence N).transpose) * normalizer N := by
    simp only [feature, Matrix.transpose_mul, normalizer, Matrix.diagonal_transpose,
      Matrix.mul_assoc]
  rw [he]
  simp only [normalizer, Matrix.mul_diagonal, Matrix.diagonal_mul, incidence_gram_apply]
  simp only [kernelMatrix, DenseCarrier.kernel, normalizer, Real.sqrt_mul hpos,
    div_eq_mul_inv, mul_inv_rev]
  ring

theorem feature_det : (feature N).det =
    ∏ a : Divisor N, (Real.sqrt (DenseCarrier.divisorCount a.val))⁻¹ := by
  rw [feature, Matrix.det_mul, incidence_det, mul_one]
  exact Matrix.det_diagonal

theorem feature_det_pos : 0 < (feature N).det := by
  rw [feature_det]
  exact Finset.prod_pos (fun a _ => inv_pos.mpr (sqrt_divisorCount_pos N a))

theorem feature_isUnit : IsUnit (feature N) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  exact isUnit_iff_ne_zero.mpr (ne_of_gt (feature_det_pos N))

/-- Strict positivity is proved from the arithmetic incidence matrix's invertibility. -/
theorem kernel_posDef : (kernelMatrix N).PosDef := by
  rw [kernel_gram_factorization]
  have h := (Matrix.PosDef.one : (1 : Matrix (Divisor N) (Divisor N) ℝ).PosDef).mul_mul_conjTranspose_same (B := feature N)
      (Matrix.vecMul_injective_iff_isUnit.mpr (feature_isUnit N))
  simpa only [Matrix.mul_one, Matrix.conjTranspose_eq_transpose_of_trivial] using h

theorem kernel_isUnit : IsUnit (kernelMatrix N) := (kernel_posDef N).isUnit

theorem kernel_det_pos : 0 < (kernelMatrix N).det := (kernel_posDef N).det_pos

/-- The exact determinant is the reciprocal product of the divisor counts. -/
theorem kernel_det : (kernelMatrix N).det =
    ∏ a : Divisor N, (DenseCarrier.divisorCount a.val : ℝ)⁻¹ := by
  rw [kernel_gram_factorization, Matrix.det_mul, Matrix.det_transpose, feature_det,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro a _
  rw [← mul_inv_rev, Real.mul_self_sqrt (Nat.cast_nonneg _)]

theorem kernel_diagonal (a : Divisor N) : kernelMatrix N a a = 1 := by
  have hp : (0 : ℝ) < DenseCarrier.divisorCount a.val := by
    exact_mod_cast divisorCount_pos N a
  simp [kernelMatrix, DenseCarrier.kernel, Real.sqrt_mul_self hp.le, ne_of_gt hp]

theorem kernel_inverse_posDef : ((kernelMatrix N)⁻¹).PosDef := (kernel_posDef N).inv

/-- The arithmetic Möbius inverse of the divisibility-incidence matrix. -/
def mobiusIncidence : Matrix (Divisor N) (Divisor N) ℝ :=
  fun a d => if d.val ∣ a.val then (ArithmeticFunction.moebius (a.val / d.val) : ℝ) else 0

theorem mobius_mul_incidence : mobiusIncidence N * incidence N = 1 := by
  ext a b
  have hN : N ≠ 0 := (Nat.mem_divisors.mp a.property).2
  let f : ℕ → ℝ := fun n => if n = b.val then 1 else 0
  let g : ℕ → ℝ := fun n => if b.val ∣ n then 1 else 0
  have hsum : ∀ n > 0, ∑ i ∈ n.divisors, f i = g n := by
    intro n hn
    simp [f, g, Nat.mem_divisors, ne_of_gt hn]
  have hinv := ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mp hsum
    a.val (divisor_pos N a)
  rw [Nat.sum_divisorsAntidiagonal'
    (f := fun x y => (ArithmeticFunction.moebius x : ℝ) * g y)] at hinv
  have he : (mobiusIncidence N * incidence N) a b =
      ∑ d ∈ a.val.divisors, (ArithmeticFunction.moebius (a.val / d) : ℝ) * g d := by
    simp only [Matrix.mul_apply, mobiusIncidence, incidence, ite_mul, zero_mul]
    rw [Finset.sum_coe_sort (s := N.divisors) (f := fun d : ℕ =>
      if d ∣ a.val then (ArithmeticFunction.moebius (a.val / d) : ℝ) * g d else 0)]
    rw [← Finset.sum_filter, Nat.divisors_filter_dvd_of_dvd hN
      (Nat.dvd_of_mem_divisors a.property)]
  rw [he, hinv]
  simp [f, Matrix.one_apply, Subtype.ext_iff]

theorem incidence_inverse : (incidence N)⁻¹ = mobiusIncidence N :=
  Matrix.inv_eq_left_inv (mobius_mul_incidence N)

theorem incidence_mul_mobius : incidence N * mobiusIncidence N = 1 := by
  rw [← incidence_inverse]
  apply Matrix.mul_nonsing_inv
  rw [incidence_det]
  exact isUnit_one

/-- Incidence-derived precision factor, with every entry defined arithmetically. -/
def precisionFactor : Matrix (Divisor N) (Divisor N) ℝ :=
  mobiusIncidence N * Matrix.diagonal (fun a => Real.sqrt (DenseCarrier.divisorCount a.val))

theorem precisionFactor_apply (a d : Divisor N) :
    precisionFactor N a d = mobiusIncidence N a d *
      Real.sqrt (DenseCarrier.divisorCount d.val) :=
  Matrix.mul_diagonal _ _ _ _

theorem feature_mul_precisionFactor : feature N * precisionFactor N = 1 := by
  have he : feature N * precisionFactor N =
      normalizer N * (incidence N * mobiusIncidence N) *
        Matrix.diagonal (fun a => Real.sqrt (DenseCarrier.divisorCount a.val)) := by
    simp only [feature, precisionFactor, Matrix.mul_assoc]
  rw [he, incidence_mul_mobius, Matrix.mul_one]
  simp only [normalizer, Matrix.diagonal_mul_diagonal]
  have hp : ∀ a : Divisor N, (Real.sqrt (DenseCarrier.divisorCount a.val))⁻¹ *
      Real.sqrt (DenseCarrier.divisorCount a.val) = 1 :=
    fun a => inv_mul_cancel₀ (ne_of_gt (sqrt_divisorCount_pos N a))
  simp only [hp, Matrix.diagonal_one]

theorem precisionFactor_mul_feature : precisionFactor N * feature N = 1 := by
  have he : precisionFactor N * feature N =
      mobiusIncidence N *
        (Matrix.diagonal (fun a => Real.sqrt (DenseCarrier.divisorCount a.val)) * normalizer N) *
        incidence N := by
    simp only [feature, precisionFactor, Matrix.mul_assoc]
  rw [he]
  have hp : Matrix.diagonal (fun a : Divisor N => Real.sqrt (DenseCarrier.divisorCount a.val)) *
      normalizer N = 1 := by
    simp only [normalizer, Matrix.diagonal_mul_diagonal]
    have h : ∀ a : Divisor N, Real.sqrt (DenseCarrier.divisorCount a.val) *
        (Real.sqrt (DenseCarrier.divisorCount a.val))⁻¹ = 1 :=
      fun a => mul_inv_cancel₀ (ne_of_gt (sqrt_divisorCount_pos N a))
    simp only [h, Matrix.diagonal_one]
  rw [hp, Matrix.mul_one, mobius_mul_incidence]

theorem feature_inverse : (feature N)⁻¹ = precisionFactor N :=
  Matrix.inv_eq_left_inv (precisionFactor_mul_feature N)

/-- Exact Möbius precision formula for the actual normalized arithmetic kernel. -/
theorem kernel_inverse_factorization : (kernelMatrix N)⁻¹ =
    (precisionFactor N).transpose * precisionFactor N := by
  apply Matrix.inv_eq_left_inv
  rw [kernel_gram_factorization]
  calc
    ((precisionFactor N).transpose * precisionFactor N) * (feature N * (feature N).transpose) =
        (precisionFactor N).transpose * (precisionFactor N * feature N) * (feature N).transpose := by
      simp only [Matrix.mul_assoc]
    _ = 1 := by
      rw [precisionFactor_mul_feature, Matrix.mul_one, ← Matrix.transpose_mul,
        feature_mul_precisionFactor, Matrix.transpose_one]

end

end ArithmeticClock.DivisorGram
