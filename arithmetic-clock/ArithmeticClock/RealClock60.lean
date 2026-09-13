import ArithmeticClock.DenseTwirl

set_option autoImplicit false
open scoped BigOperators

namespace ArithmeticClock.RealClock60

noncomputable section

def delta (p : Fin 6) : ℕ := DenseTwirl.high p - DenseTwirl.low p

def angle (p : Fin 6) (t : ℝ) : ℝ := 2 * Real.pi * (delta p : ℝ) * t / 60

/-- The full real rotation flow, in the original paired divisor coordinates. -/
def flow (t : ℝ) : Matrix (Fin 6 × Fin 2) (Fin 6 × Fin 2) ℝ :=
  fun i j => if i.1 = j.1 then
    DenseCarrier.rotation (Real.cos (angle i.1 t)) (Real.sin (angle i.1 t)) i.2 j.2 else 0

/-- The finite clock evaluates the real formula at the canonical residue representative. -/
def clock (t : ZMod 60) := flow (t.val : ℝ)

def realCarrier : Matrix (Fin 6 × Fin 2) (Fin 6 × Fin 2) ℝ :=
  fun i j => DenseCarrier.kernel (DenseTwirl.divisor i) (DenseTwirl.divisor j)

def realOrbit (t : ZMod 60) := clock t * realCarrier * (clock t).transpose

def lift (A : Matrix (Fin 6 × Fin 2) (Fin 6 × Fin 2) ℝ) := A.map Complex.ofReal

theorem divisor_enumeration : Finset.univ.image DenseTwirl.divisor = Nat.divisors 60 := by
  decide

theorem divisor_injective : Function.Injective DenseTwirl.divisor := by decide

theorem complementary_planes : ∀ p, DenseTwirl.low p * DenseTwirl.high p = 60 ∧
    DenseTwirl.low p < DenseTwirl.high p := by decide

theorem phase_eq_delta : ∀ p, DenseTwirl.phase p = (delta p : ZMod 60) := by decide

theorem lift_injective : Function.Injective lift := by
  intro A B h
  ext i j
  exact Complex.ofReal_injective (congrArg (fun M => M i j) h)

theorem lift_mul (A B : Matrix (Fin 6 × Fin 2) (Fin 6 × Fin 2) ℝ) :
    lift (A * B) = lift A * lift B := by
  ext i j
  simp [lift, Matrix.mul_apply, Complex.ofReal_sum]

theorem lift_transpose (A : Matrix (Fin 6 × Fin 2) (Fin 6 × Fin 2) ℝ) :
    lift A.transpose = (lift A).conjTranspose := by
  ext i j
  simp [lift, Matrix.conjTranspose_apply]

theorem lift_realCarrier : lift realCarrier = DenseTwirl.carrier := by rfl

theorem basis_unitary_right : DenseTwirl.basis * DenseTwirl.basis.conjTranspose = 1 := by
  exact Matrix.mul_eq_one_comm.mp DenseTwirl.basis_unitary

theorem character_integer (p : Fin 6) (k : ℤ) :
    CyclicCharacters.cyclicCharacter 60 (DenseTwirl.phase p) (k : ZMod 60) =
      (Real.cos (angle p (k : ℝ)) : ℂ) + Complex.I * Real.sin (angle p (k : ℝ)) := by
  have he : CyclicCharacters.cyclicCharacter 60 (DenseTwirl.phase p) (k : ZMod 60) =
      Complex.exp (2 * Real.pi * Complex.I * (delta p : ℂ) * (k : ℂ) / 60) := by
    simpa only [phase_eq_delta, Int.cast_natCast, Nat.cast_ofNat] using
      CyclicCharacters.cyclicCharacter_intCast 60 (delta p : ℤ) k
  have ha : 2 * (Real.pi : ℂ) * Complex.I * (delta p : ℂ) * (k : ℂ) / 60 =
      (angle p (k : ℝ) : ℂ) * Complex.I := by
    simp only [angle, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat,
      Complex.ofReal_natCast, Complex.ofReal_intCast]
    ring
  rw [he, ha]
  apply Complex.ext <;>
    simp only [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im] <;> ring

theorem character_representative (p : Fin 6) (t : ZMod 60) :
    CyclicCharacters.cyclicCharacter 60 (DenseTwirl.phase p) t =
      (Real.cos (angle p (t.val : ℝ)) : ℂ) + Complex.I * Real.sin (angle p (t.val : ℝ)) := by
  simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using character_integer p (t.val : ℤ)

theorem character_negative (p : Fin 6) (t : ZMod 60) :
    CyclicCharacters.cyclicCharacter 60 (-DenseTwirl.phase p) t =
      (Real.cos (angle p (t.val : ℝ)) : ℂ) - Complex.I * Real.sin (angle p (t.val : ℝ)) := by
  have hn : CyclicCharacters.cyclicCharacter 60 (-DenseTwirl.phase p) t =
      (starRingEnd ℂ) (CyclicCharacters.cyclicCharacter 60 (DenseTwirl.phase p) t) := by
    simpa only [CyclicCharacters.cyclicCharacter_apply, neg_mul, mul_neg] using
      CyclicCharacters.cyclicCharacter_neg 60 (DenseTwirl.phase p) t
  rw [hn, character_representative]
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

theorem character_sign (p : Fin 6) (b : Fin 2) (t : ZMod 60) :
    CyclicCharacters.cyclicCharacter 60 (DenseTwirl.weights (p, b)) t =
      ![(Real.cos (angle p (t.val : ℝ)) : ℂ) + Complex.I * Real.sin (angle p (t.val : ℝ)),
        (Real.cos (angle p (t.val : ℝ)) : ℂ) - Complex.I * Real.sin (angle p (t.val : ℝ))] b := by
  fin_cases b
  · simpa [DenseTwirl.weights] using character_representative p t
  · simpa [DenseTwirl.weights] using character_negative p t

theorem clock_intertwines (t : ZMod 60) :
    lift (clock t) * DenseTwirl.basis =
      DenseTwirl.basis * CyclicTwirl.diagonalClock 60 DenseTwirl.weights t := by
  ext i j
  rcases i with ⟨p, x⟩
  rcases j with ⟨q, y⟩
  by_cases hpq : p = q
  · subst q
    have hs := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A x y)
      (DenseTwirl.planeBasis_diagonalizes
        (Real.cos (angle p (t.val : ℝ))) (Real.sin (angle p (t.val : ℝ))))
    simpa [lift, clock, flow, DenseTwirl.basis, CyclicTwirl.diagonalClock,
      Matrix.mul_apply, Matrix.diagonal_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      apply_ite, ite_mul, mul_ite, character_sign] using hs
  · simp [lift, clock, flow, DenseTwirl.basis, CyclicTwirl.diagonalClock,
      Matrix.mul_apply, Matrix.diagonal_apply, Fintype.sum_prod_type,
      apply_ite, ite_mul, mul_ite, hpq, Ne.symm hpq]

/-- The original assembled real clock is exactly the transported cyclic diagonal clock. -/
theorem clock_basis_change (t : ZMod 60) :
    lift (clock t) = DenseTwirl.basis * CyclicTwirl.diagonalClock 60 DenseTwirl.weights t *
      DenseTwirl.basis.conjTranspose := by
  rw [← clock_intertwines, Matrix.mul_assoc, basis_unitary_right, Matrix.mul_one]

theorem carrier_transport :
    DenseTwirl.basis * DenseTwirl.spectralCarrier * DenseTwirl.basis.conjTranspose =
      DenseTwirl.carrier := by
  rw [DenseTwirl.spectralCarrier_basis_change]
  simp only [← Matrix.mul_assoc, basis_unitary_right, Matrix.one_mul]
  rw [Matrix.mul_assoc, basis_unitary_right, Matrix.mul_one]

theorem lift_realOrbit (t : ZMod 60) :
    lift (realOrbit t) = DenseTwirl.basis *
      CyclicTwirl.conjugation 60 DenseTwirl.weights t DenseTwirl.spectralCarrier *
        DenseTwirl.basis.conjTranspose := by
  simp only [realOrbit, lift_mul, lift_transpose, lift_realCarrier, clock_basis_change,
    CyclicTwirl.conjugation, DenseTwirl.spectralCarrier_basis_change,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

theorem transport_injective : Function.Injective
    (fun A : Matrix (Fin 6 × Fin 2) (Fin 6 × Fin 2) ℂ =>
      DenseTwirl.basis * A * DenseTwirl.basis.conjTranspose) := by
  intro A B h
  have he := congrArg (fun M => DenseTwirl.basis.conjTranspose * M * DenseTwirl.basis) h
  simp only [← Matrix.mul_assoc, DenseTwirl.basis_unitary, Matrix.one_mul] at he
  simpa only [Matrix.mul_assoc, DenseTwirl.basis_unitary, Matrix.mul_one] using he

theorem realOrbit_return_iff (t : ZMod 60) : realOrbit t = realCarrier ↔ t = 0 := by
  rw [← DenseTwirl.actual_dense_return_iff t]
  constructor
  · intro h
    apply transport_injective
    dsimp only
    rw [← lift_realOrbit, carrier_transport, h, lift_realCarrier]
  · intro h
    apply lift_injective
    rw [lift_realOrbit, h, carrier_transport, lift_realCarrier]

theorem realOrbit_sampled_returns (k : ℕ) :
    (realOrbit (k : ZMod 60) = realCarrier ↔ 60 ∣ k) ∧
    (realOrbit ((2 * k : ℕ) : ZMod 60) = realCarrier ↔ 30 ∣ k) ∧
    (realOrbit ((4 * k : ℕ) : ZMod 60) = realCarrier ↔ 15 ∣ k) := by
  simpa only [realOrbit_return_iff, DenseTwirl.actual_dense_return_iff] using
    DenseTwirl.actual_dense_sampled_returns k

theorem lift_one : lift (1 : Matrix (Fin 6 × Fin 2) (Fin 6 × Fin 2) ℝ) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [lift, Matrix.one_apply, h]

theorem lift_smul (c : ℝ) (A : Matrix (Fin 6 × Fin 2) (Fin 6 × Fin 2) ℝ) :
    lift (c • A) = (c : ℂ) • lift A := by
  ext i j
  simp [lift, Matrix.smul_apply, smul_eq_mul]

theorem lift_sum {ι : Type*} [Fintype ι]
    (A : ι → Matrix (Fin 6 × Fin 2) (Fin 6 × Fin 2) ℝ) :
    lift (∑ i, A i) = ∑ i, lift (A i) := by
  ext i j
  simp [lift, Matrix.sum_apply]

theorem realOrbit_twirl : (60 : ℝ)⁻¹ • ∑ t : ZMod 60, realOrbit t = 1 := by
  apply lift_injective
  calc
    lift ((60 : ℝ)⁻¹ • ∑ t : ZMod 60, realOrbit t) =
        (60 : ℂ)⁻¹ • ∑ t : ZMod 60, DenseTwirl.basis *
          CyclicTwirl.conjugation 60 DenseTwirl.weights t DenseTwirl.spectralCarrier *
            DenseTwirl.basis.conjTranspose := by
      simp only [lift_smul, lift_sum, lift_realOrbit, Complex.ofReal_inv, Complex.ofReal_ofNat]
    _ = DenseTwirl.basis * CyclicTwirl.twirl 60 DenseTwirl.weights DenseTwirl.spectralCarrier *
        DenseTwirl.basis.conjTranspose := by
      simp only [CyclicTwirl.twirl, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_sum, Matrix.sum_mul, Nat.cast_ofNat]
    _ = lift 1 := by
      rw [DenseTwirl.actual_dense_twirl, Matrix.mul_one, basis_unitary_right, lift_one]

theorem transport_mul (A B : Matrix (Fin 6 × Fin 2) (Fin 6 × Fin 2) ℂ) :
    (DenseTwirl.basis * A * DenseTwirl.basis.conjTranspose) *
        (DenseTwirl.basis * B * DenseTwirl.basis.conjTranspose) =
      DenseTwirl.basis * (A * B) * DenseTwirl.basis.conjTranspose := by
  calc
    _ = DenseTwirl.basis * A * (DenseTwirl.basis.conjTranspose * DenseTwirl.basis) *
        B * DenseTwirl.basis.conjTranspose := by simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [DenseTwirl.basis_unitary, Matrix.mul_one]
      simp only [Matrix.mul_assoc]

theorem clock_zero : clock 0 = 1 := by
  apply lift_injective
  rw [clock_basis_change, CyclicTwirl.diagonalClock_zero, Matrix.mul_one,
    basis_unitary_right, lift_one]

theorem clock_add (s t : ZMod 60) : clock (s + t) = clock s * clock t := by
  apply lift_injective
  rw [lift_mul]
  simp only [clock_basis_change, CyclicTwirl.diagonalClock_add]
  exact (transport_mul _ _).symm

theorem clock_transpose (t : ZMod 60) : (clock t).transpose = clock (-t) := by
  apply lift_injective
  simp only [lift_transpose, clock_basis_change, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, CyclicTwirl.diagonalClock_conjTranspose,
    Matrix.mul_assoc]

theorem clock_orthogonal (t : ZMod 60) : clock t * (clock t).transpose = 1 := by
  rw [clock_transpose, ← clock_add, add_neg_cancel, clock_zero]

theorem flow_zero : flow 0 = 1 := by
  ext i j
  rcases i with ⟨p, x⟩
  rcases j with ⟨q, y⟩
  fin_cases x <;> fin_cases y <;> by_cases hpq : p = q <;>
    simp [flow, angle, DenseCarrier.rotation, Matrix.one_apply, hpq]

theorem flow_add (s t : ℝ) : flow (s + t) = flow s * flow t := by
  ext i j
  rcases i with ⟨p, x⟩
  rcases j with ⟨q, y⟩
  by_cases hpq : p = q
  · subst q
    have ha : angle p (s + t) = angle p s + angle p t := by unfold angle; ring
    fin_cases x <;> fin_cases y <;>
      simp [flow, DenseCarrier.rotation, Matrix.mul_apply, Fintype.sum_prod_type,
        apply_ite, ite_mul, mul_ite, ha, Real.cos_add, Real.sin_add] <;> ring
  · simp [flow, Matrix.mul_apply, Fintype.sum_prod_type, apply_ite, ite_mul,
      mul_ite, hpq, Ne.symm hpq]

theorem flow_transpose (t : ℝ) : (flow t).transpose = flow (-t) := by
  ext i j
  rcases i with ⟨p, x⟩
  rcases j with ⟨q, y⟩
  by_cases hpq : p = q
  · subst q
    have ha : angle p (-t) = -angle p t := by unfold angle; ring
    fin_cases x <;> fin_cases y <;> simp [flow, DenseCarrier.rotation, ha]
  · simp [flow, hpq, Ne.symm hpq]

theorem flow_orthogonal (t : ℝ) : flow t * (flow t).transpose = 1 := by
  rw [flow_transpose, ← flow_add, add_neg_cancel, flow_zero]

theorem continuous_flow : Continuous flow := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  rcases i with ⟨p, x⟩
  rcases j with ⟨q, y⟩
  by_cases hpq : p = q
  · fin_cases x <;> fin_cases y <;>
      simp [flow, DenseCarrier.rotation, angle, hpq] <;> fun_prop
  · simp [flow, hpq]
    exact continuous_const

end

end ArithmeticClock.RealClock60
