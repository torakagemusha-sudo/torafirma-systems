import ArithmeticClock.ContinuousReturn60

set_option autoImplicit false

namespace ArithmeticClock.RealClock60

noncomputable section

theorem flow_integer_eq_clock (k : ℤ) : flow (k : ℝ) = clock (k : ZMod 60) := by
  have hz : ((k - ((k : ZMod 60).val : ℤ) : ℤ) : ZMod 60) = 0 := by
    simp
  have hd : (60 : ℤ) ∣ k - ((k : ZMod 60).val : ℤ) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
  obtain ⟨m, hm⟩ := hd
  have he : (k : ℝ) = ((k : ZMod 60).val : ℝ) + (m : ℝ) * 60 := by
    have hh : (k : ℝ) - ((k : ZMod 60).val : ℝ) = 60 * (m : ℝ) := by
      exact_mod_cast hm
    linarith
  rw [he]
  exact flow_periodic.int_mul m _

theorem integer_clock_basis_change (k : ℤ) :
    lift (flow (k : ℝ)) = DenseTwirl.basis *
      CyclicTwirl.diagonalClock 60 DenseTwirl.weights (k : ZMod 60) *
        DenseTwirl.basis.conjTranspose := by
  rw [flow_integer_eq_clock]
  exact clock_basis_change _

theorem integer_flowOrbit_eq_realOrbit (k : ℤ) :
    flowOrbit (k : ℝ) = realOrbit (k : ZMod 60) := by
  simp only [flowOrbit, realOrbit, flow_integer_eq_clock]

end

end ArithmeticClock.RealClock60
