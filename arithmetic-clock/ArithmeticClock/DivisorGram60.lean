import ArithmeticClock.DivisorGram
import ArithmeticClock.RealClock60

set_option autoImplicit false
open scoped BigOperators

namespace ArithmeticClock.DivisorGram60

noncomputable section

def divisorMap (i : Fin 6 × Fin 2) : DivisorGram.Divisor 60 :=
  ⟨DenseTwirl.divisor i, by
    rw [← RealClock60.divisor_enumeration]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩

theorem divisorMap_bijective : Function.Bijective divisorMap := by
  constructor
  · intro i j h
    exact RealClock60.divisor_injective (congrArg Subtype.val h)
  · intro a
    have ha : a.val ∈ Finset.univ.image DenseTwirl.divisor := by
      simpa only [RealClock60.divisor_enumeration] using a.property
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ha
    exact ⟨i, Subtype.ext hi⟩

def divisorEquiv : (Fin 6 × Fin 2) ≃ DivisorGram.Divisor 60 :=
  Equiv.ofBijective divisorMap divisorMap_bijective

theorem realCarrier_eq_reindex : RealClock60.realCarrier =
    (DivisorGram.kernelMatrix 60).submatrix divisorEquiv divisorEquiv := by
  rfl

theorem complexCarrier_eq_lift_reindex : DenseTwirl.carrier =
    RealClock60.lift
      ((DivisorGram.kernelMatrix 60).submatrix divisorEquiv divisorEquiv) := by
  rfl

/-- Strict positivity survives a bijective change of finite coordinates. -/
theorem posDef_reindex {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix n n ℝ) (e : m ≃ n) (hA : A.PosDef) :
    (A.submatrix e e).PosDef := by
  refine ⟨hA.isHermitian.submatrix e, ?_⟩
  intro x hx
  have hxe : x ∘ e.symm ≠ 0 := by
    intro he
    apply hx
    funext i
    simpa using congrFun he (e i)
  have h := hA.2 (x ∘ e.symm) hxe
  rw [Matrix.submatrix_mulVec_equiv]
  simpa only [star_trivial, comp_equiv_symm_dotProduct] using h

theorem realCarrier_posDef : RealClock60.realCarrier.PosDef := by
  rw [realCarrier_eq_reindex]
  exact posDef_reindex _ _ (DivisorGram.kernel_posDef 60)

theorem realCarrier_isUnit : IsUnit RealClock60.realCarrier :=
  realCarrier_posDef.isUnit

/-- Every state of the actual continuous real clock has a strictly positive carrier. -/
theorem flowCarrier_posDef (t : ℝ) :
    (RealClock60.flow t * RealClock60.realCarrier * (RealClock60.flow t).transpose).PosDef := by
  have hu : IsUnit (RealClock60.flow t) := by
    refine ⟨⟨RealClock60.flow t, (RealClock60.flow t).transpose,
      RealClock60.flow_orthogonal t,
      Matrix.mul_eq_one_comm.mp (RealClock60.flow_orthogonal t)⟩, rfl⟩
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    realCarrier_posDef.mul_mul_conjTranspose_same
      (B := RealClock60.flow t) (Matrix.vecMul_injective_iff_isUnit.mpr hu)

theorem realOrbit_posDef (t : ZMod 60) : (RealClock60.realOrbit t).PosDef :=
  flowCarrier_posDef (t.val : ℝ)

end

end ArithmeticClock.DivisorGram60
