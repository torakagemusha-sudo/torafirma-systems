import ArithmeticClock.RealClock60

example : ArithmeticClock.RealClock60.realOrbit (30 : ZMod 60) =
    ArithmeticClock.RealClock60.realCarrier := by
  apply (ArithmeticClock.RealClock60.realOrbit_return_iff _).2
  exact (show (0 : ZMod 60) = 0 from rfl)
