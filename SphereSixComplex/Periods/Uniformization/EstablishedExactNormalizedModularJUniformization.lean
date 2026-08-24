module

public import SphereSixComplex.Periods.Uniformization.ExactNormalizedModularJTau
import all SphereSixComplex.Periods.Uniformization.ExactNormalizedModularJTau

@[expose] public section

/-!
# Established exact normalized modular-J uniformization

Assembly of the exact target quotient, branch, fibre, special-value, and cusp results.
-/

noncomputable section

namespace SphereSixComplex.Periods

open ExactNormalizedModularJTau

/-- The formerly axiomatized exact normalized modular-J uniformization theorem. -/
theorem establishedExactNormalizedModularJUniformization_proved :
    Nonempty ExactNormalizedModularJUniformization :=
  ⟨exactNormalizedModularJUniformization⟩


end SphereSixComplex.Periods
