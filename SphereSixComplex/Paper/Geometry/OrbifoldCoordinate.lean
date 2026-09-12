module

public import SphereSixComplex.Paper.Geometry.RegularTorusFamily

/-!
# Orbifold coordinate on the regular quotient family

The invariant source coordinate descends to the global family. Its continuity controls all
three ends of the family, independently of the filling construction.
-/

namespace SphereSixComplex.Geometry.GlobalTorusFamily

open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.AnalyticTorusFamily

public noncomputable section

variable {U : TriangleUniformization} (P : PeriodFunctions U)

/-- The source orbifold coordinate descended to the regular quotient family. -/
@[expose] public def orbifoldCoordinate : PuncturedGlobalFamily P → ℂ := by
  let _ := regularFamilyDeckAction P
  exact Quotient.lift
    (fun q : RegularTotalSpace P ↦ U.coordinate (regularTotalSpaceBase P q).1) (by
      intro p q hpq
      change MulAction.orbitRel Delta _ p q at hpq
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hpq
      obtain ⟨g, rfl⟩ := hpq
      change U.coordinate (regularTotalSpaceBase P (regularFamilyDeckMap P g q)).1 = _
      rw [regularTotalSpaceBase_familyDeckMap]
      exact U.coordinate_invariant g _)

public theorem continuous_orbifoldCoordinate : Continuous (orbifoldCoordinate P) := by
  let _ := regularFamilyDeckAction P
  unfold orbifoldCoordinate
  apply continuous_quot_lift
  exact U.coordinate_holomorphic.continuous.comp
    (continuous_subtype_val.comp (regularTotalSpaceBase_continuous P))

end

end SphereSixComplex.Geometry.GlobalTorusFamily
