module

public import SphereSixComplex.Prerequisites.Periods.Uniformization.ScalarMonodromyAssembly
import all SphereSixComplex.Prerequisites.Periods.Uniformization.ScalarMonodromyAssembly
public import SphereSixComplex.Prerequisites.Periods.Uniformization.ScalarFundamentalConsistency
import all SphereSixComplex.Prerequisites.Periods.Uniformization.ScalarFundamentalConsistency
public import SphereSixComplex.Prerequisites.Periods.Uniformization.SourceAutomaticExactAssembly
import all SphereSixComplex.Prerequisites.Periods.Uniformization.SourceAutomaticExactAssembly

@[expose] public section

/-!
# Exact scalar data directly from the monodromy branch

The orbit-choice scalar is useful for stating the algebraic effect of fundamental-polygon
consistency, but it is not needed once analytic continuation of the chamber germ has been
constructed.  This file starts the shorter direct route: the global branch supplied by Tau
Ceti obeys the three Schwarz laws on the upper half-plane, hence is invariant under the whole
source triangle group without extending those laws to the lower half-plane.
-/

open Complex Set UpperHalfPlane
open scoped ComplexConjugate

noncomputable section

namespace SphereSixComplex.Periods.SourceChamberTopology

open SphereSixComplex.TriangleGroup
open SphereSixComplex.TriangleGroup.FuchsianFundamentalDomain
open SphereSixComplex.TriangleGroup.FuchsianTriangleCover
open SphereSixComplex.Periods.TriangleReflections
open SphereSixComplex.Periods.SourceAutomaticExactAssembly

namespace MonodromyScalarBranch

variable {S : ChamberCaratheodorySeed sourceBoundedChamber}





/-! ## Agreement on the closed source chamber -/

/-- The finite closed source chamber, expressed in the ambient complex plane. -/
def sourceFiniteClosedChamber : Set ℂ :=
  {z | -Real.sqrt 2 / 2 ≤ z.re ∧ z.re ≤ 1 / 2 ∧
    0 < z.im ∧ 1 ≤ normSq z}




private theorem cuspExponential_mapsTo_sourceFiniteClosedChamber :
    MapsTo (cuspExponential (1 + Real.sqrt 2)) sourceFiniteClosedChamber
      (closure sourceBoundedChamber \ {sourceCuspVertex}) := by
  intro z hz
  change -Real.sqrt 2 / 2 ≤ z.re ∧ z.re ≤ 1 / 2 ∧
    0 < z.im ∧ 1 ≤ normSq z at hz
  refine ⟨?_, ?_⟩
  · by_cases hcircle : normSq z = 1
    · exact frontier_subset_closure
        (cuspExponential_mem_source_frontier_of_circleSide hz.1 hz.2.1
          hz.2.2.1 hcircle)
    have hn : 1 < normSq z := lt_of_le_of_ne hz.2.2.2 (Ne.symm hcircle)
    by_cases hleft : z.re = -Real.sqrt 2 / 2
    · exact frontier_subset_closure
        (cuspExponential_mem_source_frontier_of_leftSide hleft hz.2.2.1 hn)
    by_cases hright : z.re = 1 / 2
    · exact frontier_subset_closure
        (cuspExponential_mem_source_frontier_of_rightSide hright hz.2.2.1 hn)
    apply subset_closure
    exact ⟨z, ⟨lt_of_le_of_ne hz.1 (Ne.symm hleft),
      lt_of_le_of_ne hz.2.1 hright, hz.2.2.1, hn⟩, rfl⟩
  · simpa [sourceCuspVertex] using
      cuspExponential_ne_zero (1 + Real.sqrt 2) z

/-- The boundary-aware chamber seed is continuous at every finite point of the closed source
triangle. -/
theorem sourceScalarTriangleMap_continuousOn_sourceFiniteClosedChamber :
    ContinuousOn (sourceScalarTriangleMap S) sourceFiniteClosedChamber := by
  exact (sourceScalarClosureMap_continuousOn_away_cusp S).comp
    (cuspExponential_continuous (1 + Real.sqrt 2)).continuousOn
    cuspExponential_mapsTo_sourceFiniteClosedChamber














end MonodromyScalarBranch



end SphereSixComplex.Periods.SourceChamberTopology
