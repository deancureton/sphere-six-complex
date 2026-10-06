module

public import SphereSixComplex.Prerequisites.Algebra.Homology.UniversalCoefficients
public import SphereSixComplex.Prerequisites.Topology.SingularHomology.ModuleComparison
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SimplexBasis

/-! # Integral universal coefficients with free lower homology -/

@[expose] public section
noncomputable section
open CategoryTheory

namespace SphereSixComplex

/-- Integral cohomology is the dual of homology when all lower homology groups are free.
In degree zero the freeness hypothesis is vacuous. -/
def integralSingularCohomologyEquivDual
    (X : Type) [TopologicalSpace X] (n : ℕ)
    (hFree : ∀ j < n, Module.Free ℤ (IntegralSingularHomology j X)) :
    IntegralSingularCohomology n X ≃+ (IntegralSingularHomology n X →+ ℤ) := by
  let C := DifferentialGeometry.Topology.integralSingularChains X
  have hProjective (j : ℕ) (hj : j < n) : Projective (C.homology j) := by
    let _ := hFree j hj
    let _ := IntegralSingularComparison.free_homology X j
    exact ModuleCat.projective_of_free (Module.Free.chooseBasis ℤ (C.homology j))
  exact (IntegralSingularComparison.linearYonedaCohomologyEquiv X n).symm.trans
    ((TauCeti.ChainComplex.kroneckerEquivOfProjective ℤ C
      (ModuleCat.of ℤ (ULift.{0} ℤ)) n hProjective).toAddEquiv.trans
        (IntegralSingularComparison.homologyDualEquiv X n))

end SphereSixComplex
