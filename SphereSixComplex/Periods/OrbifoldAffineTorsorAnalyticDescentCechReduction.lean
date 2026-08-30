module

public import SphereSixComplex.Periods.OrbifoldAffineTorsorCuspFrameBounds

/-!
# Cech reduction of orbifold affine-torsor analytic descent

The classical `H¹` input itself is already proved in
`HolomorphicAffineTorsorHOneSplitting`: the explicit Laurent decompositions give the splitting of
every affine torsor under `O(-1)` or `O` on the projective line.  This file records the exact
remaining implication.  Once finite-orbifold descent and removable extension identify the source
problem with such a projective-line Cech torsor, the full `AnalyticDescentData` follows without a
further analytic assumption.

Thus the only unresolved construction is a value of `CuspCorrectionCechReduction`.  Treating that
comparison as Cartan--B would be misleading: it also contains the finite-orbifold descent of the
affine cocycle and the cusp extension/boundedness comparison, neither of which is currently
represented by a general sheaf or orbifold API in Mathlib.
-/

noncomputable section

namespace SphereSixComplex.Periods

namespace OrbifoldAffineLineTorsorDescentProblem

/-- A projective-line Cech realization produces the global cusp-regular equivariant section used
by analytic descent. -/
public theorem hasCuspBoundedEquivariantSection_of_cechReduction
    (P : OrbifoldAffineLineTorsorDescentProblem)
    (R : P.CuspCorrectionCechReduction) :
    P.HasCuspBoundedEquivariantSection := by
  obtain ⟨C⟩ := P.nonempty_cuspBoundedEllipticOneCorrection_of_cechReduction R
  exact P.hasCuspBoundedEquivariantSection_of_correction C

/-- Finite-orbifold Cech comparison, the proved `O(-1)`/`O` first-cohomology vanishing, and cusp
extension together imply the complete analytic descent certificate. -/
public theorem nonempty_analyticDescentData_of_cechReduction
    (P : OrbifoldAffineLineTorsorDescentProblem)
    (R : P.CuspCorrectionCechReduction) :
    Nonempty P.AnalyticDescentData :=
  nonempty_analyticDescentData_of_hasCuspBoundedEquivariantSection P
    (P.hasCuspBoundedEquivariantSection_of_cechReduction R)

/-- The more concrete gluing package used by the cusp-bound modules also suffices for the full
analytic descent certificate. -/
public theorem nonempty_analyticDescentData_of_cechGluingData
    (P : OrbifoldAffineLineTorsorDescentProblem) (D : P.CechGluingData) :
    Nonempty P.AnalyticDescentData :=
  P.nonempty_analyticDescentData_of_cechReduction D.toCuspCorrectionCechReduction

end OrbifoldAffineLineTorsorDescentProblem

end SphereSixComplex.Periods
