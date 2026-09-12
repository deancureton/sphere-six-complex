module

public import SphereSixComplex.Paper.Geometry.EstablishedFuchsianCuspNeighborhoodProof

/-!
# The classical separated Fuchsian cusp neighbourhood

This module isolates the standard horodisc theorem for the normalized parabolic end of the
explicit Fuchsian triangle-group action.  It contains no toric, filling, quotient-embedding, or
collar conclusion.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.FuchsianCuspNeighborhood

open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspPeriodExpansion
open FuchsianCuspNeighborhood

/-- A sufficiently deep normalized horodisc is regular and precisely invariant under the
parabolic cyclic subgroup.  This is the standard cusp-neighbourhood theorem for a cofinite
Fuchsian group. -/
public theorem nonempty_data
    {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (upperRadius : ℝ)
    (hupper : 0 < upperRadius) : Nonempty (Data N upperRadius) :=
  nonempty_data_of_pos N upperRadius hupper

/-- Removing a precisely invariant horodisc from the explicit cofinite Fuchsian quotient leaves
a compact truncated quotient. -/
public theorem nonempty_compactTruncationData
    {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {upperRadius : ℝ}
    (H : Data N upperRadius) : Nonempty (CompactTruncationData H) :=
  nonempty_compactTruncationData_of_cuspNeighborhood N H

end SphereSixComplex.Geometry.FuchsianCuspNeighborhood
