module

public import SphereSixComplex.Geometry.EstablishedFuchsianCuspNeighborhoodProof

/-!
# The classical separated Fuchsian cusp neighbourhood

This module isolates the standard horodisc theorem for the normalized parabolic end of the
explicit Fuchsian triangle-group action.  It contains no toric, filling, quotient-embedding, or
collar conclusion.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.EstablishedFuchsianCuspNeighborhood

open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.FuchsianCuspNeighborhoodProof

namespace Established

/-- A sufficiently deep normalized horodisc is regular and precisely invariant under the
parabolic cyclic subgroup.  This is the standard cusp-neighbourhood theorem for a cofinite
Fuchsian group. -/
public theorem data
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (upperRadius : ℝ)
    (hupper : 0 < upperRadius) : Nonempty (Data N upperRadius) :=
  exists_data N upperRadius hupper

/-- Removing a precisely invariant horodisc from the explicit cofinite Fuchsian quotient leaves
a compact truncated quotient. -/
public theorem compactTruncation
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {upperRadius : ℝ}
    (H : Data N upperRadius) : Nonempty (CompactTruncationData H) :=
  exists_compactTruncation N H

end Established

end SphereSixComplex.Geometry.EstablishedFuchsianCuspNeighborhood
