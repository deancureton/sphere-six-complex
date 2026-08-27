module

public import SphereSixComplex.Topology.FiniteSimplicialRealizationCompact
public import SphereSixComplex.Topology.BoundarySevenProperFaceRealization

/-!
# Compactness of the proper-face realization

The proper-face nerve is the nerve of a finite partial order.  Its realization is therefore
compact by the finite nonsingular-realization theorem.  This discharges the compactness half of
the point-set input for the affine barycentric realization.
-/

@[expose] public section

noncomputable section

open CategoryTheory Simplicial

namespace SphereSixComplex

/-- The proper-face nerve is nonsingular because it is the nerve of a partial order. -/
public theorem boundarySevenProperFaceNerve_nonsingular :
    BoundarySevenProperFaceNerve.Nonsingular := by
  change (CategoryTheory.nerve BoundarySevenProperFace).Nonsingular
  infer_instance

/-- The proper-face nerve has only finitely many nondegenerate flags. -/
public theorem boundarySevenProperFaceNerve_finite :
    BoundarySevenProperFaceNerve.Finite := by
  change (CategoryTheory.nerve BoundarySevenProperFace).Finite
  exact finitePartialOrderNerve_finite BoundarySevenProperFace

/-- The realization of the finite proper-face nerve is compact. -/
public theorem boundarySevenProperFaceRealization_isCompact :
    IsCompact (Set.univ : Set
      (SSet.toTop.obj BoundarySevenProperFaceNerve : Type)) := by
  let : BoundarySevenProperFaceNerve.Finite :=
    boundarySevenProperFaceNerve_finite
  let : BoundarySevenProperFaceNerve.Nonsingular :=
    boundarySevenProperFaceNerve_nonsingular
  exact finiteNonsingularSSet_realization_isCompact BoundarySevenProperFaceNerve

/-- After compactness is discharged, bijectivity of the explicit affine map is the sole
remaining point-set input for the proper-face realization homeomorphism. -/
public theorem boundarySevenProperFaceAffineRealizationHomeomorphismInput_iff_bijective :
    BoundarySevenProperFaceAffineRealizationHomeomorphismInput ↔
      Function.Bijective boundarySevenProperFaceRealizationMap := by
  simp only [BoundarySevenProperFaceAffineRealizationHomeomorphismInput,
    boundarySevenProperFaceRealization_isCompact, true_and]

end SphereSixComplex
