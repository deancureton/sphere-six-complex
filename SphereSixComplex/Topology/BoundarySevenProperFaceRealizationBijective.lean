module

public import SphereSixComplex.Topology.BoundarySevenProperFaceRealizationCompact
public import SphereSixComplex.Topology.BoundarySevenOrderedCoordinateFlag
public import SphereSixComplex.Topology.BoundarySevenStrictFlagAffineInjective

/-!
# Point-set properties of the proper-face affine realization

This file records the evaluation of the affine realization on each flag simplex and develops
the point-set part of the barycentric triangulation of the boundary of the seven-simplex.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits ContinuousMap Opposite Set Simplicial

namespace SphereSixComplex

private theorem toTopSimplex_inv_apply_up_eq_toTopHomeo_symm
    (n : SimplexCategory) (w : stdSimplex ℝ (Fin (n.len + 1))) :
    SSet.toTopSimplex.inv.app n (ULift.up w) = n.toTopHomeo.symm w := by
  rfl

/-- On the realization simplex represented by a flag, the adjointly defined realization map is
the explicit affine combination of the barycenters of the faces in that flag. -/
public theorem boundarySevenProperFaceRealizationMap_flag
    (k : ℕ) (F : ComposableArrows BoundarySevenProperFace k)
    (w : stdSimplex ℝ (Fin (k + 1))) :
    boundarySevenProperFaceRealizationMap
        (SSet.toTop.map (SSet.yonedaEquiv.symm F)
          ((SimplexCategory.toTopHomeo (SimplexCategory.mk k)).symm w)) =
      boundarySevenProperFaceAffineFlagMap k F w := by
  have h := boundarySevenProperFaceRealizationMap_adjunct
  have h' := congrArg (fun η ↦ η.app (Opposite.op (SimplexCategory.mk k)) F) h
  have h'' := congrArg
    (fun s ↦ (TopCat.toSSetObjEquiv (TopCat.of (StandardSimplexBoundary 7))
      (Opposite.op (SimplexCategory.mk k))) s) h'
  have hw := congrArg (fun f ↦ f w) h''
  change boundarySevenProperFaceRealizationMap
      (((sSetTopAdj.unit.app BoundarySevenProperFaceNerve).app
        (Opposite.op (SimplexCategory.mk k)) F).down.hom (ULift.up w)) =
    boundarySevenProperFaceAffineFlagMap k F w at hw
  have hunit := sSetTopAdj_unit_app_app_down BoundarySevenProperFaceNerve
    (Opposite.op (SimplexCategory.mk k)) F
  have hpoint := ConcreteCategory.congr_hom hunit (ULift.up w)
  change (((sSetTopAdj.unit.app BoundarySevenProperFaceNerve).app
      (Opposite.op (SimplexCategory.mk k)) F).down.hom (ULift.up w)) =
    SSet.toTop.map (SSet.yonedaEquiv.symm F)
      (SSet.toTopSimplex.inv.app (SimplexCategory.mk k) (ULift.up w)) at hpoint
  rw [toTopSimplex_inv_apply_up_eq_toTopHomeo_symm] at hpoint
  rw [hpoint.symm]
  exact hw

/-- Every point of the proper-face realization is represented on the realization of a
nondegenerate flag simplex.  This is the point-set covering statement supplied by the
nonsingular-simplex colimit. -/
public theorem boundarySevenProperFaceRealization_nondegenerateFlagCovered
    (x : (SSet.toTop.obj BoundarySevenProperFaceNerve : Type)) :
    ∃ (s : BoundarySevenProperFaceNerve.N)
      (y : SSet.toTop.obj
        (SSet.stdSimplex.obj (SimplexCategory.mk s.dim))),
      SSet.toTop.map (SSet.yonedaEquiv.symm s.simplex) y = x := by
  letI : BoundarySevenProperFaceNerve.Nonsingular :=
    boundarySevenProperFaceNerve_nonsingular
  let cTop := SSet.toTop.mapCocone BoundarySevenProperFaceNerve.coconeN'
  have hcTop : IsColimit cTop :=
    isColimitOfPreserves SSet.toTop
      BoundarySevenProperFaceNerve.isColimitCoconeN'
  have hcType : IsColimit ((forget TopCat).mapCocone cTop) :=
    isColimitOfPreserves (forget TopCat) hcTop
  obtain ⟨s, y, hy⟩ := Types.jointly_surjective_of_isColimit hcType x
  exact ⟨s, y, hy⟩

/-- The explicit ordered-coordinate flag supplies a preimage of every boundary point. -/
public theorem boundarySevenProperFaceRealizationMap_surjective :
    Function.Surjective boundarySevenProperFaceRealizationMap := by
  intro w
  refine ⟨SSet.toTop.map
      (SSet.yonedaEquiv.symm (boundarySevenOrderedFlag w))
      ((SimplexCategory.toTopHomeo (SimplexCategory.mk 6)).symm
        (boundarySevenOrderedWeights w)), ?_⟩
  rw [boundarySevenProperFaceRealizationMap_flag]
  exact boundarySevenProperFaceAffineFlagMap_orderedFlag w

/-- On every nondegenerate realization simplex, the affine realization has unique simplex
coordinates. -/
public theorem boundarySevenProperFaceAffineFlagMap_injective_nondegenerate
    (s : BoundarySevenProperFaceNerve.N) :
    Function.Injective
      (boundarySevenProperFaceAffineFlagMap s.dim s.simplex) := by
  apply boundarySevenProperFaceAffineFlagMap_injective_of_strictMono
  exact (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono s.simplex).mp s.2

end SphereSixComplex
