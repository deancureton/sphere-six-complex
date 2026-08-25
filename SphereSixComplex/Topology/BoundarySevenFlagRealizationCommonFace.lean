module

public import SphereSixComplex.Topology.BoundarySevenProperFaceRealization

/-!
# Common faces in the proper-face realization

This module isolates the categorical half of overlap uniqueness.  If two flag simplices have a
common restriction and two simplex points are obtained from the same point of that restriction,
then their images in geometric realization are equal.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite Simplicial

namespace SphereSixComplex

/-- Two representatives induced from the same point of a common flag restriction define the
same point of the geometric realization. -/
public theorem boundarySevenFlagRealization_eq_of_commonRestriction
    {r k l : ℕ}
    (F : ComposableArrows BoundarySevenProperFace k)
    (G : ComposableArrows BoundarySevenProperFace l)
    (f : SimplexCategory.mk r ⟶ SimplexCategory.mk k)
    (g : SimplexCategory.mk r ⟶ SimplexCategory.mk l)
    (hfg : BoundarySevenProperFaceNerve.map f.op F =
      BoundarySevenProperFaceNerve.map g.op G)
    (u : stdSimplex ℝ (Fin (r + 1))) :
    SSet.toTop.map ((SSet.yonedaEquiv
      (X := BoundarySevenProperFaceNerve)).symm F)
        ((SimplexCategory.toTopHomeo (SimplexCategory.mk k)).symm
          (stdSimplex.map f u)) =
      SSet.toTop.map ((SSet.yonedaEquiv
        (X := BoundarySevenProperFaceNerve)).symm G)
        ((SimplexCategory.toTopHomeo (SimplexCategory.mk l)).symm
          (stdSimplex.map g u)) := by
  have hmaps :
      SSet.stdSimplex.map f ≫ (SSet.yonedaEquiv
        (X := BoundarySevenProperFaceNerve)).symm F =
        SSet.stdSimplex.map g ≫ (SSet.yonedaEquiv
          (X := BoundarySevenProperFaceNerve)).symm G := by
    apply (SSet.yonedaEquiv
      (X := BoundarySevenProperFaceNerve)).injective
    rw [← SSet.yonedaEquiv_naturality,
      ← SSet.yonedaEquiv_naturality]
    have hF : (SSet.yonedaEquiv
        (X := BoundarySevenProperFaceNerve))
          ((SSet.yonedaEquiv
            (X := BoundarySevenProperFaceNerve)).symm F) = F :=
      (SSet.yonedaEquiv
        (X := BoundarySevenProperFaceNerve)).apply_symm_apply F
    have hG : (SSet.yonedaEquiv
        (X := BoundarySevenProperFaceNerve))
          ((SSet.yonedaEquiv
            (X := BoundarySevenProperFaceNerve)).symm G) = G :=
      (SSet.yonedaEquiv
        (X := BoundarySevenProperFaceNerve)).apply_symm_apply G
    exact (congrArg (fun z ↦ BoundarySevenProperFaceNerve.map f.op z) hF).trans
      (hfg.trans
        (congrArg (fun z ↦ BoundarySevenProperFaceNerve.map g.op z) hG).symm)
  rw [SimplexCategory.toTopHomeo_symm_naturality_apply,
    SimplexCategory.toTopHomeo_symm_naturality_apply]
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    ← SSet.toTop.map_comp, ← SSet.toTop.map_comp]
  rw [hmaps]

end SphereSixComplex
