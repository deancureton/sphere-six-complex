module

public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj

/-!
# The canonical affine map from the simplicial boundary to a standard simplex

This is the elementary realization map used by both the geometric identification and the
simplicial--singular comparison argument.  Keeping it in this low-level module avoids making
either argument depend on the other.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Set Simplicial

namespace SphereSixComplex

/-- The canonical map from realization of the simplicial boundary into the ordinary standard
seven-simplex. -/
public noncomputable def boundarySevenRealizationToStdSimplex :
    C((SSet.toTop.obj (∂Δ[7] : SSet.{0}) : Type), stdSimplex ℝ (Fin 8)) :=
  ⟨fun x ↦ SimplexCategory.toTopHomeo (SimplexCategory.mk 7)
      (SSet.toTop.map (SSet.boundary 7).ι x),
    (SimplexCategory.toTopHomeo (SimplexCategory.mk 7)).continuous.comp
      (SSet.toTop.map (SSet.boundary 7).ι).hom.continuous⟩

/-- On each simplicial face, the canonical realization map is the usual affine face inclusion. -/
public theorem boundarySevenRealizationToStdSimplex_face
    (i : Fin 8) (x : (SSet.toTop.obj (Δ[6] : SSet.{0}) : Type)) :
    boundarySevenRealizationToStdSimplex
        (SSet.toTop.map (SSet.boundary.ι i) x) =
      stdSimplex.map i.succAbove
        (SimplexCategory.toTopHomeo (SimplexCategory.mk 6) x) := by
  unfold boundarySevenRealizationToStdSimplex
  change SimplexCategory.toTopHomeo (SimplexCategory.mk 7)
      (SSet.toTop.map (SSet.boundary 7).ι
        (SSet.toTop.map (SSet.boundary.ι i) x)) = _
  rw [← ConcreteCategory.comp_apply]
  rw [← SSet.toTop.map_comp]
  rw [SSet.boundary.ι_ι]
  exact SimplexCategory.toTopHomeo_naturality_apply (SimplexCategory.δ i) x

end SphereSixComplex
