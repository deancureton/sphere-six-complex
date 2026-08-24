module

public import SphereSixComplex.Geometry.FourPieceStarGluing
public import SphereSixComplex.ComplexStructure

/-!
# Biholomorphic star gluing

The standard complex-manifold gluing theorem says that complex manifolds glued along
biholomorphic open subsets inherit the atlas obtained by transporting the atlases of their
pieces.  This module states that formula-independent theorem for the four-piece star interface.
-/

open scoped ContDiff Manifold

namespace SphereSixComplex.Geometry.EstablishedBiholomorphicStarGluing

noncomputable section

/-- Complex-manifold and biholomorphic-collar data on a four-piece star. -/
public structure BiholomorphicFourPieceStarData (A : FourPieceStarGluingData) where
  centralCharts : ChartedSpace ComplexModel A.central
  fillingCharts : ∀ i, ChartedSpace ComplexModel (A.filling i)
  centralManifold :
    letI := centralCharts
    IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞ A.central
  fillingManifold :
    letI (i : Fin 3) := fillingCharts i
    ∀ i, IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞ (A.filling i)
  /-- The analytic extension of each collar homeomorphism to an open partial diffeomorphism of
  the ambient pieces. -/
  collar :
    letI := centralCharts
    letI (i : Fin 3) := fillingCharts i
    ∀ i, PartialDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) A.central (A.filling i) ∞
  collar_source :
    letI := centralCharts
    letI (i : Fin 3) := fillingCharts i
    ∀ i, (collar i).source = A.centralCollar i
  collar_target :
    letI := centralCharts
    letI (i : Fin 3) := fillingCharts i
    ∀ i, (collar i).target = A.fillingCollar i
  collar_apply :
    letI := centralCharts
    letI (i : Fin 3) := fillingCharts i
    ∀ i (x : A.centralCollar i), collar i x.1 = (A.collarEquiv i x).1

namespace BiholomorphicFourPieceStarData

variable {A : FourPieceStarGluingData} (C : BiholomorphicFourPieceStarData A)

/-- The complex atlases of the central piece and three fillings, indexed by the star diagram. -/
@[instance_reducible] public def complexCharts :
    ∀ i, ChartedSpace ComplexModel (A.glueData.U i)
  | none => C.centralCharts
  | some i => C.fillingCharts i

end BiholomorphicFourPieceStarData

/-- Standard atlas compatibility for gluing complex manifolds along biholomorphic open
subsets. -/
public axiom establishedFourPieceBiholomorphicGluingAtlasCompatible
    (A : FourPieceStarGluingData)
    (hcollar : ∀ i, Nonempty (A.centralCollar i))
    (C : BiholomorphicFourPieceStarData A) :
    letI := A.nonemptyPieceOfCollars hcollar
    letI := C.complexCharts
    GluingAtlasCompatible (I := modelWithCornersSelf ℂ ComplexModel) (n := ∞) A.glueData

end

end SphereSixComplex.Geometry.EstablishedBiholomorphicStarGluing
