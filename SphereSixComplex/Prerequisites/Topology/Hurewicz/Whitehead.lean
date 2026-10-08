module

public import SphereSixComplex.Prerequisites.Topology.MayerVietoris.StarGluing

/-!
# Homotopy invariance of integral singular homology

Homotopic continuous maps induce the same map on integral singular homology.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory ContinuousMap

namespace SphereSixComplex


/-- Homotopic maps induce the same map on integral singular homology. -/
public theorem integralSingularHomologyMap_eq_of_homotopic
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (h : f.Homotopic g) (k : ℕ) :
    ((singularHomologyFunctor AddCommGrpCat k).obj (AddCommGrpCat.of ℤ)).map
        (TopCat.ofHom f) =
      ((singularHomologyFunctor AddCommGrpCat k).obj (AddCommGrpCat.of ℤ)).map
        (TopCat.ofHom g) :=
  TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
    h.some (AddCommGrpCat.of ℤ) k











end SphereSixComplex
