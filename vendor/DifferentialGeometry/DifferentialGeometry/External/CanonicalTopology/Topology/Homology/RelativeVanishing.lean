module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.Relative

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Set

universe u

namespace DifferentialGeometry.Topology

theorem integralRelativeHomology_univ_subsingleton
    {X : Type u} [TopologicalSpace X] (n : ℕ) :
    Subsingleton (integralRelativeHomology n (univ : Set X)) := by
  let : IsIso (TopCat.ofHom (singularSubspaceInclusion (univ : Set X))) :=
    inferInstanceAs (IsIso (TopCat.isoOfHomeo
      (X := TopCat.of (univ : Set X)) (Y := TopCat.of X) (Homeomorph.Set.univ X)).hom)
  let : IsIso (integralSingularChainMap (singularSubspaceInclusion (univ : Set X))) :=
    inferInstance
  exact ModuleCat.subsingleton_of_isZero
    ((HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (ComplexShape.down ℕ) n).map_isZero
      (isZero_cokernel_of_epi (integralSingularChainMap (singularSubspaceInclusion (univ : Set X)))))

end DifferentialGeometry.Topology

end
