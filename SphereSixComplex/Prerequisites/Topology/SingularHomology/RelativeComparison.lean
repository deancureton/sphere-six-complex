module

public import DifferentialGeometry.Topology.Homology.SingularPair
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.Relative

/-! # Comparing relative singular homology models

Both relative chain complexes are cokernels of the same singular inclusion map.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open DifferentialGeometry.Topology

namespace SphereSixComplex.IntegralSingularComparison

def relativeChainsIso {X : Type} [TopologicalSpace X] (A : Set X) :
    integralRelativeChains A ≅
      (SingularPair.pair (TopCat.of X) A).chainComplex SingularPair.integerCoefficients :=
  (cokernelIsCokernel _).coconePointUniqueUpToIso
    ((SingularPair.pair (TopCat.of X) A).isColimitCokernelCoforkChainComplex
      SingularPair.integerCoefficients)

theorem relativeChainsIso_π {X : Type} [TopologicalSpace X] (A : Set X) :
    (integralRelativeChainSequence A).g ≫ (relativeChainsIso A).hom =
      (SingularPair.pair (TopCat.of X) A).chainComplexπ SingularPair.integerCoefficients :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (cokernelIsCokernel _)
    ((SingularPair.pair (TopCat.of X) A).isColimitCokernelCoforkChainComplex
      SingularPair.integerCoefficients) WalkingParallelPair.one

def relativeHomologyIso {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ) :
    integralRelativeHomology n A ≅
      SingularPair.relativeHomology SingularPair.integerCoefficients (TopCat.of X) A n :=
  HomologicalComplex.homologyMapIso (relativeChainsIso A) n

theorem relativeHomologyIso_π {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ) :
    ModuleCat.ofHom (integralAbsoluteToRelative n A) ≫ (relativeHomologyIso A n).hom =
      SingularPair.relπ SingularPair.integerCoefficients (TopCat.of X) A n := by
  change HomologicalComplex.homologyMap (integralRelativeChainSequence A).g n ≫
    HomologicalComplex.homologyMap (relativeChainsIso A).hom n = _
  exact (HomologicalComplex.homologyMap_comp (integralRelativeChainSequence A).g
    (relativeChainsIso A).hom n).symm.trans
      (congrArg (fun f ↦ HomologicalComplex.homologyMap f n) (relativeChainsIso_π A))

end SphereSixComplex.IntegralSingularComparison
