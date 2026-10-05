module


public import SphereSixComplex.Elliptic.Band.RadialCompletion
public import SphereSixComplex.Homology.Second
public import SphereSixComplex.Elliptic.Homology.HomologyVanishing
public import SphereSixComplex.Homology.SphereComparison

/-!
# Topology of the glued analytic threefold

The fundamental group and homology computations concern the same geometric glued carrier.
-/

@[expose] public section
noncomputable section

namespace SphereSixComplex.Geometry.AnalyticData

variable (P : AnalyticData)

/-- The global circle action and cusp attachment kill second homology. -/
public theorem star_homologyTwo_subsingleton :
    Subsingleton (IntegralSingularHomology 2 P.VanKampenSpace) :=
  star_homologyTwo_subsingleton_of_interior P.affineRadialCompletionInput
    (ellipticInterior_homologyTwo_eq_zero P.affineRadialCompletionInput)

/-- Low-degree vanishing and the Euler calculation give the integral homology of the six-sphere. -/
public theorem star_nonempty_homologyEquiv_sixSphere :
    ∀ k, Nonempty
      (IntegralSingularHomology k
        (GluedSpace P.openEmbeddingStarData.toFourPieceStarGluingData.glueData) ≃+
      IntegralSingularHomology k SixSphere) :=
  P.star_nonempty_homologyEquiv_sixSphere_of_lowDegrees
    P.star_homologyOne_subsingleton P.star_homologyTwo_subsingleton

/-- The cusp relations make the fundamental group abelian, and vanishing first homology kills it. -/
public theorem star_simplyConnectedSpace :
    SimplyConnectedSpace
      (GluedSpace P.openEmbeddingStarData.toFourPieceStarGluingData.glueData) := by
  let _ := P.star_homologyOne_subsingleton
  exact P.star_simplyConnectedSpace_of_homologyOne_subsingleton P.cuspCentralNaturality

end SphereSixComplex.Geometry.AnalyticData
