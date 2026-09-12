module

public import SphereSixComplex.Paper.Topology.EllipticCollarTopDegreeVanishing

/-!
# The cusp collar's four-torus fibre

The radial clutching data records its fibre as the additive four-torus of a full-rank period
parameter, so the fibre inherits the standard four-torus cell model and with it the vanishing of
its fifth and sixth homology.  That is the last hypothesis of the Section 7 top-degree obligation.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.AnalyticData

open SphereSixComplex.Geometry.CuspCollar
open SphereSixComplex.Geometry.EllipticFamilySpecialization

variable (A : AnalyticData)

/-- The cusp collar has no sixth integral singular homology. -/
public theorem subsingleton_homology_six_actualCuspCollar :
    Subsingleton (IntegralSingularHomology 6 (A.StarCollarSource 0)) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  have hT : FourTorusHomologicalModel (AdditiveTorus G.fiberParameter) :=
    StandardTorusHomology.additiveTorusFourTorusHomologicalModel _ G.fiberFullRank
  have h5 : Subsingleton (IntegralSingularHomology 5 G.Fiber) :=
    OpenEmbeddingStarData.subsingleton_homology_of_homeomorph 5 G.fiberHomeomorph.symm
      hT.subsingleton_homology_five
  have h6 : Subsingleton (IntegralSingularHomology 6 G.Fiber) :=
    OpenEmbeddingStarData.subsingleton_homology_of_homeomorph 6 G.fiberHomeomorph.symm
      hT.subsingleton_homology_six
  exact subsingleton_homology_six_of_radialMappingTorus G.clutching
    A.starCuspWitness.localWitness.radius_pos G.totalHomeomorph h5 h6

/-- The Section 7 top-degree obligation for the actual star, with no hypotheses left. -/
public theorem stageTopDegreeVanishing :
    A.openEmbeddingStarData.SectionSevenStageTopDegreeVanishing :=
  A.stageTopDegreeVanishing_of_actualCuspCollar
    A.subsingleton_homology_six_actualCuspCollar

end SphereSixComplex.Geometry.AnalyticData

end

end
