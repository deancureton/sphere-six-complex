module

public import SphereSixComplex.Topology.CollarProductVanishing
public import SphereSixComplex.Topology.PaperCuspCollarRadialMappingTorus
public import SphereSixComplex.Topology.SectionSevenStageTopDegree
public import SphereSixComplex.Topology.WangDimensionVanishing

/-!
# The cusp collar's sixth homology

The Section 7 top-degree obligation asks each collar source for its sixth integral homology.  For
the cusp collar the radial mapping-torus realization answers it outright, given only the fibre's
fifth and sixth homology: the radial interval is contractible and comes off, and what is left is a
mapping torus, whose sixth homology the Wang sequence reads off the fibre's fifth and sixth.

Nothing here is specific to the cusp beyond the realization; the fibre's own vanishing is the one
remaining input, and for a fibre built from cells of dimension at most four it is
`subsingleton_integralSingularHomology_of_labelledA2Cells`.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.PaperAnalyticData

variable {A : PaperAnalyticData}

/-- The cusp collar has no sixth integral homology as soon as its fibre has none in degrees five
and six. -/
public theorem subsingleton_homology_six_cuspCollar
    (R : A.CuspCollarRadialMappingTorusRealization)
    (h5 : letI := R.fiberTopology; Subsingleton (IntegralSingularHomology 5 R.Fiber))
    (h6 : letI := R.fiberTopology; Subsingleton (IntegralSingularHomology 6 R.Fiber)) :
    Subsingleton
      (IntegralSingularHomology 6 (A.openEmbeddingStarData.collarSource 0)) := by
  let _ := R.fiberTopology
  let _ : ContractibleSpace (OpenRadialInterval R.radius) :=
    contractibleSpace_openInterval R.radius_pos
  have hMT : Subsingleton (IntegralSingularHomology 6 (CircleMappingTorus R.clutching)) :=
    subsingleton_homology_succ_finiteBouquetMappingTorus _ 5 h6 h5
  have hprod : Subsingleton (IntegralSingularHomology 6
      (OpenRadialInterval R.radius × CircleMappingTorus R.clutching)) :=
    subsingleton_homology_prod_of_contractible _ _ 6 hMT
  exact OpenEmbeddingStarData.subsingleton_homology_of_homeomorph 6
    R.totalHomeomorph.symm hprod

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
