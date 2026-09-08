module
public import SphereSixComplex.Topology.CuspEllipticInteriorRelators
public import SphereSixComplex.Topology.HurewiczBasepointTransport

@[expose] public section
noncomputable section
open AlgebraicTopology
namespace SphereSixComplex.Geometry.PaperAnalyticData
open SphereSixComplex.Topology SphereSixComplex.Topology.FirstHurewiczProof
variable (A : PaperAnalyticData)

public def actualCuspOverlapToEllipticInterior :
    C((A.actualVanKampenFourPieceCover.core ∩ A.actualVanKampenFourPieceCover.cusp :
      Set A.VanKampenSpace), A.SectionSevenEllipticInterior) :=
  A.actualCoreToEllipticInterior.comp
    (A.actualVanKampenFourPieceCover.overlapToCore A.actualVanKampenFourPieceCover.cusp)

public theorem actualCuspOverlapToCore_hurewicz
    (g : FundamentalGroup
      (A.actualVanKampenFourPieceCover.core ∩ A.actualVanKampenFourPieceCover.cusp :
        Set A.VanKampenSpace) A.actualCuspOverlapBase) :
    hurewiczFunction _
      (A.actualCoreToEllipticInteriorPiOne (A.actualCuspOverlapToCore g)) =
      integralSingularHomologyMap 1 A.actualCuspOverlapToEllipticInterior
        (hurewiczFunction A.actualCuspOverlapBase g) := by
  rw [actualCoreToEllipticInteriorPiOne, hurewiczFunction_map]
  simp only [actualCuspOverlapToCore]
  erw [hurewiczFunction_basePath]
  erw [hurewiczFunction_map
    (A.actualVanKampenFourPieceCover.overlapToCore A.actualVanKampenFourPieceCover.cusp)
    A.actualCuspOverlapBase g]
  exact integralSingularHomologyMap_comp_wang 1 _ _ _

public theorem actualCuspOverlap_homology_fullIterate :
    (12 : ℤ) •
      (-integralSingularHomologyMap 1 A.actualCuspOverlapToEllipticInterior
        (hurewiczFunction A.actualCuspOverlapBase A.actualCuspAffineBridgeMeridian)) =
      integralSingularHomologyMap 1 A.actualCuspOverlapToEllipticInterior
        (hurewiczFunction A.actualCuspOverlapBase
          (Additive.toMul (A.actualCuspAffineBridgeTranslation
            (Pi.single (0 : Fin 4) 1)))) := by
  have h := A.ellipticInterior_cuspMeridian_twelfth_abelian (hurewiczPi1 _)
  rw [map_inv, map_inv] at h
  change (12 : ℕ) • (-hurewiczFunction _
    (A.actualCoreToEllipticInteriorPiOne
      (A.actualCuspOverlapToCore A.actualCuspAffineBridgeMeridian))) =
      hurewiczFunction _ (A.actualCoreToEllipticInteriorPiOne
        (A.actualCuspOverlapToCore (Additive.toMul
          (A.actualCuspAffineBridgeTranslation (Pi.single (0 : Fin 4) 1))))) at h
  rw [A.actualCuspOverlapToCore_hurewicz, A.actualCuspOverlapToCore_hurewicz] at h
  change (Int.ofNat 12) • _ = _
  erw [natCast_zsmul]
  exact h

end SphereSixComplex.Geometry.PaperAnalyticData
end
