module
public import SphereSixComplex.Paper.Topology.CuspEllipticInteriorRelators

@[expose] public section
noncomputable section
open AlgebraicTopology
namespace SphereSixComplex.Geometry.AnalyticData
open SphereSixComplex.Topology Hurewicz.Chains
variable (A : AnalyticData)

public def cuspOverlapToEllipticInterior :
    C((A.actualVanKampenFourPieceCover.core ∩ A.actualVanKampenFourPieceCover.cusp :
      Set A.VanKampenSpace), A.ellipticInterior) :=
  A.actualCoreToEllipticInterior.comp
    (A.actualVanKampenFourPieceCover.overlapToCore A.actualVanKampenFourPieceCover.cusp)

public theorem cuspOverlapToCore_hurewicz
    (g : FundamentalGroup
      (A.actualVanKampenFourPieceCover.core ∩ A.actualVanKampenFourPieceCover.cusp :
        Set A.VanKampenSpace) A.cuspOverlapBase) :
    hurewiczFunction _
      (A.actualCoreToEllipticInteriorPiOne (A.cuspOverlapToCore g)) =
      integralSingularHomologyMap 1 A.cuspOverlapToEllipticInterior
        (hurewiczFunction A.cuspOverlapBase g) := by
  rw [actualCoreToEllipticInteriorPiOne, hurewiczFunction_map]
  simp only [cuspOverlapToCore]
  erw [hurewiczFunction_basePath]
  erw [hurewiczFunction_map
    (A.actualVanKampenFourPieceCover.overlapToCore A.actualVanKampenFourPieceCover.cusp)
    A.cuspOverlapBase g]
  exact integralSingularHomologyMap_comp_wang 1 _ _ _

public theorem cuspOverlap_homology_fullIterate :
    (12 : ℤ) •
      (-integralSingularHomologyMap 1 A.cuspOverlapToEllipticInterior
        (hurewiczFunction A.cuspOverlapBase A.cuspAffineBridgeMeridian)) =
      integralSingularHomologyMap 1 A.cuspOverlapToEllipticInterior
        (hurewiczFunction A.cuspOverlapBase
          (Additive.toMul (A.cuspAffineBridgeTranslation
            (Pi.single (0 : Fin 4) 1)))) := by
  have h := A.ellipticInterior_cuspMeridian_twelfth_abelian (hurewiczPi1 _)
  rw [map_inv, map_inv] at h
  change (12 : ℕ) • (-hurewiczFunction _
    (A.actualCoreToEllipticInteriorPiOne
      (A.cuspOverlapToCore A.cuspAffineBridgeMeridian))) =
      hurewiczFunction _ (A.actualCoreToEllipticInteriorPiOne
        (A.cuspOverlapToCore (Additive.toMul
          (A.cuspAffineBridgeTranslation (Pi.single (0 : Fin 4) 1))))) at h
  rw [A.cuspOverlapToCore_hurewicz, A.cuspOverlapToCore_hurewicz] at h
  change (Int.ofNat 12) • _ = _
  erw [natCast_zsmul]
  exact h

end SphereSixComplex.Geometry.AnalyticData
end
