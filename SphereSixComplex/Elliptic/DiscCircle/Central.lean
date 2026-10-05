module

public import SphereSixComplex.Regular.FundamentalGroup.Peripheral
public import SphereSixComplex.Elliptic.DiscCircle.Factorization

@[expose] public section
noncomputable section

namespace SphereSixComplex.Geometry.AnalyticData

open SphereSixComplex.Topology SphereSixComplex.Hurewicz.Chains
open SphereSixComplex.StandardCircleHomologyLiftDegree

variable (A : AnalyticData)

public theorem markedCounterclockwiseZero_homology_eq_rhoOne :
    integralSingularHomologyMap 1 A.markedBaseToCentralZeroSection
      (hurewiczFunction twicePuncturedComplexBasepoint
        TwicePuncturedComplex.zeroMeridianClass⁻¹) =
      hurewiczFunction A.cuspCentralBase A.geometricCentralRhoOne := by
  rw [geometricCentralRhoOne, markedCentralToActualCuspEquiv,
    hurewiczFunction_basePath, ← hurewiczFunction_map, map_inv,
    A.markedBaseToCentralZeroSection_map_zero]
  rfl

public theorem markedCounterclockwiseOne_homology_eq_rhoTwo :
    integralSingularHomologyMap 1 A.markedBaseToCentralZeroSection
      (hurewiczFunction twicePuncturedComplexBasepoint
        TwicePuncturedComplex.oneMeridianClass⁻¹) =
      hurewiczFunction A.cuspCentralBase A.geometricCentralRhoTwo := by
  rw [geometricCentralRhoTwo, markedCentralToActualCuspEquiv,
    hurewiczFunction_basePath, ← hurewiczFunction_map, map_inv,
    A.markedBaseToCentralZeroSection_map_one]
  rfl

open EllipticDiscCircle Metric

public theorem factorizedDiscCircle_zero_central_homology
    (f u : ℂ → ℂ) (n : ℕ) (a : ℂ) (ha : a ≠ 0)
    (hu : ContinuousOn u (closedBall (0 : ℂ) ‖a‖))
    (hune : ∀ z ∈ closedBall (0 : ℂ) ‖a‖, u z ≠ 0)
    (hf : ∀ z ∈ closedBall (0 : ℂ) ‖a‖, f z = z ^ n * u z)
    (hb : ∀ z ∈ closedBall (0 : ℂ) ‖a‖, ‖a‖ ^ n * ‖u z‖ < ‖(1 : ℂ)‖)
    {x : TwicePuncturedComplex} (p : Path x x)
    (hp : ∀ t, (p t : ℂ) = f (localDegreeCirclePoint a t)) :
    loopHomologyClass (p.map A.markedBaseToCentralZeroSection.continuous) =
      n • hurewiczFunction A.cuspCentralBase A.geometricCentralRhoOne := by
  have he := loopHomologyClass_eq_of_toContinuousMap_eq p
    ((factorizedCoordinateLoop f u n a (1) ha hu hune hf hb).map
      zeroPunctureMap.continuous) (by ext t; exact hp t)
  have hbase := he.trans
    (factorizedCoordinateLoop_zero_homology f u n a ha hu hune hf hb)
  have h := congrArg (integralSingularHomologyMap 1 A.markedBaseToCentralZeroSection) hbase
  simpa only [integralSingularHomologyMap_loopHomologyClass, map_nsmul,
    A.markedCounterclockwiseZero_homology_eq_rhoOne] using h

public theorem factorizedDiscCircle_one_central_homology
    (f u : ℂ → ℂ) (n : ℕ) (a : ℂ) (ha : a ≠ 0)
    (hu : ContinuousOn u (closedBall (0 : ℂ) ‖a‖))
    (hune : ∀ z ∈ closedBall (0 : ℂ) ‖a‖, u z ≠ 0)
    (hf : ∀ z ∈ closedBall (0 : ℂ) ‖a‖, f z = z ^ n * u z)
    (hb : ∀ z ∈ closedBall (0 : ℂ) ‖a‖, ‖a‖ ^ n * ‖u z‖ < ‖(-1 : ℂ)‖)
    {x : TwicePuncturedComplex} (p : Path x x)
    (hp : ∀ t, (p t : ℂ) = 1 + f (localDegreeCirclePoint a t)) :
    loopHomologyClass (p.map A.markedBaseToCentralZeroSection.continuous) =
      n • hurewiczFunction A.cuspCentralBase A.geometricCentralRhoTwo := by
  have he := loopHomologyClass_eq_of_toContinuousMap_eq p
    ((factorizedCoordinateLoop f u n a (-1) ha hu hune hf hb).map
      onePunctureMap.continuous) (by ext t; exact hp t)
  have hbase := he.trans
    (factorizedCoordinateLoop_one_homology f u n a ha hu hune hf hb)
  have h := congrArg (integralSingularHomologyMap 1 A.markedBaseToCentralZeroSection) hbase
  simpa only [integralSingularHomologyMap_loopHomologyClass, map_nsmul,
    A.markedCounterclockwiseOne_homology_eq_rhoTwo] using h

end SphereSixComplex.Geometry.AnalyticData
