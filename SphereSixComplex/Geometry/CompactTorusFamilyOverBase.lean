module

public import SphereSixComplex.Geometry.EllipticWholeFiberCompactCover

/-!
# Compact torus families over compact base sets

The quotient torus family over a compact subset of the upper half-plane is the image of the
product of that subset with a closed real period cube.  This supplies compact total-space cores
for the completed four-piece gluing.
-/

namespace SphereSixComplex.Geometry.EllipticWholeFiberCompactCover

open Set SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open TorusFamily AnalyticTorusFamily GlobalTorusFamily ComplexTorus

noncomputable section

variable {U : TriangleUniformization} (F : PeriodFunctions U)

/-- Simultaneous real-period-cube parametrization of the varying torus family. -/
@[expose] public def familyBaseCubeParam (p : UpperHalfPlane × RealPeriods) :
    TotalSpace (parameterMap F) :=
  projection (parameterMap F)
    (p.1, (fullRankDomain (parameterMap F p.1)).realEquiv p.2)

public theorem familyBaseCubeParam_continuous :
    Continuous (familyBaseCubeParam F) := by
  unfold familyBaseCubeParam
  rw [projection.eq_def, quotientProjection.eq_def]
  apply continuous_quot_mk.comp
  convert continuous_fst.prodMk (periodRealLinear_parameterMap_continuous F) using 1
  funext p
  apply Prod.ext
  · rfl
  · rw [fullRankDomain.eq_def]
    rw [FullRank.ofSetupInequalities_realEquiv_apply]

/-- The part of the varying torus quotient lying over a selected base set. -/
@[expose] public def familyOverBaseSet (K : Set UpperHalfPlane) :
    Set (TotalSpace (parameterMap F)) :=
  familyTotalSpaceBase F ⁻¹' K

/-- A single closed real period cube parametrizes every fibre over the selected base set. -/
public theorem familyOverBaseSet_eq_image_unitCube (K : Set UpperHalfPlane) :
    familyOverBaseSet F K =
      familyBaseCubeParam F '' (K ×ˢ Set.Icc (0 : RealPeriods) 1) := by
  apply Set.Subset.antisymm
  · intro q hq
    obtain ⟨p, rfl⟩ := Quotient.mk_surjective q
    have hpK : p.1 ∈ K := by
      simpa [familyOverBaseSet, projection.eq_def] using hq
    have hpfiber : projection (parameterMap F) p ∈ familyFiber F p.1 :=
      ⟨p.2, rfl⟩
    rw [familyFiber_eq_image_unitCube F p.1] at hpfiber
    obtain ⟨r, hr, heq⟩ := hpfiber
    exact ⟨(p.1, r), ⟨hpK, hr⟩, heq⟩
  · rintro q ⟨p, hp, rfl⟩
    change familyTotalSpaceBase F (familyBaseCubeParam F p) ∈ K
    change familyTotalSpaceBase F
      (projection (parameterMap F)
        (p.1, (fullRankDomain (parameterMap F p.1)).realEquiv p.2)) ∈ K
    rw [familyTotalSpaceBase_projection]
    exact hp.1

/-- The entire quotient torus family over a compact base set is compact. -/
public theorem familyOverBaseSet_isCompact (K : Set UpperHalfPlane) (hK : IsCompact K) :
    IsCompact (familyOverBaseSet F K) := by
  rw [familyOverBaseSet_eq_image_unitCube F K]
  exact (hK.prod isCompact_Icc).image (familyBaseCubeParam_continuous F)

/-- The base projection of the varying compact-torus family is proper. -/
public theorem familyTotalSpaceBase_isProperMap :
    IsProperMap (familyTotalSpaceBase F) := by
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨continuous_quot_lift (familyTotalSpaceBase_respects F) continuous_fst, ?_⟩
  intro K hK
  simpa [familyOverBaseSet] using familyOverBaseSet_isCompact F K hK

end

end SphereSixComplex.Geometry.EllipticWholeFiberCompactCover
