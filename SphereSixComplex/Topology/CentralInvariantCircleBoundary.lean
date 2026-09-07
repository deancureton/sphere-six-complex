module
public import SphereSixComplex.Topology.GlobalInvariantPeriodCircle
public import SphereSixComplex.Topology.TwicePuncturedHomologyOneGenerators
public import SphereSixComplex.Topology.NormalizedCircleProductCross
public import SphereSixComplex.Topology.PaperSectionSevenCuspIndexFiveUnitCoefficientProof

@[expose] public section
noncomputable section
open AlgebraicTopology
open scoped ContinuousMap
namespace SphereSixComplex.Topology.CircleProductIdentityMappingTorus
open StandardTorusHomology

public theorem pathCircleMap_mem_range {X : Type} [TopologicalSpace X]
    {x : X} (p : Path x x) (z : StdTorus 1) : pathCircleMap p z ∈ Set.range p := by
  let t := AddCircle.equivIco (1 : ℝ) 0 (z 0)
  have ht : (t : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨t.2.1, by simpa using t.2.2.le⟩
  refine ⟨⟨t, ht⟩, ?_⟩
  change p ⟨t, ht⟩ = p.extend t
  exact (p.extend_apply ht).symm

end SphereSixComplex.Topology.CircleProductIdentityMappingTorus

namespace SphereSixComplex.Geometry.PaperAnalyticData
open SphereSixComplex.Topology
open CircleProductIdentityMappingTorus PositiveCircleCross StandardTorusHomology
open SectionSevenEllipticTwoDiscCoverData
open SectionSevenEllipticTwoDiscHomologyCoordinates
open SectionSevenEllipticInteriorMarkedCycleData
variable {A : PaperAnalyticData}

public noncomputable def centralFourthPeriodCircleToUnion
    (D : A.SectionSevenEllipticTwoDiscCoverData) :
    C(UnitAddCircle × TwicePuncturedComplex,
      (D.orderThreeSide ∪ D.orderFourSide : Set A.SectionSevenEllipticInterior)) := by
  refine ⟨fun p ↦ ⟨(A.sectionSevenEllipticCentralImageHomeomorph.symm
    (A.centralFourthPeriodCircle p)).1, ?_⟩, ?_⟩
  · rw [D.sides_cover]
    trivial
  · exact ((continuous_subtype_val.comp
      (A.sectionSevenEllipticCentralImageHomeomorph.symm.continuous.comp
        A.centralFourthPeriodCircle.continuous))).subtype_mk _

public theorem centralFourthPeriodCircleToUnion_height
    (D : A.SectionSevenEllipticTwoDiscCoverData)
    (t : UnitAddCircle) (b : TwicePuncturedComplex) :
    A.sectionSevenEllipticCentralHeight
      ⟨(centralFourthPeriodCircleToUnion D (t, b)).1,
        (A.sectionSevenEllipticCentralImageHomeomorph.symm
          (A.centralFourthPeriodCircle (t, b))).2⟩ = b.1.re := by
  change (A.centralFamilyCoordinate
    (A.sectionSevenEllipticCentralImageHomeomorph
      (A.sectionSevenEllipticCentralImageHomeomorph.symm
        (A.centralFourthPeriodCircle (t, b))))).1.re = _
  rw [Homeomorph.apply_symm_apply, A.centralFourthPeriodCircle_coordinate]

public theorem centralFourthPeriodCircleToUnion_mem_three
    (R : A.SectionSevenAffineRadialCompletionInput)
    (t : UnitAddCircle) (b : TwicePuncturedComplex) (hb : b.1.re < 2 / 3) :
    (centralFourthPeriodCircleToUnion R.twoDiscCover (t, b)).1 ∈
      R.twoDiscCover.orderThreeSide := by
  change _ ∈ A.sectionSevenActualAffineSplit.allocation.orderThreeSide
  refine Or.inr ⟨A.sectionSevenEllipticCentralImageHomeomorph.symm
    (A.centralFourthPeriodCircle (t, b)), ?_, rfl⟩
  exact (centralFourthPeriodCircleToUnion_height R.twoDiscCover t b).trans_lt hb

public theorem centralFourthPeriodCircleToUnion_mem_four
    (R : A.SectionSevenAffineRadialCompletionInput)
    (t : UnitAddCircle) (b : TwicePuncturedComplex) (hb : 1 / 3 < b.1.re) :
    (centralFourthPeriodCircleToUnion R.twoDiscCover (t, b)).1 ∈
      R.twoDiscCover.orderFourSide := by
  change _ ∈ A.sectionSevenActualAffineSplit.allocation.orderFourSide
  refine Or.inr ⟨A.sectionSevenEllipticCentralImageHomeomorph.symm
    (A.centralFourthPeriodCircle (t, b)), ?_, rfl⟩
  exact hb.trans_eq (centralFourthPeriodCircleToUnion_height R.twoDiscCover t b).symm

private theorem zeroMeridian_re_lt (t : unitInterval) :
    (twicePuncturedClockwiseZeroMeridian t).1.re < 2 / 3 := by
  have hnorm := circleMap_mem_sphere (0 : ℂ) (by norm_num : 0 ≤ (2 : ℝ)⁻¹)
    (-(2 * Real.pi * (t : ℝ)))
  rw [Metric.mem_sphere, dist_zero_right] at hnorm
  have hle := Complex.re_le_norm (circleMap (0 : ℂ) (2 : ℝ)⁻¹
    (-(2 * Real.pi * (t : ℝ))))
  change (circleMap (0 : ℂ) (2 : ℝ)⁻¹ (-(2 * Real.pi * (t : ℝ)))).re < _
  rw [hnorm] at hle
  linarith

private theorem oneMeridian_re_gt (t : unitInterval) :
    1 / 3 < (twicePuncturedClockwiseOneMeridian t).1.re := by
  have hnorm := circleMap_mem_sphere' (1 : ℂ) (-(2 : ℝ)⁻¹)
    (-(2 * Real.pi * (t : ℝ)))
  rw [Metric.mem_sphere, dist_comm, Complex.dist_eq] at hnorm
  have hle := Complex.re_le_norm (1 - circleMap (1 : ℂ) (-(2 : ℝ)⁻¹)
    (-(2 * Real.pi * (t : ℝ))))
  change (1 : ℝ) / 3 < (circleMap (1 : ℂ) (-(2 : ℝ)⁻¹)
    (-(2 * Real.pi * (t : ℝ)))).re
  rw [hnorm] at hle
  norm_num at hle
  linarith

private theorem canonicalBoundary_left_image
    (D : A.SectionSevenEllipticTwoDiscCoverData)
    (x : IntegralSingularHomology 2 D.orderThreeSide) :
    canonicalBoundary D 1 (integralSingularHomologyMap 2
      (IntegralMayerVietoris.leftToUnion D.orderThreeSide D.orderFourSide) x) = 0 := by
  have h := (presentationTwo (D := D)).boundary_inclusion (x, 0)
  change canonicalBoundary D 1 (integralSingularHomologyMap 2
    (IntegralMayerVietoris.leftToUnion D.orderThreeSide D.orderFourSide) x +
      integralSingularHomologyMap 2
        (IntegralMayerVietoris.rightToUnion D.orderThreeSide D.orderFourSide) 0) = 0 at h
  simpa only [map_zero, add_zero] using h

private theorem canonicalBoundary_right_image
    (D : A.SectionSevenEllipticTwoDiscCoverData)
    (x : IntegralSingularHomology 2 D.orderFourSide) :
    canonicalBoundary D 1 (integralSingularHomologyMap 2
      (IntegralMayerVietoris.rightToUnion D.orderThreeSide D.orderFourSide) x) = 0 := by
  have h := (presentationTwo (D := D)).boundary_inclusion (0, x)
  change canonicalBoundary D 1 (integralSingularHomologyMap 2
    (IntegralMayerVietoris.leftToUnion D.orderThreeSide D.orderFourSide) 0 +
      integralSingularHomologyMap 2
        (IntegralMayerVietoris.rightToUnion D.orderThreeSide D.orderFourSide) x) = 0 at h
  simpa only [map_zero, zero_add] using h

private theorem centralCircleSweep_boundary_left
    (R : A.SectionSevenAffineRadialCompletionInput)
    {b : TwicePuncturedComplex} (p : Path b b)
    (hp : ∀ t, (p t).1.re < 2 / 3) :
    canonicalBoundary R.twoDiscCover 1
      (circleSweepClass (centralFourthPeriodCircleToUnion R.twoDiscCover) p) = 0 := by
  let c := pathCircleMap p
  let f : C(UnitAddCircle × StdTorus 1, R.twoDiscCover.orderThreeSide) := by
    refine ⟨fun z ↦ ⟨(centralFourthPeriodCircleToUnion R.twoDiscCover (z.1, c z.2)).1, ?_⟩, ?_⟩
    · apply centralFourthPeriodCircleToUnion_mem_three
      obtain ⟨t, ht⟩ := pathCircleMap_mem_range p z.2
      rw [← ht]
      exact hp t
    · exact (continuous_subtype_val.comp
        ((centralFourthPeriodCircleToUnion R.twoDiscCover).continuous.comp
          (circleProductMap c).continuous)).subtype_mk _
  have hf : (IntegralMayerVietoris.leftToUnion
      R.twoDiscCover.orderThreeSide R.twoDiscCover.orderFourSide).comp f =
      (centralFourthPeriodCircleToUnion R.twoDiscCover).comp (circleProductMap c) := by
    ext z
    rfl
  change canonicalBoundary R.twoDiscCover 1
    (integralSingularHomologyMap 2 (centralFourthPeriodCircleToUnion R.twoDiscCover)
      (normalizedCircleCross 1 (StandardCircleHomologyLiftDegree.loopHomologyClass p))) = 0
  rw [← pathCircleMap_homology p, ← positiveCircleCross_eq_normalized,
    positiveCircleCross, integralSingularHomologyMap_comp_wang]
  change canonicalBoundary R.twoDiscCover 1
    (integralSingularHomologyMap 2
      ((centralFourthPeriodCircleToUnion R.twoDiscCover).comp (circleProductMap c)) _) = 0
  rw [← hf, ← integralSingularHomologyMap_comp_wang]
  exact canonicalBoundary_left_image R.twoDiscCover _

private theorem centralCircleSweep_boundary_right
    (R : A.SectionSevenAffineRadialCompletionInput)
    {b : TwicePuncturedComplex} (p : Path b b)
    (hp : ∀ t, 1 / 3 < (p t).1.re) :
    canonicalBoundary R.twoDiscCover 1
      (circleSweepClass (centralFourthPeriodCircleToUnion R.twoDiscCover) p) = 0 := by
  let c := pathCircleMap p
  let f : C(UnitAddCircle × StdTorus 1, R.twoDiscCover.orderFourSide) := by
    refine ⟨fun z ↦ ⟨(centralFourthPeriodCircleToUnion R.twoDiscCover (z.1, c z.2)).1, ?_⟩, ?_⟩
    · apply centralFourthPeriodCircleToUnion_mem_four
      obtain ⟨t, ht⟩ := pathCircleMap_mem_range p z.2
      rw [← ht]
      exact hp t
    · exact (continuous_subtype_val.comp
        ((centralFourthPeriodCircleToUnion R.twoDiscCover).continuous.comp
          (circleProductMap c).continuous)).subtype_mk _
  have hf : (IntegralMayerVietoris.rightToUnion
      R.twoDiscCover.orderThreeSide R.twoDiscCover.orderFourSide).comp f =
      (centralFourthPeriodCircleToUnion R.twoDiscCover).comp (circleProductMap c) := by
    ext z
    rfl
  change canonicalBoundary R.twoDiscCover 1
    (integralSingularHomologyMap 2 (centralFourthPeriodCircleToUnion R.twoDiscCover)
      (normalizedCircleCross 1 (StandardCircleHomologyLiftDegree.loopHomologyClass p))) = 0
  rw [← pathCircleMap_homology p, ← positiveCircleCross_eq_normalized,
    positiveCircleCross, integralSingularHomologyMap_comp_wang]
  change canonicalBoundary R.twoDiscCover 1
    (integralSingularHomologyMap 2
      ((centralFourthPeriodCircleToUnion R.twoDiscCover).comp (circleProductMap c)) _) = 0
  rw [← hf, ← integralSingularHomologyMap_comp_wang]
  exact canonicalBoundary_right_image R.twoDiscCover _

public theorem centralFourthPeriodCircle_normalizedCross_boundary
    (R : A.SectionSevenAffineRadialCompletionInput)
    (x : IntegralSingularHomology 1 TwicePuncturedComplex) :
    canonicalBoundary R.twoDiscCover 1
      (integralSingularHomologyMap 2 (centralFourthPeriodCircleToUnion R.twoDiscCover)
        (normalizedCircleCross 1 x)) = 0 := by
  let f := (canonicalBoundary R.twoDiscCover 1).comp
    ((integralSingularHomologyMap 2
      (centralFourthPeriodCircleToUnion R.twoDiscCover)).comp (normalizedCircleCross 1))
  have hf : f = 0 := twicePuncturedHomologyOneHom_eq_zero f
    (centralCircleSweep_boundary_left R twicePuncturedClockwiseZeroMeridian zeroMeridian_re_lt)
    (centralCircleSweep_boundary_right R twicePuncturedClockwiseOneMeridian oneMeridian_re_gt)
  exact DFunLike.congr_fun hf x


public theorem centralFourthPeriodCircle_boundary_of_projection_zero
    (R : A.SectionSevenAffineRadialCompletionInput)
    (x : IntegralSingularHomology 2 (UnitAddCircle × TwicePuncturedComplex))
    (hx : integralSingularHomologyMap 2 productFiberProjection x = 0) :
    canonicalBoundary R.twoDiscCover 1
      (integralSingularHomologyMap 2 (centralFourthPeriodCircleToUnion R.twoDiscCover) x) = 0 := by
  have h : x = normalizedCircleCross 1 (canonicalProductWangBoundary 1 x) := by
    apply circleProductClass_ext 1
    · rw [normalizedCircleCross_boundary]
    · rw [hx, normalizedCircleCross_projection]
  rw [h]
  exact centralFourthPeriodCircle_normalizedCross_boundary R _

end SphereSixComplex.Geometry.PaperAnalyticData
end
end
