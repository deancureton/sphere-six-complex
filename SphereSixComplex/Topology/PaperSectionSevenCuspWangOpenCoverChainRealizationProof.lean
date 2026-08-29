module

public import SphereSixComplex.Topology.PaperSectionSevenCuspWangOpenCoverChainRealizationGeometry

/-!
# Sign rigidity of the cusp Wang chain realization

The Wang input used by the cusp collar is supplied by
`finiteBouquetMappingTorusWangSequenceOfCover`, whose specification
`FiniteBouquetMappingTorusWangSequence` consists of three exactness statements and nothing else.
This file records what that specification leaves undetermined.

`FiniteBouquetMappingTorusWangSequence.neg` shows the specification is blind to the sign of the
connecting map: negating the boundary produces another finite-bouquet Wang sequence, so the
established Wang sequence and its negation are indistinguishable by their stated properties.

`ChainRealizationFor` is `ActualCuspWangOpenCoverChainRealization` with its connecting map made a
parameter; the established structure is the case `actualCuspWangBoundaryHom A`.  It is *not*
blind to that sign: `cuspPulledBackBoundaryHom_eq_zero_of_chainRealizationFor_neg` shows that a
realization for a connecting map and one for its negation together force the pulled-back
cusp-cover boundary to vanish, and `false_of_chainRealizationFor_neg` turns that into a
contradiction with the Section 7 boundary basis computation.

Consequently the chain realization is not a consequence of the exactness data alone: it also
fixes an orientation.  Pinning that orientation requires a Wang boundary that is constructed
rather than merely specified.  That is now the case: the boundary in use is the Mayer--Vietoris
boundary of the vertex/edge cover of the mapping torus, exposed by
`finiteBouquetMappingTorusWangSequenceOfCover_boundary`.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory Set TopologicalSpace
open scoped ContinuousMap

namespace SphereSixComplex

section FiniteBouquet

variable {ι F : Type}
  [Fintype ι] [Inhabited ι] [TopologicalSpace ι] [DiscreteTopology ι] [TopologicalSpace F]

/-- Negating the connecting map of a finite-bouquet Wang sequence gives another finite-bouquet
Wang sequence: all three exactness fields are invariant under a sign change of the boundary. -/
public def FiniteBouquetMappingTorusWangSequence.neg {φ : ι → F ≃ₜ F} {k : ℕ}
    (W : FiniteBouquetMappingTorusWangSequence φ k) :
    FiniteBouquetMappingTorusWangSequence φ k where
  boundary := -W.boundary
  exact_highDifference_inclusion := W.exact_highDifference_inclusion
  exact_inclusion_boundary := by
    intro x
    have h := W.exact_inclusion_boundary x
    change (-W.boundary) x = 0 ↔ _
    rw [AddMonoidHom.neg_apply, neg_eq_zero]
    exact h
  exact_boundary_lowDifference := by
    intro y
    rw [W.exact_boundary_lowDifference y]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨-x, by simp⟩
    · rintro ⟨x, rfl⟩
      exact ⟨-x, by simp⟩

/-- The circle Wang connecting map read off from an arbitrary one-loop bouquet Wang sequence,
rather than from the constructed one. -/
public noncomputable def circleBoundaryOf {F : Type} [TopologicalSpace F] {φ : F ≃ₜ F}
    {k : ℕ} (W : FiniteBouquetMappingTorusWangSequence (fun _ : Unit ↦ φ) k) :
    IntegralSingularHomology (k + 1) (CircleMappingTorus φ) →+
      IntegralSingularHomology k F where
  toFun x := W.boundary x ()
  map_zero' := by simp
  map_add' := by simp

/-- The constructed one-loop Wang sequence gives exactly the boundary of the circle Wang
presentation used throughout the development. -/
public theorem circleBoundaryOf_established {F : Type} [TopologicalSpace F] (φ : F ≃ₜ F)
    (k : ℕ) :
    circleBoundaryOf (finiteBouquetMappingTorusWangSequenceOfCover (fun _ : Unit ↦ φ) k) =
      (circleMappingTorusWangPresentation φ k).boundary :=
  rfl

/-- Reading the circle boundary off a negated Wang sequence negates it. -/
public theorem circleBoundaryOf_neg {F : Type} [TopologicalSpace F] {φ : F ≃ₜ F} {k : ℕ}
    (W : FiniteBouquetMappingTorusWangSequence (fun _ : Unit ↦ φ) k) :
    circleBoundaryOf W.neg = -circleBoundaryOf W := by
  apply AddMonoidHom.ext
  intro x
  rfl

end FiniteBouquet


namespace Geometry.PaperAnalyticData

variable {A : PaperAnalyticData} (D : A.SectionSevenEllipticTwoDiscCoverData)

namespace SectionSevenEllipticTwoDiscCoverData

/-- The type of connecting maps the cusp chain realization can be asked to realize. -/
public abbrev CuspFiberBoundaryHom (A : PaperAnalyticData) : Type :=
  IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0) →+
    (let G := A.actualCuspRadialClutchingData
     let _ := G.fiberTopology
     IntegralSingularHomology 1 G.Fiber)

/-- `ActualCuspWangOpenCoverChainRealization`, parameterized by the connecting map that the
fibre map is asked to carry to the open-cover boundary.  The actual structure is the case
`boundary = actualCuspWangBoundaryHom A`. -/
public structure ChainRealizationFor (boundary : CuspFiberBoundaryHom A) where
  fiberToCuspCoverIntersectionMap :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    C(G.Fiber,
      (Opens.toTopCat (TopCat.of (A.openEmbeddingStarData.collarSource 0))).obj
        (D.cuspOrderThreeOpen ⊓ D.cuspOrderFourOpen))
  fiberToBand_homology :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    D.canonicalCuspFiberToBandHomologyOne =
      D.cuspCoverIntersectionToEllipticBandHomologyOne.comp
        (integralSingularHomologyMap 1 fiberToCuspCoverIntersectionMap)
  wangBoundary_eq_chainConnecting :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    (integralSingularHomologyMap 1 fiberToCuspCoverIntersectionMap).comp boundary =
      D.cuspOpenCoverConnectingHom

/-- The actual chain realization is the parameterized one at the established Wang boundary. -/
public def ActualCuspWangOpenCoverChainRealization.toChainRealizationFor
    (R : D.ActualCuspWangOpenCoverChainRealization) :
    D.ChainRealizationFor (actualCuspWangBoundaryHom A) where
  fiberToCuspCoverIntersectionMap := R.fiberToCuspCoverIntersectionMap
  fiberToBand_homology := R.fiberToBand_homology
  wangBoundary_eq_chainConnecting := R.wangBoundary_eq_chainConnecting

/-- Every chain realization computes the pulled-back cusp-cover boundary as the canonical
fibre-to-band map applied after the connecting map it realizes. -/
public theorem cuspPulledBackBoundaryHom_eq_comp_of_chainRealizationFor
    {boundary : CuspFiberBoundaryHom A} (R : D.ChainRealizationFor boundary) :
    D.cuspPulledBackBoundaryHom =
      D.canonicalCuspFiberToBandHomologyOne.comp boundary := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  apply AddMonoidHom.ext
  intro x
  have h3 := DFunLike.congr_fun R.wangBoundary_eq_chainConnecting x
  have h2 := DFunLike.congr_fun R.fiberToBand_homology (boundary x)
  rw [D.cuspPulledBackBoundaryHom_eq_comp]
  simp only [AddMonoidHom.comp_apply] at h3 h2 ⊢
  rw [← h3]
  exact h2.symm

/-- Sign rigidity.  The chain realization cannot hold simultaneously for a connecting map and
for its negation unless the pulled-back cusp-cover boundary is its own negative. -/
public theorem cuspPulledBackBoundaryHom_eq_neg_self_of_chainRealizationFor_neg
    {boundary : CuspFiberBoundaryHom A}
    (R : D.ChainRealizationFor boundary) (R' : D.ChainRealizationFor (-boundary)) :
    D.cuspPulledBackBoundaryHom = -D.cuspPulledBackBoundaryHom := by
  have h := D.cuspPulledBackBoundaryHom_eq_comp_of_chainRealizationFor R
  have h' := D.cuspPulledBackBoundaryHom_eq_comp_of_chainRealizationFor R'
  apply AddMonoidHom.ext
  intro x
  have hx := DFunLike.congr_fun h x
  have hx' := DFunLike.congr_fun h' x
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.neg_apply, map_neg] at hx hx'
  rw [AddMonoidHom.neg_apply]
  conv_rhs => rw [hx]
  exact hx'

/-- The first homology of the actual elliptic band overlap is torsion free: it is the standard
period basis of the selected full-rank band torus. -/
public theorem bandHomologyOne_eq_zero_of_eq_neg
    {x : IntegralSingularHomology 1
      (D.orderThreeSide ∩ D.orderFourSide : Set A.SectionSevenEllipticInterior)}
    (h : x = -x) : x = 0 := by
  let e := (D.bandHomologyEquiv 1).trans
    (EstablishedTorusHomology.additiveTorusHomologyBasis D.bandParameter D.bandFullRank).degreeOne
  have he : e x = -e x := by
    rw [← map_neg, ← h]
  have h0 : e x = 0 := by
    funext i
    have hi := congrFun he i
    simp only [Pi.neg_apply] at hi
    simp only [Pi.zero_apply]
    omega
  have := e.injective (h0.trans (map_zero e).symm)
  exact this

/-- Sign rigidity, in its sharp form: two-sided realizability forces the pulled-back cusp-cover
boundary to vanish, which is exactly what the Section 7 basis calculation forbids. -/
public theorem cuspPulledBackBoundaryHom_eq_zero_of_chainRealizationFor_neg
    {boundary : CuspFiberBoundaryHom A}
    (R : D.ChainRealizationFor boundary) (R' : D.ChainRealizationFor (-boundary)) :
    D.cuspPulledBackBoundaryHom = 0 := by
  have h := D.cuspPulledBackBoundaryHom_eq_neg_self_of_chainRealizationFor_neg R R'
  apply AddMonoidHom.ext
  intro x
  exact D.bandHomologyOne_eq_zero_of_eq_neg (DFunLike.congr_fun h x)

/-- The established chain realization, together with a realization for the negated Wang
connecting map, would force the pulled-back cusp boundary to vanish. -/
public theorem cuspPulledBackBoundaryHom_eq_zero_of_both_signs
    (R : D.ActualCuspWangOpenCoverChainRealization)
    (R' : D.ChainRealizationFor (-(actualCuspWangBoundaryHom A))) :
    D.cuspPulledBackBoundaryHom = 0 :=
  D.cuspPulledBackBoundaryHom_eq_zero_of_chainRealizationFor_neg
    (ActualCuspWangOpenCoverChainRealization.toChainRealizationFor D R) R'

/-- A one-loop bouquet Wang sequence for the actual radial cusp clutching map: exactly the data
`FiniteBouquetMappingTorusWangSequence` supplies, with nothing beyond its three exactness
fields. -/
public abbrev CuspClutchingWangSequence (A : PaperAnalyticData) : Type :=
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  FiniteBouquetMappingTorusWangSequence (fun _ : Unit ↦ G.clutching) 1

/-- The cusp Wang connecting map attached to an arbitrary such Wang sequence. -/
public noncomputable def cuspWangBoundaryHomOf (A : PaperAnalyticData)
    (W : CuspClutchingWangSequence A) : CuspFiberBoundaryHom A := by
  let G := A.actualCuspRadialClutchingData
  letI := G.fiberTopology
  exact (circleBoundaryOf W).comp
    (integralSingularHomologyEquivOfHomotopyEquiv 2 G.totalHomotopyEquiv).toAddMonoidHom

/-- The Wang sequence actually used, constructed from the vertex/edge open cover of the mapping
torus. -/
public noncomputable def establishedCuspClutchingWangSequence (A : PaperAnalyticData) :
    CuspClutchingWangSequence A := by
  let G := A.actualCuspRadialClutchingData
  letI := G.fiberTopology
  exact finiteBouquetMappingTorusWangSequenceOfCover (fun _ : Unit ↦ G.clutching) 1

/-- At that Wang sequence this is the actual cusp Wang connecting map. -/
public theorem cuspWangBoundaryHomOf_established (A : PaperAnalyticData) :
    cuspWangBoundaryHomOf A (establishedCuspClutchingWangSequence A) =
      actualCuspWangBoundaryHom A :=
  rfl

/-- The sign-flipped Wang sequence of the actual cusp clutching. -/
public noncomputable def cuspClutchingWangSequenceNeg (A : PaperAnalyticData)
    (W : CuspClutchingWangSequence A) : CuspClutchingWangSequence A := by
  let G := A.actualCuspRadialClutchingData
  letI := G.fiberTopology
  exact W.neg

/-- Negating the Wang sequence negates the cusp Wang connecting map. -/
public theorem cuspWangBoundaryHomOf_neg (A : PaperAnalyticData)
    (W : CuspClutchingWangSequence A) :
    cuspWangBoundaryHomOf A (cuspClutchingWangSequenceNeg A W) =
      -cuspWangBoundaryHomOf A W := by
  apply AddMonoidHom.ext
  intro x
  rfl

/-- **No uniform proof.**  The established Wang input is specified by exactness alone, and
exactness is invariant under a sign change of the connecting map.  Consequently a proof of
`ActualCuspWangOpenCoverChainRealization` that used only that specification -- that is, one
producing a realization for the connecting map of an arbitrary Wang sequence of the actual cusp
clutching -- would force the pulled-back cusp-cover boundary to vanish. -/
public theorem cuspPulledBackBoundaryHom_eq_zero_of_uniform_chainRealization
    (H : ∀ W : CuspClutchingWangSequence A, D.ChainRealizationFor (cuspWangBoundaryHomOf A W)) :
    D.cuspPulledBackBoundaryHom = 0 := by
  let W : CuspClutchingWangSequence A := establishedCuspClutchingWangSequence A
  have R' := H (cuspClutchingWangSequenceNeg A W)
  rw [cuspWangBoundaryHomOf_neg] at R'
  exact D.cuspPulledBackBoundaryHom_eq_zero_of_chainRealizationFor_neg (H W) R'

/-- Two-sided realizability is outright contradictory once the Section 7 boundary basis
computation is available: `e5_boundary` would read `1 = 0`. -/
public theorem false_of_chainRealizationFor_neg
    {boundary : CuspFiberBoundaryHom A}
    (N : A.EllipticBandHomologyAlignment D)
    (B : D.SectionSevenCuspPulledBackBoundaryBasisBridge N)
    (R : D.ChainRealizationFor boundary) (R' : D.ChainRealizationFor (-boundary)) :
    False := by
  have hzero := D.cuspPulledBackBoundaryHom_eq_zero_of_chainRealizationFor_neg R R'
  have h0 : D.cuspPulledBackBoundary
      (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (5 : Fin 6) 1)) = 0 := by
    rw [← D.cuspPulledBackBoundaryHom_apply, hzero]
    rfl
  have hval : (N.actualHomologyCoordinates.degreeTwoInvariantEquiv.symm 1).1 = 0 :=
    B.e5_boundary.symm.trans h0
  have hinv : N.actualHomologyCoordinates.degreeTwoInvariantEquiv.symm 1 = 0 :=
    Subtype.ext hval
  have h1 : (1 : ℤ) = 0 := by
    have h := congrArg N.actualHomologyCoordinates.degreeTwoInvariantEquiv hinv
    rw [LinearEquiv.apply_symm_apply, map_zero] at h
    exact h
  exact one_ne_zero h1

end SectionSevenEllipticTwoDiscCoverData

end Geometry.PaperAnalyticData

end SphereSixComplex
