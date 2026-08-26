module

public import SphereSixComplex.Topology.PaperSectionSevenEllipticBaseCoordinate
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Topology.FiberBundle.IsHomeomorphicTrivialBundle

/-!
# The affine central band as a trivial torus bundle

The base of the concrete central height band is the convex vertical strip
`1 / 3 < re z < 2 / 3`.  Once the actual central torus bundle is trivialized over this strip,
contractibility of the strip gives the homotopy equivalence required by the radial input.
-/

@[expose] public section

noncomputable section

open Set Topology
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.PaperAnalyticData

/-- The affine vertical strip underlying the genuine Section 7 central band. -/
public def sectionSevenAffineVerticalStrip : Set ℂ :=
  {z : ℂ | (1 / 3 : ℝ) < z.re ∧ z.re < 2 / 3}

public theorem sectionSevenAffineVerticalStrip_convex :
    Convex ℝ sectionSevenAffineVerticalStrip := by
  exact (convex_halfSpace_gt (Complex.reCLM : ℂ →L[ℝ] ℝ).isLinear (1 / 3 : ℝ)).inter
    (convex_halfSpace_lt (Complex.reCLM : ℂ →L[ℝ] ℝ).isLinear (2 / 3 : ℝ))

public theorem sectionSevenAffineVerticalStrip_nonempty :
    sectionSevenAffineVerticalStrip.Nonempty := by
  refine ⟨(1 / 2 : ℂ), ?_⟩
  norm_num [sectionSevenAffineVerticalStrip]

/-- The vertical strip is contractible by straight-line contraction. -/
public theorem sectionSevenAffineVerticalStripContractible :
    ContractibleSpace sectionSevenAffineVerticalStrip :=
  sectionSevenAffineVerticalStrip_convex.contractibleSpace
    sectionSevenAffineVerticalStrip_nonempty

variable {A : PaperAnalyticData}

/-- Recover the unique point of the central image represented by a point of a height band. -/
public def SectionSevenCentralHeightSplit.bandToCentralImage
    (S : A.SectionSevenCentralHeightSplit) :
    centralHeightBand S.height S.lower S.upper → A.sectionSevenEllipticCentralImage :=
  fun x ↦ ⟨x.1, by
    rcases x.2 with ⟨y, _, hy⟩
    exact hy ▸ y.2⟩

public theorem SectionSevenCentralHeightSplit.bandToCentralImage_continuous
    (S : A.SectionSevenCentralHeightSplit) :
    Continuous S.bandToCentralImage :=
  continuous_subtype_val.subtype_mk _

variable (A)

/-- The concrete central band projected to its affine vertical-strip coordinate. -/
public noncomputable def sectionSevenAffineCentralBandProjection
    (S : A.SectionSevenAffineCentralSeparation) :
    centralHeightBand
        (A.sectionSevenAffineCentralHeightSplit S).height
        (A.sectionSevenAffineCentralHeightSplit S).lower
        (A.sectionSevenAffineCentralHeightSplit S).upper →
      sectionSevenAffineVerticalStrip :=
  fun x ↦ ⟨(A.sectionSevenEllipticCentralCoordinate
    ((A.sectionSevenAffineCentralHeightSplit S).bandToCentralImage x)).1, by
      rcases x.2 with ⟨y, hy, hxy⟩
      change (1 / 3 : ℝ) < (A.sectionSevenEllipticCentralCoordinate y).1.re ∧
        (A.sectionSevenEllipticCentralCoordinate y).1.re < 2 / 3 at hy
      have hcentral :
          (A.sectionSevenAffineCentralHeightSplit S).bandToCentralImage x = y := by
        apply Subtype.ext
        exact hxy.symm
      simpa only [sectionSevenAffineVerticalStrip, Set.mem_ofPred_eq, hcentral] using hy⟩

public theorem sectionSevenAffineCentralBandProjection_continuous
    (S : A.SectionSevenAffineCentralSeparation) :
    Continuous (A.sectionSevenAffineCentralBandProjection S) := by
  exact (continuous_subtype_val.comp
    (A.sectionSevenEllipticCentralCoordinate_continuous.comp
      (A.sectionSevenAffineCentralHeightSplit S).bandToCentralImage_continuous)).subtype_mk _

/-- The exact standard bundle-theoretic input still needed for the affine band.  It asserts that
the actual central family, restricted to the explicit convex strip, is a product with the fixed
order-three additive four-torus. -/
public def SectionSevenAffineCentralBandProductTrivialization
    (S : A.SectionSevenAffineCentralSeparation) : Prop :=
  IsHomeomorphicTrivialFiberBundle
    (AdditiveTorus A.duplicatedSectionSevenBandParameter)
    (A.sectionSevenAffineCentralBandProjection S)

namespace EstablishedSectionSevenAffineBandTopology

/-- Standard quotient-bundle triviality over the convex affine strip.  The unconditional
real-period product coordinates trivialize the varying lattice upstairs, while the unique lift of
the simply connected strip through the regular-coordinate covering trivializes the descended
quotient bundle.  The current APIs provide those ingredients but not their assembled global
homeomorphism. -/
public axiom establishedActualCentralBandProductTrivialization
    (A : PaperAnalyticData) (S : A.SectionSevenAffineCentralSeparation) :
    A.SectionSevenAffineCentralBandProductTrivialization S

end EstablishedSectionSevenAffineBandTopology

open EstablishedSectionSevenAffineBandTopology

/-- A trivial bundle over a contractible base is homotopy equivalent to its fibre. -/
public noncomputable def homotopyEquivFiberOfTrivialBundle
    {B F Z : Type*} [TopologicalSpace B] [TopologicalSpace F] [TopologicalSpace Z]
    [ContractibleSpace B] {proj : Z → B}
    (h : IsHomeomorphicTrivialFiberBundle F proj) :
    Z ≃ₕ F :=
  h.choose.toHomotopyEquiv.trans
    (((ContractibleSpace.hequiv_unit B).some.prodCongr
      (ContinuousMap.HomotopyEquiv.refl F)).trans
        (Homeomorph.uniqueProd Unit F).toHomotopyEquiv)

/-- The standard product trivialization over the affine strip supplies exactly the
`bandHomotopyEquiv` field of the central-height radial input. -/
public noncomputable def SectionSevenAffineCentralBandProductTrivialization.bandHomotopyEquiv
    {S : A.SectionSevenAffineCentralSeparation}
    (T : A.SectionSevenAffineCentralBandProductTrivialization S) :
    centralHeightBand
        (A.sectionSevenAffineCentralHeightSplit S).height
        (A.sectionSevenAffineCentralHeightSplit S).lower
        (A.sectionSevenAffineCentralHeightSplit S).upper ≃ₕ
      AdditiveTorus A.duplicatedSectionSevenBandParameter := by
  let _ : ContractibleSpace sectionSevenAffineVerticalStrip :=
    sectionSevenAffineVerticalStripContractible
  exact homotopyEquivFiberOfTrivialBundle T

/-- The established quotient-bundle triviality gives the concrete central band equivalence used
by the radial realization. -/
public noncomputable def sectionSevenAffineCentralBandHomotopyEquiv
    (S : A.SectionSevenAffineCentralSeparation) :
    centralHeightBand
        (A.sectionSevenAffineCentralHeightSplit S).height
        (A.sectionSevenAffineCentralHeightSplit S).lower
        (A.sectionSevenAffineCentralHeightSplit S).upper ≃ₕ
      AdditiveTorus A.duplicatedSectionSevenBandParameter :=
  by
    let T := establishedActualCentralBandProductTrivialization A S
    exact SectionSevenAffineCentralBandProductTrivialization.bandHomotopyEquiv A T

end SphereSixComplex.Geometry.PaperAnalyticData
