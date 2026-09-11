module

public import SphereSixComplex.Paper.Topology.PaperSectionSevenEllipticBaseCoordinate
public import Mathlib.Topology.FiberBundle.IsHomeomorphicTrivialBundle

/-!
# Affine central band definitions

The base of the concrete central height band is the convex vertical strip
`1 / 3 < re z < 2 / 3`.  This module collects the strip, the band projection onto it, and the
statement that the actual central torus bundle is a product over that strip, together with the
generic fibre-homotopy consequence of triviality.  It carries no trivialization proof, so the
proof itself can be developed in a separate module and imported back.
-/

@[expose] public section

noncomputable section

open Set Topology
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.PaperAnalyticData

/-- The affine vertical strip underlying the genuine Section 7 central band. -/
public def affineVerticalStrip : Set ℂ :=
  {z : ℂ | (1 / 3 : ℝ) < z.re ∧ z.re < 2 / 3}

public theorem affineVerticalStrip_convex :
    Convex ℝ affineVerticalStrip := by
  exact (convex_halfSpace_gt (Complex.reCLM : ℂ →L[ℝ] ℝ).isLinear (1 / 3 : ℝ)).inter
    (convex_halfSpace_lt (Complex.reCLM : ℂ →L[ℝ] ℝ).isLinear (2 / 3 : ℝ))

public theorem affineVerticalStrip_nonempty :
    affineVerticalStrip.Nonempty := by
  refine ⟨(1 / 2 : ℂ), ?_⟩
  norm_num [affineVerticalStrip]

/-- The vertical strip is contractible by straight-line contraction. -/
public theorem affineVerticalStrip_contractibleSpace :
    ContractibleSpace affineVerticalStrip :=
  affineVerticalStrip_convex.contractibleSpace
    affineVerticalStrip_nonempty

variable {A : PaperAnalyticData}

/-- Recover the unique point of the central image represented by a point of a height band. -/
public def CentralHeightSplit.bandToCentralImage
    (S : A.CentralHeightSplit) :
    centralHeightBand S.height S.lower S.upper → A.ellipticCentralImage :=
  fun x ↦ ⟨x.1, by
    rcases x.2 with ⟨y, _, hy⟩
    exact hy ▸ y.2⟩

public theorem CentralHeightSplit.bandToCentralImage_continuous
    (S : A.CentralHeightSplit) :
    Continuous S.bandToCentralImage :=
  continuous_subtype_val.subtype_mk _

variable (A)

/-- The concrete central band projected to its affine vertical-strip coordinate. -/
public noncomputable def affineCentralBandProjection
    (S : A.AffineCentralSeparation) :
    centralHeightBand
        (A.affineCentralHeightSplit S).height
        (A.affineCentralHeightSplit S).lower
        (A.affineCentralHeightSplit S).upper →
      affineVerticalStrip :=
  fun x ↦ ⟨(A.ellipticCentralCoordinate
    ((A.affineCentralHeightSplit S).bandToCentralImage x)).1, by
      rcases x.2 with ⟨y, hy, hxy⟩
      change (1 / 3 : ℝ) < (A.ellipticCentralCoordinate y).1.re ∧
        (A.ellipticCentralCoordinate y).1.re < 2 / 3 at hy
      have hcentral :
          (A.affineCentralHeightSplit S).bandToCentralImage x = y := by
        apply Subtype.ext
        exact hxy.symm
      simpa only [affineVerticalStrip, Set.mem_ofPred_eq, hcentral] using hy⟩

public theorem affineCentralBandProjection_continuous
    (S : A.AffineCentralSeparation) :
    Continuous (A.affineCentralBandProjection S) := by
  exact (continuous_subtype_val.comp
    (A.ellipticCentralCoordinate_continuous.comp
      (A.affineCentralHeightSplit S).bandToCentralImage_continuous)).subtype_mk _

/-- The exact standard bundle-theoretic input still needed for the affine band.  It asserts that
the actual central family, restricted to the explicit convex strip, is a product with the fixed
order-three additive four-torus. -/
public def AffineCentralBandProductTrivialization
    (S : A.AffineCentralSeparation) : Prop :=
  IsHomeomorphicTrivialFiberBundle
    (AdditiveTorus A.duplicatedSectionSevenBandParameter)
    (A.affineCentralBandProjection S)

/-- A product decomposition over a contractible base is a homotopy equivalence onto the fibre.

The product homeomorphism is taken as *data*.  Passing only the proposition
`IsHomeomorphicTrivialFiberBundle` and selecting a witness with `Exists.choose` would leave the
resulting fibre coordinate completely undetermined, because that proposition constrains the base
coordinate alone; see `exists_productTrivialization_fiberCoordinate_comp`. -/
public noncomputable def homotopyEquivFiberOfTrivialBundle
    {B F Z : Type*} [TopologicalSpace B] [TopologicalSpace F] [TopologicalSpace Z]
    [ContractibleSpace B] (e : Z ≃ₜ B × F) :
    Z ≃ₕ F :=
  e.toHomotopyEquiv.trans
    (((ContractibleSpace.hequiv_unit B).some.prodCongr
      (ContinuousMap.HomotopyEquiv.refl F)).trans
        (Homeomorph.uniqueProd Unit F).toHomotopyEquiv)

end SphereSixComplex.Geometry.PaperAnalyticData
