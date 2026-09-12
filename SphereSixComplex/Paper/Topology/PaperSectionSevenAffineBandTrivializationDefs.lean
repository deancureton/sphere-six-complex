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

namespace SphereSixComplex.Geometry.AnalyticData

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

variable {A : AnalyticData}

/-- Recover the unique point of the central image represented by a point of a height band. -/
public def CentralHeightSplit.bandToCentralImage
    (S : A.CentralHeightSplit) :
    centralHeightBand S.height S.lower S.upper → A.ellipticCentralImage :=
  fun x ↦ ⟨x.1, by
    rcases x.2 with ⟨y, _, hy⟩
    exact hy ▸ y.2⟩


variable (A)




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

end SphereSixComplex.Geometry.AnalyticData
