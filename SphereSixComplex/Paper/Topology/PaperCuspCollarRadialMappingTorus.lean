module

public import SphereSixComplex.Paper.Topology.CircleMappingTorusHomologyBases
public import SphereSixComplex.Paper.Topology.PaperEllipticCollarFundamentalDomain

/-!
# The radial mapping-torus model of the cusp collar

A punctured cusp collar retains an open radial coordinate.  Thus its dimensionally correct model
is an open interval times a four-torus mapping torus.  The interval is contractible, so this model
still supplies the Wang bases required in degrees one and two.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology Set
open scoped ContinuousMap

namespace SphereSixComplex

/-- The open radial interval is contractible when its radius is positive. -/
public noncomputable def openRadialIntervalHomotopyEquivUnit
    {r : ℝ} (hr : 0 < r) : OpenRadialInterval r ≃ₕ Unit := by
  letI : ContractibleSpace (OpenRadialInterval r) :=
    (convex_Ioo (0 : ℝ) r).contractibleSpace (nonempty_Ioo.mpr hr)
  exact Classical.choice (ContractibleSpace.hequiv_unit (OpenRadialInterval r))

/-- A contractible radial factor can be removed up to homotopy equivalence. -/
public noncomputable def openRadialIntervalProdHomotopyEquiv
    {X : Type} [TopologicalSpace X] {r : ℝ} (hr : 0 < r) :
    OpenRadialInterval r × X ≃ₕ X :=
  ((openRadialIntervalHomotopyEquivUnit hr).prodCongr
      (ContinuousMap.HomotopyEquiv.refl X)).trans
    (Homeomorph.uniqueProd Unit X).toHomotopyEquiv



end SphereSixComplex
