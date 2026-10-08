module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

@[expose] public section
noncomputable section
open CategoryTheory
open scoped ContinuousMap

/-- A homotopy equivalence induces an equivalence of fundamental groups at corresponding
basepoints. -/
public noncomputable def fundamentalGroupMulEquivOfHomotopyEquiv
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₕ Y) (x : X) :
    FundamentalGroup X x ≃* FundamentalGroup Y (e x) :=
  (FundamentalGroupoidFunctor.equivOfHomotopyEquiv e).fullyFaithfulFunctor.mulEquivEnd
    (FundamentalGroupoid.mk x)

public theorem fundamentalGroupMulEquivOfHomotopyEquiv_apply
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₕ Y) (x : X) (p : FundamentalGroup X x) :
    fundamentalGroupMulEquivOfHomotopyEquiv e x p = FundamentalGroup.map e.toFun x p := by
  exact CategoryTheory.Functor.FullyFaithful.mulEquivEnd_apply _ _ _

/-- Equality of basepoints induces the corresponding conjugation equivalence of fundamental
groups. -/
public def fundamentalGroupMulEquivOfEq
    {X : Type*} [TopologicalSpace X] {x y : X} (h : x = y) :
    FundamentalGroup X x ≃* FundamentalGroup X y :=
  (eqToIso (congrArg FundamentalGroupoid.mk h)).conj

public theorem fundamentalGroupMulEquivOfEq_apply
    {X : Type*} [TopologicalSpace X] {x y : X} (h : x = y)
    (p : FundamentalGroup X x) :
    fundamentalGroupMulEquivOfEq h p =
      Path.Homotopic.Quotient.cast p h.symm h.symm := by
  exact FundamentalGroupoid.conj_eqToHom _ _
