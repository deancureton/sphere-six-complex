module

public import SphereSixComplex.Paper.Topology.PaperEllipticFillingRealPeriodRadial

/-!
# The central-fibre cover of a radial elliptic quotient

This lower-level module contains the covering-space API for the reduced central fibre.  It is
kept independent of the Section Seven finite-CW model assembly so mapping-torus identifications
can use the cover without creating an import cycle.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology Set
open scoped ContinuousMap

namespace SphereSixComplex.EllipticFilling

open Geometry Geometry.ComplexTorus Geometry.EllipticFixedPointCriterion
open Geometry.EllipticLocalCoordinates
open Geometry.EquivariantQuotientHomeomorph
open EllipticFilling

variable {m : ℕ} [NeZero m] {T : Type} [TopologicalSpace T] [AddCommGroup T]
    (D : RadialEllipticActionData m T)

namespace RadialEllipticActionData

/-- The inverse image of the reduced central fibre under the full orbit projection. -/
public abbrev CentralFiberCoverSource :=
  {p : D.Product // Quotient.mk (orbitRelOf D.actionData.diagonalAction) p ∈
    D.reducedCentralFiber}

/-- Restriction of the full orbit projection to the reduced central fibre. -/
public def centralFiberCoverProjection :
    C(CentralFiberCoverSource D, D.reducedCentralFiber) where
  toFun p := ⟨Quotient.mk _ p.1, p.2⟩
  continuous_toFun := Continuous.subtype_mk
    (continuous_quot_mk.comp continuous_subtype_val) _

/-- A point maps into the reduced central fibre exactly when it lies in the central slice. -/
public theorem mem_centralSlice_iff_quotient_mem_reducedCentralFiber (p : D.Product) :
    Quotient.mk (orbitRelOf D.actionData.diagonalAction) p ∈ D.reducedCentralFiber ↔
      p ∈ D.centralSlice := by
  constructor
  · intro hp
    rw [EllipticFilling.RadialEllipticActionData.reducedCentralFiber] at hp
    obtain ⟨q, hq, heq⟩ := hp
    have horbit := Quotient.exact heq.symm
    change ∃ g : FiniteCyclic m,
      actionMap D.actionData.diagonalAction g q = p at horbit
    obtain ⟨g, rfl⟩ := horbit
    have h := congrArg Prod.fst (D.retract_equivariant g q)
    rw [D.retract_fixed q hq] at h
    change ComplexUnitDisc.center = (actionMap D.actionData.diagonalAction g q).1 at h
    change (actionMap D.actionData.diagonalAction g q).1 = ComplexUnitDisc.center
    exact h.symm
  · intro hp
    rw [EllipticFilling.RadialEllipticActionData.reducedCentralFiber]
    exact ⟨p, hp, rfl⟩

/-- Insert a torus point into the inverse image of the reduced central fibre. -/
public def centralFiberCoverSourceOfTorus (x : T) : CentralFiberCoverSource D :=
  ⟨(D.actionData.center, x), by
    apply (mem_centralSlice_iff_quotient_mem_reducedCentralFiber D
      (D.actionData.center, x)).2
    exact D.center_eq⟩

/-- The restricted covering source is canonically the original central four-torus. -/
public def centralFiberCoverSourceHomeomorph :
    CentralFiberCoverSource D ≃ₜ T where
  toFun p := p.1.2
  invFun := centralFiberCoverSourceOfTorus D
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · have hp := (mem_centralSlice_iff_quotient_mem_reducedCentralFiber D p.1).1 p.2
      exact D.center_eq.trans hp.symm
    · rfl
  right_inv _ := rfl
  continuous_toFun := continuous_snd.comp continuous_subtype_val
  continuous_invFun := Continuous.subtype_mk (continuous_const.prodMk continuous_id) _

/-- The central-fibre covering-source homeomorphism is projection to the torus coordinate. -/
public theorem centralFiberCoverSourceHomeomorph_apply
    (p : CentralFiberCoverSource D) :
    centralFiberCoverSourceHomeomorph D p = p.1.2 := rfl

variable [T2Space D.Product] [LocallyCompactSpace D.Product]

/-- The central-fibre projection is the restriction of the full finite cyclic quotient
covering. -/
public theorem centralFiberCoverProjection_isCovering
    (hfree : letI := D.actionData.diagonalAction
      IsCancelSMul (FiniteCyclic m) D.Product) :
    IsCoveringMap (centralFiberCoverProjection D) := by
  let action := D.actionData.diagonalAction
  let _ := action
  let _ : IsCancelSMul (FiniteCyclic m) D.Product := hfree
  let _ : ContinuousConstSMul (FiniteCyclic m) D.Product :=
    ⟨D.representation_continuous⟩
  let _ : ProperlyDiscontinuousSMul (FiniteCyclic m) D.Product := inferInstance
  let hq : IsQuotientCoveringMap
      (Quotient.mk (MulAction.orbitRel (FiniteCyclic m) D.Product)) (FiniteCyclic m) :=
    isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul
  have hq' : IsQuotientCoveringMap
      (Quotient.mk (orbitRelOf D.actionData.diagonalAction) : D.Product → D.FillingQuotient)
      (FiniteCyclic m) := by
    change IsQuotientCoveringMap
      (Quotient.mk (MulAction.orbitRel (FiniteCyclic m) D.Product)) (FiniteCyclic m)
    exact hq
  have h := hq'.isCoveringMap.restrictPreimage D.reducedCentralFiber
  let e : CentralFiberCoverSource D ≃ₜ
      {p : D.Product | Quotient.mk (orbitRelOf D.actionData.diagonalAction) p ∈
        D.reducedCentralFiber} := Homeomorph.refl _
  have he := h.comp_homeomorph e
  convert he using 1
  ext
  rfl



end RadialEllipticActionData

end SphereSixComplex.EllipticFilling

end

end
