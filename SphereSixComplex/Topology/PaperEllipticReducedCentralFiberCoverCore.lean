module

public import SphereSixComplex.Topology.PaperEllipticFillingRealPeriodRadial

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

namespace SphereSixComplex.Topology.PaperEllipticReducedCentralFiberCoverModels

open Geometry Geometry.ComplexTorus Geometry.EllipticFixedPointCriterion
open Geometry.EllipticLocalCoordinates
open Geometry.EquivariantQuotientHomeomorph
open Topology.PaperEllipticFillingRadialRetraction

variable {m : ℕ} [NeZero m] {T : Type} [TopologicalSpace T] [AddCommGroup T]
    (D : RadialEllipticActionData m T)

namespace RadialEllipticActionData

/-- The inverse image of the reduced central fibre under the full orbit projection. -/
public abbrev centralFiberCoverSource :=
  {p : D.Product // Quotient.mk (orbitRelOf D.actionData.diagonalAction) p ∈
    D.reducedCentralFiber}

/-- Restriction of the full orbit projection to the reduced central fibre. -/
public def centralFiberCoverProjection :
    C(centralFiberCoverSource D, D.reducedCentralFiber) where
  toFun p := ⟨Quotient.mk _ p.1, p.2⟩
  continuous_toFun := Continuous.subtype_mk
    (continuous_quot_mk.comp continuous_subtype_val) _

/-- A point maps into the reduced central fibre exactly when it lies in the central slice. -/
public theorem mem_centralSlice_iff_quotient_mem_reducedCentralFiber (p : D.Product) :
    Quotient.mk (orbitRelOf D.actionData.diagonalAction) p ∈ D.reducedCentralFiber ↔
      p ∈ D.centralSlice := by
  constructor
  · intro hp
    rw [PaperEllipticFillingRadialRetraction.RadialEllipticActionData.reducedCentralFiber] at hp
    obtain ⟨q, hq, heq⟩ := hp
    have horbit := Quotient.exact heq.symm
    change ∃ g : FiniteCyclic m,
      actionMap D.actionData.diagonalAction g q = p at horbit
    obtain ⟨g, rfl⟩ := horbit
    have h := congrArg Prod.fst (D.retract_equivariant g q)
    rw [D.retract_fixed q hq] at h
    change discCenter = (actionMap D.actionData.diagonalAction g q).1 at h
    change (actionMap D.actionData.diagonalAction g q).1 = discCenter
    exact h.symm
  · intro hp
    rw [PaperEllipticFillingRadialRetraction.RadialEllipticActionData.reducedCentralFiber]
    exact ⟨p, hp, rfl⟩

/-- Insert a torus point into the inverse image of the reduced central fibre. -/
public def centralFiberCoverSourceOfTorus (x : T) : centralFiberCoverSource D :=
  ⟨(D.actionData.center, x), by
    apply (mem_centralSlice_iff_quotient_mem_reducedCentralFiber D
      (D.actionData.center, x)).2
    exact D.center_eq⟩

/-- The restricted covering source is canonically the original central four-torus. -/
public def centralFiberCoverSourceHomeomorph :
    centralFiberCoverSource D ≃ₜ T where
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
    (p : centralFiberCoverSource D) :
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
  let e : centralFiberCoverSource D ≃ₜ
      {p : D.Product | Quotient.mk (orbitRelOf D.actionData.diagonalAction) p ∈
        D.reducedCentralFiber} := Homeomorph.refl _
  have he := h.comp_homeomorph e
  convert he using 1
  ext
  rfl

/-- A fibre of the restricted central projection is canonically a fibre of the full orbit
projection. -/
public def centralFiberCoverFiberEquivFullFiber
    (x : D.reducedCentralFiber) :
    {y : centralFiberCoverSource D // centralFiberCoverProjection D y = x} ≃
      {p : D.Product // Quotient.mk (orbitRelOf D.actionData.diagonalAction) p = x.1} where
  toFun y := ⟨y.1.1, congrArg Subtype.val y.2⟩
  invFun p := ⟨⟨p.1, by rw [p.2]; exact x.2⟩, by
    apply Subtype.ext
    exact p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Every fibre of the reduced central projection has exactly `m` points. -/
public theorem centralFiberCoverProjection_fiberCardinality
    (hfree : letI := D.actionData.diagonalAction
      IsCancelSMul (FiniteCyclic m) D.Product)
    (x : D.reducedCentralFiber) :
    Nat.card {y : centralFiberCoverSource D // centralFiberCoverProjection D y = x} = m := by
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
  have hx := x.2
  simp only [PaperEllipticFillingRadialRetraction.RadialEllipticActionData.reducedCentralFiber]
    at hx
  obtain ⟨p, _hp, hpx⟩ := hx
  let pFiber : {q : D.Product //
      Quotient.mk (orbitRelOf D.actionData.diagonalAction) q = x.1} := ⟨p, hpx⟩
  calc
    Nat.card {y : centralFiberCoverSource D // centralFiberCoverProjection D y = x} =
        Nat.card {q : D.Product //
          Quotient.mk (orbitRelOf D.actionData.diagonalAction) q = x.1} :=
      Nat.card_congr (centralFiberCoverFiberEquivFullFiber D x)
    _ = Nat.card (FiniteCyclic m) := Nat.card_congr (hq'.fiberEquivGroup pFiber)
    _ = m := finiteCyclic_card m

end RadialEllipticActionData

end SphereSixComplex.Topology.PaperEllipticReducedCentralFiberCoverModels

end

end
