module

public import SphereSixComplex.Topology.NormalizedAffineMappingTorusCover

/-!
# The elliptic central projections in mapping-torus coordinates

The explicit quotient recognition homeomorphisms intertwine the original central-torus orbit
projections with the normalized affine covers of the corresponding mapping tori.  Thus the
remaining work in the degree-two basis calculation is source-independent homology naturality for
these two normalized covers.
-/

@[expose] public section

noncomputable section

open Topology
open scoped ContinuousMap

namespace SphereSixComplex.Topology.EllipticCentralProjectionMappingTorusSquare

open Geometry Geometry.EllipticFamilySpecialization
open Geometry.ComplexTorus Geometry.EquivariantQuotientHomeomorph
open Geometry.EllipticFixedPointCriterion Geometry.EllipticLocalCoordinates
open Geometry.AnalyticTorusFamily Geometry.GlobalTorusFamily
open PaperAffineCyclicReducedFiberMappingTorus
open NormalizedAffineMappingTorusCover
open PaperEllipticFillingRadialRetraction
open PaperEllipticReducedCentralFiberCoverModels
open PaperEllipticReducedCentralFiberCoverModels.RadialEllipticActionData

variable {m : ℕ} [NeZero m] {F : Type} [TopologicalSpace F]

variable {X : Type} [TopologicalSpace X]

/-- Quotient recognition sends the original orbit projection to the normalized affine cover. -/
public theorem finiteCyclicOrbitQuotientCircleMappingTorusHomeomorph_projection
    (A : MulAction (FiniteCyclic m) X) (e : X ≃ₜ UnitAddCircle × F)
    (phi : F ≃ₜ F) (hpow : phi ^ m = 1)
    (hgen : ∀ x, e (actionMap A (cyclicGenerator m) x) =
      normalizedAffineShift (m := m) phi 1 (e x)) (x : X) :
    finiteCyclicOrbitQuotientCircleMappingTorusHomeomorph A e phi hpow hgen
        (Quotient.mk (MulAction.orbitRel (FiniteCyclic m) X) x) =
      normalizedAffineCoverToCircleMappingTorus phi hpow (e x) :=
  rfl

variable {T : Type} [TopologicalSpace T] [AddCommGroup T]

/-- The generic gamma-normal-form recognition theorem commutes with the central orbit
projection. -/
public theorem reducedCentralFiberCircleMappingTorusHomeomorph_projection
    (D : RadialEllipticActionData m T)
    [T2Space D.Product] [LocallyCompactSpace D.Product]
    (hfree : letI := D.actionData.diagonalAction
      IsCancelSMul (FiniteCyclic m) D.Product)
    (e : T ≃ₜ UnitAddCircle × F) (phi : F ≃ₜ F) (hpow : phi ^ m = 1)
    (hgen : ∀ x, e (D.actionData.fiberGenerator x) =
      normalizedAffineShift (m := m) phi 1 (e x)) (x : T) :
    reducedCentralFiberCircleMappingTorusHomeomorphOfGammaNormalForm
        D hfree e phi hpow hgen (centralFiberOrbitProjection D x) =
      normalizedAffineCoverToCircleMappingTorus phi hpow (e x) := by
  let A := centralFiberAction D
  have hgenA : ∀ y, e (actionMap A (cyclicGenerator m) y) =
      normalizedAffineShift (m := m) phi 1 (e y) := by
    intro y
    rw [show actionMap A (cyclicGenerator m) y = D.actionData.fiberGenerator y by
      exact congrArg (fun g : Equiv.Perm T ↦ g y)
        (centralFiberRepresentation_generator D)]
    exact hgen y
  have hquotient :
      (centralFiberOrbitQuotientHomeomorph D hfree).symm
          (centralFiberOrbitProjection D x) =
        Quotient.mk (MulAction.orbitRel (FiniteCyclic m) T) x := by
    apply (centralFiberOrbitQuotientHomeomorph D hfree).injective
    rw [(centralFiberOrbitQuotientHomeomorph D hfree).apply_symm_apply]
    rfl
  change finiteCyclicOrbitQuotientCircleMappingTorusHomeomorph A e phi hpow hgenA
      ((centralFiberOrbitQuotientHomeomorph D hfree).symm
        (centralFiberOrbitProjection D x)) = _
  rw [hquotient]
  exact finiteCyclicOrbitQuotientCircleMappingTorusHomeomorph_projection
    A e phi hpow hgenA x

/-- The central-cover projection is the central orbit projection after forgetting the redundant
disc coordinate. -/
public theorem centralFiberOrbitProjection_coverSourceHomeomorph
    (D : RadialEllipticActionData m T) (x : centralFiberCoverSource D) :
    centralFiberOrbitProjection D (centralFiberCoverSourceHomeomorph D x) =
      centralFiberCoverProjection D x := by
  simp [centralFiberOrbitProjection]

/-- The normalized mapping-torus cover written directly on the central covering source. -/
public def centralCoverToCircleMappingTorus
  (D : RadialEllipticActionData m T) (e : T ≃ₜ UnitAddCircle × F)
    (phi : F ≃ₜ F) (hpow : phi ^ m = 1) :
    C(centralFiberCoverSource D, CircleMappingTorus phi) :=
  (normalizedAffineCoverToCircleMappingTorus phi hpow).comp
    ((⟨e, e.continuous⟩ : C(T, UnitAddCircle × F)).comp
      (⟨centralFiberCoverSourceHomeomorph D,
        (centralFiberCoverSourceHomeomorph D).continuous⟩ :
          C(centralFiberCoverSource D, T)))

public theorem reducedCentralFiberCircleMappingTorusHomeomorph_coverProjection
    (D : RadialEllipticActionData m T)
    [T2Space D.Product] [LocallyCompactSpace D.Product]
    (hfree : letI := D.actionData.diagonalAction
      IsCancelSMul (FiniteCyclic m) D.Product)
    (e : T ≃ₜ UnitAddCircle × F) (phi : F ≃ₜ F) (hpow : phi ^ m = 1)
    (hgen : ∀ x, e (D.actionData.fiberGenerator x) =
      normalizedAffineShift (m := m) phi 1 (e x)) :
    (⟨reducedCentralFiberCircleMappingTorusHomeomorphOfGammaNormalForm
        D hfree e phi hpow hgen,
      (reducedCentralFiberCircleMappingTorusHomeomorphOfGammaNormalForm
        D hfree e phi hpow hgen).continuous⟩ :
          C(D.reducedCentralFiber, CircleMappingTorus phi)).comp
      (centralFiberCoverProjection D) =
      centralCoverToCircleMappingTorus D e phi hpow := by
  ext x
  change reducedCentralFiberCircleMappingTorusHomeomorphOfGammaNormalForm
      D hfree e phi hpow hgen (centralFiberCoverProjection D x) =
    normalizedAffineCoverToCircleMappingTorus phi hpow
      (e (centralFiberCoverSourceHomeomorph D x))
  rw [← centralFiberOrbitProjection_coverSourceHomeomorph D x]
  exact reducedCentralFiberCircleMappingTorusHomeomorph_projection
    D hfree e phi hpow hgen (centralFiberCoverSourceHomeomorph D x)

variable {U : Periods.TriangleUniformization} (PF : Periods.PeriodFunctions U)

/-- Point-set form of the order-three projection naturality square. -/
public theorem orderThree_coverProjection_square :
    (⟨orderThreeReducedCentralFiberCircleMappingTorusHomeomorph PF,
      (orderThreeReducedCentralFiberCircleMappingTorusHomeomorph PF).continuous⟩ :
        C(OrderThreeReducedCentralFiber PF,
          CircleMappingTorus orderThreeThreeTorusClutching)).comp
        (RadialEllipticActionData.centralFiberCoverProjection
          (orderThreeRadialActionData PF)) =
      centralCoverToCircleMappingTorus (orderThreeRadialActionData PF)
        (orderThreeGammaNormalFormHomeomorph PF) orderThreeThreeTorusClutching
        orderThreeThreeTorusClutching_pow := by
  let p := parameterMap PF U.zOne
  let hfull := fullRankDomain p
  let _ : ProperlyDiscontinuousSMul (PeriodGroup p.1) ComplexTwoSpace :=
    periodLattice_properlyDiscontinuousSMul hfull
  let _ : T2Space (AdditiveTorus p.1) := inferInstance
  let _ : CompactSpace (AdditiveTorus p.1) := torus_compactSpace p.1 hfull
  let _ : LocallyCompactSpace (AdditiveTorus p.1) := inferInstance
  let _ : LocallyCompactSpace ComplexUnitDisc :=
    (isOpen_lt continuous_norm continuous_const).locallyCompactSpace
  apply reducedCentralFiberCircleMappingTorusHomeomorph_coverProjection
  intro x
  change orderThreeGammaNormalFormHomeomorph PF
      ((orderThreeActionData PF).fiberGenerator x) = _
  simpa [normalizedAffineShift_apply] using orderThreeGammaNormalForm_generator PF x

/-- Point-set form of the order-four projection naturality square. -/
public theorem orderFour_coverProjection_square :
    (⟨orderFourReducedCentralFiberCircleMappingTorusHomeomorph PF,
      (orderFourReducedCentralFiberCircleMappingTorusHomeomorph PF).continuous⟩ :
        C(OrderFourReducedCentralFiber PF,
          CircleMappingTorus orderFourThreeTorusClutching)).comp
        (RadialEllipticActionData.centralFiberCoverProjection
          (orderFourRadialActionData PF)) =
      centralCoverToCircleMappingTorus (orderFourRadialActionData PF)
        (orderFourGammaNormalFormHomeomorph PF) orderFourThreeTorusClutching
        orderFourThreeTorusClutching_pow := by
  let p := parameterMap PF U.zTwo
  let hfull := fullRankDomain p
  let _ : ProperlyDiscontinuousSMul (PeriodGroup p.1) ComplexTwoSpace :=
    periodLattice_properlyDiscontinuousSMul hfull
  let _ : T2Space (AdditiveTorus p.1) := inferInstance
  let _ : CompactSpace (AdditiveTorus p.1) := torus_compactSpace p.1 hfull
  let _ : LocallyCompactSpace (AdditiveTorus p.1) := inferInstance
  let _ : LocallyCompactSpace ComplexUnitDisc :=
    (isOpen_lt continuous_norm continuous_const).locallyCompactSpace
  apply reducedCentralFiberCircleMappingTorusHomeomorph_coverProjection
  intro x
  change orderFourGammaNormalFormHomeomorph PF
      ((orderFourActionData PF).fiberGenerator x) = _
  simpa [normalizedAffineShift_apply] using orderFourGammaNormalForm_generator PF x

end SphereSixComplex.Topology.EllipticCentralProjectionMappingTorusSquare

end

end
