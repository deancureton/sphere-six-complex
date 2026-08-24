module

public import SphereSixComplex.Geometry.CuspPuncturedCollarBridge
public import SphereSixComplex.Topology.MayerVietoris
public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance

/-!
# Equivariant descent for the cusp-filling retraction

Proposition 7.2 requires an explicit equivariant strong deformation retraction of the toric
prequotient onto its central fibre.  The present toric model does not yet contain the polar-part,
honeycomb, or stabilizer data from which that retraction is constructed.  This file therefore
does not assert its existence.  It proves the reusable quotient-descent theorem and records the
exact datum whose construction would instantiate the theorem for the actual cusp filling.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory Set
open scoped ContinuousMap

namespace SphereSixComplex

/-- An equivariant strong deformation retraction of `X` onto `A`. -/
public structure EquivariantStrongDeformationRetraction
    (G X : Type*) [Group G] [TopologicalSpace X] [MulAction G X] (A : Set X) where
  retract : C(X, X)
  homotopy : ContinuousMap.Homotopy (ContinuousMap.id X) retract
  retract_mem : ∀ x, retract x ∈ A
  retract_fixed : ∀ x, x ∈ A → retract x = x
  homotopy_fixed : ∀ s x, x ∈ A → homotopy (s, x) = x
  retract_equivariant : ∀ (g : G) x, retract (g • x) = g • retract x
  homotopy_equivariant : ∀ (g : G) s x, homotopy (s, g • x) = g • homotopy (s, x)

namespace EquivariantStrongDeformationRetraction

variable {G X : Type*} [Group G] [TopologicalSpace X] [MulAction G X]
  {A : Set X} (D : EquivariantStrongDeformationRetraction G X A)

/-- The orbit quotient of the ambient action. -/
public abbrev OrbitQuotient (_D : EquivariantStrongDeformationRetraction G X A) :=
  Quotient (MulAction.orbitRel G X)

/-- The image of the retract in the orbit quotient. -/
public def quotientCore : Set (D.OrbitQuotient) :=
  Quotient.mk (MulAction.orbitRel G X) '' A

/-- The equivariant retraction descended to the orbit quotient. -/
public def quotientRetract : C(D.OrbitQuotient, D.OrbitQuotient) := by
  letI := MulAction.orbitRel G X
  exact {
    toFun := Quotient.lift (fun x ↦ Quotient.mk' (D.retract x)) (by
      intro a b hab
      apply Quotient.sound
      change MulAction.orbitRel G X a b at hab
      change MulAction.orbitRel G X (D.retract a) (D.retract b)
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hab ⊢
      obtain ⟨g, hg⟩ := hab
      refine ⟨g, ?_⟩
      rw [← hg]
      exact (D.retract_equivariant g b).symm)
    continuous_toFun := continuous_quot_lift _
      (continuous_quot_mk.comp D.retract.continuous) }

/-- The underlying map of the descended homotopy. -/
public def quotientHomotopyToFun : unitInterval × D.OrbitQuotient → D.OrbitQuotient := by
  letI := MulAction.orbitRel G X
  exact fun z ↦ Quotient.lift
    (fun x ↦ Quotient.mk' (D.homotopy (z.1, x))) (by
      intro a b hab
      apply Quotient.sound
      change MulAction.orbitRel G X a b at hab
      change MulAction.orbitRel G X (D.homotopy (z.1, a)) (D.homotopy (z.1, b))
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hab ⊢
      obtain ⟨g, hg⟩ := hab
      refine ⟨g, ?_⟩
      rw [← hg]
      exact (D.homotopy_equivariant g z.1 b).symm) z.2

variable [ContinuousConstSMul G X]

public theorem quotientHomotopyToFun_continuous : Continuous D.quotientHomotopyToFun := by
  let q : X → D.OrbitQuotient := Quotient.mk (MulAction.orbitRel G X)
  have hq : IsOpenQuotientMap (Prod.map (id : unitInterval → unitInterval) q) :=
    IsOpenQuotientMap.id.prodMap
      (MulAction.isOpenQuotientMap_quotientMk (Γ := G) (T := X))
  apply hq.isQuotientMap.continuous_iff.mpr
  change Continuous (fun z : unitInterval × X ↦
    Quotient.mk (MulAction.orbitRel G X) (D.homotopy (z.1, z.2)))
  exact continuous_quot_mk.comp D.homotopy.continuous

/-- The strong deformation homotopy descended to the orbit quotient. -/
public def quotientHomotopy :
    ContinuousMap.Homotopy (ContinuousMap.id D.OrbitQuotient) D.quotientRetract where
  toFun := D.quotientHomotopyToFun
  continuous_toFun := D.quotientHomotopyToFun_continuous
  map_zero_left q := by
    induction q using Quotient.inductionOn with
    | _ x => exact congrArg (Quotient.mk _) (D.homotopy.map_zero_left x)
  map_one_left q := by
    induction q using Quotient.inductionOn with
    | _ x => exact congrArg (Quotient.mk _) (D.homotopy.map_one_left x)

omit [ContinuousConstSMul G X] in
public theorem quotientRetract_mem (q : D.OrbitQuotient) :
    D.quotientRetract q ∈ D.quotientCore := by
  induction q using Quotient.inductionOn with
  | _ x => exact ⟨D.retract x, D.retract_mem x, rfl⟩

omit [ContinuousConstSMul G X] in
public theorem quotientRetract_fixed (q : D.OrbitQuotient) (hq : q ∈ D.quotientCore) :
    D.quotientRetract q = q := by
  obtain ⟨x, hx, rfl⟩ := hq
  exact congrArg (Quotient.mk _) (D.retract_fixed x hx)

public theorem quotientHomotopy_fixed (s : unitInterval) (q : D.OrbitQuotient)
    (hq : q ∈ D.quotientCore) : D.quotientHomotopy (s, q) = q := by
  obtain ⟨x, hx, rfl⟩ := hq
  exact congrArg (Quotient.mk _) (D.homotopy_fixed s x hx)

end EquivariantStrongDeformationRetraction

namespace Geometry.CuspPuncturedCollarBridge

open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.CuspCombinatorics
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspPhaseEstimates
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel
open SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination

variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
  (W : ActualPuncturedCuspCollarWitness N M)

/-- The prequotient central fibre in the actual local cusp carrier. -/
public def actualLocalCuspCentralFiber : Set (LocalCarrier M W.localWitness.radius) :=
  {p | M.t p = 0}

/-- The action used definitionally by `actualLocalCuspFilling`. -/
@[instance_reducible] public noncomputable def actualLocalCuspQuotientAction :
    MulAction (Multiplicative ParameterLattice) (LocalCarrier M W.localWitness.radius) :=
  let C :=
    CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N M W.localWitness.radius W.localWitness.radius_pos W.localWitness.radius_le
  (C.toCuspActionData W.localWitness.fixedPoint).psiAction

/-- Continuity of the actual phase-corrected lattice action. -/
public theorem actualLocalPsiContinuousConstSMul :
    letI := actualLocalCuspQuotientAction W
    ContinuousConstSMul (Multiplicative ParameterLattice)
      (LocalCarrier M W.localWitness.radius) := by
  let C :=
    CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N M W.localWitness.radius W.localWitness.radius_pos W.localWitness.radius_le
  let _ := actualLocalCuspQuotientAction W
  exact ⟨by
    intro lambda
    rw [show lambda = Multiplicative.ofAdd (Multiplicative.toAdd lambda) from rfl]
    change Continuous ((C.toCuspActionData W.localWitness.fixedPoint).psiMap
      (Multiplicative.toAdd lambda))
    exact (C.genericPsiMap_holomorphic W.localWitness.fixedPoint _).continuous⟩

/-- The exact prequotient datum still needed from the toric construction in Proposition 7.2. -/
public structure ActualLocalCuspCentralFiberRetractionData where
  toEquivariantSDR :
    letI := actualLocalCuspQuotientAction W
    EquivariantStrongDeformationRetraction
      (Multiplicative ParameterLattice) (LocalCarrier M W.localWitness.radius)
        (actualLocalCuspCentralFiber W)

namespace ActualLocalCuspCentralFiberRetractionData

variable (R : ActualLocalCuspCentralFiberRetractionData W)

/-- The central fibre after passage to the actual local cusp quotient. -/
public noncomputable def quotientCentralFiber : Set (actualLocalCuspFilling W) := by
  letI := actualLocalCuspQuotientAction W
  exact R.toEquivariantSDR.quotientCore

/-- The quotient retraction supplied conditionally by the prequotient toric retraction. -/
public noncomputable def quotientRetract : C(actualLocalCuspFilling W, actualLocalCuspFilling W) := by
  letI := actualLocalCuspQuotientAction W
  exact R.toEquivariantSDR.quotientRetract

/-- The quotient strong deformation homotopy supplied by the prequotient toric retraction. -/
public noncomputable def quotientHomotopy :
    ContinuousMap.Homotopy (ContinuousMap.id (actualLocalCuspFilling W))
      (quotientRetract W R) := by
  letI := actualLocalCuspQuotientAction W
  letI := actualLocalPsiContinuousConstSMul W
  exact R.toEquivariantSDR.quotientHomotopy

public theorem quotientRetract_mem (q : actualLocalCuspFilling W) :
    quotientRetract W R q ∈ quotientCentralFiber W R := by
  let _ := actualLocalCuspQuotientAction W
  let _ : ContinuousConstSMul (Multiplicative ParameterLattice)
      (LocalCarrier M W.localWitness.radius) := actualLocalPsiContinuousConstSMul W
  exact EquivariantStrongDeformationRetraction.quotientRetract_mem R.toEquivariantSDR q

public theorem quotientRetract_fixed (q : actualLocalCuspFilling W)
    (hq : q ∈ quotientCentralFiber W R) : quotientRetract W R q = q := by
  let _ := actualLocalCuspQuotientAction W
  exact EquivariantStrongDeformationRetraction.quotientRetract_fixed R.toEquivariantSDR q hq

/-- The quotient retraction with its codomain restricted to the central fibre. -/
public noncomputable def quotientRetractToCentralFiber :
    C(actualLocalCuspFilling W, quotientCentralFiber W R) where
  toFun q := ⟨quotientRetract W R q, quotientRetract_mem W R q⟩
  continuous_toFun := (quotientRetract W R).continuous.subtype_mk _

/-- Inclusion of the quotient central fibre into the actual local cusp filling. -/
public noncomputable def quotientCentralFiberInclusion :
    C(quotientCentralFiber W R, actualLocalCuspFilling W) where
  toFun := Subtype.val
  continuous_toFun := continuous_subtype_val

public theorem quotientHomotopy_fixed (s : unitInterval) (q : actualLocalCuspFilling W)
    (hq : q ∈ quotientCentralFiber W R) : quotientHomotopy W R (s, q) = q := by
  let _ := actualLocalCuspQuotientAction W
  let _ : ContinuousConstSMul (Multiplicative ParameterLattice)
      (LocalCarrier M W.localWitness.radius) := actualLocalPsiContinuousConstSMul W
  exact EquivariantStrongDeformationRetraction.quotientHomotopy_fixed
    R.toEquivariantSDR s q hq

/-- The homotopy equivalence produced by the descended strong deformation retraction. -/
public noncomputable def quotientCentralFiberHomotopyEquiv :
    actualLocalCuspFilling W ≃ₕ quotientCentralFiber W R where
  toFun := quotientRetractToCentralFiber W R
  invFun := quotientCentralFiberInclusion W R
  left_inv := by
    change (quotientRetract W R).Homotopic (ContinuousMap.id (actualLocalCuspFilling W))
    exact ⟨(quotientHomotopy W R).symm⟩
  right_inv := by
    have h : (quotientRetractToCentralFiber W R).comp
        (quotientCentralFiberInclusion W R) =
        ContinuousMap.id (quotientCentralFiber W R) := by
      apply ContinuousMap.ext
      intro q
      apply Subtype.ext
      exact quotientRetract_fixed W R q q.2
    rw [h]

/-- Specialization is an isomorphism on integral singular homology. -/
public noncomputable def specializationHomologyEquiv (k : ℕ) :
    IntegralSingularHomology k (actualLocalCuspFilling W) ≃+
      IntegralSingularHomology k (quotientCentralFiber W R) :=
  integralSingularHomologyEquivOfHomotopyEquiv k (quotientCentralFiberHomotopyEquiv W R)

/-- The specialization map on integral singular chains induced by the quotient retraction. -/
public noncomputable def specializationChainMap :
    IntegralSingularChainComplex (actualLocalCuspFilling W) ⟶
      IntegralSingularChainComplex (quotientCentralFiber W R) :=
  integralSingularChainMap (quotientRetractToCentralFiber W R)

/-- The specialization map on integral singular homology induced by the quotient retraction. -/
public noncomputable def specializationHomologyMap (k : ℕ) :
    IntegralSingularHomology k (actualLocalCuspFilling W) →+
      IntegralSingularHomology k (quotientCentralFiber W R) :=
  integralSingularHomologyMap k (quotientRetractToCentralFiber W R)

public theorem specializationHomologyMap_eq_equiv (k : ℕ) :
    specializationHomologyMap W R k = (specializationHomologyEquiv W R k).toAddMonoidHom :=
  rfl

/-- Restriction of specialization along any supplied continuous fibre inclusion. -/
public noncomputable def restrictedSpecializationChainMap
    {F : Type} [TopologicalSpace F] (i : C(F, actualLocalCuspFilling W)) :
    IntegralSingularChainComplex F ⟶
      IntegralSingularChainComplex (quotientCentralFiber W R) :=
  integralSingularChainMap ((quotientRetractToCentralFiber W R).comp i)

public theorem restrictedSpecializationChainMap_eq_comp
    {F : Type} [TopologicalSpace F] (i : C(F, actualLocalCuspFilling W)) :
    restrictedSpecializationChainMap W R i =
      integralSingularChainMap i ≫ specializationChainMap W R := by
  simp [restrictedSpecializationChainMap, specializationChainMap,
    integralSingularChainMap]

end ActualLocalCuspCentralFiberRetractionData

end Geometry.CuspPuncturedCollarBridge

end SphereSixComplex
