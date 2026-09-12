module

public import SphereSixComplex.Paper.Topology.PaperMultipleFiberHOneTopologyDefs

/-!
# Reducing the multiple-fibre presentation to a single generation statement

`_root_.SphereSixComplex.AffineCyclicQuotientHomology.reducedCentralFiberHOnePresentation` asks for two
things at once: an isomorphism between the first homology of a free affine cyclic torus
quotient and the abelian multiple-fibre presentation, *and* the value of that isomorphism on
the image of the covering torus.

This file proves that the second clause is automatic.  The covering projection kills the
monodromy difference, so the canonical lattice class map factors through the coinvariants; a
meridian class whose `m`-th multiple is the twist class then produces a canonical map *out of*
the presentation by `multipleFiberLift`, and any inverse of that canonical map satisfies the
naturality clause on the nose.

The presentation map is determined by a meridian class satisfying the full-iterate relation.
Its inverse has the required covering-torus coordinate formula whenever the map is bijective.
-/

open AlgebraicTopology CategoryTheory

noncomputable section

namespace SphereSixComplex.AffineCyclicQuotientHomology
open SphereSixComplex SphereSixComplex.Topology
open SphereSixComplex.AffineCyclicQuotientHomology
open Geometry Geometry.AnalyticTorusFamily Geometry.ComplexTorus
open Geometry.EllipticFamilySpecialization Geometry.EllipticLocalCoordinates
open Geometry.EquivariantQuotientHomeomorph
open LatticeData Periods
open EllipticFilling
open MultipleFiberCoinvariants
open _root_.SphereSixComplex.AffineCyclicQuotientHomology
variable {m : ℕ} [NeZero m] {p : SphereSixComplex.Periods.Parameters}
  {D : RadialEllipticActionData m (AdditiveTorus p)}

private theorem homologyMap_comp {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (k : ℕ) (f : C(X, Y)) (g : C(Y, Z))
    (x : IntegralSingularHomology k X) :
    integralSingularHomologyMap k (g.comp f) x =
      integralSingularHomologyMap k g (integralSingularHomologyMap k f x) := by
  change ConcreteCategory.hom
      (((singularHomologyFunctor AddCommGrpCat k).obj (AddCommGrpCat.of ℤ)).map
        (TopCat.ofHom (g.comp f))) x = _
  rw [show TopCat.ofHom (g.comp f) = TopCat.ofHom f ≫ TopCat.ofHom g from rfl,
    Functor.map_comp]
  rfl

private theorem homologyEquiv_map_symm {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (k : ℕ) (e : X ≃ₜ Y) (x : IntegralSingularHomology k Y) :
    integralSingularHomologyEquiv k e
        (integralSingularHomologyMap k ⟨e.symm, e.symm.continuous⟩ x) = x :=
  (integralSingularHomologyEquiv k e).apply_symm_apply x

/-- The affine cyclic generator transported to the covering torus of the reduced central
fibre. -/
@[expose] public def centralFiberCoverGenerator
    (P : AffineCyclicCentralFiberPresentationData m p D) :
    C(RadialEllipticActionData.CentralFiberCoverSource D,
      RadialEllipticActionData.CentralFiberCoverSource D) :=
  ((⟨(RadialEllipticActionData.centralFiberCoverSourceHomeomorph D).symm,
      (RadialEllipticActionData.centralFiberCoverSourceHomeomorph D).symm.continuous⟩ :
        C(AdditiveTorus p, RadialEllipticActionData.CentralFiberCoverSource D)).comp
    P.affine.map).comp
    ⟨RadialEllipticActionData.centralFiberCoverSourceHomeomorph D,
      (RadialEllipticActionData.centralFiberCoverSourceHomeomorph D).continuous⟩

/-- Points of the covering source sit over the centre of the disc. -/
public theorem centralFiberCoverSource_fst
    (t : RadialEllipticActionData.CentralFiberCoverSource D) :
    t.1.1 = ComplexUnitDisc.center := by
  have h :=
    (RadialEllipticActionData.mem_centralSlice_iff_quotient_mem_reducedCentralFiber D t.1).1 t.2
  exact h

/-- The underlying pair of a point of the covering source, in torus coordinates. -/
public theorem centralFiberCoverSource_val
    (t : RadialEllipticActionData.CentralFiberCoverSource D) :
    t.1 = (ComplexUnitDisc.center, RadialEllipticActionData.centralFiberCoverSourceHomeomorph D t) := by
  rw [RadialEllipticActionData.centralFiberCoverSourceHomeomorph_apply D t]
  exact Prod.ext (centralFiberCoverSource_fst t) rfl

/-- The cyclic generator acts on the covering source as the fibre generator. -/
public theorem centralFiberCoverSource_smul
    (t : RadialEllipticActionData.CentralFiberCoverSource D) :
    actionMap D.actionData.diagonalAction (cyclicGenerator m) t.1 =
      (ComplexUnitDisc.center, D.actionData.fiberGenerator
        (RadialEllipticActionData.centralFiberCoverSourceHomeomorph D t)) := by
  have hpair : actionMap D.actionData.diagonalAction (cyclicGenerator m) t.1 =
      (D.actionData.rotation t.1.1, D.actionData.fiberGenerator t.1.2) := by
    change D.actionData.representation (cyclicGenerator m) t.1 = _
    rw [D.actionData.representation_generator]
    rfl
  have hfix : D.retract t.1 = t.1 :=
    D.retract_fixed t.1 (centralFiberCoverSource_fst t)
  have hequiv := D.retract_equivariant (cyclicGenerator m) t.1
  rw [hfix] at hequiv
  rw [hpair] at hequiv
  have hrot : ComplexUnitDisc.center = D.actionData.rotation t.1.1 := congrArg Prod.fst hequiv
  rw [hpair, RadialEllipticActionData.centralFiberCoverSourceHomeomorph_apply D t, ← hrot]

/-- The covering projection is invariant under the transported cyclic generator. -/
public theorem centralFiberCoverProjection_comp_generator
    (P : AffineCyclicCentralFiberPresentationData m p D) :
    (RadialEllipticActionData.centralFiberCoverProjection D).comp
        (centralFiberCoverGenerator P) =
      RadialEllipticActionData.centralFiberCoverProjection D := by
  ext s
  refine Quotient.sound ⟨cyclicGenerator m, ?_⟩
  show actionMap D.actionData.diagonalAction (cyclicGenerator m) s.1 = _
  have hgen := centralFiberCoverSource_smul s
  have htarget : (centralFiberCoverGenerator P s).1 =
      (ComplexUnitDisc.center, P.affine.map
        (RadialEllipticActionData.centralFiberCoverSourceHomeomorph D s)) := by
    have h := centralFiberCoverSource_val
      ((RadialEllipticActionData.centralFiberCoverSourceHomeomorph D).symm
        (P.affine.map (RadialEllipticActionData.centralFiberCoverSourceHomeomorph D s)))
    rw [(RadialEllipticActionData.centralFiberCoverSourceHomeomorph D).apply_symm_apply] at h
    exact h
  rw [htarget, ← P.generator_eq]
  exact hgen

/-- Degree-one naturality of the standard covering basis under the transported generator. -/
public theorem centralFiberCoverSourceDegreeOneBasis_generator
    (P : AffineCyclicCentralFiberPresentationData m p D)
    (z : IntegralSingularHomology 1 (RadialEllipticActionData.CentralFiberCoverSource D)) :
    centralFiberCoverSourceDegreeOneBasis P
        (integralSingularHomologyMap 1 (centralFiberCoverGenerator P) z) =
      P.affine.latticeMap (centralFiberCoverSourceDegreeOneBasis P z) := by
  have hnat := (StandardTorusHomology.additiveTorusHomologyBasis_naturality p P.fullRank
    P.affine).1
  change (StandardTorusHomology.additiveTorusHomologyBasis p P.fullRank).degreeOne
      (integralSingularHomologyEquiv 1
        (RadialEllipticActionData.centralFiberCoverSourceHomeomorph D)
        (integralSingularHomologyMap 1 (centralFiberCoverGenerator P) z)) = _
  rw [centralFiberCoverGenerator, homologyMap_comp, homologyMap_comp,
    homologyEquiv_map_symm, hnat]
  rfl

/-- The canonical map from the covering lattice to the first homology of the reduced central
fibre: the covering projection read in the standard basis of the covering torus. -/
@[expose] public def coverProjectionLatticeMap
    (P : AffineCyclicCentralFiberPresentationData m p D) :
    Lattice →ₗ[ℤ] IntegralSingularHomology 1 D.reducedCentralFiber :=
  AddMonoidHom.toIntLinearMap
    ((integralSingularHomologyMap 1
        (RadialEllipticActionData.centralFiberCoverProjection D)).comp
      (centralFiberCoverSourceDegreeOneBasis P).symm.toAddMonoidHom)

public theorem coverProjectionLatticeMap_apply
    (P : AffineCyclicCentralFiberPresentationData m p D) (x : Lattice) :
    coverProjectionLatticeMap P x =
      integralSingularHomologyMap 1
        (RadialEllipticActionData.centralFiberCoverProjection D)
        ((centralFiberCoverSourceDegreeOneBasis P).symm x) := rfl

/-- The canonical lattice class map is invariant under the integral monodromy. -/
public theorem coverProjectionLatticeMap_latticeMap
    (P : AffineCyclicCentralFiberPresentationData m p D) (x : Lattice) :
    coverProjectionLatticeMap P (P.affine.latticeMap x) = coverProjectionLatticeMap P x := by
  have hbasis := centralFiberCoverSourceDegreeOneBasis_generator P
    ((centralFiberCoverSourceDegreeOneBasis P).symm x)
  rw [(centralFiberCoverSourceDegreeOneBasis P).apply_symm_apply] at hbasis
  have hsymm : (centralFiberCoverSourceDegreeOneBasis P).symm (P.affine.latticeMap x) =
      integralSingularHomologyMap 1 (centralFiberCoverGenerator P)
        ((centralFiberCoverSourceDegreeOneBasis P).symm x) := by
    rw [← hbasis, (centralFiberCoverSourceDegreeOneBasis P).symm_apply_apply]
  rw [coverProjectionLatticeMap_apply, coverProjectionLatticeMap_apply, hsymm,
    ← homologyMap_comp, centralFiberCoverProjection_comp_generator P]

/-- The canonical lattice class map kills the monodromy difference, so it factors through the
coinvariants appearing in the multiple-fibre presentation. -/
public theorem coverProjectionLatticeMap_latticeDifference
    (P : AffineCyclicCentralFiberPresentationData m p D) (x : Lattice) :
    coverProjectionLatticeMap P (P.latticeDifference x) = 0 := by
  rw [P.latticeDifference_eq, LinearMap.sub_apply, LinearMap.id_apply, map_sub]
  rw [show P.affine.latticeMap.toLinearMap x = P.affine.latticeMap x from rfl,
    coverProjectionLatticeMap_latticeMap P x, sub_self]

/-- The canonical map *out of* the abelian multiple-fibre presentation determined by a meridian
class whose `m`-th multiple is the twist class. -/
@[expose] public def presentationLift
    (P : AffineCyclicCentralFiberPresentationData m p D)
    (b : IntegralSingularHomology 1 D.reducedCentralFiber)
    (hb : (m : ℤ) • b = coverProjectionLatticeMap P P.twist) :
    CyclicCoinvariants.Presentation P.latticeDifference P.twist (m : ℤ) →ₗ[ℤ]
      IntegralSingularHomology 1 D.reducedCentralFiber :=
  CyclicCoinvariants.lift P.latticeDifference P.twist (m : ℤ) (coverProjectionLatticeMap P)
    (coverProjectionLatticeMap_latticeDifference P) b hb

/-- On the image of the covering torus the canonical map is the canonical lattice class map. -/
public theorem presentationLift_latticeProjection
    (P : AffineCyclicCentralFiberPresentationData m p D)
    (b : IntegralSingularHomology 1 D.reducedCentralFiber)
    (hb : (m : ℤ) • b = coverProjectionLatticeMap P P.twist) (x : Lattice) :
    presentationLift P b hb (latticeProjection P x) = coverProjectionLatticeMap P x := by
  change CyclicCoinvariants.lift P.latticeDifference P.twist (m : ℤ) (coverProjectionLatticeMap P)
      (coverProjectionLatticeMap_latticeDifference P) b hb
      (Submodule.Quotient.mk (Submodule.Quotient.mk x, (0 : ℤ))) = _
  rw [CyclicCoinvariants.lift_mk, zero_smul, add_zero]

/-- The inverse of the bijective presentation map preserves the covering-torus coordinates. -/
public def reducedCentralFiberHOnePresentation_of_bijective
    (P : AffineCyclicCentralFiberPresentationData m p D)
    (b : IntegralSingularHomology 1 D.reducedCentralFiber)
    (hb : (m : ℤ) • b = coverProjectionLatticeMap P P.twist)
    (hbij : Function.Bijective (presentationLift P b hb)) :
    ReducedCentralFiberHOnePresentation P where
  equiv := (LinearEquiv.ofBijective (presentationLift P b hb) hbij).symm
  projection x := by
    have h : LinearEquiv.ofBijective (presentationLift P b hb) hbij
        (latticeProjection P x) = coverProjectionLatticeMap P x :=
      presentationLift_latticeProjection P b hb x
    rw [← coverProjectionLatticeMap_apply, ← h, LinearEquiv.symm_apply_apply]

/-- Values of the canonical map on presentation coordinates. -/
public theorem presentationLift_mk
    (P : AffineCyclicCentralFiberPresentationData m p D)
    (b : IntegralSingularHomology 1 D.reducedCentralFiber)
    (hb : (m : ℤ) • b = coverProjectionLatticeMap P P.twist) (x : Lattice) (k : ℤ) :
    presentationLift P b hb (Submodule.Quotient.mk (Submodule.Quotient.mk x, k)) =
      coverProjectionLatticeMap P x + k • b :=
  CyclicCoinvariants.lift_mk _ _ _ _ _ _ _ x k


end SphereSixComplex.AffineCyclicQuotientHomology

end
