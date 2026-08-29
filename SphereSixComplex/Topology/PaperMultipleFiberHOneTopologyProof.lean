module

public import SphereSixComplex.Topology.PaperMultipleFiberHOneTopologyDefs

/-!
# Reducing the multiple-fibre presentation to a single generation statement

`EstablishedAffineCyclicQuotientHomology.reducedCentralFiberHOnePresentation` asks for two
things at once: an isomorphism between the first homology of a free affine cyclic torus
quotient and the abelian multiple-fibre presentation, *and* the value of that isomorphism on
the image of the covering torus.

This file proves that the second clause is automatic.  The covering projection kills the
monodromy difference, so the canonical lattice class map factors through the coinvariants; a
meridian class whose `m`-th multiple is the twist class then produces a canonical map *out of*
the presentation by `multipleFiberLift`, and any inverse of that canonical map satisfies the
naturality clause on the nose.

What remains of the axiom is therefore the single statement that one explicit map is bijective,
together with the choice of a meridian class.  The auxiliary predicate
`IsCentralFiberCoverSourceCoordinate` records the coordinate formula for
`RadialEllipticActionData.centralFiberCoverSourceHomeomorph`, which holds by `rfl` but is not
available to importing modules because that definition is not exposed.
-/

open AlgebraicTopology CategoryTheory

namespace SphereSixComplex.Topology.PaperMultipleFiberHOneTopology

open Geometry Geometry.AnalyticTorusFamily Geometry.ComplexTorus
open Geometry.EllipticFamilySpecialization Geometry.EllipticLocalCoordinates
open Geometry.EquivariantQuotientHomeomorph
open LatticeData Periods
open PaperEllipticFillingRadialRetraction
open PaperEllipticReducedCentralFiberCoverModels
open PaperLemmaSevenThirteenAlgebra

noncomputable section

namespace EstablishedAffineCyclicQuotientHomology

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
    C(RadialEllipticActionData.centralFiberCoverSource D,
      RadialEllipticActionData.centralFiberCoverSource D) :=
  ((⟨(RadialEllipticActionData.centralFiberCoverSourceHomeomorph D).symm,
      (RadialEllipticActionData.centralFiberCoverSourceHomeomorph D).symm.continuous⟩ :
        C(AdditiveTorus p, RadialEllipticActionData.centralFiberCoverSource D)).comp
    P.affine.map).comp
    ⟨RadialEllipticActionData.centralFiberCoverSourceHomeomorph D,
      (RadialEllipticActionData.centralFiberCoverSourceHomeomorph D).continuous⟩

/-- The coordinate description of the canonical identification between the covering source of
the reduced central fibre and the central torus.

`RadialEllipticActionData.centralFiberCoverSourceHomeomorph` is *the* projection to the torus
coordinate, so this predicate holds by `rfl`; it is carried explicitly because that definition is
not exposed to importing modules. -/
public def IsCentralFiberCoverSourceCoordinate
    (D : RadialEllipticActionData m (AdditiveTorus p)) : Prop :=
  ∀ t : RadialEllipticActionData.centralFiberCoverSource D,
    RadialEllipticActionData.centralFiberCoverSourceHomeomorph D t = t.1.2

/-- The canonical central-fibre covering-source homeomorphism is the torus coordinate. -/
public theorem isCentralFiberCoverSourceCoordinate :
    IsCentralFiberCoverSourceCoordinate D :=
  RadialEllipticActionData.centralFiberCoverSourceHomeomorph_apply D

/-- Points of the covering source sit over the centre of the disc. -/
public theorem centralFiberCoverSource_fst
    (t : RadialEllipticActionData.centralFiberCoverSource D) :
    t.1.1 = discCenter := by
  have h :=
    (RadialEllipticActionData.mem_centralSlice_iff_quotient_mem_reducedCentralFiber D t.1).1 t.2
  exact h

/-- The underlying pair of a point of the covering source, in torus coordinates. -/
public theorem centralFiberCoverSource_val
    (hcoord : IsCentralFiberCoverSourceCoordinate D)
    (t : RadialEllipticActionData.centralFiberCoverSource D) :
    t.1 = (discCenter, RadialEllipticActionData.centralFiberCoverSourceHomeomorph D t) := by
  rw [hcoord t]
  exact Prod.ext (centralFiberCoverSource_fst t) rfl

/-- The cyclic generator acts on the covering source as the fibre generator. -/
public theorem centralFiberCoverSource_smul
    (hcoord : IsCentralFiberCoverSourceCoordinate D)
    (t : RadialEllipticActionData.centralFiberCoverSource D) :
    actionMap D.actionData.diagonalAction (cyclicGenerator m) t.1 =
      (discCenter, D.actionData.fiberGenerator
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
  have hrot : discCenter = D.actionData.rotation t.1.1 := congrArg Prod.fst hequiv
  rw [hpair, hcoord t, ← hrot]

/-- The covering projection is invariant under the transported cyclic generator. -/
public theorem centralFiberCoverProjection_comp_generator
    (hcoord : IsCentralFiberCoverSourceCoordinate D)
    (P : AffineCyclicCentralFiberPresentationData m p D) :
    (RadialEllipticActionData.centralFiberCoverProjection D).comp
        (centralFiberCoverGenerator P) =
      RadialEllipticActionData.centralFiberCoverProjection D := by
  ext s
  refine Quotient.sound ⟨cyclicGenerator m, ?_⟩
  show actionMap D.actionData.diagonalAction (cyclicGenerator m) s.1 = _
  have hgen := centralFiberCoverSource_smul hcoord s
  have htarget : (centralFiberCoverGenerator P s).1 =
      (discCenter, P.affine.map
        (RadialEllipticActionData.centralFiberCoverSourceHomeomorph D s)) := by
    have h := centralFiberCoverSource_val hcoord
      ((RadialEllipticActionData.centralFiberCoverSourceHomeomorph D).symm
        (P.affine.map (RadialEllipticActionData.centralFiberCoverSourceHomeomorph D s)))
    rw [(RadialEllipticActionData.centralFiberCoverSourceHomeomorph D).apply_symm_apply] at h
    exact h
  rw [htarget, ← P.generator_eq]
  exact hgen

/-- Degree-one naturality of the standard covering basis under the transported generator. -/
public theorem centralFiberCoverSourceDegreeOneBasis_generator
    (P : AffineCyclicCentralFiberPresentationData m p D)
    (z : IntegralSingularHomology 1 (RadialEllipticActionData.centralFiberCoverSource D)) :
    centralFiberCoverSourceDegreeOneBasis P
        (integralSingularHomologyMap 1 (centralFiberCoverGenerator P) z) =
      P.affine.latticeMap (centralFiberCoverSourceDegreeOneBasis P z) := by
  have hnat := (EstablishedTorusHomology.additiveTorusHomologyBasis_naturality p P.fullRank
    P.affine).1
  change (EstablishedTorusHomology.additiveTorusHomologyBasis p P.fullRank).degreeOne
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
    (hcoord : IsCentralFiberCoverSourceCoordinate D)
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
    ← homologyMap_comp, centralFiberCoverProjection_comp_generator hcoord P]

/-- The canonical lattice class map kills the monodromy difference, so it factors through the
coinvariants appearing in the multiple-fibre presentation. -/
public theorem coverProjectionLatticeMap_latticeDifference
    (hcoord : IsCentralFiberCoverSourceCoordinate D)
    (P : AffineCyclicCentralFiberPresentationData m p D) (x : Lattice) :
    coverProjectionLatticeMap P (P.latticeDifference x) = 0 := by
  rw [P.latticeDifference_eq, LinearMap.sub_apply, LinearMap.id_apply, map_sub]
  rw [show P.affine.latticeMap.toLinearMap x = P.affine.latticeMap x from rfl,
    coverProjectionLatticeMap_latticeMap hcoord P x, sub_self]

/-- The canonical map *out of* the abelian multiple-fibre presentation determined by a meridian
class whose `m`-th multiple is the twist class. -/
@[expose] public def presentationLift
    (hcoord : IsCentralFiberCoverSourceCoordinate D)
    (P : AffineCyclicCentralFiberPresentationData m p D)
    (b : IntegralSingularHomology 1 D.reducedCentralFiber)
    (hb : (m : ℤ) • b = coverProjectionLatticeMap P P.twist) :
    MultipleFiberHOnePresentation P.latticeDifference P.twist (m : ℤ) →ₗ[ℤ]
      IntegralSingularHomology 1 D.reducedCentralFiber :=
  multipleFiberLift P.latticeDifference P.twist (m : ℤ) (coverProjectionLatticeMap P)
    (coverProjectionLatticeMap_latticeDifference hcoord P) b hb

/-- On the image of the covering torus the canonical map is the canonical lattice class map. -/
public theorem presentationLift_latticeProjection
    (hcoord : IsCentralFiberCoverSourceCoordinate D)
    (P : AffineCyclicCentralFiberPresentationData m p D)
    (b : IntegralSingularHomology 1 D.reducedCentralFiber)
    (hb : (m : ℤ) • b = coverProjectionLatticeMap P P.twist) (x : Lattice) :
    presentationLift hcoord P b hb (latticeProjection P x) = coverProjectionLatticeMap P x := by
  change multipleFiberLift P.latticeDifference P.twist (m : ℤ) (coverProjectionLatticeMap P)
      (coverProjectionLatticeMap_latticeDifference hcoord P) b hb
      (Submodule.Quotient.mk (Submodule.Quotient.mk x, (0 : ℤ))) = _
  rw [multipleFiberLift_mk, zero_smul, add_zero]

/-- **Reduction of the multiple-fibre presentation axiom.**  Once the canonical map out of the
presentation is bijective, the full conclusion of
`EstablishedAffineCyclicQuotientHomology.reducedCentralFiberHOnePresentation` follows: its
naturality clause on the covering torus holds automatically. -/
public def reducedCentralFiberHOnePresentation_of_bijective
    (hcoord : IsCentralFiberCoverSourceCoordinate D)
    (P : AffineCyclicCentralFiberPresentationData m p D)
    (b : IntegralSingularHomology 1 D.reducedCentralFiber)
    (hb : (m : ℤ) • b = coverProjectionLatticeMap P P.twist)
    (hbij : Function.Bijective (presentationLift hcoord P b hb)) :
    ReducedCentralFiberHOnePresentation P where
  equiv := (LinearEquiv.ofBijective (presentationLift hcoord P b hb) hbij).symm
  projection x := by
    have h : LinearEquiv.ofBijective (presentationLift hcoord P b hb) hbij
        (latticeProjection P x) = coverProjectionLatticeMap P x :=
      presentationLift_latticeProjection hcoord P b hb x
    rw [← coverProjectionLatticeMap_apply, ← h, LinearEquiv.symm_apply_apply]

/-- Values of the canonical map on presentation coordinates. -/
public theorem presentationLift_mk
    (hcoord : IsCentralFiberCoverSourceCoordinate D)
    (P : AffineCyclicCentralFiberPresentationData m p D)
    (b : IntegralSingularHomology 1 D.reducedCentralFiber)
    (hb : (m : ℤ) • b = coverProjectionLatticeMap P P.twist) (x : Lattice) (k : ℤ) :
    presentationLift hcoord P b hb (Submodule.Quotient.mk (Submodule.Quotient.mk x, k)) =
      coverProjectionLatticeMap P x + k • b :=
  multipleFiberLift_mk _ _ _ _ _ _ _ x k

/-- The canonical map is surjective exactly when the first homology of the reduced central fibre
is generated by the covering lattice classes together with the meridian. -/
public theorem presentationLift_surjective_iff
    (hcoord : IsCentralFiberCoverSourceCoordinate D)
    (P : AffineCyclicCentralFiberPresentationData m p D)
    (b : IntegralSingularHomology 1 D.reducedCentralFiber)
    (hb : (m : ℤ) • b = coverProjectionLatticeMap P P.twist) :
    Function.Surjective (presentationLift hcoord P b hb) ↔
      ∀ c : IntegralSingularHomology 1 D.reducedCentralFiber,
        ∃ (x : Lattice) (k : ℤ), coverProjectionLatticeMap P x + k • b = c := by
  constructor
  · intro hsurj c
    obtain ⟨q, rfl⟩ := hsurj c
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective (LinearMap.range P.latticeDifference) w.1
    refine ⟨x, w.2, ?_⟩
    rw [← presentationLift_mk hcoord P b hb x w.2, hx]
  · intro hgen c
    obtain ⟨x, k, hxk⟩ := hgen c
    exact ⟨Submodule.Quotient.mk (Submodule.Quotient.mk x, k), by
      rw [presentationLift_mk hcoord P b hb x k, hxk]⟩

end EstablishedAffineCyclicQuotientHomology

end

end SphereSixComplex.Topology.PaperMultipleFiberHOneTopology
