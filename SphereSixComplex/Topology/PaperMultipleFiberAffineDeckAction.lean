module

public import SphereSixComplex.Topology.PaperMultipleFiberHOneTopology
import SphereSixComplex.Topology.AffineRealMappingTorusUniversalCover

open Set Topology
open scoped ContinuousMap

namespace SphereSixComplex.Topology.PaperMultipleFiberHOneTopology
namespace EstablishedAffineCyclicQuotientHomology

open SphereSixComplex.Geometry
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.CyclicAngularFundamentalDomain
open SphereSixComplex.LatticeData
open SphereSixComplex.Topology.PaperEllipticFillingRadialRetraction

variable {m : ℕ} [NeZero m]
variable {p : SphereSixComplex.Periods.Parameters}
variable {D : RadialEllipticActionData m
  (SphereSixComplex.Geometry.EllipticFamilySpecialization.AdditiveTorus p)}

private theorem integerAffineMonodromy_apply'
    (A : AddAut LatticeData.Lattice) (k : Multiplicative ℤ)
    (n : Multiplicative LatticeData.Lattice) :
    (integerAffineMonodromy A k n).toAdd =
      (A.toEquiv ^ k.toAdd) n.toAdd := by
  change (k.toAdd • A) n.toAdd = _
  induction k.toAdd using Int.induction_on generalizing n with
  | zero => simp
  | succ i ih =>
      rw [add_zsmul, one_zsmul, AddAut.add_apply]
      have hih := ih (Multiplicative.ofAdd (A n.toAdd))
      change ((i : ℤ) • A) (A n.toAdd) =
        (A.toEquiv ^ (i : ℤ)) (A n.toAdd) at hih
      change ((i : ℤ) • A) (A n.toAdd) = _
      rw [hih]
      rw [show A.toEquiv ^ ((i : ℤ) + 1) =
          A.toEquiv ^ (i : ℤ) * A.toEquiv by rw [zpow_add_one],
        Equiv.Perm.mul_apply]
      rfl
  | pred i ih =>
      rw [sub_eq_add_neg, add_zsmul, neg_one_zsmul, AddAut.add_apply]
      have hih := ih (Multiplicative.ofAdd ((-A) n.toAdd))
      change ((- (i : ℤ)) • A) ((-A) n.toAdd) =
        (A.toEquiv ^ (- (i : ℤ))) ((-A) n.toAdd) at hih
      rw [hih]
      change (A.toEquiv ^ (- (i : ℤ))) (A.symm n.toAdd) = _
      rw [show A.toEquiv ^ (- (i : ℤ) + -1) =
          A.toEquiv ^ (- (i : ℤ)) * A.toEquiv⁻¹ by
        rw [zpow_add]
        simp,
        Equiv.Perm.mul_apply]
      apply congrArg (A.toEquiv ^ (- (i : ℤ)))
      rfl

/-- The affine action of the unquotiented cyclic boundary deck group on the universal cover. -/
@[expose] public def affineCyclicBoundaryDeckTransform
    (P : AffineCyclicCentralFiberPresentationData m p D)
    (d : CanonicalCyclicAffineBoundaryDeck P.affine.latticeMap.toAddEquiv)
    (z : ComplexTwoSpace) : ComplexTwoSpace :=
  periodVector p d.left.toAdd +
    (affineEquiv P.affine.lift P.liftTranslation ^ d.right.toAdd) z

public theorem affineCyclicBoundaryDeckTransform_one
    (P : AffineCyclicCentralFiberPresentationData m p D) (z : ComplexTwoSpace) :
    affineCyclicBoundaryDeckTransform P 1 z = z := by
  simp [affineCyclicBoundaryDeckTransform, periodVector_zero]

public theorem affineCyclicBoundaryDeckTransform_mul
    (P : AffineCyclicCentralFiberPresentationData m p D)
    (d e : CanonicalCyclicAffineBoundaryDeck P.affine.latticeMap.toAddEquiv)
    (z : ComplexTwoSpace) :
    affineCyclicBoundaryDeckTransform P (d * e) z =
      affineCyclicBoundaryDeckTransform P d
        (affineCyclicBoundaryDeckTransform P e z) := by
  change periodVector p
        (d.left.toAdd +
          (integerAffineMonodromy P.affine.latticeMap.toAddEquiv d.right e.left).toAdd) +
      (affineEquiv P.affine.lift P.liftTranslation ^
        (d.right.toAdd + e.right.toAdd)) z =
    periodVector p d.left.toAdd +
      (affineEquiv P.affine.lift P.liftTranslation ^ d.right.toAdd)
        (periodVector p e.left.toAdd +
          (affineEquiv P.affine.lift P.liftTranslation ^ e.right.toAdd) z)
  have heq : P.affine.latticeMap.toAddEquiv.toEquiv =
      P.affine.latticeMap.toEquiv := rfl
  rw [periodVector_add, integerAffineMonodromy_apply', heq,
    affineEquiv_zpow_add, descendedAffineTorusLift_zpow_period,
    zpow_add, Equiv.Perm.mul_apply]
  rw [add_assoc]

/-- The unquotiented affine cyclic boundary deck action on `ComplexTwoSpace`. -/
@[expose, instance_reducible] public noncomputable def affineCyclicBoundaryDeckAction
    (P : AffineCyclicCentralFiberPresentationData m p D) :
    MulAction (CanonicalCyclicAffineBoundaryDeck P.affine.latticeMap.toAddEquiv)
      ComplexTwoSpace where
  smul d z := affineCyclicBoundaryDeckTransform P d z
  one_smul := affineCyclicBoundaryDeckTransform_one P
  mul_smul := affineCyclicBoundaryDeckTransform_mul P

public theorem affineCyclicBoundaryTranslation_smul
    (P : AffineCyclicCentralFiberPresentationData m p D)
    (x : LatticeData.Lattice) (z : ComplexTwoSpace) :
    letI := affineCyclicBoundaryDeckAction P
    Additive.toMul ((affineCyclicBoundaryDeckData P).translation x) • z =
      periodVector p x + z := by
  change affineCyclicBoundaryDeckTransform P
    (Additive.toMul ((affineCyclicBoundaryDeckData P).translation x)) z = _
  simp [affineCyclicBoundaryDeckTransform,
    affineCyclicBoundaryDeckData, canonicalCyclicAffineBoundaryDeckData,
    canonicalCyclicAffineTranslation]

public theorem affineCyclicBoundaryMeridian_smul
    (P : AffineCyclicCentralFiberPresentationData m p D) (z : ComplexTwoSpace) :
    letI := affineCyclicBoundaryDeckAction P
    (affineCyclicBoundaryDeckData P).meridian • z =
      affineEquiv P.affine.lift P.liftTranslation z := by
  change affineCyclicBoundaryDeckTransform P
    (affineCyclicBoundaryDeckData P).meridian z = _
  simp [affineCyclicBoundaryDeckTransform,
    affineCyclicBoundaryDeckData, canonicalCyclicAffineBoundaryDeckData,
    canonicalCyclicAffineMeridian, periodVector_zero]

public theorem affineCyclicBoundaryMeridian_pow_smul
    (P : AffineCyclicCentralFiberPresentationData m p D) (z : ComplexTwoSpace) :
    letI := affineCyclicBoundaryDeckAction P
    (affineCyclicBoundaryDeckData P).meridian ^ m • z =
      z + periodVector p P.twist := by
  change affineCyclicBoundaryDeckTransform P
    ((affineCyclicBoundaryDeckData P).meridian ^ m) z = _
  have hmeridian :
      (affineCyclicBoundaryDeckData P).meridian ^ m =
        SemidirectProduct.inr
          (φ := integerAffineMonodromy P.affine.latticeMap.toAddEquiv)
          (Multiplicative.ofAdd (m : ℤ)) := by
    change (SemidirectProduct.inr
      (φ := integerAffineMonodromy P.affine.latticeMap.toAddEquiv)
      (Multiplicative.ofAdd 1)) ^ m = _
    rw [← map_pow]
    congr 1
    apply Multiplicative.toAdd.injective
    simp
  rw [hmeridian]
  change periodVector p 0 +
    (affineEquiv P.affine.lift P.liftTranslation ^ (m : ℤ)) z = _
  rw [periodVector_zero, zero_add, zpow_natCast]
  exact P.lift_full_iterate z

public theorem affineCyclicBoundaryFillingRelation_smul
    (P : AffineCyclicCentralFiberPresentationData m p D) (z : ComplexTwoSpace) :
    letI := affineCyclicBoundaryDeckAction P
    (affineCyclicBoundaryDeckData P).fillingRelation • z = z := by
  let _ := affineCyclicBoundaryDeckAction P
  rw [UnwrappedCyclicAffineBoundaryDeckData.fillingRelation, mul_smul]
  rw [show (affineCyclicBoundaryDeckData P).twist = P.twist from rfl]
  have hinv :
      (Additive.toMul ((affineCyclicBoundaryDeckData P).translation P.twist))⁻¹ =
        Additive.toMul ((affineCyclicBoundaryDeckData P).translation (-P.twist)) := by
    rw [map_neg]
    rfl
  rw [hinv, affineCyclicBoundaryTranslation_smul,
    affineCyclicBoundaryMeridian_pow_smul]
  have hneg : periodVector p (-P.twist) = -periodVector p P.twist := by
    change periodHom p (-P.twist) = -periodHom p P.twist
    simp
  rw [hneg]
  abel

/-- The raw affine action as a permutation representation. -/
@[expose] public noncomputable def affineCyclicBoundaryDeckRepresentation
    (P : AffineCyclicCentralFiberPresentationData m p D) :
    CanonicalCyclicAffineBoundaryDeck P.affine.latticeMap.toAddEquiv →*
      Equiv.Perm ComplexTwoSpace := by
  let _ := affineCyclicBoundaryDeckAction P
  exact MulAction.toPermHom _ _

public theorem affineCyclicBoundaryDeckRepresentation_apply
    (P : AffineCyclicCentralFiberPresentationData m p D)
    (d : CanonicalCyclicAffineBoundaryDeck P.affine.latticeMap.toAddEquiv)
    (z : ComplexTwoSpace) :
    affineCyclicBoundaryDeckRepresentation P d z =
      affineCyclicBoundaryDeckTransform P d z := rfl

public theorem affineCyclicFillingKernel_le_representation_ker
    (P : AffineCyclicCentralFiberPresentationData m p D) :
    (affineCyclicBoundaryDeckData P).fillingKernel ≤
      (affineCyclicBoundaryDeckRepresentation P).ker := by
  rw [UnwrappedCyclicAffineBoundaryDeckData.fillingKernel]
  apply Subgroup.normalClosure_le_normal
  rw [Set.singleton_subset_iff]
  change affineCyclicBoundaryDeckRepresentation P
    (affineCyclicBoundaryDeckData P).fillingRelation = 1
  apply Equiv.ext
  intro z
  rw [affineCyclicBoundaryDeckRepresentation_apply]
  change (let _ := affineCyclicBoundaryDeckAction P
    (affineCyclicBoundaryDeckData P).fillingRelation • z = z)
  exact affineCyclicBoundaryFillingRelation_smul P z

/-- The affine permutation representation descended to the filling deck quotient. -/
@[expose] public noncomputable def affineCyclicFillingDeckRepresentation
    (P : AffineCyclicCentralFiberPresentationData m p D) :
    (affineCyclicBoundaryDeckData P).FillingDeck →* Equiv.Perm ComplexTwoSpace :=
  QuotientGroup.lift (affineCyclicBoundaryDeckData P).fillingKernel
    (affineCyclicBoundaryDeckRepresentation P)
    (affineCyclicFillingKernel_le_representation_ker P)

/-- The filling deck quotient acts on the affine universal cover. -/
@[expose, instance_reducible] public noncomputable def affineCyclicFillingDeckAction
    (P : AffineCyclicCentralFiberPresentationData m p D) :
    MulAction (affineCyclicBoundaryDeckData P).FillingDeck ComplexTwoSpace where
  smul g z := affineCyclicFillingDeckRepresentation P g z
  one_smul z := by
    change affineCyclicFillingDeckRepresentation P 1 z = z
    rw [map_one]
    rfl
  mul_smul g h z := by
    change affineCyclicFillingDeckRepresentation P (g * h) z =
      affineCyclicFillingDeckRepresentation P g
        (affineCyclicFillingDeckRepresentation P h z)
    rw [map_mul]
    rfl

public theorem affineCyclicFillingDeckMap_smul
    (P : AffineCyclicCentralFiberPresentationData m p D)
    (d : CanonicalCyclicAffineBoundaryDeck P.affine.latticeMap.toAddEquiv)
    (z : ComplexTwoSpace) :
    letI := affineCyclicFillingDeckAction P
    (affineCyclicBoundaryDeckData P).fillingDeckMap d • z =
      affineCyclicBoundaryDeckTransform P d z := by
  change affineCyclicFillingDeckRepresentation P
    ((affineCyclicBoundaryDeckData P).fillingDeckMap d) z = _
  have h :
      affineCyclicFillingDeckRepresentation P
          ((affineCyclicBoundaryDeckData P).fillingDeckMap d) =
        affineCyclicBoundaryDeckRepresentation P d := by
    exact QuotientGroup.lift_mk'
      (affineCyclicBoundaryDeckData P).fillingKernel
      (affineCyclicFillingKernel_le_representation_ker P) d
  rw [h]
  exact affineCyclicBoundaryDeckRepresentation_apply P d z

public theorem affineCyclicKernelIncl_smul
    (P : AffineCyclicCentralFiberPresentationData m p D)
    (x : LatticeData.Lattice) (z : ComplexTwoSpace) :
    letI := affineCyclicFillingDeckAction P
    affineCyclicKernelIncl P x • z = periodVector p x + z := by
  rw [affineCyclicKernelIncl, affineCyclicFillingDeckMap_smul]
  change (let _ := affineCyclicBoundaryDeckAction P
    Additive.toMul ((affineCyclicBoundaryDeckData P).translation x) • z = _)
  exact affineCyclicBoundaryTranslation_smul P x z

public theorem torusProjection_affineEquiv
    (P : AffineCyclicCentralFiberPresentationData m p D) (z : ComplexTwoSpace) :
    torusProjection p (affineEquiv P.affine.lift P.liftTranslation z) =
      P.affine.map (torusProjection p z) := by
  rw [affineEquiv_apply]
  change Quotient.mk _ (P.affine.lift z + P.liftTranslation) =
    P.affine.map (Quotient.mk _ z)
  rw [P.affine.map_mk, P.translation_mk]
  rfl

public theorem complexTwoReducedCentralFiberProjection_affineEquiv
    (P : AffineCyclicCentralFiberPresentationData m p D) (z : ComplexTwoSpace) :
    complexTwoReducedCentralFiberProjection (D := D)
        (affineEquiv P.affine.lift P.liftTranslation z) =
      complexTwoReducedCentralFiberProjection (D := D) z := by
  let h := SphereSixComplex.Topology.PaperEllipticReducedCentralFiberCoverModels.RadialEllipticActionData.centralFiberCoverSourceHomeomorph D
  let s : SphereSixComplex.Topology.PaperEllipticReducedCentralFiberCoverModels.RadialEllipticActionData.centralFiberCoverSource D :=
    h.symm (torusProjection p z)
  have hgen := congrArg (fun f ↦ f s)
    (centralFiberCoverProjection_comp_generator
      (isCentralFiberCoverSourceCoordinate (D := D)) P)
  have hs : centralFiberCoverGenerator P s =
      h.symm (torusProjection p
        (affineEquiv P.affine.lift P.liftTranslation z)) := by
    apply h.injective
    change P.affine.map (torusProjection p z) =
      torusProjection p (affineEquiv P.affine.lift P.liftTranslation z)
    exact (torusProjection_affineEquiv P z).symm
  change
    SphereSixComplex.Topology.PaperEllipticReducedCentralFiberCoverModels.RadialEllipticActionData.centralFiberCoverProjection D
        (centralFiberCoverGenerator P s) =
      SphereSixComplex.Topology.PaperEllipticReducedCentralFiberCoverModels.RadialEllipticActionData.centralFiberCoverProjection D s
    at hgen
  rw [hs] at hgen
  change
    SphereSixComplex.Topology.PaperEllipticReducedCentralFiberCoverModels.RadialEllipticActionData.centralFiberCoverProjection D
        (h.symm (torusProjection p
          (affineEquiv P.affine.lift P.liftTranslation z))) =
      SphereSixComplex.Topology.PaperEllipticReducedCentralFiberCoverModels.RadialEllipticActionData.centralFiberCoverProjection D
        (h.symm (torusProjection p z))
  exact hgen

end EstablishedAffineCyclicQuotientHomology
end SphereSixComplex.Topology.PaperMultipleFiberHOneTopology
