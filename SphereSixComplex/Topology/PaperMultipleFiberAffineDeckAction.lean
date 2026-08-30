module

public import SphereSixComplex.Topology.PaperMultipleFiberHOneTopologyCore
import SphereSixComplex.Topology.AffineRealMappingTorusUniversalCover

open Set Topology
open scoped ContinuousMap

namespace SphereSixComplex.Topology.PaperMultipleFiberHOneTopology
namespace EstablishedAffineCyclicQuotientHomology

open SphereSixComplex.Geometry
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.CyclicAngularFundamentalDomain
open SphereSixComplex.LatticeData
open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
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

public theorem torusProjection_period_add
    (x : LatticeData.Lattice) (z : ComplexTwoSpace) :
    torusProjection p (periodVector p x + z) = torusProjection p z := by
  let g : PeriodGroup p :=
    Multiplicative.ofAdd ⟨periodVector p x, ⟨x, rfl⟩⟩
  change Quotient.mk _ (g • z) = Quotient.mk _ z
  exact Quotient.sound ⟨g, rfl⟩

public theorem complexTwoReducedCentralFiberProjection_period_add
    (x : LatticeData.Lattice) (z : ComplexTwoSpace) :
    complexTwoReducedCentralFiberProjection (D := D) (periodVector p x + z) =
      complexTwoReducedCentralFiberProjection (D := D) z := by
  change
    SphereSixComplex.Topology.PaperEllipticReducedCentralFiberCoverModels.RadialEllipticActionData.centralFiberCoverProjection D
        ((SphereSixComplex.Topology.PaperEllipticReducedCentralFiberCoverModels.RadialEllipticActionData.centralFiberCoverSourceHomeomorph D).symm
          (torusProjection p (periodVector p x + z))) =
      SphereSixComplex.Topology.PaperEllipticReducedCentralFiberCoverModels.RadialEllipticActionData.centralFiberCoverProjection D
        ((SphereSixComplex.Topology.PaperEllipticReducedCentralFiberCoverModels.RadialEllipticActionData.centralFiberCoverSourceHomeomorph D).symm
          (torusProjection p z))
  rw [torusProjection_period_add]

public theorem complexTwoReducedCentralFiberProjection_affineEquiv_zpow
    (P : AffineCyclicCentralFiberPresentationData m p D)
    (k : ℤ) (z : ComplexTwoSpace) :
    complexTwoReducedCentralFiberProjection (D := D)
        ((affineEquiv P.affine.lift P.liftTranslation ^ k) z) =
      complexTwoReducedCentralFiberProjection (D := D) z := by
  let F := affineEquiv P.affine.lift P.liftTranslation
  have hforward (w : ComplexTwoSpace) :
      complexTwoReducedCentralFiberProjection (D := D) (F w) =
        complexTwoReducedCentralFiberProjection (D := D) w :=
    complexTwoReducedCentralFiberProjection_affineEquiv P w
  have hinverse (w : ComplexTwoSpace) :
      complexTwoReducedCentralFiberProjection (D := D) (F⁻¹ w) =
        complexTwoReducedCentralFiberProjection (D := D) w := by
    have h := hforward (F⁻¹ w)
    simpa using h.symm
  induction k using Int.induction_on generalizing z with
  | zero => simp
  | succ i ih =>
      rw [zpow_add_one, Equiv.Perm.mul_apply, ih, hforward]
  | pred i ih =>
      rw [show F ^ (- (i : ℤ) - 1) = F ^ (- (i : ℤ)) * F⁻¹ by
        rw [zpow_sub, zpow_one],
        Equiv.Perm.mul_apply, ih, hinverse]

public theorem torusProjection_affineEquiv_pow
    (P : AffineCyclicCentralFiberPresentationData m p D)
    (k : ℕ) (z : ComplexTwoSpace) :
    torusProjection p
        ((affineEquiv P.affine.lift P.liftTranslation ^ k) z) =
      (D.actionData.fiberGenerator ^ k) (torusProjection p z) := by
  induction k generalizing z with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, torusProjection_affineEquiv, ih,
        pow_succ', Equiv.Perm.mul_apply]
      exact (P.generator_eq _).symm

public theorem torusProjection_affineEquiv_zpow
    (P : AffineCyclicCentralFiberPresentationData m p D)
    (k : ℤ) (z : ComplexTwoSpace) :
    torusProjection p
        ((affineEquiv P.affine.lift P.liftTranslation ^ k) z) =
      (D.actionData.fiberGenerator ^ k) (torusProjection p z) := by
  let F := affineEquiv P.affine.lift P.liftTranslation
  let A := D.actionData.fiberGenerator
  have hforward (w : ComplexTwoSpace) :
      torusProjection p (F w) = A (torusProjection p w) := by
    rw [torusProjection_affineEquiv]
    exact (P.generator_eq _).symm
  have hinverse (w : ComplexTwoSpace) :
      torusProjection p (F⁻¹ w) = A⁻¹ (torusProjection p w) := by
    have h := hforward (F⁻¹ w)
    apply A.injective
    simpa using h.symm
  induction k using Int.induction_on generalizing z with
  | zero => simp
  | succ i ih =>
      rw [zpow_add_one, Equiv.Perm.mul_apply, ih, hforward,
        zpow_add_one, Equiv.Perm.mul_apply]
  | pred i ih =>
      rw [show F ^ (- (i : ℤ) - 1) = F ^ (- (i : ℤ)) * F⁻¹ by
        rw [zpow_sub, zpow_one],
        Equiv.Perm.mul_apply, ih, hinverse,
        show A ^ (- (i : ℤ) - 1) = A ^ (- (i : ℤ)) * A⁻¹ by
          rw [zpow_sub, zpow_one],
        Equiv.Perm.mul_apply]

public theorem fiberGenerator_zpow_eq_modOrder_pow
    (k : ℤ) :
    D.actionData.fiberGenerator ^ k =
      D.actionData.fiberGenerator ^ ((k : ZMod m).val : ℕ) := by
  let A := D.actionData.fiberGenerator
  let R : FiniteCyclic m →* Equiv.Perm
      (SphereSixComplex.Geometry.EllipticFamilySpecialization.AdditiveTorus p) :=
    cyclicRepresentation m A D.actionData.fiberGenerator_pow
  let c : FiniteCyclic m := Multiplicative.ofAdd (k : ZMod m)
  have hcInt : c = cyclicGenerator m ^ k := by
    apply Multiplicative.toAdd.injective
    simp [c, cyclicGenerator]
  have hcNat : c = cyclicGenerator m ^ (Multiplicative.toAdd c).val :=
    cyclic_eq_generator_pow c
  have hgen : R (cyclicGenerator m) = A := by
    exact cyclicRepresentation_generator m A D.actionData.fiberGenerator_pow
  have hInt := congrArg R hcInt
  have hNat := congrArg R hcNat
  rw [map_zpow, hgen] at hInt
  rw [map_pow, hgen] at hNat
  exact hInt.symm.trans hNat

public theorem affineCyclicBoundaryDeckTransform_fixed_right_modOrder
    (P : AffineCyclicCentralFiberPresentationData m p D)
    (d : CanonicalCyclicAffineBoundaryDeck P.affine.latticeMap.toAddEquiv)
    (z : ComplexTwoSpace) (hd : affineCyclicBoundaryDeckTransform P d z = z) :
    ((d.right.toAdd : ℤ) : ZMod m) = 0 := by
  have htorus := congrArg (torusProjection p) hd
  change torusProjection p
      (periodVector p d.left.toAdd +
        (affineEquiv P.affine.lift P.liftTranslation ^ d.right.toAdd) z) =
    torusProjection p z at htorus
  rw [torusProjection_period_add, torusProjection_affineEquiv_zpow,
    fiberGenerator_zpow_eq_modOrder_pow] at htorus
  let r := ((d.right.toAdd : ℤ) : ZMod m).val
  have hrlt : r < m := ZMod.val_lt _
  by_contra hne
  have hrne : r ≠ 0 := by
    intro hr
    apply hne
    apply ZMod.val_injective
    simpa [r] using hr
  have hrpos : 0 < r := Nat.pos_of_ne_zero hrne
  have hnofixed :=
    (D.actionData.isCancelSMul_iff_no_fixed_powers.mp P.free) r hrpos hrlt
  apply hnofixed
  apply (D.actionData.diagonal_fixed_iff_fiber_fixed hrpos hrlt).2
  exact ⟨torusProjection p z, htorus⟩

public theorem affineCyclicKernelIncl_add'
    (P : AffineCyclicCentralFiberPresentationData m p D)
    (x y : LatticeData.Lattice) :
    affineCyclicKernelIncl P (x + y) =
      affineCyclicKernelIncl P x * affineCyclicKernelIncl P y := by
  rw [affineCyclicKernelIncl, affineCyclicKernelIncl, affineCyclicKernelIncl,
    map_add]
  change (affineCyclicBoundaryDeckData P).fillingDeckMap
      (Additive.toMul ((affineCyclicBoundaryDeckData P).translation x) *
        Additive.toMul ((affineCyclicBoundaryDeckData P).translation y)) = _
  rw [map_mul]

public theorem affineCyclicKernelIncl_zsmul'
    (P : AffineCyclicCentralFiberPresentationData m p D)
    (k : ℤ) (x : LatticeData.Lattice) :
    affineCyclicKernelIncl P (k • x) = affineCyclicKernelIncl P x ^ k := by
  induction k using Int.induction_on with
  | zero => simp [affineCyclicKernelIncl]
  | succ i ih =>
      rw [add_zsmul, one_zsmul, affineCyclicKernelIncl_add', ih, zpow_add_one]
  | pred i ih =>
    rw [sub_eq_add_neg, add_zsmul, neg_one_zsmul,
        affineCyclicKernelIncl_add', ih]
    have hneg : affineCyclicKernelIncl P (-x) =
        (affineCyclicKernelIncl P x)⁻¹ := by
      rw [affineCyclicKernelIncl]
      change (affineCyclicBoundaryDeckData P).fillingDeckMap
          (Additive.toMul ((affineCyclicBoundaryDeckData P).translation (-x))) = _
      rw [map_neg]
      change (affineCyclicBoundaryDeckData P).fillingDeckMap
          (Additive.toMul ((affineCyclicBoundaryDeckData P).translation x))⁻¹ = _
      rw [map_inv]
      rfl
    rw [hneg, ← zpow_neg_one, ← zpow_add]

public theorem affineCyclicBoundaryDeck_decompose'
    (P : AffineCyclicCentralFiberPresentationData m p D)
    (d : CanonicalCyclicAffineBoundaryDeck P.affine.latticeMap.toAddEquiv) :
    d = Additive.toMul
        ((affineCyclicBoundaryDeckData P).translation d.left.toAdd) *
      (affineCyclicBoundaryDeckData P).meridian ^ d.right.toAdd := by
  change d = SemidirectProduct.inl (Multiplicative.ofAdd d.left.toAdd) *
    SemidirectProduct.inr (Multiplicative.ofAdd 1) ^ d.right.toAdd
  rw [show SemidirectProduct.inr
        (φ := integerAffineMonodromy P.affine.latticeMap.toAddEquiv)
        (Multiplicative.ofAdd 1) ^ d.right.toAdd =
      SemidirectProduct.inr d.right by
    rw [← map_zpow]
    congr 1
    apply Multiplicative.toAdd.injective
    simp]
  exact (SemidirectProduct.inl_left_mul_inr_right d).symm

public theorem affineCyclicFillingDeckGenerator_pow'
    (P : AffineCyclicCentralFiberPresentationData m p D) :
    (affineCyclicBoundaryDeckData P).fillingDeckMap
          (affineCyclicBoundaryDeckData P).meridian ^ m =
      affineCyclicKernelIncl P P.twist := by
  have hrel := (affineCyclicBoundaryDeckData P).fillingDeckMap_fillingRelation
  rw [UnwrappedCyclicAffineBoundaryDeckData.fillingRelation, map_mul, map_pow,
    map_inv] at hrel
  change (affineCyclicBoundaryDeckData P).fillingDeckMap
      (affineCyclicBoundaryDeckData P).meridian ^ m *
    (affineCyclicKernelIncl P P.twist)⁻¹ = 1 at hrel
  exact eq_of_mul_inv_eq_one hrel

public theorem affineCyclicFillingDeckMap_eq_kernelIncl_of_right_modOrder_zero
    (P : AffineCyclicCentralFiberPresentationData m p D)
    (d : CanonicalCyclicAffineBoundaryDeck P.affine.latticeMap.toAddEquiv)
    (hzero : ((d.right.toAdd : ℤ) : ZMod m) = 0) :
    ∃ x : LatticeData.Lattice,
      affineCyclicKernelIncl P x =
        (affineCyclicBoundaryDeckData P).fillingDeckMap d := by
  obtain ⟨k, hk⟩ :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd d.right.toAdd m).mp hzero
  refine ⟨d.left.toAdd + k • P.twist, ?_⟩
  rw [affineCyclicKernelIncl_add', affineCyclicKernelIncl_zsmul']
  have hd := congrArg (affineCyclicBoundaryDeckData P).fillingDeckMap
    (affineCyclicBoundaryDeck_decompose' P d)
  rw [map_mul, map_zpow] at hd
  rw [hd, hk, zpow_mul, zpow_natCast,
    affineCyclicFillingDeckGenerator_pow', affineCyclicKernelIncl]

public theorem affineCyclicFillingDeckAction_free
    (P : AffineCyclicCentralFiberPresentationData m p D) :
    letI := affineCyclicFillingDeckAction P
    IsCancelSMul (affineCyclicBoundaryDeckData P).FillingDeck
      ComplexTwoSpace := by
  let _ := affineCyclicFillingDeckAction P
  rw [isCancelSMul_iff_eq_one_of_smul_eq]
  intro g z hg
  obtain ⟨d, rfl⟩ :=
    (affineCyclicBoundaryDeckData P).fillingDeckMap_surjective g
  rw [affineCyclicFillingDeckMap_smul] at hg
  have hzero :=
    affineCyclicBoundaryDeckTransform_fixed_right_modOrder P d z hg
  obtain ⟨x, hx⟩ :=
    affineCyclicFillingDeckMap_eq_kernelIncl_of_right_modOrder_zero P d hzero
  have hperiod : periodVector p x + z = z := by
    rw [← affineCyclicKernelIncl_smul P x z, hx]
    exact hg
  have hp : periodVector p x = 0 := by
    apply add_right_cancel (b := z)
    simpa using hperiod
  have hxzero : x = 0 := by
    apply periodHom_injective P.fullRank
    change periodVector p x = periodVector p 0
    simpa using hp
  rw [← hx, hxzero, affineCyclicKernelIncl]
  simp

public theorem affineCyclicFillingDeck_exists_normalForm
    (P : AffineCyclicCentralFiberPresentationData m p D)
    (g : (affineCyclicBoundaryDeckData P).FillingDeck) :
    ∃ r : ℕ, r < m ∧ ∃ x : LatticeData.Lattice,
      g = affineCyclicKernelIncl P x *
        ((affineCyclicBoundaryDeckData P).fillingDeckMap
          (affineCyclicBoundaryDeckData P).meridian) ^ r := by
  obtain ⟨d, rfl⟩ :=
    (affineCyclicBoundaryDeckData P).fillingDeckMap_surjective g
  let r := ((d.right.toAdd : ℤ) : ZMod m).val
  let e := d * (affineCyclicBoundaryDeckData P).meridian ^ (-(r : ℤ))
  have hrlt : r < m := ZMod.val_lt _
  have hzero : ((e.right.toAdd : ℤ) : ZMod m) = 0 := by
    change ((((d * (affineCyclicBoundaryDeckData P).meridian ^ (-(r : ℤ))).right).toAdd :
      ℤ) : ZMod m) = 0
    rw [SemidirectProduct.mul_right]
    have hrightpow := map_zpow SemidirectProduct.rightHom
      (affineCyclicBoundaryDeckData P).meridian (-(r : ℤ))
    rw [show ((affineCyclicBoundaryDeckData P).meridian ^ (-(r : ℤ))).right =
        (affineCyclicBoundaryDeckData P).meridian.right ^ (-(r : ℤ)) by
      exact hrightpow]
    simp only [affineCyclicBoundaryDeckData, canonicalCyclicAffineBoundaryDeckData,
      canonicalCyclicAffineMeridian, SemidirectProduct.right_inr]
    have hpow : (Multiplicative.ofAdd (1 : ℤ)) ^ (-(r : ℤ)) =
        Multiplicative.ofAdd (-(r : ℤ)) := by
      apply Multiplicative.toAdd.injective
      simp
    rw [hpow]
    change ((d.right.toAdd + -(r : ℤ) : ℤ) : ZMod m) = 0
    rw [Int.cast_add, Int.cast_neg]
    rw [show (((r : ℤ) : ZMod m)) = (r : ZMod m) by norm_num]
    rw [show (r : ZMod m) = ((d.right.toAdd : ℤ) : ZMod m) by
      exact (ZMod.natCast_zmod_val
        ((d.right.toAdd : ℤ) : ZMod m))]
    simp
  obtain ⟨x, hx⟩ :=
    affineCyclicFillingDeckMap_eq_kernelIncl_of_right_modOrder_zero P e hzero
  refine ⟨r, hrlt, x, ?_⟩
  have hemap : (affineCyclicBoundaryDeckData P).fillingDeckMap e =
      (affineCyclicBoundaryDeckData P).fillingDeckMap d *
        ((affineCyclicBoundaryDeckData P).fillingDeckMap
          (affineCyclicBoundaryDeckData P).meridian) ^ (-(r : ℤ)) := by
    simp [e, map_mul]
  rw [← hx] at hemap
  calc
    (affineCyclicBoundaryDeckData P).fillingDeckMap d =
        ((affineCyclicBoundaryDeckData P).fillingDeckMap d *
          ((affineCyclicBoundaryDeckData P).fillingDeckMap
            (affineCyclicBoundaryDeckData P).meridian) ^ (-(r : ℤ))) *
          ((affineCyclicBoundaryDeckData P).fillingDeckMap
            (affineCyclicBoundaryDeckData P).meridian) ^ r := by group
    _ = affineCyclicKernelIncl P x *
          ((affineCyclicBoundaryDeckData P).fillingDeckMap
            (affineCyclicBoundaryDeckData P).meridian) ^ r := by rw [← hemap]

public theorem affineCyclicFillingDeckAction_properlyDiscontinuous
    (P : AffineCyclicCentralFiberPresentationData m p D)
    (hL : Continuous P.affine.lift)
    (hLinv : Continuous P.affine.lift.symm) :
    letI := affineCyclicFillingDeckAction P
  ProperlyDiscontinuousSMul (affineCyclicBoundaryDeckData P).FillingDeck
      ComplexTwoSpace := by
  let _ := affineCyclicFillingDeckAction P
  let _ : ContinuousConstSMul (affineCyclicBoundaryDeckData P).FillingDeck
      ComplexTwoSpace := by
    refine ⟨fun g ↦ ?_⟩
    obtain ⟨d, rfl⟩ :=
      (affineCyclicBoundaryDeckData P).fillingDeckMap_surjective g
    rw [show (fun z : ComplexTwoSpace ↦
        (affineCyclicBoundaryDeckData P).fillingDeckMap d • z) =
      fun z ↦ affineCyclicBoundaryDeckTransform P d z by
        funext z
        exact affineCyclicFillingDeckMap_smul P d z]
    change Continuous fun z : ComplexTwoSpace ↦
      periodVector p d.left.toAdd +
        (affineEquiv P.affine.lift P.liftTranslation ^ d.right.toAdd) z
    exact continuous_const.add
      (continuous_affineEquiv_zpow P.affine.lift P.liftTranslation hL hLinv
        d.right.toAdd)
  refine ⟨?_⟩
  intro K L hK hLcompact
  let gen : (affineCyclicBoundaryDeckData P).FillingDeck :=
    (affineCyclicBoundaryDeckData P).fillingDeckMap
      (affineCyclicBoundaryDeckData P).meridian
  let C (r : ℕ) : Set ComplexTwoSpace :=
    (fun zw : ComplexTwoSpace × ComplexTwoSpace ↦ zw.1 - gen ^ r • zw.2) ''
      (L ×ˢ K)
  have hC (r : ℕ) : IsCompact (C r) := by
    apply (hLcompact.prod hK).image
    exact continuous_fst.sub ((continuous_const_smul (gen ^ r)).comp continuous_snd)
  have hX (r : ℕ) :
      {x : LatticeData.Lattice | periodVector p x ∈ C r}.Finite := by
    exact (tendsto_cofinite_cocompact_iff.mp
      (periodHom_tendsto_cofinite_cocompact P.fullRank) (C r) (hC r))
  let T : Set (affineCyclicBoundaryDeckData P).FillingDeck :=
    ⋃ r ∈ {r : ℕ | r < m},
      (fun x ↦ affineCyclicKernelIncl P x * gen ^ r) ''
        {x : LatticeData.Lattice | periodVector p x ∈ C r}
  have hT : T.Finite := by
    apply (Set.finite_Iio m).biUnion
    intro r hr
    exact (hX r).image _
  apply hT.subset
  intro g hg
  obtain ⟨r, hr, x, rfl⟩ := affineCyclicFillingDeck_exists_normalForm P g
  change (((fun z ↦ (affineCyclicKernelIncl P x * gen ^ r) • z) '' K ∩ L).Nonempty) at hg
  rcases hg with ⟨q, ⟨z, hzK, hzq⟩, hqL⟩
  have hspace : periodVector p x + gen ^ r • z = q := by
    change (affineCyclicKernelIncl P x * gen ^ r) • z = q at hzq
    rw [mul_smul, affineCyclicKernelIncl_smul] at hzq
    exact hzq
  refine Set.mem_iUnion.mpr ⟨r, Set.mem_iUnion.mpr ⟨hr, ?_⟩⟩
  refine ⟨x, ?_, rfl⟩
  refine ⟨(q, z), ⟨hqL, hzK⟩, ?_⟩
  exact (eq_sub_iff_add_eq.mpr hspace).symm

public theorem complexTwoReducedCentralFiberProjection_boundaryDeckTransform
    (P : AffineCyclicCentralFiberPresentationData m p D)
    (d : CanonicalCyclicAffineBoundaryDeck P.affine.latticeMap.toAddEquiv)
    (z : ComplexTwoSpace) :
    complexTwoReducedCentralFiberProjection (D := D)
        (affineCyclicBoundaryDeckTransform P d z) =
      complexTwoReducedCentralFiberProjection (D := D) z := by
  rw [affineCyclicBoundaryDeckTransform,
    complexTwoReducedCentralFiberProjection_period_add,
    complexTwoReducedCentralFiberProjection_affineEquiv_zpow]

public theorem complexTwoReducedCentralFiberProjection_fillingDeck_smul
    (P : AffineCyclicCentralFiberPresentationData m p D)
    (g : (affineCyclicBoundaryDeckData P).FillingDeck)
    (z : ComplexTwoSpace) :
    letI := affineCyclicFillingDeckAction P
    complexTwoReducedCentralFiberProjection (D := D) (g • z) =
      complexTwoReducedCentralFiberProjection (D := D) z := by
  let _ := affineCyclicFillingDeckAction P
  obtain ⟨d, rfl⟩ :=
    (affineCyclicBoundaryDeckData P).fillingDeckMap_surjective g
  rw [affineCyclicFillingDeckMap_smul,
    complexTwoReducedCentralFiberProjection_boundaryDeckTransform]

public theorem complexTwoReducedCentralFiberProjection_eq_implies_fiberGenerator_pow
    (z w : ComplexTwoSpace)
    (hq : complexTwoReducedCentralFiberProjection (D := D) z =
      complexTwoReducedCentralFiberProjection (D := D) w) :
    ∃ k : ℕ, torusProjection p z =
      (D.actionData.fiberGenerator ^ k) (torusProjection p w) := by
  change
    SphereSixComplex.Topology.PaperEllipticReducedCentralFiberCoverModels.RadialEllipticActionData.centralFiberCoverProjection D
        ((SphereSixComplex.Topology.PaperEllipticReducedCentralFiberCoverModels.RadialEllipticActionData.centralFiberCoverSourceHomeomorph D).symm
          (torusProjection p z)) =
      SphereSixComplex.Topology.PaperEllipticReducedCentralFiberCoverModels.RadialEllipticActionData.centralFiberCoverProjection D
        ((SphereSixComplex.Topology.PaperEllipticReducedCentralFiberCoverModels.RadialEllipticActionData.centralFiberCoverSourceHomeomorph D).symm
          (torusProjection p w)) at hq
  let _ := D.actionData.diagonalAction
  have horbit := Quotient.exact (congrArg Subtype.val hq)
  change ∃ g : FiniteCyclic m,
    g • ((SphereSixComplex.Topology.PaperEllipticReducedCentralFiberCoverModels.RadialEllipticActionData.centralFiberCoverSourceHomeomorph D).symm
        (torusProjection p w)).1 =
      ((SphereSixComplex.Topology.PaperEllipticReducedCentralFiberCoverModels.RadialEllipticActionData.centralFiberCoverSourceHomeomorph D).symm
        (torusProjection p z)).1 at horbit
  obtain ⟨g, hg⟩ := horbit
  refine ⟨(Multiplicative.toAdd g).val, ?_⟩
  rw [cyclic_eq_generator_pow g] at hg
  rw [D.actionData.generator_pow_smul] at hg
  have hsnd := congrArg Prod.snd hg
  rw [D.actionData.diagonalGenerator_pow_apply] at hsnd
  exact hsnd.symm

public theorem torusProjection_eq_implies_period_add
    (z w : ComplexTwoSpace) (h : torusProjection p z = torusProjection p w) :
    ∃ x : LatticeData.Lattice, periodVector p x + w = z := by
  have horbit := Quotient.exact h
  change ∃ g : PeriodGroup p, g • w = z at horbit
  obtain ⟨g, hg⟩ := horbit
  obtain ⟨x, hx⟩ := g.toAdd.2
  refine ⟨x, ?_⟩
  change (g.toAdd : ComplexTwoSpace) + w = z at hg
  change periodVector p x = (g.toAdd : ComplexTwoSpace) at hx
  rw [hx]
  exact hg

public theorem complexTwoReducedCentralFiberProjection_eq_implies_boundaryDeck
    (P : AffineCyclicCentralFiberPresentationData m p D)
    (z w : ComplexTwoSpace)
    (hq : complexTwoReducedCentralFiberProjection (D := D) z =
      complexTwoReducedCentralFiberProjection (D := D) w) :
    ∃ d : CanonicalCyclicAffineBoundaryDeck P.affine.latticeMap.toAddEquiv,
      affineCyclicBoundaryDeckTransform P d w = z := by
  obtain ⟨k, hk⟩ :=
    complexTwoReducedCentralFiberProjection_eq_implies_fiberGenerator_pow z w hq
  have htorus : torusProjection p z =
      torusProjection p
        ((affineEquiv P.affine.lift P.liftTranslation ^ k) w) := by
    rw [torusProjection_affineEquiv_pow]
    exact hk
  obtain ⟨x, hx⟩ := torusProjection_eq_implies_period_add z
    ((affineEquiv P.affine.lift P.liftTranslation ^ k) w) htorus
  refine ⟨⟨Multiplicative.ofAdd x, Multiplicative.ofAdd (k : ℤ)⟩, ?_⟩
  change periodVector p x +
    (affineEquiv P.affine.lift P.liftTranslation ^ (k : ℤ)) w = z
  simpa using hx

public theorem complexTwoReducedCentralFiberProjection_eq_iff_exists_fillingDeck
    (P : AffineCyclicCentralFiberPresentationData m p D)
    (z w : ComplexTwoSpace) :
    letI := affineCyclicFillingDeckAction P
    complexTwoReducedCentralFiberProjection (D := D) z =
        complexTwoReducedCentralFiberProjection (D := D) w ↔
      ∃ g : (affineCyclicBoundaryDeckData P).FillingDeck, g • w = z := by
  let _ := affineCyclicFillingDeckAction P
  constructor
  · intro hq
    obtain ⟨d, hd⟩ :=
      complexTwoReducedCentralFiberProjection_eq_implies_boundaryDeck P z w hq
    refine ⟨(affineCyclicBoundaryDeckData P).fillingDeckMap d, ?_⟩
    rw [affineCyclicFillingDeckMap_smul]
    exact hd
  · rintro ⟨g, rfl⟩
    exact complexTwoReducedCentralFiberProjection_fillingDeck_smul P g w

public theorem complexTwoReducedCentralFiberProjection_eq_iff_orbitRel
    (P : AffineCyclicCentralFiberPresentationData m p D)
    (z w : ComplexTwoSpace) :
    letI := affineCyclicFillingDeckAction P
    complexTwoReducedCentralFiberProjection (D := D) z =
        complexTwoReducedCentralFiberProjection (D := D) w ↔
      MulAction.orbitRel (affineCyclicBoundaryDeckData P).FillingDeck
        ComplexTwoSpace z w := by
  let _ := affineCyclicFillingDeckAction P
  rw [complexTwoReducedCentralFiberProjection_eq_iff_exists_fillingDeck]
  rfl

public theorem affineCyclicFillingDeckAction_continuous
    (P : AffineCyclicCentralFiberPresentationData m p D)
    (hL : Continuous P.affine.lift)
    (hLinv : Continuous P.affine.lift.symm) :
    letI := affineCyclicFillingDeckAction P
    ContinuousConstSMul (affineCyclicBoundaryDeckData P).FillingDeck
      ComplexTwoSpace := by
  let _ := affineCyclicFillingDeckAction P
  refine ⟨fun g ↦ ?_⟩
  obtain ⟨d, rfl⟩ :=
    (affineCyclicBoundaryDeckData P).fillingDeckMap_surjective g
  have htransform : Continuous fun z : ComplexTwoSpace ↦
      affineCyclicBoundaryDeckTransform P d z := by
    change Continuous fun z : ComplexTwoSpace ↦
      periodVector p d.left.toAdd +
        (affineEquiv P.affine.lift P.liftTranslation ^ d.right.toAdd) z
    exact continuous_const.add
      (continuous_affineEquiv_zpow P.affine.lift P.liftTranslation hL hLinv
        d.right.toAdd)
  simpa only [affineCyclicFillingDeckMap_smul] using htransform

variable {U : TriangleUniformization}
  (F : SphereSixComplex.Periods.PeriodFunctions U)

public theorem orderThreeCentralFiberPresentationData_lift_continuous :
    Continuous (orderThreeCentralFiberPresentationData F).affine.lift := by
  exact LinearMap.continuous_of_finiteDimensional
    (periodTransport g₁ (parameterMap F U.zOne)).toLinearMap

public theorem orderThreeCentralFiberPresentationData_lift_symm_continuous :
    Continuous (orderThreeCentralFiberPresentationData F).affine.lift.symm := by
  exact LinearMap.continuous_of_finiteDimensional
    (periodTransport g₁ (parameterMap F U.zOne)).symm.toLinearMap

public theorem orderFourCentralFiberPresentationData_lift_continuous :
    Continuous (orderFourCentralFiberPresentationData F).affine.lift := by
  exact LinearMap.continuous_of_finiteDimensional
    (periodTransport g₂ (parameterMap F U.zTwo)).toLinearMap

public theorem orderFourCentralFiberPresentationData_lift_symm_continuous :
    Continuous (orderFourCentralFiberPresentationData F).affine.lift.symm := by
  exact LinearMap.continuous_of_finiteDimensional
    (periodTransport g₂ (parameterMap F U.zTwo)).symm.toLinearMap

public theorem orderThreeAffineCyclicFillingDeckAction_continuous :
    let P := orderThreeCentralFiberPresentationData F
    letI := affineCyclicFillingDeckAction P
    ContinuousConstSMul (affineCyclicBoundaryDeckData P).FillingDeck
      ComplexTwoSpace := by
  exact affineCyclicFillingDeckAction_continuous _
    (orderThreeCentralFiberPresentationData_lift_continuous F)
    (orderThreeCentralFiberPresentationData_lift_symm_continuous F)

public theorem orderFourAffineCyclicFillingDeckAction_continuous :
    let P := orderFourCentralFiberPresentationData F
    letI := affineCyclicFillingDeckAction P
    ContinuousConstSMul (affineCyclicBoundaryDeckData P).FillingDeck
      ComplexTwoSpace := by
  exact affineCyclicFillingDeckAction_continuous _
    (orderFourCentralFiberPresentationData_lift_continuous F)
    (orderFourCentralFiberPresentationData_lift_symm_continuous F)

end EstablishedAffineCyclicQuotientHomology
end SphereSixComplex.Topology.PaperMultipleFiberHOneTopology
