module

public import SphereSixComplex.Paper.Topology.PaperActualEllipticCentralCoverProductLiftComparison
public import SphereSixComplex.Prerequisites.TriangleGroup.FreeProductCentralizers
import all SphereSixComplex.Paper.TriangleGroup.Representation

/-!
# The order-four boundary deck evaluation

The order-four cyclic-affine boundary deck group maps to the global affine deck group by
sending its positive meridian to the second free meridian and reversing lattice translations.
This computes the complete filling relation in the based-path orientation.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.TriangleGroup

open LatticeData

public theorem rhoLambda_inr_epsilon' (a : CyclicFour) :
    rhoLambda (Monoid.Coprod.inr a) epsilon' = epsilon' := by
  have ha : a = Multiplicative.ofAdd (1 : ZMod 4) ^ a.toAdd.val := by
    apply Multiplicative.toAdd.injective
    simp
  rw [ha, map_pow]
  change rhoLambda (g₂ ^ a.toAdd.val) epsilon' = epsilon'
  generalize a.toAdd.val = n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, map_mul]
    change rhoLambda (g₂ ^ n) (rhoLambda g₂ epsilon') = epsilon'
    rw [rhoLambda_g₂_apply, A₂_epsilon', ih]

public theorem rhoLambda_epsilon'_eq_of_commute_g₂ (g : Delta) (h : Commute g g₂) :
    rhoLambda g epsilon' = epsilon' := by
  obtain ⟨a, rfl⟩ := eq_inr_of_commute_g₂ g h
  exact rhoLambda_inr_epsilon' a

end SphereSixComplex.TriangleGroup

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex
open SphereSixComplex.CyclicAngularFundamentalDomain
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.LatticeData
open SphereSixComplex.Topology
open SphereSixComplex.Topology.PaperMultipleFiberHOneTopology
open SphereSixComplex.TriangleGroup

variable (A : PaperAnalyticData)

/-- Matching the first-power meridian determines the transported twist even when the entering
sheet is only known up to the finite elliptic stabilizer. -/
public theorem orderFour_enteringSheet_inverse_transports_epsilon'
    (g : Delta)
    (hmeridian : g⁻¹ * g₂ * g = A.geometricCentralClockwiseTwoDeck) :
    rhoLambda g⁻¹ epsilon' =
      rhoLambda ((g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent) epsilon' := by
  let q := (g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent
  have hconj : g⁻¹ * g₂ * g = q * g₂ * q⁻¹ :=
    hmeridian.trans A.geometricCentralClockwiseTwoDeck_eq_cuspConjugate
  have hcomm : Commute (g * q) g₂ := by
    rw [commute_iff_eq]
    calc
      (g * q) * g₂ = g * (q * g₂ * q⁻¹) * q := by group
      _ = g * (g⁻¹ * g₂ * g) * q := by rw [hconj]
      _ = g₂ * (g * q) := by group
  apply (rhoLambda g).injective
  rw [map_inv]
  change (rhoLambda g) ((rhoLambda g).symm epsilon') = _
  rw [LinearEquiv.apply_symm_apply]
  simpa only [map_mul, LinearEquiv.mul_apply] using
    (rhoLambda_epsilon'_eq_of_commute_g₂ (g * q) hcomm).symm

/-- The order-four boundary monodromy is the monodromy of the second marked free meridian. -/
public theorem paperOrderFourCentralMonodromy_second :
    (paperCentralFreeMonodromy secondMeridian).toAdd =
      (orderFourCentralFiberPresentationData A.periods).affine.latticeMap.toAddEquiv := by
  rw [A.orderFourCentralFiberPresentationData_affine_eq]
  apply AddEquiv.ext
  intro a
  simp [paperCentralFreeMonodromy, freeTwoMeridianMonodromy,
    integralOrbifoldPeriodMonodromy, orderFourDescendedAffineTorusAutomorphism]

/-- Integral powers of the second marked free meridian in the global affine deck group. -/
public def paperOrderFourCentralAngularDeck :
    Multiplicative ℤ →* paperCentralFreeAffineDeck where
  toFun n := freeAffineLift (M := paperCentralFreeMonodromy)
    (secondMeridian ^ n.toAdd)
  map_one' := by simp
  map_mul' n k := by
    change freeAffineLift (M := paperCentralFreeMonodromy)
        (secondMeridian ^ (n.toAdd + k.toAdd)) =
      freeAffineLift (M := paperCentralFreeMonodromy) (secondMeridian ^ n.toAdd) *
        freeAffineLift (M := paperCentralFreeMonodromy) (secondMeridian ^ k.toAdd)
    rw [zpow_add, map_mul]

@[simp]
public theorem paperOrderFourCentralAngularDeck_one :
    paperOrderFourCentralAngularDeck (Multiplicative.ofAdd 1) =
      freeAffineLift (M := paperCentralFreeMonodromy) secondMeridian := by
  simp [paperOrderFourCentralAngularDeck]

/-- Every power of the local order-four monodromy agrees with the corresponding power of the
second global free-meridian monodromy. -/
public theorem paperOrderFourCentralMonodromy_zpow
    (n : Multiplicative ℤ) (a : Lattice) :
    (paperCentralFreeMonodromy (secondMeridian ^ n.toAdd)).toAdd a =
      (integerAffineMonodromy
        (orderFourCentralFiberPresentationData A.periods).affine.latticeMap.toAddEquiv n
        (Multiplicative.ofAdd a)).toAdd := by
  rw [map_zpow]
  change ((n.toAdd • (paperCentralFreeMonodromy secondMeridian).toAdd) a) =
    (n.toAdd •
      (orderFourCentralFiberPresentationData A.periods).affine.latticeMap.toAddEquiv) a
  rw [A.paperOrderFourCentralMonodromy_second]

/-- The order-four boundary deck homomorphism with the orientation forced by the based-path
universal cover. -/
public def paperOrderFourCentralBoundaryToUniversalDeck :
    CanonicalCyclicAffineBoundaryDeck
        (orderFourCentralFiberPresentationData A.periods).affine.latticeMap.toAddEquiv →*
      paperCentralFreeAffineDeck :=
  SemidirectProduct.lift
    ((freeAffineTranslation (M := paperCentralFreeMonodromy)).comp
      (-AddMonoidHom.id Lattice)).toMultiplicative
    paperOrderFourCentralAngularDeck (by
      intro n
      apply MonoidHom.ext
      intro a
      change Additive.toMul
          (freeAffineTranslation (M := paperCentralFreeMonodromy)
            (-((integerAffineMonodromy
              (orderFourCentralFiberPresentationData A.periods).affine.latticeMap.toAddEquiv
              n a).toAdd))) =
        freeAffineLift (M := paperCentralFreeMonodromy) (secondMeridian ^ n.toAdd) *
          Additive.toMul
            (freeAffineTranslation (M := paperCentralFreeMonodromy) (-a.toAdd)) *
          (freeAffineLift (M := paperCentralFreeMonodromy)
            (secondMeridian ^ n.toAdd))⁻¹
      rw [freeAffine_conjugate]
      congr 2
      rw [map_neg]
      exact congrArg Neg.neg (A.paperOrderFourCentralMonodromy_zpow n a.toAdd).symm)

@[simp]
public theorem paperOrderFourCentralBoundaryToUniversalDeck_translation (a : Lattice) :
    A.paperOrderFourCentralBoundaryToUniversalDeck
        (Additive.toMul (canonicalCyclicAffineTranslation
          (orderFourCentralFiberPresentationData A.periods).affine.latticeMap.toAddEquiv a)) =
      Additive.toMul (freeAffineTranslation (M := paperCentralFreeMonodromy) (-a)) := by
  change Additive.toMul
      (freeAffineTranslation (M := paperCentralFreeMonodromy) (-a)) * 1 = _
  simp

@[simp]
public theorem paperOrderFourCentralBoundaryToUniversalDeck_meridian :
    A.paperOrderFourCentralBoundaryToUniversalDeck
        (canonicalCyclicAffineMeridian
          (orderFourCentralFiberPresentationData A.periods).affine.latticeMap.toAddEquiv) =
      freeAffineLift (M := paperCentralFreeMonodromy) secondMeridian := by
  change 1 * paperOrderFourCentralAngularDeck (Multiplicative.ofAdd 1) = _
  rw [one_mul, paperOrderFourCentralAngularDeck_one]

/-- The physical order-four mapping-torus deck group in based-path orientation. -/
public noncomputable def paperOrderFourActualBoundaryToUniversalDeck :
    OrderFourAffineMappingTorusDeck A.periods →* paperCentralFreeAffineDeck :=
  A.paperOrderFourCentralBoundaryToUniversalDeck.comp
    A.orderFourActualToCentralBoundaryDeckEquiv.toMonoidHom

@[simp]
public theorem paperOrderFourActualBoundaryToUniversalDeck_translation (a : Lattice) :
    A.paperOrderFourActualBoundaryToUniversalDeck
        (Additive.toMul (affineTorusMappingTorusDeckTranslation
          (orderFourDescendedAffineTorusAutomorphism A.periods) a)) =
      Additive.toMul (freeAffineTranslation (M := paperCentralFreeMonodromy) (-a)) := by
  rw [paperOrderFourActualBoundaryToUniversalDeck, MonoidHom.comp_apply]
  change A.paperOrderFourCentralBoundaryToUniversalDeck
      (A.orderFourActualToCentralBoundaryDeckEquiv
        (Additive.toMul (affineTorusMappingTorusDeckTranslation
          (orderFourDescendedAffineTorusAutomorphism A.periods) a))) = _
  rw [A.orderFourActualToCentralBoundaryDeckEquiv_translation,
    A.paperOrderFourCentralBoundaryToUniversalDeck_translation]

@[simp]
public theorem paperOrderFourActualBoundaryToUniversalDeck_positive_meridian :
    A.paperOrderFourActualBoundaryToUniversalDeck
        (affineTorusMappingTorusDeckMeridian
          (orderFourDescendedAffineTorusAutomorphism A.periods)) =
      freeAffineLift (M := paperCentralFreeMonodromy) secondMeridian := by
  rw [paperOrderFourActualBoundaryToUniversalDeck, MonoidHom.comp_apply]
  change A.paperOrderFourCentralBoundaryToUniversalDeck
      (A.orderFourActualToCentralBoundaryDeckEquiv
        (affineTorusMappingTorusDeckMeridian
          (orderFourDescendedAffineTorusAutomorphism A.periods))) = _
  rw [A.orderFourActualToCentralBoundaryDeckEquiv_meridian,
    A.paperOrderFourCentralBoundaryToUniversalDeck_meridian]

@[simp]
public theorem paperOrderFourActualBoundaryToUniversalDeck_physical_meridian :
    A.paperOrderFourActualBoundaryToUniversalDeck
        A.orderFourActualEllipticBoundaryDeckData.meridian =
      (freeAffineLift (M := paperCentralFreeMonodromy) secondMeridian)⁻¹ := by
  rw [orderFourActualEllipticBoundaryDeckData, map_inv,
    A.paperOrderFourActualBoundaryToUniversalDeck_positive_meridian]

/-- The second marked free meridian commutes with the invariant order-four twist translation. -/
public theorem paperOrderFourCentralDeck_second_commutes_epsilon' :
    Commute
      (freeAffineLift (M := paperCentralFreeMonodromy) secondMeridian)
      (Additive.toMul
        (freeAffineTranslation (M := paperCentralFreeMonodromy) epsilon')) := by
  rw [commute_iff_eq]
  have h := freeAffine_conjugate
    (M := paperCentralFreeMonodromy) secondMeridian epsilon'
  have hfixed :
      (paperCentralFreeMonodromy secondMeridian).toAdd epsilon' = epsilon' := by
    change rhoLambda (twoMeridianOrbifoldMap g₁ g₂ secondMeridian) epsilon' = epsilon'
    rw [twoMeridianOrbifoldMap_second, rhoLambda_g₂_apply, A₂_epsilon']
  rw [hfixed] at h
  exact mul_inv_eq_iff_eq_mul.mp h

/-- The complete order-four physical relation has the inverse classified central deck label. -/
public theorem paperOrderFourActualBoundaryToUniversalDeck_fillingRelation :
    A.paperOrderFourActualBoundaryToUniversalDeck
        A.orderFourActualEllipticBoundaryDeckData.fillingRelation =
      orderFourFillingRelationClassifiedCentralProductDeck⁻¹ := by
  simp only [UnwrappedCyclicAffineBoundaryDeckData.fillingRelation,
    orderFourActualEllipticBoundaryDeckData, map_mul, map_pow, map_inv]
  rw [A.paperOrderFourActualBoundaryToUniversalDeck_positive_meridian]
  rw [A.paperOrderFourActualBoundaryToUniversalDeck_translation]
  rw [orderFourFillingRelationClassifiedCentralProductDeck]
  simp only [map_neg, toMul_neg, inv_inv, mul_inv_rev, inv_pow]
  simpa only [inv_inv, inv_pow] using
    (paperOrderFourCentralDeck_second_commutes_epsilon'.inv_left.pow_left 4).eq

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
