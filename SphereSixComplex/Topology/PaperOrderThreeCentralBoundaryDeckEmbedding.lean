module

public import SphereSixComplex.Topology.PaperActualEllipticFillingDeckTransport
public import SphereSixComplex.Topology.PaperCuspCentralDeckComparison

/-!
# The order-three boundary deck group in the central affine deck group

This file embeds the canonical order-three cyclic-affine boundary deck group in the marked
two-meridian affine deck group.  The canonical positive meridian maps to the positive first
free lift.  Consequently its inverse, which is the physical order-three boundary meridian, maps
to the inverse first lift underlying the covering-space-oriented element `rhoOne`.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.CyclicAngularFundamentalDomain
open SphereSixComplex.LatticeData
open SphereSixComplex.Periods
open SphereSixComplex.Topology
open SphereSixComplex.Topology.PaperMultipleFiberHOneTopology
open SphereSixComplex.TriangleGroup

variable (A : PaperAnalyticData)

/-- The order-three boundary monodromy is the monodromy of the first marked free meridian. -/
public theorem paperOrderThreeCentralMonodromy_first :
    (paperCentralFreeMonodromy firstMeridian).toAdd =
      (orderThreeCentralFiberPresentationData A.periods).affine.latticeMap.toAddEquiv := by
  rw [A.orderThreeCentralFiberPresentationData_affine_eq]
  apply AddEquiv.ext
  intro a
  simp [paperCentralFreeMonodromy, freeTwoMeridianMonodromy,
    integralOrbifoldPeriodMonodromy, orderThreeDescendedAffineTorusAutomorphism]

/-- Integral powers of the first marked free meridian in the central affine deck group. -/
public def paperOrderThreeCentralAngularDeck :
    Multiplicative ℤ →* paperCentralFreeAffineDeck where
  toFun n := freeAffineLift (M := paperCentralFreeMonodromy)
    (firstMeridian ^ n.toAdd)
  map_one' := by simp
  map_mul' n k := by
    change freeAffineLift (M := paperCentralFreeMonodromy)
        (firstMeridian ^ (n.toAdd + k.toAdd)) =
      freeAffineLift (M := paperCentralFreeMonodromy) (firstMeridian ^ n.toAdd) *
        freeAffineLift (M := paperCentralFreeMonodromy) (firstMeridian ^ k.toAdd)
    rw [zpow_add, map_mul]

@[simp]
public theorem paperOrderThreeCentralAngularDeck_apply (n : Multiplicative ℤ) :
    paperOrderThreeCentralAngularDeck n =
      freeAffineLift (M := paperCentralFreeMonodromy)
        (firstMeridian ^ n.toAdd) := rfl

@[simp]
public theorem paperOrderThreeCentralAngularDeck_one :
    paperOrderThreeCentralAngularDeck (Multiplicative.ofAdd 1) =
      freeAffineLift (M := paperCentralFreeMonodromy) firstMeridian := by
  simp

private theorem paperOrderThreeCentralAngularDeck_left (n : Multiplicative ℤ) :
    (paperOrderThreeCentralAngularDeck n).left = 1 := by
  rfl

private theorem paperOrderThreeCentralAngularDeck_right (n : Multiplicative ℤ) :
    (paperOrderThreeCentralAngularDeck n).right = firstMeridian ^ n.toAdd := by
  rfl

/-- Every integral power of the local order-three monodromy agrees with the corresponding
power of the first global free-meridian monodromy. -/
public theorem paperOrderThreeCentralMonodromy_zpow
    (n : Multiplicative ℤ) (a : Lattice) :
    (paperCentralFreeMonodromy (firstMeridian ^ n.toAdd)).toAdd a =
      (integerAffineMonodromy
        (orderThreeCentralFiberPresentationData A.periods).affine.latticeMap.toAddEquiv n
        (Multiplicative.ofAdd a)).toAdd := by
  rw [map_zpow]
  change ((n.toAdd • (paperCentralFreeMonodromy firstMeridian).toAdd) a) =
    (n.toAdd •
      (orderThreeCentralFiberPresentationData A.periods).affine.latticeMap.toAddEquiv) a
  rw [A.paperOrderThreeCentralMonodromy_first]

/-- The canonical order-three cyclic-affine boundary deck group as the subgroup carried by the
first marked meridian of the global affine deck group. -/
public def paperOrderThreeCentralBoundaryToCentralDeck :
    CanonicalCyclicAffineBoundaryDeck
        (orderThreeCentralFiberPresentationData A.periods).affine.latticeMap.toAddEquiv →*
      paperCentralFreeAffineDeck :=
  SemidirectProduct.lift
    (freeAffineTranslation (M := paperCentralFreeMonodromy)).toMultiplicative
    paperOrderThreeCentralAngularDeck (by
      intro n
      apply MonoidHom.ext
      intro a
      change Additive.toMul
          (freeAffineTranslation (M := paperCentralFreeMonodromy)
            ((integerAffineMonodromy
              (orderThreeCentralFiberPresentationData A.periods).affine.latticeMap.toAddEquiv
              n a).toAdd)) =
        freeAffineLift (M := paperCentralFreeMonodromy) (firstMeridian ^ n.toAdd) *
          Additive.toMul
            (freeAffineTranslation (M := paperCentralFreeMonodromy) a.toAdd) *
          (freeAffineLift (M := paperCentralFreeMonodromy)
            (firstMeridian ^ n.toAdd))⁻¹
      rw [freeAffine_conjugate]
      congr 2
      exact (A.paperOrderThreeCentralMonodromy_zpow n a.toAdd).symm)

@[simp]
public theorem paperOrderThreeCentralBoundaryToCentralDeck_inl
    (a : Multiplicative Lattice) :
    A.paperOrderThreeCentralBoundaryToCentralDeck (SemidirectProduct.inl a) =
      Additive.toMul
        (freeAffineTranslation (M := paperCentralFreeMonodromy) a.toAdd) := by
  change Additive.toMul
      (freeAffineTranslation (M := paperCentralFreeMonodromy) a.toAdd) * 1 = _
  simp

@[simp]
public theorem paperOrderThreeCentralBoundaryToCentralDeck_inr
    (n : Multiplicative ℤ) :
    A.paperOrderThreeCentralBoundaryToCentralDeck (SemidirectProduct.inr n) =
      paperOrderThreeCentralAngularDeck n := by
  change 1 * paperOrderThreeCentralAngularDeck n = _
  simp

@[simp]
public theorem paperOrderThreeCentralBoundaryToCentralDeck_translation (a : Lattice) :
    A.paperOrderThreeCentralBoundaryToCentralDeck
        (Additive.toMul (canonicalCyclicAffineTranslation
          (orderThreeCentralFiberPresentationData A.periods).affine.latticeMap.toAddEquiv a)) =
      Additive.toMul
        (freeAffineTranslation (M := paperCentralFreeMonodromy) a) := by
  change Additive.toMul
      (freeAffineTranslation (M := paperCentralFreeMonodromy) a) * 1 = _
  simp

@[simp]
public theorem paperOrderThreeCentralBoundaryToCentralDeck_meridian :
    A.paperOrderThreeCentralBoundaryToCentralDeck
        (canonicalCyclicAffineMeridian
          (orderThreeCentralFiberPresentationData A.periods).affine.latticeMap.toAddEquiv) =
      freeAffineLift (M := paperCentralFreeMonodromy) firstMeridian := by
  change 1 * paperOrderThreeCentralAngularDeck (Multiplicative.ofAdd 1) = _
  rw [one_mul, paperOrderThreeCentralAngularDeck_one]

/-- The physical inverse meridian maps to the inverse first free lift. -/
@[simp]
public theorem paperOrderThreeCentralBoundaryToCentralDeck_inverse_meridian :
    A.paperOrderThreeCentralBoundaryToCentralDeck
        (canonicalCyclicAffineMeridian
          (orderThreeCentralFiberPresentationData A.periods).affine.latticeMap.toAddEquiv)⁻¹ =
      (freeAffineLift (M := paperCentralFreeMonodromy) firstMeridian)⁻¹ := by
  rw [map_inv, A.paperOrderThreeCentralBoundaryToCentralDeck_meridian]

/-- In covering-space orientation, the inverse local meridian is precisely `rhoOne`. -/
public theorem opposite_paperOrderThreeCentralBoundaryToCentralDeck_inverse_meridian :
    MulOpposite.op
        (A.paperOrderThreeCentralBoundaryToCentralDeck
          (canonicalCyclicAffineMeridian
            (orderThreeCentralFiberPresentationData A.periods).affine.latticeMap.toAddEquiv)⁻¹) =
      (oppositeFreeAffineCorePiOneData paperCentralFreeMonodromy).rhoOne := by
  rw [A.paperOrderThreeCentralBoundaryToCentralDeck_inverse_meridian]
  rfl

private theorem paperOrderThreeCentralTranslation_left (a : Multiplicative Lattice) :
    (Additive.toMul
      (freeAffineTranslation (M := paperCentralFreeMonodromy) a.toAdd)).left = a := by
  exact ofAdd_toAdd a

private theorem paperOrderThreeCentralTranslation_right (a : Multiplicative Lattice) :
    (Additive.toMul
      (freeAffineTranslation (M := paperCentralFreeMonodromy) a.toAdd)).right = 1 := rfl

/-- The cyclic-affine comparison is an embedding. -/
public theorem paperOrderThreeCentralBoundaryToCentralDeck_injective :
    Function.Injective A.paperOrderThreeCentralBoundaryToCentralDeck := by
  intro d e h
  rw [← SemidirectProduct.inl_left_mul_inr_right d,
    ← SemidirectProduct.inl_left_mul_inr_right e, map_mul, map_mul,
    A.paperOrderThreeCentralBoundaryToCentralDeck_inl,
    A.paperOrderThreeCentralBoundaryToCentralDeck_inl,
    A.paperOrderThreeCentralBoundaryToCentralDeck_inr,
    A.paperOrderThreeCentralBoundaryToCentralDeck_inr] at h
  apply SemidirectProduct.ext
  · have hleft := congrArg SemidirectProduct.left h
    simpa only [SemidirectProduct.mul_left, paperOrderThreeCentralTranslation_left,
      paperOrderThreeCentralTranslation_right, paperOrderThreeCentralAngularDeck_left,
      map_one, mul_one] using hleft
  · have hright := congrArg SemidirectProduct.right h
    simp only [SemidirectProduct.mul_right, paperOrderThreeCentralTranslation_right,
      paperOrderThreeCentralAngularDeck_right, one_mul] at hright
    have hright' := congrArg
      (twoMeridianOrbifoldMap (Multiplicative.ofAdd 1 : Multiplicative ℤ) 1) hright
    simp only [map_zpow, twoMeridianOrbifoldMap_first] at hright'
    rw [← ofAdd_zsmul, ← ofAdd_zsmul] at hright'
    have htoAdd := congrArg Multiplicative.toAdd hright'
    apply Multiplicative.toAdd.injective
    simpa using htoAdd

/-- The translation and positive-meridian formulas uniquely determine the cyclic-affine
comparison. -/
public theorem paperOrderThreeCentralBoundaryToCentralDeck_unique
    (f : CanonicalCyclicAffineBoundaryDeck
        (orderThreeCentralFiberPresentationData A.periods).affine.latticeMap.toAddEquiv →*
      paperCentralFreeAffineDeck)
    (htranslation : ∀ a : Lattice,
      f (Additive.toMul (canonicalCyclicAffineTranslation
        (orderThreeCentralFiberPresentationData A.periods).affine.latticeMap.toAddEquiv a)) =
        Additive.toMul (freeAffineTranslation (M := paperCentralFreeMonodromy) a))
    (hmeridian :
      f (canonicalCyclicAffineMeridian
        (orderThreeCentralFiberPresentationData A.periods).affine.latticeMap.toAddEquiv) =
        freeAffineLift (M := paperCentralFreeMonodromy) firstMeridian) :
    f = A.paperOrderThreeCentralBoundaryToCentralDeck := by
  apply SemidirectProduct.hom_ext
  · apply MonoidHom.ext
    intro a
    change f (SemidirectProduct.inl a) =
      A.paperOrderThreeCentralBoundaryToCentralDeck (SemidirectProduct.inl a)
    rw [A.paperOrderThreeCentralBoundaryToCentralDeck_inl]
    convert htranslation a.toAdd using 1
    apply congrArg f
    change SemidirectProduct.inl a = SemidirectProduct.inl (Multiplicative.ofAdd a.toAdd)
    exact congrArg
      (SemidirectProduct.inl (N := Multiplicative Lattice)
        (G := Multiplicative ℤ)
        (φ := integerAffineMonodromy
          (orderThreeCentralFiberPresentationData A.periods).affine.latticeMap.toAddEquiv))
      (ofAdd_toAdd a).symm
  · apply MonoidHom.ext
    intro n
    have hn : SemidirectProduct.inr n =
        (canonicalCyclicAffineMeridian
          (orderThreeCentralFiberPresentationData A.periods).affine.latticeMap.toAddEquiv) ^
            n.toAdd := by
      change SemidirectProduct.inr n =
        (SemidirectProduct.inr (Multiplicative.ofAdd 1)) ^ n.toAdd
      rw [← map_zpow]
      congr 1
      apply Multiplicative.toAdd.injective
      simp
    change f (SemidirectProduct.inr n) =
      A.paperOrderThreeCentralBoundaryToCentralDeck (SemidirectProduct.inr n)
    rw [hn, map_zpow, map_zpow, hmeridian,
      A.paperOrderThreeCentralBoundaryToCentralDeck_meridian]

/-- The physical order-three mapping-torus deck group mapped into the global central deck group. -/
public noncomputable def paperOrderThreeActualBoundaryToCentralDeck :
    OrderThreeAffineMappingTorusDeck A.periods →* paperCentralFreeAffineDeck :=
  A.paperOrderThreeCentralBoundaryToCentralDeck.comp
    A.orderThreeActualToCentralBoundaryDeckEquiv.toMonoidHom

@[simp]
public theorem paperOrderThreeActualBoundaryToCentralDeck_translation (a : Lattice) :
    A.paperOrderThreeActualBoundaryToCentralDeck
        (Additive.toMul (affineTorusMappingTorusDeckTranslation
          (orderThreeDescendedAffineTorusAutomorphism A.periods) a)) =
      Additive.toMul
        (freeAffineTranslation (M := paperCentralFreeMonodromy) a) := by
  rw [paperOrderThreeActualBoundaryToCentralDeck, MonoidHom.comp_apply]
  change A.paperOrderThreeCentralBoundaryToCentralDeck
      (A.orderThreeActualToCentralBoundaryDeckEquiv
        (Additive.toMul (affineTorusMappingTorusDeckTranslation
          (orderThreeDescendedAffineTorusAutomorphism A.periods) a))) = _
  rw [
    A.orderThreeActualToCentralBoundaryDeckEquiv_translation,
    A.paperOrderThreeCentralBoundaryToCentralDeck_translation]

@[simp]
public theorem paperOrderThreeActualBoundaryToCentralDeck_positive_meridian :
    A.paperOrderThreeActualBoundaryToCentralDeck
        (affineTorusMappingTorusDeckMeridian
          (orderThreeDescendedAffineTorusAutomorphism A.periods)) =
      freeAffineLift (M := paperCentralFreeMonodromy) firstMeridian := by
  rw [paperOrderThreeActualBoundaryToCentralDeck, MonoidHom.comp_apply]
  change A.paperOrderThreeCentralBoundaryToCentralDeck
      (A.orderThreeActualToCentralBoundaryDeckEquiv
        (affineTorusMappingTorusDeckMeridian
          (orderThreeDescendedAffineTorusAutomorphism A.periods))) = _
  rw [
    A.orderThreeActualToCentralBoundaryDeckEquiv_meridian,
    A.paperOrderThreeCentralBoundaryToCentralDeck_meridian]

/-- The selected physical meridian in the actual order-three deck data maps to the inverse first
free lift, hence to the deck element underlying the central `rhoOne`. -/
@[simp]
public theorem paperOrderThreeActualBoundaryToCentralDeck_physical_meridian :
    A.paperOrderThreeActualBoundaryToCentralDeck
        A.orderThreeActualEllipticBoundaryDeckData.meridian =
      (freeAffineLift (M := paperCentralFreeMonodromy) firstMeridian)⁻¹ := by
  rw [orderThreeActualEllipticBoundaryDeckData, map_inv,
    A.paperOrderThreeActualBoundaryToCentralDeck_positive_meridian]

public theorem opposite_paperOrderThreeActualBoundaryToCentralDeck_physical_meridian :
    MulOpposite.op
        (A.paperOrderThreeActualBoundaryToCentralDeck
          A.orderThreeActualEllipticBoundaryDeckData.meridian) =
      (oppositeFreeAffineCorePiOneData paperCentralFreeMonodromy).rhoOne := by
  rw [A.paperOrderThreeActualBoundaryToCentralDeck_physical_meridian]
  rfl

end SphereSixComplex.Geometry.PaperAnalyticData

end
