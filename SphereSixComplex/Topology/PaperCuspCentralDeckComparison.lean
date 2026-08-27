module

public import SphereSixComplex.Topology.EstablishedEquivariantUniversalCover
public import SphereSixComplex.Topology.PaperCuspBoundaryUniversalCover

/-!
# The cusp peripheral subgroup in the marked central affine deck group

This file identifies the abstract deck group used by the actual cusp collar with the canonical
parabolic subgroup of the two-meridian affine deck group.  It is purely algebraic: the geometric
equivariant comparison of the two covering projections is constructed separately.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Topology

open SphereSixComplex.LatticeData SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.GlobalTorusFamily

/-- The monodromy representation carried by the marked central affine deck group. -/
public abbrev paperCentralFreeMonodromy :
    TwoMeridianDeckGroup →* Multiplicative (AddAut Lattice) :=
  freeTwoMeridianMonodromy (twoMeridianOrbifoldMap g₁ g₂)
    integralOrbifoldPeriodMonodromy

/-- The marked affine deck group of the punctured central family. -/
public abbrev paperCentralFreeAffineDeck :=
  FreeTwoMeridianAffineDeck Lattice paperCentralFreeMonodromy

/-- The positively oriented local cusp meridian is the inverse of the product of the two finite
puncture meridians. -/
public def paperCuspCentralBaseMeridian : TwoMeridianDeckGroup :=
  (firstMeridian * secondMeridian)⁻¹

@[simp]
public theorem twoMeridianOrbifoldMap_paperCuspCentralBaseMeridian :
    twoMeridianOrbifoldMap g₁ g₂ paperCuspCentralBaseMeridian = g₀ := by
  simp only [paperCuspCentralBaseMeridian, map_inv, map_mul,
    twoMeridianOrbifoldMap_first, twoMeridianOrbifoldMap_second]
  exact (eq_inv_of_mul_eq_one_right g₁_mul_g₂_mul_g₀).symm

/-- The central monodromy around the marked cusp word is the actual parabolic cusp monodromy. -/
public theorem paperCentralFreeMonodromy_cusp :
    (paperCentralFreeMonodromy paperCuspCentralBaseMeridian).toAdd =
      paperCuspMonodromy := by
  apply AddEquiv.ext
  intro a
  change rhoLambda
      (twoMeridianOrbifoldMap g₁ g₂ paperCuspCentralBaseMeridian) a = m₀ a
  rw [twoMeridianOrbifoldMap_paperCuspCentralBaseMeridian, rhoLambda_g₀]

/-- Integral powers of the central cusp word, regarded as affine deck transformations. -/
public def paperCuspCentralAngularDeck :
    Multiplicative ℤ →* paperCentralFreeAffineDeck where
  toFun n := freeAffineLift (M := paperCentralFreeMonodromy)
    paperCuspCentralBaseMeridian ^ n.toAdd
  map_one' := by simp
  map_mul' n k := by
    change freeAffineLift (M := paperCentralFreeMonodromy)
        paperCuspCentralBaseMeridian ^ (n.toAdd + k.toAdd) =
      freeAffineLift (M := paperCentralFreeMonodromy)
          paperCuspCentralBaseMeridian ^ n.toAdd *
        freeAffineLift (M := paperCentralFreeMonodromy)
          paperCuspCentralBaseMeridian ^ k.toAdd
    rw [zpow_add]

@[simp]
public theorem paperCuspCentralAngularDeck_one :
    paperCuspCentralAngularDeck (Multiplicative.ofAdd 1) =
      freeAffineLift (M := paperCentralFreeMonodromy)
        paperCuspCentralBaseMeridian := by
  simp [paperCuspCentralAngularDeck]

/-- The action of every integral cusp power on the lattice agrees in the local and central deck
groups. -/
public theorem paperCentralFreeMonodromy_cusp_zpow
    (n : Multiplicative ℤ) (a : Lattice) :
    (paperCentralFreeMonodromy
        (paperCuspCentralBaseMeridian ^ n.toAdd)).toAdd a =
      (integerAffineMonodromy paperCuspMonodromy n
        (Multiplicative.ofAdd a)).toAdd := by
  rw [map_zpow]
  change ((n.toAdd •
      (paperCentralFreeMonodromy paperCuspCentralBaseMeridian).toAdd) a) =
    (n.toAdd • paperCuspMonodromy) a
  rw [paperCentralFreeMonodromy_cusp]

/-- The actual cusp boundary deck group maps to the canonical parabolic subgroup of the marked
central affine deck group. -/
public def paperCuspBoundaryToCentralDeck :
    paperCuspBoundaryDeck →* paperCentralFreeAffineDeck :=
  SemidirectProduct.lift
    (freeAffineTranslation (M := paperCentralFreeMonodromy)).toMultiplicative
    paperCuspCentralAngularDeck (by
      intro n
      apply MonoidHom.ext
      intro a
      change Additive.toMul
          (freeAffineTranslation (M := paperCentralFreeMonodromy)
            ((integerAffineMonodromy paperCuspMonodromy n a).toAdd)) =
        (freeAffineLift (M := paperCentralFreeMonodromy)
            paperCuspCentralBaseMeridian) ^ n.toAdd *
          Additive.toMul
            (freeAffineTranslation (M := paperCentralFreeMonodromy) a.toAdd) *
          ((freeAffineLift (M := paperCentralFreeMonodromy)
            paperCuspCentralBaseMeridian) ^ n.toAdd)⁻¹
      rw [← map_zpow]
      rw [freeAffine_conjugate]
      congr 2
      exact (paperCentralFreeMonodromy_cusp_zpow n a.toAdd).symm)

@[simp]
public theorem paperCuspBoundaryToCentralDeck_translation (a : Lattice) :
    paperCuspBoundaryToCentralDeck
        (Additive.toMul (paperCuspBoundaryTranslation a)) =
      Additive.toMul
        (freeAffineTranslation (M := paperCentralFreeMonodromy) a) := by
  change Additive.toMul
      (freeAffineTranslation (M := paperCentralFreeMonodromy) a) * 1 = _
  rw [mul_one]

@[simp]
public theorem paperCuspBoundaryToCentralDeck_meridian :
    paperCuspBoundaryToCentralDeck paperCuspBoundaryMeridian =
      freeAffineLift (M := paperCentralFreeMonodromy)
        paperCuspCentralBaseMeridian := by
  change 1 * paperCuspCentralAngularDeck (Multiplicative.ofAdd 1) = _
  rw [one_mul, paperCuspCentralAngularDeck_one]

/-- In covering-space orientation, the marked central cusp word is the product of the two core
meridians in the order used by `ActualCuspCentralNaturality`. -/
public theorem opposite_paperCuspCentralBaseMeridian_eq_rhoOne_mul_rhoTwo :
    MulOpposite.op
        (freeAffineLift (M := paperCentralFreeMonodromy)
          paperCuspCentralBaseMeridian) =
      (oppositeFreeAffineCorePiOneData paperCentralFreeMonodromy).rhoOne *
        (oppositeFreeAffineCorePiOneData paperCentralFreeMonodromy).rhoTwo := by
  simp [paperCuspCentralBaseMeridian, oppositeFreeAffineCorePiOneData]

end SphereSixComplex.Topology

end
