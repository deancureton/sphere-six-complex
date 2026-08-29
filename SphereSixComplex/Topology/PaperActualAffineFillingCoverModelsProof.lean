module

public import SphereSixComplex.Topology.PaperActualAffineFillingCoverModelsDefs
public import SphereSixComplex.Topology.PaperCuspAffineFillingBridge

/-!
# Reduction of the actual affine filling-cover squares to the two elliptic inputs

`ActualAffineFillingCoverSquares` bundles the three regular cover squares of the four-piece star
together with the based affine filling bridge.  The cusp square, its marked central naturality
and the whole cusp half of the bridge are already available:
`PaperCuspChosenAffineFilling` and `PaperCuspAffineFillingBridge`.

This module supplies the two purely formal pieces that were still missing on the elliptic side —
the based gluing squares of the two elliptic overlaps, and the transported cyclic filling
relations — and isolates the remaining geometric content in a single structure,
`ActualEllipticCentralNaturality`.  That structure is the exact elliptic counterpart of
`ActualCuspCentralNaturality`, extended by the two chosen cyclic regular-cover models.

The reduction theorem, `nonempty_actualAffineFillingCoverSquares_of_ellipticNaturality`, shows
that any marked cusp naturality together with such an elliptic package produces
`Nonempty A.ActualAffineFillingCoverSquares`.  It uses no van Kampen conclusion and, in
particular, not `establishedActualAffineFillingCoverSquares`.

The two naturalities are then bundled as `ActualStarPeripheralNaturality`, and the single
remaining geometric input is `establishedActualStarPeripheralNaturality`.
-/

@[expose] public section

noncomputable section

open Set Topology

namespace SphereSixComplex.Topology
namespace PaperVanKampenFourPieceCover

variable {Y : Type*} [TopologicalSpace Y] {base : Y}

/-- The based gluing square for an arbitrary overlap of the core with a piece, transported to the
base point along a connector that stays inside the core. -/
public theorem coreSquare_apply
    (D : PaperVanKampenFourPieceCover base) (P : Set Y) {pt : Y}
    (hpt : pt ∈ D.core ∩ P) (conn : Path base pt) (hconn : ∀ t, conn t ∈ D.core)
    (γ : FundamentalGroup (D.core ∩ P : Set Y) ⟨pt, hpt⟩) :
    D.coreFundamentalGroupMap
        ((FundamentalGroup.fundamentalGroupMulEquivOfPath
            (D.connectorInCore conn hconn hpt.1).symm)
          (FundamentalGroup.map (D.overlapToCore P) ⟨pt, hpt⟩ γ)) =
      (FundamentalGroup.fundamentalGroupMulEquivOfPath conn.symm)
        (FundamentalGroup.map (subsetInclusion P) ⟨pt, hpt.2⟩
          (FundamentalGroup.map
            (⟨fun z : (D.core ∩ P : Set Y) ↦ (⟨z.1, z.2.2⟩ : P), by fun_prop⟩ :
              C((D.core ∩ P : Set Y), P)) ⟨pt, hpt⟩ γ)) := by
  set connCore := D.connectorInCore conn hconn hpt.1
  have hnat := map_fundamentalGroupMulEquivOfPath (subsetInclusion D.core) connCore.symm
    (FundamentalGroup.map (D.overlapToCore P) ⟨pt, hpt⟩ γ)
  have hpath : connCore.symm.map (subsetInclusion D.core).continuous = conn.symm := by
    ext t
    rfl
  change FundamentalGroup.map (subsetInclusion D.core) _
      ((FundamentalGroup.fundamentalGroupMulEquivOfPath connCore.symm) _) =
    (FundamentalGroup.fundamentalGroupMulEquivOfPath conn.symm) _
  apply Eq.trans hnat
  rw [hpath]
  congr 1
  have h1 := map_map (D.overlapToCore P) (subsetInclusion D.core) ⟨pt, hpt⟩ γ
  have h2 := map_map
    (⟨fun z : (D.core ∩ P : Set Y) ↦ (⟨z.1, z.2.2⟩ : P), by fun_prop⟩ :
      C((D.core ∩ P : Set Y), P)) (subsetInclusion P) ⟨pt, hpt⟩ γ
  apply Eq.trans h1
  apply Eq.trans ?_ h2.symm
  rfl

end PaperVanKampenFourPieceCover
end SphereSixComplex.Topology

namespace SphereSixComplex

/-- The canonical cyclic affine relation is killed by the transported filling inclusion. -/
public theorem chosenCyclicRelation_killed
    {m : ℕ} {Λ B N : Type*} [NeZero m] [AddCommGroup Λ]
    [TopologicalSpace B] [TopologicalSpace N]
    (D : ChosenCyclicAffineFillingCoverModel m Λ B N) {b : B} {n : N}
    (hb : D.boundaryBase = b) (hn : D.fillingBase = n) {tw : Λ} (htw : D.twist = tw) :
    fundamentalGroupHomOfBaseEq hb hn D.fundamentalGroupMap
        ((fundamentalGroupElementOfBaseEq hb D.meridian) ^ m *
          (Additive.toMul
            ((fundamentalGroupAddHomOfBaseEq hb D.translation) tw))⁻¹) = 1 := by
  subst hb
  subst hn
  subst htw
  exact D.fundamentalGroupMap_relation

end SphereSixComplex

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex.LatticeData SphereSixComplex.Topology
open SphereSixComplex.Topology.PaperVanKampenFourPieceCover

variable (A : PaperAnalyticData)

/-- The actual order-three overlap included into the core and transported along the specified
connector to the base point of the four-piece cover. -/
public noncomputable def actualEllipticThreeOverlapToCore :
    FundamentalGroup
        (A.actualVanKampenFourPieceCover.core ∩
          A.actualVanKampenFourPieceCover.ellipticThree : Set A.VanKampenSpace)
        ⟨A.actualVanKampenFourPieceCover.ellipticThreePoint,
          A.actualVanKampenFourPieceCover.ellipticThreePoint_mem⟩ →*
      FundamentalGroup A.actualVanKampenFourPieceCover.core
        ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩ :=
  (FundamentalGroup.fundamentalGroupMulEquivOfPath
      (A.actualVanKampenFourPieceCover.connectorInCore
        A.actualVanKampenFourPieceCover.ellipticThreeConnector
        A.actualVanKampenFourPieceCover.ellipticThreeConnector_mem
        A.actualVanKampenFourPieceCover.ellipticThreePoint_mem.1).symm).toMonoidHom.comp
    (FundamentalGroup.map
      (A.actualVanKampenFourPieceCover.overlapToCore
        A.actualVanKampenFourPieceCover.ellipticThree)
      ⟨A.actualVanKampenFourPieceCover.ellipticThreePoint,
        A.actualVanKampenFourPieceCover.ellipticThreePoint_mem⟩)

/-- The actual order-four overlap included into the core and transported along the specified
connector to the base point of the four-piece cover. -/
public noncomputable def actualEllipticFourOverlapToCore :
    FundamentalGroup
        (A.actualVanKampenFourPieceCover.core ∩
          A.actualVanKampenFourPieceCover.ellipticFour : Set A.VanKampenSpace)
        ⟨A.actualVanKampenFourPieceCover.ellipticFourPoint,
          A.actualVanKampenFourPieceCover.ellipticFourPoint_mem⟩ →*
      FundamentalGroup A.actualVanKampenFourPieceCover.core
        ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩ :=
  (FundamentalGroup.fundamentalGroupMulEquivOfPath
      (A.actualVanKampenFourPieceCover.connectorInCore
        A.actualVanKampenFourPieceCover.ellipticFourConnector
        A.actualVanKampenFourPieceCover.ellipticFourConnector_mem
        A.actualVanKampenFourPieceCover.ellipticFourPoint_mem.1).symm).toMonoidHom.comp
    (FundamentalGroup.map
      (A.actualVanKampenFourPieceCover.overlapToCore
        A.actualVanKampenFourPieceCover.ellipticFour)
      ⟨A.actualVanKampenFourPieceCover.ellipticFourPoint,
        A.actualVanKampenFourPieceCover.ellipticFourPoint_mem⟩)

/-- The actual overlap-to-core map gives the order-three square of the affine star bridge. -/
public theorem actualEllipticThreeAffineBridge_square :
    A.actualVanKampenFourPieceCover.coreFundamentalGroupMap.comp
        A.actualEllipticThreeOverlapToCore =
      A.actualVanKampenFourPieceCover.ellipticThreeFundamentalGroupMap.comp
        A.actualVanKampenFourPieceCover.ellipticThreeOverlapFundamentalGroupMap := by
  ext γ
  exact coreSquare_apply A.actualVanKampenFourPieceCover
    A.actualVanKampenFourPieceCover.ellipticThree
    A.actualVanKampenFourPieceCover.ellipticThreePoint_mem
    A.actualVanKampenFourPieceCover.ellipticThreeConnector
    A.actualVanKampenFourPieceCover.ellipticThreeConnector_mem γ

/-- The actual overlap-to-core map gives the order-four square of the affine star bridge. -/
public theorem actualEllipticFourAffineBridge_square :
    A.actualVanKampenFourPieceCover.coreFundamentalGroupMap.comp
        A.actualEllipticFourOverlapToCore =
      A.actualVanKampenFourPieceCover.ellipticFourFundamentalGroupMap.comp
        A.actualVanKampenFourPieceCover.ellipticFourOverlapFundamentalGroupMap := by
  ext γ
  exact coreSquare_apply A.actualVanKampenFourPieceCover
    A.actualVanKampenFourPieceCover.ellipticFour
    A.actualVanKampenFourPieceCover.ellipticFourPoint_mem
    A.actualVanKampenFourPieceCover.ellipticFourConnector
    A.actualVanKampenFourPieceCover.ellipticFourConnector_mem γ
/-- The central affine presentation transported through a marked cusp naturality equivalence. -/
public noncomputable def coreDataOf (N : A.ActualCuspCentralNaturality) :
    AffineTorusCorePiOneData
      (FundamentalGroup A.actualVanKampenFourPieceCover.core
        ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩)
      Lattice paperMonodromyOne paperMonodromyTwo :=
  A.centralAffineCorePiOneData.mapSurjective N.centralToCore.toMonoidHom
    N.centralToCore.surjective

/-- Every marked cusp translation maps to the corresponding transported core translation. -/
public theorem cuspBridge_translation_core (N : A.ActualCuspCentralNaturality) (a : Lattice) :
    A.actualCuspOverlapToCore
        (Additive.toMul (A.actualCuspAffineBridgeTranslation a)) =
      Additive.toMul ((A.coreDataOf N).translation a) :=
  N.translation_core a

/-- At cusp twist zero, the marked cusp meridian maps to the product of the two core meridians. -/
public theorem cuspBridge_meridian_core (N : A.ActualCuspCentralNaturality) :
    A.actualCuspOverlapToCore A.actualCuspAffineBridgeMeridian =
      (A.coreDataOf N).rhoOne * (A.coreDataOf N).rhoTwo *
        (Additive.toMul ((A.coreDataOf N).translation 0))⁻¹ := by
  apply Eq.trans N.meridian_core
  change
    N.centralToCore A.centralAffineCorePiOneData.rhoOne *
      N.centralToCore A.centralAffineCorePiOneData.rhoTwo =
    N.centralToCore A.centralAffineCorePiOneData.rhoOne *
      N.centralToCore A.centralAffineCorePiOneData.rhoTwo *
      (N.centralToCore
        (Additive.toMul (A.centralAffineCorePiOneData.translation 0)))⁻¹
  have hz : Additive.toMul (A.centralAffineCorePiOneData.translation 0) = 1 := by
    rw [map_zero]
    rfl
  rw [hz, map_one, inv_one, mul_one]

/-- Marked peripheral naturality and chosen regular cover squares for the two actual elliptic
collars, relative to a marked cusp naturality equivalence `N`.

This is the exact elliptic counterpart of `ActualCuspCentralNaturality` together with the two
chosen cyclic filling-cover models.  Every remaining field of
`ActualAffineFillingCoverSquares` is derived from it and from the already established cusp
package. -/
public structure ActualEllipticCentralNaturality (N : A.ActualCuspCentralNaturality) where
  orderThreeCover : ChosenCyclicAffineFillingCoverModel 3 Lattice
    (A.actualVanKampenFourPieceCover.core ∩
      A.actualVanKampenFourPieceCover.ellipticThree : Set A.VanKampenSpace)
    A.actualVanKampenFourPieceCover.ellipticThree
  orderThreeBoundaryBase_eq : orderThreeCover.boundaryBase =
    ⟨A.actualVanKampenFourPieceCover.ellipticThreePoint,
      A.actualVanKampenFourPieceCover.ellipticThreePoint_mem⟩
  orderThreeFillingBase_eq : orderThreeCover.fillingBase =
    ⟨A.actualVanKampenFourPieceCover.ellipticThreePoint,
      A.actualVanKampenFourPieceCover.ellipticThreePoint_mem.2⟩
  orderThreeMap_eq : fundamentalGroupHomOfBaseEq
    orderThreeBoundaryBase_eq orderThreeFillingBase_eq
    orderThreeCover.fundamentalGroupMap =
    A.actualVanKampenFourPieceCover.ellipticThreeOverlapFundamentalGroupMap
  orderThreeTwist_eq : orderThreeCover.twist = epsilon
  orderThreeTranslation_naturality : ∀ a : Lattice,
    A.actualEllipticThreeOverlapToCore
        (Additive.toMul
          (fundamentalGroupAddHomOfBaseEq orderThreeBoundaryBase_eq
            orderThreeCover.translation a)) =
      N.centralToCore (Additive.toMul (A.centralAffineCorePiOneData.translation a))
  orderThreeMeridian_naturality :
    A.actualEllipticThreeOverlapToCore
        (fundamentalGroupElementOfBaseEq orderThreeBoundaryBase_eq
          orderThreeCover.meridian) =
      N.centralToCore A.centralAffineCorePiOneData.rhoOne
  orderFourCover : ChosenCyclicAffineFillingCoverModel 4 Lattice
    (A.actualVanKampenFourPieceCover.core ∩
      A.actualVanKampenFourPieceCover.ellipticFour : Set A.VanKampenSpace)
    A.actualVanKampenFourPieceCover.ellipticFour
  orderFourBoundaryBase_eq : orderFourCover.boundaryBase =
    ⟨A.actualVanKampenFourPieceCover.ellipticFourPoint,
      A.actualVanKampenFourPieceCover.ellipticFourPoint_mem⟩
  orderFourFillingBase_eq : orderFourCover.fillingBase =
    ⟨A.actualVanKampenFourPieceCover.ellipticFourPoint,
      A.actualVanKampenFourPieceCover.ellipticFourPoint_mem.2⟩
  orderFourMap_eq : fundamentalGroupHomOfBaseEq
    orderFourBoundaryBase_eq orderFourFillingBase_eq
    orderFourCover.fundamentalGroupMap =
    A.actualVanKampenFourPieceCover.ellipticFourOverlapFundamentalGroupMap
  orderFourTwist_eq : orderFourCover.twist = -epsilon'
  orderFourTranslation_naturality : ∀ a : Lattice,
    A.actualEllipticFourOverlapToCore
        (Additive.toMul
          (fundamentalGroupAddHomOfBaseEq orderFourBoundaryBase_eq
            orderFourCover.translation a)) =
      N.centralToCore (Additive.toMul (A.centralAffineCorePiOneData.translation a))
  orderFourMeridian_naturality :
    A.actualEllipticFourOverlapToCore
        (fundamentalGroupElementOfBaseEq orderFourBoundaryBase_eq
          orderFourCover.meridian) =
      N.centralToCore A.centralAffineCorePiOneData.rhoTwo

/-- Two additive homomorphisms out of the rank-four paper lattice agree when they agree on the
standard integral basis.  The codomain need not be commutative. -/
public theorem latticeAddHom_ext_integralBasis
    {G : Type*} [AddGroup G] (f g : Lattice →+ G)
    (h : ∀ i : Fin 4,
      f (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector i) =
        g (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector i)) :
    f = g := by
  ext a
  have ha : a =
      a 0 • SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 0 +
      a 1 • SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 1 +
      a 2 • SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 2 +
      a 3 • SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 3 := by
    ext i
    fin_cases i <;>
      simp [SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector, Pi.single]
  rw [ha]
  simp only [map_add, map_zsmul]
  rw [h 0, h 1, h 2, h 3]

/-- The order-three monodromy sends the second basis vector to the difference of the fourth and
third basis vectors. -/
public theorem paperMonodromyOne_integralBasisVector_one :
    paperMonodromyOne
        (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 1) =
      -SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 2 +
        SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 3 := by
  ext i
  fin_cases i <;>
    simp [paperMonodromyOne, A₁, dotProduct,
      SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector, Pi.single,
      Fin.sum_univ_succ]

/-- The order-four monodromy sends the second basis vector to the third. -/
public theorem paperMonodromyTwo_integralBasisVector_one :
    paperMonodromyTwo
        (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 1) =
      SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 2 := by
  ext i
  fin_cases i <;>
    simp [paperMonodromyTwo, A₂, dotProduct,
      SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector, Pi.single,
      Fin.sum_univ_succ]

/-- The order-four monodromy sends the third basis vector to the difference of the fourth and
second basis vectors. -/
public theorem paperMonodromyTwo_integralBasisVector_two :
    paperMonodromyTwo
        (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 2) =
      -SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 1 +
        SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 3 := by
  ext i
  fin_cases i <;>
    simp [paperMonodromyTwo, A₂, dotProduct,
      SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector, Pi.single,
      Fin.sum_univ_succ]

/-- Two lattice markings conjugated by the same meridian propagate equality along their common
monodromy. -/
public theorem latticeAddHom_eq_propagates_of_conjugates
    {Λ G : Type*} [AddCommGroup Λ] [Group G]
    (M : Λ →+ Λ) (f g : Λ →+ Additive G) (r : G)
    (hf : ∀ a, r * Additive.toMul (f a) * r⁻¹ = Additive.toMul (f (M a)))
    (hg : ∀ a, r * Additive.toMul (g a) * r⁻¹ = Additive.toMul (g (M a))) :
    ∀ a, f a = g a → f (M a) = g (M a) := by
  intro a h
  change Additive.toMul (f (M a)) = Additive.toMul (g (M a))
  rw [← hf, ← hg, h]

/-- For order three, monodromy propagation reduces equality of lattice maps to three marked
coordinates. -/
public theorem latticeAddHom_ext_orderThreeMonodromy
    {G : Type*} [AddGroup G] (f g : Lattice →+ G)
    (hmonodromy : ∀ a, f a = g a →
      f (paperMonodromyOne a) = g (paperMonodromyOne a))
    (hzero : f (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 0) =
      g (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 0))
    (hone : f (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 1) =
      g (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 1))
    (hthree : f (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 3) =
      g (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 3)) :
    f = g := by
  have hmonodromyOne := hmonodromy
    (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 1) hone
  rw [paperMonodromyOne_integralBasisVector_one, map_add, map_add, map_neg, map_neg]
    at hmonodromyOne
  rw [hthree] at hmonodromyOne
  have htwo : f (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 2) =
      g (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 2) := by
    exact neg_injective (add_right_cancel hmonodromyOne)
  apply latticeAddHom_ext_integralBasis
  intro i
  fin_cases i
  · exact hzero
  · exact hone
  · exact htwo
  · exact hthree

/-- For order four, monodromy propagation reduces equality of lattice maps to two marked
coordinates. -/
public theorem latticeAddHom_ext_orderFourMonodromy
    {G : Type*} [AddGroup G] (f g : Lattice →+ G)
    (hmonodromy : ∀ a, f a = g a →
      f (paperMonodromyTwo a) = g (paperMonodromyTwo a))
    (hzero : f (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 0) =
      g (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 0))
    (hone : f (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 1) =
      g (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 1)) :
    f = g := by
  have htwo : f (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 2) =
      g (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 2) := by
    rw [← paperMonodromyTwo_integralBasisVector_one]
    exact hmonodromy
      (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 1) hone
  have hmonodromyTwo := hmonodromy
    (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 2) htwo
  rw [paperMonodromyTwo_integralBasisVector_two, map_add, map_add, map_neg, map_neg]
    at hmonodromyTwo
  rw [hone] at hmonodromyTwo
  have hthree : f (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 3) =
      g (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 3) := by
    exact add_left_cancel hmonodromyTwo
  apply latticeAddHom_ext_integralBasis
  intro i
  fin_cases i
  · exact hzero
  · exact hone
  · exact htwo
  · exact hthree

/-- The order-three collar translations, transported to the central core. -/
public noncomputable def actualEllipticThreeTranslationToCore
    (D : ChosenCyclicAffineFillingCoverModel 3 Lattice
      (A.actualVanKampenFourPieceCover.core ∩
        A.actualVanKampenFourPieceCover.ellipticThree : Set A.VanKampenSpace)
      A.actualVanKampenFourPieceCover.ellipticThree)
    (hb : D.boundaryBase =
      ⟨A.actualVanKampenFourPieceCover.ellipticThreePoint,
        A.actualVanKampenFourPieceCover.ellipticThreePoint_mem⟩) :
    Lattice →+ Additive
      (FundamentalGroup A.actualVanKampenFourPieceCover.core
        ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩) :=
  A.actualEllipticThreeOverlapToCore.toAdditive.comp
    (fundamentalGroupAddHomOfBaseEq hb D.translation)

/-- The order-four collar translations, transported to the central core. -/
public noncomputable def actualEllipticFourTranslationToCore
    (D : ChosenCyclicAffineFillingCoverModel 4 Lattice
      (A.actualVanKampenFourPieceCover.core ∩
        A.actualVanKampenFourPieceCover.ellipticFour : Set A.VanKampenSpace)
      A.actualVanKampenFourPieceCover.ellipticFour)
    (hb : D.boundaryBase =
      ⟨A.actualVanKampenFourPieceCover.ellipticFourPoint,
        A.actualVanKampenFourPieceCover.ellipticFourPoint_mem⟩) :
    Lattice →+ Additive
      (FundamentalGroup A.actualVanKampenFourPieceCover.core
        ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩) :=
  A.actualEllipticFourOverlapToCore.toAdditive.comp
    (fundamentalGroupAddHomOfBaseEq hb D.translation)

/-- The central-family translations, transported to the central core. -/
public noncomputable def actualCentralTranslationToCore
    (N : A.ActualCuspCentralNaturality) :
    Lattice →+ Additive
      (FundamentalGroup A.actualVanKampenFourPieceCover.core
        ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩) :=
  N.centralToCore.toMonoidHom.toAdditive.comp A.centralAffineCorePiOneData.translation

/-- The first central meridian conjugates the transported central marking by the order-three
monodromy. -/
public theorem actualCentralRhoOne_conjugatesTranslationToCore
    (N : A.ActualCuspCentralNaturality) (a : Lattice) :
    N.centralToCore A.centralAffineCorePiOneData.rhoOne *
        Additive.toMul (A.actualCentralTranslationToCore N a) *
        (N.centralToCore A.centralAffineCorePiOneData.rhoOne)⁻¹ =
      Additive.toMul
        (A.actualCentralTranslationToCore N (paperMonodromyOne a)) :=
  (A.coreDataOf N).conjugate_one a

/-- The second central meridian conjugates the transported central marking by the order-four
monodromy. -/
public theorem actualCentralRhoTwo_conjugatesTranslationToCore
    (N : A.ActualCuspCentralNaturality) (a : Lattice) :
    N.centralToCore A.centralAffineCorePiOneData.rhoTwo *
        Additive.toMul (A.actualCentralTranslationToCore N a) *
        (N.centralToCore A.centralAffineCorePiOneData.rhoTwo)⁻¹ =
      Additive.toMul
        (A.actualCentralTranslationToCore N (paperMonodromyTwo a)) :=
  (A.coreDataOf N).conjugate_two a

/-- The transported order-three collar meridian conjugates its translations by the paper
monodromy whenever the selected deck monodromy has the corresponding inverse convention. -/
public theorem actualEllipticThreeMeridian_conjugatesTranslationToCore
    (D : ChosenCyclicAffineFillingCoverModel 3 Lattice
      (A.actualVanKampenFourPieceCover.core ∩
        A.actualVanKampenFourPieceCover.ellipticThree : Set A.VanKampenSpace)
      A.actualVanKampenFourPieceCover.ellipticThree)
    (hb : D.boundaryBase =
      ⟨A.actualVanKampenFourPieceCover.ellipticThreePoint,
        A.actualVanKampenFourPieceCover.ellipticThreePoint_mem⟩)
    (hinv : ∀ a, D.monodromy.toAdd (paperMonodromyOne a) = a) (a : Lattice) :
    A.actualEllipticThreeOverlapToCore
          (fundamentalGroupElementOfBaseEq hb D.meridian) *
        Additive.toMul (A.actualEllipticThreeTranslationToCore D hb a) *
        (A.actualEllipticThreeOverlapToCore
          (fundamentalGroupElementOfBaseEq hb D.meridian))⁻¹ =
      Additive.toMul
        (A.actualEllipticThreeTranslationToCore D hb (paperMonodromyOne a)) := by
  have h := D.meridian_conjugates_translation_of_rightInverse paperMonodromyOne hinv a
  have h' := congrArg
    (fun z ↦ A.actualEllipticThreeOverlapToCore
      (fundamentalGroupElementOfBaseEq hb z)) h
  simpa only [actualEllipticThreeTranslationToCore, AddMonoidHom.comp_apply,
    fundamentalGroupAddHomOfBaseEq_apply, MonoidHom.coe_toAdditive, Function.comp_apply,
    toMul_ofMul, fundamentalGroupElementOfBaseEq_mul, fundamentalGroupElementOfBaseEq_inv,
    map_mul, map_inv] using h'

/-- The transported order-four collar meridian conjugates its translations by the paper
monodromy whenever the selected deck monodromy has the corresponding inverse convention. -/
public theorem actualEllipticFourMeridian_conjugatesTranslationToCore
    (D : ChosenCyclicAffineFillingCoverModel 4 Lattice
      (A.actualVanKampenFourPieceCover.core ∩
        A.actualVanKampenFourPieceCover.ellipticFour : Set A.VanKampenSpace)
      A.actualVanKampenFourPieceCover.ellipticFour)
    (hb : D.boundaryBase =
      ⟨A.actualVanKampenFourPieceCover.ellipticFourPoint,
        A.actualVanKampenFourPieceCover.ellipticFourPoint_mem⟩)
    (hinv : ∀ a, D.monodromy.toAdd (paperMonodromyTwo a) = a) (a : Lattice) :
    A.actualEllipticFourOverlapToCore
          (fundamentalGroupElementOfBaseEq hb D.meridian) *
        Additive.toMul (A.actualEllipticFourTranslationToCore D hb a) *
        (A.actualEllipticFourOverlapToCore
          (fundamentalGroupElementOfBaseEq hb D.meridian))⁻¹ =
      Additive.toMul
        (A.actualEllipticFourTranslationToCore D hb (paperMonodromyTwo a)) := by
  have h := D.meridian_conjugates_translation_of_rightInverse paperMonodromyTwo hinv a
  have h' := congrArg
    (fun z ↦ A.actualEllipticFourOverlapToCore
      (fundamentalGroupElementOfBaseEq hb z)) h
  simpa only [actualEllipticFourTranslationToCore, AddMonoidHom.comp_apply,
    fundamentalGroupAddHomOfBaseEq_apply, MonoidHom.coe_toAdditive, Function.comp_apply,
    toMul_ofMul, fundamentalGroupElementOfBaseEq_mul, fundamentalGroupElementOfBaseEq_inv,
    map_mul, map_inv] using h'

/-- The exact elliptic cover geometry and a finite marking.

The cover monodromy is required to be inverse to the displayed paper monodromy, as dictated by
the opposite-deck-group convention.  Conjugation then propagates translation naturality from
three marked coordinates on the order-three side and two on the order-four side. -/
public structure ActualEllipticCentralBasisNaturality (N : A.ActualCuspCentralNaturality) where
  orderThreeCover : ChosenCyclicAffineFillingCoverModel 3 Lattice
    (A.actualVanKampenFourPieceCover.core ∩
      A.actualVanKampenFourPieceCover.ellipticThree : Set A.VanKampenSpace)
    A.actualVanKampenFourPieceCover.ellipticThree
  orderThreeBoundaryBase_eq : orderThreeCover.boundaryBase =
    ⟨A.actualVanKampenFourPieceCover.ellipticThreePoint,
      A.actualVanKampenFourPieceCover.ellipticThreePoint_mem⟩
  orderThreeFillingBase_eq : orderThreeCover.fillingBase =
    ⟨A.actualVanKampenFourPieceCover.ellipticThreePoint,
      A.actualVanKampenFourPieceCover.ellipticThreePoint_mem.2⟩
  orderThreeMap_eq : fundamentalGroupHomOfBaseEq
    orderThreeBoundaryBase_eq orderThreeFillingBase_eq
    orderThreeCover.fundamentalGroupMap =
    A.actualVanKampenFourPieceCover.ellipticThreeOverlapFundamentalGroupMap
  orderThreeTwist_eq : orderThreeCover.twist = epsilon
  orderThreeMonodromy_inverse : ∀ a,
    orderThreeCover.monodromy.toAdd (paperMonodromyOne a) = a
  orderThreeTranslation_zero :
    A.actualEllipticThreeTranslationToCore orderThreeCover orderThreeBoundaryBase_eq
        (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 0) =
      A.actualCentralTranslationToCore N
        (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 0)
  orderThreeTranslation_one :
    A.actualEllipticThreeTranslationToCore orderThreeCover orderThreeBoundaryBase_eq
        (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 1) =
      A.actualCentralTranslationToCore N
        (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 1)
  orderThreeTranslation_three :
    A.actualEllipticThreeTranslationToCore orderThreeCover orderThreeBoundaryBase_eq
        (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 3) =
      A.actualCentralTranslationToCore N
        (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 3)
  orderThreeMeridian_naturality :
    A.actualEllipticThreeOverlapToCore
        (fundamentalGroupElementOfBaseEq orderThreeBoundaryBase_eq
          orderThreeCover.meridian) =
      N.centralToCore A.centralAffineCorePiOneData.rhoOne
  orderFourCover : ChosenCyclicAffineFillingCoverModel 4 Lattice
    (A.actualVanKampenFourPieceCover.core ∩
      A.actualVanKampenFourPieceCover.ellipticFour : Set A.VanKampenSpace)
    A.actualVanKampenFourPieceCover.ellipticFour
  orderFourBoundaryBase_eq : orderFourCover.boundaryBase =
    ⟨A.actualVanKampenFourPieceCover.ellipticFourPoint,
      A.actualVanKampenFourPieceCover.ellipticFourPoint_mem⟩
  orderFourFillingBase_eq : orderFourCover.fillingBase =
    ⟨A.actualVanKampenFourPieceCover.ellipticFourPoint,
      A.actualVanKampenFourPieceCover.ellipticFourPoint_mem.2⟩
  orderFourMap_eq : fundamentalGroupHomOfBaseEq
    orderFourBoundaryBase_eq orderFourFillingBase_eq
    orderFourCover.fundamentalGroupMap =
    A.actualVanKampenFourPieceCover.ellipticFourOverlapFundamentalGroupMap
  orderFourTwist_eq : orderFourCover.twist = -epsilon'
  orderFourMonodromy_inverse : ∀ a,
    orderFourCover.monodromy.toAdd (paperMonodromyTwo a) = a
  orderFourTranslation_zero :
    A.actualEllipticFourTranslationToCore orderFourCover orderFourBoundaryBase_eq
        (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 0) =
      A.actualCentralTranslationToCore N
        (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 0)
  orderFourTranslation_one :
    A.actualEllipticFourTranslationToCore orderFourCover orderFourBoundaryBase_eq
        (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 1) =
      A.actualCentralTranslationToCore N
        (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 1)
  orderFourMeridian_naturality :
    A.actualEllipticFourOverlapToCore
        (fundamentalGroupElementOfBaseEq orderFourBoundaryBase_eq
          orderFourCover.meridian) =
      N.centralToCore A.centralAffineCorePiOneData.rhoTwo

namespace ActualEllipticCentralBasisNaturality

variable {A} {N : A.ActualCuspCentralNaturality}

/-- Extend the finite basis marking to every lattice translation. -/
public noncomputable def toActualEllipticCentralNaturality
    (E : ActualEllipticCentralBasisNaturality A N) :
    ActualEllipticCentralNaturality A N where
  orderThreeCover := E.orderThreeCover
  orderThreeBoundaryBase_eq := E.orderThreeBoundaryBase_eq
  orderThreeFillingBase_eq := E.orderThreeFillingBase_eq
  orderThreeMap_eq := E.orderThreeMap_eq
  orderThreeTwist_eq := E.orderThreeTwist_eq
  orderThreeTranslation_naturality := fun a ↦ by
    have hf : ∀ x,
        N.centralToCore A.centralAffineCorePiOneData.rhoOne *
            Additive.toMul
              (A.actualEllipticThreeTranslationToCore E.orderThreeCover
                E.orderThreeBoundaryBase_eq x) *
            (N.centralToCore A.centralAffineCorePiOneData.rhoOne)⁻¹ =
          Additive.toMul
            (A.actualEllipticThreeTranslationToCore E.orderThreeCover
              E.orderThreeBoundaryBase_eq (paperMonodromyOne x)) := by
      intro x
      rw [← E.orderThreeMeridian_naturality]
      exact A.actualEllipticThreeMeridian_conjugatesTranslationToCore E.orderThreeCover
        E.orderThreeBoundaryBase_eq E.orderThreeMonodromy_inverse x
    have hprop := latticeAddHom_eq_propagates_of_conjugates paperMonodromyOne
      (A.actualEllipticThreeTranslationToCore E.orderThreeCover
        E.orderThreeBoundaryBase_eq)
      (A.actualCentralTranslationToCore N)
      (N.centralToCore A.centralAffineCorePiOneData.rhoOne) hf
      (A.actualCentralRhoOne_conjugatesTranslationToCore N)
    have hmaps := latticeAddHom_ext_orderThreeMonodromy
      (A.actualEllipticThreeTranslationToCore E.orderThreeCover
        E.orderThreeBoundaryBase_eq)
      (A.actualCentralTranslationToCore N) hprop E.orderThreeTranslation_zero
      E.orderThreeTranslation_one E.orderThreeTranslation_three
    exact congrArg Additive.toMul (DFunLike.congr_fun hmaps a)
  orderThreeMeridian_naturality := E.orderThreeMeridian_naturality
  orderFourCover := E.orderFourCover
  orderFourBoundaryBase_eq := E.orderFourBoundaryBase_eq
  orderFourFillingBase_eq := E.orderFourFillingBase_eq
  orderFourMap_eq := E.orderFourMap_eq
  orderFourTwist_eq := E.orderFourTwist_eq
  orderFourTranslation_naturality := fun a ↦ by
    have hf : ∀ x,
        N.centralToCore A.centralAffineCorePiOneData.rhoTwo *
            Additive.toMul
              (A.actualEllipticFourTranslationToCore E.orderFourCover
                E.orderFourBoundaryBase_eq x) *
            (N.centralToCore A.centralAffineCorePiOneData.rhoTwo)⁻¹ =
          Additive.toMul
            (A.actualEllipticFourTranslationToCore E.orderFourCover
              E.orderFourBoundaryBase_eq (paperMonodromyTwo x)) := by
      intro x
      rw [← E.orderFourMeridian_naturality]
      exact A.actualEllipticFourMeridian_conjugatesTranslationToCore E.orderFourCover
        E.orderFourBoundaryBase_eq E.orderFourMonodromy_inverse x
    have hprop := latticeAddHom_eq_propagates_of_conjugates paperMonodromyTwo
      (A.actualEllipticFourTranslationToCore E.orderFourCover
        E.orderFourBoundaryBase_eq)
      (A.actualCentralTranslationToCore N)
      (N.centralToCore A.centralAffineCorePiOneData.rhoTwo) hf
      (A.actualCentralRhoTwo_conjugatesTranslationToCore N)
    have hmaps := latticeAddHom_ext_orderFourMonodromy
      (A.actualEllipticFourTranslationToCore E.orderFourCover
        E.orderFourBoundaryBase_eq)
      (A.actualCentralTranslationToCore N) hprop E.orderFourTranslation_zero
      E.orderFourTranslation_one
    exact congrArg Additive.toMul (DFunLike.congr_fun hmaps a)
  orderFourMeridian_naturality := E.orderFourMeridian_naturality

end ActualEllipticCentralBasisNaturality

namespace ActualEllipticCentralNaturality

variable {A} {N : A.ActualCuspCentralNaturality}

/-- The actual order-three collar inclusion is onto on fundamental groups. -/
public theorem orderThreeOverlapFundamentalGroupMap_surjective
    (E : ActualEllipticCentralNaturality A N) :
    Function.Surjective
      A.actualVanKampenFourPieceCover.ellipticThreeOverlapFundamentalGroupMap := by
  rw [← E.orderThreeMap_eq]
  exact fundamentalGroupHomOfBaseEq_surjective
    E.orderThreeBoundaryBase_eq E.orderThreeFillingBase_eq
    E.orderThreeCover.fundamentalGroupMap
    E.orderThreeCover.fundamentalGroupMap_surjective

/-- The actual order-four collar inclusion is onto on fundamental groups. -/
public theorem orderFourOverlapFundamentalGroupMap_surjective
    (E : ActualEllipticCentralNaturality A N) :
    Function.Surjective
      A.actualVanKampenFourPieceCover.ellipticFourOverlapFundamentalGroupMap := by
  rw [← E.orderFourMap_eq]
  exact fundamentalGroupHomOfBaseEq_surjective
    E.orderFourBoundaryBase_eq E.orderFourFillingBase_eq
    E.orderFourCover.fundamentalGroupMap
    E.orderFourCover.fundamentalGroupMap_surjective

/-- The order-three filling kills the marked cyclic affine relation at twist `epsilon`. -/
public theorem orderThreeRelation_killed (E : ActualEllipticCentralNaturality A N) :
    A.actualVanKampenFourPieceCover.ellipticThreeOverlapFundamentalGroupMap
        ((fundamentalGroupElementOfBaseEq E.orderThreeBoundaryBase_eq
            E.orderThreeCover.meridian) ^ 3 *
          (Additive.toMul
            (fundamentalGroupAddHomOfBaseEq E.orderThreeBoundaryBase_eq
              E.orderThreeCover.translation epsilon))⁻¹) = 1 := by
  rw [← E.orderThreeMap_eq]
  exact chosenCyclicRelation_killed E.orderThreeCover E.orderThreeBoundaryBase_eq
    E.orderThreeFillingBase_eq E.orderThreeTwist_eq

/-- The order-four filling kills the marked cyclic affine relation at twist `-epsilon'`. -/
public theorem orderFourRelation_killed (E : ActualEllipticCentralNaturality A N) :
    A.actualVanKampenFourPieceCover.ellipticFourOverlapFundamentalGroupMap
        ((fundamentalGroupElementOfBaseEq E.orderFourBoundaryBase_eq
            E.orderFourCover.meridian) ^ 4 *
          (Additive.toMul
            (fundamentalGroupAddHomOfBaseEq E.orderFourBoundaryBase_eq
              E.orderFourCover.translation (-epsilon')))⁻¹) = 1 := by
  rw [← E.orderFourMap_eq]
  exact chosenCyclicRelation_killed E.orderFourCover E.orderFourBoundaryBase_eq
    E.orderFourFillingBase_eq E.orderFourTwist_eq

/-- The complete based affine star filling bridge for the actual four-piece cover. -/
public noncomputable def bridge (E : ActualEllipticCentralNaturality A N) :
    AffineTorusStarFillingBridge A.actualVanKampenFourPieceCover
      (A.coreDataOf N) 3 4 epsilon (-epsilon') 0 paperToricSubgroup where
  cuspSurjective := A.actualCuspOverlapFundamentalGroupMap_surjective
  oneSurjective := E.orderThreeOverlapFundamentalGroupMap_surjective
  twoSurjective := E.orderFourOverlapFundamentalGroupMap_surjective
  cuspToCore := A.actualCuspOverlapToCore
  oneToCore := A.actualEllipticThreeOverlapToCore
  twoToCore := A.actualEllipticFourOverlapToCore
  cuspSquare := A.actualCuspAffineBridge_cuspSquare
  oneSquare := A.actualEllipticThreeAffineBridge_square
  twoSquare := A.actualEllipticFourAffineBridge_square
  cuspTranslation := A.actualCuspAffineBridgeTranslation
  cuspMeridian := A.actualCuspAffineBridgeMeridian
  cuspTranslation_core := A.cuspBridge_translation_core N
  cuspMeridian_core := A.cuspBridge_meridian_core N
  cuspMeridian_killed := A.actualCuspAffineBridge_meridian_killed
  cuspToric_killed := A.actualCuspAffineBridge_toric_killed
  oneTranslation := fundamentalGroupAddHomOfBaseEq E.orderThreeBoundaryBase_eq
    E.orderThreeCover.translation
  oneMeridian := fundamentalGroupElementOfBaseEq E.orderThreeBoundaryBase_eq
    E.orderThreeCover.meridian
  oneTranslation_core := E.orderThreeTranslation_naturality
  oneMeridian_core := E.orderThreeMeridian_naturality
  oneRelation_killed := E.orderThreeRelation_killed
  twoTranslation := fundamentalGroupAddHomOfBaseEq E.orderFourBoundaryBase_eq
    E.orderFourCover.translation
  twoMeridian := fundamentalGroupElementOfBaseEq E.orderFourBoundaryBase_eq
    E.orderFourCover.meridian
  twoTranslation_core := E.orderFourTranslation_naturality
  twoMeridian_core := E.orderFourMeridian_naturality
  twoRelation_killed := E.orderFourRelation_killed

/-- The three actual regular cover squares, assembled from the marked elliptic package and the
explicit cusp cover square. -/
public noncomputable def toActualAffineFillingCoverSquares
    (E : ActualEllipticCentralNaturality A N) :
    A.ActualAffineFillingCoverSquares where
  coreData := A.coreDataOf N
  centralToCore := N.centralToCore
  coreData_eq := rfl
  orderThreeCover := E.orderThreeCover
  orderThreeBoundaryBase_eq := E.orderThreeBoundaryBase_eq
  orderThreeFillingBase_eq := E.orderThreeFillingBase_eq
  orderThreeMap_eq := E.orderThreeMap_eq
  orderFourCover := E.orderFourCover
  orderFourBoundaryBase_eq := E.orderFourBoundaryBase_eq
  orderFourFillingBase_eq := E.orderFourFillingBase_eq
  orderFourMap_eq := E.orderFourMap_eq
  cuspCover := A.actualCuspChosenAffineFillingCover
  cuspBoundaryBase_eq := A.actualCuspChosenAffineFillingCover_boundaryBase_eq
  cuspFillingBase_eq := A.actualCuspChosenAffineFillingCover_fillingBase_eq
  cuspMap_eq := A.actualCuspChosenAffineFillingCover_map_eq
  bridge := E.bridge
  orderThreeTwist_eq := E.orderThreeTwist_eq
  orderThreeTranslation_eq := rfl
  orderThreeMeridian_eq := rfl
  orderFourTwist_eq := E.orderFourTwist_eq
  orderFourTranslation_eq := rfl
  orderFourMeridian_eq := rfl
  cuspTranslation_eq := rfl
  cuspMeridian_eq := rfl
  cuspVanishing_onto := A.actualCuspAffineBridge_vanishing_onto

end ActualEllipticCentralNaturality

/-- The two elliptic marked cover packages are the only missing inputs: together with any marked
cusp naturality they yield the full actual affine filling-cover square package. -/
public theorem nonempty_actualAffineFillingCoverSquares_of_ellipticNaturality
    (N : A.ActualCuspCentralNaturality) (E : ActualEllipticCentralNaturality A N) :
    Nonempty A.ActualAffineFillingCoverSquares :=
  ⟨E.toActualAffineFillingCoverSquares⟩

/-- Marked peripheral naturality for all three collars of the actual four-piece star.

The `cusp` field is the marked cusp naturality of `PaperCuspCentralNaturality`; the `elliptic`
field is its exact counterpart for the two elliptic collars, together with their chosen cyclic
regular-cover models. -/
public structure ActualStarPeripheralNaturality where
  cusp : A.ActualCuspCentralNaturality
  elliptic : ActualEllipticCentralNaturality A cusp

/-- Marked peripheral naturality and regular cover squares for the three actual collars.

This replaces the former `establishedActualAffineFillingCoverSquares`, which is now the theorem of
the same name.

## Why the two naturalities are bundled

Stated separately, the cusp and elliptic inputs are the more symmetric presentation: one
peripheral-naturality input per singularity type of the star. They are bundled here because
`establishedActualCuspCentralNaturality` is not otherwise reachable from the closure roots of the
construction, so splitting them would add one axiom to the transitive closure of the main theorem
without changing the mathematics assumed. That standalone cusp axiom remains available and
unchanged, and `ActualStarPeripheralNaturality.cusp` is exactly its content, for anyone who later
prefers the symmetric two-axiom presentation at that cost.

## What is assumed, and why in this form

The content behind the removed boundary was, after unwinding the algebraic adapter, exactly that
`π₁` of the glued four-piece star is trivial, obtained from the paper's peripheral presentation of
the punctured central family. Everything in that package which is formal has been discharged: the
cusp square and the whole cusp half of the affine bridge (`PaperCuspChosenAffineFilling`,
`PaperCuspAffineFillingBridge`), the two elliptic based gluing squares
(`actualEllipticThreeAffineBridge_square`, `actualEllipticFourAffineBridge_square`), the two
transported cyclic filling relations (`chosenCyclicRelation_killed`), and the final assembly
(`nonempty_actualAffineFillingCoverSquares_of_ellipticNaturality`). What is left is the elliptic
geometry, and only that.

Two components are bundled here.

* The two `ChosenCyclicAffineFillingCoverModel`s, for `m = 3` at twist `epsilon` and for `m = 4`
  at twist `-epsilon'`: a simply connected quotient covering of the elliptic collar, one of the
  elliptic filling, an equivariant lift, and the deck presentation
  `deckMap_kernel = normalClosure {meridian ^ m * translation twist⁻¹}`. The corresponding cusp
  construction is the five-module chain `PaperCuspBoundaryUniversalCover` →
  `PaperCuspFillingDeckAction` → `PaperCuspUnwrappedFillingCover` →
  `PaperCuspActualAffineFillingCoverSquare` → `PaperCuspChosenAffineFilling`; no elliptic
  counterpart of it exists yet.
* The opposite-deck convention identifies each selected deck monodromy as the inverse of the
  corresponding paper monodromy.  Meridian conjugation then reduces translation naturality to
  three marked lattice coordinates on the order-three collar and two on the order-four collar;
  the two meridians are identified with `rhoOne` and `rhoTwo`.  The complete infinite families
  are theorems above.

## Raw material that already exists, and what is missing

On the filling side: `orderThreeFillingCoverSource_simplyConnected` and
`orderFourFillingCoverSource_simplyConnected`, together with
`orderThreeActualFillingCoverProjection_surjective` and
`orderFourActualFillingCoverProjection_surjective`, and `EllipticFilling`'s
`quotient_isQuotientCoveringMap` with the freeness inputs `epsilon_action_free` and
`neg_epsilonPrime_action_free`. On the collar side: `orderThreeCollarRadialMappingTorusHomeomorph`
and `orderFourCollarRadialMappingTorusHomeomorph`. What is missing is the universal cover of the
collar, i.e. of `OpenRadialInterval r × CircleMappingTorus (orderThreeAffineClutchingHomeomorph …)`,
and the identification of its deck group with the semidirect product.

The canonical punctured-family presentation now identifies the central translations and
meridians, but it does not construct the two elliptic collar universal covers or compare their
deck markings with the corresponding central peripheral loops.  Those two geometric comparison
packages are precisely what remains here. -/
public axiom establishedActualEllipticCentralBasisNaturality :
    Nonempty (ActualEllipticCentralBasisNaturality A A.actualCuspCentralNaturality)

/-- The full elliptic naturality package, extended from finite monodromy-orbit anchors. -/
public theorem establishedActualEllipticCentralNaturality :
    Nonempty (ActualEllipticCentralNaturality A A.actualCuspCentralNaturality) :=
  A.establishedActualEllipticCentralBasisNaturality.map
    ActualEllipticCentralBasisNaturality.toActualEllipticCentralNaturality

/-- Marked peripheral naturality for all three actual collars.  The cusp half is now proved
(`actualCuspCentralNaturality`), so only the elliptic half remains assumed. -/
public theorem establishedActualStarPeripheralNaturality :
    Nonempty A.ActualStarPeripheralNaturality :=
  A.establishedActualEllipticCentralNaturality.elim fun E ↦
    ⟨{ cusp := A.actualCuspCentralNaturality, elliptic := E }⟩

/-- The three actual regular cover squares exist, given the star's peripheral naturality. -/
public theorem nonempty_actualAffineFillingCoverSquares :
    Nonempty A.ActualAffineFillingCoverSquares :=
  A.establishedActualStarPeripheralNaturality.elim fun P ↦
    nonempty_actualAffineFillingCoverSquares_of_ellipticNaturality A P.cusp P.elliptic

end SphereSixComplex.Geometry.PaperAnalyticData

end
