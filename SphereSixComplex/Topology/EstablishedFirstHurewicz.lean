module

public import SphereSixComplex.Topology.FirstHurewiczProof

/-!
# The first Hurewicz theorem

This module exposes the chain-level proof of the classical first Hurewicz theorem in its standard
natural form and develops the quotient-cover consequences used downstream.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology
open scoped ContinuousMap

namespace SphereSixComplex.Topology.EstablishedFirstHurewicz

/-- The map on abelianized fundamental groups induced by a continuous map. -/
public def abelianPi1Map {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (b : X) : AbelianPi1 X b →ₗ[ℤ] AbelianPi1 Y (f b) :=
  AddMonoidHom.toIntLinearMap
    (Abelianization.map (FundamentalGroup.map f b)).toAdditive

/-- The antihomomorphism `unop` becomes a homomorphism after mapping to an abelian group. -/
public def oppositeToAbelianizationHom (G : Type) [Group G] :
    Gᵐᵒᵖ →* Abelianization G where
  toFun g := Abelianization.of g.unop
  map_one' := rfl
  map_mul' g h := by
    change Abelianization.of (h.unop * g.unop) =
      Abelianization.of g.unop * Abelianization.of h.unop
    rw [map_mul, mul_comm]

/-- The antihomomorphism `op` becomes a homomorphism after mapping to an abelian group. -/
public def toOppositeAbelianizationHom (G : Type) [Group G] :
    G →* Abelianization Gᵐᵒᵖ where
  toFun g := Abelianization.of (MulOpposite.op g)
  map_one' := rfl
  map_mul' g h := by
    rw [MulOpposite.op_mul, map_mul, mul_comm]

/-- Abelianization canonically removes an opposite-group convention without reversing the
represented generator. -/
public def abelianizationMulOppositeEquiv (G : Type) [Group G] :
    Abelianization Gᵐᵒᵖ ≃* Abelianization G where
  toFun := Abelianization.lift (oppositeToAbelianizationHom G)
  invFun := Abelianization.lift (toOppositeAbelianizationHom G)
  left_inv := by
    rintro ⟨g⟩
    rfl
  right_inv := by
    rintro ⟨g⟩
    rfl
  map_mul' := map_mul _

@[simp]
public theorem abelianizationMulOppositeEquiv_of_op {G : Type} [Group G] (g : G) :
    abelianizationMulOppositeEquiv G
        (Abelianization.of (MulOpposite.op g)) = Abelianization.of g :=
  rfl

@[simp]
public theorem abelianizationMulOppositeEquiv_symm_of {G : Type} [Group G] (g : G) :
    (abelianizationMulOppositeEquiv G).symm (Abelianization.of g) =
      Abelianization.of (MulOpposite.op g) := by
  apply (abelianizationMulOppositeEquiv G).injective
  simp

/-- The integer-linear additive form of `abelianizationMulOppositeEquiv`. -/
public def additiveAbelianizationMulOppositeEquiv (G : Type) [Group G] :
    Additive (Abelianization Gᵐᵒᵖ) ≃ₗ[ℤ] Additive (Abelianization G) :=
  (abelianizationMulOppositeEquiv G).toAdditive.toIntLinearEquiv

@[simp]
public theorem additiveAbelianizationMulOppositeEquiv_of_op
    {G : Type} [Group G] (g : G) :
    additiveAbelianizationMulOppositeEquiv G
        (Additive.ofMul (Abelianization.of (MulOpposite.op g))) =
      Additive.ofMul (Abelianization.of g) :=
  by
    rfl

/-- The classical first Hurewicz theorem in degree one. -/
public def establishedFirstHurewiczData
    (X : Type) [TopologicalSpace X] (b : X) [PathConnectedSpace X] :
    FirstHurewiczData X b :=
  FirstHurewiczProof.establishedFirstHurewiczData_proof X b

/-- The abelianized deck-to-fundamental-group equivalence obtained from quotient-cover monodromy.
Mathlib's monodromy convention produces the opposite deck group; the opposite convention is
removed only after abelianization, preserving marked generator orientation. -/
public def deckAbelianPi1EquivOfFundamentalGroupEquivOpposite
    {X G : Type} [TopologicalSpace X] [PathConnectedSpace X] [Group G] (b : X)
    (e : FundamentalGroup X b ≃* Gᵐᵒᵖ) :
    Additive (Abelianization G) ≃ₗ[ℤ] AbelianPi1 X b :=
  ((e.abelianizationCongr.trans
      (abelianizationMulOppositeEquiv G)).symm.toAdditive.toIntLinearEquiv)

/-- First homology obtained from a quotient-cover monodromy equivalence. -/
public def deckHOneEquivOfFundamentalGroupEquivOpposite
    {X G : Type} [TopologicalSpace X] [PathConnectedSpace X] [Group G] (b : X)
    (e : FundamentalGroup X b ≃* Gᵐᵒᵖ) :
    Additive (Abelianization G) ≃ₗ[ℤ] IntegralSingularHomology 1 X :=
  (deckAbelianPi1EquivOfFundamentalGroupEquivOpposite b e).trans
    (establishedFirstHurewiczData X b).equiv

/-- A marked deck transformation represented by a loop maps to that loop's integral homology
class under the quotient-cover first-Hurewicz equivalence. -/
public theorem deckHOneEquivOfFundamentalGroupEquivOpposite_markedLoop
    {X G Λ : Type} [TopologicalSpace X] [PathConnectedSpace X] [Group G] (b : X)
    (e : FundamentalGroup X b ≃* Gᵐᵒᵖ) (deck : Λ → G)
    (loop : Λ → Path b b)
    (hmark : ∀ a, e (Path.Homotopic.Quotient.mk (loop a)) = MulOpposite.op (deck a))
    (a : Λ) :
    deckHOneEquivOfFundamentalGroupEquivOpposite b e
        (Additive.ofMul (Abelianization.of (deck a))) =
      StandardCircleHomologyLiftDegree.loopHomologyClass (loop a) := by
  rw [deckHOneEquivOfFundamentalGroupEquivOpposite]
  rw [LinearEquiv.trans_apply]
  have hloop :
      deckAbelianPi1EquivOfFundamentalGroupEquivOpposite b e
          (Additive.ofMul (Abelianization.of (deck a))) = loopClass (loop a) := by
    apply (deckAbelianPi1EquivOfFundamentalGroupEquivOpposite b e).symm.injective
    simp [deckAbelianPi1EquivOfFundamentalGroupEquivOpposite, loopClass, hmark,
      abelianizationCongr_symm]
  rw [hloop, (establishedFirstHurewiczData X b).equiv_loopClass]

/-- The marked form of the quotient-cover first-Hurewicz comparison with a prescribed target
homology class. -/
public theorem deckHOneEquivOfFundamentalGroupEquivOpposite_marked
    {X G Λ : Type} [TopologicalSpace X] [PathConnectedSpace X] [Group G] (b : X)
    (e : FundamentalGroup X b ≃* Gᵐᵒᵖ) (deck : Λ → G)
    (loop : Λ → Path b b)
    (target : Λ → IntegralSingularHomology 1 X)
    (hmark : ∀ a, e (Path.Homotopic.Quotient.mk (loop a)) = MulOpposite.op (deck a))
    (hhomology : ∀ a, StandardCircleHomologyLiftDegree.loopHomologyClass (loop a) = target a)
    (a : Λ) :
    deckHOneEquivOfFundamentalGroupEquivOpposite b e
        (Additive.ofMul (Abelianization.of (deck a))) = target a := by
  rw [deckHOneEquivOfFundamentalGroupEquivOpposite_markedLoop b e deck loop hmark,
    hhomology]

@[simp]
public theorem abelianPi1Map_loopClass {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) {b : X} (p : Path b b) :
    abelianPi1Map f b (loopClass p) = loopClass (p.map f.continuous) := by
  rfl

/-- Naturality of the first Hurewicz equivalence. -/
public theorem establishedFirstHurewiczData_naturality
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [PathConnectedSpace X] [PathConnectedSpace Y] (f : C(X, Y)) (b : X)
    (a : AbelianPi1 X b) :
    (establishedFirstHurewiczData Y (f b)).equiv (abelianPi1Map f b a) =
      integralSingularHomologyMap 1 f
        ((establishedFirstHurewiczData X b).equiv a) := by
  obtain ⟨p, rfl⟩ := loopClass_surjective a
  rw [abelianPi1Map_loopClass]
  rw [(establishedFirstHurewiczData Y (f b)).equiv_loopClass]
  rw [(establishedFirstHurewiczData X b).equiv_loopClass]
  exact
    (StandardCircleHomologyLiftDegree.integralSingularHomologyMap_loopHomologyClass f p).symm

end SphereSixComplex.Topology.EstablishedFirstHurewicz
