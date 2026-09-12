module

public import SphereSixComplex.Prerequisites.Topology.FirstHurewiczProof

/-!
# The first Hurewicz theorem

This module exposes the chain-level proof of the classical first Hurewicz theorem in its standard
natural form and develops the quotient-cover consequences used downstream.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology
open scoped ContinuousMap

namespace SphereSixComplex.Hurewicz


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


/-- The classical first Hurewicz theorem in degree one. -/
public def abelianizationComparison
    (X : Type) [TopologicalSpace X] (b : X) [PathConnectedSpace X] :
    AbelianizationComparison X b :=
  Chains.abelianizationComparison X b

/-- The abelianized deck-to-fundamental-group equivalence obtained from quotient-cover monodromy.
Mathlib's monodromy convention produces the opposite deck group; the opposite convention is
removed only after abelianization, preserving marked generator orientation. -/
public def abelianizationEquivOfPi1Opposite
    {X G : Type} [TopologicalSpace X] [PathConnectedSpace X] [Group G] (b : X)
    (e : FundamentalGroup X b ≃* Gᵐᵒᵖ) :
    Additive (Abelianization G) ≃ₗ[ℤ] AbelianPi1 X b :=
  ((e.abelianizationCongr.trans
      (abelianizationMulOppositeEquiv G)).symm.toAdditive.toIntLinearEquiv)

/-- First homology obtained from a quotient-cover monodromy equivalence. -/
public def homologyOneEquivOfPi1Opposite
    {X G : Type} [TopologicalSpace X] [PathConnectedSpace X] [Group G] (b : X)
    (e : FundamentalGroup X b ≃* Gᵐᵒᵖ) :
    Additive (Abelianization G) ≃ₗ[ℤ] IntegralSingularHomology 1 X :=
  (abelianizationEquivOfPi1Opposite b e).trans
    (abelianizationComparison X b).equiv

/-- A marked deck transformation represented by a loop maps to that loop's integral homology
class under the quotient-cover first-Hurewicz equivalence. -/
public theorem homologyOneEquivOfPi1Opposite_apply_loop
    {X G Λ : Type} [TopologicalSpace X] [PathConnectedSpace X] [Group G] (b : X)
    (e : FundamentalGroup X b ≃* Gᵐᵒᵖ) (deck : Λ → G)
    (loop : Λ → Path b b)
    (hmark : ∀ a, e (Path.Homotopic.Quotient.mk (loop a)) = MulOpposite.op (deck a))
    (a : Λ) :
    homologyOneEquivOfPi1Opposite b e
        (Additive.ofMul (Abelianization.of (deck a))) =
      StandardCircleHomologyLiftDegree.loopHomologyClass (loop a) := by
  rw [homologyOneEquivOfPi1Opposite]
  rw [LinearEquiv.trans_apply]
  have hloop :
      abelianizationEquivOfPi1Opposite b e
          (Additive.ofMul (Abelianization.of (deck a))) = loopClass (loop a) := by
    apply (abelianizationEquivOfPi1Opposite b e).symm.injective
    simp [abelianizationEquivOfPi1Opposite, loopClass, hmark,
      abelianizationCongr_symm]
    change e.abelianizationCongr
      (e.abelianizationCongr.symm (Abelianization.of (MulOpposite.op (deck a)))) = _
    exact e.abelianizationCongr.apply_symm_apply _
  rw [hloop, (abelianizationComparison X b).equiv_loopClass]

/-- The marked form of the quotient-cover first-Hurewicz comparison with a prescribed target
homology class. -/
public theorem homologyOneEquivOfPi1Opposite_apply_marked
    {X G Λ : Type} [TopologicalSpace X] [PathConnectedSpace X] [Group G] (b : X)
    (e : FundamentalGroup X b ≃* Gᵐᵒᵖ) (deck : Λ → G)
    (loop : Λ → Path b b)
    (target : Λ → IntegralSingularHomology 1 X)
    (hmark : ∀ a, e (Path.Homotopic.Quotient.mk (loop a)) = MulOpposite.op (deck a))
    (hhomology : ∀ a, StandardCircleHomologyLiftDegree.loopHomologyClass (loop a) = target a)
    (a : Λ) :
    homologyOneEquivOfPi1Opposite b e
        (Additive.ofMul (Abelianization.of (deck a))) = target a := by
  rw [homologyOneEquivOfPi1Opposite_apply_loop b e deck loop hmark,
    hhomology]


end SphereSixComplex.Hurewicz
