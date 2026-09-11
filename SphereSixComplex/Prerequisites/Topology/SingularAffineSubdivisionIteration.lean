module

public import SphereSixComplex.Prerequisites.Topology.SingularAffineSubdivisionSmallPrism

/-!
# Iterated affine subdivision on singular chains

This file packages finite iterates of geometric affine subdivision on full and cover-small
singular chains.  Every iterate is chain homotopic to the identity, and the small/full iterates
commute with the canonical inclusion.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory

namespace SphereSixComplex

/-- Finite iteration of affine subdivision on all integral singular chains. -/
public noncomputable def affineSingularSubdivisionIterate (X : TopCat.{0}) :
    ℕ → ((TopCat.toSSet.obj X).chainComplex (AddCommGrpCat.of ℤ) ⟶
      (TopCat.toSSet.obj X).chainComplex (AddCommGrpCat.of ℤ))
  | 0 => 𝟙 _
  | m + 1 => affineSingularSubdivisionIterate X m ≫
      affineSingularSubdivisionChainMap X

@[simp]
public theorem affineSingularSubdivisionIterate_zero (X : TopCat.{0}) :
    affineSingularSubdivisionIterate X 0 = 𝟙 _ :=
  rfl

public theorem affineSingularSubdivisionIterate_succ
    (X : TopCat.{0}) (m : ℕ) :
    affineSingularSubdivisionIterate X (m + 1) =
      affineSingularSubdivisionIterate X m ≫
        affineSingularSubdivisionChainMap X :=
  rfl


/-- Every finite affine-subdivision iterate is chain homotopic to the identity. -/
public noncomputable def affineSingularSubdivisionIterateHomotopy
    (X : TopCat.{0}) : ∀ m : ℕ,
    Homotopy (affineSingularSubdivisionIterate X m)
      (𝟙 ((TopCat.toSSet.obj X).chainComplex (AddCommGrpCat.of ℤ)))
  | 0 => Homotopy.refl _
  | m + 1 => by
      simpa [affineSingularSubdivisionIterate_succ] using
        (affineSingularSubdivisionIterateHomotopy X m).comp
          (affineSingularSubdivisionHomotopy X)


section Small

variable {iota : Type} (X : TopCat) (U : iota → Set X)

/-- Finite iteration of affine subdivision on cover-small chains. -/
public noncomputable def coverSmallAffineSubdivisionIterate :
    ℕ → (coverSmallIntegralSingularChainComplex X U ⟶
      coverSmallIntegralSingularChainComplex X U)
  | 0 => 𝟙 _
  | m + 1 => coverSmallAffineSubdivisionIterate m ≫
      coverSmallAffineSubdivisionChainMap X U


public theorem coverSmallAffineSubdivisionIterate_succ (m : ℕ) :
    coverSmallAffineSubdivisionIterate X U (m + 1) =
      coverSmallAffineSubdivisionIterate X U m ≫
        coverSmallAffineSubdivisionChainMap X U :=
  rfl

/-- Every cover-small affine-subdivision iterate is chain homotopic to the identity. -/
public noncomputable def coverSmallAffineSubdivisionIterateHomotopy :
    ∀ m : ℕ, Homotopy (coverSmallAffineSubdivisionIterate X U m)
      (𝟙 (coverSmallIntegralSingularChainComplex X U))
  | 0 => Homotopy.refl _
  | m + 1 => by
      simpa [coverSmallAffineSubdivisionIterate_succ] using
        (coverSmallAffineSubdivisionIterateHomotopy m).comp
          (coverSmallAffineSubdivisionHomotopy X U)


/-- Small and full affine-subdivision iterates commute with the small-chain inclusion. -/
public theorem coverSmallAffineSubdivisionIterate_comp_inclusion : ∀ m : ℕ,
    coverSmallAffineSubdivisionIterate X U m ≫
        coverSmallIntegralSingularChainInclusion X U =
      coverSmallIntegralSingularChainInclusion X U ≫
        affineSingularSubdivisionIterate X m
  | 0 => by
      change (SSet.chainComplexMap (coverSmallSingularSubcomplex X U).ι
        (AddCommGrpCat.of ℤ)) =
        SSet.chainComplexMap (coverSmallSingularSubcomplex X U).ι
          (AddCommGrpCat.of ℤ) ≫ 𝟙 _
      simp
  | m + 1 => by
      let I := SSet.chainComplexMap (coverSmallSingularSubcomplex X U).ι
        (AddCommGrpCat.of ℤ)
      have hm := coverSmallAffineSubdivisionIterate_comp_inclusion m
      change coverSmallAffineSubdivisionIterate X U m ≫ I =
        I ≫ affineSingularSubdivisionIterate X m at hm
      have hA := coverSmallAffineSubdivisionChainMap_comp_inclusion X U
      change coverSmallAffineSubdivisionChainMap X U ≫ I =
        I ≫ affineSingularSubdivisionChainMap X at hA
      rw [coverSmallAffineSubdivisionIterate_succ,
        affineSingularSubdivisionIterate_succ]
      change (coverSmallAffineSubdivisionIterate X U m ≫
          coverSmallAffineSubdivisionChainMap X U) ≫ I =
        I ≫ (affineSingularSubdivisionIterate X m ≫
          affineSingularSubdivisionChainMap X)
      rw [Category.assoc, hA, ← Category.assoc, hm, Category.assoc]

end Small

end SphereSixComplex
