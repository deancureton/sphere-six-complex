module

public import SphereSixComplex.Prerequisites.Topology.CyclicCoinvariantPresentation
public import SphereSixComplex.Paper.Topology.TwistObstruction

/-!
# Integral algebra for the two multiple fibres

This module formalizes the lattice and abelian-group calculations in Lemma 7.13.  It makes no
identification with the homology of a topological space.
-/

@[expose] public section

noncomputable section

open Matrix

namespace SphereSixComplex.MultipleFiberCoinvariants

open LatticeData
open SphereSixComplex.Topology.TwistObstruction

public abbrev IntSquared := Fin 2 → ℤ

@[simp]
public theorem gamma_apply (x : LatticeData.Lattice) : gamma x = x 0 := by
  rfl



public theorem vOne_eq_explicit : v₁ = ![1, 2, -4, 0] := by
  rfl

public theorem vTwo_eq_explicit : v₂ = ![-1, -3, 3, 0] := by
  funext i
  fin_cases i <;> norm_num [v₂, epsilon']

/-- The integral endomorphism `A₁ - I` on the dual lattice. -/
public def orderThreeDifference : Lattice →ₗ[ℤ] Lattice :=
  A₁.mulVecLin - LinearMap.id

/-- The integral endomorphism `A₂ - I` on the dual lattice. -/
public def orderFourDifference : Lattice →ₗ[ℤ] Lattice :=
  A₂.mulVecLin - LinearMap.id

@[simp]
public theorem orderThreeDifference_apply (x : Lattice) :
    orderThreeDifference x = A₁ *ᵥ x - x := by
  rfl

@[simp]
public theorem orderFourDifference_apply (x : Lattice) :
    orderFourDifference x = A₂ *ᵥ x - x := by
  rfl

/-- The second quotient coordinate for the order-three monodromy. -/
public def psiOne : Lattice →ₗ[ℤ] ℤ where
  toFun x := 2 * x 1 + x 2 + 3 * x 3
  map_add' x y := by simp; ring
  map_smul' n x := by simp; ring

/-- The second quotient coordinate for the order-four monodromy. -/
public def psiTwo : Lattice →ₗ[ℤ] ℤ where
  toFun x := x 1 + x 2 + 2 * x 3
  map_add' x y := by simp; ring
  map_smul' n x := by simp; ring

/-- The two quotient coordinates `(gamma, psiOne)`. -/
public def orderThreeCoordinates : Lattice →ₗ[ℤ] IntSquared where
  toFun x := ![gamma x, psiOne x]
  map_add' x y := by
    funext i
    fin_cases i <;> simp
  map_smul' n x := by
    funext i
    fin_cases i
    · change gamma (n • x) = n • gamma x
      exact gamma.map_smul n x
    · change psiOne (n • x) = n • psiOne x
      exact psiOne.map_smul n x

/-- The two quotient coordinates `(gamma, psiTwo)`. -/
public def orderFourCoordinates : Lattice →ₗ[ℤ] IntSquared where
  toFun x := ![gamma x, psiTwo x]
  map_add' x y := by
    funext i
    fin_cases i <;> simp
  map_smul' n x := by
    funext i
    fin_cases i
    · change gamma (n • x) = n • gamma x
      exact gamma.map_smul n x
    · change psiTwo (n • x) = n • psiTwo x
      exact psiTwo.map_smul n x

/-- Explicit description of the image of `A₁ - I`. -/
public theorem range_orderThreeDifference :
    LinearMap.range orderThreeDifference =
      {x : Lattice | x 0 = 0 ∧ 2 * x 1 + x 2 + 3 * x 3 = 0} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    constructor
    · simp [orderThreeDifference, A₁, dotProduct,
        Fin.sum_univ_succ]
    · simp [orderThreeDifference, A₁, dotProduct,
        Fin.sum_univ_succ]
      ring
  · rintro ⟨h0, hpsi⟩
    refine ⟨![0, x 3, x 1 + x 3, 0], ?_⟩
    funext i
    fin_cases i <;> simp [orderThreeDifference, A₁, h0]
    all_goals omega

/-- Explicit description of the image of `A₂ - I`. -/
public theorem range_orderFourDifference :
    LinearMap.range orderFourDifference =
      {x : Lattice | x 0 = 0 ∧ x 1 + x 2 + 2 * x 3 = 0} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    constructor
    · simp [orderFourDifference, A₂, dotProduct,
        Fin.sum_univ_succ]
    · simp [orderFourDifference, A₂, dotProduct,
        Fin.sum_univ_succ]
      ring
  · rintro ⟨h0, hpsi⟩
    refine ⟨![0, -x 1 - x 3, x 3, 0], ?_⟩
    funext i
    fin_cases i <;> simp [orderFourDifference, A₂, h0]
    all_goals omega

public theorem ker_orderThreeCoordinates :
    LinearMap.ker orderThreeCoordinates = LinearMap.range orderThreeDifference := by
  ext x
  constructor
  · intro hx
    have h := LinearMap.mem_ker.mp hx
    have h0 := congrFun h (0 : Fin 2)
    have h1 := congrFun h (1 : Fin 2)
    change x ∈ (↑(LinearMap.range orderThreeDifference) : Set Lattice)
    rw [range_orderThreeDifference]
    simpa [orderThreeCoordinates, psiOne] using And.intro h0 h1
  · intro hx
    have hx' : x ∈ (↑(LinearMap.range orderThreeDifference) : Set Lattice) := hx
    rw [range_orderThreeDifference] at hx'
    apply LinearMap.mem_ker.mpr
    funext i
    fin_cases i <;> simp [orderThreeCoordinates, psiOne, hx'.1, hx'.2]

public theorem ker_orderFourCoordinates :
    LinearMap.ker orderFourCoordinates = LinearMap.range orderFourDifference := by
  ext x
  constructor
  · intro hx
    have h := LinearMap.mem_ker.mp hx
    have h0 := congrFun h (0 : Fin 2)
    have h1 := congrFun h (1 : Fin 2)
    change x ∈ (↑(LinearMap.range orderFourDifference) : Set Lattice)
    rw [range_orderFourDifference]
    simpa [orderFourCoordinates, psiTwo] using And.intro h0 h1
  · intro hx
    have hx' : x ∈ (↑(LinearMap.range orderFourDifference) : Set Lattice) := hx
    rw [range_orderFourDifference] at hx'
    apply LinearMap.mem_ker.mpr
    funext i
    fin_cases i <;> simp [orderFourCoordinates, psiTwo, hx'.1, hx'.2]

public theorem surjective_orderThreeCoordinates :
    Function.Surjective orderThreeCoordinates := by
  intro y
  refine ⟨![y 0, 0, y 1, 0], ?_⟩
  funext i
  fin_cases i <;> simp [orderThreeCoordinates, psiOne]

public theorem surjective_orderFourCoordinates :
    Function.Surjective orderFourCoordinates := by
  intro y
  refine ⟨![y 0, 0, y 1, 0], ?_⟩
  funext i
  fin_cases i <;> simp [orderFourCoordinates, psiTwo]

public abbrev OrderThreeCoinvariants :=
  LatticeData.Lattice ⧸ LinearMap.range orderThreeDifference

public abbrev OrderFourCoinvariants :=
  LatticeData.Lattice ⧸ LinearMap.range orderFourDifference

/-- The order-three coinvariants, in the basis `(gamma, psiOne)`. -/
public noncomputable def orderThreeCoinvariantsEquivIntSquared :
    OrderThreeCoinvariants ≃ₗ[ℤ] IntSquared :=
  (Submodule.quotEquivOfEq _ _ ker_orderThreeCoordinates.symm).trans
    (orderThreeCoordinates.quotKerEquivOfSurjective surjective_orderThreeCoordinates)

/-- The order-four coinvariants, in the basis `(gamma, psiTwo)`. -/
public noncomputable def orderFourCoinvariantsEquivIntSquared :
    OrderFourCoinvariants ≃ₗ[ℤ] IntSquared :=
  (Submodule.quotEquivOfEq _ _ ker_orderFourCoordinates.symm).trans
    (orderFourCoordinates.quotKerEquivOfSurjective surjective_orderFourCoordinates)

@[simp]
public theorem orderThreeCoinvariantsEquivIntSquared_mk (x : Lattice) :
    orderThreeCoinvariantsEquivIntSquared (Submodule.Quotient.mk x) =
      orderThreeCoordinates x := by
  rfl

@[simp]
public theorem orderFourCoinvariantsEquivIntSquared_mk (x : Lattice) :
    orderFourCoinvariantsEquivIntSquared (Submodule.Quotient.mk x) =
      orderFourCoordinates x := by
  rfl








public abbrev OrderThreeSelectedPresentation :=
  CyclicCoinvariants.Presentation orderThreeDifference v₁ 3

public abbrev OrderFourSelectedPresentation :=
  CyclicCoinvariants.Presentation orderFourDifference v₂ 4

@[simp]
public theorem orderThree_selected_twist_coordinates :
    orderThreeCoinvariantsEquivIntSquared (Submodule.Quotient.mk v₁) = ![1, 0] := by
  rw [orderThreeCoinvariantsEquivIntSquared_mk]
  funext i
  fin_cases i <;> simp [vOne_eq_explicit, orderThreeCoordinates, psiOne]

@[simp]
public theorem orderFour_selected_twist_coordinates :
    orderFourCoinvariantsEquivIntSquared (Submodule.Quotient.mk v₂) = ![-1, 0] := by
  rw [orderFourCoinvariantsEquivIntSquared_mk]
  funext i
  fin_cases i <;> simp [vTwo_eq_explicit, orderFourCoordinates, psiTwo]

/-- Coordinates on the order-three presentation before imposing the meridian relation. -/
public def orderThreePresentationCoordinates : (OrderThreeCoinvariants × ℤ) →ₗ[ℤ] IntSquared where
  toFun x := ![3 * (orderThreeCoinvariantsEquivIntSquared x.1) 0 + x.2,
    (orderThreeCoinvariantsEquivIntSquared x.1) 1]
  map_add' x y := by
    funext i
    fin_cases i <;> simp
    ring
  map_smul' n x := by
    funext i
    fin_cases i <;> simp
    ring

/-- Coordinates on the order-four presentation before imposing the meridian relation. -/
public def orderFourPresentationCoordinates : (OrderFourCoinvariants × ℤ) →ₗ[ℤ] IntSquared where
  toFun x := ![4 * (orderFourCoinvariantsEquivIntSquared x.1) 0 - x.2,
    (orderFourCoinvariantsEquivIntSquared x.1) 1]
  map_add' x y := by
    funext i
    fin_cases i <;> simp
    ring
  map_smul' n x := by
    funext i
    fin_cases i <;> simp
    ring

public theorem surjective_orderThreePresentationCoordinates :
    Function.Surjective orderThreePresentationCoordinates := by
  intro y
  refine ⟨(orderThreeCoinvariantsEquivIntSquared.symm ![0, y 1], y 0), ?_⟩
  funext i
  fin_cases i <;> simp [orderThreePresentationCoordinates]

public theorem surjective_orderFourPresentationCoordinates :
    Function.Surjective orderFourPresentationCoordinates := by
  intro y
  refine ⟨(orderFourCoinvariantsEquivIntSquared.symm ![0, y 1], -y 0), ?_⟩
  funext i
  fin_cases i <;> simp [orderFourPresentationCoordinates]

public theorem range_orderThreeRelationMap_eq_ker :
    LinearMap.range (CyclicCoinvariants.relationMap orderThreeDifference v₁ 3) =
      LinearMap.ker orderThreePresentationCoordinates := by
  have hv : orderThreeCoordinates v₁ = ![1, 0] := by
    simpa only [orderThreeCoinvariantsEquivIntSquared_mk] using
      orderThree_selected_twist_coordinates
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    apply LinearMap.mem_ker.mpr
    funext i
    fin_cases i <;> simp [CyclicCoinvariants.relationMap, orderThreePresentationCoordinates, hv]
    ring
  · intro hx
    have h := LinearMap.mem_ker.mp hx
    have h0 := congrFun h (0 : Fin 2)
    have h1 := congrFun h (1 : Fin 2)
    let a := (orderThreeCoinvariantsEquivIntSquared x.1) 0
    refine ⟨-a, ?_⟩
    apply Prod.ext
    · apply orderThreeCoinvariantsEquivIntSquared.injective
      funext i
      fin_cases i
      · simp [CyclicCoinvariants.relationMap, a, hv]
      · simpa [CyclicCoinvariants.relationMap, orderThreePresentationCoordinates, hv] using h1.symm
    · simp [CyclicCoinvariants.relationMap, orderThreePresentationCoordinates, a] at h0 ⊢
      omega

public theorem range_orderFourRelationMap_eq_ker :
    LinearMap.range (CyclicCoinvariants.relationMap orderFourDifference v₂ 4) =
      LinearMap.ker orderFourPresentationCoordinates := by
  have hv : orderFourCoordinates v₂ = ![-1, 0] := by
    simpa only [orderFourCoinvariantsEquivIntSquared_mk] using
      orderFour_selected_twist_coordinates
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    apply LinearMap.mem_ker.mpr
    funext i
    fin_cases i <;> simp [CyclicCoinvariants.relationMap, orderFourPresentationCoordinates, hv]
    ring
  · intro hx
    have h := LinearMap.mem_ker.mp hx
    have h0 := congrFun h (0 : Fin 2)
    have h1 := congrFun h (1 : Fin 2)
    let a := (orderFourCoinvariantsEquivIntSquared x.1) 0
    refine ⟨a, ?_⟩
    apply Prod.ext
    · apply orderFourCoinvariantsEquivIntSquared.injective
      funext i
      fin_cases i
      · simp [CyclicCoinvariants.relationMap, a, hv]
      · simpa [CyclicCoinvariants.relationMap, orderFourPresentationCoordinates, hv] using h1.symm
    · simp [CyclicCoinvariants.relationMap, orderFourPresentationCoordinates, a] at h0 ⊢
      omega

/-- For the selected twist `v₁ = epsilon`, the order-three presentation is free of rank two. -/
public noncomputable def orderThreeSelectedPresentationEquivIntSquared :
    OrderThreeSelectedPresentation ≃ₗ[ℤ] IntSquared :=
  (Submodule.quotEquivOfEq _ _ range_orderThreeRelationMap_eq_ker).trans
    (orderThreePresentationCoordinates.quotKerEquivOfSurjective
      surjective_orderThreePresentationCoordinates)

/-- For the selected twist `v₂ = -epsilon'`, the order-four presentation is free of rank two. -/
public noncomputable def orderFourSelectedPresentationEquivIntSquared :
    OrderFourSelectedPresentation ≃ₗ[ℤ] IntSquared :=
  (Submodule.quotEquivOfEq _ _ range_orderFourRelationMap_eq_ker).trans
    (orderFourPresentationCoordinates.quotKerEquivOfSurjective
      surjective_orderFourPresentationCoordinates)

@[simp]
public theorem orderThreeSelectedPresentationEquivIntSquared_mk
    (x : OrderThreeCoinvariants × ℤ) :
    orderThreeSelectedPresentationEquivIntSquared (Submodule.Quotient.mk x) =
      orderThreePresentationCoordinates x := by
  rfl

@[simp]
public theorem orderFourSelectedPresentationEquivIntSquared_mk
    (x : OrderFourCoinvariants × ℤ) :
    orderFourSelectedPresentationEquivIntSquared (Submodule.Quotient.mk x) =
      orderFourPresentationCoordinates x := by
  rfl



end SphereSixComplex.MultipleFiberCoinvariants
