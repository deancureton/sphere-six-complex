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
public def orderOneDifference : Lattice →ₗ[ℤ] Lattice :=
  A₁.mulVecLin - LinearMap.id

/-- The integral endomorphism `A₂ - I` on the dual lattice. -/
public def orderTwoDifference : Lattice →ₗ[ℤ] Lattice :=
  A₂.mulVecLin - LinearMap.id

@[simp]
public theorem orderOneDifference_apply (x : Lattice) :
    orderOneDifference x = A₁ *ᵥ x - x := by
  rfl

@[simp]
public theorem orderTwoDifference_apply (x : Lattice) :
    orderTwoDifference x = A₂ *ᵥ x - x := by
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
public def orderOneCoordinates : Lattice →ₗ[ℤ] IntSquared where
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
public def orderTwoCoordinates : Lattice →ₗ[ℤ] IntSquared where
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
public theorem range_orderOneDifference :
    LinearMap.range orderOneDifference =
      {x : Lattice | x 0 = 0 ∧ 2 * x 1 + x 2 + 3 * x 3 = 0} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    constructor
    · simp [orderOneDifference, A₁, dotProduct,
        Fin.sum_univ_succ]
    · simp [orderOneDifference, A₁, dotProduct,
        Fin.sum_univ_succ]
      ring
  · rintro ⟨h0, hpsi⟩
    refine ⟨![0, x 3, x 1 + x 3, 0], ?_⟩
    funext i
    fin_cases i <;> simp [orderOneDifference, A₁, h0]
    all_goals omega

/-- Explicit description of the image of `A₂ - I`. -/
public theorem range_orderTwoDifference :
    LinearMap.range orderTwoDifference =
      {x : Lattice | x 0 = 0 ∧ x 1 + x 2 + 2 * x 3 = 0} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    constructor
    · simp [orderTwoDifference, A₂, dotProduct,
        Fin.sum_univ_succ]
    · simp [orderTwoDifference, A₂, dotProduct,
        Fin.sum_univ_succ]
      ring
  · rintro ⟨h0, hpsi⟩
    refine ⟨![0, -x 1 - x 3, x 3, 0], ?_⟩
    funext i
    fin_cases i <;> simp [orderTwoDifference, A₂, h0]
    all_goals omega

public theorem ker_orderOneCoordinates :
    LinearMap.ker orderOneCoordinates = LinearMap.range orderOneDifference := by
  ext x
  constructor
  · intro hx
    have h := LinearMap.mem_ker.mp hx
    have h0 := congrFun h (0 : Fin 2)
    have h1 := congrFun h (1 : Fin 2)
    change x ∈ (↑(LinearMap.range orderOneDifference) : Set Lattice)
    rw [range_orderOneDifference]
    simpa [orderOneCoordinates, psiOne] using And.intro h0 h1
  · intro hx
    have hx' : x ∈ (↑(LinearMap.range orderOneDifference) : Set Lattice) := hx
    rw [range_orderOneDifference] at hx'
    apply LinearMap.mem_ker.mpr
    funext i
    fin_cases i <;> simp [orderOneCoordinates, psiOne, hx'.1, hx'.2]

public theorem ker_orderTwoCoordinates :
    LinearMap.ker orderTwoCoordinates = LinearMap.range orderTwoDifference := by
  ext x
  constructor
  · intro hx
    have h := LinearMap.mem_ker.mp hx
    have h0 := congrFun h (0 : Fin 2)
    have h1 := congrFun h (1 : Fin 2)
    change x ∈ (↑(LinearMap.range orderTwoDifference) : Set Lattice)
    rw [range_orderTwoDifference]
    simpa [orderTwoCoordinates, psiTwo] using And.intro h0 h1
  · intro hx
    have hx' : x ∈ (↑(LinearMap.range orderTwoDifference) : Set Lattice) := hx
    rw [range_orderTwoDifference] at hx'
    apply LinearMap.mem_ker.mpr
    funext i
    fin_cases i <;> simp [orderTwoCoordinates, psiTwo, hx'.1, hx'.2]

public theorem orderOneCoordinates_surjective :
    Function.Surjective orderOneCoordinates := by
  intro y
  refine ⟨![y 0, 0, y 1, 0], ?_⟩
  funext i
  fin_cases i <;> simp [orderOneCoordinates, psiOne]

public theorem orderTwoCoordinates_surjective :
    Function.Surjective orderTwoCoordinates := by
  intro y
  refine ⟨![y 0, 0, y 1, 0], ?_⟩
  funext i
  fin_cases i <;> simp [orderTwoCoordinates, psiTwo]

public abbrev OrderOneCoinvariants :=
  LatticeData.Lattice ⧸ LinearMap.range orderOneDifference

public abbrev OrderTwoCoinvariants :=
  LatticeData.Lattice ⧸ LinearMap.range orderTwoDifference

/-- The order-three coinvariants, in the basis `(gamma, psiOne)`. -/
public noncomputable def orderOneCoinvariantsEquivIntSquared :
    OrderOneCoinvariants ≃ₗ[ℤ] IntSquared :=
  (Submodule.quotEquivOfEq _ _ ker_orderOneCoordinates.symm).trans
    (orderOneCoordinates.quotKerEquivOfSurjective orderOneCoordinates_surjective)

/-- The order-four coinvariants, in the basis `(gamma, psiTwo)`. -/
public noncomputable def orderTwoCoinvariantsEquivIntSquared :
    OrderTwoCoinvariants ≃ₗ[ℤ] IntSquared :=
  (Submodule.quotEquivOfEq _ _ ker_orderTwoCoordinates.symm).trans
    (orderTwoCoordinates.quotKerEquivOfSurjective orderTwoCoordinates_surjective)

@[simp]
public theorem orderOneCoinvariantsEquivIntSquared_mk (x : Lattice) :
    orderOneCoinvariantsEquivIntSquared (Submodule.Quotient.mk x) =
      orderOneCoordinates x := by
  rfl

@[simp]
public theorem orderTwoCoinvariantsEquivIntSquared_mk (x : Lattice) :
    orderTwoCoinvariantsEquivIntSquared (Submodule.Quotient.mk x) =
      orderTwoCoordinates x := by
  rfl








public abbrev OrderOneSelectedPresentation :=
  CyclicCoinvariants.Presentation orderOneDifference v₁ 3

public abbrev OrderTwoSelectedPresentation :=
  CyclicCoinvariants.Presentation orderTwoDifference v₂ 4

@[simp]
public theorem orderOne_selected_twist_coordinates :
    orderOneCoinvariantsEquivIntSquared (Submodule.Quotient.mk v₁) = ![1, 0] := by
  rw [orderOneCoinvariantsEquivIntSquared_mk]
  funext i
  fin_cases i <;> simp [vOne_eq_explicit, orderOneCoordinates, psiOne]

@[simp]
public theorem orderTwo_selected_twist_coordinates :
    orderTwoCoinvariantsEquivIntSquared (Submodule.Quotient.mk v₂) = ![-1, 0] := by
  rw [orderTwoCoinvariantsEquivIntSquared_mk]
  funext i
  fin_cases i <;> simp [vTwo_eq_explicit, orderTwoCoordinates, psiTwo]

/-- Coordinates on the order-three presentation before imposing the meridian relation. -/
public def orderOnePresentationCoordinates : (OrderOneCoinvariants × ℤ) →ₗ[ℤ] IntSquared where
  toFun x := ![3 * (orderOneCoinvariantsEquivIntSquared x.1) 0 + x.2,
    (orderOneCoinvariantsEquivIntSquared x.1) 1]
  map_add' x y := by
    funext i
    fin_cases i <;> simp
    ring
  map_smul' n x := by
    funext i
    fin_cases i <;> simp
    ring

/-- Coordinates on the order-four presentation before imposing the meridian relation. -/
public def orderTwoPresentationCoordinates : (OrderTwoCoinvariants × ℤ) →ₗ[ℤ] IntSquared where
  toFun x := ![4 * (orderTwoCoinvariantsEquivIntSquared x.1) 0 - x.2,
    (orderTwoCoinvariantsEquivIntSquared x.1) 1]
  map_add' x y := by
    funext i
    fin_cases i <;> simp
    ring
  map_smul' n x := by
    funext i
    fin_cases i <;> simp
    ring

public theorem orderOnePresentationCoordinates_surjective :
    Function.Surjective orderOnePresentationCoordinates := by
  intro y
  refine ⟨(orderOneCoinvariantsEquivIntSquared.symm ![0, y 1], y 0), ?_⟩
  funext i
  fin_cases i <;> simp [orderOnePresentationCoordinates]

public theorem orderTwoPresentationCoordinates_surjective :
    Function.Surjective orderTwoPresentationCoordinates := by
  intro y
  refine ⟨(orderTwoCoinvariantsEquivIntSquared.symm ![0, y 1], -y 0), ?_⟩
  funext i
  fin_cases i <;> simp [orderTwoPresentationCoordinates]

public theorem range_orderOneRelationMap_eq_ker :
    LinearMap.range (CyclicCoinvariants.relationMap orderOneDifference v₁ 3) =
      LinearMap.ker orderOnePresentationCoordinates := by
  have hv : orderOneCoordinates v₁ = ![1, 0] := by
    simpa only [orderOneCoinvariantsEquivIntSquared_mk] using
      orderOne_selected_twist_coordinates
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    apply LinearMap.mem_ker.mpr
    funext i
    fin_cases i <;> simp [CyclicCoinvariants.relationMap, orderOnePresentationCoordinates, hv]
    ring
  · intro hx
    have h := LinearMap.mem_ker.mp hx
    have h0 := congrFun h (0 : Fin 2)
    have h1 := congrFun h (1 : Fin 2)
    let a := (orderOneCoinvariantsEquivIntSquared x.1) 0
    refine ⟨-a, ?_⟩
    apply Prod.ext
    · apply orderOneCoinvariantsEquivIntSquared.injective
      funext i
      fin_cases i
      · simp [CyclicCoinvariants.relationMap, a, hv]
      · simpa [CyclicCoinvariants.relationMap, orderOnePresentationCoordinates, hv] using h1.symm
    · simp [CyclicCoinvariants.relationMap, orderOnePresentationCoordinates, a] at h0 ⊢
      omega

public theorem range_orderTwoRelationMap_eq_ker :
    LinearMap.range (CyclicCoinvariants.relationMap orderTwoDifference v₂ 4) =
      LinearMap.ker orderTwoPresentationCoordinates := by
  have hv : orderTwoCoordinates v₂ = ![-1, 0] := by
    simpa only [orderTwoCoinvariantsEquivIntSquared_mk] using
      orderTwo_selected_twist_coordinates
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    apply LinearMap.mem_ker.mpr
    funext i
    fin_cases i <;> simp [CyclicCoinvariants.relationMap, orderTwoPresentationCoordinates, hv]
    ring
  · intro hx
    have h := LinearMap.mem_ker.mp hx
    have h0 := congrFun h (0 : Fin 2)
    have h1 := congrFun h (1 : Fin 2)
    let a := (orderTwoCoinvariantsEquivIntSquared x.1) 0
    refine ⟨a, ?_⟩
    apply Prod.ext
    · apply orderTwoCoinvariantsEquivIntSquared.injective
      funext i
      fin_cases i
      · simp [CyclicCoinvariants.relationMap, a, hv]
      · simpa [CyclicCoinvariants.relationMap, orderTwoPresentationCoordinates, hv] using h1.symm
    · simp [CyclicCoinvariants.relationMap, orderTwoPresentationCoordinates, a] at h0 ⊢
      omega

/-- For the selected twist `v₁ = epsilon`, the order-three presentation is free of rank two. -/
public noncomputable def orderOneSelectedPresentationEquivIntSquared :
    OrderOneSelectedPresentation ≃ₗ[ℤ] IntSquared :=
  (Submodule.quotEquivOfEq _ _ range_orderOneRelationMap_eq_ker).trans
    (orderOnePresentationCoordinates.quotKerEquivOfSurjective
      orderOnePresentationCoordinates_surjective)

/-- For the selected twist `v₂ = -epsilon'`, the order-four presentation is free of rank two. -/
public noncomputable def orderTwoSelectedPresentationEquivIntSquared :
    OrderTwoSelectedPresentation ≃ₗ[ℤ] IntSquared :=
  (Submodule.quotEquivOfEq _ _ range_orderTwoRelationMap_eq_ker).trans
    (orderTwoPresentationCoordinates.quotKerEquivOfSurjective
      orderTwoPresentationCoordinates_surjective)

@[simp]
public theorem orderOneSelectedPresentationEquivIntSquared_mk
    (x : OrderOneCoinvariants × ℤ) :
    orderOneSelectedPresentationEquivIntSquared (Submodule.Quotient.mk x) =
      orderOnePresentationCoordinates x := by
  rfl

@[simp]
public theorem orderTwoSelectedPresentationEquivIntSquared_mk
    (x : OrderTwoCoinvariants × ℤ) :
    orderTwoSelectedPresentationEquivIntSquared (Submodule.Quotient.mk x) =
      orderTwoPresentationCoordinates x := by
  rfl



end SphereSixComplex.MultipleFiberCoinvariants
