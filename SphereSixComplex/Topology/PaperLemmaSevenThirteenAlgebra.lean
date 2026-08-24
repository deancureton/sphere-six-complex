module

public import SphereSixComplex.Topology.TwistObstruction

/-!
# Integral algebra for the two multiple fibres

This module formalizes the lattice and abelian-group calculations in Lemma 7.13.  It makes no
identification with the homology of a topological space.
-/

@[expose] public section

noncomputable section

open Matrix

namespace SphereSixComplex.Topology.PaperLemmaSevenThirteenAlgebra

open LatticeData
open TwistObstruction

public abbrev IntSquared := Fin 2 → ℤ

/-- Exposed copy of the first source matrix, used only to evaluate its integral action. -/
public def explicitAOne : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1, 0, 0, 0; 6, 0, 1, 0; -6, -1, -1, 0; -2, 1, 0, 1]

/-- Exposed copy of the second source matrix, used only to evaluate its integral action. -/
public def explicitATwo : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1, 0, 0, 0; 0, 0, -1, 0; -6, 1, 0, 0; 3, 0, 1, 1]

public theorem AOne_eq_explicit : A₁ = explicitAOne := by
  rfl

public theorem ATwo_eq_explicit : A₂ = explicitATwo := by
  rfl

@[simp]
public theorem gamma_apply (x : LatticeData.Lattice) : gamma x = x 0 := by
  rfl

public theorem gammaVec_eq_explicit : gammaVec = ![1, 0, 0, 0] := by
  rfl

public theorem wVec_eq_explicit : wVec = ![0, 0, 1, 0] := by
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
    · simp [orderOneDifference, AOne_eq_explicit, explicitAOne, dotProduct,
        Fin.sum_univ_succ]
    · simp [orderOneDifference, AOne_eq_explicit, explicitAOne, dotProduct,
        Fin.sum_univ_succ]
      ring
  · rintro ⟨h0, hpsi⟩
    refine ⟨![0, x 3, x 1 + x 3, 0], ?_⟩
    funext i
    fin_cases i <;> simp [orderOneDifference, AOne_eq_explicit, explicitAOne, h0]
    all_goals omega

/-- Explicit description of the image of `A₂ - I`. -/
public theorem range_orderTwoDifference :
    LinearMap.range orderTwoDifference =
      {x : Lattice | x 0 = 0 ∧ x 1 + x 2 + 2 * x 3 = 0} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    constructor
    · simp [orderTwoDifference, ATwo_eq_explicit, explicitATwo, dotProduct,
        Fin.sum_univ_succ]
    · simp [orderTwoDifference, ATwo_eq_explicit, explicitATwo, dotProduct,
        Fin.sum_univ_succ]
      ring
  · rintro ⟨h0, hpsi⟩
    refine ⟨![0, -x 1 - x 3, x 3, 0], ?_⟩
    funext i
    fin_cases i <;> simp [orderTwoDifference, ATwo_eq_explicit, explicitATwo, h0]
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

/-- Functionals annihilating the image of an integral endomorphism. -/
public def DifferenceAnnihilator (D : Lattice →ₗ[ℤ] Lattice) :
    Submodule ℤ (Module.Dual ℤ Lattice) where
  carrier := {f | ∀ x, f (D x) = 0}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg x
    simp [hf x, hg x]
  smul_mem' := by
    intro n f hf x
    simp [hf x]

/-- The two explicit generators `gamma, psiOne` of the first annihilator. -/
public def orderOneAnnihilatorFromCoordinates (c : IntSquared) : Module.Dual ℤ Lattice :=
  (c 0) • gamma + (c 1) • psiOne

/-- The two explicit generators `gamma, psiTwo` of the second annihilator. -/
public def orderTwoAnnihilatorFromCoordinates (c : IntSquared) : Module.Dual ℤ Lattice :=
  (c 0) • gamma + (c 1) • psiTwo

public theorem orderOneAnnihilatorFromCoordinates_mem (c : IntSquared) :
    orderOneAnnihilatorFromCoordinates c ∈ DifferenceAnnihilator orderOneDifference := by
  intro x
  have hmem : orderOneDifference x ∈ LinearMap.ker orderOneCoordinates := by
    rw [ker_orderOneCoordinates]
    exact ⟨x, rfl⟩
  have h := LinearMap.mem_ker.mp hmem
  have h0 := congrFun h (0 : Fin 2)
  have h1 := congrFun h (1 : Fin 2)
  simp [orderOneCoordinates] at h0 h1
  simp [orderOneAnnihilatorFromCoordinates, h0, h1]

public theorem orderTwoAnnihilatorFromCoordinates_mem (c : IntSquared) :
    orderTwoAnnihilatorFromCoordinates c ∈ DifferenceAnnihilator orderTwoDifference := by
  intro x
  have hmem : orderTwoDifference x ∈ LinearMap.ker orderTwoCoordinates := by
    rw [ker_orderTwoCoordinates]
    exact ⟨x, rfl⟩
  have h := LinearMap.mem_ker.mp hmem
  have h0 := congrFun h (0 : Fin 2)
  have h1 := congrFun h (1 : Fin 2)
  simp [orderTwoCoordinates] at h0 h1
  simp [orderTwoAnnihilatorFromCoordinates, h0, h1]

/-- The annihilator of `A₁ - I` is freely generated by `gamma` and `psiOne`. -/
public noncomputable def orderOneAnnihilatorEquivIntSquared :
    DifferenceAnnihilator orderOneDifference ≃ₗ[ℤ] IntSquared where
  toFun f := ![f.1 gammaVec, f.1 wVec]
  invFun c := ⟨orderOneAnnihilatorFromCoordinates c,
    orderOneAnnihilatorFromCoordinates_mem c⟩
  map_add' f g := by
    funext i
    fin_cases i <;> simp
  map_smul' n f := by
    funext i
    fin_cases i <;> simp
  left_inv f := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    let r : Lattice := ![0, x 1, x 2 - psiOne x, x 3]
    have hr : x = (x 0) • gammaVec + (psiOne x) • wVec + r := by
      funext i
      fin_cases i <;> simp [r, gammaVec, wVec]
    have hrker : r ∈ LinearMap.ker orderOneCoordinates := by
      apply LinearMap.mem_ker.mpr
      funext i
      fin_cases i <;> simp [r, orderOneCoordinates, psiOne]
      ring
    have hrange : r ∈ LinearMap.range orderOneDifference := by
      rw [← ker_orderOneCoordinates]
      exact hrker
    obtain ⟨y, hy⟩ := hrange
    have hfr : f.1 r = 0 := by
      rw [← hy]
      exact f.2 y
    have hfx : f.1 x = (x 0) * f.1 gammaVec + (psiOne x) * f.1 wVec := by
      calc
        f.1 x = f.1 ((x 0) • gammaVec + (psiOne x) • wVec + r) := by rw [← hr]
        _ = (x 0) * f.1 gammaVec + (psiOne x) * f.1 wVec := by
          simp only [map_add, map_zsmul, hfr, add_zero, smul_eq_mul]
    change (f.1 gammaVec) * gamma x + (f.1 wVec) * psiOne x = f.1 x
    rw [hfx, gamma_apply]
    ring
  right_inv c := by
    funext i
    fin_cases i <;>
      simp [orderOneAnnihilatorFromCoordinates, gammaVec_eq_explicit, wVec_eq_explicit,
        psiOne]

/-- The annihilator of `A₂ - I` is freely generated by `gamma` and `psiTwo`. -/
public noncomputable def orderTwoAnnihilatorEquivIntSquared :
    DifferenceAnnihilator orderTwoDifference ≃ₗ[ℤ] IntSquared where
  toFun f := ![f.1 gammaVec, f.1 wVec]
  invFun c := ⟨orderTwoAnnihilatorFromCoordinates c,
    orderTwoAnnihilatorFromCoordinates_mem c⟩
  map_add' f g := by
    funext i
    fin_cases i <;> simp
  map_smul' n f := by
    funext i
    fin_cases i <;> simp
  left_inv f := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    let r : Lattice := ![0, x 1, x 2 - psiTwo x, x 3]
    have hr : x = (x 0) • gammaVec + (psiTwo x) • wVec + r := by
      funext i
      fin_cases i <;> simp [r, gammaVec, wVec]
    have hrker : r ∈ LinearMap.ker orderTwoCoordinates := by
      apply LinearMap.mem_ker.mpr
      funext i
      fin_cases i <;> simp [r, orderTwoCoordinates, psiTwo]
      ring
    have hrange : r ∈ LinearMap.range orderTwoDifference := by
      rw [← ker_orderTwoCoordinates]
      exact hrker
    obtain ⟨y, hy⟩ := hrange
    have hfr : f.1 r = 0 := by
      rw [← hy]
      exact f.2 y
    have hfx : f.1 x = (x 0) * f.1 gammaVec + (psiTwo x) * f.1 wVec := by
      calc
        f.1 x = f.1 ((x 0) • gammaVec + (psiTwo x) • wVec + r) := by rw [← hr]
        _ = (x 0) * f.1 gammaVec + (psiTwo x) * f.1 wVec := by
          simp only [map_add, map_zsmul, hfr, add_zero, smul_eq_mul]
    change (f.1 gammaVec) * gamma x + (f.1 wVec) * psiTwo x = f.1 x
    rw [hfx, gamma_apply]
    ring
  right_inv c := by
    funext i
    fin_cases i <;>
      simp [orderTwoAnnihilatorFromCoordinates, gammaVec_eq_explicit, wVec_eq_explicit,
        psiTwo]

/-- The relation map imposing `m * meridian = [v]` after taking coinvariants. -/
public def multipleFiberRelationMap (D : Lattice →ₗ[ℤ] Lattice) (v : Lattice) (m : ℤ) :
    ℤ →ₗ[ℤ] ((LatticeData.Lattice ⧸ LinearMap.range D) × ℤ) where
  toFun k := k • (-Submodule.Quotient.mk v, m)
  map_add' a b := by simp [add_smul]
  map_smul' a b := by simp [mul_smul]

/-- The abelian multiple-fibre presentation: coinvariants plus a meridian, modulo
`m * meridian = [v]`. -/
public abbrev MultipleFiberHOnePresentation
    (D : Lattice →ₗ[ℤ] Lattice) (v : Lattice) (m : ℤ) :=
  ((LatticeData.Lattice ⧸ LinearMap.range D) × ℤ) ⧸
    LinearMap.range (multipleFiberRelationMap D v m)

public abbrev OrderOneSelectedPresentation :=
  MultipleFiberHOnePresentation orderOneDifference v₁ 3

public abbrev OrderTwoSelectedPresentation :=
  MultipleFiberHOnePresentation orderTwoDifference v₂ 4

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
    LinearMap.range (multipleFiberRelationMap orderOneDifference v₁ 3) =
      LinearMap.ker orderOnePresentationCoordinates := by
  have hv : orderOneCoordinates v₁ = ![1, 0] := by
    simpa only [orderOneCoinvariantsEquivIntSquared_mk] using
      orderOne_selected_twist_coordinates
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    apply LinearMap.mem_ker.mpr
    funext i
    fin_cases i <;> simp [multipleFiberRelationMap, orderOnePresentationCoordinates, hv]
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
      · simp [multipleFiberRelationMap, a, hv]
      · simpa [multipleFiberRelationMap, orderOnePresentationCoordinates, hv] using h1.symm
    · simp [multipleFiberRelationMap, orderOnePresentationCoordinates, a] at h0 ⊢
      omega

public theorem range_orderTwoRelationMap_eq_ker :
    LinearMap.range (multipleFiberRelationMap orderTwoDifference v₂ 4) =
      LinearMap.ker orderTwoPresentationCoordinates := by
  have hv : orderTwoCoordinates v₂ = ![-1, 0] := by
    simpa only [orderTwoCoinvariantsEquivIntSquared_mk] using
      orderTwo_selected_twist_coordinates
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    apply LinearMap.mem_ker.mpr
    funext i
    fin_cases i <;> simp [multipleFiberRelationMap, orderTwoPresentationCoordinates, hv]
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
      · simp [multipleFiberRelationMap, a, hv]
      · simpa [multipleFiberRelationMap, orderTwoPresentationCoordinates, hv] using h1.symm
    · simp [multipleFiberRelationMap, orderTwoPresentationCoordinates, a] at h0 ⊢
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

public instance orderOneSelectedPresentation_noZeroSMulDivisors :
    NoZeroSMulDivisors ℤ OrderOneSelectedPresentation where
  eq_zero_or_eq_zero_of_smul_eq_zero {c x} h := by
    by_cases hc : c = 0
    · exact Or.inl hc
    · right
      apply orderOneSelectedPresentationEquivIntSquared.injective
      funext i
      have h' : c • orderOneSelectedPresentationEquivIntSquared x = 0 := by
        rw [← map_smul, h, map_zero]
      have hi : c * orderOneSelectedPresentationEquivIntSquared x i = 0 := by
        simpa using congrFun h' i
      simpa using (mul_eq_zero.mp hi).resolve_left hc

public instance orderTwoSelectedPresentation_noZeroSMulDivisors :
    NoZeroSMulDivisors ℤ OrderTwoSelectedPresentation where
  eq_zero_or_eq_zero_of_smul_eq_zero {c x} h := by
    by_cases hc : c = 0
    · exact Or.inl hc
    · right
      apply orderTwoSelectedPresentationEquivIntSquared.injective
      funext i
      have h' : c • orderTwoSelectedPresentationEquivIntSquared x = 0 := by
        rw [← map_smul, h, map_zero]
      have hi : c * orderTwoSelectedPresentationEquivIntSquared x i = 0 := by
        simpa using congrFun h' i
      simpa using (mul_eq_zero.mp hi).resolve_left hc

end SphereSixComplex.Topology.PaperLemmaSevenThirteenAlgebra
