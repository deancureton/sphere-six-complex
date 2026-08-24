module

public import SphereSixComplex.Topology.WangHomologyPresentation

/-!
# Integral lattice algebra for Wang differentials

This module records only consequences of the source matrices on the explicitly encoded rank-four
lattice.  It does not identify that lattice with the homology of any paper space.  Such an
identification, and the corresponding induced-map compatibility, must be supplied separately.
-/

@[expose] public section

noncomputable section

open Matrix

namespace SphereSixComplex.LatticeWangAlgebra

open LatticeData

/-- The algebraic Wang differential `M - 1` associated to an integral matrix. -/
public def matrixDifference (M : Matrix (Fin 4) (Fin 4) ℤ) : Lattice →ₗ[ℤ] Lattice :=
  M.mulVecLin - LinearMap.id

@[simp]
public theorem matrixDifference_apply (M : Matrix (Fin 4) (Fin 4) ℤ) (x : Lattice) :
    matrixDifference M x = M *ᵥ x - x := by
  rfl

public abbrev tOneDifference := matrixDifference T₁
public abbrev tTwoDifference := matrixDifference T₂
public abbrev mZeroDifference := matrixDifference M₀

public theorem mem_ker_tOneDifference_iff (x : Lattice) :
    x ∈ LinearMap.ker tOneDifference ↔
      x 1 = 2 * x 2 ∧ x 3 = 3 * x 2 := by
  rw [LinearMap.mem_ker, matrixDifference_apply, sub_eq_zero, T₁_fixed_iff]

public theorem mem_ker_tTwoDifference_iff (x : Lattice) :
    x ∈ LinearMap.ker tTwoDifference ↔
      x 2 = x 1 ∧ x 3 = 2 * x 1 := by
  rw [LinearMap.mem_ker, matrixDifference_apply, sub_eq_zero, T₂_fixed_iff]

public theorem mem_ker_mZeroDifference_iff (x : Lattice) :
    x ∈ LinearMap.ker mZeroDifference ↔ x 0 = 0 ∧ x 1 = 0 := by
  rw [LinearMap.mem_ker, matrixDifference_apply, M₀_sub_mulVec_eq_zero_iff]

/-- The coordinate plane spanned by the last two standard lattice vectors. -/
public def tailCoordinateSubmodule : Submodule ℤ Lattice where
  carrier := {x | x 0 = 0 ∧ x 1 = 0}
  zero_mem' := by simp
  add_mem' := by
    rintro x y ⟨hx0, hx1⟩ ⟨hy0, hy1⟩
    simp [hx0, hx1, hy0, hy1]
  smul_mem' := by
    rintro n x ⟨hx0, hx1⟩
    simp [hx0, hx1]

public theorem ker_mZeroDifference :
    LinearMap.ker mZeroDifference = tailCoordinateSubmodule := by
  ext x
  exact mem_ker_mZeroDifference_iff x

public theorem range_mZeroDifference :
    LinearMap.range mZeroDifference = tailCoordinateSubmodule := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change (M₀ *ᵥ y - y) 0 = 0 ∧ (M₀ *ᵥ y - y) 1 = 0
    constructor
    · simpa using congrFun (M₀_sub_mulVec y) (0 : Fin 4)
    · simpa using congrFun (M₀_sub_mulVec y) (1 : Fin 4)
  · intro hx
    have hx' : x ∈ Set.range (fun y : Lattice ↦ M₀ *ᵥ y - y) := by
      rw [range_M₀_sub_mulVec]
      exact hx
    obtain ⟨y, hy⟩ := hx'
    exact ⟨y, by simpa using hy⟩

/-- Projection to the first two coordinates. -/
public def headCoordinateProjection : Lattice →ₗ[ℤ] (Fin 2 → ℤ) where
  toFun x := ![x 0, x 1]
  map_add' x y := by
    funext i
    fin_cases i <;> simp
  map_smul' n x := by
    funext i
    fin_cases i <;> simp

public theorem ker_headCoordinateProjection :
    LinearMap.ker headCoordinateProjection = tailCoordinateSubmodule := by
  ext x
  constructor
  · intro hx
    have h := LinearMap.mem_ker.mp hx
    constructor
    · have := congrFun h (0 : Fin 2)
      simpa [headCoordinateProjection] using this
    · have := congrFun h (1 : Fin 2)
      simpa [headCoordinateProjection] using this
  · rintro ⟨h0, h1⟩
    apply LinearMap.mem_ker.mpr
    funext i
    fin_cases i <;> simp [headCoordinateProjection, h0, h1]

public theorem headCoordinateProjection_surjective :
    Function.Surjective headCoordinateProjection := by
  intro y
  refine ⟨![y 0, y 1, 0, 0], ?_⟩
  funext i
  fin_cases i <;> simp [headCoordinateProjection]

/-- The `M₀` coinvariants are the free rank-two group detected by the first two coordinates. -/
public noncomputable def mZeroCoinvariantsEquivIntSquared :
    (Lattice ⧸ LinearMap.range mZeroDifference) ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  (Submodule.quotEquivOfEq _ _
      (range_mZeroDifference.trans ker_headCoordinateProjection.symm)).trans
    (headCoordinateProjection.quotKerEquivOfSurjective headCoordinateProjection_surjective)

/-- The `M₀` invariants are the free rank-two group detected by the last two coordinates. -/
public def mZeroInvariantsEquivIntSquared :
    LinearMap.ker mZeroDifference ≃ₗ[ℤ] (Fin 2 → ℤ) where
  toFun x := ![x.1 2, x.1 3]
  invFun y :=
    ⟨![0, 0, y 0, y 1], mem_ker_mZeroDifference_iff _ |>.mpr ⟨by simp, by simp⟩⟩
  map_add' x y := by
    funext i
    fin_cases i <;> simp
  map_smul' n x := by
    funext i
    fin_cases i <;> simp
  left_inv x := by
    apply Subtype.ext
    have hx := (mem_ker_mZeroDifference_iff x.1).mp x.2
    funext i
    fin_cases i <;> simp [hx.1, hx.2]
  right_inv y := by
    funext i
    fin_cases i <;> simp

end SphereSixComplex.LatticeWangAlgebra
