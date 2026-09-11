module

public import SphereSixComplex.Prerequisites.Topology.CellularSquareOrientation
public import SphereSixComplex.Prerequisites.Topology.ContractingPrismSuspension

@[expose] public section
noncomputable section
open Set Topology
namespace SphereSixComplex

public def cylinderLowerSide {X : Type} (A : Set X) : Set (unitInterval × X) :=
  {p | p.1 = 0 ∨ p.2 ∈ A}

public def cylinderVerticalScale (s t : unitInterval) : unitInterval :=
  ⟨(1 - (s : ℝ)) * (t : ℝ),
    mul_nonneg (sub_nonneg.mpr s.2.2) t.2.1,
    (mul_le_mul_of_nonneg_right (by linarith [s.2.1] : 1 - (s : ℝ) ≤ 1) t.2.1).trans
      (by simpa using t.2.2)⟩

public theorem cylinderVerticalScale_continuous :
    Continuous (fun p : unitInterval × unitInterval ↦ cylinderVerticalScale p.1 p.2) := by
  apply Continuous.subtype_mk
  fun_prop

@[simp] public theorem cylinderVerticalScale_zero (t : unitInterval) :
    cylinderVerticalScale 0 t = t := by
  apply Subtype.ext
  simp [cylinderVerticalScale]

@[simp] public theorem cylinderVerticalScale_one (t : unitInterval) :
    cylinderVerticalScale 1 t = 0 := by
  apply Subtype.ext
  simp [cylinderVerticalScale]

@[simp] public theorem cylinderVerticalScale_zero_right (s : unitInterval) :
    cylinderVerticalScale s 0 = 0 := by
  apply Subtype.ext
  simp [cylinderVerticalScale]

public def cylinderBottomMap (X : Type) [TopologicalSpace X] :
    ContinuousMap (unitInterval × X) (unitInterval × X) where
  toFun p := (0, p.2)
  continuous_toFun := continuous_const.prodMk continuous_snd

public def cylinderVerticalHomotopy (X : Type) [TopologicalSpace X] :
    ContinuousMap.Homotopy (ContinuousMap.id (unitInterval × X)) (cylinderBottomMap X) where
  toFun p := (cylinderVerticalScale p.1 p.2.1, p.2.2)
  continuous_toFun := (cylinderVerticalScale_continuous.comp
    (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk
      (continuous_snd.comp continuous_snd)
  map_zero_left p := by simp
  map_one_left p := by simp [cylinderBottomMap]

public theorem cylinderVerticalHomotopy_preserves_lowerSide {X : Type} [TopologicalSpace X]
    (A : Set X) (s : unitInterval) (p : unitInterval × X) (hp : p ∈ cylinderLowerSide A) :
    cylinderVerticalHomotopy X (s, p) ∈ cylinderLowerSide A := by
  rcases hp with hp | hp
  · exact Or.inl (by change cylinderVerticalScale s p.1 = 0; rw [hp]; simp)
  · exact Or.inr hp

public def cylinderLowerSideBottomMap {X : Type} [TopologicalSpace X] (A : Set X) :
    ContinuousMap (cylinderLowerSide A) (cylinderLowerSide A) where
  toFun p := ⟨(0, p.1.2), Or.inl rfl⟩
  continuous_toFun := (continuous_const.prodMk
    (continuous_snd.comp continuous_subtype_val)).subtype_mk _

public def cylinderLowerSideHomotopy {X : Type} [TopologicalSpace X] (A : Set X) :
    ContinuousMap.Homotopy (ContinuousMap.id (cylinderLowerSide A))
      (cylinderLowerSideBottomMap A) where
  toFun p := ⟨cylinderVerticalHomotopy X (p.1, p.2.1),
    cylinderVerticalHomotopy_preserves_lowerSide A p.1 p.2.1 p.2.2⟩
  continuous_toFun := ((cylinderVerticalHomotopy X).continuous.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  map_zero_left p := by apply Subtype.ext; exact (cylinderVerticalHomotopy X).map_zero_left _
  map_one_left p := by apply Subtype.ext; exact (cylinderVerticalHomotopy X).map_one_left _



end SphereSixComplex
