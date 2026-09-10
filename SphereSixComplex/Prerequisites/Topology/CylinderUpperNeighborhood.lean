module

public import SphereSixComplex.Prerequisites.Topology.CylinderRelativeTriple

@[expose] public section
noncomputable section
open Set Topology
namespace SphereSixComplex

public def cylinderUpperNeighborhood {X : Type} (A : Set X) : Set (cylinderBoundary A) :=
  {p | 0 < (p.1.1 : ℝ)}

public theorem cylinderUpperNeighborhood_isOpen {X : Type} [TopologicalSpace X] (A : Set X) :
    IsOpen (cylinderUpperNeighborhood A) := by
  exact isOpen_lt continuous_const
    (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val))

public def cylinderBottomNeighborhood {X : Type} (A : Set X) : Set (cylinderBoundary A) :=
  {p | (p.1.1 : ℝ) < 1}

public theorem cylinderBottomNeighborhood_isOpen {X : Type} [TopologicalSpace X] (A : Set X) :
    IsOpen (cylinderBottomNeighborhood A) := by
  exact isOpen_lt
    (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)) continuous_const

public theorem cylinderBoundary_open_cover {X : Type} (A : Set X) :
    cylinderUpperNeighborhood A ∪ cylinderBottomNeighborhood A = Set.univ := by
  ext p
  simp only [Set.mem_union, Set.mem_univ, iff_true]
  change 0 < (p.1.1 : ℝ) ∨ (p.1.1 : ℝ) < 1
  by_cases h : 0 < (p.1.1 : ℝ)
  · exact Or.inl h
  · exact Or.inr (by linarith)

public theorem cylinderBottomNeighborhood_subset_lowerSide {X : Type} (A : Set X)
    (p : cylinderBoundary A) (hp : p ∈ cylinderBottomNeighborhood A) :
    p.1 ∈ cylinderLowerSide A := by
  rcases p.2 with h | h | h
  · exact Or.inl h
  · have he : (p.1.1 : ℝ) = 1 := congrArg Subtype.val h
    change (p.1.1 : ℝ) < 1 at hp
    exact False.elim (by linarith)
  · exact Or.inr h

public theorem cylinderUpperNeighborhood_mem_lowerSide_iff {X : Type} (A : Set X)
    (p : cylinderUpperNeighborhood A) : p.1.1 ∈ cylinderLowerSide A ↔ p.1.1.2 ∈ A := by
  constructor
  · rintro (h | h)
    · have he : (p.1.1.1 : ℝ) = 0 := congrArg Subtype.val h
      have hp : 0 < (p.1.1.1 : ℝ) := p.2
      exact False.elim (by linarith)
    · exact h
  · exact Or.inr

public def cylinderUpperTime (s t : unitInterval) : unitInterval :=
  ⟨(1 - (s : ℝ)) * (t : ℝ) + (s : ℝ), by
    constructor
    · exact add_nonneg (mul_nonneg (sub_nonneg.mpr s.2.2) t.2.1) s.2.1
    · nlinarith [s.2.1, s.2.2, t.2.1, t.2.2]⟩

public theorem cylinderUpperTime_pos (s t : unitInterval) (ht : 0 < (t : ℝ)) :
    0 < (cylinderUpperTime s t : ℝ) := by
  change 0 < (1 - (s : ℝ)) * (t : ℝ) + (s : ℝ)
  nlinarith [s.2.1, s.2.2, t.2.2]

@[simp] public theorem cylinderUpperTime_zero (t : unitInterval) : cylinderUpperTime 0 t = t := by
  apply Subtype.ext
  simp [cylinderUpperTime]

@[simp] public theorem cylinderUpperTime_one (t : unitInterval) : cylinderUpperTime 1 t = 1 := by
  apply Subtype.ext
  simp [cylinderUpperTime]

@[simp] public theorem cylinderUpperTime_one_right (s : unitInterval) : cylinderUpperTime s 1 = 1 := by
  apply Subtype.ext
  simp [cylinderUpperTime]

public theorem cylinderUpperTime_continuous :
    Continuous (fun p : unitInterval × unitInterval ↦ cylinderUpperTime p.1 p.2) := by
  apply Continuous.subtype_mk
  fun_prop

public def cylinderUpperRetraction {X : Type} [TopologicalSpace X] (A : Set X) :
    ContinuousMap (cylinderUpperNeighborhood A) X where
  toFun p := p.1.1.2
  continuous_toFun := continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val)

public def cylinderTopToUpper {X : Type} [TopologicalSpace X] (A : Set X) :
    ContinuousMap X (cylinderUpperNeighborhood A) where
  toFun x := ⟨⟨(1, x), Or.inr (Or.inl rfl)⟩, by change (0 : ℝ) < 1; norm_num⟩
  continuous_toFun := ((continuous_const.prodMk continuous_id).subtype_mk _).subtype_mk _

public def cylinderUpperHomotopyPoint {X : Type} (A : Set X) (s : unitInterval)
    (p : cylinderUpperNeighborhood A) : cylinderUpperNeighborhood A :=
  ⟨⟨(cylinderUpperTime s p.1.1.1, p.1.1.2), by
    rcases p.1.2 with h | h | h
    · have he : (p.1.1.1 : ℝ) = 0 := congrArg Subtype.val h
      have hp : 0 < (p.1.1.1 : ℝ) := p.2
      exact False.elim (by linarith)
    · exact Or.inr (Or.inl (by rw [h]; simp))
    · exact Or.inr (Or.inr h)⟩, cylinderUpperTime_pos s _ p.2⟩

public def cylinderUpperHomotopy {X : Type} [TopologicalSpace X] (A : Set X) :
    ContinuousMap.Homotopy (ContinuousMap.id (cylinderUpperNeighborhood A))
      ((cylinderTopToUpper A).comp (cylinderUpperRetraction A)) where
  toFun p := cylinderUpperHomotopyPoint A p.1 p.2
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact (cylinderUpperTime_continuous.comp (continuous_fst.prodMk
      (continuous_fst.comp (continuous_subtype_val.comp
        (continuous_subtype_val.comp continuous_snd))))).prodMk
      (continuous_snd.comp (continuous_subtype_val.comp
        (continuous_subtype_val.comp continuous_snd)))
  map_zero_left p := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext (cylinderUpperTime_zero _) rfl
  map_one_left p := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext (cylinderUpperTime_one _) rfl

public theorem cylinderUpperHomotopy_preserves_lowerSide {X : Type} [TopologicalSpace X]
    (A : Set X) (s : unitInterval) (p : cylinderUpperNeighborhood A)
    (hp : p.1.1 ∈ cylinderLowerSide A) :
    (cylinderUpperHomotopy A (s, p)).1.1 ∈ cylinderLowerSide A :=
  Or.inr ((cylinderUpperNeighborhood_mem_lowerSide_iff A p).mp hp)

end SphereSixComplex
