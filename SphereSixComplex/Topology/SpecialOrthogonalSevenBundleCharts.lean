module

public import SphereSixComplex.Topology.SpecialOrthogonalSevenPatchTrivializations
public import Mathlib.Topology.FiberBundle.Trivialization

/-!
# Bundle charts for the `SO(7) → S⁶` Stiefel projection

This file promotes the north and south restricted product homeomorphisms to Mathlib bundle
trivializations of the ambient first-column projection.  Their base sets are exactly the two open
antipode-complement patches, and hence cover the entire six-sphere.
-/

@[expose] public section

noncomputable section

open Bundle Set Topology
open scoped Classical MatrixGroups RealInnerProductSpace Topology

namespace SphereSixComplex.SpecialOrthogonalSevenStiefel

/-- The north-patch product homeomorphism as a trivialization over the subtype base. -/
public def northRestrictedTrivialization :
    Bundle.Trivialization SO6 northTotalBase where
  toOpenPartialHomeomorph := northPatchTrivialization.toOpenPartialHomeomorph
  baseSet := Set.univ
  open_baseSet := isOpen_univ
  source_eq := by simp
  target_eq := by simp
  proj_toFun := by
    intro Q _
    rfl

/-- The south-patch product homeomorphism as a trivialization over the subtype base. -/
public def southRestrictedTrivialization :
    Bundle.Trivialization SO6 southTotalBase where
  toOpenPartialHomeomorph := southPatchTrivialization.toOpenPartialHomeomorph
  baseSet := Set.univ
  open_baseSet := isOpen_univ
  source_eq := by simp
  target_eq := by simp
  proj_toFun := by
    intro Q _
    rfl

public theorem rawSphere_firstColumn_one :
    rawSphere (firstColumn (1 : SO7)) = basisVec 0 := by
  apply WithLp.toLp_injective 2
  rw [toLp_rawSphere]
  apply congr_arg (WithLp.toLp 2)
  ext i
  simp [basisVec, Matrix.one_apply]

public theorem firstColumn_one_mem_northSet :
    firstColumn (1 : SO7) ∈ northSet := by
  rw [northSet]
  intro h
  rw [rawSphere_firstColumn_one] at h
  have h0 := congr_fun h 0
  norm_num [basisVec] at h0

public theorem northSet_nonempty : northSet.Nonempty :=
  ⟨firstColumn (1 : SO7), firstColumn_one_mem_northSet⟩

/-- Antipodal map on the concrete unit sphere model. -/
public def sphereAntipode (x : Sphere6) : Sphere6 :=
  ⟨-x.1, by
    rw [Metric.mem_sphere, dist_zero_right, norm_neg]
    simpa only [Metric.mem_sphere, dist_zero_right] using x.2⟩

public theorem rawSphere_sphereAntipode (x : Sphere6) :
    rawSphere (sphereAntipode x) = -rawSphere x := by
  change
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 7 ↦ ℝ)) (-x.1) =
      -(PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 7 ↦ ℝ)) x.1
  exact map_neg _ _

public theorem rawSphere_southPole :
    rawSphere (sphereAntipode (firstColumn (1 : SO7))) = -basisVec 0 := by
  rw [rawSphere_sphereAntipode, rawSphere_firstColumn_one]

public theorem southPole_mem_southSet :
    sphereAntipode (firstColumn (1 : SO7)) ∈ southSet := by
  rw [southSet]
  intro h
  rw [rawSphere_southPole] at h
  have h0 := congr_fun h 0
  norm_num [basisVec] at h0

public theorem southSet_nonempty : southSet.Nonempty :=
  ⟨sphereAntipode (firstColumn (1 : SO7)), southPole_mem_southSet⟩

/-- Extend the north chart's base subtype back to the ambient sphere. -/
public def northBaseExtendedTrivialization :
    Bundle.Trivialization SO6 (Subtype.val ∘ northTotalBase) :=
  northRestrictedTrivialization.codExtend isOpen_northSet northSet_nonempty

/-- Extend the south chart's base subtype back to the ambient sphere. -/
public def southBaseExtendedTrivialization :
    Bundle.Trivialization SO6 (Subtype.val ∘ southTotalBase) :=
  southRestrictedTrivialization.codExtend isOpen_southSet southSet_nonempty

/-- Direct Mathlib bundle chart for `SO(7) → S⁶` over the north patch. -/
public def northTrivialization : Bundle.Trivialization SO6 firstColumn :=
  northBaseExtendedTrivialization.domExtend
    (isOpen_northSet.preimage continuous_firstColumn)

/-- Direct Mathlib bundle chart for `SO(7) → S⁶` over the south patch. -/
public def southTrivialization : Bundle.Trivialization SO6 firstColumn :=
  southBaseExtendedTrivialization.domExtend
    (isOpen_southSet.preimage continuous_firstColumn)

@[simp] public theorem northTrivialization_baseSet :
    northTrivialization.baseSet = northSet := by
  change northBaseExtendedTrivialization.baseSet = northSet
  rw [northBaseExtendedTrivialization, Bundle.Trivialization.codExtend_baseSet]
  change Subtype.val '' Set.univ = northSet
  ext x
  constructor
  · rintro ⟨y, _, rfl⟩
    exact y.2
  · intro hx
    exact ⟨⟨x, hx⟩, Set.mem_univ _, rfl⟩

@[simp] public theorem southTrivialization_baseSet :
    southTrivialization.baseSet = southSet := by
  change southBaseExtendedTrivialization.baseSet = southSet
  rw [southBaseExtendedTrivialization, Bundle.Trivialization.codExtend_baseSet]
  change Subtype.val '' Set.univ = southSet
  ext x
  constructor
  · rintro ⟨y, _, rfl⟩
    exact y.2
  · intro hx
    exact ⟨⟨x, hx⟩, Set.mem_univ _, rfl⟩

@[simp] public theorem northTrivialization_source :
    northTrivialization.source = firstColumn ⁻¹' northSet := by
  rw [northTrivialization.source_eq, northTrivialization_baseSet]

@[simp] public theorem southTrivialization_source :
    southTrivialization.source = firstColumn ⁻¹' southSet := by
  rw [southTrivialization.source_eq, southTrivialization_baseSet]

@[simp] public theorem northTrivialization_target :
    northTrivialization.target = northSet ×ˢ (Set.univ : Set SO6) := by
  rw [northTrivialization.target_eq, northTrivialization_baseSet]

@[simp] public theorem southTrivialization_target :
    southTrivialization.target = southSet ×ˢ (Set.univ : Set SO6) := by
  rw [southTrivialization.target_eq, southTrivialization_baseSet]

public theorem continuousOn_northTrivialization :
    ContinuousOn northTrivialization.toOpenPartialHomeomorph
      (firstColumn ⁻¹' northSet) := by
  simpa only [northTrivialization_source] using
    northTrivialization.toOpenPartialHomeomorph.continuousOn

public theorem continuousOn_southTrivialization :
    ContinuousOn southTrivialization.toOpenPartialHomeomorph
      (firstColumn ⁻¹' southSet) := by
  simpa only [southTrivialization_source] using
    southTrivialization.toOpenPartialHomeomorph.continuousOn

public theorem continuousOn_northTrivialization_symm :
    ContinuousOn northTrivialization.toOpenPartialHomeomorph.symm
      (northSet ×ˢ (Set.univ : Set SO6)) := by
  simpa only [northTrivialization_target] using
    northTrivialization.toOpenPartialHomeomorph.continuousOn_symm

public theorem continuousOn_southTrivialization_symm :
    ContinuousOn southTrivialization.toOpenPartialHomeomorph.symm
      (southSet ×ˢ (Set.univ : Set SO6)) := by
  simpa only [southTrivialization_target] using
    southTrivialization.toOpenPartialHomeomorph.continuousOn_symm

@[simp] public theorem northTrivialization_left_inv
    (Q : SO7) (hQ : firstColumn Q ∈ northSet) :
    northTrivialization.toOpenPartialHomeomorph.symm
        (northTrivialization Q) = Q := by
  apply northTrivialization.toOpenPartialHomeomorph.left_inv
  rw [northTrivialization_source]
  exact hQ

@[simp] public theorem southTrivialization_left_inv
    (Q : SO7) (hQ : firstColumn Q ∈ southSet) :
    southTrivialization.toOpenPartialHomeomorph.symm
        (southTrivialization Q) = Q := by
  apply southTrivialization.toOpenPartialHomeomorph.left_inv
  rw [southTrivialization_source]
  exact hQ

@[simp] public theorem northTrivialization_right_inv
    (p : Sphere6 × SO6) (hp : p.1 ∈ northSet) :
    northTrivialization
        (northTrivialization.toOpenPartialHomeomorph.symm p) = p := by
  apply northTrivialization.toOpenPartialHomeomorph.right_inv
  rw [northTrivialization_target]
  exact ⟨hp, Set.mem_univ _⟩

@[simp] public theorem southTrivialization_right_inv
    (p : Sphere6 × SO6) (hp : p.1 ∈ southSet) :
    southTrivialization
        (southTrivialization.toOpenPartialHomeomorph.symm p) = p := by
  apply southTrivialization.toOpenPartialHomeomorph.right_inv
  rw [southTrivialization_target]
  exact ⟨hp, Set.mem_univ _⟩

@[simp] public theorem northTrivialization_proj
    (Q : SO7) (hQ : firstColumn Q ∈ northSet) :
    (northTrivialization Q).1 = firstColumn Q := by
  apply northTrivialization.proj_toFun
  rw [northTrivialization_source]
  exact hQ

@[simp] public theorem southTrivialization_proj
    (Q : SO7) (hQ : firstColumn Q ∈ southSet) :
    (southTrivialization Q).1 = firstColumn Q := by
  apply southTrivialization.proj_toFun
  rw [southTrivialization_source]
  exact hQ

@[simp] public theorem firstColumn_northTrivialization_symm
    (p : Sphere6 × SO6) (hp : p.1 ∈ northSet) :
    firstColumn (northTrivialization.toOpenPartialHomeomorph.symm p) = p.1 := by
  apply northTrivialization.proj_symm_apply
  rw [northTrivialization_target]
  exact ⟨hp, Set.mem_univ _⟩

@[simp] public theorem firstColumn_southTrivialization_symm
    (p : Sphere6 × SO6) (hp : p.1 ∈ southSet) :
    firstColumn (southTrivialization.toOpenPartialHomeomorph.symm p) = p.1 := by
  apply southTrivialization.proj_symm_apply
  rw [southTrivialization_target]
  exact ⟨hp, Set.mem_univ _⟩

/-- On its patch, the ambient north chart is the original restricted product homeomorphism. -/
@[simp] public theorem northTrivialization_apply_patch
    (Q : SO7) (hQ : firstColumn Q ∈ northSet) :
    northTrivialization Q =
      ((northPatchTrivialization (⟨Q, hQ⟩ : NorthTotal)).1.1,
        (northPatchTrivialization (⟨Q, hQ⟩ : NorthTotal)).2) := by
  change (if h : firstColumn Q ∈ northSet then
      northBaseExtendedTrivialization ⟨Q, h⟩
    else _) = _
  rw [dite_eq_left hQ]
  rfl

/-- The inverse ambient north chart agrees with the inverse restricted product homeomorphism. -/
@[simp] public theorem northTrivialization_symm_patch (p : NorthPatch × SO6) :
    northTrivialization.toOpenPartialHomeomorph.symm (p.1.1, p.2) =
      (northPatchTrivialization.symm p).1 := by
  let Q : SO7 := (northPatchTrivialization.symm p).1
  have hQ : firstColumn Q ∈ northSet := by
    rw [show firstColumn Q = p.1.1 by
      exact firstColumn_northPatchTrivialization_symm p]
    exact p.1.2
  have hinput : (⟨Q, hQ⟩ : NorthTotal) = northPatchTrivialization.symm p := by
    apply Subtype.ext
    rfl
  have hforward := northTrivialization_apply_patch Q hQ
  rw [hinput, northPatchTrivialization.apply_symm_apply] at hforward
  rw [← hforward]
  exact northTrivialization_left_inv Q hQ

/-- On its patch, the ambient south chart is the original restricted product homeomorphism. -/
@[simp] public theorem southTrivialization_apply_patch
    (Q : SO7) (hQ : firstColumn Q ∈ southSet) :
    southTrivialization Q =
      ((southPatchTrivialization (⟨Q, hQ⟩ : SouthTotal)).1.1,
        (southPatchTrivialization (⟨Q, hQ⟩ : SouthTotal)).2) := by
  change (if h : firstColumn Q ∈ southSet then
      southBaseExtendedTrivialization ⟨Q, h⟩
    else _) = _
  rw [dite_eq_left hQ]
  rfl

/-- The inverse ambient south chart agrees with the inverse restricted product homeomorphism. -/
@[simp] public theorem southTrivialization_symm_patch (p : SouthPatch × SO6) :
    southTrivialization.toOpenPartialHomeomorph.symm (p.1.1, p.2) =
      (southPatchTrivialization.symm p).1 := by
  let Q : SO7 := (southPatchTrivialization.symm p).1
  have hQ : firstColumn Q ∈ southSet := by
    rw [show firstColumn Q = p.1.1 by
      exact firstColumn_southPatchTrivialization_symm p]
    exact p.1.2
  have hinput : (⟨Q, hQ⟩ : SouthTotal) = southPatchTrivialization.symm p := by
    apply Subtype.ext
    rfl
  have hforward := southTrivialization_apply_patch Q hQ
  rw [hinput, southPatchTrivialization.apply_symm_apply] at hforward
  rw [← hforward]
  exact southTrivialization_left_inv Q hQ

/-- The two Mathlib bundle charts cover the entire base sphere. -/
public theorem northTrivialization_baseSet_union_southTrivialization_baseSet :
    northTrivialization.baseSet ∪ southTrivialization.baseSet = Set.univ := by
  rw [northTrivialization_baseSet, southTrivialization_baseSet,
    northSet_union_southSet]

end SphereSixComplex.SpecialOrthogonalSevenStiefel
