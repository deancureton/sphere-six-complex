module

public import SphereSixComplex.Topology.EquivariantCoveringHomotopyLift
public import SphereSixComplex.Topology.EquivariantHomotopyEquivalenceDescent

/-!
# Equivariant homotopy equivalences on covering preimages

A deformation of a base region that preserves a smaller subregion lifts uniquely through a
covering.  Its endpoint gives an equivariant homotopy inverse to the inclusion of the two
preimages.
-/

@[expose] public section

noncomputable section

open scoped ContinuousMap
open unitInterval

namespace SphereSixComplex

open Geometry.EquivariantQuotientHomeomorph

universe u v w

variable {G : Type*} [Group G]
variable {E : Type u} {Z : Type v}
  [TopologicalSpace E] [TopologicalSpace Z]

/-- The preimage of a base region under a map. -/
public abbrev coveringRegionPreimage (p : E → Z) (S : Set Z) :=
  {e : E // p e ∈ S}

/-- An invariant map induces an action on every preimage region. -/
@[instance_reducible] public noncomputable def coveringRegionPreimageAction
    (totalAction : MulAction G E) (p : E → Z)
    (p_invariant : ∀ g e, p (actionMap totalAction g e) = p e)
    (S : Set Z) : MulAction G (coveringRegionPreimage p S) where
  smul g e := ⟨actionMap totalAction g e.1, by rw [p_invariant]; exact e.2⟩
  one_smul e := Subtype.ext (one_smul G e.1)
  mul_smul g h e := Subtype.ext (mul_smul g h e.1)

public theorem coveringRegionPreimageAction_continuous
    (totalAction : MulAction G E) (p : E → Z)
    (p_invariant : ∀ g e, p (actionMap totalAction g e) = p e)
    (S : Set Z)
    (totalContinuous : letI := totalAction; ContinuousConstSMul G E) :
    letI := coveringRegionPreimageAction totalAction p p_invariant S
    ContinuousConstSMul G (coveringRegionPreimage p S) := by
  let _ := totalAction
  let _ : ContinuousConstSMul G E := totalContinuous
  let _ := coveringRegionPreimageAction totalAction p p_invariant S
  constructor
  intro g
  change Continuous (fun e : coveringRegionPreimage p S ↦
    (⟨actionMap totalAction g e.1, by rw [p_invariant]; exact e.2⟩ :
      coveringRegionPreimage p S))
  exact ((continuous_const_smul g).comp continuous_subtype_val).subtype_mk _

public def coveringRegionInclusion
    {small big : Set Z} (hsmall : small ⊆ big) : C(small, big) where
  toFun x := ⟨x.1, hsmall x.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- Base deformation data sufficient to lift the inclusion of two covering preimages to an
equivariant homotopy equivalence. -/
public structure CoveringPreimageDeformationData
    (small big : Set Z) (hsmall : small ⊆ big) where
  normalize : C(big, small)
  homotopy : ContinuousMap.Homotopy
    ((coveringRegionInclusion hsmall).comp normalize) (ContinuousMap.id big)
  preservesSmall : ∀ (t : unitInterval) (x : small),
    (homotopy (t, ⟨x.1, hsmall x.2⟩)).1 ∈ small

namespace CoveringPreimageDeformationData

variable {small big : Set Z} {hsmall : small ⊆ big}
variable (D : CoveringPreimageDeformationData small big hsmall)
variable (totalAction : MulAction G E) (p : E → Z)
variable (p_invariant : ∀ g e, p (actionMap totalAction g e) = p e)
variable (cov : IsCoveringMap p)

def bigCoordinate : C(coveringRegionPreimage p big, big) where
  toFun e := ⟨p e.1, e.2⟩
  continuous_toFun := (cov.continuous.comp continuous_subtype_val).subtype_mk _

def reversedBaseHomotopy : C(unitInterval × coveringRegionPreimage p big, Z) where
  toFun te := (D.homotopy.symm (te.1, bigCoordinate p cov te.2)).1
  continuous_toFun := continuous_subtype_val.comp
    (D.homotopy.symm.continuous.comp
      (continuous_fst.prodMk
        ((bigCoordinate p cov).continuous.comp continuous_snd)))

def initialBigLift : C(coveringRegionPreimage p big, E) :=
  ⟨Subtype.val, continuous_subtype_val⟩

theorem reversedBaseHomotopy_zero (e : coveringRegionPreimage p big) :
    D.reversedBaseHomotopy p cov (0, e) = p (initialBigLift p e) := by
  change (D.homotopy.symm (0, bigCoordinate p cov e)).1 = p e.1
  exact congrArg Subtype.val (D.homotopy.symm.map_zero_left (bigCoordinate p cov e))

noncomputable def ambientLift :
    C(unitInterval × coveringRegionPreimage p big, E) :=
  cov.liftHomotopy (D.reversedBaseHomotopy p cov) (initialBigLift p)
    (D.reversedBaseHomotopy_zero p cov)

theorem ambientLift_projects (t : unitInterval)
    (e : coveringRegionPreimage p big) :
    p (D.ambientLift p cov (t, e)) = D.reversedBaseHomotopy p cov (t, e) :=
  congr_fun (cov.liftHomotopy_lifts (D.reversedBaseHomotopy p cov)
    (initialBigLift p) (D.reversedBaseHomotopy_zero p cov)) (t, e)

theorem reversedBaseHomotopy_invariant (g : G) (t : unitInterval)
    (e : coveringRegionPreimage p big) :
    D.reversedBaseHomotopy p cov
        (t, actionMap (coveringRegionPreimageAction totalAction p p_invariant big) g e) =
      D.reversedBaseHomotopy p cov (t, e) := by
  apply congrArg Subtype.val
  apply congrArg D.homotopy.symm
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    exact p_invariant g e.1

theorem ambientLift_equivariant
    (totalContinuous : letI := totalAction; ContinuousConstSMul G E)
    (g : G) (t : unitInterval) (e : coveringRegionPreimage p big) :
    D.ambientLift p cov
        (t, actionMap (coveringRegionPreimageAction totalAction p p_invariant big) g e) =
      actionMap totalAction g (D.ambientLift p cov (t, e)) := by
  exact IsCoveringMap.liftHomotopy_equivariant totalAction
    (coveringRegionPreimageAction totalAction p p_invariant big)
    totalContinuous cov p_invariant
    (D.reversedBaseHomotopy p cov) (initialBigLift p)
    (D.reversedBaseHomotopy_zero p cov)
    (D.reversedBaseHomotopy_invariant totalAction p p_invariant cov)
    (fun g e ↦ rfl) g t e

theorem ambientLift_mem_big (t : unitInterval)
    (e : coveringRegionPreimage p big) :
    p (D.ambientLift p cov (t, e)) ∈ big := by
  rw [D.ambientLift_projects p cov]
  exact (D.homotopy.symm (t, bigCoordinate p cov e)).2

theorem ambientLift_one_mem_small (e : coveringRegionPreimage p big) :
    p (D.ambientLift p cov (1, e)) ∈ small := by
  rw [D.ambientLift_projects p cov]
  simp only [reversedBaseHomotopy, ContinuousMap.Homotopy.symm_apply]
  norm_num
  exact (D.normalize (bigCoordinate p cov e)).2

theorem ambientLift_of_small_mem_small (t : unitInterval)
    (e : coveringRegionPreimage p small) :
    p (D.ambientLift p cov
      (t, (⟨e.1, hsmall e.2⟩ : coveringRegionPreimage p big))) ∈ small := by
  rw [D.ambientLift_projects p cov]
  change (D.homotopy.symm
    (t, ⟨p e.1, hsmall e.2⟩)).1 ∈ small
  exact D.preservesSmall (σ t) ⟨p e.1, e.2⟩

/-- The inclusion of two preimage regions, with its homotopy inverse obtained by lifting the
reversed base deformation. -/
public noncomputable def equivariantHomotopyEquivData
    (totalContinuous : letI := totalAction; ContinuousConstSMul G E) :
    EquivariantHomotopyEquivData
      (coveringRegionPreimageAction totalAction p p_invariant small)
      (coveringRegionPreimageAction totalAction p p_invariant big) where
  toFun :=
    { toFun := fun e ↦ ⟨e.1, hsmall e.2⟩
      continuous_toFun := continuous_subtype_val.subtype_mk _ }
  invFun :=
    { toFun := fun e ↦ ⟨D.ambientLift p cov (1, e), D.ambientLift_one_mem_small p cov e⟩
      continuous_toFun :=
        (D.ambientLift p cov).continuous.comp
          (continuous_const.prodMk continuous_id) |>.subtype_mk _ }
  toFun_equivariant := fun _ _ ↦ rfl
  invFun_equivariant := fun g e ↦ Subtype.ext
    (D.ambientLift_equivariant totalAction p p_invariant cov totalContinuous g 1 e)
  leftInvHomotopy :=
    { toFun := fun te ↦ ⟨D.ambientLift p cov
          (σ te.1, ⟨te.2.1, hsmall te.2.2⟩),
        D.ambientLift_of_small_mem_small p cov (σ te.1) te.2⟩
      continuous_toFun := by fun_prop
      map_zero_left := fun e ↦ by
        apply Subtype.ext
        norm_num
      map_one_left := fun e ↦ by
        apply Subtype.ext
        norm_num
        exact cov.liftHomotopy_zero _ _ _
          (⟨e.1, hsmall e.2⟩ : coveringRegionPreimage p big) }
  rightInvHomotopy :=
    { toFun := fun te ↦ ⟨D.ambientLift p cov (σ te.1, te.2),
        D.ambientLift_mem_big p cov (σ te.1) te.2⟩
      continuous_toFun := by fun_prop
      map_zero_left := fun e ↦ by
        apply Subtype.ext
        norm_num
      map_one_left := fun e ↦ by
        apply Subtype.ext
        norm_num
        exact cov.liftHomotopy_zero _ _ _ e }
  leftInvHomotopy_equivariant := fun g t e ↦ Subtype.ext
    (D.ambientLift_equivariant totalAction p p_invariant cov totalContinuous
      g (σ t) ⟨e.1, hsmall e.2⟩)
  rightInvHomotopy_equivariant := fun g t e ↦ Subtype.ext
    (D.ambientLift_equivariant totalAction p p_invariant cov totalContinuous g (σ t) e)

end CoveringPreimageDeformationData

end SphereSixComplex
