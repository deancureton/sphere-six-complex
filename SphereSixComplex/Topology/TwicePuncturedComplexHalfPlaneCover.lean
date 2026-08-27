module

public import SphereSixComplex.Topology.PuncturedAffineHalfPlaneRadial
public import SphereSixComplex.Topology.PuncturedComplexFundamentalGroup
public import Mathlib.Analysis.Complex.Convex

/-!
# A marked two-open cover of the twice-punctured complex plane

The vertical half-planes `re < 2 / 3` and `1 / 3 < re` cover `ℂ \ {0, 1}`.  The first contains
only the puncture at zero, the second only the puncture at one, and their overlap is the convex
vertical strip `1 / 3 < re < 2 / 3`.  This is the geometric input for a based van Kampen
calculation with the two actual meridians.
-/

@[expose] public section

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace SphereSixComplex.Topology

/-- The complex plane with the two marked points zero and one removed. -/
public abbrev TwicePuncturedComplex := ↥(({0, 1} : Set ℂ)ᶜ)

/-- The left member of the marked cover.  Its only missing point in the ambient half-plane is
zero. -/
public def twicePuncturedComplexLeft : Set TwicePuncturedComplex :=
  {z | z.1.re < 2 / 3}

/-- The right member of the marked cover.  Its only missing point in the ambient half-plane is
one. -/
public def twicePuncturedComplexRight : Set TwicePuncturedComplex :=
  {z | 1 / 3 < z.1.re}

/-- The overlap of the two marked half-planes. -/
public def twicePuncturedComplexOverlap : Set TwicePuncturedComplex :=
  twicePuncturedComplexLeft ∩ twicePuncturedComplexRight

/-- The common real basepoint of the two tangent meridian circles. -/
public def twicePuncturedComplexBasepoint : TwicePuncturedComplex :=
  ⟨(2 : ℂ)⁻¹, by norm_num⟩

public theorem twicePuncturedComplexLeft_isOpen :
    IsOpen twicePuncturedComplexLeft := by
  exact isOpen_lt
    (Complex.continuous_re.comp continuous_subtype_val) continuous_const

public theorem twicePuncturedComplexRight_isOpen :
    IsOpen twicePuncturedComplexRight := by
  exact isOpen_lt continuous_const
    (Complex.continuous_re.comp continuous_subtype_val)

public theorem twicePuncturedComplexOverlap_isOpen :
    IsOpen twicePuncturedComplexOverlap :=
  twicePuncturedComplexLeft_isOpen.inter twicePuncturedComplexRight_isOpen

/-- The two half-planes cover every point of the twice-punctured plane. -/
public theorem twicePuncturedComplexLeft_union_right :
    twicePuncturedComplexLeft ∪ twicePuncturedComplexRight = Set.univ := by
  ext z
  simp only [twicePuncturedComplexLeft, twicePuncturedComplexRight,
    mem_union, mem_setOf_eq, mem_univ, iff_true]
  by_cases hz : z.1.re < 2 / 3
  · exact Or.inl hz
  · right
    have hz' : 2 / 3 ≤ z.1.re := le_of_not_gt hz
    norm_num at hz' ⊢
    linarith

public theorem twicePuncturedComplexBasepoint_mem_left :
    twicePuncturedComplexBasepoint ∈ twicePuncturedComplexLeft := by
  norm_num [twicePuncturedComplexBasepoint, twicePuncturedComplexLeft]

public theorem twicePuncturedComplexBasepoint_mem_right :
    twicePuncturedComplexBasepoint ∈ twicePuncturedComplexRight := by
  norm_num [twicePuncturedComplexBasepoint, twicePuncturedComplexRight]

public theorem twicePuncturedComplexBasepoint_mem_overlap :
    twicePuncturedComplexBasepoint ∈ twicePuncturedComplexOverlap :=
  ⟨twicePuncturedComplexBasepoint_mem_left,
    twicePuncturedComplexBasepoint_mem_right⟩

/-- The ordinary open vertical strip underlying the overlap. -/
public def complexOpenVerticalStrip : Set ℂ :=
  {z | 1 / 3 < z.re ∧ z.re < 2 / 3}

public theorem complexOpenVerticalStrip_convex :
    Convex ℝ complexOpenVerticalStrip := by
  exact (convex_halfSpace_re_gt (1 / 3 : ℝ)).inter
    (convex_halfSpace_re_lt (2 / 3 : ℝ))

public theorem complexOpenVerticalStrip_nonempty :
    complexOpenVerticalStrip.Nonempty := by
  refine ⟨(1 / 2 : ℂ), ?_⟩
  norm_num [complexOpenVerticalStrip]

/-- Points of the open strip automatically avoid both punctures. -/
public theorem complexOpenVerticalStrip_mem_twicePunctured
    (z : complexOpenVerticalStrip) : z.1 ∈ ({0, 1} : Set ℂ)ᶜ := by
  simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
  constructor
  · intro hz
    have h := z.2.1
    rw [hz] at h
    norm_num at h
  · intro hz
    have h := z.2.2
    rw [hz] at h
    norm_num at h

/-- The cover overlap is literally the open vertical strip, with the redundant puncture
conditions removed. -/
public def twicePuncturedComplexOverlapHomeomorphStrip :
    twicePuncturedComplexOverlap ≃ₜ complexOpenVerticalStrip where
  toFun z := ⟨z.1.1, ⟨z.2.2, z.2.1⟩⟩
  invFun z :=
    ⟨⟨z.1, complexOpenVerticalStrip_mem_twicePunctured z⟩, ⟨z.2.2, z.2.1⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- The overlap is contractible, so it contributes no relation in based van Kampen. -/
public theorem twicePuncturedComplexOverlap_contractible :
    ContractibleSpace twicePuncturedComplexOverlap := by
  letI : ContractibleSpace complexOpenVerticalStrip :=
    complexOpenVerticalStrip_convex.contractibleSpace
      complexOpenVerticalStrip_nonempty
  exact twicePuncturedComplexOverlapHomeomorphStrip.contractibleSpace

/-- In particular, the overlap is path-connected. -/
public theorem twicePuncturedComplexOverlap_isPathConnected :
    IsPathConnected twicePuncturedComplexOverlap := by
  letI : ContractibleSpace twicePuncturedComplexOverlap :=
    twicePuncturedComplexOverlap_contractible
  exact isPathConnected_iff_pathConnectedSpace.mpr inferInstance

/-! ## Homotopy types of the two pieces -/

/-- The once-punctured complex plane as a set. -/
public abbrev puncturedComplexSet : Set ℂ := {z | z ≠ 0}

/-- The whole punctured plane is a radial domain about every positive circle. -/
public theorem puncturedComplex_radial {s : ℝ} (hs : 0 < s) :
    ComplexRadialDomain puncturedComplexSet s where
  radius_pos := hs
  nonzero x := x.2
  circle_mem z hz := by
    intro h
    rw [h, norm_zero] at hz
    exact hs.ne' hz.symm
  interpolate_mem t x := by
    have hnorm : 0 < ‖x.1‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr x.2)
    have hscale : 0 < (t : ℝ) + (1 - (t : ℝ)) * s * ‖x.1‖⁻¹ := by
      by_cases ht : (t : ℝ) = 0
      · simp [ht, hs, hnorm]
      · exact add_pos_of_pos_of_nonneg
          (lt_of_le_of_ne t.2.1 (Ne.symm ht))
          (mul_nonneg (mul_nonneg (sub_nonneg.mpr t.2.2) hs.le) hnorm.le)
    exact smul_ne_zero hscale.ne' x.2

/-- Forgetting the redundant puncture at one identifies the left cover piece with the punctured
left half-plane. -/
public def twicePuncturedComplexLeftHomeomorph :
    twicePuncturedComplexLeft ≃ₜ puncturedComplexLeftHalfPlane (2 / 3) where
  toFun z := ⟨z.1.1, by
    have hz := z.1.2
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] at hz
    exact ⟨hz.1, z.2⟩⟩
  invFun z := ⟨⟨z.1, by
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    refine ⟨z.2.1, ?_⟩
    intro hz
    have h := z.2.2
    rw [hz] at h
    norm_num at h⟩, z.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    by fun_prop
  continuous_invFun :=
    by fun_prop

/-- Forgetting the redundant puncture at zero identifies the right cover piece with the
punctured right half-plane. -/
public def twicePuncturedComplexRightHomeomorph :
    twicePuncturedComplexRight ≃ₜ puncturedComplexRightHalfPlane (1 / 3) where
  toFun z := ⟨z.1.1, by
    have hz := z.1.2
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] at hz
    exact ⟨hz.2, z.2⟩⟩
  invFun z := ⟨⟨z.1, by
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    refine ⟨?_, z.2.1⟩
    intro hz
    have h := z.2.2
    rw [hz] at h
    norm_num at h⟩, z.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    by fun_prop
  continuous_invFun :=
    by fun_prop

/-- Radial normalization makes the left cover piece homotopy equivalent to the once-punctured
plane.  The selected constants keep the common basepoint fixed. -/
public def twicePuncturedComplexLeftHomotopyEquivPuncturedComplex :
    twicePuncturedComplexLeft ≃ₕ PuncturedComplex :=
  twicePuncturedComplexLeftHomeomorph.toHomotopyEquiv.trans
    ((puncturedComplexLeftHalfPlane_radial (s := 1 / 2) (c := 2 / 3)
        (by norm_num) (by norm_num)).homotopyEquivOfSubset
      (puncturedComplex_radial (s := 1 / 2) (by norm_num))
      (fun _ hz ↦ hz.1)).symm

/-- Reflection about `1 / 2`, followed by radial normalization, gives the corresponding
homotopy equivalence for the right cover piece. -/
public def twicePuncturedComplexRightHomotopyEquivPuncturedComplex :
    twicePuncturedComplexRight ≃ₕ PuncturedComplex :=
  twicePuncturedComplexRightHomeomorph.toHomotopyEquiv.trans
    (puncturedComplexRightHalfPlaneHomeomorphLeft (1 / 3)).toHomotopyEquiv |>.trans
      (((puncturedComplexLeftHalfPlane_radial (s := 1 / 2) (c := 1 - 1 / 3)
          (by norm_num) (by norm_num)).homotopyEquivOfSubset
        (puncturedComplex_radial (s := 1 / 2) (by norm_num))
        (fun _ hz ↦ hz.1)).symm)

@[simp]
public theorem twicePuncturedComplexLeftHomotopyEquivPuncturedComplex_basepoint :
    twicePuncturedComplexLeftHomotopyEquivPuncturedComplex
        ⟨twicePuncturedComplexBasepoint,
          twicePuncturedComplexBasepoint_mem_left⟩ =
      (⟨(2 : ℂ)⁻¹, by norm_num⟩ : PuncturedComplex) := by
  apply Subtype.ext
  rfl

@[simp]
public theorem twicePuncturedComplexRightHomotopyEquivPuncturedComplex_basepoint :
    twicePuncturedComplexRightHomotopyEquivPuncturedComplex
        ⟨twicePuncturedComplexBasepoint,
          twicePuncturedComplexBasepoint_mem_right⟩ =
      (⟨(2 : ℂ)⁻¹, by norm_num⟩ : PuncturedComplex) := by
  apply Subtype.ext
  norm_num [twicePuncturedComplexRightHomotopyEquivPuncturedComplex,
    twicePuncturedComplexRightHomeomorph, twicePuncturedComplexBasepoint,
    puncturedComplexRightHalfPlaneHomeomorphLeft,
    ContinuousMap.HomotopyEquiv.trans, Homeomorph.toHomotopyEquiv,
    ContinuousMap.HomotopyEquiv.symm, ComplexRadialDomain.homotopyEquivOfSubset,
    ComplexRadialDomain.inclusion]

end SphereSixComplex.Topology
