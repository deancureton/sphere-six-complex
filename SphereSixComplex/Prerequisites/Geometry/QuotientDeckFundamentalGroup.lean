module

public import SphereSixComplex.Prerequisites.Geometry.Quotient
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.Topology.Homotopy.Lifting

/-!
# Fundamental-group classes from deck paths

For a path-connected space with a group action, a path from a point to one of its deck translates
projects to a based loop in the orbit quotient.  This elementary construction is shared by the
outer triangle-group quotient and the two finite affine elliptic filling quotients.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry

variable {M G : Type*} [TopologicalSpace M] [Group G] [MulAction G M]







/-- Regard a based path as its fundamental-group class. -/
public def pathLoopClass {Y : Type*} [TopologicalSpace Y] {y : Y}
    (L : Path y y) : FundamentalGroup Y y :=
  Path.Homotopic.Quotient.mk L


/-- Transporting a local loop back along a path is represented by whiskering the loop with that
path and its reverse. -/
public def whiskeredLoopClass {X : Type*} [TopologicalSpace X] {x y : X}
    (W : Path x y) (L : Path y y) : FundamentalGroup X x :=
  pathLoopClass (W.trans (L.trans W.symm))

/-- If the far endpoint of a whisker is identified with its starting point, Mathlib's reversed
path-composition convention writes geometric whiskering as inverse conjugation.  This is the
conversion needed when a paper presentation uses the usual left-to-right loop convention. -/
public theorem whiskeredLoopClass_eq_conjugate_cast
    {X : Type*} [TopologicalSpace X] {x y : X}
    (W : Path x y) (L : Path y y) (h : y = x) :
    whiskeredLoopClass W L =
      (pathLoopClass (W.cast rfl h.symm))⁻¹ *
        pathLoopClass (L.cast h.symm h.symm) *
        pathLoopClass (W.cast rfl h.symm) := by
  subst h
  simp only [whiskeredLoopClass, pathLoopClass,
    Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm]
  rfl

public theorem fundamentalGroupMulEquivOfPath_symm_apply_eq_whiskeredLoopClass
    {X : Type*} [TopologicalSpace X] {x y : X}
    (W : Path x y) (L : Path y y) :
    (FundamentalGroup.fundamentalGroupMulEquivOfPath W).symm (pathLoopClass L) =
      whiskeredLoopClass W L := by
  rfl

















/-! ## Surjectivity through quotient coverings -/



/-- Project a chosen path to a deck translate through an arbitrary quotient covering. -/
public def projectedQuotientDeckPath {X : Type*} [TopologicalSpace X] {f : M → X}
    (hf : IsQuotientCoveringMap f G) (x : M) (g : G) (P : Path x (g • x)) :
    Path (f x) (f x) :=
  (P.map hf.continuous).cast rfl (hf.map_smul g).symm

/-- A projected deck path has the prescribed monodromy label. -/
public theorem fundamentalGroupToMulOpposite_projectedQuotientDeckPath
    {X : Type*} [TopologicalSpace X] {f : M → X}
    (hf : IsQuotientCoveringMap f G) (x : M) (g : G) (P : Path x (g • x)) :
    hf.fundamentalGroupToMulOpposite (⟨x, rfl⟩ : f ⁻¹' {f x})
        (pathLoopClass (projectedQuotientDeckPath hf x g P)) = MulOpposite.op g := by
  rw [hf.fundamentalGroupToMulOpposite_apply_eq_Iff]
  let e : f ⁻¹' {f x} := ⟨x, rfl⟩
  let e' : f ⁻¹' {f x} := ⟨g • x, hf.map_smul g⟩
  have hm : hf.isCoveringMap.monodromy
        (pathLoopClass (projectedQuotientDeckPath hf x g P)) e = e' :=
    hf.isCoveringMap.monodromy_eq_of_map_eq (Path.Homotopic.Quotient.mk P) (by rfl)
  exact congrArg Subtype.val hm.symm




end SphereSixComplex.Geometry
