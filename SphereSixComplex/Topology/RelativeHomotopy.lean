module

public import SphereSixComplex.Topology.CollarHomotopyExtension

/-!
# Relative strictification of deformation homotopies

This file proves the relative part of the standard cofibration argument.  The key auxiliary
fact is that the homotopy-extension property is stable under taking a product with the unit
interval.  A rectangular homotopy then changes an ordinary deformation retraction into one
whose deformation homotopy is stationary on the included subspace.
-/

@[expose] public section

noncomputable section

open CategoryTheory ContinuousMap Function Set TopologicalSpace Topology
open unitInterval
open scoped Topology

namespace SphereSixComplex

universe u

variable {A X : Type u} [TopologicalSpace A] [TopologicalSpace X]

/-- Product of a specified map with the identity of the unit interval. -/
public def unitIntervalProdMap (i : C(A, X)) : C(unitInterval × A, unitInterval × X) :=
  ⟨fun p ↦ (p.1, i p.2), continuous_fst.prodMk (i.continuous.comp continuous_snd)⟩

@[simp]
public theorem unitIntervalProdMap_apply (i : C(A, X)) (p : unitInterval × A) :
    unitIntervalProdMap i p = (p.1, i p.2) :=
  rfl

/-- The homotopy-extension property is stable under taking a product with the compact unit
interval.  The proof curries the interval variable into the compact-open mapping space, invokes
HEP there, and then evaluates the resulting family of paths. -/
public theorem HomotopyExtensionProperty.unitInterval_prod
    {i : C(A, X)} (hep : HomotopyExtensionProperty i) :
    HomotopyExtensionProperty (unitIntervalProdMap i) := by
  refine ⟨?_⟩
  intro Y _ f h₁ H
  let fSwap : C(X × unitInterval, Y) :=
    ⟨fun p ↦ f (p.2, p.1), f.continuous.comp continuous_swap⟩
  let fC : C(X, C(unitInterval, Y)) := ContinuousMap.curry fSwap
  let h₁Swap : C(A × unitInterval, Y) :=
    ⟨fun p ↦ h₁ (p.2, p.1), h₁.continuous.comp continuous_swap⟩
  let h₁C : C(A, C(unitInterval, Y)) := ContinuousMap.curry h₁Swap
  let HCMap : C(unitInterval × A, C(unitInterval, Y)) :=
    ContinuousMap.curry
      ⟨fun p : (unitInterval × A) × unitInterval ↦ H (p.1.1, (p.2, p.1.2)),
        H.continuous.comp
          ((continuous_fst.fst).prodMk (continuous_snd.prodMk continuous_fst.snd))⟩
  let HC : ContinuousMap.Homotopy (fC.comp i) h₁C :=
    { toContinuousMap := HCMap
      map_zero_left := fun a ↦ by
        ext t
        exact H.map_zero_left (t, a)
      map_one_left := fun a ↦ by
        ext t
        exact H.map_one_left (t, a) }
  obtain ⟨gC, FC, hFC⟩ := hep.extend fC HC
  let gSwap : C(X × unitInterval, Y) := ContinuousMap.uncurry gC
  let g : C(unitInterval × X, Y) :=
    gSwap.comp ⟨Prod.swap, continuous_swap⟩
  let F : ContinuousMap.Homotopy f g :=
    { toFun := fun p ↦ FC (p.1, p.2.2) p.2.1
      continuous_toFun := continuous_eval.comp
        ((FC.continuous.comp (continuous_fst.prodMk continuous_snd.snd)).prodMk
          continuous_snd.fst)
      map_zero_left := fun p ↦ by
        change FC (0, p.2) p.1 = fC p.2 p.1
        exact congrArg (fun k : C(unitInterval, Y) ↦ k p.1)
          (FC.map_zero_left p.2)
      map_one_left := fun p ↦ by
        change FC (1, p.2) p.1 = gC p.2 p.1
        exact congrArg (fun k : C(unitInterval, Y) ↦ k p.1)
          (FC.map_one_left p.2) }
  refine ⟨g, F, ?_⟩
  intro t p
  change FC (t, i p.2) p.1 = H (t, p)
  have hmaps := hFC t p.2
  exact congrArg (fun k : C(unitInterval, Y) ↦ k p.1) hmaps

/-- A fixed-parameter slice of a map defined on a cylinder. -/
public def cylinderSlice {Y : Type u} [TopologicalSpace Y]
    (f : C(unitInterval × X, Y)) (t : unitInterval) : C(X, Y) :=
  f.comp ⟨fun x ↦ (t, x), continuous_const.prodMk continuous_id⟩

@[simp]
public theorem cylinderSlice_apply {Y : Type u} [TopologicalSpace Y]
    (f : C(unitInterval × X, Y)) (t : unitInterval) (x : X) :
    cylinderSlice f t x = f (t, x) :=
  rfl

namespace ContinuousMap.Homotopy

variable {Y : Type u} [TopologicalSpace Y]
variable {f₀ f₁ : C(unitInterval × X, Y)}

/-- Restrict a homotopy between cylinder maps to one vertical side of the cylinder. -/
public def cylinderSide (F : ContinuousMap.Homotopy f₀ f₁) (t : unitInterval) :
    ContinuousMap.Homotopy (cylinderSlice f₀ t) (cylinderSlice f₁ t) where
  toFun p := F (p.1, (t, p.2))
  continuous_toFun := F.continuous.comp
    (continuous_fst.prodMk (continuous_const.prodMk continuous_snd))
  map_zero_left x := F.map_zero_left (t, x)
  map_one_left x := F.map_one_left (t, x)

@[simp]
public theorem cylinderSide_apply (F : ContinuousMap.Homotopy f₀ f₁)
    (t u : unitInterval) (x : X) :
    ContinuousMap.Homotopy.cylinderSide F t (u, x) = F (u, (t, x)) :=
  rfl

end ContinuousMap.Homotopy

/-- Regard a continuous map out of a cylinder as a homotopy between its endpoint slices. -/
public def cylinderMapHomotopy {Y : Type u} [TopologicalSpace Y]
    (f : C(unitInterval × X, Y)) :
    ContinuousMap.Homotopy (cylinderSlice f 0) (cylinderSlice f 1) where
  toContinuousMap := f
  map_zero_left _ := rfl
  map_one_left _ := rfl

@[simp]
public theorem cylinderMapHomotopy_apply {Y : Type u} [TopologicalSpace Y]
    (f : C(unitInterval × X, Y)) (p : unitInterval × X) :
    cylinderMapHomotopy f p = f p :=
  rfl

/-! ## The rectangular relative-homotopy construction -/

/-- Fold the unit interval at its midpoint: `t ↦ |2t - 1|`. -/
public def unitIntervalFold (t : unitInterval) : unitInterval :=
  ⟨|2 * (t : ℝ) - 1|, by
    constructor
    · exact abs_nonneg _
    · rw [abs_le]
      constructor <;> linarith [t.2.1, t.2.2]⟩

@[simp]
public theorem unitIntervalFold_zero : unitIntervalFold 0 = 1 := by
  apply Subtype.ext
  norm_num [unitIntervalFold]

@[simp]
public theorem unitIntervalFold_one : unitIntervalFold 1 = 1 := by
  apply Subtype.ext
  norm_num [unitIntervalFold]

public theorem continuous_unitIntervalFold : Continuous unitIntervalFold := by
  apply Continuous.subtype_mk
  fun_prop

/-- During the rectangular homotopy, raise the folded time coordinate towards `1`. -/
public def rectangleHomotopyTime (p : unitInterval × unitInterval) : unitInterval :=
  max (unitIntervalFold p.2) p.1

@[simp]
public theorem rectangleHomotopyTime_zero (t : unitInterval) :
    rectangleHomotopyTime (0, t) = unitIntervalFold t := by
  exact max_eq_left bot_le

@[simp]
public theorem rectangleHomotopyTime_one (t : unitInterval) :
    rectangleHomotopyTime (1, t) = 1 := by
  exact max_eq_right (unitIntervalFold t).2.2

@[simp]
public theorem rectangleHomotopyTime_left_end (u : unitInterval) :
    rectangleHomotopyTime (u, 0) = 1 := by
  rw [rectangleHomotopyTime, unitIntervalFold_zero]
  exact max_eq_left u.2.2

@[simp]
public theorem rectangleHomotopyTime_right_end (u : unitInterval) :
    rectangleHomotopyTime (u, 1) = 1 := by
  rw [rectangleHomotopyTime, unitIntervalFold_one]
  exact max_eq_left u.2.2

public theorem continuous_rectangleHomotopyTime : Continuous rectangleHomotopyTime := by
  exact (continuous_unitIntervalFold.comp continuous_snd).max continuous_fst

namespace DeformationRetractData

variable {i : C(A, X)} (D : DeformationRetractData i)

/-- The idempotent self-map obtained by retracting and including again. -/
public abbrev retractMap : C(X, X) := i.comp D.retraction

@[simp]
public theorem retractMap_apply (x : X) : D.retractMap x = i (D.retraction x) :=
  rfl

@[simp]
public theorem retractMap_inclusion (a : A) : D.retractMap (i a) = i a := by
  change i (D.retraction (i a)) = i a
  have ha := ContinuousMap.congr_fun D.retract a
  change D.retraction (i a) = a at ha
  rw [ha]

public theorem retractMap_idempotent : D.retractMap.comp D.retractMap = D.retractMap := by
  ext x
  exact D.retractMap_inclusion (D.retraction x)

/-- Restrict the deformation homotopy to the image of its retraction.  It is a loop based at the
retraction map, even when the original deformation homotopy is not stationary there. -/
public def imageLoop : ContinuousMap.Homotopy D.retractMap D.retractMap where
  toFun p := D.homotopy (p.1, D.retractMap p.2)
  continuous_toFun := D.homotopy.continuous.comp
    (continuous_fst.prodMk (D.retractMap.continuous.comp continuous_snd))
  map_zero_left x := by
    change D.homotopy (0, D.retractMap x) = D.retractMap x
    calc
      D.homotopy (0, D.retractMap x) = D.retractMap (D.retractMap x) :=
        D.homotopy.map_zero_left (D.retractMap x)
      _ = D.retractMap x := ContinuousMap.congr_fun D.retractMap_idempotent x
  map_one_left x := by
    change D.homotopy (1, D.retractMap x) = D.retractMap x
    exact D.homotopy.map_one_left (D.retractMap x)

/-- A homotopy from the identity to the retraction map which first reverses the given deformation
and then traverses its restriction to the retract.  On the included subspace it is exactly the
folded path `t ↦ D.homotopy (|2t-1|, i a)`. -/
public abbrev rectangularBase :
    ContinuousMap.Homotopy (ContinuousMap.id X) D.retractMap :=
  D.homotopy.symm.trans D.imageLoop

public theorem rectangularBase_inclusion (t : unitInterval) (a : A) :
    D.rectangularBase (t, i a) = D.homotopy (unitIntervalFold t, i a) := by
  rw [rectangularBase, ContinuousMap.Homotopy.trans_apply]
  split_ifs with ht
  · change D.homotopy
      ((σ ⟨2 * (t : ℝ), _⟩), i a) = D.homotopy (unitIntervalFold t, i a)
    congr 2
    apply Subtype.ext
    simp only [unitIntervalFold, unitInterval.coe_symm_eq]
    rw [abs_of_nonpos]
    · ring
    · linarith
  · change D.homotopy
      (⟨2 * (t : ℝ) - 1, _⟩, D.retractMap (i a)) =
        D.homotopy (unitIntervalFold t, i a)
    rw [D.retractMap_inclusion]
    congr 2
    apply Subtype.ext
    simp only [unitIntervalFold]
    rw [abs_of_nonneg]
    linarith

/-- The stationary map on the cylinder over the included subspace. -/
public def inclusionCylinderConstant : C(unitInterval × A, X) :=
  i.comp ContinuousMap.snd

@[simp]
public theorem inclusionCylinderConstant_apply (p : unitInterval × A) :
    inclusionCylinderConstant (i := i) p = i p.2 :=
  rfl

/-- The central rectangle used to make a deformation homotopy relative to the included
subspace.  At rectangle time zero it is the restriction of `rectangularBase`; at rectangle time
one the whole included cylinder is stationary.  Along both vertical sides it is stationary for
every rectangle time. -/
public def subspaceRectangle : ContinuousMap.Homotopy
    (D.rectangularBase.toContinuousMap.comp (unitIntervalProdMap i))
    (inclusionCylinderConstant (i := i)) where
  toFun p := D.homotopy
    (rectangleHomotopyTime (p.1, p.2.1), i p.2.2)
  continuous_toFun := D.homotopy.continuous.comp
    ((continuous_rectangleHomotopyTime.comp
        (continuous_fst.prodMk continuous_snd.fst)).prodMk
      (i.continuous.comp continuous_snd.snd))
  map_zero_left p := by
    change D.homotopy (rectangleHomotopyTime (0, p.1), i p.2) =
      D.rectangularBase (p.1, i p.2)
    rw [rectangleHomotopyTime_zero, D.rectangularBase_inclusion]
  map_one_left p := by
    change D.homotopy (rectangleHomotopyTime (1, p.1), i p.2) = i p.2
    rw [rectangleHomotopyTime_one]
    exact D.homotopy.map_one_left (i p.2)

@[simp]
public theorem subspaceRectangle_left_end (u : unitInterval) (a : A) :
    D.subspaceRectangle (u, (0, a)) = i a := by
  change D.homotopy (rectangleHomotopyTime (u, 0), i a) = i a
  rw [rectangleHomotopyTime_left_end]
  exact D.homotopy.map_one_left (i a)

@[simp]
public theorem subspaceRectangle_right_end (u : unitInterval) (a : A) :
    D.subspaceRectangle (u, (1, a)) = i a := by
  change D.homotopy (rectangleHomotopyTime (u, 1), i a) = i a
  rw [rectangleHomotopyTime_right_end]
  exact D.homotopy.map_one_left (i a)

/-- HEP makes every ordinary deformation retraction strong.  This is the relative part of the
standard theorem that an acyclic cofibration is a strong deformation retract. -/
public theorem strongDeformationRetractData_of_hep (D : DeformationRetractData i)
    (hep : HomotopyExtensionProperty i) :
    Nonempty (TopCat.StrongDeformationRetractData (TopCat.ofHom i)) := by
  obtain ⟨g, F, hF⟩ :=
    hep.unitInterval_prod.extend (D.rectangularBase).toContinuousMap D.subspaceRectangle
  let g₀ : C(X, X) := cylinderSlice g 0
  let g₁ : C(X, X) := cylinderSlice g 1
  have hbase₀ : cylinderSlice (D.rectangularBase).toContinuousMap 0 =
      ContinuousMap.id X := by
    ext x
    exact (D.rectangularBase).map_zero_left x
  have hbase₁ : cylinderSlice (D.rectangularBase).toContinuousMap 1 =
      D.retractMap := by
    ext x
    exact (D.rectangularBase).map_one_left x
  let leftHomotopy : ContinuousMap.Homotopy (ContinuousMap.id X) g₀ :=
    (ContinuousMap.Homotopy.cylinderSide F 0).cast hbase₀ rfl
  let middleHomotopy : ContinuousMap.Homotopy g₀ g₁ :=
    cylinderMapHomotopy g
  let rightHomotopy : ContinuousMap.Homotopy D.retractMap g₁ :=
    (ContinuousMap.Homotopy.cylinderSide F 1).cast hbase₁ rfl
  let leftRelative : ContinuousMap.HomotopyRel
      (ContinuousMap.id X) g₀ (range i) :=
    { toHomotopy := leftHomotopy
      prop' := fun u x hx ↦ by
        obtain ⟨a, rfl⟩ := hx
        change F (u, (0, i a)) = i a
        calc
          F (u, (0, i a)) = D.subspaceRectangle (u, (0, a)) := hF u (0, a)
          _ = i a := D.subspaceRectangle_left_end u a }
  let middleRelative : ContinuousMap.HomotopyRel g₀ g₁ (range i) :=
    { toHomotopy := middleHomotopy
      prop' := fun t x hx ↦ by
        obtain ⟨a, rfl⟩ := hx
        change g (t, i a) = g₀ (i a)
        have hgt : g (t, i a) = i a := by
          calc
            g (t, i a) = F (1, (t, i a)) := (F.map_one_left (t, i a)).symm
            _ = D.subspaceRectangle (1, (t, a)) := hF 1 (t, a)
            _ = i a := (D.subspaceRectangle).map_one_left (t, a)
        have hg₀ : g₀ (i a) = i a := by
          change g (0, i a) = i a
          calc
            g (0, i a) = F (1, (0, i a)) := (F.map_one_left (0, i a)).symm
            _ = D.subspaceRectangle (1, (0, a)) := hF 1 (0, a)
            _ = i a := (D.subspaceRectangle).map_one_left (0, a)
        exact hgt.trans hg₀.symm }
  let rightRelative : ContinuousMap.HomotopyRel D.retractMap g₁ (range i) :=
    { toHomotopy := rightHomotopy
      prop' := fun u x hx ↦ by
        obtain ⟨a, rfl⟩ := hx
        change F (u, (1, i a)) = D.retractMap (i a)
        rw [D.retractMap_inclusion]
        calc
          F (u, (1, i a)) = D.subspaceRectangle (u, (1, a)) := hF u (1, a)
          _ = i a := D.subspaceRectangle_right_end u a }
  let relativeBase : ContinuousMap.HomotopyRel
      (ContinuousMap.id X) D.retractMap (range i) :=
    (leftRelative.trans middleRelative).trans rightRelative.symm
  let relativeDeformation : ContinuousMap.HomotopyRel
      D.retractMap (ContinuousMap.id X) (range i) :=
    relativeBase.symm
  let D' : DeformationRetractData i :=
    { retraction := D.retraction
      retract := D.retract
      homotopy := relativeDeformation.toHomotopy }
  refine ⟨D'.toStrong ?_⟩
  intro t a
  change relativeDeformation (t, i a) = i a
  calc
    relativeDeformation (t, i a) = D.retractMap (i a) :=
      relativeDeformation.prop t (i a) ⟨a, rfl⟩
    _ = i a := D.retractMap_inclusion a

end DeformationRetractData

/-- A map which has HEP and is a homotopy equivalence is the inclusion of a strong deformation
retract.  In particular, its deformation homotopy is pointwise fixed on the specified map, which
is exactly the coherence required for descent through a pushout. -/
public theorem HomotopyExtensionProperty.exists_strongDeformationRetractData
    {i : C(A, X)} (hep : HomotopyExtensionProperty i)
    (hi : IsHomotopyEquivalence i) :
    Nonempty (TopCat.StrongDeformationRetractData (TopCat.ofHom i)) := by
  obtain ⟨D⟩ := hep.exists_deformationRetractData hi
  exact D.strongDeformationRetractData_of_hep hep

end SphereSixComplex
