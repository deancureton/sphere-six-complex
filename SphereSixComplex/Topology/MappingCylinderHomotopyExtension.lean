module

public import SphereSixComplex.Topology.MappingCylinderGluing
public import SphereSixComplex.Topology.RelativeHomotopy

/-!
# Homotopy extension at the free end of a mapping cylinder

The free end of a mapping cylinder is a cofibration.  The construction below retracts the
parameter square onto its bottom and free-end edges, then descends the resulting extension
through the mapping-cylinder pushout.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open ContinuousMap Function TopologicalSpace Topology

namespace SphereSixComplex

universe u

namespace TopCat

/-- Distance from a unit-interval point to the free endpoint. -/
public def mappingCylinderFreeDistance (t : unitInterval) : ℝ :=
  1 - (t : ℝ)

public theorem mappingCylinderFreeDistance_nonneg (t : unitInterval) :
    0 ≤ mappingCylinderFreeDistance t :=
  sub_nonneg.mpr t.2.2

public theorem mappingCylinderFreeDistance_le_one (t : unitInterval) :
    mappingCylinderFreeDistance t ≤ 1 := by
  simp only [mappingCylinderFreeDistance]
  linarith [t.2.1]

/-- A cutoff supported near the free endpoint. -/
public def mappingCylinderFreeCutoff (t : unitInterval) : ℝ :=
  max (1 - 2 * mappingCylinderFreeDistance t) 0

public theorem mappingCylinderFreeCutoff_nonneg (t : unitInterval) :
    0 ≤ mappingCylinderFreeCutoff t :=
  le_max_right _ _

public theorem mappingCylinderFreeCutoff_le_one (t : unitInterval) :
    mappingCylinderFreeCutoff t ≤ 1 := by
  apply max_le
  · linarith [mappingCylinderFreeDistance_nonneg t]
  · norm_num

public def mappingCylinderFreeEffectiveTime (s t : unitInterval) : ℝ :=
  (s : ℝ) * mappingCylinderFreeCutoff t

public theorem mappingCylinderFreeEffectiveTime_nonneg (s t : unitInterval) :
    0 ≤ mappingCylinderFreeEffectiveTime s t :=
  mul_nonneg s.2.1 (mappingCylinderFreeCutoff_nonneg t)

public theorem mappingCylinderFreeEffectiveTime_le_one (s t : unitInterval) :
    mappingCylinderFreeEffectiveTime s t ≤ 1 := by
  exact mul_le_one₀ s.2.2 (mappingCylinderFreeCutoff_nonneg t)
    (mappingCylinderFreeCutoff_le_one t)

/-- Cylinder coordinate on the bottom branch of the L-shaped square retraction. -/
public def mappingCylinderFreeBottomTime (s t : unitInterval) : unitInterval :=
  ⟨1 - max (mappingCylinderFreeDistance t - mappingCylinderFreeEffectiveTime s t) 0, by
    constructor
    · have hmax : max (mappingCylinderFreeDistance t -
          mappingCylinderFreeEffectiveTime s t) 0 ≤ 1 := by
        apply max_le
        · linarith [mappingCylinderFreeDistance_le_one t,
            mappingCylinderFreeEffectiveTime_nonneg s t]
        · norm_num
      linarith
    · exact sub_le_self 1 (le_max_right _ _)⟩

/-- Homotopy coordinate on the vertical branch of the L-shaped square retraction. -/
public def mappingCylinderFreeVerticalTime (s t : unitInterval) : unitInterval :=
  ⟨max (mappingCylinderFreeEffectiveTime s t - mappingCylinderFreeDistance t) 0, by
    constructor
    · exact le_max_right _ _
    · apply max_le
      · linarith [mappingCylinderFreeEffectiveTime_le_one s t,
          mappingCylinderFreeDistance_nonneg t]
      · norm_num⟩

public theorem continuous_mappingCylinderFreeEffectiveTime :
    Continuous (fun p : unitInterval × unitInterval ↦
      mappingCylinderFreeEffectiveTime p.1 p.2) := by
  have hd : Continuous mappingCylinderFreeDistance := by
    unfold mappingCylinderFreeDistance
    fun_prop
  have hc : Continuous mappingCylinderFreeCutoff := by
    unfold mappingCylinderFreeCutoff
    exact (continuous_const.sub (hd.const_mul 2)).max continuous_const
  exact (continuous_subtype_val.comp continuous_fst).mul
    (hc.comp continuous_snd)

public theorem continuous_mappingCylinderFreeBottomTime :
    Continuous (fun p : unitInterval × unitInterval ↦
      mappingCylinderFreeBottomTime p.1 p.2) := by
  apply Continuous.subtype_mk
  exact continuous_const.sub
    ((((continuous_const.sub continuous_subtype_val).comp continuous_snd).sub
      continuous_mappingCylinderFreeEffectiveTime).max continuous_const)

public theorem continuous_mappingCylinderFreeVerticalTime :
    Continuous (fun p : unitInterval × unitInterval ↦
      mappingCylinderFreeVerticalTime p.1 p.2) := by
  apply Continuous.subtype_mk
  exact (continuous_mappingCylinderFreeEffectiveTime.sub
    ((continuous_const.sub continuous_subtype_val).comp continuous_snd)).max continuous_const

@[simp]
public theorem mappingCylinderFreeBottomTime_zero (t : unitInterval) :
    mappingCylinderFreeBottomTime 0 t = t := by
  apply Subtype.ext
  simp [mappingCylinderFreeBottomTime, mappingCylinderFreeEffectiveTime,
    mappingCylinderFreeDistance, t.2.2]

@[simp]
public theorem mappingCylinderFreeVerticalTime_zero (t : unitInterval) :
    mappingCylinderFreeVerticalTime 0 t = 0 := by
  apply Subtype.ext
  simp [mappingCylinderFreeVerticalTime, mappingCylinderFreeEffectiveTime,
    mappingCylinderFreeDistance, t.2.2]

@[simp]
public theorem mappingCylinderFreeBottomTime_one (s : unitInterval) :
    mappingCylinderFreeBottomTime s 1 = 1 := by
  apply Subtype.ext
  simp only [mappingCylinderFreeBottomTime]
  rw [show mappingCylinderFreeDistance (1 : unitInterval) = 0 by
    norm_num [mappingCylinderFreeDistance]]
  change 1 - max (0 - mappingCylinderFreeEffectiveTime s 1) 0 = (1 : ℝ)
  have h : 0 - mappingCylinderFreeEffectiveTime s 1 ≤ 0 := by
    linarith [mappingCylinderFreeEffectiveTime_nonneg s 1]
  rw [max_eq_right h]
  norm_num

@[simp]
public theorem mappingCylinderFreeVerticalTime_one (s : unitInterval) :
    mappingCylinderFreeVerticalTime s 1 = s := by
  apply Subtype.ext
  simp [mappingCylinderFreeVerticalTime, mappingCylinderFreeDistance,
    mappingCylinderFreeEffectiveTime, mappingCylinderFreeCutoff, s.2.1]

@[simp]
public theorem mappingCylinderFreeEffectiveTime_right_zero (s : unitInterval) :
    mappingCylinderFreeEffectiveTime s 0 = 0 := by
  simp [mappingCylinderFreeEffectiveTime, mappingCylinderFreeCutoff,
    mappingCylinderFreeDistance]

@[simp]
public theorem mappingCylinderFreeBottomTime_right_zero (s : unitInterval) :
    mappingCylinderFreeBottomTime s 0 = 0 := by
  apply Subtype.ext
  simp [mappingCylinderFreeBottomTime, mappingCylinderFreeDistance]

@[simp]
public theorem mappingCylinderFreeVerticalTime_right_zero (s : unitInterval) :
    mappingCylinderFreeVerticalTime s 0 = 0 := by
  apply Subtype.ext
  simp [mappingCylinderFreeVerticalTime, mappingCylinderFreeDistance]

public theorem mappingCylinderFreeBottomTime_eq_one_of_effective_eq_distance
    {s t : unitInterval}
    (h : mappingCylinderFreeEffectiveTime s t = mappingCylinderFreeDistance t) :
    mappingCylinderFreeBottomTime s t = 1 := by
  apply Subtype.ext
  simp [mappingCylinderFreeBottomTime, h]

public theorem mappingCylinderFreeVerticalTime_eq_zero_of_effective_eq_distance
    {s t : unitInterval}
    (h : mappingCylinderFreeEffectiveTime s t = mappingCylinderFreeDistance t) :
    mappingCylinderFreeVerticalTime s t = 0 := by
  apply Subtype.ext
  simp [mappingCylinderFreeVerticalTime, h]

variable {A X : TopCat.{u}}

/-- The L-shaped extension formula on the cylinder branch of a mapping cylinder. -/
public def mappingCylinderFreeLocalExtension
    {Y : Type u} [TopologicalSpace Y]
    (f : A ⟶ X) (q : C((MappingCylinder f : TopCat), Y))
    {q₁ : C(A, Y)}
    (H : ContinuousMap.Homotopy (q.comp (mappingCylinderFree f).hom) q₁) :
    unitInterval × (A × unitInterval) → Y :=
  fun p ↦
    if mappingCylinderFreeEffectiveTime p.1 p.2.2 ≤
        mappingCylinderFreeDistance p.2.2 then
      q (mappingCylinderCylinder f
        (p.2.1, mappingCylinderFreeBottomTime p.1 p.2.2))
    else
      H (mappingCylinderFreeVerticalTime p.1 p.2.2, p.2.1)

public theorem continuous_mappingCylinderFreeLocalExtension
    {Y : Type u} [TopologicalSpace Y]
    (f : A ⟶ X) (q : C((MappingCylinder f : TopCat), Y))
    {q₁ : C(A, Y)}
    (H : ContinuousMap.Homotopy (q.comp (mappingCylinderFree f).hom) q₁) :
    Continuous (mappingCylinderFreeLocalExtension f q H) := by
  let e : unitInterval × (A × unitInterval) → ℝ := fun p ↦
    mappingCylinderFreeEffectiveTime p.1 p.2.2
  let d : unitInterval × (A × unitInterval) → ℝ := fun p ↦
    mappingCylinderFreeDistance p.2.2
  let bottom : unitInterval × (A × unitInterval) → Y := fun p ↦
    q (mappingCylinderCylinder f
      (p.2.1, mappingCylinderFreeBottomTime p.1 p.2.2))
  let vertical : unitInterval × (A × unitInterval) → Y := fun p ↦
    H (mappingCylinderFreeVerticalTime p.1 p.2.2, p.2.1)
  have he : Continuous e :=
    continuous_mappingCylinderFreeEffectiveTime.comp
      (continuous_fst.prodMk continuous_snd.snd)
  have hdistance : Continuous mappingCylinderFreeDistance := by
    unfold mappingCylinderFreeDistance
    fun_prop
  have hd : Continuous d := hdistance.comp continuous_snd.snd
  have hbottomTime : Continuous (fun p : unitInterval × (A × unitInterval) ↦
      mappingCylinderFreeBottomTime p.1 p.2.2) :=
    continuous_mappingCylinderFreeBottomTime.comp
      (continuous_fst.prodMk continuous_snd.snd)
  have hbottom : Continuous bottom := q.continuous.comp <|
    (mappingCylinderCylinder f).hom.continuous.comp <|
      continuous_snd.fst.prodMk hbottomTime
  have hvertical : Continuous vertical := H.continuous.comp <|
    (continuous_mappingCylinderFreeVerticalTime.comp
      (continuous_fst.prodMk continuous_snd.snd)).prodMk continuous_snd.fst
  change Continuous (fun p ↦ if e p ≤ d p then bottom p else vertical p)
  apply hbottom.if_le hvertical he hd
  intro p hp
  change q (mappingCylinderCylinder f
      (p.2.1, mappingCylinderFreeBottomTime p.1 p.2.2)) =
    H (mappingCylinderFreeVerticalTime p.1 p.2.2, p.2.1)
  rw [mappingCylinderFreeBottomTime_eq_one_of_effective_eq_distance hp,
    mappingCylinderFreeVerticalTime_eq_zero_of_effective_eq_distance hp]
  exact (H.map_zero_left p.2.1).symm

@[simp]
public theorem mappingCylinderFreeLocalExtension_zero
    {Y : Type u} [TopologicalSpace Y]
    (f : A ⟶ X) (q : C((MappingCylinder f : TopCat), Y))
    {q₁ : C(A, Y)}
    (H : ContinuousMap.Homotopy (q.comp (mappingCylinderFree f).hom) q₁)
    (p : A × unitInterval) :
    mappingCylinderFreeLocalExtension f q H (0, p) =
      q (mappingCylinderCylinder f p) := by
  have hcond : mappingCylinderFreeEffectiveTime 0 p.2 ≤
      mappingCylinderFreeDistance p.2 := by
    simpa [mappingCylinderFreeEffectiveTime] using mappingCylinderFreeDistance_nonneg p.2
  change (if mappingCylinderFreeEffectiveTime 0 p.2 ≤ mappingCylinderFreeDistance p.2 then
      q (mappingCylinderCylinder f (p.1, mappingCylinderFreeBottomTime 0 p.2))
    else H (mappingCylinderFreeVerticalTime 0 p.2, p.1)) =
      q (mappingCylinderCylinder f p)
  simp only [hcond, ↓reduceIte, mappingCylinderFreeBottomTime_zero]

@[simp]
public theorem mappingCylinderFreeLocalExtension_cylinderZero
    {Y : Type u} [TopologicalSpace Y]
    (f : A ⟶ X) (q : C((MappingCylinder f : TopCat), Y))
    {q₁ : C(A, Y)}
    (H : ContinuousMap.Homotopy (q.comp (mappingCylinderFree f).hom) q₁)
    (s : unitInterval) (a : A) :
    mappingCylinderFreeLocalExtension f q H (s, (a, 0)) =
      q (mappingCylinderCylinder f (a, 0)) := by
  simp [mappingCylinderFreeLocalExtension, mappingCylinderFreeDistance]

@[simp]
public theorem mappingCylinderFreeLocalExtension_free
    {Y : Type u} [TopologicalSpace Y]
    (f : A ⟶ X) (q : C((MappingCylinder f : TopCat), Y))
    {q₁ : C(A, Y)}
    (H : ContinuousMap.Homotopy (q.comp (mappingCylinderFree f).hom) q₁)
    (s : unitInterval) (a : A) :
    mappingCylinderFreeLocalExtension f q H (s, (a, 1)) = H (s, a) := by
  by_cases hs : s = 0
  · subst s
    rw [mappingCylinderFreeLocalExtension_zero]
    exact (H.map_zero_left a).symm
  · have hspos : 0 < (s : ℝ) := lt_of_le_of_ne s.2.1 (Ne.symm (Subtype.coe_ne_coe.mpr hs))
    have hnle : ¬(s : ℝ) ≤ 0 := by linarith
    simp [mappingCylinderFreeLocalExtension, mappingCylinderFreeDistance,
      mappingCylinderFreeEffectiveTime, mappingCylinderFreeCutoff, hnle]

/-- The cylinder-branch extension, bundled as a continuous map. -/
public def mappingCylinderFreeLocalExtensionMap
    {Y : Type u} [TopologicalSpace Y]
    (f : A ⟶ X) (q : C((MappingCylinder f : TopCat), Y))
    {q₁ : C(A, Y)}
    (H : ContinuousMap.Homotopy (q.comp (mappingCylinderFree f).hom) q₁) :
    C(unitInterval × (A × unitInterval), Y) :=
  ⟨mappingCylinderFreeLocalExtension f q H,
    continuous_mappingCylinderFreeLocalExtension f q H⟩

/-- Paths on the cylinder branch, obtained by currying the extension time. -/
public def mappingCylinderFreeCylinderPaths
    {Y : Type u} [TopologicalSpace Y]
    (f : A ⟶ X) (q : C((MappingCylinder f : TopCat), Y))
    {q₁ : C(A, Y)}
    (H : ContinuousMap.Homotopy (q.comp (mappingCylinderFree f).hom) q₁) :
    C(A × unitInterval, C(unitInterval, Y)) :=
  ContinuousMap.curry <| (mappingCylinderFreeLocalExtensionMap f q H).comp
    ⟨Prod.swap, continuous_swap⟩

/-- Constant paths on the base branch of the mapping cylinder. -/
public def mappingCylinderFreeBasePaths
    {Y : Type u} [TopologicalSpace Y]
    (f : A ⟶ X) (q : C((MappingCylinder f : TopCat), Y)) :
    C(X, C(unitInterval, Y)) :=
  ContinuousMap.curry
    ⟨fun p : X × unitInterval ↦ q (mappingCylinderBase f p.1),
      q.continuous.comp ((mappingCylinderBase f).hom.continuous.comp continuous_fst)⟩

/-- The cylinder and base path families agree along the attached zero section. -/
public theorem mappingCylinderFreePaths_compatible
    {Y : Type u} [TopologicalSpace Y]
    (f : A ⟶ X) (q : C((MappingCylinder f : TopCat), Y))
    {q₁ : C(A, Y)}
    (H : ContinuousMap.Homotopy (q.comp (mappingCylinderFree f).hom) q₁) :
    cylinderZeroSection A ≫ TopCat.ofHom (mappingCylinderFreeCylinderPaths f q H) =
      f ≫ TopCat.ofHom (mappingCylinderFreeBasePaths f q) := by
  ext a s
  change mappingCylinderFreeLocalExtension f q H (s, (a, 0)) =
    q (mappingCylinderBase f (f a))
  rw [mappingCylinderFreeLocalExtension_cylinderZero]
  exact congrArg q (CategoryTheory.congr_fun (mappingCylinder_zero_eq_base f) a)

/-- The continuous family of paths on the whole mapping cylinder. -/
public def mappingCylinderFreePaths
    {Y : Type u} [TopologicalSpace Y]
    (f : A ⟶ X) (q : C((MappingCylinder f : TopCat), Y))
    {q₁ : C(A, Y)}
    (H : ContinuousMap.Homotopy (q.comp (mappingCylinderFree f).hom) q₁) :
    MappingCylinder f ⟶ TopCat.of C(unitInterval, Y) :=
  pushout.desc
    (TopCat.ofHom (mappingCylinderFreeCylinderPaths f q H))
    (TopCat.ofHom (mappingCylinderFreeBasePaths f q))
    (mappingCylinderFreePaths_compatible f q H)

/-- Evaluate the descended path family, with extension time as the first coordinate. -/
public def mappingCylinderFreeGlobalExtension
    {Y : Type u} [TopologicalSpace Y]
    (f : A ⟶ X) (q : C((MappingCylinder f : TopCat), Y))
    {q₁ : C(A, Y)}
    (H : ContinuousMap.Homotopy (q.comp (mappingCylinderFree f).hom) q₁) :
    C(unitInterval × (MappingCylinder f : TopCat), Y) :=
  ContinuousMap.uncurry (mappingCylinderFreePaths f q H).hom |>.comp
    ⟨Prod.swap, continuous_swap⟩

public theorem mappingCylinderFreeGlobalExtension_cylinder
    {Y : Type u} [TopologicalSpace Y]
    (f : A ⟶ X) (q : C((MappingCylinder f : TopCat), Y))
    {q₁ : C(A, Y)}
    (H : ContinuousMap.Homotopy (q.comp (mappingCylinderFree f).hom) q₁)
    (s : unitInterval) (p : A × unitInterval) :
    mappingCylinderFreeGlobalExtension f q H
        (s, mappingCylinderCylinder f p) =
      mappingCylinderFreeLocalExtension f q H (s, p) := by
  change (mappingCylinderFreePaths f q H (mappingCylinderCylinder f p)) s = _
  have hpath := CategoryTheory.congr_fun (pushout.inl_desc
    (TopCat.ofHom (mappingCylinderFreeCylinderPaths f q H))
    (TopCat.ofHom (mappingCylinderFreeBasePaths f q))
    (mappingCylinderFreePaths_compatible f q H)) p
  change mappingCylinderFreePaths f q H (mappingCylinderCylinder f p) =
    mappingCylinderFreeCylinderPaths f q H p at hpath
  rw [hpath]
  rfl

public theorem mappingCylinderFreeGlobalExtension_base
    {Y : Type u} [TopologicalSpace Y]
    (f : A ⟶ X) (q : C((MappingCylinder f : TopCat), Y))
    {q₁ : C(A, Y)}
    (H : ContinuousMap.Homotopy (q.comp (mappingCylinderFree f).hom) q₁)
    (s : unitInterval) (x : X) :
    mappingCylinderFreeGlobalExtension f q H
        (s, mappingCylinderBase f x) =
      q (mappingCylinderBase f x) := by
  change (mappingCylinderFreePaths f q H (mappingCylinderBase f x)) s = _
  have hpath := CategoryTheory.congr_fun (pushout.inr_desc
    (TopCat.ofHom (mappingCylinderFreeCylinderPaths f q H))
    (TopCat.ofHom (mappingCylinderFreeBasePaths f q))
    (mappingCylinderFreePaths_compatible f q H)) x
  change mappingCylinderFreePaths f q H (mappingCylinderBase f x) =
    mappingCylinderFreeBasePaths f q x at hpath
  rw [hpath]
  rfl

/-- At time zero the global extension is the original mapping-cylinder map. -/
public theorem mappingCylinderFreeGlobalExtension_zero
    {Y : Type u} [TopologicalSpace Y]
    (f : A ⟶ X) (q : C((MappingCylinder f : TopCat), Y))
    {q₁ : C(A, Y)}
    (H : ContinuousMap.Homotopy (q.comp (mappingCylinderFree f).hom) q₁)
    (p : MappingCylinder f) :
    mappingCylinderFreeGlobalExtension f q H (0, p) = q p := by
  have heq : TopCat.ofHom (cylinderSlice (mappingCylinderFreeGlobalExtension f q H) 0) =
      TopCat.ofHom q := by
    apply pushout.hom_ext
    · ext z
      change mappingCylinderFreeGlobalExtension f q H
          (0, mappingCylinderCylinder f z) = q (mappingCylinderCylinder f z)
      rw [mappingCylinderFreeGlobalExtension_cylinder,
        mappingCylinderFreeLocalExtension_zero]
    · ext x
      exact mappingCylinderFreeGlobalExtension_base f q H 0 x
  exact CategoryTheory.congr_fun heq p

/-- On the free end, the global extension is the prescribed homotopy. -/
public theorem mappingCylinderFreeGlobalExtension_free
    {Y : Type u} [TopologicalSpace Y]
    (f : A ⟶ X) (q : C((MappingCylinder f : TopCat), Y))
    {q₁ : C(A, Y)}
    (H : ContinuousMap.Homotopy (q.comp (mappingCylinderFree f).hom) q₁)
    (s : unitInterval) (a : A) :
    mappingCylinderFreeGlobalExtension f q H (s, mappingCylinderFree f a) =
      H (s, a) := by
  change mappingCylinderFreeGlobalExtension f q H
      (s, mappingCylinderCylinder f (a, 1)) = H (s, a)
  rw [mappingCylinderFreeGlobalExtension_cylinder,
    mappingCylinderFreeLocalExtension_free]

/-- The free-end inclusion of every mapping cylinder has the homotopy-extension property. -/
public theorem mappingCylinderFree_homotopyExtensionProperty (f : A ⟶ X) :
    HomotopyExtensionProperty (mappingCylinderFree f).hom := by
  refine ⟨?_⟩
  intro Y _ q q₁ H
  let qEnd : C((MappingCylinder f : TopCat), Y) :=
    cylinderSlice (mappingCylinderFreeGlobalExtension f q H) 1
  let F : ContinuousMap.Homotopy q qEnd :=
    { toContinuousMap := mappingCylinderFreeGlobalExtension f q H
      map_zero_left := mappingCylinderFreeGlobalExtension_zero f q H
      map_one_left := fun _ ↦ rfl }
  exact ⟨qEnd, F, mappingCylinderFreeGlobalExtension_free f q H⟩

end TopCat

end SphereSixComplex
