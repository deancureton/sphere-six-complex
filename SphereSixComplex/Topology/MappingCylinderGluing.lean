module

public import SphereSixComplex.Topology.MapHomotopyEquivalence
public import SphereSixComplex.Topology.PushoutHomotopy

/-!
# Mapping-cylinder replacements for topological gluing

This file isolates the standard mapping-cylinder alternative to relativeising a homotopy on an
ordinary pushout.  The target copy in a mapping cylinder is always a strong deformation retract,
whereas the free end is homotopic to the original map followed by that target inclusion.  Thus a
homotopy-equivalent attaching map is replaced by a homotopy-equivalent *free-end inclusion*.

For a span `X ← A → Y`, the double mapping cylinder is the pushout of this free-end
inclusion and the right leg.  There is a canonical collapse from the double mapping cylinder to
the ordinary pushout.  The final theorem records exactly the two comparison facts which would
make the ordinary right coprojection a homotopy equivalence.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open ContinuousMap Function TopologicalSpace Topology

namespace SphereSixComplex

universe u

namespace TopCat

variable {A X Y : TopCat.{u}}

/-! ## The cylinder as a strong deformation retract -/

/-- The zero section of the unit cylinder on `A`. -/
public def cylinderZeroSection (A : TopCat.{u}) :
    A ⟶ TopCat.of (A × unitInterval) :=
  TopCat.ofHom ⟨fun a ↦ (a, 0), continuous_id.prodMk continuous_const⟩

/-- The one section of the unit cylinder on `A`. -/
public def cylinderOneSection (A : TopCat.{u}) :
    A ⟶ TopCat.of (A × unitInterval) :=
  TopCat.ofHom ⟨fun a ↦ (a, 1), continuous_id.prodMk continuous_const⟩

/-- Projection of the unit cylinder onto its base. -/
public def cylinderProjection (A : TopCat.{u}) :
    TopCat.of (A × unitInterval) ⟶ A :=
  TopCat.ofHom ⟨Prod.fst, continuous_fst⟩

/-- Multiplication of two unit-interval parameters, retained in the unit interval. -/
public def unitIntervalScale (s t : unitInterval) : unitInterval :=
  ⟨(s : ℝ) * (t : ℝ), by
    constructor
    · exact mul_nonneg s.2.1 t.2.1
    · calc
        (s : ℝ) * (t : ℝ) ≤ 1 * (t : ℝ) :=
          mul_le_mul_of_nonneg_right s.2.2 t.2.1
        _ ≤ 1 := by simpa using t.2.2⟩

@[simp]
public theorem unitIntervalScale_zero (t : unitInterval) :
    unitIntervalScale 0 t = 0 := by
  apply Subtype.ext
  simp [unitIntervalScale]

@[simp]
public theorem unitIntervalScale_one (t : unitInterval) :
    unitIntervalScale 1 t = t := by
  apply Subtype.ext
  simp [unitIntervalScale]

@[simp]
public theorem unitIntervalScale_zero_right (s : unitInterval) :
    unitIntervalScale s 0 = 0 := by
  apply Subtype.ext
  simp [unitIntervalScale]

/-- Joint continuity of multiplication on the unit interval. -/
public theorem continuous_unitIntervalScale :
    Continuous (fun p : unitInterval × unitInterval ↦
      unitIntervalScale p.1 p.2) := by
  exact ((continuous_subtype_val.comp continuous_fst).mul
    (continuous_subtype_val.comp continuous_snd)).subtype_mk _

/-- The contraction of the unit cylinder onto its zero section. -/
public def cylinderZeroHomotopy (A : TopCat.{u}) :
    TopCat.Homotopy
      (cylinderProjection A ≫ cylinderZeroSection A)
      (𝟙 (TopCat.of (A × unitInterval))) where
  toFun p := (p.2.1, unitIntervalScale p.1 p.2.2)
  continuous_toFun := continuous_snd.fst.prodMk
    (continuous_unitIntervalScale.comp
      (continuous_fst.prodMk continuous_snd.snd))
  map_zero_left p := by
    apply Prod.ext
    · rfl
    · exact unitIntervalScale_zero p.2
  map_one_left p := by
    apply Prod.ext
    · rfl
    · exact unitIntervalScale_one p.2

/-- The zero section is a strong deformation retract of the unit cylinder. -/
public def cylinderZeroStrongDeformationRetract (A : TopCat.{u}) :
    TopCat.StrongDeformationRetractData (cylinderZeroSection A) where
  retraction := cylinderProjection A
  retract := by
    ext a
    rfl
  homotopy := cylinderZeroHomotopy A
  fixed s a := by
    change (a, unitIntervalScale s 0) = (a, 0)
    rw [unitIntervalScale_zero_right]

/-! ## Mapping cylinders -/

/-- The (unreduced) mapping cylinder of `f`, with the zero end of `A × I` attached to `X`. -/
public abbrev MappingCylinder (f : A ⟶ X) : TopCat.{u} :=
  pushout (cylinderZeroSection A) f

/-- The cylinder branch of a mapping cylinder. -/
public def mappingCylinderCylinder (f : A ⟶ X) :
    TopCat.of (A × unitInterval) ⟶ MappingCylinder f :=
  pushout.inl (cylinderZeroSection A) f

/-- The target/base branch of a mapping cylinder. -/
public def mappingCylinderBase (f : A ⟶ X) : X ⟶ MappingCylinder f :=
  pushout.inr (cylinderZeroSection A) f

/-- The unattached, one-end inclusion into a mapping cylinder. -/
public def mappingCylinderFree (f : A ⟶ X) : A ⟶ MappingCylinder f :=
  cylinderOneSection A ≫ mappingCylinderCylinder f

@[reassoc]
public theorem mappingCylinder_zero_eq_base (f : A ⟶ X) :
    cylinderZeroSection A ≫ mappingCylinderCylinder f =
      f ≫ mappingCylinderBase f :=
  pushout.condition

/-- The target copy is homotopy equivalent to the mapping cylinder, without any hypothesis on
the map. -/
public def mappingCylinderBaseHomotopyEquiv (f : A ⟶ X) :
    (X : Type u) ≃ₕ (MappingCylinder f : Type u) :=
  (cylinderZeroStrongDeformationRetract A).pushoutInrHomotopyEquiv f

@[simp]
public theorem mappingCylinderBaseHomotopyEquiv_apply (f : A ⟶ X) (x : X) :
    mappingCylinderBaseHomotopyEquiv f x = mappingCylinderBase f x :=
  (cylinderZeroStrongDeformationRetract A).pushoutInrHomotopyEquiv_apply f x

/-- Sliding along the cylinder homotopes the original map followed by the base inclusion to the
free-end inclusion. -/
public def mappingCylinderBaseToFreeHomotopy (f : A ⟶ X) :
    TopCat.Homotopy (f ≫ mappingCylinderBase f) (mappingCylinderFree f) where
  toFun p := mappingCylinderCylinder f (p.2, p.1)
  continuous_toFun := (mappingCylinderCylinder f).hom.continuous.comp
    (continuous_snd.prodMk continuous_fst)
  map_zero_left a := by
    exact CategoryTheory.congr_fun (mappingCylinder_zero_eq_base f) a
  map_one_left _ := rfl

/-! ## Homotopy invariance of a specified homotopy-equivalence map -/

/-- Replacing the forward map of a homotopy equivalence by a homotopic map preserves the bundled
homotopy equivalence. -/
public def homotopyEquivOfHomotopic {P Q : Type u}
    [TopologicalSpace P] [TopologicalSpace Q]
    (e : P ≃ₕ Q) {g : C(P, Q)}
    (H : ContinuousMap.Homotopy e.toFun g) : P ≃ₕ Q where
  toFun := g
  invFun := e.invFun
  left_inv :=
    (ContinuousMap.Homotopic.comp (.refl e.invFun) ⟨H.symm⟩).trans e.left_inv
  right_inv :=
    (ContinuousMap.Homotopic.comp ⟨H.symm⟩ (.refl e.invFun)).trans e.right_inv

@[simp]
public theorem homotopyEquivOfHomotopic_apply {P Q : Type u}
    [TopologicalSpace P] [TopologicalSpace Q]
    (e : P ≃ₕ Q) {g : C(P, Q)}
    (H : ContinuousMap.Homotopy e.toFun g) (p : P) :
    homotopyEquivOfHomotopic e H p = g p :=
  rfl

/-- A function homotopic to a specified homotopy-equivalence map is itself a specified homotopy
equivalence. -/
public theorem isHomotopyEquivalence_of_homotopic {P Q : Type u}
    [TopologicalSpace P] [TopologicalSpace Q]
    {f g : C(P, Q)} (hf : IsHomotopyEquivalence f)
    (H : ContinuousMap.Homotopy f g) : IsHomotopyEquivalence g := by
  obtain ⟨e, he⟩ := hf
  have he' : e.toFun = f := by
    ext p
    exact congrFun he p
  let H' : ContinuousMap.Homotopy e.toFun g := H.cast he'.symm rfl
  exact ⟨homotopyEquivOfHomotopic e H', rfl⟩

/-- If the original map is a homotopy equivalence, then so is the *specified* free-end inclusion
of its mapping cylinder. -/
public theorem mappingCylinderFree_isHomotopyEquivalence (f : A ⟶ X)
    (hf : IsHomotopyEquivalence f.hom) :
    IsHomotopyEquivalence (mappingCylinderFree f).hom := by
  have hbase : IsHomotopyEquivalence (mappingCylinderBase f).hom :=
    ⟨mappingCylinderBaseHomotopyEquiv f, by
      funext x
      exact mappingCylinderBaseHomotopyEquiv_apply f x⟩
  have hcomp : IsHomotopyEquivalence
      ((mappingCylinderBase f).hom.comp f.hom) := by
    simpa only [ContinuousMap.coe_comp] using hbase.comp hf
  exact isHomotopyEquivalence_of_homotopic hcomp
    (mappingCylinderBaseToFreeHomotopy f)

/-! ## Double mapping cylinders and their collapse to ordinary pushouts -/

/-- The double mapping cylinder of a span `X ← A → Y`. -/
public abbrev DoubleMappingCylinder (f : A ⟶ X) (g : A ⟶ Y) : TopCat.{u} :=
  pushout (mappingCylinderFree f) g

/-- The mapping-cylinder branch of the double mapping cylinder. -/
public def doubleMappingCylinderLeft (f : A ⟶ X) (g : A ⟶ Y) :
    MappingCylinder f ⟶ DoubleMappingCylinder f g :=
  pushout.inl (mappingCylinderFree f) g

/-- The right branch of the double mapping cylinder. -/
public def doubleMappingCylinderRight (f : A ⟶ X) (g : A ⟶ Y) :
    Y ⟶ DoubleMappingCylinder f g :=
  pushout.inr (mappingCylinderFree f) g

@[reassoc]
public theorem doubleMappingCylinder_condition (f : A ⟶ X) (g : A ⟶ Y) :
    mappingCylinderFree f ≫ doubleMappingCylinderLeft f g =
      g ≫ doubleMappingCylinderRight f g :=
  pushout.condition

/-- If the free end has been upgraded to a strong deformation retract, the right branch of the
double mapping cylinder is a homotopy equivalence.  This is the exact input consumed by the
existing pushout theorem. -/
public def doubleMappingCylinderRightHomotopyEquiv (f : A ⟶ X) (g : A ⟶ Y)
    (D : TopCat.StrongDeformationRetractData (mappingCylinderFree f)) :
    (Y : Type u) ≃ₕ (DoubleMappingCylinder f g : Type u) :=
  D.pushoutInrHomotopyEquiv g

@[simp]
public theorem doubleMappingCylinderRightHomotopyEquiv_apply
    (f : A ⟶ X) (g : A ⟶ Y)
    (D : TopCat.StrongDeformationRetractData (mappingCylinderFree f)) (y : Y) :
    doubleMappingCylinderRightHomotopyEquiv f g D y =
      doubleMappingCylinderRight f g y :=
  D.pushoutInrHomotopyEquiv_apply g y

/-- Any homotopy-equivalence comparison from the double mapping cylinder to the ordinary pushout
which preserves the right branch transfers the desired map-level homotopy equivalence.  A collar
stretching homeomorphism is one geometric way to supply such a comparison. -/
public theorem pushoutInr_isHomotopyEquivalence_of_doubleComparison
    (f : A ⟶ X) (g : A ⟶ Y)
    (D : TopCat.StrongDeformationRetractData (mappingCylinderFree f))
    (e : (DoubleMappingCylinder f g : Type u) ≃ₕ
      ((pushout f g : TopCat.{u}) : Type u))
    (he : ∀ y : Y, e (doubleMappingCylinderRight f g y) = pushout.inr f g y) :
    IsHomotopyEquivalence (pushout.inr f g).hom := by
  refine ⟨(doubleMappingCylinderRightHomotopyEquiv f g D).trans e, ?_⟩
  funext y
  exact he y

/-- Collapse a mapping cylinder back to its target. -/
public def mappingCylinderCollapse (f : A ⟶ X) : MappingCylinder f ⟶ X :=
  pushout.desc (cylinderProjection A ≫ f) (𝟙 X) (by
    ext a
    rfl)

@[simp]
public theorem mappingCylinderCylinder_comp_collapse (f : A ⟶ X) :
    mappingCylinderCylinder f ≫ mappingCylinderCollapse f =
      cylinderProjection A ≫ f :=
  pushout.inl_desc _ _ _

@[simp]
public theorem mappingCylinderBase_comp_collapse (f : A ⟶ X) :
    mappingCylinderBase f ≫ mappingCylinderCollapse f = 𝟙 X :=
  pushout.inr_desc _ _ _

@[simp]
public theorem mappingCylinderFree_comp_collapse (f : A ⟶ X) :
    mappingCylinderFree f ≫ mappingCylinderCollapse f = f := by
  rw [mappingCylinderFree, Category.assoc,
    mappingCylinderCylinder_comp_collapse, ← Category.assoc]
  ext a
  rfl

/-- The explicit collapse is the retraction occurring in the canonical mapping-cylinder
homotopy equivalence. -/
public theorem mappingCylinderCollapse_eq_pushoutRetraction (f : A ⟶ X) :
    mappingCylinderCollapse f =
      (cylinderZeroStrongDeformationRetract A).pushoutRetraction f := by
  apply pushout.hom_ext
  · change mappingCylinderCylinder f ≫ mappingCylinderCollapse f = _
    rw [mappingCylinderCylinder_comp_collapse]
    simpa only [cylinderZeroStrongDeformationRetract] using
      ((cylinderZeroStrongDeformationRetract A).inl_pushoutRetraction f).symm
  · change mappingCylinderBase f ≫ mappingCylinderCollapse f = _
    rw [mappingCylinderBase_comp_collapse]
    exact ((cylinderZeroStrongDeformationRetract A).inr_pushoutRetraction f).symm

/-- Collapsing a mapping cylinder to its target is itself a homotopy equivalence. -/
public def mappingCylinderCollapseHomotopyEquiv (f : A ⟶ X) :
    (MappingCylinder f : Type u) ≃ₕ (X : Type u) :=
  (mappingCylinderBaseHomotopyEquiv f).symm

@[simp]
public theorem mappingCylinderCollapseHomotopyEquiv_apply
    (f : A ⟶ X) (p : MappingCylinder f) :
    mappingCylinderCollapseHomotopyEquiv f p = mappingCylinderCollapse f p := by
  change (cylinderZeroStrongDeformationRetract A).pushoutRetraction f p = _
  rw [← mappingCylinderCollapse_eq_pushoutRetraction f]

/-- Map-level version of the mapping-cylinder collapse equivalence. -/
public theorem mappingCylinderCollapse_isHomotopyEquivalence (f : A ⟶ X) :
    IsHomotopyEquivalence (mappingCylinderCollapse f).hom :=
  ⟨mappingCylinderCollapseHomotopyEquiv f, by
    funext p
    exact mappingCylinderCollapseHomotopyEquiv_apply f p⟩

/-- Map the mapping-cylinder branch into the ordinary pushout by collapsing its interval. -/
public def mappingCylinderToPushout (f : A ⟶ X) (g : A ⟶ Y) :
    MappingCylinder f ⟶ pushout f g :=
  mappingCylinderCollapse f ≫ pushout.inl f g

@[reassoc]
public theorem mappingCylinderFree_comp_toPushout (f : A ⟶ X) (g : A ⟶ Y) :
    mappingCylinderFree f ≫ mappingCylinderToPushout f g =
      g ≫ pushout.inr f g := by
  rw [mappingCylinderToPushout, ← Category.assoc,
    mappingCylinderFree_comp_collapse, pushout.condition]

/-- Collapse the inserted interval in the double mapping cylinder, obtaining the ordinary
pushout. -/
public def doubleMappingCylinderCollapse (f : A ⟶ X) (g : A ⟶ Y) :
    DoubleMappingCylinder f g ⟶ pushout f g :=
  pushout.desc (mappingCylinderToPushout f g) (pushout.inr f g)
    (mappingCylinderFree_comp_toPushout f g)

@[simp]
public theorem doubleMappingCylinderLeft_comp_collapse (f : A ⟶ X) (g : A ⟶ Y) :
    doubleMappingCylinderLeft f g ≫ doubleMappingCylinderCollapse f g =
      mappingCylinderToPushout f g :=
  pushout.inl_desc _ _ _

@[simp]
public theorem doubleMappingCylinderRight_comp_collapse (f : A ⟶ X) (g : A ⟶ Y) :
    doubleMappingCylinderRight f g ≫ doubleMappingCylinderCollapse f g =
      pushout.inr f g :=
  pushout.inr_desc _ _ _

/-- Reduction from the mapping-cylinder route to two precise comparison inputs: strongification
of the free end and homotopy invariance of the collapse to the ordinary pushout. -/
public theorem pushoutInr_isHomotopyEquivalence_of_mappingCylinder
    (f : A ⟶ X) (g : A ⟶ Y)
    (D : TopCat.StrongDeformationRetractData (mappingCylinderFree f))
    (hcollapse : IsHomotopyEquivalence (doubleMappingCylinderCollapse f g).hom) :
    IsHomotopyEquivalence (pushout.inr f g).hom := by
  have hright : IsHomotopyEquivalence (doubleMappingCylinderRight f g).hom :=
    ⟨doubleMappingCylinderRightHomotopyEquiv f g D, by
      funext y
      exact doubleMappingCylinderRightHomotopyEquiv_apply f g D y⟩
  have hcomp := hcollapse.comp hright
  have hmaps :
      (doubleMappingCylinderCollapse f g).hom.comp
          (doubleMappingCylinderRight f g).hom =
        (pushout.inr f g).hom := by
    exact congrArg (fun k ↦ k.hom)
      (doubleMappingCylinderRight_comp_collapse f g)
  change IsHomotopyEquivalence
    (⇑((doubleMappingCylinderCollapse f g).hom.comp
      (doubleMappingCylinderRight f g).hom)) at hcomp
  rw [hmaps] at hcomp
  exact hcomp

end TopCat

end SphereSixComplex
