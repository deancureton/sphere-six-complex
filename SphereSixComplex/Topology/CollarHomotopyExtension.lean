module

public import SphereSixComplex.Topology.CollaredBordism
public import SphereSixComplex.Topology.MapHomotopyEquivalence
public import SphereSixComplex.Topology.PushoutHomotopy

/-!
# Homotopy data supplied by an explicit collar

An explicit collar makes its zero section a strong deformation retract of the *collar
neighbourhood*.  This file records that fact in the form used by `PushoutHomotopy` and transports
it across the collar chart.  It also isolates the relative path-lifting property which is needed
to upgrade a homotopy-equivalent inclusion to a strong deformation retract of the whole ambient
space.

The local construction is completely explicit: at time `s`, the collar parameter `t` is replaced
by `s * t`.  No collar-gluing, cofibration, or homotopy-extension theorem is assumed.
-/

@[expose] public section

noncomputable section

open CategoryTheory ContinuousMap Function Set TopologicalSpace Topology
open scoped ContDiff Manifold Topology

namespace SphereSixComplex

universe u uE uH uM uW

/-- Scale a point of the half-open collar parameter towards its zero endpoint. -/
public def halfCollarScale (s : unitInterval) (t : HalfCollarParameter) :
    HalfCollarParameter :=
  ⟨⟨(s : ℝ) * (t.1 : ℝ), by
      constructor
      · exact mul_nonneg s.2.1 t.1.2.1
      · calc
          (s : ℝ) * (t.1 : ℝ) ≤ 1 * (t.1 : ℝ) :=
            mul_le_mul_of_nonneg_right s.2.2 t.1.2.1
          _ ≤ 1 := by simpa using t.1.2.2⟩, by
    have hs : (s : ℝ) ≤ 1 := s.2.2
    have ht0 : 0 ≤ (t.1 : ℝ) := t.1.2.1
    have ht1 : (t.1 : ℝ) < 1 := t.2
    calc
      (s : ℝ) * (t.1 : ℝ) ≤ 1 * (t.1 : ℝ) :=
        mul_le_mul_of_nonneg_right hs ht0
      _ < 1 := by simpa using ht1⟩

@[simp]
public theorem halfCollarScale_zero (t : HalfCollarParameter) :
    halfCollarScale 0 t = halfCollarStart := by
  apply Subtype.ext
  apply Subtype.ext
  simp [halfCollarScale, halfCollarStart, collarStart]

@[simp]
public theorem halfCollarScale_one (t : HalfCollarParameter) :
    halfCollarScale 1 t = t := by
  apply Subtype.ext
  apply Subtype.ext
  simp [halfCollarScale]

@[simp]
public theorem halfCollarScale_start (s : unitInterval) :
    halfCollarScale s halfCollarStart = halfCollarStart := by
  apply Subtype.ext
  apply Subtype.ext
  simp [halfCollarScale, halfCollarStart, collarStart]

/-- Joint continuity of collar scaling in the time and collar variables. -/
public theorem continuous_halfCollarScale :
    Continuous (fun p : unitInterval × HalfCollarParameter ↦
      halfCollarScale p.1 p.2) := by
  have hReal : Continuous (fun p : unitInterval × HalfCollarParameter ↦
      (p.1 : ℝ) * (p.2.1 : ℝ)) :=
    (continuous_subtype_val.comp continuous_fst).mul
      ((continuous_subtype_val.comp continuous_subtype_val).comp continuous_snd)
  have hIcc : Continuous (fun p : unitInterval × HalfCollarParameter ↦
      (⟨(p.1 : ℝ) * (p.2.1 : ℝ), (halfCollarScale p.1 p.2).1.2⟩ :
        CollarParameter)) :=
    hReal.subtype_mk _
  exact hIcc.subtype_mk _

/-- The zero section of the standard half-open collar, as a morphism of topological spaces. -/
public def halfCollarZeroSection (M : Type u) [TopologicalSpace M] :
    TopCat.of M ⟶ TopCat.of (CollarSource M) :=
  TopCat.ofHom
    ⟨collarSourceZeroSection M, continuous_id.prodMk continuous_const⟩

/-- Projection of a standard half-open collar back to its zero section. -/
public def halfCollarProjection (M : Type u) [TopologicalSpace M] :
    TopCat.of (CollarSource M) ⟶ TopCat.of M :=
  TopCat.ofHom ⟨Prod.fst, continuous_fst⟩

/-- Radial contraction of the standard half-open collar onto its zero section. -/
public def halfCollarHomotopy (M : Type u) [TopologicalSpace M] :
    TopCat.Homotopy
      (halfCollarProjection M ≫ halfCollarZeroSection M)
      (𝟙 (TopCat.of (CollarSource M))) where
  toFun p := (p.2.1, halfCollarScale p.1 p.2.2)
  continuous_toFun := continuous_snd.fst.prodMk
    (continuous_halfCollarScale.comp (continuous_fst.prodMk continuous_snd.snd))
  map_zero_left p := by
    apply Prod.ext
    · rfl
    · exact halfCollarScale_zero p.2
  map_one_left p := by
    apply Prod.ext
    · rfl
    · exact halfCollarScale_one p.2

/-- The zero section is a strong deformation retract of the standard half-open collar. -/
public def halfCollarStrongDeformationRetract (M : Type u) [TopologicalSpace M] :
    TopCat.StrongDeformationRetractData (halfCollarZeroSection M) where
  retraction := halfCollarProjection M
  retract := by
    ext x
    rfl
  homotopy := halfCollarHomotopy M
  fixed s x := by
    change (x, halfCollarScale s halfCollarStart) = (x, halfCollarStart)
    rw [halfCollarScale_start]

variable {A X : TopCat.{u}} {i : A ⟶ X}

/-- A strong deformation retract presents its inclusion as a bundled homotopy equivalence. -/
public def strongDeformationRetractHomotopyEquiv
    (D : TopCat.StrongDeformationRetractData i) :
    (A : Type u) ≃ₕ (X : Type u) where
  toFun := i.hom
  invFun := D.retraction.hom
  left_inv := by
    have h : D.retraction.hom.comp i.hom = ContinuousMap.id A := by
      ext a
      exact CategoryTheory.congr_fun D.retract a
    rw [h]
  right_inv := ⟨D.homotopy⟩

@[simp]
public theorem strongDeformationRetractHomotopyEquiv_apply
    (D : TopCat.StrongDeformationRetractData i) (a : A) :
    strongDeformationRetractHomotopyEquiv D a = i a :=
  rfl

/-- Transport strong deformation-retract data across a homeomorphism of the ambient space. -/
public def transportStrongDeformationRetract
    (D : TopCat.StrongDeformationRetractData i)
    {Y : Type u} [TopologicalSpace Y] (e : (X : Type u) ≃ₜ Y) :
    TopCat.StrongDeformationRetractData
      (i ≫ TopCat.ofHom ⟨e, e.continuous⟩) where
  retraction := TopCat.ofHom ⟨e.symm, e.symm.continuous⟩ ≫ D.retraction
  retract := by
    ext a
    change D.retraction (e.symm (e (i a))) = a
    rw [e.symm_apply_apply]
    exact CategoryTheory.congr_fun D.retract a
  homotopy :=
    { toFun := fun p ↦ e (D.homotopy (p.1, e.symm p.2))
      continuous_toFun := e.continuous.comp
        (D.homotopy.continuous.comp
          (continuous_fst.prodMk (e.symm.continuous.comp continuous_snd)))
      map_zero_left := fun y ↦ by
        change e (D.homotopy (0, e.symm y)) =
          e (i (D.retraction (e.symm y)))
        exact congrArg e (D.homotopy.map_zero_left (e.symm y))
      map_one_left := fun y ↦ by
        change e (D.homotopy (1, e.symm y)) = y
        calc
          e (D.homotopy (1, e.symm y)) = e (e.symm y) :=
            congrArg e (D.homotopy.map_one_left (e.symm y))
          _ = y := e.apply_symm_apply y }
  fixed s a := by
    change e (D.homotopy (s, e.symm (e (i a)))) = e (i a)
    rw [e.symm_apply_apply]
    exact congrArg e (D.fixed s a)

/-- The zero section, transported into the open target of a collar chart. -/
public def collarTargetZeroSection
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type uH} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {W : Type u} [TopologicalSpace W]
    [ChartedSpace (ModelProd H (EuclideanHalfSpace 1)) W]
    (c : SmoothCollar I M W) :
    TopCat.of M ⟶ TopCat.of c.chart.target :=
  halfCollarZeroSection M ≫
    TopCat.ofHom ⟨c.chart.toDiffeomorph.toHomeomorph,
      c.chart.toDiffeomorph.toHomeomorph.continuous⟩

@[simp]
public theorem collarTargetZeroSection_apply
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type uH} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {W : Type u} [TopologicalSpace W]
    [ChartedSpace (ModelProd H (EuclideanHalfSpace 1)) W]
    (c : SmoothCollar I M W) (m : M) :
    collarTargetZeroSection c m =
      c.chart.toDiffeomorph (collarSourceZeroSection M m) :=
  rfl

/-- A collar zero section is a strong deformation retract of the collar chart's open target. -/
public def collarTargetStrongDeformationRetract
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type uH} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {W : Type u} [TopologicalSpace W]
    [ChartedSpace (ModelProd H (EuclideanHalfSpace 1)) W]
    (c : SmoothCollar I M W) :
    TopCat.StrongDeformationRetractData (collarTargetZeroSection c) :=
  transportStrongDeformationRetract (halfCollarStrongDeformationRetract M)
    c.chart.toDiffeomorph.toHomeomorph

/-- The zero section into the open target of a collar chart is a homotopy equivalence. -/
public theorem isHomotopyEquivalence_collarTargetZeroSection
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type uH} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {W : Type u} [TopologicalSpace W]
    [ChartedSpace (ModelProd H (EuclideanHalfSpace 1)) W]
    (c : SmoothCollar I M W) :
    IsHomotopyEquivalence (collarTargetZeroSection c) :=
  ⟨strongDeformationRetractHomotopyEquiv
      (collarTargetStrongDeformationRetract c), rfl⟩

/-- For a compact end in a Hausdorff ambient space, the global collar inclusion is closed as well
as embedded.  This is the closedness input in the usual cofibration proof for collars. -/
public theorem SmoothCollar.inclusion_isClosedEmbedding
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type uH} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M]
    {W : Type uW} [TopologicalSpace W] [T2Space W]
    [ChartedSpace (ModelProd H (EuclideanHalfSpace 1)) W]
    (c : SmoothCollar I M W) :
    IsClosedEmbedding c.inclusion :=
  c.inclusion_contMDiff.continuous.isClosedEmbedding
    c.inclusion_isEmbedding.injective

/-- The ambient zero-section map of a collar, bundled in `TopCat`. -/
public def collarAmbientZeroSection
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type uH} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {W : Type u} [TopologicalSpace W]
    [ChartedSpace (ModelProd H (EuclideanHalfSpace 1)) W]
    (c : SmoothCollar I M W) : TopCat.of M ⟶ TopCat.of W :=
  TopCat.ofHom ⟨c.inclusion, c.inclusion_contMDiff.continuous⟩

/-- A closed inclusion together with an open neighbourhood on which it is a strong deformation
retract.  This packages exactly the topological data supplied by a compact collar before invoking
the (currently absent from Mathlib) closed-NDR/cofibration theorem. -/
public structure ClosedNeighborhoodDeformationRetractData
    {A X : TopCat.{u}} (i : A ⟶ X) where
  neighborhood : Opens X
  localInclusion : A ⟶ TopCat.of neighborhood
  localStrong : TopCat.StrongDeformationRetractData localInclusion
  factor : localInclusion ≫
    TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ = i
  isClosedEmbedding : IsClosedEmbedding i

/-- A compact collar in a Hausdorff ambient space supplies closed-neighbourhood deformation-
retract data. -/
public def SmoothCollar.closedNeighborhoodDeformationRetractData
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type uH} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M]
    {W : Type u} [TopologicalSpace W] [T2Space W]
    [ChartedSpace (ModelProd H (EuclideanHalfSpace 1)) W]
    (c : SmoothCollar I M W) :
    ClosedNeighborhoodDeformationRetractData (collarAmbientZeroSection c) where
  neighborhood := c.chart.target
  localInclusion := collarTargetZeroSection c
  localStrong := collarTargetStrongDeformationRetract c
  factor := by
    ext m
    rfl
  isClosedEmbedding := c.inclusion_isClosedEmbedding

/-! ## The precise global homotopy-extension interface -/

variable {A₀ X₀ : Type u} [TopologicalSpace A₀] [TopologicalSpace X₀]

/-- Homotopy-extension data for a specified inclusion.  This is the usual HEP formulation: a
homotopy on the subspace which starts as the restriction of an ambient map extends to an ambient
homotopy, with equality on the subspace at every time.

It is kept as an explicit proposition because pinned Mathlib has no topological cofibration API. -/
public structure HomotopyExtensionProperty (i : C(A₀, X₀)) : Prop where
  extend : ∀ {Y : Type u} [TopologicalSpace Y]
      (f : C(X₀, Y)) {h₁ : C(A₀, Y)}
      (H : ContinuousMap.Homotopy (f.comp i) h₁),
    ∃ (f₁ : C(X₀, Y)) (F : ContinuousMap.Homotopy f f₁),
      ∀ (t : unitInterval) (a : A₀), F (t, i a) = H (t, a)

/-- A (not necessarily strong) deformation-retract package.  The endpoint homotopy need not fix
the image of the inclusion pointwise. -/
public structure DeformationRetractData (i : C(A₀, X₀)) where
  retraction : C(X₀, A₀)
  retract : retraction.comp i = ContinuousMap.id A₀
  homotopy : ContinuousMap.Homotopy
    (i.comp retraction) (ContinuousMap.id X₀)

namespace DeformationRetractData

variable {i₀ : C(A₀, X₀)} (D : DeformationRetractData i₀)

/-- A deformation retract whose homotopy fixes the included subspace gives the strong package
used by the pushout theorem. -/
public def toStrong
    (fixed : ∀ (t : unitInterval) (a : A₀), D.homotopy (t, i₀ a) = i₀ a) :
    TopCat.StrongDeformationRetractData (TopCat.ofHom i₀) where
  retraction := TopCat.ofHom D.retraction
  retract := by
    ext a
    exact ContinuousMap.congr_fun D.retract a
  homotopy := D.homotopy
  fixed := fixed

end DeformationRetractData

/-- HEP strictifies the inverse of a homotopy-equivalent inclusion and produces an ordinary
deformation retract.  The only datum still absent from a strong deformation retract is the
pointwise fixedness of the final homotopy. -/
public theorem HomotopyExtensionProperty.exists_deformationRetractData
    {i₀ : C(A₀, X₀)} (hep : HomotopyExtensionProperty i₀)
    (hi : IsHomotopyEquivalence i₀) :
    Nonempty (DeformationRetractData i₀) := by
  obtain ⟨e, he⟩ := hi
  have he' : e.toFun = i₀ := by
    ext a
    exact congrFun he a
  let L₀ : ContinuousMap.Homotopy (e.invFun.comp e.toFun) (ContinuousMap.id A₀) :=
    e.left_inv.some
  let L : ContinuousMap.Homotopy (e.invFun.comp i₀) (ContinuousMap.id A₀) :=
    L₀.cast (by rw [← he']) rfl
  obtain ⟨r, F, hF⟩ := hep.extend e.invFun L
  have hr : r.comp i₀ = ContinuousMap.id A₀ := by
    ext a
    calc
      r (i₀ a) = F (1, i₀ a) := (F.map_one_left (i₀ a)).symm
      _ = L (1, a) := hF 1 a
      _ = a := L.map_one_left a
  let K₀ : ContinuousMap.Homotopy (e.toFun.comp e.invFun) (ContinuousMap.id X₀) :=
    e.right_inv.some
  let K : ContinuousMap.Homotopy (i₀.comp e.invFun) (ContinuousMap.id X₀) :=
    K₀.cast (by rw [← he']) rfl
  let iF : ContinuousMap.Homotopy (i₀.comp e.invFun) (i₀.comp r) :=
    (ContinuousMap.Homotopy.refl i₀).comp F
  exact ⟨{
    retraction := r
    retract := hr
    homotopy := iF.symm.trans K }⟩

/-- The standard half-collar zero section is a homotopy equivalence. -/
public theorem isHomotopyEquivalence_halfCollarZeroSection
    (M : Type u) [TopologicalSpace M] :
    IsHomotopyEquivalence (collarSourceZeroSection M) :=
  ⟨strongDeformationRetractHomotopyEquiv (halfCollarStrongDeformationRetract M), rfl⟩

end SphereSixComplex
