module

public import SphereSixComplex.Topology.CubicalSphereQuotient
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Topology.Category.TopCat.Sphere
public import Mathlib.Topology.Compactification.OnePoint.Sphere

/-!
# Comparing the cubical and Euclidean sphere models

The complement of the collapsed boundary point in the cubical sphere is the open cube. This file
identifies that open cube with Euclidean space, proves the boundary quotient Hausdorff, and packages
the resulting one-point-compactification comparison.
-/

@[expose] public section

noncomputable section

open Function Metric Set Topology
open scoped OnePoint Topology unitInterval

namespace SphereSixComplex

/-- The open unit cube, with its product topology. -/
public abbrev OpenCube (N : Type*) := N → Set.Ioo (0 : ℝ) 1

/-- The affine map from `(0, 1)` onto `(-π / 2, π / 2)`. -/
public def openUnitIntervalHomeomorphTanInterval :
    Set.Ioo (0 : ℝ) 1 ≃ₜ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
  ((Homeomorph.image
      (affineHomeomorph Real.pi (-(Real.pi / 2)) Real.pi_ne_zero)
      (Set.Ioo (0 : ℝ) 1)).trans
    (Homeomorph.setCongr (by
      rw [affineHomeomorph_image_Ioo _ _ _ _ Real.pi_pos]
      congr 1 <;> ring))).trans
    (Homeomorph.refl _)

/-- The open interval `(0, 1)` is homeomorphic to the real line. -/
public def openUnitIntervalHomeomorphReal : Set.Ioo (0 : ℝ) 1 ≃ₜ ℝ :=
  openUnitIntervalHomeomorphTanInterval.trans Real.tanOrderIso.toHomeomorph

/-- Coordinatewise tangent identifies the open `N`-cube with Euclidean `N`-space. -/
public def openCubeHomeomorphEuclidean (N : Type*) :
    OpenCube N ≃ₜ EuclideanSpace ℝ N :=
  (Homeomorph.piCongrRight fun _ : N ↦ openUnitIntervalHomeomorphReal).trans
    (PiLp.homeomorph 2 (fun _ : N ↦ ℝ)).symm

/-- Insert the open cube into the closed unit cube. -/
public def openCubeToUnitCube {N : Type*} (a : OpenCube N) : I^N :=
  fun i ↦ ⟨a i, le_of_lt (a i).2.1, le_of_lt (a i).2.2⟩

public theorem openCubeToUnitCube_not_mem_boundary {N : Type*} (a : OpenCube N) :
    openCubeToUnitCube a ∉ Cube.boundary N := by
  rintro ⟨i, hi | hi⟩
  · exact (a i).2.1.ne' (Subtype.ext_iff.mp hi)
  · exact (a i).2.2.ne (Subtype.ext_iff.mp hi)

/-- The open cube maps into the complement of the collapsed boundary point. -/
public def openCubeToCubicalSphere {N : Type*} : OpenCube N → CubicalSphere N :=
  fun a ↦ cubicalSphereMk N (openCubeToUnitCube a)

public theorem continuous_openCubeToUnitCube {N : Type*} :
    Continuous (openCubeToUnitCube : OpenCube N → I^N) := by
  apply continuous_pi
  intro i
  exact (continuous_subtype_val.comp (continuous_apply i)).subtype_mk _

public theorem isClosed_cubeBoundary (N : Type*) [Fintype N] :
    IsClosed (Cube.boundary N) := by
  rw [show Cube.boundary N = ⋃ i : N, {a : I^N | a i = 0 ∨ a i = 1} by
    ext a
    simp [Cube.boundary]]
  apply isClosed_iUnion_of_finite
  intro i
  have hzero : IsClosed {a : I^N | a i = 0} :=
    isClosed_eq (continuous_apply i) continuous_const
  have hone : IsClosed {a : I^N | a i = 1} :=
    isClosed_eq (continuous_apply i) continuous_const
  rw [show {a : I^N | a i = 0 ∨ a i = 1} =
      {a : I^N | a i = 0} ∪ {a : I^N | a i = 1} by ext; simp]
  exact hzero.union hone

/-- The open cube as the literal complement of the cubical boundary. -/
public def openCubeHomeomorphBoundaryComplement (N : Type*) :
    OpenCube N ≃ₜ {a : I^N // a ∉ Cube.boundary N} where
  toFun a := ⟨openCubeToUnitCube a, openCubeToUnitCube_not_mem_boundary a⟩
  invFun a := fun i ↦ ⟨a.1 i, by
    constructor
    · exact lt_of_le_of_ne (a.1 i).2.1 fun h ↦ a.2 ⟨i, Or.inl (Subtype.ext h.symm)⟩
    · exact lt_of_le_of_ne (a.1 i).2.2 fun h ↦ a.2 ⟨i, Or.inr (Subtype.ext h)⟩⟩
  left_inv a := by
    ext i
    rfl
  right_inv a := by
    apply Subtype.ext
    ext i
    rfl
  continuous_toFun := continuous_openCubeToUnitCube.subtype_mk _
  continuous_invFun := by
    apply continuous_pi
    intro i
    exact (continuous_subtype_val.comp
      ((continuous_apply i).comp continuous_subtype_val)).subtype_mk _

public theorem isOpenEmbedding_openCubeToUnitCube (N : Type*) [Fintype N] :
    IsOpenEmbedding (openCubeToUnitCube : OpenCube N → I^N) := by
  have hopen : IsOpen ({a : I^N | a ∉ Cube.boundary N}) :=
    (isClosed_cubeBoundary N).isOpen_compl
  exact (hopen.isOpenEmbedding_subtypeVal.comp
    (openCubeHomeomorphBoundaryComplement N).isOpenEmbedding)

public theorem cubicalSphereMk_preimage_image (N : Type*) (s : Set (I^N)) :
    cubicalSphereMk N ⁻¹' (cubicalSphereMk N '' s) =
      s ∪ {a | a ∈ Cube.boundary N ∧ ∃ b ∈ s, b ∈ Cube.boundary N} := by
  ext a
  constructor
  · rintro ⟨b, hb, hab⟩
    rcases (cubicalSphereMk_eq_iff N _ _).mp hab with rfl | hab
    · exact Or.inl hb
    · exact Or.inr ⟨hab.2, b, hb, hab.1⟩
  · rintro (ha | ⟨ha, b, hb, hb_boundary⟩)
    · exact ⟨a, ha, rfl⟩
    · exact ⟨b, hb, Quotient.sound (Or.inr ⟨hb_boundary, ha⟩)⟩

public theorem isClosedMap_cubicalSphereMk (N : Type*) [Fintype N] :
    IsClosedMap (cubicalSphereMk N) := by
  intro s hs
  rw [← isQuotientMap_quotient_mk'.isCoinducing.isClosed_preimage]
  change IsClosed (cubicalSphereMk N ⁻¹' (cubicalSphereMk N '' s))
  rw [cubicalSphereMk_preimage_image]
  by_cases hboundary : ∃ b ∈ s, b ∈ Cube.boundary N
  · have heq : {a : I^N | a ∈ Cube.boundary N ∧ ∃ b ∈ s, b ∈ Cube.boundary N} =
        Cube.boundary N := by
      ext a
      simp [hboundary]
    rw [heq]
    exact hs.union (isClosed_cubeBoundary N)
  · have heq : {a : I^N | a ∈ Cube.boundary N ∧ ∃ b ∈ s, b ∈ Cube.boundary N} = ∅ := by
      ext a
      simp [hboundary]
    rw [heq, union_empty]
    exact hs

public theorem cubicalSphereMk_fiber_of_mem_boundary (N : Type*) (a : I^N)
    (ha : a ∈ Cube.boundary N) :
    cubicalSphereMk N ⁻¹' {cubicalSphereMk N a} =
      Cube.boundary N := by
  ext b
  simp only [mem_preimage, mem_singleton_iff]
  rw [cubicalSphereMk_eq_iff]
  constructor
  · rintro (rfl | hb)
    · exact ha
    · exact hb.1
  · exact fun hb ↦ Or.inr ⟨hb, ha⟩

public theorem cubicalSphereMk_fiber_of_not_mem_boundary (N : Type*) (a : I^N)
    (ha : a ∉ Cube.boundary N) :
    cubicalSphereMk N ⁻¹' {cubicalSphereMk N a} = {a} := by
  ext b
  simp only [mem_preimage, mem_singleton_iff]
  rw [cubicalSphereMk_eq_iff]
  constructor
  · rintro (rfl | hb)
    · rfl
    · exact (ha hb.2).elim
  · exact Or.inl

/-- Collapsing the closed boundary of a finite cube produces a Hausdorff quotient. -/
public instance cubicalSphereT2Space (N : Type*) [Fintype N] : T2Space (CubicalSphere N) where
  t2 x y hxy := by
    obtain ⟨a, rfl⟩ := Quotient.exists_rep x
    obtain ⟨b, rfl⟩ := Quotient.exists_rep y
    let A : Set (I^N) := cubicalSphereMk N ⁻¹' {cubicalSphereMk N a}
    let B : Set (I^N) := cubicalSphereMk N ⁻¹' {cubicalSphereMk N b}
    have hA : IsClosed A := by
      change IsClosed (cubicalSphereMk N ⁻¹' {cubicalSphereMk N a})
      by_cases ha : a ∈ Cube.boundary N
      · rw [cubicalSphereMk_fiber_of_mem_boundary N a ha]
        exact isClosed_cubeBoundary N
      · rw [cubicalSphereMk_fiber_of_not_mem_boundary N a ha]
        exact isClosed_singleton
    have hB : IsClosed B := by
      change IsClosed (cubicalSphereMk N ⁻¹' {cubicalSphereMk N b})
      by_cases hb : b ∈ Cube.boundary N
      · rw [cubicalSphereMk_fiber_of_mem_boundary N b hb]
        exact isClosed_cubeBoundary N
      · rw [cubicalSphereMk_fiber_of_not_mem_boundary N b hb]
        exact isClosed_singleton
    have hAB : Disjoint A B := by
      rw [Set.disjoint_left]
      intro z hzA hzB
      change cubicalSphereMk N z = cubicalSphereMk N a at hzA
      change cubicalSphereMk N z = cubicalSphereMk N b at hzB
      exact hxy (hzA.symm.trans hzB)
    obtain ⟨U, V, hU, hV, hAU, hBV, hUV⟩ := normal_separation hA hB hAB
    refine ⟨(cubicalSphereMk N '' Uᶜ)ᶜ, (cubicalSphereMk N '' Vᶜ)ᶜ,
      (isClosedMap_cubicalSphereMk N Uᶜ hU.isClosed_compl).isOpen_compl,
      (isClosedMap_cubicalSphereMk N Vᶜ hV.isClosed_compl).isOpen_compl, ?_, ?_, ?_⟩
    · intro haU
      rcases haU with ⟨z, hz, hza⟩
      exact hz (hAU (show z ∈ A by exact hza))
    · intro hbV
      rcases hbV with ⟨z, hz, hzb⟩
      exact hz (hBV (show z ∈ B by exact hzb))
    · rw [Set.disjoint_left]
      intro q hqU hqV
      obtain ⟨z, rfl⟩ := Quotient.exists_rep q
      have hzU : z ∈ U := by
        by_contra hz
        exact hqU ⟨z, hz, rfl⟩
      have hzV : z ∈ V := by
        by_contra hz
        exact hqV ⟨z, hz, rfl⟩
      exact Set.disjoint_left.mp hUV hzU hzV

public theorem continuous_openCubeToCubicalSphere {N : Type*} :
    Continuous (openCubeToCubicalSphere : OpenCube N → CubicalSphere N) :=
  (cubicalSphereMk N).continuous.comp continuous_openCubeToUnitCube

public theorem openCubeToCubicalSphere_injective {N : Type*} :
    Injective (openCubeToCubicalSphere : OpenCube N → CubicalSphere N) := by
  intro a b hab
  change cubicalSphereMk N (openCubeToUnitCube a) =
    cubicalSphereMk N (openCubeToUnitCube b) at hab
  rw [cubicalSphereMk_eq_iff] at hab
  rcases hab with hab | hab
  · ext i
    exact congr_arg ((↑) : I → ℝ) (congr_fun hab i)
  · exact (openCubeToUnitCube_not_mem_boundary a hab.1).elim

public theorem openCubeToCubicalSphere_range [Nonempty N] :
    range (openCubeToCubicalSphere : OpenCube N → CubicalSphere N) =
      {cubicalSphereBasepoint N}ᶜ := by
  ext q
  constructor
  · rintro ⟨a, rfl⟩ hbase
    change cubicalSphereMk N (openCubeToUnitCube a) =
      cubicalSphereMk N (fun _ : N ↦ (0 : I)) at hbase
    rw [cubicalSphereMk_eq_iff] at hbase
    rcases hbase with hbase | hbase
    · have hzero : openCubeToUnitCube a ∈ Cube.boundary N := by
        rw [hbase]
        exact ⟨Classical.arbitrary N, Or.inl rfl⟩
      exact openCubeToUnitCube_not_mem_boundary a hzero
    · exact openCubeToUnitCube_not_mem_boundary a hbase.1
  · intro hq
    obtain ⟨a, rfl⟩ := Quotient.exists_rep q
    have ha : a ∉ Cube.boundary N := by
      intro ha
      exact hq (cubicalSphereMk_eq_basepoint_of_mem_boundary ha)
    let b : OpenCube N := fun i ↦ ⟨a i, by
      constructor
      · exact lt_of_le_of_ne (a i).2.1 fun h ↦ ha ⟨i, Or.inl (Subtype.ext h.symm)⟩
      · exact lt_of_le_of_ne (a i).2.2 fun h ↦ ha ⟨i, Or.inr (Subtype.ext h)⟩⟩
    refine ⟨b, ?_⟩
    apply congr_arg (cubicalSphereMk N)
    ext i
    rfl

/-- The cubical quotient is canonically the one-point compactification of its open cell. -/
public def onePointOpenCubeHomeomorphCubicalSphere
    (N : Type*) [Fintype N] [Nonempty N] :
    OnePoint (OpenCube N) ≃ₜ CubicalSphere N :=
  OnePoint.equivOfIsEmbeddingOfRangeEq
    (cubicalSphereBasepoint N) openCubeToCubicalSphere
    (by
      exact (IsOpenEmbedding.of_continuous_injective_isOpenMap
        continuous_openCubeToCubicalSphere openCubeToCubicalSphere_injective fun s hs ↦ by
          rw [← isQuotientMap_quotient_mk'.isCoinducing.isOpen_preimage]
          have himage :
              (@Quotient.mk' _ (cubeBoundarySetoid N)) ⁻¹'
                  (openCubeToCubicalSphere '' s) = openCubeToUnitCube '' s := by
            ext a
            constructor
            · rintro ⟨b, hb, hab⟩
              have hab' : cubicalSphereMk N a =
                  cubicalSphereMk N (openCubeToUnitCube b) := hab.symm
              rcases (cubicalSphereMk_eq_iff N _ _).mp hab' with hab | hab
              · exact ⟨b, hb, hab.symm⟩
              · exact (openCubeToUnitCube_not_mem_boundary b hab.2).elim
            · rintro ⟨b, hb, rfl⟩
              exact ⟨b, hb, rfl⟩
          rw [himage]
          exact (isOpenEmbedding_openCubeToUnitCube N).isOpenMap s hs).isEmbedding)
    (openCubeToCubicalSphere_range (N := N))

@[simp]
public theorem onePointOpenCubeHomeomorphCubicalSphere_apply_coe
    (N : Type*) [Fintype N] [Nonempty N] (a : OpenCube N) :
    onePointOpenCubeHomeomorphCubicalSphere N (a : OnePoint (OpenCube N)) =
      openCubeToCubicalSphere a :=
  rfl

@[simp]
public theorem onePointOpenCubeHomeomorphCubicalSphere_apply_infty
    (N : Type*) [Fintype N] [Nonempty N] :
    onePointOpenCubeHomeomorphCubicalSphere N (∞ : OnePoint (OpenCube N)) =
      cubicalSphereBasepoint N :=
  rfl

@[simp]
public theorem onePointOpenCubeHomeomorphCubicalSphere_symm_basepoint
    (N : Type*) [Fintype N] [Nonempty N] :
    (onePointOpenCubeHomeomorphCubicalSphere N).symm (cubicalSphereBasepoint N) =
      (∞ : OnePoint (OpenCube N)) := by
  apply (onePointOpenCubeHomeomorphCubicalSphere N).injective
  simp

/-- The comparison from the cubical `n`-sphere to the ordinary Euclidean unit sphere. -/
public def cubicalSphereHomeomorphMetricSphere
    (n : ℕ) [NeZero n] :
    CubicalSphere (Fin n) ≃ₜ
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
  (onePointOpenCubeHomeomorphCubicalSphere (Fin n)).symm |>.trans
    ((openCubeHomeomorphEuclidean (Fin n)).onePointCongr |>.trans
      (onePointEquivSphereOfFinrankEq (ι := Fin (n + 1))
        (V := EuclideanSpace ℝ (Fin n)) (by simp)))

/-- The point corresponding to infinity in the one-point compactification model of `S^n`. -/
public def topCatSphereCompactificationPoint (n : ℕ) : TopCat.sphere n :=
  Homeomorph.ulift.symm
    (onePointEquivSphereOfFinrankEq (ι := Fin (n + 1))
      (V := EuclideanSpace ℝ (Fin n)) (by simp) (∞ : OnePoint (EuclideanSpace ℝ (Fin n))))

/-- The cubical boundary quotient is homeomorphic to Mathlib's `TopCat.sphere`. -/
public def cubicalSphereHomeomorphTopCatSphere
    (n : ℕ) [NeZero n] :
    CubicalSphere (Fin n) ≃ₜ TopCat.sphere n :=
  (cubicalSphereHomeomorphMetricSphere n).trans Homeomorph.ulift.symm

@[simp]
public theorem cubicalSphereHomeomorphTopCatSphere_basepoint
    (n : ℕ) [NeZero n] :
    cubicalSphereHomeomorphTopCatSphere n (cubicalSphereBasepoint (Fin n)) =
      topCatSphereCompactificationPoint n := by
  change Homeomorph.ulift.symm
      (onePointEquivSphereOfFinrankEq (ι := Fin (n + 1))
        (V := EuclideanSpace ℝ (Fin n)) (by simp)
        ((openCubeHomeomorphEuclidean (Fin n)).onePointCongr
          ((onePointOpenCubeHomeomorphCubicalSphere (Fin n)).symm
            (cubicalSphereBasepoint (Fin n))))) =
    topCatSphereCompactificationPoint n
  rw [onePointOpenCubeHomeomorphCubicalSphere_symm_basepoint]
  rfl

end SphereSixComplex
