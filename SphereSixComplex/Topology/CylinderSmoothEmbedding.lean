module

public import Mathlib.Geometry.Manifold.Instances.Icc

/-!
# Smooth endpoint sections of a manifold cylinder

Mathlib has a smooth manifold structure on the closed interval and a product construction for
manifolds with corners.  It does not yet provide the corresponding smooth-embedding theorem for
the two endpoint sections `x ↦ (x, 0)` and `x ↦ (x, 1)`.  This file proves those two small lemmas
directly from the chart definition of `Manifold.IsImmersionOfComplement`.

These are elementary cylinder facts.  They do not use a collar-neighbourhood theorem, a gluing
theorem, or any h-cobordism input.
-/

@[expose] public section

noncomputable section

open Function Set
open scoped ContDiff Manifold Topology

namespace SphereSixComplex

/-- The compact interval used to parameterize explicit collars. -/
public abbrev CollarParameter := Set.Icc (0 : ℝ) 1

/-- The initial endpoint of `CollarParameter`. -/
public def collarStart : CollarParameter := ⟨0, by norm_num⟩

/-- The final endpoint of `CollarParameter`. -/
public def collarFinish : CollarParameter := ⟨1, by norm_num⟩

@[simp]
public theorem collarStart_val : (collarStart : ℝ) = 0 := rfl

@[simp]
public theorem collarFinish_val : (collarFinish : ℝ) = 1 := rfl

/-- Which endpoint of the collar parameter is attached to the boundary component. -/
public inductive CollarSide where
  | start
  | finish
  deriving DecidableEq

/-- The endpoint selected by a collar side. -/
public def CollarSide.parameter : CollarSide → CollarParameter
  | .start => collarStart
  | .finish => collarFinish

/-- The selected endpoint section of a cylinder. -/
public def CollarSide.section (side : CollarSide) (M : Type*) : M → M × CollarParameter :=
  fun x => (x, side.parameter)

@[simp]
public theorem CollarSide.section_apply (side : CollarSide) {M : Type*} (x : M) :
    side.section M x = (x, side.parameter) := rfl

/-- Reflection of the collar parameter, exchanging its two endpoints. -/
public def collarReflection (t : CollarParameter) : CollarParameter :=
  ⟨1 - t, by
    constructor
    · linarith [t.property.2]
    · linarith [t.property.1]⟩

@[simp]
public theorem collarReflection_val (t : CollarParameter) :
    (collarReflection t : ℝ) = 1 - t :=
  rfl

@[simp]
public theorem collarReflection_involutive (t : CollarParameter) :
    collarReflection (collarReflection t) = t := by
  apply Subtype.ext
  simp

@[simp]
public theorem collarReflection_start : collarReflection collarStart = collarFinish := by
  apply Subtype.ext
  norm_num [collarReflection, collarStart, collarFinish]

@[simp]
public theorem collarReflection_finish : collarReflection collarFinish = collarStart := by
  apply Subtype.ext
  norm_num [collarReflection, collarStart, collarFinish]

/-- Reflection is a smooth self-diffeomorphism of the closed collar parameter. -/
public def collarReflectionDiffeomorph :
    CollarParameter ≃ₘ⟮(𝓡∂ 1), (𝓡∂ 1)⟯ CollarParameter where
  toEquiv :=
    { toFun := collarReflection
      invFun := collarReflection
      left_inv := collarReflection_involutive
      right_inv := collarReflection_involutive }
  contMDiff_toFun := by
    apply contMDiff_iff_comp_subtypeVal_Icc.mpr
    constructor
    · exact (continuous_const.sub continuous_subtype_val).subtype_mk _
    · have h : ContDiff ℝ ∞ (fun x : ℝ ↦ 1 - x) := by fun_prop
      change ContMDiff (𝓡∂ 1) (modelWithCornersSelf ℝ ℝ) ∞
        (fun x : Set.Icc (0 : ℝ) 1 ↦ 1 - (x : ℝ))
      exact h.comp_contMDiff
        (contMDiff_subtypeVal_Icc (x := (0 : ℝ)) (y := 1) (n := ∞))
  contMDiff_invFun := by
    apply contMDiff_iff_comp_subtypeVal_Icc.mpr
    constructor
    · exact (continuous_const.sub continuous_subtype_val).subtype_mk _
    · have h : ContDiff ℝ ∞ (fun x : ℝ ↦ 1 - x) := by fun_prop
      change ContMDiff (𝓡∂ 1) (modelWithCornersSelf ℝ ℝ) ∞
        (fun x : Set.Icc (0 : ℝ) 1 ↦ 1 - (x : ℝ))
      exact h.comp_contMDiff
        (contMDiff_subtypeVal_Icc (x := (0 : ℝ)) (y := 1) (n := ∞))

/-- The half-open parameter neighborhood `[0, 1)` inside the closed interval. -/
public def collarStartNeighborhood : TopologicalSpace.Opens CollarParameter where
  carrier := {t | (t : ℝ) < 1}
  is_open' := isOpen_Iio.preimage continuous_subtype_val

/-- The half-open parameter neighborhood `(0, 1]` inside the closed interval. -/
public def collarFinishNeighborhood : TopologicalSpace.Opens CollarParameter where
  carrier := {t | 0 < (t : ℝ)}
  is_open' := isOpen_Ioi.preimage continuous_subtype_val

@[simp]
public theorem mem_collarStartNeighborhood (t : CollarParameter) :
    t ∈ collarStartNeighborhood ↔ (t : ℝ) < 1 :=
  Iff.rfl

@[simp]
public theorem mem_collarFinishNeighborhood (t : CollarParameter) :
    t ∈ collarFinishNeighborhood ↔ 0 < (t : ℝ) :=
  Iff.rfl

/-- The standard half-open collar domain `M × [0, 1)`, represented as an open submanifold
of the closed cylinder. -/
public def CollarDomain (M : Type*) [TopologicalSpace M] :
    TopologicalSpace.Opens (M × CollarParameter) where
  carrier := {p | p.2 ∈ collarStartNeighborhood}
  is_open' := collarStartNeighborhood.isOpen.preimage continuous_snd

/-- The reflected half-open collar domain `M × (0, 1]`. -/
public def ReflectedCollarDomain (M : Type*) [TopologicalSpace M] :
    TopologicalSpace.Opens (M × CollarParameter) where
  carrier := {p | p.2 ∈ collarFinishNeighborhood}
  is_open' := collarFinishNeighborhood.isOpen.preimage continuous_snd

/-- The zero section as a point of the standard half-open collar domain. -/
public def collarZeroSection (M : Type*) [TopologicalSpace M] (x : M) : CollarDomain M :=
  ⟨(x, collarStart), by
    norm_num [CollarDomain, collarStartNeighborhood, collarStart]⟩

/-- The one section as a point of the reflected half-open collar domain. -/
public def collarOneSection (M : Type*) [TopologicalSpace M] (x : M) :
    ReflectedCollarDomain M :=
  ⟨(x, collarFinish), by
    norm_num [ReflectedCollarDomain, collarFinishNeighborhood, collarFinish]⟩

@[simp]
public theorem collarZeroSection_val (M : Type*) [TopologicalSpace M] (x : M) :
    (collarZeroSection M x : M × CollarParameter) = (x, collarStart) :=
  rfl

@[simp]
public theorem collarOneSection_val (M : Type*) [TopologicalSpace M] (x : M) :
    (collarOneSection M x : M × CollarParameter) = (x, collarFinish) :=
  rfl

variable {E₀ H₀ M₀ : Type*} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
  [TopologicalSpace H₀] {I₀ : ModelWithCorners ℝ E₀ H₀}
  [TopologicalSpace M₀] [ChartedSpace H₀ M₀]

/-- Product reflection identifies the standard and reflected half-open collar domains. -/
public def collarDomainReflection :
    CollarDomain M₀ ≃ₘ⟮I₀.prod (𝓡∂ 1), I₀.prod (𝓡∂ 1)⟯ ReflectedCollarDomain M₀ where
  toEquiv :=
    { toFun := fun p ↦ ⟨(p.1.1, collarReflection p.1.2), by
          change 0 < (collarReflection p.1.2 : ℝ)
          rw [collarReflection_val]
          exact sub_pos.mpr p.2⟩
      invFun := fun p ↦ ⟨(p.1.1, collarReflection p.1.2), by
          change (collarReflection p.1.2 : ℝ) < 1
          rw [collarReflection_val]
          have hp := p.property
          change 0 < (p.1.2 : ℝ) at hp
          linarith [hp]⟩
      left_inv := by
        intro p
        apply Subtype.ext
        exact Prod.ext rfl (collarReflection_involutive p.1.2)
      right_inv := by
        intro p
        apply Subtype.ext
        exact Prod.ext rfl (collarReflection_involutive p.1.2) }
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff (ReflectedCollarDomain M₀) _).mp
    exact (contMDiff_fst.comp contMDiff_subtype_val).prodMk
      (collarReflectionDiffeomorph.contMDiff.comp
        (contMDiff_snd.comp contMDiff_subtype_val))
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff (CollarDomain M₀) _).mp
    exact (contMDiff_fst.comp contMDiff_subtype_val).prodMk
      (collarReflectionDiffeomorph.contMDiff.comp
        (contMDiff_snd.comp contMDiff_subtype_val))

@[simp]
public theorem collarDomainReflection_apply (p : CollarDomain M₀) :
    (collarDomainReflection (I₀ := I₀) p : M₀ × CollarParameter) =
      (p.1.1, collarReflection p.1.2) :=
  rfl

/-- The half-open interval `[0, 1)` with its inherited manifold-with-boundary structure. -/
public abbrev HalfCollarParameter := collarStartNeighborhood

/-- The distinguished zero of the half-open collar parameter. -/
public def halfCollarStart : HalfCollarParameter :=
  ⟨collarStart, by norm_num [collarStartNeighborhood, collarStart]⟩

/-- The standard source type for an explicit collar. -/
public abbrev CollarSource (M : Type*) [TopologicalSpace M] := M × HalfCollarParameter

/-- The zero section of the standard collar source. -/
public def collarSourceZeroSection (M : Type*) [TopologicalSpace M] (x : M) :
    CollarSource M :=
  (x, halfCollarStart)

@[simp]
public theorem collarSourceZeroSection_apply (M : Type*) [TopologicalSpace M] (x : M) :
    collarSourceZeroSection M x = (x, halfCollarStart) :=
  rfl

/-- The natural diffeomorphism from `M × [0, 1)` to the corresponding open submanifold of
the closed cylinder. -/
public def collarSourceToDomain :
    CollarSource M₀ ≃ₘ⟮I₀.prod (𝓡∂ 1), I₀.prod (𝓡∂ 1)⟯ CollarDomain M₀ where
  toEquiv :=
    { toFun := fun p ↦ ⟨(p.1, p.2.1), p.2.2⟩
      invFun := fun p ↦ (p.1.1, ⟨p.1.2, p.2⟩)
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff (CollarDomain M₀) _).mp
    exact contMDiff_fst.prodMk (contMDiff_subtype_val.comp contMDiff_snd)
  contMDiff_invFun := by
    apply contMDiff_fst.comp contMDiff_subtype_val |>.prodMk
    apply (ContMDiff.subtypeVal_comp_iff collarStartNeighborhood _).mp
    exact contMDiff_snd.comp contMDiff_subtype_val

/-- Reflection identifies the standard collar source with the open neighborhood at the other end
of the closed cylinder. -/
public def collarSourceToReflectedDomain :
    CollarSource M₀ ≃ₘ⟮I₀.prod (𝓡∂ 1), I₀.prod (𝓡∂ 1)⟯ ReflectedCollarDomain M₀ :=
  (collarSourceToDomain (I₀ := I₀)).trans (collarDomainReflection (I₀ := I₀))

@[simp]
public theorem collarSourceToDomain_apply (p : CollarSource M₀) :
    (collarSourceToDomain (I₀ := I₀) p : M₀ × CollarParameter) =
      (p.1, p.2.1) :=
  rfl

@[simp]
public theorem collarSourceToReflectedDomain_apply (p : CollarSource M₀) :
    (collarSourceToReflectedDomain (I₀ := I₀) p : M₀ × CollarParameter) =
      (p.1, collarReflection p.2.1) :=
  rfl

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The initial endpoint section is a smooth embedding of codimension one. -/
public theorem isSmoothEmbedding_collarStartSection :
    Manifold.IsSmoothEmbedding I (I.prod (𝓡∂ 1)) ∞
      (fun x : M => (x, collarStart)) := by
  constructor
  · apply Manifold.IsImmersionOfComplement.isImmersion
      (F := EuclideanSpace ℝ (Fin 1))
    intro x
    apply Manifold.IsImmersionAtOfComplement.mk_of_continuousAt
      (continuousAt_id.prodMk continuousAt_const)
      (ContinuousLinearEquiv.refl ℝ (E × EuclideanSpace ℝ (Fin 1)))
      (chartAt H x)
      (chartAt (ModelProd H (EuclideanHalfSpace 1)) (x, collarStart))
      (mem_chart_source H x) (mem_chart_source _ (x, collarStart))
      (IsManifold.chart_mem_maximalAtlas x)
      (IsManifold.chart_mem_maximalAtlas (x, collarStart))
    intro y hy
    simp only [Function.comp_apply]
    simp
    constructor
    · rw [(chartAt H x).right_inv (by simp_all), I.right_inv (by simp_all)]
    · norm_num [collarStart, IccLeftChart]
      rfl
  · exact isEmbedding_prodMkLeft collarStart

/-- The final endpoint section is a smooth embedding of codimension one. -/
public theorem isSmoothEmbedding_collarFinishSection :
    Manifold.IsSmoothEmbedding I (I.prod (𝓡∂ 1)) ∞
      (fun x : M => (x, collarFinish)) := by
  constructor
  · apply Manifold.IsImmersionOfComplement.isImmersion
      (F := EuclideanSpace ℝ (Fin 1))
    intro x
    apply Manifold.IsImmersionAtOfComplement.mk_of_continuousAt
      (continuousAt_id.prodMk continuousAt_const)
      (ContinuousLinearEquiv.refl ℝ (E × EuclideanSpace ℝ (Fin 1)))
      (chartAt H x)
      (chartAt (ModelProd H (EuclideanHalfSpace 1)) (x, collarFinish))
      (mem_chart_source H x) (mem_chart_source _ (x, collarFinish))
      (IsManifold.chart_mem_maximalAtlas x)
      (IsManifold.chart_mem_maximalAtlas (x, collarFinish))
    intro y hy
    simp only [Function.comp_apply]
    simp
    constructor
    · rw [(chartAt H x).right_inv (by simp_all), I.right_inv (by simp_all)]
    · norm_num [collarFinish, IccRightChart]
      rfl
  · exact isEmbedding_prodMkLeft collarFinish

/-- Either endpoint section selected by `CollarSide` is a smooth embedding. -/
public theorem CollarSide.isSmoothEmbedding_section (side : CollarSide) :
    Manifold.IsSmoothEmbedding I (I.prod (𝓡∂ 1)) ∞ (side.section M) := by
  cases side with
  | start => exact isSmoothEmbedding_collarStartSection
  | finish => exact isSmoothEmbedding_collarFinishSection

end SphereSixComplex
