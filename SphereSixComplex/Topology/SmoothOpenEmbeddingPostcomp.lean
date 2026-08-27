module

public import SphereSixComplex.Topology.SmoothOpenGluingInclusions
public import Mathlib.Geometry.Manifold.SmoothEmbedding

/-!
# Smooth embeddings and open changes of codomain

This file supplies the two composition facts needed when collars are moved into an open piece and
then into the glued manifold.  They are proved directly from the chart definition of a smooth
immersion; in particular, they do not use Mathlib's currently unfinished general composition
theorem for smooth embeddings.
-/

@[expose] public section

noncomputable section

open Function Set Topology TopologicalSpace
open scoped ContDiff Manifold Topology

namespace SphereSixComplex

universe u𝕜 uE uF uH uG uM uN uP

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type uH} [TopologicalSpace H]
  {G : Type uG} [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H}
  {J : ModelWithCorners 𝕜 F G}
  {M : Type uM} {N : Type uN} {P : Type uP}
  [TopologicalSpace M] [ChartedSpace G M]
  [TopologicalSpace N] [ChartedSpace H N]
  [TopologicalSpace P] [ChartedSpace H P]

namespace Manifold.IsSmoothEmbedding

/-- Restrict a maximal smooth chart to an open subtype of its source manifold. -/
private theorem subtypeRestr_mem_maximalAtlas
    [IsManifold I ∞ N] (U : Opens N) (hU : Nonempty U)
    {c : OpenPartialHomeomorph N H}
    (hc : c ∈ IsManifold.maximalAtlas I ∞ N) :
    c.subtypeRestr hU ∈ IsManifold.maximalAtlas I ∞ U := by
  apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
  · have hc' : ContMDiffOn I I ∞ c c.source :=
      contMDiffOn_of_mem_maximalAtlas hc
    have hcomp : ContMDiffOn I I ∞ (c ∘ (Subtype.val : U → N))
        ((c.subtypeRestr hU).source) :=
      hc'.comp (contMDiff_subtype_val (I := I)).contMDiffOn (by
        intro x hx
        simpa only [OpenPartialHomeomorph.subtypeRestr_source, Set.mem_preimage] using hx)
    exact hcomp.congr fun _ _ ↦ rfl
  · have hc' : ContMDiffOn I I ∞ c.symm c.target :=
      contMDiffOn_symm_of_mem_maximalAtlas hc
    have hambient : ContMDiffOn I I ∞
        (Subtype.val ∘ (c.subtypeRestr hU).symm) (c.subtypeRestr hU).target :=
      (hc'.mono (c.subtypeRestr_target_subset hU)).congr
        (c.subtypeRestr_symm_eqOn hU).symm
    intro y hy
    exact (ContMDiffWithinAt.subtypeVal_comp_iff U _ _ _).mp (hambient y hy)

/-- A smooth embedding whose range lies in an open set remains a smooth embedding after its
codomain is restricted to that open set. -/
public theorem _root_.Manifold.IsSmoothEmbedding.codRestrictOpens
    [IsManifold I ∞ N] {g : M → N}
    (hg : Manifold.IsSmoothEmbedding J I ∞ g)
    (U : Opens N) (hU : ∀ x, g x ∈ U) :
    Manifold.IsSmoothEmbedding J I ∞ (fun x ↦ ⟨g x, hU x⟩ : M → U) := by
  let gU : M → U := fun x ↦ ⟨g x, hU x⟩
  have hgU_contMDiff : ContMDiff J I ∞ gU := by
    apply (ContMDiff.subtypeVal_comp_iff U gU).mp
    exact hg.contMDiff.congr fun _ ↦ rfl
  constructor
  · have hImm : Manifold.IsImmersion J I ∞ gU := by
      apply Manifold.IsImmersionOfComplement.isImmersion
        (F := hg.isImmersion.complement)
      intro x
      let hx := hg.isImmersion.isImmersionOfComplement_complement x
      let hUne : Nonempty U := ⟨gU x⟩
      let cU : OpenPartialHomeomorph U H := hx.codChart.subtypeRestr hUne
      apply Manifold.IsImmersionAtOfComplement.mk_of_continuousAt
        hgU_contMDiff.continuous.continuousAt hx.equiv hx.domChart cU
        hx.mem_domChart_source
      · simpa only [cU, OpenPartialHomeomorph.subtypeRestr_source, Set.mem_preimage,
          gU] using hx.mem_codChart_source
      · exact hx.domChart_mem_maximalAtlas
      · exact subtypeRestr_mem_maximalAtlas U hUne hx.codChart_mem_maximalAtlas
      · intro y hy
        simpa only [Function.comp_apply, cU, gU,
          OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.subtypeRestr_coe,
          Set.domRestrict_apply] using hx.writtenInCharts hy
    exact hImm.congr rfl
  · exact hg.isEmbedding.codRestrict (U : Set N) hU

namespace SmoothOpenEmbedding

/-- The inverse of the open partial homeomorphism underlying a smooth open embedding is smooth
on its source. -/
private theorem openPartialHomeomorph_symm_contMDiffOn
    (f : SmoothOpenEmbedding I N P) [Nonempty N] :
    ContMDiffOn I I ∞ (f.isOpenEmbedding.toOpenPartialHomeomorph f).symm
      (f.isOpenEmbedding.toOpenPartialHomeomorph f).symm.source := by
  let e := f.isOpenEmbedding.toOpenPartialHomeomorph f
  change ContMDiffOn I I ∞ e.symm e.symm.source
  intro y hy
  have hy_range : y ∈ Set.range f := by
    simpa only [e, OpenPartialHomeomorph.symm_source,
      Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target] using hy
  obtain ⟨z, rfl⟩ := hy_range
  let y' : f.target := f.toDiffeomorph z
  have hy'_val : (y' : P) = f z := rfl
  have hinverse : ContMDiff I I ∞
      (fun q : f.target ↦ e.symm (q : P)) := by
    apply f.toDiffeomorph.contMDiff_invFun.congr
    intro q
    apply f.isOpenEmbedding.isEmbedding.injective
    rw [f.isOpenEmbedding.toOpenPartialHomeomorph_right_inv]
    · exact congrArg Subtype.val (f.toDiffeomorph.apply_symm_apply q) |>.symm
    · exact ⟨f.toDiffeomorph.symm q,
        congrArg Subtype.val (f.toDiffeomorph.apply_symm_apply q)⟩
  have hat : ContMDiffAt I I ∞ e.symm (f z) := by
    rw [← hy'_val]
    exact contMDiffAt_subtype_iff.mp (hinverse y')
  exact hat.contMDiffWithinAt

/-- Transporting a maximal chart through a smooth open embedding gives a maximal chart on the
ambient target. -/
private theorem pushedChart_mem_maximalAtlas
    [IsManifold I ∞ P] (f : SmoothOpenEmbedding I N P) [Nonempty N]
    {c : OpenPartialHomeomorph N H}
    (hc : c ∈ IsManifold.maximalAtlas I ∞ N) :
    (f.isOpenEmbedding.toOpenPartialHomeomorph f).symm.trans c ∈
      IsManifold.maximalAtlas I ∞ P := by
  let e := f.isOpenEmbedding.toOpenPartialHomeomorph f
  let cP := e.symm.trans c
  change cP ∈ IsManifold.maximalAtlas I ∞ P
  apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
  · have hc' : ContMDiffOn I I ∞ c c.source :=
      contMDiffOn_of_mem_maximalAtlas hc
    have he' : ContMDiffOn I I ∞ e.symm e.symm.source :=
      openPartialHomeomorph_symm_contMDiffOn f
    have hcomp : ContMDiffOn I I ∞ (c ∘ e.symm) cP.source :=
      hc'.comp (he'.mono (by
        intro y hy
        exact hy.1)) (by
          intro y hy
          exact hy.2)
    exact hcomp.congr fun _ _ ↦ rfl
  · have hc' : ContMDiffOn I I ∞ c.symm c.target :=
      contMDiffOn_symm_of_mem_maximalAtlas hc
    have hcomp : ContMDiffOn I I ∞ (f ∘ c.symm) cP.target :=
      f.contMDiff.comp_contMDiffOn (hc'.mono (by
        intro y hy
        exact hy.1))
    exact hcomp.congr fun y hy ↦ by
      change f (c.symm y) = cP.symm y
      rfl

end SmoothOpenEmbedding

/-- Postcomposing a smooth embedding with a smooth open embedding preserves smooth embeddedness.

This is the open-codomain case of Mathlib's unfinished general composition theorem.  Its proof
transports the immersion's codomain chart across the explicit open diffeomorphism. -/
public theorem _root_.Manifold.IsSmoothEmbedding.comp_smoothOpenEmbedding
    [IsManifold I ∞ P] {g : M → N}
    (hg : Manifold.IsSmoothEmbedding J I ∞ g)
    (f : SmoothOpenEmbedding I N P) :
    Manifold.IsSmoothEmbedding J I ∞ (f ∘ g) := by
  constructor
  · cases isEmpty_or_nonempty N with
    | inl hempty =>
        letI : IsEmpty N := hempty
        apply Manifold.IsImmersionOfComplement.isImmersion (F := Unit)
        intro x
        exact isEmptyElim (g x)
    | inr hnonempty =>
        letI : Nonempty N := hnonempty
        apply Manifold.IsImmersionOfComplement.isImmersion
          (F := hg.isImmersion.complement)
        intro x
        let hx := hg.isImmersion.isImmersionOfComplement_complement x
        let e := f.isOpenEmbedding.toOpenPartialHomeomorph f
        let cP : OpenPartialHomeomorph P H := e.symm.trans hx.codChart
        apply Manifold.IsImmersionAtOfComplement.mk_of_continuousAt
          (f.contMDiff.comp hg.contMDiff).continuous.continuousAt
          hx.equiv hx.domChart cP hx.mem_domChart_source
        · change f (g x) ∈ e.symm.source ∩ e.symm ⁻¹' hx.codChart.source
          constructor
          · change f (g x) ∈ e.target
            simpa only [e, Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target] using
              (show f (g x) ∈ Set.range f from ⟨g x, rfl⟩)
          · change e.symm (f (g x)) ∈ hx.codChart.source
            rw [show e.symm (f (g x)) = g x by
              exact f.isOpenEmbedding.toOpenPartialHomeomorph_left_inv]
            exact hx.mem_codChart_source
        · exact hx.domChart_mem_maximalAtlas
        · exact SmoothOpenEmbedding.pushedChart_mem_maximalAtlas f
            hx.codChart_mem_maximalAtlas
        · intro y hy
          simpa only [Function.comp_apply, cP, e,
            OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.trans_apply,
            Topology.IsOpenEmbedding.toOpenPartialHomeomorph_left_inv] using
            hx.writtenInCharts hy
  · exact f.isOpenEmbedding.isEmbedding.comp hg.isEmbedding

end Manifold.IsSmoothEmbedding

end SphereSixComplex
