module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.ContMDiff.Basic
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import all Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Transporting local diffeomorphisms

Two general facts about `IsLocalDiffeomorph` that the analytic construction needs and Mathlib
does not yet provide.

* `isLocalDiffeomorph_of_contDiff_of_hasFDerivAt_equiv`: the inverse function theorem, packaged as
  a local diffeomorphism between model spaces.  Mathlib has the normed-space statement
  (`ContDiffAt.toOpenPartialHomeomorph`) but not its manifold consequence.
* `isLocalDiffeomorph_of_comp_isOpenEmbedding`: if the charted-space structure on the target comes
  from an open embedding, a map into it is a local diffeomorphism as soon as its composite with
  that embedding is.
Together they reduce a local-biholomorphism claim about an explicitly coordinatized map to a
derivative computation.
-/

@[expose] public section

open Set Topology
open scoped ContDiff Manifold

namespace SphereSixComplex

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F H'} {n : ℕ∞ω}

/-! ## The inverse function theorem as a local diffeomorphism -/

/-- Inverse function theorem: a `C^∞` map between model spaces whose derivative is everywhere a
continuous linear equivalence is a local diffeomorphism. -/
public theorem isLocalDiffeomorph_of_contDiff_of_hasFDerivAt_equiv
    {𝕂 : Type*} [RCLike 𝕂]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕂 E'] [CompleteSpace E']
    {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕂 F']
    {f : E' → F'} (hf : ContDiff 𝕂 ∞ f)
    (h : ∀ x, ∃ f' : E' ≃L[𝕂] F', HasFDerivAt f (f' : E' →L[𝕂] F') x) :
    IsLocalDiffeomorph 𝓘(𝕂, E') 𝓘(𝕂, F') ∞ f := by
  intro x
  obtain ⟨f', hf'⟩ := h x
  let Φ : OpenPartialHomeomorph E' F' :=
    (hf.contDiffAt (x := x)).toOpenPartialHomeomorph f hf' (by simp)
  refine ⟨{ toPartialEquiv := Φ.toPartialEquiv
            open_source := Φ.open_source
            open_target := Φ.open_target
            contMDiffOn_toFun := ?_
            contMDiffOn_invFun := ?_ }, ?_, ?_⟩
  · exact contMDiffOn_iff_contDiffOn.mpr hf.contDiffOn
  · refine contMDiffOn_iff_contDiffOn.mpr ?_
    intro y hy
    obtain ⟨g', hg'⟩ := h (Φ.symm y)
    exact ((Φ.contDiffAt_symm hy hg' hf.contDiffAt).contDiffWithinAt)
  · exact ContDiffAt.mem_toOpenPartialHomeomorph_source (n := ∞) hf.contDiffAt hf' (by simp)
  · intro y _
    rfl

/-! ## Transport through an open-embedding chart -/

section OfCompOpenEmbedding

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [Nonempty N] {g : N → H'} (hg : IsOpenEmbedding g)

/-- If the charted-space structure on `N` is the one induced by an open embedding `g : N → H'`,
then a map into `N` is a local diffeomorphism as soon as its composite with `g` is. -/
public theorem isLocalDiffeomorph_of_comp_isOpenEmbedding {f : M → N}
    (h : letI := hg.singletonChartedSpace; IsLocalDiffeomorph I J n (g ∘ f)) :
    letI := hg.singletonChartedSpace
    IsLocalDiffeomorph I J n f := by
  letI := hg.singletonChartedSpace
  intro x
  obtain ⟨Φ, hxΦ, hΦ⟩ := h x
  set e := hg.toOpenPartialHomeomorph g with he
  have hetarget : e.target = range g := hg.toOpenPartialHomeomorph_target
  set T : OpenPartialHomeomorph M N := Φ.toOpenPartialHomeomorph.trans e.symm with hT
  have hTsource : T.source = Φ.source ∩ Φ ⁻¹' range g := by
    rw [hT, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source, hetarget]
    rfl
  have hmapsTarget : MapsTo g T.target Φ.target := by
    intro y hy
    rw [hT, OpenPartialHomeomorph.trans_target] at hy
    have hy2 : e y ∈ Φ.target := hy.2
    have hey : e y = g y := rfl
    rwa [hey] at hy2
  refine ⟨{ toPartialEquiv := T.toPartialEquiv
            open_source := T.open_source
            open_target := T.open_target
            contMDiffOn_toFun := ?_
            contMDiffOn_invFun := ?_ }, ?_, ?_⟩
  · have hcomp : ContMDiffOn I J n (fun y => e.symm (Φ y)) T.source := by
      refine (contMDiffOn_isOpenEmbedding_symm hg).comp
        (Φ.contMDiffOn_toFun.mono (by rw [hTsource]; exact fun y hy => hy.1)) ?_
      intro y hy
      rw [hTsource] at hy
      exact hy.2
    exact hcomp
  · have hcomp : ContMDiffOn J I n (fun y => Φ.symm (g y)) T.target :=
      Φ.contMDiffOn_invFun.comp (contMDiff_isOpenEmbedding hg).contMDiffOn hmapsTarget
    exact hcomp
  · show x ∈ T.source
    rw [hTsource]
    refine ⟨hxΦ, ?_⟩
    have hx : (Φ : M → H') x = g (f x) := (hΦ hxΦ).symm
    show (Φ : M → H') x ∈ range g
    rw [hx]
    exact mem_range_self _
  · intro y hy
    rw [show T.source = Φ.source ∩ Φ ⁻¹' range g from hTsource] at hy
    have hgy : (Φ : M → H') y = g (f y) := (hΦ hy.1).symm
    show f y = e.symm ((Φ : M → H') y)
    rw [hgy, hg.toOpenPartialHomeomorph_left_inv]

end OfCompOpenEmbedding

/-! ## The inclusion of an open subset -/

section OpenSubtype

variable {X : Type*} [TopologicalSpace X] [ChartedSpace H X]

/-- The inclusion of an open subset, as a partial diffeomorphism onto its image. -/
public noncomputable def openSubtypeValPartialDiffeomorph
    (U : TopologicalSpace.Opens X) [Nonempty U] : PartialDiffeomorph I I U X ∞ := by
  let f : U → X := Subtype.val
  let hopen : IsOpenEmbedding f := U.2.isOpenEmbedding_subtypeVal
  exact {
    toPartialEquiv := (hopen.toOpenPartialHomeomorph f).toPartialEquiv
    open_source := isOpen_univ
    open_target := by
      rw [hopen.toOpenPartialHomeomorph_target]
      change IsOpen (Set.range (Subtype.val : U → X))
      rw [Subtype.range_val]
      exact U.2
    contMDiffOn_toFun := contMDiff_subtype_val.contMDiffOn
    contMDiffOn_invFun := by
      intro y hy
      apply (ContMDiffWithinAt.subtypeVal_comp_iff U _ _ y).mp
      apply contMDiffAt_id.contMDiffWithinAt.congr
      · intro z hz
        exact IsOpenEmbedding.toOpenPartialHomeomorph_right_inv f hopen
          (by rwa [hopen.toOpenPartialHomeomorph_target] at hz)
      · exact IsOpenEmbedding.toOpenPartialHomeomorph_right_inv f hopen
          (by rwa [hopen.toOpenPartialHomeomorph_target] at hy)
  }

/-- The inclusion of an open subset is a local diffeomorphism. -/
public theorem openSubtypeVal_isLocalDiffeomorph (U : TopologicalSpace.Opens X) :
    IsLocalDiffeomorph I I ∞ (Subtype.val : U → X) := by
  intro x
  let _ : Nonempty U := ⟨x⟩
  exact (openSubtypeValPartialDiffeomorph (I := I) U).isLocalDiffeomorphAt I I ∞
    (show x ∈ Set.univ from Set.mem_univ x)

end OpenSubtype

end SphereSixComplex
