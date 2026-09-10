module

public import Mathlib.Geometry.Manifold.SmoothEmbedding

/-!
# Smooth embeddings of disjoint unions

This file supplies local infrastructure for combining smooth embeddings on the two components of a
disjoint union.  Mathlib already proves smoothness of `Sum.map`, but its definition of a global
immersion also asks for one complement which works on every connected component.  The lemmas below
therefore keep that common complement explicit.
-/

@[expose] public section

noncomputable section

open Function Set
open scoped ContDiff Manifold Topology

namespace SphereSixComplex

namespace SmoothEmbeddingSum

variable {k E E' H G M M' N N' F : Type*}
  [NontriviallyNormedField k]
  [NormedAddCommGroup E] [NormedSpace k E]
  [NormedAddCommGroup E'] [NormedSpace k E']
  [NormedAddCommGroup F] [NormedSpace k F]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners k E H} {J : ModelWithCorners k E' G}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace M'] [ChartedSpace H M']
  [TopologicalSpace N] [ChartedSpace G N]
  [TopologicalSpace N'] [ChartedSpace G N']
  {n : ℕ∞ω}

/-- Lifting a chart along the left inclusion preserves membership in the maximal atlas. -/
private lemma liftSumInl_mem_maximalAtlas [Nonempty H]
    [IsManifold I n M] [IsManifold I n M']
    {e : OpenPartialHomeomorph M H} (he : e ∈ IsManifold.maximalAtlas I n M) :
    e.lift_openEmbedding Topology.IsOpenEmbedding.inl ∈
      IsManifold.maximalAtlas I n (M ⊕ M') := by
  rw [IsManifold.mem_maximalAtlas_iff]
  intro e' he'
  obtain (⟨f, hf, rfl⟩ | ⟨f, hf, rfl⟩) := ChartedSpace.mem_atlas_sum he'
  · rw [e.lift_openEmbedding_trans f Topology.IsOpenEmbedding.inl,
      f.lift_openEmbedding_trans e Topology.IsOpenEmbedding.inl]
    exact (IsManifold.mem_maximalAtlas_iff.mp he f hf)
  · constructor
    · apply ContDiffGroupoid.mem_of_source_eq_empty
      ext x
      exact ⟨fun ⟨hx₁, hx₂⟩ ↦ by simp_all, fun hx ↦ hx.elim⟩
    · apply ContDiffGroupoid.mem_of_source_eq_empty
      ext x
      exact ⟨fun ⟨hx₁, hx₂⟩ ↦ by simp_all, fun hx ↦ hx.elim⟩

/-- Lifting a chart along the right inclusion preserves membership in the maximal atlas. -/
private lemma liftSumInr_mem_maximalAtlas [Nonempty H]
    [IsManifold I n M] [IsManifold I n M']
    {e : OpenPartialHomeomorph M' H} (he : e ∈ IsManifold.maximalAtlas I n M') :
    e.lift_openEmbedding Topology.IsOpenEmbedding.inr ∈
      IsManifold.maximalAtlas I n (M ⊕ M') := by
  rw [IsManifold.mem_maximalAtlas_iff]
  intro e' he'
  obtain (⟨f, hf, rfl⟩ | ⟨f, hf, rfl⟩) := ChartedSpace.mem_atlas_sum he'
  · constructor
    · apply ContDiffGroupoid.mem_of_source_eq_empty
      ext x
      exact ⟨fun ⟨hx₁, hx₂⟩ ↦ by simp_all, fun hx ↦ hx.elim⟩
    · apply ContDiffGroupoid.mem_of_source_eq_empty
      ext x
      exact ⟨fun ⟨hx₁, hx₂⟩ ↦ by simp_all, fun hx ↦ hx.elim⟩
  · rw [e.lift_openEmbedding_trans f Topology.IsOpenEmbedding.inr,
      f.lift_openEmbedding_trans e Topology.IsOpenEmbedding.inr]
    exact (IsManifold.mem_maximalAtlas_iff.mp he f hf)

/-- Two immersions with the same specified normal complement combine to an immersion of their
disjoint unions.  The common-complement hypothesis is essential for Mathlib's global
`IsImmersionOfComplement` representation. -/
public theorem isImmersionOfComplement_sumMap
    [IsManifold I n M] [IsManifold I n M']
    [IsManifold J n N] [IsManifold J n N']
    {f : M → N} {g : M' → N'}
    (hf : Manifold.IsImmersionOfComplement F I J n f)
    (hg : Manifold.IsImmersionOfComplement F I J n g) :
    Manifold.IsImmersionOfComplement F I J n (Sum.map f g) := by
  intro x
  cases x with
  | inl x =>
      let : Nonempty H := nonempty_of_chartedSpace x
      let : Nonempty G := nonempty_of_chartedSpace (f x)
      let h := hf x
      apply Manifold.IsImmersionAtOfComplement.mk_of_continuousAt
        ((ContMDiff.sumMap hf.contMDiff hg.contMDiff).continuous.continuousAt)
        h.equiv
        (h.domChart.lift_openEmbedding Topology.IsOpenEmbedding.inl)
        (h.codChart.lift_openEmbedding Topology.IsOpenEmbedding.inl)
        (by simpa using h.mem_domChart_source)
        (by simpa using h.mem_codChart_source)
        (liftSumInl_mem_maximalAtlas h.domChart_mem_maximalAtlas)
        (liftSumInl_mem_maximalAtlas h.codChart_mem_maximalAtlas)
      intro y hy
      simpa [OpenPartialHomeomorph.extend_coe,
        OpenPartialHomeomorph.extend_coe_symm, Function.comp_def,
        Sum.inl_injective.extend_apply h.codChart] using h.writtenInCharts hy
  | inr x =>
      let : Nonempty H := nonempty_of_chartedSpace x
      let : Nonempty G := nonempty_of_chartedSpace (g x)
      let h := hg x
      apply Manifold.IsImmersionAtOfComplement.mk_of_continuousAt
        ((ContMDiff.sumMap hf.contMDiff hg.contMDiff).continuous.continuousAt)
        h.equiv
        (h.domChart.lift_openEmbedding Topology.IsOpenEmbedding.inr)
        (h.codChart.lift_openEmbedding Topology.IsOpenEmbedding.inr)
        (by simpa using h.mem_domChart_source)
        (by simpa using h.mem_codChart_source)
        (liftSumInr_mem_maximalAtlas h.domChart_mem_maximalAtlas)
        (liftSumInr_mem_maximalAtlas h.codChart_mem_maximalAtlas)
      intro y hy
      simpa [OpenPartialHomeomorph.extend_coe,
        OpenPartialHomeomorph.extend_coe_symm, Function.comp_def,
        Sum.inr_injective.extend_apply h.codChart] using h.writtenInCharts hy

/-- Topological embeddings into the two summands combine to a topological embedding. -/
public theorem isEmbedding_sumMap
    {f : M → N} {g : M' → N'}
    (hf : Topology.IsEmbedding f) (hg : Topology.IsEmbedding g) :
    Topology.IsEmbedding (Sum.map f g) := by
  change Topology.IsEmbedding
    (Sum.elim ((@Sum.inl N N') ∘ f) ((@Sum.inr N N') ∘ g))
  apply (Topology.IsEmbedding.inl.comp hf).sumElim_of_separatedNhds
    (Topology.IsEmbedding.inr.comp hg)
  apply (show SeparatedNhds (range (@Sum.inl N N')) (range (@Sum.inr N N')) from
    ⟨range Sum.inl, range Sum.inr, isOpen_range_inl, isOpen_range_inr,
      Subset.rfl, Subset.rfl, by
        apply Set.disjoint_left.2
        rintro _ ⟨x, rfl⟩ ⟨y, h⟩
        simp at h⟩).mono
  · rintro _ ⟨x, rfl⟩
    exact ⟨f x, rfl⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨g x, rfl⟩

/-- Smooth embeddings with one explicitly shared normal complement combine under `Sum.map`. -/
public theorem isSmoothEmbedding_sumMap_of_commonComplement
    [IsManifold I n M] [IsManifold I n M']
    [IsManifold J n N] [IsManifold J n N']
    {f : M → N} {g : M' → N'}
    (hf : Manifold.IsSmoothEmbedding I J n f)
    (hg : Manifold.IsSmoothEmbedding I J n g)
    (hfF : Manifold.IsImmersionOfComplement F I J n f)
    (hgF : Manifold.IsImmersionOfComplement F I J n g) :
    Manifold.IsSmoothEmbedding I J n (Sum.map f g) :=
  ⟨(isImmersionOfComplement_sumMap hfF hgF).isImmersion,
    isEmbedding_sumMap hf.isEmbedding hg.isEmbedding⟩

/-- In finite dimensions, any two normal complements for maps between the same model spaces are
linearly isomorphic.  Consequently two smooth embeddings combine to a smooth embedding of
disjoint unions without exposing complements in the public statement. -/
public theorem isSmoothEmbedding_sumMap
    [CompleteSpace k] [FiniteDimensional k E] [FiniteDimensional k E']
    [IsManifold I n M] [IsManifold I n M']
    [IsManifold J n N] [IsManifold J n N']
    {f : M → N} {g : M' → N'}
    (hf : Manifold.IsSmoothEmbedding I J n f)
    (hg : Manifold.IsSmoothEmbedding I J n g) :
    Manifold.IsSmoothEmbedding I J n (Sum.map f g) := by
  rcases isEmpty_or_nonempty M with hM | hM
  · let := hM
    let hgF := hg.isImmersion.isImmersionOfComplement_complement
    apply isSmoothEmbedding_sumMap_of_commonComplement hf hg (F := hg.isImmersion.complement)
    · exact fun x ↦ isEmptyElim x
    · exact hgF
  rcases isEmpty_or_nonempty M' with hM' | hM'
  · let := hM'
    let hfF := hf.isImmersion.isImmersionOfComplement_complement
    apply isSmoothEmbedding_sumMap_of_commonComplement hf hg (F := hf.isImmersion.complement)
    · exact hfF
    · exact fun x ↦ isEmptyElim x
  let x : M := Classical.choice hM
  let x' : M' := Classical.choice hM'
  let hfF := hf.isImmersion.isImmersionOfComplement_complement
  let hgF := hg.isImmersion.isImmersionOfComplement_complement
  let hfx := hfF x
  let hgx := hgF x'
  let inclF : hf.isImmersion.complement →ₗ[k] E × hf.isImmersion.complement :=
    LinearMap.inr k E hf.isImmersion.complement
  let inclG : hg.isImmersion.complement →ₗ[k] E × hg.isImmersion.complement :=
    LinearMap.inr k E hg.isImmersion.complement
  let normalF : hf.isImmersion.complement →ₗ[k] E' :=
    hfx.equiv.toLinearEquiv.toLinearMap.comp inclF
  let normalG : hg.isImmersion.complement →ₗ[k] E' :=
    hgx.equiv.toLinearEquiv.toLinearMap.comp inclG
  let : FiniteDimensional k hf.isImmersion.complement :=
    FiniteDimensional.of_injective normalF
      (hfx.equiv.injective.comp LinearMap.inr_injective)
  let : FiniteDimensional k hg.isImmersion.complement :=
    FiniteDimensional.of_injective normalG
      (hgx.equiv.injective.comp LinearMap.inr_injective)
  have hfinrank : Module.finrank k hf.isImmersion.complement =
      Module.finrank k hg.isImmersion.complement := by
    have hfDim := hfx.equiv.toLinearEquiv.finrank_eq
    have hgDim := hgx.equiv.toLinearEquiv.finrank_eq
    rw [Module.finrank_prod] at hfDim hgDim
    omega
  let e : hf.isImmersion.complement ≃L[k] hg.isImmersion.complement :=
    ContinuousLinearEquiv.ofFinrankEq hfinrank
  apply isSmoothEmbedding_sumMap_of_commonComplement hf hg (F := hf.isImmersion.complement)
  · exact hfF
  · exact (Manifold.IsImmersionOfComplement.congr_F e).mpr hgF

end SmoothEmbeddingSum

end SphereSixComplex
