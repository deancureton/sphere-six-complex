module

public import SphereSixComplex.Topology.SmoothOpenGluingCompatibility
public import SphereSixComplex.Topology.SmoothOpenEmbedding
public import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Smooth canonical inclusions into an open gluing

The charted-space structure on an open gluing is built by pushing the charts of every piece
through its canonical open embedding.  Once those pushed charts are compatible, the canonical
piece inclusions are `C^n`; at infinite regularity they bundle as smooth open embeddings.
-/

@[expose] public section

noncomputable section

set_option linter.style.haveILetI false

open Filter Function Set TopologicalSpace Topology
open scoped ContDiff Manifold Topology

namespace SphereSixComplex

universe u v

section

variable {H : Type v} [TopologicalSpace H]
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  (D : TopCat.GlueData.{u}) [∀ i, ChartedSpace H (D.U i)]
  (I : ModelWithCorners 𝕜 E H) (n : WithTop ℕ∞)

/-- Every pushed piece chart belongs to the maximal atlas of the compatible open gluing. -/
public theorem openGluingPieceChart_mem_maximalAtlas
    (hcompat : OpenGluingSmoothCompatibility D I n)
    (p : Sigma fun i ↦ (D.U i : Type u)) :
    openGluingPieceChart D p ∈
      @IsManifold.maximalAtlas 𝕜 _ E _ _ H _ I n D.toGlueData.glued _
        (openGluingChartedSpace D) := by
  letI : ChartedSpace H D.toGlueData.glued := openGluingChartedSpace D
  letI : IsManifold I n D.toGlueData.glued :=
    openGluing_isManifold_of_pieceChart_compatible D I n hcompat
  apply StructureGroupoid.subset_maximalAtlas (contDiffGroupoid n I)
  exact ⟨p, rfl⟩

/-- The open range of a canonical piece inclusion. -/
public def openGluingPieceTarget (i : D.J) : Opens D.toGlueData.glued where
  carrier := Set.range (D.toGlueData.ι i)
  is_open' := (D.ι_isOpenEmbedding i).isOpen_range

variable [∀ i, IsManifold I n (D.U i)]

/-- A canonical piece inclusion into a compatible open gluing is `C^n`. -/
public theorem openGluing_pieceInclusion_contMDiff
    (hcompat : OpenGluingSmoothCompatibility D I n) (i : D.J) :
    @ContMDiff 𝕜 _ E _ _ H _ I (D.U i) _ _ E _ _ H _ I
      D.toGlueData.glued _ (openGluingChartedSpace D) n (D.toGlueData.ι i) := by
  letI : ChartedSpace H D.toGlueData.glued := openGluingChartedSpace D
  letI : IsManifold I n D.toGlueData.glued :=
    openGluing_isManifold_of_pieceChart_compatible D I n hcompat
  intro x
  letI : Nonempty (D.U i : Type u) := ⟨x⟩
  let c : OpenPartialHomeomorph (D.U i) H := chartAt H x
  let g : OpenPartialHomeomorph D.toGlueData.glued H :=
    openGluingPieceChart D ⟨i, x⟩
  have hg_mem : g ∈ IsManifold.maximalAtlas I n D.toGlueData.glued := by
    exact openGluingPieceChart_mem_maximalAtlas D I n hcompat ⟨i, x⟩
  have hg_symm : ContMDiffOn I I n g.symm g.target :=
    contMDiffOn_symm_of_mem_maximalAtlas hg_mem
  have hc : ContMDiffOn I I n c c.source := contMDiffOn_chart
  have hmaps : MapsTo c c.source g.target := by
    intro y hy
    simp only [g, openGluingPieceChart, c, OpenPartialHomeomorph.trans_target,
      OpenPartialHomeomorph.symm_target,
      Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source, Set.mem_inter_iff,
      Set.mem_preimage]
    exact ⟨c.mapsTo hy, Set.mem_univ _⟩
  have hcomp : ContMDiffOn I I n (g.symm ∘ c) c.source :=
    hg_symm.comp hc hmaps
  have heq : EqOn (g.symm ∘ c) (D.toGlueData.ι i) c.source := by
    intro y hy
    simp only [g, openGluingPieceChart, c,
      OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm, Function.comp_apply,
      OpenPartialHomeomorph.trans_apply,
      Topology.IsOpenEmbedding.toOpenPartialHomeomorph_apply]
    rw [c.left_inv hy]
  have hev : D.toGlueData.ι i =ᶠ[𝓝 x] (g.symm ∘ c) := by
    filter_upwards [c.open_source.mem_nhds (mem_chart_source H x)] with y hy
    exact (heq hy).symm
  exact (hcomp x (mem_chart_source H x)).contMDiffAt
    (c.open_source.mem_nhds (mem_chart_source H x)) |>.congr_of_eventuallyEq hev

/-- On the open range of a canonical piece inclusion, its topological inverse is `C^n`.

The `Nonempty` assumption is only needed to form Mathlib's total-function presentation of the
inverse of an open embedding.  The bundled smooth-open-embedding theorem below removes this
assumption by treating an empty piece separately. -/
public theorem openGluing_pieceInclusion_inverse_contMDiffOn
    (hcompat : OpenGluingSmoothCompatibility D I n) (i : D.J)
    [Nonempty (D.U i : Type u)] :
    @ContMDiffOn 𝕜 _ E _ _ H _ I D.toGlueData.glued _
      (openGluingChartedSpace D) E _ _ H _ I (D.U i) _ _ n
        ((D.ι_isOpenEmbedding i).toOpenPartialHomeomorph (D.toGlueData.ι i)).symm
        (Set.range (D.toGlueData.ι i)) := by
  letI : ChartedSpace H D.toGlueData.glued := openGluingChartedSpace D
  letI : IsManifold I n D.toGlueData.glued :=
    openGluing_isManifold_of_pieceChart_compatible D I n hcompat
  let e : OpenPartialHomeomorph (D.U i) D.toGlueData.glued :=
    (D.ι_isOpenEmbedding i).toOpenPartialHomeomorph _
  intro y hy
  let x : D.U i := e.symm y
  let c : OpenPartialHomeomorph (D.U i) H := chartAt H x
  let ex : OpenPartialHomeomorph (D.U i) D.toGlueData.glued := by
    letI : Nonempty (D.U i : Type u) := ⟨x⟩
    exact (D.ι_isOpenEmbedding i).toOpenPartialHomeomorph _
  let g : OpenPartialHomeomorph D.toGlueData.glued H :=
    openGluingPieceChart D ⟨i, x⟩
  have g_eq : g = ex.symm.trans c := by
    rfl
  have hg_mem : g ∈ IsManifold.maximalAtlas I n D.toGlueData.glued :=
    openGluingPieceChart_mem_maximalAtlas D I n hcompat ⟨i, x⟩
  have hg : ContMDiffOn I I n g g.source :=
    contMDiffOn_of_mem_maximalAtlas hg_mem
  have hc_symm : ContMDiffOn I I n c.symm c.target := contMDiffOn_chart_symm
  have hgtarget : g.target ⊆ c.target := by
    intro z hz
    simpa only [g, openGluingPieceChart, c, OpenPartialHomeomorph.trans_target,
      Set.mem_inter_iff] using hz.1
  have hmaps : MapsTo g g.source c.target := fun _ hz ↦ hgtarget (g.mapsTo hz)
  have hcomp : ContMDiffOn I I n (c.symm ∘ g) g.source :=
    hc_symm.comp hg hmaps
  have hy_source : y ∈ g.source := by
    simp only [g, openGluingPieceChart, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.symm_source,
      Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target, Set.mem_inter_iff,
      Set.mem_preimage]
    exact ⟨hy, mem_chart_source H x⟩
  have heq : EqOn (c.symm ∘ g) e.symm g.source := by
    intro z hz
    have hz' : z ∈ ex.symm.source ∩ ex.symm ⁻¹' c.source := by
      rwa [g_eq, OpenPartialHomeomorph.trans_source] at hz
    have hz_c : ex.symm z ∈ c.source := hz'.2
    have hz_range : z ∈ Set.range (D.toGlueData.ι i) := by
      simpa only [ex, OpenPartialHomeomorph.symm_source,
        Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target] using hz'.1
    have hex_e : ex.symm z = e.symm z := by
      apply (D.ι_isOpenEmbedding i).isEmbedding.injective
      rw [show D.toGlueData.ι i (ex.symm z) = z by
        simpa only [ex] using
          (D.ι_isOpenEmbedding i).toOpenPartialHomeomorph_right_inv
            (D.toGlueData.ι i) hz_range]
    change c.symm (g z) = e.symm z
    rw [g_eq, OpenPartialHomeomorph.trans_apply, c.left_inv hz_c, hex_e]
  have hev : e.symm =ᶠ[𝓝 y] (c.symm ∘ g) := by
    filter_upwards [g.open_source.mem_nhds hy_source] with z hz
    exact (heq hz).symm
  exact ((hcomp y hy_source).contMDiffAt (g.open_source.mem_nhds hy_source)).congr_of_eventuallyEq
    hev |>.contMDiffWithinAt

end

section Smooth

variable {H : Type v} [TopologicalSpace H]
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  (D : TopCat.GlueData.{u}) [∀ i, ChartedSpace H (D.U i)]
  (I : ModelWithCorners 𝕜 E H) [∀ i, IsManifold I ∞ (D.U i)]

/-- Each canonical piece map of a smoothly compatible open gluing, bundled as a smooth open
embedding.  This construction also covers an empty piece. -/
public noncomputable def openGluingPieceSmoothOpenEmbedding
    (hcompat : OpenGluingSmoothCompatibility D I ∞) (i : D.J) :
    @SmoothOpenEmbedding 𝕜 _ E _ _ H _ I (D.U i) D.toGlueData.glued _ _ _
      (openGluingChartedSpace D) := by
  classical
  letI : ChartedSpace H D.toGlueData.glued := openGluingChartedSpace D
  let target : Opens D.toGlueData.glued := openGluingPieceTarget D i
  let homeo : (D.U i : Type u) ≃ₜ target :=
    (D.ι_isOpenEmbedding i).isEmbedding.toHomeomorph
  refine
    { target := target
      toDiffeomorph :=
        { toEquiv := homeo.toEquiv
          contMDiff_toFun := ?_
          contMDiff_invFun := ?_ } }
  · apply (ContMDiff.subtypeVal_comp_iff target homeo).mp
    have hforward := openGluing_pieceInclusion_contMDiff D I ∞ hcompat i
    have heq : (Subtype.val ∘ homeo) = D.toGlueData.ι i := by
      funext x
      rfl
    rwa [heq]
  · cases isEmpty_or_nonempty (D.U i : Type u) with
    | inl hempty =>
        intro y
        obtain ⟨x, _⟩ := y.property
        exact (hempty.false x).elim
    | inr hnonempty =>
        letI : Nonempty (D.U i : Type u) := hnonempty
        let e : OpenPartialHomeomorph (D.U i) D.toGlueData.glued :=
          (D.ι_isOpenEmbedding i).toOpenPartialHomeomorph _
        have hinverse : ContMDiff I I ∞ (e.symm ∘ (Subtype.val : target → _)) :=
          (openGluing_pieceInclusion_inverse_contMDiffOn D I ∞ hcompat i).comp_contMDiff
            (contMDiff_subtype_val (I := I)) fun z ↦ z.property
        apply hinverse.congr
        intro z
        apply (D.ι_isOpenEmbedding i).isEmbedding.injective
        have hhomeo : D.toGlueData.ι i (homeo.symm z) = z.1 := by
          exact congrArg Subtype.val (homeo.apply_symm_apply z)
        calc
          D.toGlueData.ι i (homeo.symm z) = z.1 := hhomeo
          _ = D.toGlueData.ι i (e.symm z.1) :=
            ((D.ι_isOpenEmbedding i).toOpenPartialHomeomorph_right_inv
              (D.toGlueData.ι i) z.property).symm
          _ = D.toGlueData.ι i ((e.symm ∘ (Subtype.val : target → _)) z) := rfl

@[simp]
public theorem openGluingPieceSmoothOpenEmbedding_target
    (hcompat : OpenGluingSmoothCompatibility D I ∞) (i : D.J) :
    letI : ChartedSpace H D.toGlueData.glued := openGluingChartedSpace D
    (openGluingPieceSmoothOpenEmbedding D I hcompat i).target = openGluingPieceTarget D i := by
  letI : ChartedSpace H D.toGlueData.glued := openGluingChartedSpace D
  rfl

@[simp]
public theorem openGluingPieceSmoothOpenEmbedding_apply
    (hcompat : OpenGluingSmoothCompatibility D I ∞) (i : D.J) (x : D.U i) :
    letI : ChartedSpace H D.toGlueData.glued := openGluingChartedSpace D
    openGluingPieceSmoothOpenEmbedding D I hcompat i x = D.toGlueData.ι i x := by
  letI : ChartedSpace H D.toGlueData.glued := openGluingChartedSpace D
  change (((D.ι_isOpenEmbedding i).isEmbedding.toHomeomorph x :
    openGluingPieceTarget D i) : D.toGlueData.glued) = D.toGlueData.ι i x
  rfl

end Smooth

namespace SmoothOpenEmbedding

universe uE uH uM uN uP

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type uH} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H}
  {M : Type uM} {N : Type uN} {P : Type uP}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace H N]
  [TopologicalSpace P] [ChartedSpace H P]

/-- The image of the first embedding's open target under the second embedding. -/
public def compTarget (f : SmoothOpenEmbedding I N P) (e : SmoothOpenEmbedding I M N) : Opens P
    where
  carrier := f '' (e.target : Set N)
  is_open' := f.isOpenEmbedding.isOpenMap _ e.target.isOpen

@[simp]
public theorem mem_compTarget (f : SmoothOpenEmbedding I N P)
    (e : SmoothOpenEmbedding I M N) (z : P) :
    z ∈ compTarget f e ↔ ∃ y ∈ e.target, f y = z :=
  Iff.rfl

/-- Regard a point of the composite target as a point of the second embedding's target. -/
public def compTargetLift (f : SmoothOpenEmbedding I N P)
    (e : SmoothOpenEmbedding I M N) (z : compTarget f e) : f.target := by
  refine ⟨z.1, ?_⟩
  obtain ⟨y, _, hfy⟩ := z.2
  rw [← hfy]
  exact (f.toDiffeomorph y).2

/-- Pull a point of the composite target back to the first embedding's target. -/
public def compTargetPreimage (f : SmoothOpenEmbedding I N P)
    (e : SmoothOpenEmbedding I M N) (z : compTarget f e) : e.target := by
  refine ⟨f.toDiffeomorph.symm (compTargetLift f e z), ?_⟩
  obtain ⟨y, hy, hfy⟩ := z.2
  have hlift : compTargetLift f e z = f.toDiffeomorph y := by
    apply Subtype.ext
    exact hfy.symm
  rw [hlift, f.toDiffeomorph.symm_apply_apply]
  exact hy

public theorem compTargetPreimage_map (f : SmoothOpenEmbedding I N P)
    (e : SmoothOpenEmbedding I M N) (z : compTarget f e) :
    f (compTargetPreimage f e z).1 = z.1 := by
  change (f.toDiffeomorph (f.toDiffeomorph.symm (compTargetLift f e z)) : P) = z.1
  exact congrArg Subtype.val (f.toDiffeomorph.apply_symm_apply (compTargetLift f e z))

public theorem contMDiff_compTargetLift (f : SmoothOpenEmbedding I N P)
    (e : SmoothOpenEmbedding I M N) : ContMDiff I I ∞ (compTargetLift f e) := by
  apply (ContMDiff.subtypeVal_comp_iff f.target _).mp
  change ContMDiff I I ∞ (Subtype.val : compTarget f e → P)
  exact contMDiff_subtype_val (I := I)

/-- The restriction of the second embedding to the first embedding's open target is a
diffeomorphism onto the composite target. -/
public def compTargetDiffeomorph (f : SmoothOpenEmbedding I N P)
    (e : SmoothOpenEmbedding I M N) : e.target ≃ₘ⟮I, I⟯ compTarget f e where
  toEquiv :=
    { toFun := fun y ↦ ⟨f y.1, ⟨y.1, y.2, rfl⟩⟩
      invFun := compTargetPreimage f e
      left_inv := by
        intro y
        apply Subtype.ext
        apply f.isOpenEmbedding.isEmbedding.injective
        exact compTargetPreimage_map f e ⟨f y.1, ⟨y.1, y.2, rfl⟩⟩
      right_inv := by
        intro z
        apply Subtype.ext
        exact compTargetPreimage_map f e z }
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff (compTarget f e) _).mp
    change ContMDiff I I ∞ (f ∘ (Subtype.val : e.target → N))
    exact f.contMDiff.comp (contMDiff_subtype_val (I := I))
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff e.target _).mp
    change ContMDiff I I ∞ (f.toDiffeomorph.symm ∘ compTargetLift f e)
    exact f.toDiffeomorph.contMDiff_invFun.comp (contMDiff_compTargetLift f e)

/-- Composition of smooth open embeddings.  As for ordinary function composition, `f.comp e`
means first apply `e`, then apply `f`. -/
public def comp (f : SmoothOpenEmbedding I N P) (e : SmoothOpenEmbedding I M N) :
    SmoothOpenEmbedding I M P where
  target := compTarget f e
  toDiffeomorph := e.toDiffeomorph.trans (compTargetDiffeomorph f e)

@[simp]
public theorem comp_target (f : SmoothOpenEmbedding I N P) (e : SmoothOpenEmbedding I M N) :
    (f.comp e).target = compTarget f e :=
  rfl

@[simp]
public theorem comp_apply (f : SmoothOpenEmbedding I N P) (e : SmoothOpenEmbedding I M N)
    (x : M) : f.comp e x = f (e x) := by
  change ((compTargetDiffeomorph f e) (e.toDiffeomorph x) : P) = f (e x)
  rfl

end SmoothOpenEmbedding


end SphereSixComplex
