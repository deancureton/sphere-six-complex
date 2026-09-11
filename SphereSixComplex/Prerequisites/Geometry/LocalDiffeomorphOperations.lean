module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
import all Mathlib.Geometry.Manifold.LocalDiffeomorph

open scoped ContDiff Manifold

namespace SphereSixComplex.Geometry

open Set Topology

noncomputable section

universe u v w

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type w} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M N P : Type*} [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P]
variable [ChartedSpace H M] [ChartedSpace H N] [ChartedSpace H P]
variable {n : WithTop ℕ∞}

/-- A local diffeomorphism can be cancelled on the right through a surjective local
diffeomorphism. -/
private theorem isLocalDiffeomorph_of_comp_surjective
    {p : M → N} {f : N → P}
    (hp : IsLocalDiffeomorph I I n p) (hsurj : Function.Surjective p)
    (hcomp : IsLocalDiffeomorph I I n (f ∘ p)) :
    IsLocalDiffeomorph I I n f := by
  intro y
  obtain ⟨x, rfl⟩ := hsurj y
  let L := (hp x).localInverse
  let K := (hcomp x).localInverse
  refine ⟨L.trans K.symm, ?_, ?_⟩
  · constructor
    · exact (hp x).localInverse_mem_source
    · change L (p x) ∈ K.target
      rw [(hp x).localInverse_left_inv (hp x).localInverse_mem_target]
      exact (hcomp x).localInverse_mem_target
  · intro y hy
    change y ∈ L.source ∧ L y ∈ K.symm.source at hy
    change f y = K.symm (L y)
    have hz := (hcomp x).localInverse_right_inv (K.symm.map_source hy.2)
    change (f ∘ p) (K (K.symm (L y))) = K.symm (L y) at hz
    calc
      f y = f (p (L y)) := congrArg f ((hp x).localInverse_right_inv hy.1).symm
      _ = (f ∘ p) (K (K.symm (L y))) :=
        congrArg (f ∘ p) (K.right_inv hy.2).symm
      _ = K.symm (L y) := hz

private noncomputable def opensInclusionPartialDiffeomorph
    {X : Type*} [TopologicalSpace X] [ChartedSpace H X]
    {U V : TopologicalSpace.Opens X} (h : U ≤ V) [Nonempty U] :
    PartialDiffeomorph I I U V ∞ := by
  let f : U → V := TopologicalSpace.Opens.inclusion h
  let hopen : IsOpenEmbedding f := Topology.IsOpenEmbedding.inclusion h
    (U.2.preimage continuous_subtype_val)
  exact {
    toPartialEquiv := (hopen.toOpenPartialHomeomorph f).toPartialEquiv
    open_source := isOpen_univ
    open_target := by
      rw [hopen.toOpenPartialHomeomorph_target]
      exact hopen.isOpen_range
    contMDiffOn_toFun := (contMDiff_inclusion h).contMDiffOn
    contMDiffOn_invFun := by
      intro y hy
      apply (ContMDiffWithinAt.subtypeVal_comp_iff U _ _ y).mp
      apply contMDiff_subtype_val.contMDiffAt.contMDiffWithinAt.congr
      · intro z hz
        change ((hopen.toOpenPartialHomeomorph f).symm z : X) = z
        exact congrArg Subtype.val
          (IsOpenEmbedding.toOpenPartialHomeomorph_right_inv f hopen
            (by rwa [hopen.toOpenPartialHomeomorph_target] at hz))
      · change ((hopen.toOpenPartialHomeomorph f).symm y : X) = y
        exact congrArg Subtype.val
          (IsOpenEmbedding.toOpenPartialHomeomorph_right_inv f hopen
            (by rwa [hopen.toOpenPartialHomeomorph_target] at hy))
  }

private theorem opensInclusion_isLocalDiffeomorph
    {X : Type*} [TopologicalSpace X] [ChartedSpace H X]
    {U V : TopologicalSpace.Opens X} (h : U ≤ V) :
    IsLocalDiffeomorph I I ∞ (TopologicalSpace.Opens.inclusion h) := by
  intro x
  let _ : Nonempty U := ⟨x⟩
  exact (opensInclusionPartialDiffeomorph (I := I) h).isLocalDiffeomorphAt
    I I ∞ (by simp [opensInclusionPartialDiffeomorph])

private noncomputable def openSubtypeValPartialDiffeomorph
    {X : Type*} [TopologicalSpace X] [ChartedSpace H X]
    (U : TopologicalSpace.Opens X) [Nonempty U] :
    PartialDiffeomorph I I U X ∞ := by
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

private theorem openSubtypeVal_isLocalDiffeomorph
    {X : Type*} [TopologicalSpace X] [ChartedSpace H X]
    (U : TopologicalSpace.Opens X) :
    IsLocalDiffeomorph I I ∞ (Subtype.val : U → X) := by
  intro x
  let _ : Nonempty U := ⟨x⟩
  exact (openSubtypeValPartialDiffeomorph (I := I) U).isLocalDiffeomorphAt
    I I ∞ (by simp [openSubtypeValPartialDiffeomorph])

private def partialDiffeomorphProd
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
    {M' N' : Type*} [TopologicalSpace M'] [TopologicalSpace N']
    [ChartedSpace H' M'] [ChartedSpace H' N']
    (Phi : PartialDiffeomorph I I M N n)
    (Psi : PartialDiffeomorph I' I' M' N' n) :
    PartialDiffeomorph (I.prod I') (I.prod I') (M × M') (N × N') n where
  toPartialEquiv := Phi.toPartialEquiv.prod Psi.toPartialEquiv
  open_source := Phi.open_source.prod Psi.open_source
  open_target := Phi.open_target.prod Psi.open_target
  contMDiffOn_toFun := Phi.contMDiffOn_toFun.prodMap Psi.contMDiffOn_toFun
  contMDiffOn_invFun := Phi.contMDiffOn_invFun.prodMap Psi.contMDiffOn_invFun

private theorem isLocalDiffeomorph_prodMap
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
    {M' N' : Type*} [TopologicalSpace M'] [TopologicalSpace N']
    [ChartedSpace H' M'] [ChartedSpace H' N']
    {f : M → N} {g : M' → N'}
    (hf : IsLocalDiffeomorph I I n f) (hg : IsLocalDiffeomorph I' I' n g) :
    IsLocalDiffeomorph (I.prod I') (I.prod I') n (Prod.map f g) := by
  intro x
  obtain ⟨Phi, hx, hPhi⟩ := hf x.1
  obtain ⟨Psi, hy, hPsi⟩ := hg x.2
  refine ⟨partialDiffeomorphProd Phi Psi, ⟨hx, hy⟩, ?_⟩
  intro y hy
  exact Prod.ext (hPhi hy.1) (hPsi hy.2)

private theorem isLocalDiffeomorph_of_comp_left
    {f : M → N} {g : N → P}
    (hg : IsLocalDiffeomorph I I n g) (hginj : Function.Injective g)
    (hcomp : IsLocalDiffeomorph I I n (g ∘ f)) :
    IsLocalDiffeomorph I I n f := by
  intro x
  obtain ⟨Phi, hx, hPhi⟩ := hcomp x
  let L := (hg (f x)).localInverse
  refine ⟨Phi.trans L, ?_, ?_⟩
  · change x ∈ Phi.source ∧ Phi x ∈ L.source
    refine ⟨hx, ?_⟩
    rw [← hPhi hx]
    exact (hg (f x)).localInverse_mem_source
  · intro y hy
    change y ∈ Phi.source ∧ Phi y ∈ L.source at hy
    change f y = L (Phi y)
    apply hginj
    rw [(hg (f x)).localInverse_right_inv hy.2]
    exact hPhi hy.1

@[expose] public section

/-- An injective local diffeomorphism, viewed on its open range, is a partial
diffeomorphism. -/
public noncomputable def partialDiffeomorphOfOpenEmbedding
    {f : M → N} [Nonempty M]
    (hopen : IsOpenEmbedding f) (hlocal : IsLocalDiffeomorph I I n f) :
    PartialDiffeomorph I I M N n where
  toPartialEquiv := (hopen.toOpenPartialHomeomorph f).toPartialEquiv
  open_source := isOpen_univ
  open_target := by
    rw [hopen.toOpenPartialHomeomorph_target]
    exact hopen.isOpen_range
  contMDiffOn_toFun := hlocal.contMDiff.contMDiffOn
  contMDiffOn_invFun := by
    intro y hy
    rw [hopen.toOpenPartialHomeomorph_target] at hy
    obtain ⟨x, rfl⟩ := hy
    let L := (hlocal x).localInverse
    have hevent : (hopen.toOpenPartialHomeomorph f).symm =ᶠ[nhds (f x)] L := by
      filter_upwards [L.open_source.mem_nhds
        (hlocal x).localInverse_mem_source] with y hy
      apply hopen.injective
      calc
        f ((hopen.toOpenPartialHomeomorph f).symm y) = y :=
          IsOpenEmbedding.toOpenPartialHomeomorph_right_inv f hopen
            ⟨L y, (hlocal x).localInverse_right_inv hy⟩
        _ = f (L y) := ((hlocal x).localInverse_right_inv hy).symm
    exact (hlocal x).localInverse_contMDiffAt.congr_of_eventuallyEq hevent
      |>.contMDiffWithinAt


@[simp]
public theorem partialDiffeomorphOfOpenEmbedding_source
    {f : M → N} [Nonempty M]
    (hopen : IsOpenEmbedding f) (hlocal : IsLocalDiffeomorph I I n f) :
    (partialDiffeomorphOfOpenEmbedding hopen hlocal).source = univ :=
  rfl

@[simp]
public theorem partialDiffeomorphOfOpenEmbedding_target
    {f : M → N} [Nonempty M]
    (hopen : IsOpenEmbedding f) (hlocal : IsLocalDiffeomorph I I n f) :
    (partialDiffeomorphOfOpenEmbedding hopen hlocal).target = range f := by
  exact hopen.toOpenPartialHomeomorph_target


/-- Two analytic open embeddings of the same nonempty manifold determine the ambient
partial diffeomorphism between their ranges. -/
public noncomputable def partialDiffeomorphBetweenOpenEmbeddings
    {f : M → N} {g : M → P} [Nonempty M]
    (hfopen : IsOpenEmbedding f) (hflocal : IsLocalDiffeomorph I I n f)
    (hgopen : IsOpenEmbedding g) (hglocal : IsLocalDiffeomorph I I n g) :
    PartialDiffeomorph I I N P n :=
  (partialDiffeomorphOfOpenEmbedding hfopen hflocal).symm.trans
    (partialDiffeomorphOfOpenEmbedding hgopen hglocal)

@[simp]
public theorem partialDiffeomorphBetweenOpenEmbeddings_source
    {f : M → N} {g : M → P} [Nonempty M]
    (hfopen : IsOpenEmbedding f) (hflocal : IsLocalDiffeomorph I I n f)
    (hgopen : IsOpenEmbedding g) (hglocal : IsLocalDiffeomorph I I n g) :
    (partialDiffeomorphBetweenOpenEmbeddings hfopen hflocal hgopen hglocal).source =
      range f := by
  simp [partialDiffeomorphBetweenOpenEmbeddings]

@[simp]
public theorem partialDiffeomorphBetweenOpenEmbeddings_target
    {f : M → N} {g : M → P} [Nonempty M]
    (hfopen : IsOpenEmbedding f) (hflocal : IsLocalDiffeomorph I I n f)
    (hgopen : IsOpenEmbedding g) (hglocal : IsLocalDiffeomorph I I n g) :
    (partialDiffeomorphBetweenOpenEmbeddings hfopen hflocal hgopen hglocal).target =
      range g := by
  simp [partialDiffeomorphBetweenOpenEmbeddings]

@[simp]
public theorem partialDiffeomorphBetweenOpenEmbeddings_apply
    {f : M → N} {g : M → P} [Nonempty M]
    (hfopen : IsOpenEmbedding f) (hflocal : IsLocalDiffeomorph I I n f)
    (hgopen : IsOpenEmbedding g) (hglocal : IsLocalDiffeomorph I I n g) (x : M) :
    partialDiffeomorphBetweenOpenEmbeddings hfopen hflocal hgopen hglocal (f x) =
      g x := by
  change g ((partialDiffeomorphOfOpenEmbedding hfopen hflocal).symm (f x)) = g x
  congr 1
  exact (partialDiffeomorphOfOpenEmbedding hfopen hflocal).left_inv trivial

end

end

end SphereSixComplex.Geometry
