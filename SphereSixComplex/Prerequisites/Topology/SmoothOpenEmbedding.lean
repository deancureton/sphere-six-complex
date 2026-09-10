module

public import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Smooth open embeddings

A smooth open embedding is packaged by an explicit open subset of the target and a
diffeomorphism onto that subset.  This form retains both the image and its smooth inverse, which
is useful when the embedding is later used as gluing data.

This packaging is inspired by the sphere-eversion `OpenSmoothEmbedding` design; the implementation
is local and depends only on Mathlib.
-/

@[expose] public section

noncomputable section

open Filter Function Set TopologicalSpace
open scoped ContDiff Manifold Topology

namespace SphereSixComplex

universe uE uH uM uN

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type uH} [TopologicalSpace H]

/-- A smooth open embedding of `M` into `N`, for manifolds over the same model with corners.

The range is retained as the open set `target`, while `toDiffeomorph` identifies the source with
that open submanifold. -/
public structure SmoothOpenEmbedding (I : ModelWithCorners 𝕜 E H)
    (M : Type uM) (N : Type uN) [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace N] [ChartedSpace H N] where
  /-- The open range of the embedding. -/
  target : Opens N
  /-- The source is smoothly diffeomorphic to the open range. -/
  toDiffeomorph : M ≃ₘ⟮I, I⟯ target

namespace SmoothOpenEmbedding

variable {I : ModelWithCorners 𝕜 E H}
  {M : Type uM} {N : Type uN} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace H N]

/-- The ambient-space map underlying a smooth open embedding. -/
public def toFun (e : SmoothOpenEmbedding I M N) : M → N :=
  fun x ↦ e.toDiffeomorph x

public instance : CoeFun (SmoothOpenEmbedding I M N) fun _ ↦ M → N :=
  ⟨toFun⟩

@[simp]
public theorem toFun_apply (e : SmoothOpenEmbedding I M N) (x : M) :
    e.toFun x = (e.toDiffeomorph x : N) :=
  rfl

@[simp]
public theorem coe_apply (e : SmoothOpenEmbedding I M N) (x : M) :
    e x = (e.toDiffeomorph x : N) :=
  rfl

/-- The ambient map of a smooth open embedding is infinitely differentiable. -/
public theorem contMDiff (e : SmoothOpenEmbedding I M N) : ContMDiff I I ∞ e := by
  change ContMDiff I I ∞ (fun x ↦ (e.toDiffeomorph x : N))
  simpa only [Function.comp_def] using
    (contMDiff_subtype_val (I := I) (U := e.target)).comp e.toDiffeomorph.contMDiff

/-- The ambient map is an open topological embedding. -/
public theorem isOpenEmbedding (e : SmoothOpenEmbedding I M N) :
    Topology.IsOpenEmbedding e := by
  change Topology.IsOpenEmbedding (fun x ↦ (e.toDiffeomorph x : N))
  simpa only [Function.comp_def, Diffeomorph.coe_toHomeomorph] using
    e.target.isOpenEmbedding'.comp e.toDiffeomorph.toHomeomorph.isOpenEmbedding

/-- The identity map, presented as a smooth open embedding with universal target. -/
public def refl (I : ModelWithCorners 𝕜 E H) (M : Type uM)
    [TopologicalSpace M] [ChartedSpace H M] : SmoothOpenEmbedding I M M where
  target := ⊤
  toDiffeomorph :=
    { toEquiv :=
        { toFun := fun x ↦ ⟨x, trivial⟩
          invFun := Subtype.val
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl }
      contMDiff_toFun := by
        apply (ContMDiff.subtypeVal_comp_iff (⊤ : Opens M) _).mp
        exact contMDiff_id
      contMDiff_invFun := contMDiff_subtype_val (I := I) }

@[simp]
public theorem refl_target (I : ModelWithCorners 𝕜 E H) (M : Type uM)
    [TopologicalSpace M] [ChartedSpace H M] : (refl I M).target = ⊤ :=
  rfl

@[simp]
public theorem refl_apply (I : ModelWithCorners 𝕜 E H) (M : Type uM)
    [TopologicalSpace M] [ChartedSpace H M] (x : M) : refl I M x = x :=
  rfl

universe uM' uN'

variable {M' : Type uM'} {N' : Type uN'}
  [TopologicalSpace M'] [ChartedSpace H M']
  [TopologicalSpace N'] [ChartedSpace H N']

/-- The disjoint union of two open subsets, regarded as an open subset of a disjoint union. -/
public def sumTarget (e : SmoothOpenEmbedding I M N) (e' : SmoothOpenEmbedding I M' N') :
    Opens (N ⊕ N') where
  carrier := Sum.inl '' (e.target : Set N) ∪ Sum.inr '' (e'.target : Set N')
  is_open' :=
    (isOpenMap_inl (e.target : Set N) e.target.isOpen).union
      (isOpenMap_inr (e'.target : Set N') e'.target.isOpen)

@[simp]
public theorem mem_sumTarget_inl (e : SmoothOpenEmbedding I M N)
    (e' : SmoothOpenEmbedding I M' N') (x : N) :
    Sum.inl x ∈ sumTarget e e' ↔ x ∈ e.target := by
  simp [sumTarget]

@[simp]
public theorem mem_sumTarget_inr (e : SmoothOpenEmbedding I M N)
    (e' : SmoothOpenEmbedding I M' N') (x : N') :
    Sum.inr x ∈ sumTarget e e' ↔ x ∈ e'.target := by
  simp [sumTarget]

/-- The disjoint union of two smooth open embeddings. -/
public def sum (e : SmoothOpenEmbedding I M N) (e' : SmoothOpenEmbedding I M' N') :
    SmoothOpenEmbedding I (M ⊕ M') (N ⊕ N') where
  target := sumTarget e e'
  toDiffeomorph :=
    { toEquiv :=
        { toFun := fun x ↦
            match x with
            | Sum.inl m => ⟨Sum.inl (e m), by simp⟩
            | Sum.inr m => ⟨Sum.inr (e' m), by simp⟩
          invFun := fun z ↦
            match z with
            | ⟨Sum.inl x, hx⟩ =>
                Sum.inl (e.toDiffeomorph.symm ⟨x, by simpa using hx⟩)
            | ⟨Sum.inr x, hx⟩ =>
                Sum.inr (e'.toDiffeomorph.symm ⟨x, by simpa using hx⟩)
          left_inv := by
            rintro (m | m) <;> simp
          right_inv := by
            rintro ⟨x | x, hx⟩ <;> apply Subtype.ext <;> simp }
      contMDiff_toFun := by
        apply (ContMDiff.subtypeVal_comp_iff (sumTarget e e') _).mp
        apply (e.contMDiff.sumMap e'.contMDiff).congr
        rintro (m | m) <;> rfl
      contMDiff_invFun := by
        rintro ⟨x | x, hx⟩
        · have hxe : x ∈ e.target := by simpa using hx
          let left : sumTarget e e' → e.target := fun z ↦
            match z with
            | ⟨Sum.inl y, hy⟩ => ⟨y, by simpa using hy⟩
            | ⟨Sum.inr _, _⟩ => ⟨x, hxe⟩
          have hleft : ContMDiff I I ∞ left := by
            apply (ContMDiff.subtypeVal_comp_iff e.target left).mp
            have hbase : ContMDiff I I ∞ (Sum.elim id (fun _ : N' ↦ x)) :=
              contMDiff_id.sumElim contMDiff_const
            apply (hbase.comp (contMDiff_subtype_val (I := I) (U := sumTarget e e'))).congr
            rintro ⟨y | y, hy⟩ <;> rfl
          have hlocal : ContMDiff I I ∞
              (fun z ↦ (Sum.inl (e.toDiffeomorph.symm (left z)) : M ⊕ M')) :=
            ContMDiff.inl.comp (e.toDiffeomorph.contMDiff_invFun.comp hleft)
          apply hlocal.contMDiffAt.congr_of_eventuallyEq
          filter_upwards [
            (isOpen_range_inl.preimage continuous_subtype_val).mem_nhds
              (show (Sum.inl x : N ⊕ N') ∈ Set.range (@Sum.inl N N') from ⟨x, rfl⟩)] with z hz
          rcases z with ⟨y | y, hy⟩
          · rfl
          · simp at hz
        · have hxe : x ∈ e'.target := by simpa using hx
          let right : sumTarget e e' → e'.target := fun z ↦
            match z with
            | ⟨Sum.inl _, _⟩ => ⟨x, hxe⟩
            | ⟨Sum.inr y, hy⟩ => ⟨y, by simpa using hy⟩
          have hright : ContMDiff I I ∞ right := by
            apply (ContMDiff.subtypeVal_comp_iff e'.target right).mp
            have hbase : ContMDiff I I ∞ (Sum.elim (fun _ : N ↦ x) id) :=
              contMDiff_const.sumElim contMDiff_id
            apply (hbase.comp (contMDiff_subtype_val (I := I) (U := sumTarget e e'))).congr
            rintro ⟨y | y, hy⟩ <;> rfl
          have hlocal : ContMDiff I I ∞
              (fun z ↦ (Sum.inr (e'.toDiffeomorph.symm (right z)) : M ⊕ M')) :=
            ContMDiff.inr.comp (e'.toDiffeomorph.contMDiff_invFun.comp hright)
          apply hlocal.contMDiffAt.congr_of_eventuallyEq
          filter_upwards [
            (isOpen_range_inr.preimage continuous_subtype_val).mem_nhds
              (show (Sum.inr x : N ⊕ N') ∈ Set.range (@Sum.inr N N') from ⟨x, rfl⟩)] with z hz
          rcases z with ⟨y | y, hy⟩
          · simp at hz
          · rfl }

@[simp]
public theorem sum_target (e : SmoothOpenEmbedding I M N)
    (e' : SmoothOpenEmbedding I M' N') : (e.sum e').target = sumTarget e e' :=
  rfl

@[simp]
public theorem sum_apply_inl (e : SmoothOpenEmbedding I M N)
    (e' : SmoothOpenEmbedding I M' N') (m : M) :
    e.sum e' (Sum.inl m) = Sum.inl (e m) :=
  rfl

@[simp]
public theorem sum_apply_inr (e : SmoothOpenEmbedding I M N)
    (e' : SmoothOpenEmbedding I M' N') (m : M') :
    e.sum e' (Sum.inr m) = Sum.inr (e' m) :=
  rfl

end SmoothOpenEmbedding

namespace Diffeomorph

universe uF uG uM' uP

variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type uG} [TopologicalSpace G]

/-- Smooth right-distributivity of products over disjoint unions. -/
public def sumProdDistrib (I : ModelWithCorners 𝕜 E H) (J : ModelWithCorners 𝕜 F G)
    (M : Type uM) (M' : Type uM') (N : Type uP)
    [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace M'] [ChartedSpace H M']
    [TopologicalSpace N] [ChartedSpace G N] (n : WithTop ℕ∞) :
    ((M ⊕ M') × N) ≃ₘ^n⟮I.prod J, I.prod J⟯ (M × N) ⊕ (M' × N) where
  toEquiv := Equiv.sumProdDistrib M M' N
  contMDiff_toFun := by
    rintro ⟨m | m', y⟩
    · let left : M ⊕ M' → M := Sum.elim id (fun _ ↦ m)
      let localMap : (M ⊕ M') × N → (M × N) ⊕ (M' × N) :=
        fun p ↦ Sum.inl (left p.1, p.2)
      have hleft : ContMDiff I I n left := contMDiff_id.sumElim contMDiff_const
      have hlocal : ContMDiff (I.prod J) (I.prod J) n localMap := by
        exact ContMDiff.inl.comp ((hleft.comp contMDiff_fst).prodMk contMDiff_snd)
      apply hlocal.contMDiffAt.congr_of_eventuallyEq
      filter_upwards [
        (isOpen_range_inl.preimage continuous_fst).mem_nhds ⟨m, rfl⟩] with p hp
      rcases p with ⟨p | p, z⟩
      · rfl
      · simp at hp
    · let right : M ⊕ M' → M' := Sum.elim (fun _ ↦ m') id
      let localMap : (M ⊕ M') × N → (M × N) ⊕ (M' × N) :=
        fun p ↦ Sum.inr (right p.1, p.2)
      have hright : ContMDiff I I n right := contMDiff_const.sumElim contMDiff_id
      have hlocal : ContMDiff (I.prod J) (I.prod J) n localMap := by
        exact ContMDiff.inr.comp ((hright.comp contMDiff_fst).prodMk contMDiff_snd)
      apply hlocal.contMDiffAt.congr_of_eventuallyEq
      filter_upwards [
        (isOpen_range_inr.preimage continuous_fst).mem_nhds ⟨m', rfl⟩] with p hp
      rcases p with ⟨p | p, z⟩
      · simp at hp
      · rfl
  contMDiff_invFun :=
    (ContMDiff.inl.prodMap contMDiff_id).sumElim
      (ContMDiff.inr.prodMap contMDiff_id)

@[simp]
public theorem sumProdDistrib_apply_inl (I : ModelWithCorners 𝕜 E H)
    (J : ModelWithCorners 𝕜 F G) (M : Type uM) (M' : Type uM') (N : Type uP)
    [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace M'] [ChartedSpace H M']
    [TopologicalSpace N] [ChartedSpace G N] (n : WithTop ℕ∞) (m : M) (y : N) :
    sumProdDistrib I J M M' N n (Sum.inl m, y) = Sum.inl (m, y) :=
  rfl

@[simp]
public theorem sumProdDistrib_apply_inr (I : ModelWithCorners 𝕜 E H)
    (J : ModelWithCorners 𝕜 F G) (M : Type uM) (M' : Type uM') (N : Type uP)
    [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace M'] [ChartedSpace H M']
    [TopologicalSpace N] [ChartedSpace G N] (n : WithTop ℕ∞) (m : M') (y : N) :
    sumProdDistrib I J M M' N n (Sum.inr m, y) = Sum.inr (m, y) :=
  rfl

end Diffeomorph

end SphereSixComplex
