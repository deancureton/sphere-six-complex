module

public import SphereSixComplex.Topology.SingularBarycentricChains
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic

/-!
# Barycentric fundamental chains in all degrees

For each permutation of the vertices of the standard `n`-simplex, its successive nonempty
prefixes form a maximal flag in the poset of nonempty subsets.  The signed sum of these flags is
the oriented barycentric fundamental chain.  This file constructs that chain in Mathlib's actual
`SimplexCategory.sd` nerve model and transports it naturally to every simplex of every simplicial
set.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits PartialOrder Simplicial

namespace SphereSixComplex

/-- The set of the first `k+1` vertices in the ordering specified by `σ`. -/
public noncomputable def permutationPrefixFinset {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 1))) (k : Fin (n + 1)) :
    Finset (ULift.{0} (Fin (n + 1))) :=
  (Finset.Iic k).image (fun i ↦ ULift.up (σ i))

/-- Every permutation prefix is nonempty. -/
public theorem permutationPrefixFinset_nonempty {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 1))) (k : Fin (n + 1)) :
    (permutationPrefixFinset σ k).Nonempty := by
  refine ⟨ULift.up (σ k), ?_⟩
  simp [permutationPrefixFinset]

/-- Permutation prefixes are nested. -/
public theorem permutationPrefixFinset_mono {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 1))) :
    Monotone (permutationPrefixFinset σ) := by
  intro i j hij
  apply Finset.image_mono
  intro k hk
  exact Finset.mem_Iic.mpr (le_trans (Finset.mem_Iic.mp hk) hij)

/-- A permutation prefix, regarded as a nonempty finite chain in the linearly ordered vertex
set. -/
public noncomputable def permutationPrefixChain {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 1))) (k : Fin (n + 1)) :
    NonemptyFiniteChains (ULift.{0} (Fin (n + 1))) :=
  nonemptyFiniteChainOfFinset (permutationPrefixFinset σ k)
    (permutationPrefixFinset_nonempty σ k)

/-- The monotone maximal flag of prefix chains associated to a permutation. -/
public noncomputable def permutationMaximalFlagOrderHom {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 1))) :
    Fin (n + 1) →o NonemptyFiniteChains (ULift.{0} (Fin (n + 1))) where
  toFun := permutationPrefixChain σ
  monotone' _ _ hij := permutationPrefixFinset_mono σ hij

/-- The `n`-simplex of the subdivision model corresponding to a maximal permutation flag. -/
public noncomputable def permutationMaximalFlagSimplex {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 1))) :
    (SimplexCategory.sd.{0}.obj (SimplexCategory.mk n)).obj
      (Opposite.op (SimplexCategory.mk n)) :=
  (permutationMaximalFlagOrderHom σ).monotone.functor

/-- The sign of a permutation, as an integer coefficient. -/
public noncomputable def permutationSignInteger {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 1))) : ℤ :=
  Equiv.Perm.sign σ

/-- Swapping two distinct positions reverses the integer orientation coefficient. -/
public theorem permutationSignInteger_mul_swap {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 1))) {i j : Fin (n + 1)} (hij : i ≠ j) :
    permutationSignInteger (σ * Equiv.swap i j) =
      -permutationSignInteger σ := by
  rw [permutationSignInteger, permutationSignInteger, Equiv.Perm.sign_mul,
    Equiv.Perm.sign_swap hij]
  norm_num

/-- A swap preserves an initial segment exactly when its two swapped positions lie on the same
side of the cutoff. -/
public theorem swap_le_iff_of_equiv {n : ℕ} {i j k a : Fin (n + 1)}
    (hk : (i ≤ k ↔ j ≤ k)) :
    Equiv.swap i j a ≤ k ↔ a ≤ k := by
  by_cases hai : a = i
  · subst a
    rw [Equiv.swap_apply_left]
    exact hk.symm
  by_cases haj : a = j
  · subst a
    rw [Equiv.swap_apply_right]
    exact hk
  rw [Equiv.swap_apply_of_ne_of_ne hai haj]

/-- Swapping two positions on the same side of a cutoff leaves the corresponding permutation
prefix unchanged.  This is the combinatorial pairing mechanism for interior boundary faces. -/
public theorem permutationPrefixFinset_mul_swap {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 1))) {i j k : Fin (n + 1)}
    (hk : (i ≤ k ↔ j ≤ k)) :
    permutationPrefixFinset (σ * Equiv.swap i j) k =
      permutationPrefixFinset σ k := by
  unfold permutationPrefixFinset
  change (Finset.Iic k).image
      (fun a ↦ ULift.up (σ (Equiv.swap i j a))) =
    (Finset.Iic k).image (fun a ↦ ULift.up (σ a))
  have hs : (Finset.Iic k).image (Equiv.swap i j) = Finset.Iic k := by
    ext a
    simp only [Finset.mem_image, Finset.mem_Iic]
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact (swap_le_iff_of_equiv hk).2 hb
    · intro ha
      refine ⟨Equiv.swap i j a, (swap_le_iff_of_equiv hk).2 ha, ?_⟩
      simp
  calc
    _ = ((Finset.Iic k).image (Equiv.swap i j)).image
        (fun a ↦ ULift.up (σ a)) := by
      rw [Finset.image_image]
      rfl
    _ = _ := by rw [hs]

/-- Deleting the prefix at position `r` makes the two maximal flags obtained by swapping the
adjacent positions `r` and `r+1` identical.  These are precisely the paired interior faces in the
fundamental-chain boundary. -/
public theorem permutationMaximalFlagSimplex_interiorFace_swap {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 2))) (r : Fin (n + 1)) :
    (SimplexCategory.sd.{0}.obj (SimplexCategory.mk (n + 1))).δ r.castSucc
        (permutationMaximalFlagSimplex
          (σ * Equiv.swap r.castSucc r.succ)) =
      (SimplexCategory.sd.{0}.obj (SimplexCategory.mk (n + 1))).δ r.castSucc
        (permutationMaximalFlagSimplex σ) := by
  refine ComposableArrows.ext (fun k ↦ ?_) (fun k hk ↦ ?_)
  ·
    change permutationPrefixChain (σ * Equiv.swap r.castSucc r.succ)
        (r.castSucc.succAbove k) =
      permutationPrefixChain σ (r.castSucc.succAbove k)
    apply NonemptyFiniteChains.ext
    apply permutationPrefixFinset_mul_swap
    have ht : r.castSucc.succAbove k ≠ r.castSucc := Fin.succAbove_ne _ _
    constructor
    · intro h
      have htval : (r.castSucc.succAbove k).val ≠ r.val := by
        intro heq
        apply ht
        exact Fin.ext heq
      change r.val + 1 ≤ (r.castSucc.succAbove k).val
      change r.val ≤ (r.castSucc.succAbove k).val at h
      omega
    · intro h
      exact le_trans r.castSucc_le_succ h
  · apply Subsingleton.elim

/-- The oriented barycentric fundamental `n`-chain in the explicit subdivision model of
`Δ[n]`. -/
public noncomputable def subdividedSimplexFundamentalChain (n : ℕ) :
    AddCommGrpCat.of ℤ ⟶
      ((SimplexCategory.sd.{0}.obj (SimplexCategory.mk n)).chainComplex
        (AddCommGrpCat.of ℤ)).X n :=
  ∑ σ : Equiv.Perm (Fin (n + 1)),
    permutationSignInteger σ •
      (SimplexCategory.sd.{0}.obj (SimplexCategory.mk n)).ιChainComplex
        (permutationMaximalFlagSimplex σ)

/-- The all-degree fundamental chain transported to Mathlib's left-Kan-extension model
`sd Δ[n]`. -/
public noncomputable def subdividedStandardSimplexFundamentalChain (n : ℕ) :
    AddCommGrpCat.of ℤ ⟶
      ((SSet.sd.obj (Δ[n] : SSet.{0})).chainComplex
        (AddCommGrpCat.of ℤ)).X n :=
  subdividedSimplexFundamentalChain n ≫
    (SSet.chainComplexMap (SSet.stdSimplex.sdIso.inv.app (SimplexCategory.mk n))
      (AddCommGrpCat.of ℤ)).f n

/-- The barycentric fundamental chain associated to an arbitrary `n`-simplex. -/
public noncomputable def barycentricSubdivisionSimplexChain
    (X : SSet.{0}) (n : ℕ)
    (x : X.obj (Opposite.op (SimplexCategory.mk n))) :
    AddCommGrpCat.of ℤ ⟶
      ((SSet.sd.obj X).chainComplex (AddCommGrpCat.of ℤ)).X n :=
  subdividedStandardSimplexFundamentalChain n ≫
    (SSet.chainComplexMap (SSet.sd.map (SSet.yonedaEquiv.symm x))
      (AddCommGrpCat.of ℤ)).f n

/-- The degree-`n` component of barycentric subdivision, defined on every simplex by its signed
maximal-flag fundamental chain. -/
public noncomputable def barycentricSubdivisionComponent
    (X : SSet.{0}) (n : ℕ) :
    (X.chainComplex (AddCommGrpCat.of ℤ)).X n ⟶
      ((SSet.sd.obj X).chainComplex (AddCommGrpCat.of ℤ)).X n :=
  Sigma.desc (barycentricSubdivisionSimplexChain X n)

@[reassoc (attr := simp)]
public theorem iota_barycentricSubdivisionComponent
    (X : SSet.{0}) (n : ℕ)
    (x : X.obj (Opposite.op (SimplexCategory.mk n))) :
    X.ιChainComplex x ≫ barycentricSubdivisionComponent X n =
      barycentricSubdivisionSimplexChain X n x := by
  apply Sigma.ι_desc

/-- The signed maximal-flag chain associated to a simplex is natural in the ambient simplicial
set. -/
public theorem barycentricSubdivisionSimplexChain_naturality
    {X Y : SSet.{0}} (f : X ⟶ Y) (n : ℕ)
    (x : X.obj (Opposite.op (SimplexCategory.mk n))) :
    barycentricSubdivisionSimplexChain Y n (f.app _ x) =
      barycentricSubdivisionSimplexChain X n x ≫
        (SSet.chainComplexMap (SSet.sd.map f) (AddCommGrpCat.of ℤ)).f n := by
  rw [barycentricSubdivisionSimplexChain, barycentricSubdivisionSimplexChain]
  rw [← SSet.yonedaEquiv_symm_comp]
  let F := (SSet.chainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)
  have hsd := SSet.sd.map_comp (SSet.yonedaEquiv.symm x) f
  have hmap := F.congr_map hsd
  have hn := congrArg (fun k ↦ k.f n) hmap
  rw [hn]
  rw [Functor.map_comp]
  rfl

/-- Every degree of the barycentric subdivision operator is natural. -/
public theorem barycentricSubdivisionComponent_naturality
    {X Y : SSet.{0}} (f : X ⟶ Y) (n : ℕ) :
    (SSet.chainComplexMap f (AddCommGrpCat.of ℤ)).f n ≫
        barycentricSubdivisionComponent Y n =
      barycentricSubdivisionComponent X n ≫
        (SSet.chainComplexMap (SSet.sd.map f) (AddCommGrpCat.of ℤ)).f n := by
  apply X.chainComplex_hom_ext
  intro x
  rw [← Category.assoc, SSet.ι_chainComplexMap_f,
    iota_barycentricSubdivisionComponent]
  rw [← Category.assoc, iota_barycentricSubdivisionComponent,
    barycentricSubdivisionSimplexChain_naturality]

/-- The alternating sum of the subdivided fundamental chains of the codimension-one faces of
the standard `(n+1)`-simplex, in the explicit nerve model. -/
public noncomputable def subdividedSimplexAlternatingFaceChain (n : ℕ) :
    AddCommGrpCat.of ℤ ⟶
      ((SimplexCategory.sd.{0}.obj (SimplexCategory.mk (n + 1))).chainComplex
        (AddCommGrpCat.of ℤ)).X n :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
    (subdividedSimplexFundamentalChain n ≫
      (SSet.chainComplexMap
        (SimplexCategory.sd.{0}.map (SimplexCategory.δ i))
        (AddCommGrpCat.of ℤ)).f n)

/-- The contribution to the boundary in which the prefix at the interior position `r` is
deleted. -/
public noncomputable def subdividedSimplexInteriorFaceSum
    (n : ℕ) (r : Fin (n + 1)) :
    AddCommGrpCat.of ℤ ⟶
      ((SimplexCategory.sd.{0}.obj (SimplexCategory.mk (n + 1))).chainComplex
        (AddCommGrpCat.of ℤ)).X n :=
  ∑ σ : Equiv.Perm (Fin (n + 2)),
    permutationSignInteger σ •
      (SimplexCategory.sd.{0}.obj (SimplexCategory.mk (n + 1))).ιChainComplex
        ((SimplexCategory.sd.{0}.obj (SimplexCategory.mk (n + 1))).δ r.castSucc
          (permutationMaximalFlagSimplex σ))

/-- Every interior face cancels in pairs.  The involution exchanges the two adjacent entries
surrounding the deleted prefix; the flags agree after deletion and their signs are opposite. -/
public theorem subdividedSimplexInteriorFaceSum_eq_zero
    (n : ℕ) (r : Fin (n + 1)) :
    subdividedSimplexInteriorFaceSum n r = 0 := by
  rw [subdividedSimplexInteriorFaceSum]
  exact Finset.sum_involution
    (fun σ _ ↦ σ * Equiv.swap r.castSucc r.succ)
    (fun σ _ ↦ by
      rw [permutationSignInteger_mul_swap σ Fin.castSucc_lt_succ.ne,
        permutationMaximalFlagSimplex_interiorFace_swap]
      simp)
    (fun σ _ _ ↦ (not_congr Equiv.mul_swap_eq_iff).mpr Fin.castSucc_lt_succ.ne)
    (fun _ _ ↦ Finset.mem_univ _)
    (fun σ _ ↦ Equiv.mul_swap_involutive r.castSucc r.succ σ)

/-- The surviving last-prefix faces in the boundary of the signed maximal-flag chain. -/
public noncomputable def subdividedSimplexOuterFaceSum (n : ℕ) :
    AddCommGrpCat.of ℤ ⟶
      ((SimplexCategory.sd.{0}.obj (SimplexCategory.mk (n + 1))).chainComplex
        (AddCommGrpCat.of ℤ)).X n :=
  ∑ σ : Equiv.Perm (Fin (n + 2)),
    permutationSignInteger σ •
      ((-1 : ℤ) ^ (Fin.last (n + 1)).val •
        (SimplexCategory.sd.{0}.obj (SimplexCategory.mk (n + 1))).ιChainComplex
          ((SimplexCategory.sd.{0}.obj (SimplexCategory.mk (n + 1))).δ
            (Fin.last (n + 1)) (permutationMaximalFlagSimplex σ)))

/-- After the certified pairwise cancellations, only the faces obtained by deleting the full
vertex set remain in the boundary of the barycentric fundamental chain. -/
public theorem subdividedSimplexFundamentalChain_boundary_eq_outer
    (n : ℕ) :
    subdividedSimplexFundamentalChain (n + 1) ≫
        ((SimplexCategory.sd.{0}.obj (SimplexCategory.mk (n + 1))).chainComplex
          (AddCommGrpCat.of ℤ)).d (n + 1) n =
      subdividedSimplexOuterFaceSum n := by
  rw [subdividedSimplexFundamentalChain, Preadditive.sum_comp]
  simp only [Preadditive.zsmul_comp, SSet.ιChainComplex_d]
  have hsplit (σ : Equiv.Perm (Fin (n + 2))) :
      (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
          (SimplexCategory.sd.{0}.obj (SimplexCategory.mk (n + 1))).ιChainComplex
            ((SimplexCategory.sd.{0}.obj (SimplexCategory.mk (n + 1))).δ i
              (permutationMaximalFlagSimplex σ)) :
          AddCommGrpCat.of ℤ ⟶
            ((SimplexCategory.sd.{0}.obj (SimplexCategory.mk (n + 1))).chainComplex
              (AddCommGrpCat.of ℤ)).X n) =
        (∑ r : Fin (n + 1), (-1 : ℤ) ^ r.val •
            (SimplexCategory.sd.{0}.obj (SimplexCategory.mk (n + 1))).ιChainComplex
              ((SimplexCategory.sd.{0}.obj (SimplexCategory.mk (n + 1))).δ r.castSucc
                (permutationMaximalFlagSimplex σ))) +
          (-1 : ℤ) ^ (Fin.last (n + 1)).val •
            (SimplexCategory.sd.{0}.obj (SimplexCategory.mk (n + 1))).ιChainComplex
              ((SimplexCategory.sd.{0}.obj (SimplexCategory.mk (n + 1))).δ
                (Fin.last (n + 1)) (permutationMaximalFlagSimplex σ)) := by
    rw [Fin.sum_univ_castSucc]
    rfl
  simp_rw [hsplit, smul_add]
  rw [Finset.sum_add_distrib]
  simp_rw [Finset.smul_sum]
  rw [Finset.sum_comm]
  have hinterior (r : Fin (n + 1)) :
      (∑ σ : Equiv.Perm (Fin (n + 2)),
        permutationSignInteger σ • (-1 : ℤ) ^ r.val •
          (SimplexCategory.sd.{0}.obj (SimplexCategory.mk (n + 1))).ιChainComplex
            ((SimplexCategory.sd.{0}.obj (SimplexCategory.mk (n + 1))).δ r.castSucc
              (permutationMaximalFlagSimplex σ)) :
        AddCommGrpCat.of ℤ ⟶
          ((SimplexCategory.sd.{0}.obj (SimplexCategory.mk (n + 1))).chainComplex
            (AddCommGrpCat.of ℤ)).X n) = 0 := by
    calc
      _ = (-1 : ℤ) ^ r.val • subdividedSimplexInteriorFaceSum n r := by
        rw [subdividedSimplexInteriorFaceSum, Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro σ _
        simp only [smul_smul]
        rw [mul_comm]
      _ = 0 := by rw [subdividedSimplexInteriorFaceSum_eq_zero, smul_zero]
  simp_rw [hinterior]
  simp only [Finset.sum_const_zero, zero_add]
  rfl

/-- Reindex a permutation by first rotating its final position to position zero and then using
Mathlib's standard `decomposeFin` equivalence.  The first coordinate is therefore the vertex
omitted by the surviving outer face. -/
public noncomputable def permutationLastDecomposition (n : ℕ) :
    Equiv.Perm (Fin (n + 2)) ≃
      Fin (n + 2) × Equiv.Perm (Fin (n + 1)) :=
  (Equiv.mulRight (finRotate (n + 2))⁻¹).trans Equiv.Perm.decomposeFin

/-- The distinguished vertex in `permutationLastDecomposition` is the image of the last
position. -/
public theorem permutationLastDecomposition_fst
    (n : ℕ) (σ : Equiv.Perm (Fin (n + 2))) :
    (permutationLastDecomposition n σ).1 = σ (Fin.last (n + 1)) := by
  let θ := σ * (finRotate (n + 2))⁻¹
  have hinv := Equiv.Perm.decomposeFin.symm_apply_apply θ
  have hfirst := congrArg (fun e ↦ e 0) hinv
  rw [Equiv.Perm.decomposeFin_symm_apply_zero] at hfirst
  change (Equiv.Perm.decomposeFin θ).1 = σ (Fin.last (n + 1))
  rw [hfirst]
  change σ ((finRotate (n + 2))⁻¹ 0) = σ (Fin.last (n + 1))
  congr 1

/-- The sole surviving combinatorial assertion: reindexing the outer faces by their omitted
vertex gives the alternating sum of the subdivided codimension-one faces. -/
public def BarycentricOuterFaceIdentity : Prop :=
  ∀ n : ℕ,
    subdividedSimplexOuterFaceSum n =
      subdividedSimplexAlternatingFaceChain n

/-- The exact all-dimensional combinatorial cancellation theorem required of the signed
maximal-flag chains.  Unlike a chain-map or homology-isomorphism assumption, this states the
single explicit boundary calculation on the permutation sums above. -/
public def BarycentricFundamentalBoundaryIdentity : Prop :=
  ∀ n : ℕ,
    subdividedSimplexFundamentalChain (n + 1) ≫
        ((SimplexCategory.sd.{0}.obj (SimplexCategory.mk (n + 1))).chainComplex
          (AddCommGrpCat.of ℤ)).d (n + 1) n =
      subdividedSimplexAlternatingFaceChain n

/-- The full boundary identity is equivalent to the remaining outer-face reindexing identity;
all interior faces have already been cancelled above. -/
public theorem barycentricFundamentalBoundaryIdentity_iff_outerFaceIdentity :
    BarycentricFundamentalBoundaryIdentity ↔ BarycentricOuterFaceIdentity := by
  constructor
  · intro h n
    rw [← subdividedSimplexFundamentalChain_boundary_eq_outer n]
    exact h n
  · intro h n
    rw [subdividedSimplexFundamentalChain_boundary_eq_outer n]
    exact h n

/-- The remaining outer-face reindexing theorem is sufficient to construct the full
barycentric chain map. -/
public theorem barycentricFundamentalBoundaryIdentity_of_outerFaceIdentity
    (h : BarycentricOuterFaceIdentity) :
    BarycentricFundamentalBoundaryIdentity :=
  barycentricFundamentalBoundaryIdentity_iff_outerFaceIdentity.mpr h

/-- Naturality of `stdSimplex.sdIso.inv`, transported to integral chains in a fixed degree. -/
public theorem subdividedStandardSimplexFace_naturality
    (n : ℕ) (i : Fin (n + 2)) :
    (SSet.chainComplexMap
          (SimplexCategory.sd.{0}.map (SimplexCategory.δ i))
          (AddCommGrpCat.of ℤ)).f n ≫
        (SSet.chainComplexMap
          (SSet.stdSimplex.sdIso.inv.app (SimplexCategory.mk (n + 1)))
          (AddCommGrpCat.of ℤ)).f n =
      (SSet.chainComplexMap
          (SSet.stdSimplex.sdIso.inv.app (SimplexCategory.mk n))
          (AddCommGrpCat.of ℤ)).f n ≫
        (SSet.chainComplexMap
          (SSet.sd.map (SSet.stdSimplex.map (SimplexCategory.δ i)))
          (AddCommGrpCat.of ℤ)).f n := by
  let F := (SSet.chainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)
  have hnat := SSet.stdSimplex.sdIso.inv.naturality (SimplexCategory.δ i)
  have hmap := F.congr_map hnat
  rw [Functor.map_comp, Functor.map_comp] at hmap
  exact congrArg (fun k ↦ k.f n) hmap

/-- The alternating face chain after transport to `sd Δ[n+1]`. -/
public noncomputable def subdividedStandardSimplexAlternatingFaceChain (n : ℕ) :
    AddCommGrpCat.of ℤ ⟶
      ((SSet.sd.obj (Δ[n + 1] : SSet.{0})).chainComplex
        (AddCommGrpCat.of ℤ)).X n :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
    (subdividedStandardSimplexFundamentalChain n ≫
      (SSet.chainComplexMap
        (SSet.sd.map (SSet.stdSimplex.map (SimplexCategory.δ i)))
        (AddCommGrpCat.of ℤ)).f n)

/-- The explicit model boundary identity transports to the left-Kan-extension standard
simplices. -/
public theorem subdividedStandardSimplexFundamentalChain_boundary
    (h : BarycentricFundamentalBoundaryIdentity) (n : ℕ) :
    subdividedStandardSimplexFundamentalChain (n + 1) ≫
        ((SSet.sd.obj (Δ[n + 1] : SSet.{0})).chainComplex
          (AddCommGrpCat.of ℤ)).d (n + 1) n =
      subdividedStandardSimplexAlternatingFaceChain n := by
  let F := SSet.chainComplexMap
    (SSet.stdSimplex.sdIso.inv.app (SimplexCategory.mk (n + 1)))
    (AddCommGrpCat.of ℤ)
  change (subdividedSimplexFundamentalChain (n + 1) ≫ F.f (n + 1)) ≫ _ = _
  have hcomm := F.comm (n + 1) n
  have hpre := congrArg
    (fun k ↦ subdividedSimplexFundamentalChain (n + 1) ≫ k) hcomm
  calc
    _ = subdividedSimplexFundamentalChain (n + 1) ≫
        (F.f (n + 1) ≫ _) := Category.assoc _ _ _
    _ = subdividedSimplexFundamentalChain (n + 1) ≫
        (_ ≫ F.f n) := hpre
    _ = (subdividedSimplexFundamentalChain (n + 1) ≫
        ((SimplexCategory.sd.{0}.obj (SimplexCategory.mk (n + 1))).chainComplex
          (AddCommGrpCat.of ℤ)).d (n + 1) n) ≫ F.f n := (Category.assoc _ _ _).symm
    _ = subdividedSimplexAlternatingFaceChain n ≫ F.f n := by rw [h n]
    _ = _ := by
      rw [subdividedSimplexAlternatingFaceChain, Preadditive.sum_comp]
      simp only [Preadditive.zsmul_comp, Category.assoc]
      rw [subdividedStandardSimplexAlternatingFaceChain]
      apply Finset.sum_congr rfl
      intro i hi
      rw [subdividedStandardSimplexFundamentalChain, Category.assoc,
        subdividedStandardSimplexFace_naturality]

/-- Subdividing a face and then mapping its ambient simplex agrees with subdividing the
corresponding face simplex. -/
public theorem subdividedFace_then_simplex_naturality
    {X : SSet.{0}} (n : ℕ)
    (x : X.obj (Opposite.op (SimplexCategory.mk (n + 1))))
    (i : Fin (n + 2)) :
    (SSet.chainComplexMap
          (SSet.sd.map (SSet.stdSimplex.map (SimplexCategory.δ i)))
          (AddCommGrpCat.of ℤ)).f n ≫
        (SSet.chainComplexMap (SSet.sd.map (SSet.yonedaEquiv.symm x))
          (AddCommGrpCat.of ℤ)).f n =
      (SSet.chainComplexMap (SSet.sd.map (SSet.yonedaEquiv.symm (X.δ i x)))
        (AddCommGrpCat.of ℤ)).f n := by
  let F := (SSet.chainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)
  have hδ := SSet.stdSimplex.δ_comp_yonedaEquiv_symm x i
  have hsd := SSet.sd.congr_map hδ
  have hmap := F.congr_map hsd
  rw [SSet.sd.map_comp, Functor.map_comp] at hmap
  exact congrArg (fun k ↦ k.f n) hmap

/-- The alternating sum of the barycentrically subdivided faces of an arbitrary simplex. -/
public noncomputable def barycentricSubdivisionAlternatingFaceChain
    (X : SSet.{0}) (n : ℕ)
    (x : X.obj (Opposite.op (SimplexCategory.mk (n + 1)))) :
    AddCommGrpCat.of ℤ ⟶
      ((SSet.sd.obj X).chainComplex (AddCommGrpCat.of ℤ)).X n :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
    barycentricSubdivisionSimplexChain X n (X.δ i x)

/-- The explicit model cancellation theorem gives the correct boundary for the subdivided chain
of every simplex. -/
public theorem barycentricSubdivisionSimplexChain_boundary
    (h : BarycentricFundamentalBoundaryIdentity)
    (X : SSet.{0}) (n : ℕ)
    (x : X.obj (Opposite.op (SimplexCategory.mk (n + 1)))) :
    barycentricSubdivisionSimplexChain X (n + 1) x ≫
        ((SSet.sd.obj X).chainComplex (AddCommGrpCat.of ℤ)).d (n + 1) n =
      barycentricSubdivisionAlternatingFaceChain X n x := by
  let F := SSet.chainComplexMap (SSet.sd.map (SSet.yonedaEquiv.symm x))
    (AddCommGrpCat.of ℤ)
  change (subdividedStandardSimplexFundamentalChain (n + 1) ≫ F.f (n + 1)) ≫
    _ = _
  have hcomm := F.comm (n + 1) n
  have hpre := congrArg
    (fun k ↦ subdividedStandardSimplexFundamentalChain (n + 1) ≫ k) hcomm
  calc
    _ = subdividedStandardSimplexFundamentalChain (n + 1) ≫
        (F.f (n + 1) ≫ _) := Category.assoc _ _ _
    _ = subdividedStandardSimplexFundamentalChain (n + 1) ≫
        (_ ≫ F.f n) := hpre
    _ = (subdividedStandardSimplexFundamentalChain (n + 1) ≫
        ((SSet.sd.obj (Δ[n + 1] : SSet.{0})).chainComplex
          (AddCommGrpCat.of ℤ)).d (n + 1) n) ≫ F.f n := (Category.assoc _ _ _).symm
    _ = subdividedStandardSimplexAlternatingFaceChain n ≫ F.f n := by
      rw [subdividedStandardSimplexFundamentalChain_boundary h n]
    _ = _ := by
      rw [subdividedStandardSimplexAlternatingFaceChain, Preadditive.sum_comp]
      simp only [Preadditive.zsmul_comp, Category.assoc]
      rw [barycentricSubdivisionAlternatingFaceChain]
      apply Finset.sum_congr rfl
      intro i hi
      rw [barycentricSubdivisionSimplexChain]
      apply congrArg (fun k ↦ ((-1 : ℤ) ^ i.val) • k)
      rw [subdividedFace_then_simplex_naturality]

/-- The precise degreewise chain compatibility needed to assemble the constructed components
into a chain morphism. -/
public def BarycentricSubdivisionComponentsCommute : Prop :=
  ∀ (X : SSet.{0}) (n : ℕ),
    barycentricSubdivisionComponent X (n + 1) ≫
        ((SSet.sd.obj X).chainComplex (AddCommGrpCat.of ℤ)).d (n + 1) n =
      (X.chainComplex (AddCommGrpCat.of ℤ)).d (n + 1) n ≫
        barycentricSubdivisionComponent X n

/-- The single explicit maximal-flag cancellation theorem implies all degreewise chain
compatibilities. -/
public theorem barycentricSubdivisionComponentsCommute_of_fundamentalBoundary
    (h : BarycentricFundamentalBoundaryIdentity) :
    BarycentricSubdivisionComponentsCommute := by
  intro X n
  apply X.chainComplex_hom_ext
  intro x
  rw [← Category.assoc, iota_barycentricSubdivisionComponent,
    barycentricSubdivisionSimplexChain_boundary h]
  rw [← Category.assoc, SSet.ιChainComplex_d, Preadditive.sum_comp]
  simp only [Preadditive.zsmul_comp, iota_barycentricSubdivisionComponent]
  rfl

/-- The actual all-degree barycentric subdivision chain morphism, conditional only on the
explicit permutation-boundary cancellation theorem. -/
public noncomputable def barycentricSubdivisionChainMapOfFundamentalBoundary
    (h : BarycentricFundamentalBoundaryIdentity) (X : SSet.{0}) :
    X.chainComplex (AddCommGrpCat.of ℤ) ⟶
      (SSet.sd.obj X).chainComplex (AddCommGrpCat.of ℤ) :=
  ChainComplex.ofHom (barycentricSubdivisionComponent X)
    (barycentricSubdivisionComponentsCommute_of_fundamentalBoundary h X)

/-- The constructed all-degree chain morphism, now conditional only on the isolated
outer-face permutation reindexing. -/
public noncomputable def barycentricSubdivisionChainMapOfOuterFaceIdentity
    (h : BarycentricOuterFaceIdentity) (X : SSet.{0}) :
    X.chainComplex (AddCommGrpCat.of ℤ) ⟶
      (SSet.sd.obj X).chainComplex (AddCommGrpCat.of ℤ) :=
  barycentricSubdivisionChainMapOfFundamentalBoundary
    (barycentricFundamentalBoundaryIdentity_of_outerFaceIdentity h) X

@[simp]
public theorem barycentricSubdivisionChainMapOfOuterFaceIdentity_f
    (h : BarycentricOuterFaceIdentity) (X : SSet.{0}) (n : ℕ) :
    (barycentricSubdivisionChainMapOfOuterFaceIdentity h X).f n =
      barycentricSubdivisionComponent X n :=
  rfl

/-- Naturality of the all-degree chain morphism constructed from the outer-face identity. -/
public theorem barycentricSubdivisionChainMapOfOuterFaceIdentity_naturality
    (h : BarycentricOuterFaceIdentity) {X Y : SSet.{0}} (f : X ⟶ Y) :
    SSet.chainComplexMap f (AddCommGrpCat.of ℤ) ≫
        barycentricSubdivisionChainMapOfOuterFaceIdentity h Y =
      barycentricSubdivisionChainMapOfOuterFaceIdentity h X ≫
        SSet.chainComplexMap (SSet.sd.map f) (AddCommGrpCat.of ℤ) := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact barycentricSubdivisionComponent_naturality f n

/-- Once the explicit maximal-flag boundary calculation is supplied, the already constructed
degreewise maps assemble into the barycentric subdivision chain morphism. -/
public noncomputable def barycentricSubdivisionChainMap
    (h : BarycentricSubdivisionComponentsCommute) (X : SSet.{0}) :
    X.chainComplex (AddCommGrpCat.of ℤ) ⟶
      (SSet.sd.obj X).chainComplex (AddCommGrpCat.of ℤ) :=
  ChainComplex.ofHom (barycentricSubdivisionComponent X) (h X)

@[simp]
public theorem barycentricSubdivisionChainMap_f
    (h : BarycentricSubdivisionComponentsCommute) (X : SSet.{0}) (n : ℕ) :
    (barycentricSubdivisionChainMap h X).f n =
      barycentricSubdivisionComponent X n :=
  rfl

/-- The assembled barycentric subdivision chain maps are natural. -/
public theorem barycentricSubdivisionChainMap_naturality
    (h : BarycentricSubdivisionComponentsCommute)
    {X Y : SSet.{0}} (f : X ⟶ Y) :
    SSet.chainComplexMap f (AddCommGrpCat.of ℤ) ≫
        barycentricSubdivisionChainMap h Y =
      barycentricSubdivisionChainMap h X ≫
        SSet.chainComplexMap (SSet.sd.map f) (AddCommGrpCat.of ℤ) := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact barycentricSubdivisionComponent_naturality f n

end SphereSixComplex
