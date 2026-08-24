module

public import SphereSixComplex.Topology.SingularBarycentricAllDegrees

/-!
# The outer-face identity for barycentric fundamental chains

This file reindexes the surviving outer faces of the signed maximal-flag sum by the omitted
vertex and the induced ordering of its complement.  It completes the boundary calculation and
therefore supplies the unconditional natural barycentric subdivision chain morphism.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits PartialOrder Simplicial

namespace SphereSixComplex

/-- `Finset.image` does not depend propositionally on the chosen decidable equality. -/
public theorem finsetImage_decidableEq_independent
    {α β : Type*} (d₁ d₂ : DecidableEq β) (f : α → β) (s : Finset α) :
    @Finset.image α β d₁ f s = @Finset.image α β d₂ f s := by
  ext y
  simp only [Finset.mem_image]

/-- Insert the omitted vertex `p` at the final position of an ordering of its complement. -/
public noncomputable def insertOmittedVertexLast {n : ℕ}
    (p : Fin (n + 2)) (τ : Equiv.Perm (Fin (n + 1))) :
    Equiv.Perm (Fin (n + 2)) where
  toFun := Fin.lastCases p (fun k ↦ p.succAbove (τ k))
  invFun := Fin.succAboveCases p (Fin.last (n + 1))
    (fun k ↦ (τ.symm k).castSucc)
  left_inv i := by
    refine Fin.lastCases ?_ (fun k ↦ ?_) i
    · simp
    · simp
  right_inv i := by
    refine Fin.succAboveCases p ?_ (fun k ↦ ?_) i
    · simp
    · simp

@[simp]
public theorem insertOmittedVertexLast_apply_last {n : ℕ}
    (p : Fin (n + 2)) (τ : Equiv.Perm (Fin (n + 1))) :
    insertOmittedVertexLast p τ (Fin.last (n + 1)) = p := by
  simp [insertOmittedVertexLast]

@[simp]
public theorem insertOmittedVertexLast_apply_castSucc {n : ℕ}
    (p : Fin (n + 2)) (τ : Equiv.Perm (Fin (n + 1))) (k : Fin (n + 1)) :
    insertOmittedVertexLast p τ k.castSucc = p.succAbove (τ k) := by
  simp [insertOmittedVertexLast]

/-- Every permutation is uniquely an omitted final vertex together with an ordering of its
complement. -/
public noncomputable def insertOmittedVertexLastEquiv (n : ℕ) :
    Fin (n + 2) × Equiv.Perm (Fin (n + 1)) ≃
      Equiv.Perm (Fin (n + 2)) :=
  Equiv.ofBijective (fun pτ ↦ insertOmittedVertexLast pτ.1 pτ.2) <| by
    rw [Fintype.bijective_iff_injective_and_card]
    constructor
    · rintro ⟨p, τ⟩ ⟨q, υ⟩ h
      have hp := congrArg (fun σ ↦ σ (Fin.last (n + 1))) h
      simp only [insertOmittedVertexLast_apply_last] at hp
      subst q
      congr 1
      apply Equiv.ext
      intro k
      apply p.succAbove_right_injective
      have hk := congrArg (fun σ ↦ σ k.castSucc) h
      simpa only [insertOmittedVertexLast_apply_castSucc] using hk
    · simp [Fintype.card_prod, Fintype.card_perm, Nat.factorial_succ]

@[simp]
public theorem insertOmittedVertexLastEquiv_apply
    (n : ℕ) (pτ : Fin (n + 2) × Equiv.Perm (Fin (n + 1))) :
    insertOmittedVertexLastEquiv n pτ =
      insertOmittedVertexLast pτ.1 pτ.2 :=
  rfl

/-- The reindexing equivalence really records the omitted final vertex in its first
coordinate. -/
@[simp]
public theorem insertOmittedVertexLastEquiv_symm_fst
    (n : ℕ) (σ : Equiv.Perm (Fin (n + 2))) :
    ((insertOmittedVertexLastEquiv n).symm σ).1 = σ (Fin.last (n + 1)) := by
  let pτ := (insertOmittedVertexLastEquiv n).symm σ
  have h := (insertOmittedVertexLastEquiv n).apply_symm_apply σ
  change insertOmittedVertexLast pτ.1 pτ.2 = σ at h
  have hlast := congrArg (fun e ↦ e (Fin.last (n + 1))) h
  simpa only [insertOmittedVertexLast_apply_last] using hlast

/-- The order of the complement obtained after recording the omitted final vertex. -/
public noncomputable def permutationLastComplementOrder
    (n : ℕ) (σ : Equiv.Perm (Fin (n + 2))) :
    Equiv.Perm (Fin (n + 1)) :=
  ((insertOmittedVertexLastEquiv n).symm σ).2

@[simp]
public theorem permutationLastComplementOrder_insert
    {n : ℕ} (p : Fin (n + 2)) (τ : Equiv.Perm (Fin (n + 1))) :
    permutationLastComplementOrder n (insertOmittedVertexLast p τ) = τ := by
  change ((insertOmittedVertexLastEquiv n).symm
    (insertOmittedVertexLastEquiv n (p, τ))).2 = τ
  rw [(insertOmittedVertexLastEquiv n).symm_apply_apply]

/-- Mathlib's rotate-and-`decomposeFin` parametrization and the order-preserving parametrization
record the same omitted vertex. -/
public theorem permutationLastDecomposition_fst_eq_orderPreserving
    (n : ℕ) (σ : Equiv.Perm (Fin (n + 2))) :
    (permutationLastDecomposition n σ).1 =
      ((insertOmittedVertexLastEquiv n).symm σ).1 := by
  rw [permutationLastDecomposition_fst,
    insertOmittedVertexLastEquiv_symm_fst]

/-- Exact compatibility of `decomposeFin` with order-preserving deletion: before its final
vertex, `σ` is the monotone face inclusion applied to the induced complement ordering. -/
public theorem permutationLastDecomposition_orderCompatibility
    (n : ℕ) (σ : Equiv.Perm (Fin (n + 2))) (k : Fin (n + 1)) :
    σ k.castSucc =
      (permutationLastDecomposition n σ).1.succAbove
        (permutationLastComplementOrder n σ k) := by
  let pτ := (insertOmittedVertexLastEquiv n).symm σ
  have h := (insertOmittedVertexLastEquiv n).apply_symm_apply σ
  change insertOmittedVertexLast pτ.1 pτ.2 = σ at h
  rw [← h, insertOmittedVertexLast_apply_castSucc,
    permutationLastDecomposition_fst, insertOmittedVertexLast_apply_last,
    permutationLastComplementOrder_insert]

/-- `Fin.castSucc` identifies `Fin (n+1)` with all vertices except the last one. -/
public def finCastSuccEquivNotLast (n : ℕ) :
    Fin (n + 1) ≃ {i : Fin (n + 2) // i ≠ Fin.last (n + 1)} where
  toFun i := ⟨i.castSucc, Fin.castSucc_lt_last i |>.ne⟩
  invFun i := i.1.castPred i.2
  left_inv _ := Fin.castPred_castSucc
  right_inv i := Subtype.ext (Fin.castSucc_castPred i.1 i.2)

/-- Inserting the last vertex last extends a permutation while fixing that vertex. -/
public theorem insertOmittedVertexLast_last_eq_extendDomain
    {n : ℕ} (τ : Equiv.Perm (Fin (n + 1))) :
    insertOmittedVertexLast (Fin.last (n + 1)) τ =
      τ.extendDomain (finCastSuccEquivNotLast n) := by
  apply Equiv.ext
  intro i
  refine Fin.lastCases ?_ (fun k ↦ ?_) i
  · rw [insertOmittedVertexLast_apply_last]
    symm
    apply Equiv.Perm.extendDomain_apply_not_subtype
    simp
  · rw [insertOmittedVertexLast_apply_castSucc]
    change (Fin.last (n + 1)).succAbove (τ k) =
      τ.extendDomain (finCastSuccEquivNotLast n) ↑((finCastSuccEquivNotLast n) k)
    rw [Equiv.Perm.extendDomain_apply_image τ (finCastSuccEquivNotLast n) k]
    simp [finCastSuccEquivNotLast]

/-- Inserting `p` last factors into the order-preserving cycle from the last vertex to `p`,
followed by extension of the complement ordering. -/
public theorem insertOmittedVertexLast_eq_cycle_mul_extend {n : ℕ}
    (p : Fin (n + 2)) (τ : Equiv.Perm (Fin (n + 1))) :
    insertOmittedVertexLast p τ =
      p.cycleIcc (Fin.last (n + 1)) *
        τ.extendDomain (finCastSuccEquivNotLast n) := by
  rw [← insertOmittedVertexLast_last_eq_extendDomain]
  apply Equiv.ext
  intro i
  refine Fin.lastCases ?_ (fun k ↦ ?_) i
  · rw [insertOmittedVertexLast_apply_last, Equiv.Perm.mul_apply,
      insertOmittedVertexLast_apply_last]
    exact (Fin.cycleIcc_of_last (Fin.le_last p)).symm
  · rw [insertOmittedVertexLast_apply_castSucc, Equiv.Perm.mul_apply,
      insertOmittedVertexLast_apply_castSucc]
    exact (congrFun
      (Fin.cycleIcc_comp_succAbove p (Fin.last (n + 1)) (Fin.le_last p)) (τ k)).symm

/-- The sign of an ordering with omitted vertex `p` inserted last. -/
public theorem permutationSignInteger_insertOmittedVertexLast {n : ℕ}
    (p : Fin (n + 2)) (τ : Equiv.Perm (Fin (n + 1))) :
    permutationSignInteger (insertOmittedVertexLast p τ) =
      (-1 : ℤ) ^ (n + 1 - p.val) * permutationSignInteger τ := by
  rw [insertOmittedVertexLast_eq_cycle_mul_extend]
  simp only [permutationSignInteger, Equiv.Perm.sign_mul,
    Equiv.Perm.sign_extendDomain, Fin.sign_cycleIcc_of_le (Fin.le_last p),
    Fin.val_last]
  simp

/-- Multiplying by the boundary sign of the final face leaves exactly the usual sign of the
omitted vertex. -/
public theorem outerFaceCoefficient_insertOmittedVertexLast {n : ℕ}
    (p : Fin (n + 2)) (τ : Equiv.Perm (Fin (n + 1))) :
    permutationSignInteger (insertOmittedVertexLast p τ) * (-1 : ℤ) ^ (n + 1) =
      (-1 : ℤ) ^ p.val * permutationSignInteger τ := by
  rw [permutationSignInteger_insertOmittedVertexLast]
  have hp : p.val ≤ n + 1 := Nat.le_of_lt_succ p.isLt
  have hadd : n + 1 - p.val + p.val = n + 1 := Nat.sub_add_cancel hp
  nth_rewrite 2 [← hadd]
  rw [pow_add]
  calc
    (-1 : ℤ) ^ (n + 1 - p.val) * permutationSignInteger τ *
          ((-1 : ℤ) ^ (n + 1 - p.val) * (-1 : ℤ) ^ p.val) =
        (((-1 : ℤ) ^ (n + 1 - p.val)) *
          ((-1 : ℤ) ^ (n + 1 - p.val))) *
            ((-1 : ℤ) ^ p.val * permutationSignInteger τ) := by ring
    _ = ((-1 : ℤ) * (-1 : ℤ)) ^ (n + 1 - p.val) *
          ((-1 : ℤ) ^ p.val * permutationSignInteger τ) := by rw [mul_pow]
    _ = _ := by norm_num

/-- The `decomposeFin` sign written using the order-preserving complement ordering. -/
public theorem permutationLastDecomposition_signCompatibility
    (n : ℕ) (σ : Equiv.Perm (Fin (n + 2))) :
    permutationSignInteger σ =
      (-1 : ℤ) ^ (n + 1 - (permutationLastDecomposition n σ).1.val) *
        permutationSignInteger (permutationLastComplementOrder n σ) := by
  let pτ := (insertOmittedVertexLastEquiv n).symm σ
  have h := (insertOmittedVertexLastEquiv n).apply_symm_apply σ
  change insertOmittedVertexLast pτ.1 pτ.2 = σ at h
  rw [← h, permutationSignInteger_insertOmittedVertexLast,
    permutationLastDecomposition_fst, insertOmittedVertexLast_apply_last,
    permutationLastComplementOrder_insert]

/-- Deleting the final (full-set) prefix of an inserted ordering is the subdivided face obtained
by omitting `p`. -/
public theorem permutationMaximalFlagSimplex_outerFace_insert {n : ℕ}
    (p : Fin (n + 2)) (τ : Equiv.Perm (Fin (n + 1))) :
    (SimplexCategory.sd.{0}.obj (SimplexCategory.mk (n + 1))).δ (Fin.last (n + 1))
        (permutationMaximalFlagSimplex (insertOmittedVertexLast p τ)) =
      (SimplexCategory.sd.{0}.map (SimplexCategory.δ p)).app
        (Opposite.op (SimplexCategory.mk n))
        (permutationMaximalFlagSimplex τ) := by
  refine ComposableArrows.ext (fun k ↦ ?_) (fun k hk ↦ ?_)
  · change permutationPrefixChain (insertOmittedVertexLast p τ)
      ((Fin.last (n + 1)).succAbove k) =
        (permutationPrefixChain τ k).map
          (SimplexCategory.toPartOrd.{0}.map (SimplexCategory.δ p)).hom
    apply NonemptyFiniteChains.ext
    have hfinset :
        permutationPrefixFinset (insertOmittedVertexLast p τ)
            ((Fin.last (n + 1)).succAbove k) =
          Finset.image (fun i : ULift.{0} (Fin (n + 1)) ↦
            ULift.up (p.succAbove i.down)) (permutationPrefixFinset τ k) := by
      rw [Fin.succAbove_last]
      unfold permutationPrefixFinset
      rw [← Fin.finsetImage_castSucc_Iic k, Finset.image_image, Finset.image_image]
      apply Finset.image_congr
      intro a ha
      simp
    unfold permutationPrefixChain nonemptyFiniteChainOfFinset NonemptyFiniteChains.map
    dsimp only
    have hmap (i : ULift.{0} (Fin (n + 1))) :
        (SimplexCategory.toPartOrd.{0}.map (SimplexCategory.δ p)).hom i =
          ULift.up (p.succAbove i.down) := by
      induction i
      rfl
    calc
      _ = Finset.image (fun i : ULift.{0} (Fin (n + 1)) ↦
          ULift.up (p.succAbove i.down)) (permutationPrefixFinset τ k) := hfinset
      _ = _ := by
        rw [show (fun i : ULift.{0} (Fin (n + 1)) ↦
          ULift.up (p.succAbove i.down)) =
            (SimplexCategory.toPartOrd.{0}.map (SimplexCategory.δ p)).hom from
              funext (fun i ↦ (hmap i).symm)]
        apply finsetImage_decidableEq_independent
  · apply Subsingleton.elim

/-- The surviving outer faces reindex to the alternating sum of subdivided simplex faces. -/
public theorem barycentricOuterFaceIdentity : BarycentricOuterFaceIdentity := by
  intro n
  rw [subdividedSimplexOuterFaceSum, subdividedSimplexAlternatingFaceChain]
  rw [← Equiv.sum_comp (insertOmittedVertexLastEquiv n)]
  rw [Fintype.sum_prod_type]
  simp only [insertOmittedVertexLastEquiv_apply, smul_smul, Fin.val_last,
    outerFaceCoefficient_insertOmittedVertexLast,
    permutationMaximalFlagSimplex_outerFace_insert]
  simp_rw [subdividedSimplexFundamentalChain, Preadditive.sum_comp,
    Preadditive.zsmul_comp, Finset.smul_sum, SSet.ι_chainComplexMap_f]
  simp only [smul_smul]

/-- The signed maximal-flag fundamental chains satisfy the complete alternating boundary
identity in every degree. -/
public theorem barycentricFundamentalBoundaryIdentity :
    BarycentricFundamentalBoundaryIdentity :=
  barycentricFundamentalBoundaryIdentity_of_outerFaceIdentity
    barycentricOuterFaceIdentity

/-- The unconditional natural barycentric subdivision chain morphism. -/
public noncomputable def barycentricSubdivisionChainMapCanonical (X : SSet.{0}) :
    X.chainComplex (AddCommGrpCat.of ℤ) ⟶
      (SSet.sd.obj X).chainComplex (AddCommGrpCat.of ℤ) :=
  barycentricSubdivisionChainMapOfOuterFaceIdentity
    barycentricOuterFaceIdentity X

@[simp]
public theorem barycentricSubdivisionChainMapCanonical_f
    (X : SSet.{0}) (n : ℕ) :
    (barycentricSubdivisionChainMapCanonical X).f n =
      barycentricSubdivisionComponent X n :=
  rfl

/-- Naturality of the unconditional barycentric subdivision chain morphism. -/
public theorem barycentricSubdivisionChainMapCanonical_naturality
    {X Y : SSet.{0}} (f : X ⟶ Y) :
    SSet.chainComplexMap f (AddCommGrpCat.of ℤ) ≫
        barycentricSubdivisionChainMapCanonical Y =
      barycentricSubdivisionChainMapCanonical X ≫
        SSet.chainComplexMap (SSet.sd.map f) (AddCommGrpCat.of ℤ) :=
  barycentricSubdivisionChainMapOfOuterFaceIdentity_naturality
    barycentricOuterFaceIdentity f

end SphereSixComplex
