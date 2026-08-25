module

public import SphereSixComplex.Topology.FirstQuadrantColumnFiltrationQuotient
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.Abelian

/-!
# Short exact sequences for the finite column filtration

The inclusion from the prefix ending in column `p` to the prefix ending in column `p + 1`
is the kernel of projection to the new final column.  Consequently the successive quotients
of the finite column filtration are single-column bicomplexes.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits ZeroObject

namespace SphereSixComplex

set_option backward.isDefEq.respectTransparency false in
/-- The differential of a finite prefix, transported to the original bicomplex in two
retained degrees. -/
public theorem firstQuadrantColumnPrefix_d_eq
    (K : FirstQuadrantBicomplex) (n i j : ℕ) (hi : i ≤ n) (hj : j ≤ n) :
    (firstQuadrantColumnPrefix K n).d i j =
      (firstQuadrantColumnPrefixXIso K n i hi).hom ≫ K.d i j ≫
        (firstQuadrantColumnPrefixXIso K n j hj).inv := by
  let e := firstQuadrantColumnPrefixEmbedding n
  have h := HomologicalComplex.extend_d_eq
    (K := K.restriction e) (e := e)
    (i' := i) (j' := j) (i := ⟨i, hi⟩) (j := ⟨j, hj⟩) (hi := rfl) (hj := rfl)
  simpa [e, firstQuadrantColumnPrefix, firstQuadrantColumnPrefixXIso,
    firstQuadrantColumnPrefixEmbedding, ComplexShape.Embedding.mk',
    HomologicalComplex.stupidTrunc, HomologicalComplex.stupidTruncXIso,
    HomologicalComplex.restriction] using h

/-- Component of the canonical inclusion of two consecutive finite column prefixes. -/
public noncomputable def firstQuadrantColumnPrefixSuccInclusionComponent
    (K : FirstQuadrantBicomplex) (p q : ℕ) :
    (firstQuadrantColumnPrefix K p).X q ⟶
      (firstQuadrantColumnPrefix K (p + 1)).X q := by
  by_cases hq : q ≤ p
  · exact (firstQuadrantColumnPrefixXIso K p q hq).hom ≫
      (firstQuadrantColumnPrefixXIso K (p + 1) q (by omega)).inv
  · exact 0

@[simp]
public theorem firstQuadrantColumnPrefixSuccInclusionComponent_of_le
    (K : FirstQuadrantBicomplex) (p q : ℕ) (hq : q ≤ p) :
    firstQuadrantColumnPrefixSuccInclusionComponent K p q =
      (firstQuadrantColumnPrefixXIso K p q hq).hom ≫
        (firstQuadrantColumnPrefixXIso K (p + 1) q (by omega)).inv := by
  simp [firstQuadrantColumnPrefixSuccInclusionComponent, hq]

public theorem firstQuadrantColumnPrefixSuccInclusionComponent_eq_zero
    (K : FirstQuadrantBicomplex) (p q : ℕ) (hq : p < q) :
    firstQuadrantColumnPrefixSuccInclusionComponent K p q = 0 := by
  simp [firstQuadrantColumnPrefixSuccInclusionComponent, show ¬ q ≤ p by omega]

set_option backward.isDefEq.respectTransparency false in
/-- Canonical inclusion from the prefix through `p` into the prefix through `p + 1`. -/
public noncomputable def firstQuadrantColumnPrefixSuccInclusion
    (K : FirstQuadrantBicomplex) (p : ℕ) :
    firstQuadrantColumnPrefix K p ⟶ firstQuadrantColumnPrefix K (p + 1) where
  f := firstQuadrantColumnPrefixSuccInclusionComponent K p
  comm' i j hij := by
    change j + 1 = i at hij
    by_cases hi : i ≤ p
    · have hj : j ≤ p := by omega
      rw [firstQuadrantColumnPrefixSuccInclusionComponent_of_le K p i hi,
        firstQuadrantColumnPrefixSuccInclusionComponent_of_le K p j hj,
        firstQuadrantColumnPrefix_d_eq K (p + 1) i j (by omega) (by omega),
        firstQuadrantColumnPrefix_d_eq K p i j hi hj]
      simp
    · rw [firstQuadrantColumnPrefixSuccInclusionComponent_eq_zero K p i (by omega),
        zero_comp]
      have hz : IsZero ((firstQuadrantColumnPrefix K p).X i) :=
        firstQuadrantColumnPrefix_isZero_X K p i (by omega)
      exact hz.eq_of_src _ _

@[reassoc (attr := simp)]
public theorem firstQuadrantColumnPrefixSuccInclusion_comp_toLast
    (K : FirstQuadrantBicomplex) (p : ℕ) :
    firstQuadrantColumnPrefixSuccInclusion K p ≫
      firstQuadrantColumnPrefixToLast K (p + 1) = 0 := by
  apply HomologicalComplex.hom_ext
  intro q
  by_cases hq : q ≤ p
  · have hne : q ≠ p + 1 := by omega
    change firstQuadrantColumnPrefixSuccInclusionComponent K p q ≫
      firstQuadrantColumnPrefixToLastComponent K (p + 1) q = 0
    rw [firstQuadrantColumnPrefixToLastComponent_eq_zero K (p + 1) q hne,
      comp_zero]
  · change firstQuadrantColumnPrefixSuccInclusionComponent K p q ≫
      firstQuadrantColumnPrefixToLastComponent K (p + 1) q = 0
    rw [firstQuadrantColumnPrefixSuccInclusionComponent_eq_zero K p q (by omega),
      zero_comp]

/-- The inclusion of one finite prefix into the next is the kernel of projection onto the
new final column. -/
public noncomputable def firstQuadrantColumnPrefixSuccInclusionIsKernel
    (K : FirstQuadrantBicomplex) (p : ℕ) :
    IsLimit (KernelFork.ofι
      (firstQuadrantColumnPrefixSuccInclusion K p)
      (firstQuadrantColumnPrefixSuccInclusion_comp_toLast K p)) := by
  apply HomologicalComplex.isLimitOfEval
  intro q
  refine (Limits.isLimitMapConeForkEquiv'
    (HomologicalComplex.eval (ChainComplex AddCommGrpCat ℕ) (ComplexShape.down ℕ) q)
    (firstQuadrantColumnPrefixSuccInclusion_comp_toLast K p)).symm ?_
  change IsLimit (KernelFork.ofι
    (HomologicalComplex.Hom.f (firstQuadrantColumnPrefixSuccInclusion K p) q)
    _)
  by_cases hq : q ≤ p
  · let e : (firstQuadrantColumnPrefix K p).X q ≅
        (firstQuadrantColumnPrefix K (p + 1)).X q :=
      firstQuadrantColumnPrefixXIso K p q hq ≪≫
        (firstQuadrantColumnPrefixXIso K (p + 1) q (by omega)).symm
    have he : (firstQuadrantColumnPrefixSuccInclusion K p).f q = e.hom := by
      change firstQuadrantColumnPrefixSuccInclusionComponent K p q = e.hom
      simp [e, firstQuadrantColumnPrefixSuccInclusionComponent_of_le K p q hq]
    refine KernelFork.IsLimit.ofι _ _
      (fun {_} k _ => k ≫ e.inv) ?_ ?_
    · intro W k hk
      rw [he, Category.assoc, e.inv_hom_id, Category.comp_id]
    · intro W k hk m hm
      rw [he] at hm
      rw [← hm, Category.assoc, e.hom_inv_id, Category.comp_id]
  · have hpq : p < q := by omega
    have hz : IsZero ((firstQuadrantColumnPrefix K p).X q) :=
      firstQuadrantColumnPrefix_isZero_X K p q hpq
    apply KernelFork.IsLimit.ofMonoOfIsZero _ _ hz
    by_cases hself : q = p + 1
    · subst q
      change Mono (firstQuadrantColumnPrefixToLastComponent K (p + 1) (p + 1))
      rw [firstQuadrantColumnPrefixToLastComponent_self]
      infer_instance
    · have hgt : p + 1 < q := by omega
      exact (firstQuadrantColumnPrefix_isZero_X K (p + 1) q hgt).mono _

/-- The canonical short complex associated to one step of the finite column filtration. -/
local instance : Preadditive FirstQuadrantBicomplex :=
  (inferInstance : Abelian FirstQuadrantBicomplex).toPreadditive

local instance : HasZeroMorphisms FirstQuadrantBicomplex :=
  Preadditive.preadditiveHasZeroMorphisms

public noncomputable def firstQuadrantColumnPrefixSuccShortComplex
    (K : FirstQuadrantBicomplex) (p : ℕ) :
    ShortComplex FirstQuadrantBicomplex :=
  ShortComplex.mk
    (firstQuadrantColumnPrefixSuccInclusion K p)
    (firstQuadrantColumnPrefixToLast K (p + 1))
    (firstQuadrantColumnPrefixSuccInclusion_comp_toLast K p)

/-- Each step of the finite column filtration is a short exact sequence whose quotient is
the newly added single column. -/
public theorem firstQuadrantColumnPrefixSuccShortComplex_shortExact
    (K : FirstQuadrantBicomplex) (p : ℕ) :
    (firstQuadrantColumnPrefixSuccShortComplex K p).ShortExact := by
  exact
    { exact := (firstQuadrantColumnPrefixSuccShortComplex K p).exact_of_f_is_kernel
        (firstQuadrantColumnPrefixSuccInclusionIsKernel K p)
      mono_f := mono_of_isLimit_fork
        (firstQuadrantColumnPrefixSuccInclusionIsKernel K p)
      epi_g := firstQuadrantColumnPrefixToLast_epi K (p + 1) }

end SphereSixComplex
