/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
module

public import SphereSixComplex.Topology.BinaryOpenCoverExcision
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# The geometric boundary for singular barycentric subdivision

This file develops the parts of the classical subdivision argument that can be proved from the
current Mathlib API. Compactness of the standard simplex gives a Lebesgue number for a binary
open cover. On the algebraic side, it is enough to prove eventual smallness on singular-simplex
generators: preservation of small chains then promotes this to arbitrary finite chains.

The remaining boundary is the affine barycentric operator itself. The fields below expose the
chain map, its prism homotopy, quotient descent, face locality, and generatorwise mesh decay as a
certificate rather than assuming excision as a single opaque proposition.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory Metric Set TopologicalSpace
open scoped Topology

namespace SphereSixComplex.BinaryOpenCover

/-! ## The Lebesgue-number step on a singular simplex -/

/-- The two inverse-image opens on the domain of a singular simplex. -/
public def simplexCoverSet {X : Type*} [TopologicalSpace X] {n : ℕ}
    (U V : Set X) (sigma : C(stdSimplex ℝ (Fin (n + 1)), X)) :
    Bool → Set (stdSimplex ℝ (Fin (n + 1)))
  | false => sigma ⁻¹' U
  | true => sigma ⁻¹' V

public theorem simplexCoverSet_isOpen {X : Type*} [TopologicalSpace X] {n : ℕ}
    {U V : Set X} (hU : IsOpen U) (hV : IsOpen V)
    (sigma : C(stdSimplex ℝ (Fin (n + 1)), X)) (b : Bool) :
    IsOpen (simplexCoverSet U V sigma b) := by
  cases b with
  | false => exact hU.preimage sigma.continuous
  | true => exact hV.preimage sigma.continuous

public theorem simplexCoverSet_iUnion_eq_univ {X : Type*} [TopologicalSpace X]
    {n : ℕ} {U V : Set X} (hcover : U ∪ V = Set.univ)
    (sigma : C(stdSimplex ℝ (Fin (n + 1)), X)) :
    ⋃ b, simplexCoverSet U V sigma b = Set.univ := by
  ext x
  have hx : sigma x ∈ U ∪ V := by rw [hcover]; exact Set.mem_univ _
  simpa [simplexCoverSet] using hx

/-- A singular simplex has a metric Lebesgue number for a binary open cover of its image. -/
public theorem singularSimplex_binaryLebesgueNumber
    {X : Type*} [TopologicalSpace X] {n : ℕ} {U V : Set X}
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (sigma : C(stdSimplex ℝ (Fin (n + 1)), X)) :
    ∃ delta > 0, ∀ x, Set.MapsTo sigma (Metric.ball x delta) U ∨
      Set.MapsTo sigma (Metric.ball x delta) V := by
  obtain ⟨delta, hdelta, hballs⟩ := lebesgue_number_lemma_of_metric
    (s := Set.univ) (c := simplexCoverSet U V sigma) isCompact_univ
    (simplexCoverSet_isOpen hU hV sigma)
    (by rw [simplexCoverSet_iUnion_eq_univ hcover sigma])
  refine ⟨delta, hdelta, fun x ↦ ?_⟩
  obtain ⟨b, hb⟩ := hballs x (Set.mem_univ x)
  cases b with
  | false => exact Or.inl hb
  | true => exact Or.inr hb

/-- Any set lying in one Lebesgue ball is sent into one member of the binary cover. -/
public theorem mapsTo_cover_of_subset_ball
    {X : Type*} [TopologicalSpace X] {n : ℕ} {U V : Set X}
    {sigma : C(stdSimplex ℝ (Fin (n + 1)), X)} {delta : ℝ}
    (hdelta : ∀ x, Set.MapsTo sigma (Metric.ball x delta) U ∨
      Set.MapsTo sigma (Metric.ball x delta) V)
    {s : Set (stdSimplex ℝ (Fin (n + 1)))} {x}
    (hs : s ⊆ Metric.ball x delta) :
    Set.MapsTo sigma s U ∨ Set.MapsTo sigma s V := by
  rcases hdelta x with hU | hV
  · exact Or.inl (hU.mono hs Subset.rfl)
  · exact Or.inr (hV.mono hs Subset.rfl)

/-! ## Iterates and finite-chain reduction -/

/-- Iteration of a chain endomorphism converts addition of exponents into composition. -/
public theorem chainMapIterate_add {K : ChainComplex AddCommGrpCat ℕ}
    (f : K ⟶ K) (k l : ℕ) :
    chainMapIterate f (k + l) = chainMapIterate f k ≫ chainMapIterate f l := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.succ_add, chainMapIterate_succ, chainMapIterate_succ, ih,
        Category.assoc]

/-- A chain endomorphism preserves cover-small chains degreewise. -/
public def PreservesCoverSmallChains {X : TopCat} (U V : Opens X)
    (f : singularChains X ⟶ singularChains X) : Prop :=
  ∀ n c, IsCoverSmallChain U V n c → IsCoverSmallChain U V n (f.f n c)

/-- Every iterate of a small-chain-preserving endomorphism again preserves small chains. -/
public theorem preservesCoverSmallChains_iterate {X : TopCat} {U V : Opens X}
    {f : singularChains X ⟶ singularChains X}
    (hf : PreservesCoverSmallChains U V f) :
    ∀ k n c, IsCoverSmallChain U V n c →
      IsCoverSmallChain U V n ((chainMapIterate f k).f n c)
  | 0, n, c, hc => by simpa using hc
  | k + 1, n, c, hc => by
      simpa only [chainMapIterate_succ, HomologicalComplex.comp_f,
        ConcreteCategory.comp_apply] using
        preservesCoverSmallChains_iterate hf k n (f.f n c) (hf n c hc)

/-- Eventual smallness under iterated subdivision. -/
public def IsEventuallyCoverSmallChain {X : TopCat} (U V : Opens X)
    (f : singularChains X ⟶ singularChains X) (n : ℕ)
    (c : (singularChains X).X n) : Prop :=
  ∃ k, IsCoverSmallChain U V n ((chainMapIterate f k).f n c)

public theorem isEventuallyCoverSmallChain_zero {X : TopCat} (U V : Opens X)
    (f : singularChains X ⟶ singularChains X) (n : ℕ) :
    IsEventuallyCoverSmallChain U V f n 0 := by
  exact ⟨0, by simpa using isCoverSmallChain_zero U V n⟩

public theorem IsEventuallyCoverSmallChain.raiseExponent {X : TopCat}
    {U V : Opens X} {f : singularChains X ⟶ singularChains X}
    (hf : PreservesCoverSmallChains U V f) {n k : ℕ}
    {c : (singularChains X).X n}
    (hc : IsCoverSmallChain U V n ((chainMapIterate f k).f n c)) (l : ℕ) :
    IsCoverSmallChain U V n ((chainMapIterate f (k + l)).f n c) := by
  have hsmall := preservesCoverSmallChains_iterate hf l n
    ((chainMapIterate f k).f n c) hc
  have hmaps := congrArg (fun g ↦ g.f n c) (chainMapIterate_add f k l)
  simpa only [HomologicalComplex.comp_f, ConcreteCategory.comp_apply] using
    hmaps.symm ▸ hsmall

public theorem IsEventuallyCoverSmallChain.add {X : TopCat} {U V : Opens X}
    {f : singularChains X ⟶ singularChains X}
    (hf : PreservesCoverSmallChains U V f) {n : ℕ}
    {c c' : (singularChains X).X n}
    (hc : IsEventuallyCoverSmallChain U V f n c)
    (hc' : IsEventuallyCoverSmallChain U V f n c') :
    IsEventuallyCoverSmallChain U V f n (c + c') := by
  obtain ⟨k, hk⟩ := hc
  obtain ⟨l, hl⟩ := hc'
  refine ⟨k + l, ?_⟩
  rw [map_add]
  exact (IsEventuallyCoverSmallChain.raiseExponent hf hk l).add (by
    rw [Nat.add_comm]
    exact IsEventuallyCoverSmallChain.raiseExponent hf hl k)

public theorem IsEventuallyCoverSmallChain.neg {X : TopCat} {U V : Opens X}
    {f : singularChains X ⟶ singularChains X} {n : ℕ}
    {c : (singularChains X).X n} (hc : IsEventuallyCoverSmallChain U V f n c) :
    IsEventuallyCoverSmallChain U V f n (-c) := by
  obtain ⟨k, hk⟩ := hc
  exact ⟨k, by simpa using hk.neg⟩

/-- Eventually small chains form an additive subgroup in each degree. -/
public def eventuallyCoverSmallAddSubgroup {X : TopCat} (U V : Opens X)
    (f : singularChains X ⟶ singularChains X)
    (hf : PreservesCoverSmallChains U V f) (n : ℕ) :
    AddSubgroup ((singularChains X).X n) where
  carrier := IsEventuallyCoverSmallChain U V f n
  zero_mem' := isEventuallyCoverSmallChain_zero U V f n
  add_mem' := IsEventuallyCoverSmallChain.add hf
  neg_mem' := IsEventuallyCoverSmallChain.neg

/-- The integral chain represented by one singular-simplex generator. -/
public def singularSimplexChain (X : TopCat) (n : ℕ)
    (sigma : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))) :
    (singularChains X).X n :=
  ((TopCat.toSSet.obj X).ιChainComplex (R := AddCommGrpCat.of ℤ) sigma) (1 : ℤ)

/-- Generatorwise eventual smallness implies chainwise eventual smallness. -/
public theorem eventuallySmall_of_generators {X : TopCat} {U V : Opens X}
    {f : singularChains X ⟶ singularChains X}
    (hf : PreservesCoverSmallChains U V f)
    (hgenerators : ∀ n
      (sigma : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))),
      IsEventuallyCoverSmallChain U V f n (singularSimplexChain X n sigma)) :
    ∀ n c, IsEventuallyCoverSmallChain U V f n c := by
  intro n c
  let S := eventuallyCoverSmallAddSubgroup U V f hf n
  let q : (singularChains X).X n ⟶ AddCommGrpCat.of ((singularChains X).X n ⧸ S) :=
    AddCommGrpCat.ofHom (QuotientAddGroup.mk' S)
  have hq : q = 0 := by
    apply (TopCat.toSSet.obj X).chainComplex_hom_ext
    intro sigma
    apply AddCommGrpCat.int_hom_ext
    simp only [CategoryTheory.comp_apply]
    change QuotientAddGroup.mk' S (singularSimplexChain X n sigma) = 0
    rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
    exact hgenerators n sigma
  change c ∈ S
  rw [← QuotientAddGroup.eq_zero_iff]
  change q c = 0
  rw [hq]
  rfl

/-! ## A generatorwise certificate and the exact remaining boundary -/

/-- The classical certificate with smallness required only on simplex generators.

The fields `ambient`, `quotient`, and `projection_comm` contain the barycentric chain map and its
descended prism homotopy. `preservesSmall` is face-locality, while `generatorEventuallySmall` is
the mesh-shrinking consequence of the Lebesgue-number lemma above. -/
public structure GeneratorwiseCoverSubdivisionData {X : TopCat} (U V : Opens X) where
  isCover : U ⊔ V = ⊤
  ambient : ChainSubdivision (singularChains X)
  quotient : ChainSubdivision (coverChainQuotient U V)
  projection_comm :
    ambient.map ≫ coverChainQuotientProjection U V =
      coverChainQuotientProjection U V ≫ quotient.map
  preservesSmall : PreservesCoverSmallChains U V ambient.map
  generatorEventuallySmall :
    ∀ n (sigma : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))),
      IsEventuallyCoverSmallChain U V ambient.map n (singularSimplexChain X n sigma)

namespace GeneratorwiseCoverSubdivisionData

/-- Generatorwise data assemble into the chainwise certificate used by excision. -/
public def toCoverSubdivisionData {X : TopCat} {U V : Opens X}
    (D : GeneratorwiseCoverSubdivisionData U V) : CoverSubdivisionData U V where
  isCover := D.isCover
  ambient := D.ambient
  quotient := D.quotient
  projection_comm := D.projection_comm
  eventuallySmall := eventuallySmall_of_generators D.preservesSmall D.generatorEventuallySmall

/-- The generatorwise certificate proves the generated-cover comparison is a quasi-isomorphism. -/
public theorem coverChainInclusion_quasiIso {X : TopCat} {U V : Opens X}
    (D : GeneratorwiseCoverSubdivisionData U V) :
    QuasiIso (coverChainInclusion U V) :=
  D.toCoverSubdivisionData.coverChainInclusion_quasiIso

end GeneratorwiseCoverSubdivisionData

/-- Exact affine/prism construction still needed to complete binary-cover subdivision. -/
public def GeneratorwiseBinaryOpenCoverSubdivisionStatement : Prop :=
  ∀ (X : TopCat) (U V : Opens X), U ⊔ V = ⊤ →
    Nonempty (GeneratorwiseCoverSubdivisionData U V)

/-- The generatorwise construction is sufficient for the original subdivision statement. -/
public theorem binaryOpenCoverSubdivisionStatement_of_generatorwise
    (h : GeneratorwiseBinaryOpenCoverSubdivisionStatement) :
    BinaryOpenCoverSubdivisionStatement := by
  intro X U V hcover
  obtain ⟨D⟩ := h X U V hcover
  exact ⟨D.toCoverSubdivisionData⟩

end SphereSixComplex.BinaryOpenCover
