module

public import SphereSixComplex.Topology.EstablishedStrongDeformationRetracts
public import Mathlib.Topology.CWComplex.Classical.Subcomplex

/-!
# A relative CW pair is a cofibration

This file proves that the inclusion of the base of a relative CW complex has the homotopy-extension
property (Hatcher, *Algebraic Topology*, Prop. 0.16), in the form of the interface
`SphereSixComplex.HasHomotopyExtensionProperty`.  The main theorem is
`hasHomotopyExtensionProperty_of_relativeCWComplex_proved`, which replaces a former axiom of
`EstablishedGeneralTopology`.

All declarations live in `SphereSixComplex.EstablishedGeneralTopology`.

## The disc-cylinder retraction

* `discCylinderRetraction`: the cylinder `Dⁿ × I` over the closed unit ball of `Fin n → ℝ`
  retracts onto `Dⁿ × {0} ∪ ∂Dⁿ × I`, by radial projection away from the point `(0, 2)` above the
  cylinder.  Writing `u = max ‖x‖ ((2 - t)/2)`, the retraction is the single closed formula
  `(x, t) ↦ (u⁻¹ • x, 2 - (2 - t)/u)`: because `u ≥ 1/2` on `I` there is no case split and no
  gluing to do.  Mathlib's cells are modelled on the *sup*-metric ball, i.e. on a cube; radial
  projection is insensitive to this.  `discCylinderRetraction_mem_lShape` and
  `discCylinderRetraction_fix` are its two defining properties, and
  `exists_discCylinderRetraction` is the existence form.

## Reduction of the homotopy-extension property to a retraction

* `hasHomotopyExtensionProperty_of_cylinderRetraction`: a retraction of `I × X` onto
  `{0} × X ∪ I × A` gives the homotopy-extension property of `A ⊆ X` (Hatcher, p. 14).
* `hasHomotopyExtensionProperty_of_relativeCWComplex_of_cylinderRetraction`: the same for a
  relative CW pair, where the closedness of the base is free (`RelCWComplex.isClosedBase`).
* `exists_cylinderRetraction_trans`: cylinder retractions compose along a filtration
  `A ⊆ B ⊆ X`, which is the step that chains successive skeletal retractions.

## The weak topology

* `isQuotientMap_cellModelProj`: the tautological map onto the complex from the disjoint union
  `cellModel` of all its closed cells with its base is a quotient map.  This repackages the
  weak-topology field `RelCWComplex.closed'` in the form that composes with Whitehead's theorem.
  It needs `[T2Space X]`, which is what makes the compact image of a closed subset of a closed
  cell closed in the complex; `RelCWComplex` deliberately does not provide this, and this is the
  reason the cofibration statement itself has to carry a Hausdorff hypothesis.
* `continuous_of_continuous_cellPoint`: a map out of the complex is continuous as soon as its
  composites with the characteristic maps of the cells and with the inclusion of the base are.
* `continuous_prod_of_continuous_cellPoint`: the same criterion for maps out of `I × C`, obtained
  from the previous one by `Topology.IsQuotientMap.continuous_lift_prod_right` — Whitehead's
  theorem that a quotient map stays a quotient map after multiplying by a locally compact factor.
* `continuous_of_continuousOn_closedCell` and `continuous_prod_of_continuousOn_closedCell`: the
  two criteria specialised to a complex which is the whole ambient space.

These are stated for an arbitrary complex `C`, not just for `C = univ`, because the skeletal
induction applies them to the skeleta, which are subcomplexes (`Subcomplex.instRelCWComplex`).
The general helpers `continuous_prod_sum` and `continuous_prod_sigma` express that `W × -`
preserves sums and sigma types.

## Transport through a characteristic map

* `cellCylinderRetract`: the disc-cylinder retraction carried through the characteristic map of a
  cell — the value the skeletal retraction is forced to take on that closed cell.
* `cellCylinderRetract_of_norm_one`: on the frontier of the cell it is the identity.  This is what
  makes the cell-by-cell definition agree with the identity on the previous skeleton, hence both
  well defined and continuous.
* `cellCylinderRetract_mem_lShape`: it lands in the L-shaped set.

## Assembling the proof

* `exists_cellAttachmentRetraction`: the cell-attachment step.  If `B ⊆ C` contains the base, every
  closed cell of dimension `≠ m`, and every `m`-cell frontier, and misses every open `m`-cell, then
  `I × C` retracts onto `{0} × C ∪ I × B`.  The retraction is obtained by descending the cellwise
  formula `attachModelMap` along `cellModelProj`, which avoids having to choose, for a point of
  `C`, the open cell containing it: the only nontrivial coincidences happen on cell frontiers,
  where `cellCylinderRetract` is the identity.
* `exists_skeletalRetraction`: the same for consecutive skeleta.
* `exists_cylinderRetraction_trans_subset`: retractions compose along `A ⊆ B ⊆ C`, and record that
  the composite restricts to the inner retraction on `I × B` — the coherence needed to pass to the
  limit.
* `skeletonRetractData`: the coherent family of retractions of `I × (m-skeleton)` onto
  `{0} × (m-skeleton) ∪ I × A`, built by recursion, with `skeletonRetractData_agrees_le` recording
  that later stages restrict to earlier ones.
* `hasHomotopyExtensionProperty_of_relativeCWComplex_proved`: **the main theorem.**  Since every
  point of the complex lies in some finite skeleton, the coherent family assembles into a single
  retraction of `I × X`, continuous by `continuous_prod_of_continuousOn_closedCell` because a
  closed `l`-cell already lies in the `(l+1)`-skeleton.  No time reparametrisation is needed: only
  a retraction is required, not a deformation retraction, and the composite of the skeletal
  retractions is already stationary on each cell.
-/

@[expose] public section

noncomputable section

open Metric Set Topology unitInterval

namespace SphereSixComplex

namespace EstablishedGeneralTopology

universe u

/-! ## The radial retraction of the cylinder over a cell -/

/-- The radial scale used by the retraction of `Dⁿ × I` onto `Dⁿ × {0} ∪ ∂Dⁿ × I`: the ray from
`(0, 2)` through `(x, t)` leaves the L-shaped set at parameter `‖x‖⁻¹` or `2/(2 - t)`, whichever
comes first, i.e. at the reciprocal of `discRetractScale`. -/
public def discRetractScale (n : ℕ) (p : (Fin n → ℝ) × I) : ℝ :=
  max ‖p.1‖ ((2 - (p.2 : ℝ)) / 2)

public theorem discRetractScale_half_le (n : ℕ) (p : (Fin n → ℝ) × I) :
    1 / 2 ≤ discRetractScale n p := by
  refine le_trans ?_ (le_max_right _ _)
  have := p.2.2.2
  linarith

public theorem discRetractScale_pos (n : ℕ) (p : (Fin n → ℝ) × I) : 0 < discRetractScale n p :=
  lt_of_lt_of_le (by norm_num) (discRetractScale_half_le n p)

public theorem discRetractScale_ne_zero (n : ℕ) (p : (Fin n → ℝ) × I) :
    discRetractScale n p ≠ 0 :=
  (discRetractScale_pos n p).ne'

public theorem norm_le_discRetractScale (n : ℕ) (p : (Fin n → ℝ) × I) :
    ‖p.1‖ ≤ discRetractScale n p :=
  le_max_left _ _

public theorem discRetractScale_le_one (n : ℕ) (p : (Fin n → ℝ) × I) (hp : ‖p.1‖ ≤ 1) :
    discRetractScale n p ≤ 1 := by
  refine max_le hp ?_
  have := p.2.2.1
  linarith

public theorem continuous_discRetractScale (n : ℕ) : Continuous (discRetractScale n) :=
  (continuous_norm.comp continuous_fst).max
    ((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).div_const 2)

/-- The disc coordinate of the radial retraction of `Dⁿ × I`. -/
public def discRetractFst (n : ℕ) (p : (Fin n → ℝ) × I) : Fin n → ℝ :=
  (discRetractScale n p)⁻¹ • p.1

/-- The cylinder coordinate of the radial retraction of `Dⁿ × I`. -/
public def discRetractSnd (n : ℕ) (p : (Fin n → ℝ) × I) : ℝ :=
  2 - (2 - (p.2 : ℝ)) / discRetractScale n p

public theorem continuous_discRetractFst (n : ℕ) : Continuous (discRetractFst n) :=
  ((continuous_discRetractScale n).inv₀ (discRetractScale_ne_zero n)).smul continuous_fst

public theorem continuous_discRetractSnd (n : ℕ) : Continuous (discRetractSnd n) :=
  continuous_const.sub
    ((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).div
      (continuous_discRetractScale n) (discRetractScale_ne_zero n))

public theorem norm_discRetractFst (n : ℕ) (p : (Fin n → ℝ) × I) :
    ‖discRetractFst n p‖ = ‖p.1‖ / discRetractScale n p := by
  rw [discRetractFst, norm_smul, norm_inv, Real.norm_eq_abs,
    abs_of_pos (discRetractScale_pos n p), div_eq_inv_mul]

public theorem norm_discRetractFst_le_one (n : ℕ) (p : (Fin n → ℝ) × I) :
    ‖discRetractFst n p‖ ≤ 1 := by
  rw [norm_discRetractFst, div_le_one (discRetractScale_pos n p)]
  exact norm_le_discRetractScale n p

public theorem discRetractSnd_nonneg (n : ℕ) (p : (Fin n → ℝ) × I) : 0 ≤ discRetractSnd n p := by
  have hu := discRetractScale_pos n p
  have hle : (2 - (p.2 : ℝ)) / 2 ≤ discRetractScale n p := le_max_right _ _
  have hkey : (2 - (p.2 : ℝ)) / discRetractScale n p ≤ 2 := by
    rw [div_le_iff₀ hu]; linarith
  show 0 ≤ 2 - (2 - (p.2 : ℝ)) / discRetractScale n p
  linarith

public theorem discRetractSnd_le_one (n : ℕ) (p : (Fin n → ℝ) × I) (hp : ‖p.1‖ ≤ 1) :
    discRetractSnd n p ≤ 1 := by
  have hu := discRetractScale_pos n p
  have hu1 := discRetractScale_le_one n p hp
  have ht := p.2.2.2
  have hkey : 1 ≤ (2 - (p.2 : ℝ)) / discRetractScale n p := by
    rw [le_div_iff₀ hu]; linarith
  show 2 - (2 - (p.2 : ℝ)) / discRetractScale n p ≤ 1
  linarith

/-- The retraction lands in the L-shaped subset `Dⁿ × {0} ∪ ∂Dⁿ × I`. -/
public theorem discRetract_mem_lShape (n : ℕ) (p : (Fin n → ℝ) × I) :
    ‖discRetractFst n p‖ = 1 ∨ discRetractSnd n p = 0 := by
  rcases max_cases ‖p.1‖ ((2 - (p.2 : ℝ)) / 2) with ⟨hu, -⟩ | ⟨hu, -⟩
  · left
    have hu' : discRetractScale n p = ‖p.1‖ := hu
    have hne : ‖p.1‖ ≠ 0 := hu' ▸ discRetractScale_ne_zero n p
    rw [norm_discRetractFst, hu', div_self hne]
  · right
    have hu' : discRetractScale n p = (2 - (p.2 : ℝ)) / 2 := hu
    have h2 : (2 : ℝ) - (p.2 : ℝ) ≠ 0 := by
      have ht := p.2.2.2; intro hcon; linarith
    have hdiv : (2 - (p.2 : ℝ)) / ((2 - (p.2 : ℝ)) / 2) = 2 := by field_simp
    show 2 - (2 - (p.2 : ℝ)) / discRetractScale n p = 0
    rw [hu', hdiv]
    norm_num

/-- The retraction fixes the bottom `Dⁿ × {0}` of the cylinder. -/
public theorem discRetract_bottom (n : ℕ) (p : (Fin n → ℝ) × I) (hp : ‖p.1‖ ≤ 1)
    (ht : (p.2 : ℝ) = 0) : discRetractFst n p = p.1 ∧ discRetractSnd n p = 0 := by
  have hu : discRetractScale n p = 1 := by
    rw [discRetractScale, ht]; norm_num; exact hp
  refine ⟨?_, ?_⟩
  · rw [discRetractFst, hu, inv_one, one_smul]
  · rw [discRetractSnd, hu, ht]; norm_num

/-- The retraction fixes the side `∂Dⁿ × I` of the cylinder. -/
public theorem discRetract_side (n : ℕ) (p : (Fin n → ℝ) × I) (hp : ‖p.1‖ = 1) :
    discRetractFst n p = p.1 ∧ discRetractSnd n p = (p.2 : ℝ) := by
  have hu : discRetractScale n p = 1 := by
    rw [discRetractScale, hp]
    refine max_eq_left ?_
    have := p.2.2.1; linarith
  refine ⟨?_, ?_⟩
  · rw [discRetractFst, hu, inv_one, one_smul]
  · rw [discRetractSnd, hu]; norm_num

/-- Every point of the closed unit ball of `Fin n → ℝ` has norm at most one. -/
public theorem norm_le_one_of_mem_closedBall {n : ℕ}
    (y : ↥(closedBall (0 : Fin n → ℝ) 1)) : ‖(y : Fin n → ℝ)‖ ≤ 1 := by
  simpa using mem_closedBall_zero_iff.mp y.2

/-- **The disc-cylinder retraction.**  The cylinder `Dⁿ × I` over the closed unit ball of
`Fin n → ℝ` (in the sup metric, i.e. a cube — this is Mathlib's model for a CW cell) retracts onto
the union of its bottom `Dⁿ × {0}` with its side `∂Dⁿ × I`.  The retraction is radial projection
from the point `(0, 2)` lying above the cylinder.  Source: Hatcher, *Algebraic Topology*, p. 15.

This is a named definition rather than an existence statement because the skeletal induction has to
transport it through the characteristic maps of cells, which needs its formula, not just its
existence. -/
public def discCylinderRetraction (n : ℕ) :
    C(↥(closedBall (0 : Fin n → ℝ) 1) × I, ↥(closedBall (0 : Fin n → ℝ) 1) × I) where
  toFun p :=
    (⟨discRetractFst n ((p.1 : Fin n → ℝ), p.2),
        mem_closedBall_zero_iff.mpr (norm_discRetractFst_le_one n _)⟩,
      ⟨discRetractSnd n ((p.1 : Fin n → ℝ), p.2), discRetractSnd_nonneg n _,
        discRetractSnd_le_one n _ (norm_le_one_of_mem_closedBall p.1)⟩)
  continuous_toFun := by
    have hemb : Continuous fun p : ↥(closedBall (0 : Fin n → ℝ) 1) × I ↦
        (((p.1 : Fin n → ℝ)), p.2) :=
      (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
    exact (((continuous_discRetractFst n).comp hemb).subtype_mk _).prodMk
      (((continuous_discRetractSnd n).comp hemb).subtype_mk _)

@[simp]
public theorem discCylinderRetraction_fst_coe (n : ℕ)
    (p : ↥(closedBall (0 : Fin n → ℝ) 1) × I) :
    ((discCylinderRetraction n p).1 : Fin n → ℝ) =
      discRetractFst n ((p.1 : Fin n → ℝ), p.2) :=
  rfl

@[simp]
public theorem discCylinderRetraction_snd_coe (n : ℕ)
    (p : ↥(closedBall (0 : Fin n → ℝ) 1) × I) :
    ((discCylinderRetraction n p).2 : ℝ) = discRetractSnd n ((p.1 : Fin n → ℝ), p.2) :=
  rfl

/-- The retraction lands in the bottom-and-sides of the cylinder. -/
public theorem discCylinderRetraction_mem_lShape (n : ℕ)
    (p : ↥(closedBall (0 : Fin n → ℝ) 1) × I) :
    ‖((discCylinderRetraction n p).1 : Fin n → ℝ)‖ = 1 ∨
      ((discCylinderRetraction n p).2 : ℝ) = 0 :=
  discRetract_mem_lShape n _

/-- The retraction fixes the bottom-and-sides of the cylinder. -/
public theorem discCylinderRetraction_fix (n : ℕ) (p : ↥(closedBall (0 : Fin n → ℝ) 1) × I)
    (hp : ‖((p.1 : Fin n → ℝ))‖ = 1 ∨ ((p.2 : ℝ)) = 0) : discCylinderRetraction n p = p := by
  rcases hp with hp | hp
  · obtain ⟨h1, h2⟩ := discRetract_side n ((p.1 : Fin n → ℝ), p.2) hp
    exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
  · obtain ⟨h1, h2⟩ :=
      discRetract_bottom n ((p.1 : Fin n → ℝ), p.2) (norm_le_one_of_mem_closedBall p.1) hp
    exact Prod.ext (Subtype.ext h1) (Subtype.ext (h2.trans hp.symm))

/-- In particular the retraction is the identity on the side `∂Dⁿ × I`.  This is exactly what makes
the cell-by-cell definition of the skeletal retraction match the identity on the cell frontier. -/
public theorem discCylinderRetraction_of_norm_one (n : ℕ)
    (p : ↥(closedBall (0 : Fin n → ℝ) 1) × I) (hp : ‖((p.1 : Fin n → ℝ))‖ = 1) :
    discCylinderRetraction n p = p :=
  discCylinderRetraction_fix n p (Or.inl hp)

/-- Existence form of the disc-cylinder retraction. -/
public theorem exists_discCylinderRetraction (n : ℕ) :
    ∃ r : C((closedBall (0 : Fin n → ℝ) 1) × I, (closedBall (0 : Fin n → ℝ) 1) × I),
      (∀ p, ‖((r p).1 : Fin n → ℝ)‖ = 1 ∨ ((r p).2 : ℝ) = 0) ∧
      (∀ p, (‖((p.1 : Fin n → ℝ))‖ = 1 ∨ ((p.2 : ℝ)) = 0) → r p = p) :=
  ⟨discCylinderRetraction n, discCylinderRetraction_mem_lShape n, discCylinderRetraction_fix n⟩

/-! ## Continuity out of a product with a sum or a sigma type -/

/-- A map out of `W × (S ⊕ T)` is continuous as soon as its two restrictions are. -/
public theorem continuous_prod_sum {W S T Y : Type*} [TopologicalSpace W] [TopologicalSpace S]
    [TopologicalSpace T] [TopologicalSpace Y] {g : W × (S ⊕ T) → Y}
    (h₁ : Continuous fun p : W × S ↦ g (p.1, Sum.inl p.2))
    (h₂ : Continuous fun p : W × T ↦ g (p.1, Sum.inr p.2)) : Continuous g := by
  let e : W × (S ⊕ T) ≃ₜ (S × W) ⊕ (T × W) :=
    (Homeomorph.prodComm W (S ⊕ T)).trans Homeomorph.sumProdDistrib
  rw [← e.symm.comp_continuous_iff']
  refine continuous_sum_dom.mpr ⟨?_, ?_⟩
  · exact h₁.comp continuous_swap
  · exact h₂.comp continuous_swap

/-- A map out of `W × Σ i, F i` is continuous as soon as all its restrictions are. -/
public theorem continuous_prod_sigma {W Y : Type*} {ι : Type*} {F : ι → Type*}
    [TopologicalSpace W] [TopologicalSpace Y] [∀ i, TopologicalSpace (F i)]
    {g : W × (Σ i, F i) → Y}
    (h : ∀ i, Continuous fun p : W × F i ↦ g (p.1, ⟨i, p.2⟩)) : Continuous g := by
  let e : W × (Σ i, F i) ≃ₜ Σ i, F i × W :=
    (Homeomorph.prodComm W (Σ i, F i)).trans Homeomorph.sigmaProdDistrib
  rw [← e.symm.comp_continuous_iff', continuous_sigma_iff]
  intro i
  exact (h i).comp continuous_swap

/-! ## Composing cylinder retractions along a filtration -/

/-- **Cylinder retractions compose.**  If `I × X` retracts onto `{0} × X ∪ I × B` and, one step
further down, `I × B` retracts onto `{0} × B ∪ I × A`, then `I × X` retracts onto
`{0} × X ∪ I × A`.  This is the step that assembles the successive skeletal retractions in the
proof that a relative CW pair is a cofibration. -/
public theorem exists_cylinderRetraction_trans {X : Type u} [TopologicalSpace X] {A B : Set X}
    (hAB : A ⊆ B) (hB : IsClosed B)
    (r₁ : C(I × X, I × X))
    (h₁mem : ∀ p : I × X, (r₁ p).1 = 0 ∨ (r₁ p).2 ∈ B)
    (h₁fix : ∀ p : I × X, p.1 = 0 ∨ p.2 ∈ B → r₁ p = p)
    (r₂ : C(I × ↥B, I × ↥B))
    (h₂mem : ∀ q : I × ↥B, (r₂ q).1 = 0 ∨ ((r₂ q).2 : X) ∈ A)
    (h₂fix : ∀ q : I × ↥B, q.1 = 0 ∨ ((q.2 : X)) ∈ A → r₂ q = q) :
    ∃ r : C(I × X, I × X),
      (∀ p : I × X, (r p).1 = 0 ∨ (r p).2 ∈ A) ∧
      (∀ p : I × X, p.1 = 0 ∨ p.2 ∈ A → r p = p) := by
  classical
  set ι : I × ↥B → I × X := fun z ↦ (z.1, (z.2 : X)) with hι
  have hιcont : Continuous ι := continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  set G : I × X → I × X :=
    fun q ↦ if hq : q.2 ∈ B then ι (r₂ (q.1, ⟨q.2, hq⟩)) else q with hG
  have hGB : ∀ (q : I × X) (hq : q.2 ∈ B), G q = ι (r₂ (q.1, ⟨q.2, hq⟩)) := by
    intro q hq
    simp only [hG, hq, ↓reduceDIte]
  have hGnotB : ∀ q : I × X, q.2 ∉ B → G q = q := by
    intro q hq
    simp only [hG, hq, ↓reduceDIte]
  set S₀ : Set (I × X) := {q | q.1 = 0} with hS₀
  set SB : Set (I × X) := {q | q.2 ∈ B} with hSB
  have hGcontB : ContinuousOn G SB := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hcont : Continuous fun q : SB ↦ ((q : I × X).1, (⟨(q : I × X).2, q.2⟩ : ↥B)) :=
      (continuous_fst.comp continuous_subtype_val).prodMk
        ((continuous_snd.comp continuous_subtype_val).subtype_mk _)
    refine ((hιcont.comp r₂.continuous).comp hcont).congr ?_
    intro q
    exact (hGB (q : I × X) q.2).symm
  have hGcont₀ : ContinuousOn G S₀ := by
    rw [continuousOn_iff_continuous_domRestrict]
    refine continuous_subtype_val.congr ?_
    intro q
    have hq0 : (q : I × X).1 = 0 := q.2
    show ((q : I × X)) = G (q : I × X)
    by_cases hq : (q : I × X).2 ∈ B
    · rw [hGB _ hq, h₂fix _ (Or.inl hq0)]
    · rw [hGnotB _ hq]
  have hGcont : ContinuousOn G (S₀ ∪ SB) :=
    hGcont₀.union_of_isClosed hGcontB (isClosed_singleton.preimage continuous_fst)
      (hB.preimage continuous_snd)
  have hmaps : ∀ p : I × X, r₁ p ∈ S₀ ∪ SB := by
    intro p
    rcases h₁mem p with hp | hp
    · exact Or.inl hp
    · exact Or.inr hp
  refine ⟨⟨G ∘ r₁, hGcont.comp_continuous r₁.continuous hmaps⟩, ?_, ?_⟩
  · intro p
    show (G (r₁ p)).1 = 0 ∨ (G (r₁ p)).2 ∈ A
    by_cases hp : (r₁ p).2 ∈ B
    · rw [hGB _ hp]
      exact h₂mem ((r₁ p).1, ⟨(r₁ p).2, hp⟩)
    · rw [hGnotB _ hp]
      exact Or.inl ((h₁mem p).resolve_right hp)
  · intro p hp
    have hpB : p.1 = 0 ∨ p.2 ∈ B := hp.imp id (fun h ↦ hAB h)
    show G (r₁ p) = p
    rw [h₁fix p hpB]
    by_cases hq : p.2 ∈ B
    · rw [hGB _ hq, h₂fix _ (hp.imp id id)]
    · rw [hGnotB _ hq]

/-! ## The weak topology of a relative CW complex -/

section WeakTopology

variable {X : Type u} [TopologicalSpace X]

/-- The disjoint union of all closed cells of a relative CW complex with its base. -/
public abbrev cellModel (C A : Set X) [RelCWComplex C A] : Type u :=
  (Σ i : (Σ n, RelCWComplex.cell C n), ↥(closedBall (0 : Fin i.1 → ℝ) 1)) ⊕ ↥A

/-- A point of a closed cell, viewed as a point of the complex. -/
public def cellPoint (C A : Set X) [RelCWComplex C A] {n : ℕ} (j : RelCWComplex.cell C n)
    (y : ↥(closedBall (0 : Fin n → ℝ) 1)) : ↥C :=
  ⟨RelCWComplex.map n j (y : Fin n → ℝ),
    RelCWComplex.closedCell_subset_complex n j ⟨(y : Fin n → ℝ), y.2, rfl⟩⟩

@[simp]
public theorem cellPoint_coe (C A : Set X) [RelCWComplex C A] {n : ℕ}
    (j : RelCWComplex.cell C n) (y : ↥(closedBall (0 : Fin n → ℝ) 1)) :
    (cellPoint C A j y : X) = RelCWComplex.map n j (y : Fin n → ℝ) :=
  rfl

/-- A point of the base, viewed as a point of the complex. -/
public def basePoint (C A : Set X) [RelCWComplex C A] (a : ↥A) : ↥C :=
  ⟨(a : X), RelCWComplex.base_subset_complex a.2⟩

@[simp]
public theorem basePoint_coe (C A : Set X) [RelCWComplex C A] (a : ↥A) :
    (basePoint C A a : X) = (a : X) :=
  rfl

public theorem continuous_cellPoint (C A : Set X) [RelCWComplex C A] {n : ℕ}
    (j : RelCWComplex.cell C n) : Continuous (cellPoint C A j) :=
  ((RelCWComplex.continuousOn (C := C) n j).domRestrict).subtype_mk _

public theorem continuous_basePoint (C A : Set X) [RelCWComplex C A] :
    Continuous (basePoint C A) :=
  continuous_subtype_val.subtype_mk _

/-- The tautological map onto the complex from the disjoint union of its closed cells with its
base: the characteristic map on each cell, the inclusion on the base. -/
public def cellModelProj (C A : Set X) [RelCWComplex C A] : cellModel C A → ↥C :=
  Sum.elim (fun z ↦ cellPoint C A z.1.2 z.2) (basePoint C A)

public theorem continuous_cellModelProj (C A : Set X) [RelCWComplex C A] :
    Continuous (cellModelProj C A) := by
  refine continuous_sum_dom.mpr ⟨?_, continuous_basePoint C A⟩
  rw [show (cellModelProj C A ∘ Sum.inl) = fun z : (Σ i : (Σ n, RelCWComplex.cell C n),
      ↥(closedBall (0 : Fin i.1 → ℝ) 1)) ↦ cellPoint C A z.1.2 z.2 from rfl,
    continuous_sigma_iff]
  intro i
  exact continuous_cellPoint C A i.2

public theorem surjective_cellModelProj (C A : Set X) [RelCWComplex C A] :
    Function.Surjective (cellModelProj C A) := by
  rintro ⟨x, hx⟩
  rw [← RelCWComplex.union (C := C) (D := A)] at hx
  rcases hx with hxA | hxc
  · exact ⟨Sum.inr ⟨x, hxA⟩, rfl⟩
  · simp only [mem_iUnion] at hxc
    obtain ⟨n, j, y, hy, hxy⟩ := hxc
    exact ⟨Sum.inl ⟨⟨n, j⟩, ⟨y, hy⟩⟩, Subtype.ext hxy⟩

/-- **The weak topology of a relative CW complex, as a quotient map.**  The tautological map onto
the complex from the disjoint union of its closed cells with its base is a quotient map.  This is
the form of the weak-topology axiom `RelCWComplex.closed'` that composes with Whitehead's theorem
on products with a locally compact factor.  Hausdorffness is genuinely used: it is what makes the
compact image of a closed subset of a closed cell a closed subset of the complex. -/
public theorem isQuotientMap_cellModelProj [T2Space X] (C A : Set X) [RelCWComplex C A] :
    Topology.IsQuotientMap (cellModelProj C A) := by
  refine Topology.isQuotientMap_iff_isClosed.mpr ⟨surjective_cellModelProj C A, fun S ↦ ⟨?_, ?_⟩⟩
  · exact fun hS ↦ hS.preimage (continuous_cellModelProj C A)
  · intro hS
    have himg : IsClosed (Subtype.val '' S) := by
      refine (RelCWComplex.closed C (D := A) (Subtype.val '' S) ?_).mpr ⟨?_, ?_⟩
      · rintro _ ⟨a, -, rfl⟩
        exact a.2
      · intro n j
        have : CompactSpace ↥(closedBall (0 : Fin n → ℝ) 1) :=
          isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
        have hK : IsClosed {y : ↥(closedBall (0 : Fin n → ℝ) 1) | cellPoint C A j y ∈ S} :=
          hS.preimage (f := fun y : ↥(closedBall (0 : Fin n → ℝ) 1) ↦
              (Sum.inl ⟨⟨n, j⟩, y⟩ : cellModel C A))
            (continuous_inl.comp continuous_sigmaMk)
        have heq : (fun y : ↥(closedBall (0 : Fin n → ℝ) 1) ↦ (cellPoint C A j y : X)) ''
            {y | cellPoint C A j y ∈ S} =
              Subtype.val '' S ∩ RelCWComplex.closedCell n j := by
          ext x
          constructor
          · rintro ⟨y, hy, rfl⟩
            exact ⟨⟨cellPoint C A j y, hy, rfl⟩, ⟨(y : Fin n → ℝ), y.2, rfl⟩⟩
          · rintro ⟨⟨s, hs, rfl⟩, y, hy, hxy⟩
            refine ⟨⟨y, hy⟩, ?_, hxy⟩
            show cellPoint C A j ⟨y, hy⟩ ∈ S
            rw [show cellPoint C A j ⟨y, hy⟩ = s from Subtype.ext hxy]
            exact hs
        rw [← heq]
        exact (hK.isCompact.image
          (continuous_subtype_val.comp (continuous_cellPoint C A j))).isClosed
      · have hA : IsClosed A := RelCWComplex.isClosedBase C
        have hK : IsClosed {a : ↥A | basePoint C A a ∈ S} :=
          hS.preimage (f := fun a : ↥A ↦ (Sum.inr a : cellModel C A)) continuous_inr
        have heq : Subtype.val '' {a : ↥A | basePoint C A a ∈ S} = Subtype.val '' S ∩ A := by
          ext x
          constructor
          · rintro ⟨a, ha, rfl⟩
            exact ⟨⟨basePoint C A a, ha, rfl⟩, a.2⟩
          · rintro ⟨⟨s, hs, rfl⟩, hxA⟩
            refine ⟨⟨(s : X), hxA⟩, ?_, rfl⟩
            show basePoint C A ⟨(s : X), hxA⟩ ∈ S
            rw [show basePoint C A ⟨(s : X), hxA⟩ = s from Subtype.ext rfl]
            exact hs
        rw [← heq]
        exact hA.isClosedEmbedding_subtypeVal.isClosedMap _ hK
    rw [← preimage_image_eq S Subtype.val_injective]
    exact himg.preimage continuous_subtype_val

/-- **Continuity criterion out of a relative CW complex.**  A map is continuous as soon as its
composites with the characteristic map of every cell and with the inclusion of the base are. -/
public theorem continuous_of_continuous_cellPoint [T2Space X] (C A : Set X) [RelCWComplex C A]
    {Y : Type*} [TopologicalSpace Y] {F : ↥C → Y}
    (hcell : ∀ (n : ℕ) (j : RelCWComplex.cell C n), Continuous fun y ↦ F (cellPoint C A j y))
    (hbase : Continuous fun a ↦ F (basePoint C A a)) : Continuous F := by
  rw [(isQuotientMap_cellModelProj C A).continuous_iff]
  refine continuous_sum_dom.mpr ⟨?_, hbase⟩
  show Continuous fun z : (Σ i : (Σ n, RelCWComplex.cell C n),
    ↥(closedBall (0 : Fin i.1 → ℝ) 1)) ↦ F (cellPoint C A z.1.2 z.2)
  rw [continuous_sigma_iff]
  intro i
  exact hcell i.1 i.2

/-- **Continuity criterion out of the cylinder over a relative CW complex.**  This is the product
form of the weak topology: Whitehead's theorem that a quotient map stays a quotient map after
multiplying by a locally compact space, applied to the compact interval. -/
public theorem continuous_prod_of_continuous_cellPoint [T2Space X] (C A : Set X)
    [RelCWComplex C A] {Y : Type*} [TopologicalSpace Y] {G : I × ↥C → Y}
    (hcell : ∀ (n : ℕ) (j : RelCWComplex.cell C n),
      Continuous fun p : I × ↥(closedBall (0 : Fin n → ℝ) 1) ↦ G (p.1, cellPoint C A j p.2))
    (hbase : Continuous fun p : I × ↥A ↦ G (p.1, basePoint C A p.2)) : Continuous G := by
  refine (isQuotientMap_cellModelProj C A).continuous_lift_prod_right ?_
  refine continuous_prod_sum ?_ hbase
  exact continuous_prod_sigma fun i ↦ hcell i.1 i.2

/-! ### The absolute case -/

/-- The continuity criterion for a complex which is the whole ambient space. -/
public theorem continuous_of_continuousOn_closedCell [T2Space X] {A : Set X}
    [RelCWComplex (univ : Set X) A] {Y : Type*} [TopologicalSpace Y] {F : X → Y}
    (hcell : ∀ (n : ℕ) (j : RelCWComplex.cell (univ : Set X) n),
      ContinuousOn F (RelCWComplex.closedCell n j))
    (hbase : ContinuousOn F A) : Continuous F := by
  have hF : Continuous fun x : ↥(univ : Set X) ↦ F (x : X) := by
    refine continuous_of_continuous_cellPoint (univ : Set X) A ?_ ?_
    · intro n j
      exact (hcell n j).comp_continuous
        ((RelCWComplex.continuousOn (C := (univ : Set X)) n j).domRestrict)
        fun y ↦ ⟨(y : Fin n → ℝ), y.2, rfl⟩
    · exact hbase.comp_continuous continuous_subtype_val fun a ↦ a.2
  have hmk : Continuous fun x : X ↦ (⟨x, mem_univ x⟩ : ↥(univ : Set X)) :=
    continuous_id.subtype_mk _
  exact hF.comp hmk

/-- The cylinder continuity criterion for a complex which is the whole ambient space. -/
public theorem continuous_prod_of_continuousOn_closedCell [T2Space X] {A : Set X}
    [RelCWComplex (univ : Set X) A] {Y : Type*} [TopologicalSpace Y] {G : I × X → Y}
    (hcell : ∀ (n : ℕ) (j : RelCWComplex.cell (univ : Set X) n),
      Continuous fun p : I × ↥(closedBall (0 : Fin n → ℝ) 1) ↦
        G (p.1, RelCWComplex.map (C := (univ : Set X)) n j (p.2 : Fin n → ℝ)))
    (hbase : Continuous fun p : I × ↥A ↦ G (p.1, (p.2 : X))) : Continuous G := by
  have hG : Continuous fun p : I × ↥(univ : Set X) ↦ G (p.1, (p.2 : X)) :=
    continuous_prod_of_continuous_cellPoint (univ : Set X) A hcell hbase
  have hmk : Continuous fun p : I × X ↦ (p.1, (⟨p.2, mem_univ p.2⟩ : ↥(univ : Set X))) :=
    continuous_fst.prodMk (continuous_snd.subtype_mk _)
  exact hG.comp hmk

end WeakTopology

/-! ## Transporting the disc retraction through a characteristic map -/

section CellTransport

variable {X : Type u} [TopologicalSpace X]

/-- The disc-cylinder retraction carried through the characteristic map of a cell.  This is the
value the skeletal retraction is forced to take on the closed cell `(n, j)`. -/
public def cellCylinderRetract (C A : Set X) [RelCWComplex C A] {n : ℕ}
    (j : RelCWComplex.cell C n) (p : I × ↥(closedBall (0 : Fin n → ℝ) 1)) : I × ↥C :=
  ((discCylinderRetraction n (p.2, p.1)).2,
    cellPoint C A j (discCylinderRetraction n (p.2, p.1)).1)

public theorem continuous_cellCylinderRetract (C A : Set X) [RelCWComplex C A] {n : ℕ}
    (j : RelCWComplex.cell C n) : Continuous (cellCylinderRetract C A j) := by
  have h : Continuous fun p : I × ↥(closedBall (0 : Fin n → ℝ) 1) ↦
      discCylinderRetraction n (p.2, p.1) :=
    (discCylinderRetraction n).continuous.comp (continuous_snd.prodMk continuous_fst)
  exact (continuous_snd.comp h).prodMk ((continuous_cellPoint C A j).comp (continuous_fst.comp h))

/-- On the frontier of the cell the transported retraction is the identity.  This is what makes the
cell-by-cell definition of the skeletal retraction agree with the identity on the lower skeleton,
and hence both well defined and continuous. -/
public theorem cellCylinderRetract_of_norm_one (C A : Set X) [RelCWComplex C A] {n : ℕ}
    (j : RelCWComplex.cell C n) (p : I × ↥(closedBall (0 : Fin n → ℝ) 1))
    (hp : ‖((p.2 : Fin n → ℝ))‖ = 1) :
    cellCylinderRetract C A j p = (p.1, cellPoint C A j p.2) := by
  rw [cellCylinderRetract, discCylinderRetraction_of_norm_one n (p.2, p.1) hp]

/-- The transported retraction lands in the L-shaped set: either the time coordinate has been
pushed down to `0`, or the disc coordinate has been pushed out to the frontier of the cell, which
lies in the previous skeleton. -/
public theorem cellCylinderRetract_mem_lShape (C A : Set X) [RelCWComplex C A] {n : ℕ}
    (j : RelCWComplex.cell C n) (p : I × ↥(closedBall (0 : Fin n → ℝ) 1)) :
    ((cellCylinderRetract C A j p).1 : ℝ) = 0 ∨
      ((cellCylinderRetract C A j p).2 : X) ∈ RelCWComplex.cellFrontier n j := by
  rcases discCylinderRetraction_mem_lShape n (p.2, p.1) with h | h
  · exact Or.inr ⟨((discCylinderRetraction n (p.2, p.1)).1 : Fin n → ℝ),
      mem_sphere_zero_iff_norm.mpr h, rfl⟩
  · exact Or.inl h

/-- At time `0` the transported retraction is the identity. -/
public theorem cellCylinderRetract_zero (C A : Set X) [RelCWComplex C A] {n : ℕ}
    (j : RelCWComplex.cell C n) (y : ↥(closedBall (0 : Fin n → ℝ) 1)) :
    cellCylinderRetract C A j (0, y) = (0, cellPoint C A j y) := by
  rw [cellCylinderRetract, discCylinderRetraction_fix n (y, (0 : I)) (Or.inr rfl)]

/-- The cellwise formula for the cell-attachment retraction, written on the disjoint union of the
closed cells with the base: `cellCylinderRetract` on the cells of the attaching dimension `m`, the
identity on every other cell and on the base. -/
public def attachModelMap (C A : Set X) [RelCWComplex C A] (m : ℕ)
    (q : I × cellModel C A) : I × ↥C :=
  Sum.elim
    (fun z : (Σ i : (Σ l, RelCWComplex.cell C l), ↥(closedBall (0 : Fin i.1 → ℝ) 1)) ↦
      if z.1.1 = m then cellCylinderRetract C A z.1.2 (q.1, z.2)
      else (q.1, cellPoint C A z.1.2 z.2))
    (fun a ↦ (q.1, basePoint C A a)) q.2

public theorem attachModelMap_inl (C A : Set X) [RelCWComplex C A] (m : ℕ) (t : I) {l : ℕ}
    (j : RelCWComplex.cell C l) (y : ↥(closedBall (0 : Fin l → ℝ) 1)) :
    attachModelMap C A m (t, Sum.inl ⟨⟨l, j⟩, y⟩) =
      if l = m then cellCylinderRetract C A j (t, y) else (t, cellPoint C A j y) :=
  rfl

public theorem attachModelMap_inr (C A : Set X) [RelCWComplex C A] (m : ℕ) (t : I) (a : ↥A) :
    attachModelMap C A m (t, Sum.inr a) = (t, basePoint C A a) :=
  rfl

public theorem attachModelMap_inl_self (C A : Set X) [RelCWComplex C A] (m : ℕ) (t : I)
    (j : RelCWComplex.cell C m) (y : ↥(closedBall (0 : Fin m → ℝ) 1)) :
    attachModelMap C A m (t, Sum.inl ⟨⟨m, j⟩, y⟩) = cellCylinderRetract C A j (t, y) := by
  rw [attachModelMap_inl]
  simp

public theorem attachModelMap_inl_of_ne (C A : Set X) [RelCWComplex C A] (m : ℕ) (t : I) {l : ℕ}
    (hl : l ≠ m) (j : RelCWComplex.cell C l) (y : ↥(closedBall (0 : Fin l → ℝ) 1)) :
    attachModelMap C A m (t, Sum.inl ⟨⟨l, j⟩, y⟩) = (t, cellPoint C A j y) := by
  rw [attachModelMap_inl]
  simp [hl]

end CellTransport

/-! ## Attaching a family of cells -/

section CellAttachment

variable {X : Type u} [TopologicalSpace X] [T2Space X]

/-- **The cell-attachment step.**  Let `B` be a subset of a relative CW complex `C` which contains
the base, contains every closed cell of dimension other than `m`, contains the frontier of every
`m`-cell, and misses every open `m`-cell.  Then `I × C` retracts onto `{0} × C ∪ I × B`.

Applied with `C = skeletonLT _ (m+1)` and `B = skeletonLT _ m` this is the skeletal step of the
proof that a relative CW pair is a cofibration.  The retraction is `cellCylinderRetract` on the
`m`-cells and the identity everywhere else.  It is well defined because the only way a point of
`C` can be written as a point of a cell in two different ways, other than trivially, is on a cell
frontier — and there `cellCylinderRetract` is the identity (`cellCylinderRetract_of_norm_one`).
The map is therefore obtained by descending the cellwise formula `attachModelMap` along the
quotient map `cellModelProj`, which avoids having to choose, for a point of `C`, the open cell
containing it. -/
public theorem exists_cellAttachmentRetraction (C A B : Set X) [RelCWComplex C A] (m : ℕ)
    (hAB : A ⊆ B)
    (hlow : ∀ (l : ℕ) (j : RelCWComplex.cell C l), l ≠ m → RelCWComplex.closedCell l j ⊆ B)
    (hfront : ∀ j : RelCWComplex.cell C m, RelCWComplex.cellFrontier m j ⊆ B)
    (hdisj : ∀ j : RelCWComplex.cell C m, Disjoint (RelCWComplex.openCell m j) B) :
    ∃ ρ : C(I × ↥C, I × ↥C),
      (∀ q, (ρ q).1 = 0 ∨ ((ρ q).2 : X) ∈ B) ∧
      (∀ q, q.1 = 0 ∨ ((q.2 : X)) ∈ B → ρ q = q) := by
  classical
  -- On the part of the model that lands in `B`, the formula is the identity.
  have hGB : ∀ (t : I) (p : cellModel C A), ((cellModelProj C A p : X)) ∈ B →
      attachModelMap C A m (t, p) = (t, cellModelProj C A p) := by
    rintro t (⟨⟨l, j⟩, y⟩ | a) hp
    · by_cases hl : l = m
      · subst hl
        rw [attachModelMap_inl_self]
        refine cellCylinderRetract_of_norm_one C A j (t, y) ?_
        by_contra hy
        have hlt : ‖(y : Fin l → ℝ)‖ < 1 := lt_of_le_of_ne (norm_le_one_of_mem_closedBall y) hy
        exact (hdisj j).notMem_of_mem_left
          (⟨(y : Fin l → ℝ), mem_ball_zero_iff.mpr hlt, rfl⟩ :
            ((cellPoint C A j y : X)) ∈ RelCWComplex.openCell l j) hp
      · rw [attachModelMap_inl_of_ne C A m t hl]
        rfl
    · rfl
  -- Off `B`, the point necessarily comes from an `m`-cell.
  have hGnotB : ∀ (t : I) (p : cellModel C A), ((cellModelProj C A p : X)) ∉ B →
      ∃ (j : RelCWComplex.cell C m) (y : ↥(closedBall (0 : Fin m → ℝ) 1)),
        cellPoint C A j y = cellModelProj C A p ∧
          attachModelMap C A m (t, p) = cellCylinderRetract C A j (t, y) := by
    rintro t (⟨⟨l, j⟩, y⟩ | a) hp
    · by_cases hl : l = m
      · subst hl
        exact ⟨j, y, rfl, attachModelMap_inl_self C A l t j y⟩
      · exact absurd (hlow l j hl ⟨(y : Fin l → ℝ), y.2, rfl⟩) hp
    · exact absurd (hAB a.2) hp
  -- The formula is constant on the fibres of `cellModelProj`.
  have hcompat : ∀ (t : I) (p q : cellModel C A), cellModelProj C A p = cellModelProj C A q →
      attachModelMap C A m (t, p) = attachModelMap C A m (t, q) := by
    intro t p q hpq
    by_cases hB : ((cellModelProj C A p : X)) ∈ B
    · rw [hGB t p hB, hGB t q (by rwa [← hpq]), hpq]
    · obtain ⟨j, y, hy, hGp⟩ := hGnotB t p hB
      obtain ⟨j', y', hy', hGq⟩ := hGnotB t q (by rwa [← hpq])
      have hnorm : ∀ (i : RelCWComplex.cell C m) (z : ↥(closedBall (0 : Fin m → ℝ) 1)),
          cellPoint C A i z = cellModelProj C A p → ‖(z : Fin m → ℝ)‖ < 1 := by
        intro i z hz
        refine lt_of_le_of_ne (norm_le_one_of_mem_closedBall z) ?_
        intro h1
        have hmem : ((cellPoint C A i z : X)) ∈ B :=
          hfront i ⟨(z : Fin m → ℝ), mem_sphere_zero_iff_norm.mpr h1, rfl⟩
        rw [hz] at hmem
        exact hB hmem
      have hylt := hnorm j y hy
      have hy'lt := hnorm j' y' (hy'.trans hpq.symm)
      have hjj : j = j' := by
        by_contra hne
        have h1 : ((cellModelProj C A p : X)) ∈ RelCWComplex.openCell m j := by
          rw [← hy]
          exact ⟨(y : Fin m → ℝ), mem_ball_zero_iff.mpr hylt, rfl⟩
        have h2 : ((cellModelProj C A p : X)) ∈ RelCWComplex.openCell m j' := by
          rw [hpq, ← hy']
          exact ⟨(y' : Fin m → ℝ), mem_ball_zero_iff.mpr hy'lt, rfl⟩
        exact (RelCWComplex.disjoint_openCell_of_ne (by simpa using hne)).notMem_of_mem_left h1 h2
      subst hjj
      have hyy : (y : Fin m → ℝ) = (y' : Fin m → ℝ) := by
        refine (RelCWComplex.map (C := C) m j).injOn ?_ ?_ ?_
        · rw [RelCWComplex.source_eq]; exact mem_ball_zero_iff.mpr hylt
        · rw [RelCWComplex.source_eq]; exact mem_ball_zero_iff.mpr hy'lt
        · exact congrArg Subtype.val (hy.trans (hpq.trans hy'.symm))
      rw [hGp, hGq, Subtype.ext hyy]
  -- Descend along the quotient map using any set-theoretic section.
  obtain ⟨s, hs⟩ := (surjective_cellModelProj C A).hasRightInverse
  have hdesc : ∀ (t : I) (p : cellModel C A),
      attachModelMap C A m (t, s (cellModelProj C A p)) = attachModelMap C A m (t, p) :=
    fun t p ↦ hcompat t _ p (hs _)
  refine ⟨⟨fun q ↦ attachModelMap C A m (q.1, s q.2), ?_⟩, ?_, ?_⟩
  · refine continuous_prod_of_continuous_cellPoint C A ?_ ?_
    · intro l j
      by_cases hl : l = m
      · subst hl
        refine (continuous_cellCylinderRetract C A j).congr fun p ↦ ?_
        exact ((hdesc p.1 (Sum.inl ⟨⟨l, j⟩, p.2⟩)).trans
          (attachModelMap_inl_self C A l p.1 j p.2)).symm
      · refine (continuous_fst.prodMk ((continuous_cellPoint C A j).comp continuous_snd)).congr
          fun p ↦ ?_
        exact ((hdesc p.1 (Sum.inl ⟨⟨l, j⟩, p.2⟩)).trans
          (attachModelMap_inl_of_ne C A m p.1 hl j p.2)).symm
    · refine (continuous_fst.prodMk ((continuous_basePoint C A).comp continuous_snd)).congr
        fun p ↦ ?_
      exact ((hdesc p.1 (Sum.inr p.2)).trans (attachModelMap_inr C A m p.1 p.2)).symm
  · intro q
    by_cases hB : ((q.2 : X)) ∈ B
    · refine Or.inr ?_
      show ((attachModelMap C A m (q.1, s q.2)).2 : X) ∈ B
      rw [hGB q.1 (s q.2) (by rwa [hs])]
      show ((cellModelProj C A (s q.2) : X)) ∈ B
      rwa [hs]
    · obtain ⟨j, y, hy, hGq⟩ := hGnotB q.1 (s q.2) (by rwa [hs])
      show (attachModelMap C A m (q.1, s q.2)).1 = 0 ∨
        ((attachModelMap C A m (q.1, s q.2)).2 : X) ∈ B
      rw [hGq]
      rcases cellCylinderRetract_mem_lShape C A j (q.1, y) with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (hfront j h)
  · rintro q (h0 | hB)
    · by_cases hB : ((q.2 : X)) ∈ B
      · show attachModelMap C A m (q.1, s q.2) = q
        rw [hGB q.1 (s q.2) (by rwa [hs]), hs]
      · obtain ⟨j, y, hy, hGq⟩ := hGnotB q.1 (s q.2) (by rwa [hs])
        show attachModelMap C A m (q.1, s q.2) = q
        rw [hGq, h0, cellCylinderRetract_zero, hy, hs]
        exact Prod.ext h0.symm rfl
    · show attachModelMap C A m (q.1, s q.2) = q
      rw [hGB q.1 (s q.2) (by rwa [hs]), hs]

end CellAttachment

/-! ## Composing along a filtration by subspaces -/

/-- **Cylinder retractions compose along a filtration of subspaces of `X`.**  For nested subsets
`A ⊆ B ⊆ C` of `X`, a retraction of `I × C` onto `{0} × C ∪ I × B` and a retraction of `I × B`
onto `{0} × B ∪ I × A` compose to a retraction of `I × C` onto `{0} × C ∪ I × A`.  This is the
form in which the successive skeletal retractions are chained. -/
public theorem exists_cylinderRetraction_trans_subset {X : Type u} [TopologicalSpace X]
    {A B C : Set X} (hAB : A ⊆ B) (hBC : B ⊆ C) (hB : IsClosed B)
    (r₁ : C(I × ↥C, I × ↥C))
    (h₁mem : ∀ q : I × ↥C, (r₁ q).1 = 0 ∨ ((r₁ q).2 : X) ∈ B)
    (h₁fix : ∀ q : I × ↥C, q.1 = 0 ∨ ((q.2 : X)) ∈ B → r₁ q = q)
    (r₂ : C(I × ↥B, I × ↥B))
    (h₂mem : ∀ q : I × ↥B, (r₂ q).1 = 0 ∨ ((r₂ q).2 : X) ∈ A)
    (h₂fix : ∀ q : I × ↥B, q.1 = 0 ∨ ((q.2 : X)) ∈ A → r₂ q = q) :
    ∃ r : C(I × ↥C, I × ↥C),
      (∀ q, (r q).1 = 0 ∨ ((r q).2 : X) ∈ A) ∧
      (∀ q, q.1 = 0 ∨ ((q.2 : X)) ∈ A → r q = q) ∧
      (∀ (q : I × ↥C) (hq : ((q.2 : X)) ∈ B),
        (r q).1 = (r₂ (q.1, ⟨(q.2 : X), hq⟩)).1 ∧
          ((r q).2 : X) = ((r₂ (q.1, ⟨(q.2 : X), hq⟩)).2 : X)) := by
  classical
  set incl : ↥B → ↥C := fun b ↦ ⟨(b : X), hBC b.2⟩ with hincl
  have hinclcont : Continuous incl := continuous_subtype_val.subtype_mk _
  set G : I × ↥C → I × ↥C := fun q ↦
    if hq : ((q.2 : X)) ∈ B then
      ((r₂ (q.1, ⟨(q.2 : X), hq⟩)).1, incl (r₂ (q.1, ⟨(q.2 : X), hq⟩)).2)
    else q with hGdef
  have hGB : ∀ (q : I × ↥C) (hq : ((q.2 : X)) ∈ B),
      G q = ((r₂ (q.1, ⟨(q.2 : X), hq⟩)).1, incl (r₂ (q.1, ⟨(q.2 : X), hq⟩)).2) := by
    intro q hq
    simp only [hGdef, hq, ↓reduceDIte]
  have hGnotB : ∀ q : I × ↥C, ((q.2 : X)) ∉ B → G q = q := by
    intro q hq
    simp only [hGdef, hq, ↓reduceDIte]
  set S₀ : Set (I × ↥C) := {q | q.1 = 0} with hS₀
  set SB : Set (I × ↥C) := {q | ((q.2 : X)) ∈ B} with hSB
  have hSBclosed : IsClosed SB := hB.preimage (continuous_subtype_val.comp continuous_snd)
  have hGcontB : ContinuousOn G SB := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hmap : Continuous fun q : SB ↦ ((q : I × ↥C).1, (⟨((q : I × ↥C).2 : X), q.2⟩ : ↥B)) :=
      (continuous_fst.comp continuous_subtype_val).prodMk
        (((continuous_subtype_val.comp continuous_snd).comp continuous_subtype_val).subtype_mk _)
    refine ((continuous_fst.comp (r₂.continuous.comp hmap)).prodMk
      (hinclcont.comp (continuous_snd.comp (r₂.continuous.comp hmap)))).congr ?_
    intro q
    exact (hGB (q : I × ↥C) q.2).symm
  have hGcont₀ : ContinuousOn G S₀ := by
    rw [continuousOn_iff_continuous_domRestrict]
    refine continuous_subtype_val.congr ?_
    intro q
    have hq0 : (q : I × ↥C).1 = 0 := q.2
    show ((q : I × ↥C)) = G (q : I × ↥C)
    by_cases hq : (((q : I × ↥C).2 : X)) ∈ B
    · rw [hGB _ hq, h₂fix _ (Or.inl hq0)]
    · rw [hGnotB _ hq]
  have hGcont : ContinuousOn G (S₀ ∪ SB) :=
    hGcont₀.union_of_isClosed hGcontB (isClosed_singleton.preimage continuous_fst) hSBclosed
  have hmaps : ∀ q : I × ↥C, r₁ q ∈ S₀ ∪ SB := by
    intro q
    rcases h₁mem q with hq | hq
    · exact Or.inl hq
    · exact Or.inr hq
  refine ⟨⟨G ∘ r₁, hGcont.comp_continuous r₁.continuous hmaps⟩, ?_, ?_, ?_⟩
  · intro q
    show (G (r₁ q)).1 = 0 ∨ ((G (r₁ q)).2 : X) ∈ A
    by_cases hq : (((r₁ q).2 : X)) ∈ B
    · rw [hGB _ hq]
      exact h₂mem ((r₁ q).1, ⟨((r₁ q).2 : X), hq⟩)
    · rw [hGnotB _ hq]
      exact Or.inl ((h₁mem q).resolve_right hq)
  · intro q hq
    have hqB : q.1 = 0 ∨ ((q.2 : X)) ∈ B := hq.imp id fun h ↦ hAB h
    show G (r₁ q) = q
    rw [h₁fix q hqB]
    by_cases hq' : ((q.2 : X)) ∈ B
    · rw [hGB _ hq', h₂fix _ (hq.imp id id)]
    · rw [hGnotB _ hq']
  · intro q hq
    show (G (r₁ q)).1 = _ ∧ ((G (r₁ q)).2 : X) = _
    rw [h₁fix q (Or.inr hq), hGB q hq]
    exact ⟨rfl, rfl⟩

/-! ## The skeletal step -/

/-- **The skeletal step.**  `I × skeletonLT C (m+1)` retracts onto
`{0} × skeletonLT C (m+1) ∪ I × skeletonLT C m`.  This is `exists_cellAttachmentRetraction`
applied to the pair of consecutive skeleta, whose hypotheses are exactly the standard facts that a
closed cell lies in the next skeleton, that a cell frontier lies in the previous one, and that an
open cell misses the previous skeleton. -/
public theorem exists_skeletalRetraction {X : Type u} [TopologicalSpace X] [T2Space X]
    (C A : Set X) [RelCWComplex C A] (m : ℕ) :
    ∃ ρ : C(I × ↥(RelCWComplex.skeletonLT C ((m + 1 : ℕ) : ℕ∞) : Set X),
        I × ↥(RelCWComplex.skeletonLT C ((m + 1 : ℕ) : ℕ∞) : Set X)),
      (∀ q, (ρ q).1 = 0 ∨ ((ρ q).2 : X) ∈ (RelCWComplex.skeletonLT C ((m : ℕ) : ℕ∞) : Set X)) ∧
      (∀ q, q.1 = 0 ∨ ((q.2 : X)) ∈ (RelCWComplex.skeletonLT C ((m : ℕ) : ℕ∞) : Set X) →
        ρ q = q) := by
  refine exists_cellAttachmentRetraction _ A _ m
    (RelCWComplex.Subcomplex.base_subset (RelCWComplex.skeletonLT C m)) ?_ ?_ ?_
  · rintro l ⟨j, hj⟩ hl
    have hj' : (l : ℕ∞) < ((m + 1 : ℕ) : ℕ∞) :=
      (Set.ext_iff.mp (RelCWComplex.skeletonLT_I C ((m + 1 : ℕ) : ℕ∞) l) j).mp hj
    have hlm : ((l : ℕ∞) + 1) ≤ (m : ℕ∞) := by
      have hlt : l < m + 1 := by exact_mod_cast hj'
      have : l + 1 ≤ m := by omega
      exact_mod_cast this
    rw [RelCWComplex.Subcomplex.closedCell_eq]
    exact (RelCWComplex.closedCell_subset_skeletonLT l j).trans
      (SetLike.coe_subset_coe.mpr (RelCWComplex.skeletonLT_mono hlm))
  · rintro ⟨j, hj⟩
    rw [RelCWComplex.Subcomplex.cellFrontier_eq]
    exact RelCWComplex.cellFrontier_subset_skeletonLT m j
  · rintro ⟨j, hj⟩
    rw [RelCWComplex.Subcomplex.openCell_eq]
    exact (RelCWComplex.disjoint_skeletonLT_openCell (n := (m : ℕ∞)) (le_refl _)).symm

/-! ## The homotopy-extension property from a cylinder retraction -/

/-- **Retraction criterion for the homotopy-extension property.**  If the cylinder `I × X`
retracts onto `{0} × X ∪ I × A`, then the inclusion `A ⊆ X` has the homotopy-extension property.
Source: Hatcher, *Algebraic Topology*, p. 14. -/
public theorem hasHomotopyExtensionProperty_of_cylinderRetraction {X : Type u}
    [TopologicalSpace X] {A : Set X} (hA : IsClosed A) (r : C(I × X, I × X))
    (hmem : ∀ p : I × X, (r p).1 = 0 ∨ (r p).2 ∈ A)
    (hfix : ∀ p : I × X, p.1 = 0 ∨ p.2 ∈ A → r p = p) :
    HasHomotopyExtensionProperty A := by
  classical
  intro Y _ f g h
  set S₀ : Set (I × X) := {q | q.1 = 0} with hS₀
  set S₁ : Set (I × X) := {q | q.2 ∈ A} with hS₁
  set F : I × X → Y := fun q ↦ if hq : q.2 ∈ A then h (q.1, ⟨q.2, hq⟩) else f q.2 with hF
  have hFA : ∀ (q : I × X) (hq : q.2 ∈ A), F q = h (q.1, ⟨q.2, hq⟩) := by
    intro q hq
    simp only [hF, hq, ↓reduceDIte]
  have hFnotA : ∀ q : I × X, q.2 ∉ A → F q = f q.2 := by
    intro q hq
    simp only [hF, hq, ↓reduceDIte]
  have hFone : ContinuousOn F S₁ := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hcont : Continuous fun q : S₁ ↦ ((q : I × X).1, (⟨(q : I × X).2, q.2⟩ : A)) :=
      (continuous_fst.comp continuous_subtype_val).prodMk
        ((continuous_snd.comp continuous_subtype_val).subtype_mk _)
    refine (h.continuous.comp hcont).congr ?_
    intro q
    exact (hFA (q : I × X) q.2).symm
  have hFzero : ContinuousOn F S₀ := by
    rw [continuousOn_iff_continuous_domRestrict]
    refine ((f.continuous.comp continuous_snd).comp continuous_subtype_val).congr ?_
    intro q
    have hq0 : (q : I × X).1 = 0 := q.2
    show f ((q : I × X).2) = F (q : I × X)
    by_cases hq : (q : I × X).2 ∈ A
    · rw [hFA _ hq, hq0]
      exact (h.map_zero_left ⟨(q : I × X).2, hq⟩).symm
    · rw [hFnotA _ hq]
  have hFcont : ContinuousOn F (S₀ ∪ S₁) :=
    hFzero.union_of_isClosed hFone (isClosed_singleton.preimage continuous_fst)
      (hA.preimage continuous_snd)
  have hmaps : ∀ p : I × X, r p ∈ S₀ ∪ S₁ := by
    intro p
    rcases hmem p with hp | hp
    · exact Or.inl hp
    · exact Or.inr hp
  have hHcont : Continuous (F ∘ r) := hFcont.comp_continuous r.continuous hmaps
  set Hc : C(I × X, Y) := ⟨F ∘ r, hHcont⟩ with hHc
  have hHcA : ∀ (s : I) (a : A), Hc (s, (a : X)) = h (s, a) := by
    intro s a
    have hr : r (s, (a : X)) = (s, (a : X)) := hfix _ (Or.inr a.2)
    show F (r (s, (a : X))) = h (s, a)
    rw [hr, hFA (s, (a : X)) a.2]
  have hHc0 : ∀ x : X, Hc (0, x) = f x := by
    intro x
    have hr : r ((0 : I), x) = ((0 : I), x) := hfix _ (Or.inl rfl)
    show F (r ((0 : I), x)) = f x
    rw [hr]
    by_cases hx : x ∈ A
    · rw [hFA ((0 : I), x) hx]
      exact h.map_zero_left ⟨x, hx⟩
    · rw [hFnotA _ hx]
  refine ⟨⟨fun x ↦ Hc (1, x), Hc.continuous.comp (continuous_const.prodMk continuous_id)⟩,
    { toContinuousMap := Hc
      map_zero_left := hHc0
      map_one_left := fun _ ↦ rfl }, hHcA⟩

/-- The cofibration statement for a relative CW pair reduced to its geometric input: a retraction
of the cylinder `I × X` onto `{0} × X ∪ I × A`.  The closedness of the base is part of the
`RelCWComplex` structure (`isClosedBase`), so no separatedness hypothesis is needed here. -/
public theorem hasHomotopyExtensionProperty_of_relativeCWComplex_of_cylinderRetraction
    {X : Type u} [TopologicalSpace X] (A : Set X)
    (hCW : RelCWComplex (Set.univ : Set X) A)
    (r : C(I × X, I × X))
    (hmem : ∀ p : I × X, (r p).1 = 0 ∨ (r p).2 ∈ A)
    (hfix : ∀ p : I × X, p.1 = 0 ∨ p.2 ∈ A → r p = p) :
    HasHomotopyExtensionProperty A :=
  hasHomotopyExtensionProperty_of_cylinderRetraction hCW.isClosedBase r hmem hfix

/-! ## Assembling the skeletal retractions -/

section Assembly

variable {X : Type u} [TopologicalSpace X] [T2Space X]

/-- The `m`-skeleton of a relative CW complex, as a subset of the ambient space. -/
public abbrev skeletonSet (C A : Set X) [RelCWComplex C A] (m : ℕ) : Set X :=
  (RelCWComplex.skeletonLT C ((m : ℕ) : ℕ∞) : Set X)

public theorem base_subset_skeletonSet (C A : Set X) [RelCWComplex C A] (m : ℕ) :
    A ⊆ skeletonSet C A m :=
  RelCWComplex.Subcomplex.base_subset (RelCWComplex.skeletonLT C ((m : ℕ) : ℕ∞))

public theorem skeletonSet_mono (C A : Set X) [RelCWComplex C A] {m k : ℕ} (h : m ≤ k) :
    skeletonSet C A m ⊆ skeletonSet C A k :=
  SetLike.coe_subset_coe.mpr (RelCWComplex.skeletonLT_mono (by exact_mod_cast h))

public theorem isClosed_skeletonSet (C A : Set X) [RelCWComplex C A] (m : ℕ) :
    IsClosed (skeletonSet C A m) :=
  RelCWComplex.Subcomplex.closed (RelCWComplex.skeletonLT C ((m : ℕ) : ℕ∞))

public theorem skeletonSet_zero (C A : Set X) [RelCWComplex C A] : skeletonSet C A 0 = A := by
  rw [skeletonSet, Nat.cast_zero]
  exact RelCWComplex.skeletonLT_zero_eq_base

/-- A retraction of `I × (m-skeleton)` onto `{0} × (m-skeleton) ∪ I × A`. -/
public structure SkeletonRetractData (C A : Set X) [RelCWComplex C A] (m : ℕ) where
  /-- The underlying retraction. -/
  toMap : C(I × ↥(skeletonSet C A m), I × ↥(skeletonSet C A m))
  /-- It lands in the L-shaped set. -/
  mem : ∀ q, (toMap q).1 = 0 ∨ ((toMap q).2 : X) ∈ A
  /-- It fixes the L-shaped set. -/
  fix : ∀ q, q.1 = 0 ∨ ((q.2 : X)) ∈ A → toMap q = q

/-- Compatibility of consecutive stages: the retraction of the `(m+1)`-skeleton restricts on the
`m`-skeleton to the retraction of the `m`-skeleton. -/
public def SkeletonRetractData.Agrees {C A : Set X} [RelCWComplex C A] {m : ℕ}
    (d : SkeletonRetractData C A (m + 1)) (e : SkeletonRetractData C A m) : Prop :=
  ∀ (q : I × ↥(skeletonSet C A (m + 1))) (hq : ((q.2 : X)) ∈ skeletonSet C A m),
    (d.toMap q).1 = (e.toMap (q.1, ⟨(q.2 : X), hq⟩)).1 ∧
      ((d.toMap q).2 : X) = ((e.toMap (q.1, ⟨(q.2 : X), hq⟩)).2 : X)

/-- The `0`-skeleton is the base, so the identity retracts it. -/
public def skeletonRetractDataZero (C A : Set X) [RelCWComplex C A] :
    SkeletonRetractData C A 0 where
  toMap := ContinuousMap.id _
  mem q := Or.inr ((skeletonSet_zero C A).subset q.2.2)
  fix _ _ := rfl

/-- The inductive step: the skeletal retraction composed with the retraction of the previous
skeleton. -/
public theorem nonempty_skeletonRetractData_succ (C A : Set X) [RelCWComplex C A] (m : ℕ)
    (e : SkeletonRetractData C A m) :
    Nonempty { d : SkeletonRetractData C A (m + 1) // d.Agrees e } := by
  obtain ⟨ρ, hρmem, hρfix⟩ := exists_skeletalRetraction C A m
  obtain ⟨r, hrmem, hrfix, hragree⟩ :=
    exists_cylinderRetraction_trans_subset (A := A) (B := skeletonSet C A m)
      (C := skeletonSet C A (m + 1)) (base_subset_skeletonSet C A m)
      (skeletonSet_mono C A (Nat.le_succ m)) (isClosed_skeletonSet C A m)
      ρ hρmem hρfix e.toMap e.mem e.fix
  exact ⟨⟨⟨r, hrmem, hrfix⟩, hragree⟩⟩

/-- The coherent family of skeletal retractions, built by recursion on the skeleton. -/
public noncomputable def skeletonRetractData (C A : Set X) [RelCWComplex C A] :
    (m : ℕ) → SkeletonRetractData C A m
  | 0 => skeletonRetractDataZero C A
  | m + 1 => (Classical.choice (nonempty_skeletonRetractData_succ C A m
      (skeletonRetractData C A m))).1

public theorem skeletonRetractData_zero (C A : Set X) [RelCWComplex C A] :
    skeletonRetractData C A 0 = skeletonRetractDataZero C A :=
  rfl

public theorem skeletonRetractData_agrees (C A : Set X) [RelCWComplex C A] (m : ℕ) :
    (skeletonRetractData C A (m + 1)).Agrees (skeletonRetractData C A m) :=
  (Classical.choice (nonempty_skeletonRetractData_succ C A m (skeletonRetractData C A m))).2

/-- Stages beyond `m` restrict to the `m`-th stage on the `m`-skeleton. -/
public theorem skeletonRetractData_agrees_le (C A : Set X) [RelCWComplex C A]
    {m k : ℕ} (hmk : m ≤ k) (t : I) (x : X) (hxm : x ∈ skeletonSet C A m) :
    ∀ hxk : x ∈ skeletonSet C A k,
      ((skeletonRetractData C A k).toMap (t, ⟨x, hxk⟩)).1 =
          ((skeletonRetractData C A m).toMap (t, ⟨x, hxm⟩)).1 ∧
        (((skeletonRetractData C A k).toMap (t, ⟨x, hxk⟩)).2 : X) =
          (((skeletonRetractData C A m).toMap (t, ⟨x, hxm⟩)).2 : X) := by
  induction k, hmk using Nat.le_induction with
  | base => exact fun _ ↦ ⟨rfl, rfl⟩
  | succ k hmk ih =>
    intro hxk
    have hxk' : x ∈ skeletonSet C A k := skeletonSet_mono C A hmk hxm
    obtain ⟨h1, h2⟩ := skeletonRetractData_agrees C A k (t, ⟨x, hxk⟩) hxk'
    obtain ⟨i1, i2⟩ := ih hxk'
    exact ⟨h1.trans i1, h2.trans i2⟩

end Assembly

/-! ## The homotopy-extension property of a relative CW pair -/

/-- **A relative CW pair is a cofibration.**  The inclusion of the base of a relative CW complex
has the homotopy-extension property.  Source: Hatcher, *Algebraic Topology*, Prop. 0.16.

The Hausdorff hypothesis is genuine: Mathlib's `RelCWComplex` does not require it, and without it
the closed cells need not be closed, which is what the cell-by-cell recognition of continuity
(`continuous_prod_of_continuous_cellPoint`) rests on. -/
public theorem hasHomotopyExtensionProperty_of_relativeCWComplex_proved
    {X : Type*} [TopologicalSpace X] [T2Space X] (A : Set X)
    (hCW : RelCWComplex (Set.univ : Set X) A) :
    HasHomotopyExtensionProperty A := by
  classical
  have := hCW
  have hex : ∀ x : X, ∃ m : ℕ, x ∈ skeletonSet (Set.univ : Set X) A m := by
    intro x
    have := RelCWComplex.iUnion_skeletonLT_eq_complex (C := (Set.univ : Set X)) (D := A)
    have hx : x ∈ ⋃ (n : ℕ), (RelCWComplex.skeletonLT (Set.univ : Set X) (n : ℕ∞) : Set X) := by
      rw [this]
      exact Set.mem_univ x
    simpa using hx
  choose mIdx hmIdx using hex
  set R := skeletonRetractData (Set.univ : Set X) A with hR
  -- the value of the retraction, computed at any admissible stage
  have hval : ∀ (t : I) (x : X) (m : ℕ) (hx : x ∈ skeletonSet (Set.univ : Set X) A m),
      ((R (mIdx x)).toMap (t, ⟨x, hmIdx x⟩)).1 = ((R m).toMap (t, ⟨x, hx⟩)).1 ∧
        (((R (mIdx x)).toMap (t, ⟨x, hmIdx x⟩)).2 : X) =
          (((R m).toMap (t, ⟨x, hx⟩)).2 : X) := by
    intro t x m hx
    have hxmax : x ∈ skeletonSet (Set.univ : Set X) A (max (mIdx x) m) :=
      skeletonSet_mono _ A (le_max_left _ _) (hmIdx x)
    obtain ⟨a1, a2⟩ :=
      skeletonRetractData_agrees_le (Set.univ : Set X) A (le_max_left (mIdx x) m) t x
        (hmIdx x) hxmax
    obtain ⟨b1, b2⟩ :=
      skeletonRetractData_agrees_le (Set.univ : Set X) A (le_max_right (mIdx x) m) t x hx hxmax
    exact ⟨a1.symm.trans b1, a2.symm.trans b2⟩
  refine hasHomotopyExtensionProperty_of_relativeCWComplex_of_cylinderRetraction A hCW
    ⟨fun q ↦ (((R (mIdx q.2)).toMap (q.1, ⟨q.2, hmIdx q.2⟩)).1,
      (((R (mIdx q.2)).toMap (q.1, ⟨q.2, hmIdx q.2⟩)).2 : X)), ?_⟩ ?_ ?_
  · refine continuous_prod_of_continuousOn_closedCell (A := A) ?_ ?_
    · intro l j
      have hsub : ∀ y : ↥(closedBall (0 : Fin l → ℝ) 1),
          RelCWComplex.map (C := (Set.univ : Set X)) l j (y : Fin l → ℝ) ∈
            skeletonSet (Set.univ : Set X) A (l + 1) :=
        fun y ↦ RelCWComplex.closedCell_subset_skeletonLT l j
          ⟨(y : Fin l → ℝ), y.2, rfl⟩
      have hc : Continuous fun p : I × ↥(closedBall (0 : Fin l → ℝ) 1) ↦
          (((R (l + 1)).toMap (p.1, ⟨RelCWComplex.map (C := (Set.univ : Set X)) l j
              (p.2 : Fin l → ℝ), hsub p.2⟩)).1,
            (((R (l + 1)).toMap (p.1, ⟨RelCWComplex.map (C := (Set.univ : Set X)) l j
              (p.2 : Fin l → ℝ), hsub p.2⟩)).2 : X)) := by
        have hin : Continuous fun p : I × ↥(closedBall (0 : Fin l → ℝ) 1) ↦
            (p.1, (⟨RelCWComplex.map (C := (Set.univ : Set X)) l j (p.2 : Fin l → ℝ),
              hsub p.2⟩ : ↥(skeletonSet (Set.univ : Set X) A (l + 1)))) :=
          continuous_fst.prodMk
            (((RelCWComplex.continuousOn (C := (Set.univ : Set X)) l j).domRestrict.comp
              continuous_snd).subtype_mk _)
        exact (continuous_fst.comp ((R (l + 1)).toMap.continuous.comp hin)).prodMk
          (continuous_subtype_val.comp
            (continuous_snd.comp ((R (l + 1)).toMap.continuous.comp hin)))
      refine hc.congr fun p ↦ ?_
      obtain ⟨h1, h2⟩ := hval p.1 (RelCWComplex.map (C := (Set.univ : Set X)) l j
        (p.2 : Fin l → ℝ)) (l + 1) (hsub p.2)
      exact (Prod.ext h1 h2).symm
    · have hbase : ∀ a : ↥A, a.1 ∈ skeletonSet (Set.univ : Set X) A 0 :=
        fun a ↦ (skeletonSet_zero (Set.univ : Set X) A).symm ▸ a.2
      refine (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).congr
        fun p ↦ ?_
      obtain ⟨h1, h2⟩ := hval p.1 (p.2 : X) 0 (hbase p.2)
      have hid : (R 0).toMap (p.1, ⟨(p.2 : X), hbase p.2⟩) = (p.1, ⟨(p.2 : X), hbase p.2⟩) := by
        rw [hR, skeletonRetractData_zero]
        rfl
      rw [hid] at h1 h2
      exact (Prod.ext h1 h2).symm
  · intro q
    exact (R (mIdx q.2)).mem (q.1, ⟨q.2, hmIdx q.2⟩)
  · intro q hq
    have h := (R (mIdx q.2)).fix (q.1, ⟨q.2, hmIdx q.2⟩) hq
    show (((R (mIdx q.2)).toMap (q.1, ⟨q.2, hmIdx q.2⟩)).1,
      (((R (mIdx q.2)).toMap (q.1, ⟨q.2, hmIdx q.2⟩)).2 : X)) = q
    rw [h]

end EstablishedGeneralTopology

end SphereSixComplex

end

end
