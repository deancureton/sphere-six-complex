module

public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Convex.Combination

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite Simplicial

universe u

namespace DifferentialGeometry.Homology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]


def affineSimplex {n : ℕ} (v : Fin (n + 1) → E) :
    C(Convexity.StdSimplex ℝ (Fin (n + 1)), E) where
  toFun x := ∑ i, x.weights i • v i
  continuous_toFun := continuous_finsetSum _ (fun i _ ↦
    (Convexity.StdSimplex.continuous_weights_apply ℝ i).smul continuous_const)


theorem affineSimplex_apply {n : ℕ} (v : Fin (n + 1) → E)
    (x : Convexity.StdSimplex ℝ (Fin (n + 1))) : affineSimplex v x = ∑ i, x.weights i • v i := rfl


@[simp]
theorem affineSimplex_vertex {n : ℕ} (v : Fin (n + 1) → E) (i : Fin (n + 1)) :
    affineSimplex v (Convexity.StdSimplex.single i) = v i := by
  change ∑ j, (Finsupp.single i (1 : ℝ)) j • v j = v i
  rw [← Finsupp.sum_fintype (Finsupp.single i (1 : ℝ))
    (fun j a => a • v j) (fun _ => zero_smul _ _), Finsupp.sum_single_index]
  · exact one_smul ℝ _
  · exact zero_smul ℝ _

theorem affineSimplex_comp_map {n m : ℕ} (v : Fin (n + 1) → E)
    (f : Fin (m + 1) → Fin (n + 1)) :
    (affineSimplex v).comp ⟨Convexity.StdSimplex.map f, Convexity.StdSimplex.continuous_map ℝ f⟩ =
      affineSimplex (v ∘ f) := by
  ext x
  change ∑ j, (x.weights.mapDomain f) j • v j = ∑ i, x.weights i • v (f i)
  rw [← Finsupp.sum_fintype (x.weights.mapDomain f)
    (fun j a => a • v j) (fun _ => zero_smul _ _),
    ← Finsupp.sum_fintype x.weights (fun i a => a • v (f i)) (fun _ => zero_smul _ _)]
  exact Finsupp.sum_mapDomain_index (fun _ => zero_smul _ _)
    (fun _ _ _ => add_smul _ _ _)



theorem range_affineSimplex_subset {n : ℕ} (v : Fin (n + 1) → E) {s : Set E}
    (hs : Convex ℝ s) (hv : ∀ i, v i ∈ s) : Set.range (affineSimplex v) ⊆ s := by
  rintro _ ⟨x, rfl⟩
  exact hs.sum_mem (fun i _ ↦ x.weights_nonneg i) x.total_of_fintype (fun i _ ↦ hv i)


def affineSimplexIn {s : Set E} (hs : Convex ℝ s) {n : ℕ} (v : Fin (n + 1) → s) :
    C(Convexity.StdSimplex ℝ (Fin (n + 1)), s) :=
  ⟨fun x ↦ ⟨affineSimplex (fun i ↦ (v i : E)) x,
      range_affineSimplex_subset _ hs (fun i ↦ (v i).property) ⟨x, rfl⟩⟩,
    (affineSimplex (fun i ↦ (v i : E))).continuous.subtype_mk _⟩


def affineSingularSimplex {n : ℕ} (v : Fin (n + 1) → E) :
    TopCat.toSSet.obj (TopCat.of E) _⦋n⦌ :=
  ((TopCat.of E).toSSetObjEquiv (op ⦋n⦌)).symm (affineSimplex v)


def singularSimplexVertices {n : ℕ} (σ : TopCat.toSSet.obj (TopCat.of E) _⦋n⦌) :
    Fin (n + 1) → E :=
  fun i ↦ (TopCat.of E).toSSetObjEquiv (op ⦋n⦌) σ (Convexity.StdSimplex.single i)


@[simp]
theorem singularSimplexVertices_affineSingularSimplex {n : ℕ} (v : Fin (n + 1) → E) :
    singularSimplexVertices (affineSingularSimplex v) = v := by
  funext i
  exact affineSimplex_vertex v i

omit [NormedSpace ℝ E] in
theorem singularSimplexVertices_map {n m : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌)
    (σ : TopCat.toSSet.obj (TopCat.of E) _⦋n⦌) :
    singularSimplexVertices ((TopCat.toSSet.obj (TopCat.of E)).map f.op σ) =
      singularSimplexVertices σ ∘ f := by
  funext i
  change (TopCat.of E).toSSetObjEquiv (op ⦋n⦌) σ
      (Convexity.StdSimplex.map f (Convexity.StdSimplex.single i)) = _
  rw [Convexity.StdSimplex.map_single]
  rfl

omit [NormedSpace ℝ E] in
@[simp]
theorem singularSimplexVertices_δ {n : ℕ}
    (σ : TopCat.toSSet.obj (TopCat.of E) _⦋n + 1⦌) (i : Fin (n + 2)) :
    singularSimplexVertices ((TopCat.toSSet.obj (TopCat.of E)).δ i σ) =
      singularSimplexVertices σ ∘ i.succAbove :=
  singularSimplexVertices_map (SimplexCategory.δ i) σ


theorem map_affineSingularSimplex {n m : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) (v : Fin (n + 1) → E) :
    (TopCat.toSSet.obj (TopCat.of E)).map f.op (affineSingularSimplex v) =
      affineSingularSimplex (v ∘ f) := by
  apply ((TopCat.of E).toSSetObjEquiv (op ⦋m⦌)).injective
  change (affineSimplex v).comp
    ⟨Convexity.StdSimplex.map f, Convexity.StdSimplex.continuous_map ℝ f⟩ = affineSimplex (v ∘ f)
  exact affineSimplex_comp_map v f

def affineStraightening : TopCat.toSSet.obj (TopCat.of E) ⟶ TopCat.toSSet.obj (TopCat.of E) where
  app n := ↾fun σ ↦ affineSingularSimplex (n := n.unop.len) (singularSimplexVertices σ)
  naturality n m f := by
    ext σ
    change affineSingularSimplex (singularSimplexVertices
      ((TopCat.toSSet.obj (TopCat.of E)).map f σ)) =
        (TopCat.toSSet.obj (TopCat.of E)).map f
          (affineSingularSimplex (singularSimplexVertices σ))
    exact (congrArg affineSingularSimplex (singularSimplexVertices_map f.unop σ)).trans
      (map_affineSingularSimplex f.unop (singularSimplexVertices σ)).symm


@[simp]
theorem affineStraightening_affineSingularSimplex {n : ℕ} (v : Fin (n + 1) → E) :
    (affineStraightening (E := E)).app (op ⦋n⦌) (affineSingularSimplex v) =
      affineSingularSimplex v := by
  change affineSingularSimplex (singularSimplexVertices (affineSingularSimplex v)) = _
  rw [singularSimplexVertices_affineSingularSimplex]


theorem affineSingularSimplex_vertices_zero (σ : TopCat.toSSet.obj (TopCat.of E) _⦋0⦌) :
    affineSingularSimplex (singularSimplexVertices σ) = σ := by
  apply ((TopCat.of E).toSSetObjEquiv (op ⦋0⦌)).injective
  ext x
  obtain rfl := Subsingleton.elim x (Convexity.StdSimplex.single (0 : Fin 1))
  exact affineSimplex_vertex _ 0


@[simp]
theorem δ_affineSingularSimplex {n : ℕ} (v : Fin (n + 2) → E) (i : Fin (n + 2)) :
    (TopCat.toSSet.obj (TopCat.of E)).δ i (affineSingularSimplex v) =
      affineSingularSimplex (v ∘ i.succAbove) := by
  apply ((TopCat.of E).toSSetObjEquiv (op ⦋n⦌)).injective
  change (affineSimplex v).comp
    ⟨Convexity.StdSimplex.map i.succAbove, Convexity.StdSimplex.continuous_map ℝ i.succAbove⟩ =
      affineSimplex (v ∘ i.succAbove)
  exact affineSimplex_comp_map v i.succAbove


def affineSingularSimplexIn {s : Set E} (hs : Convex ℝ s) {n : ℕ}
    (v : Fin (n + 1) → s) : TopCat.toSSet.obj (TopCat.of s) _⦋n⦌ :=
  ((TopCat.of s).toSSetObjEquiv (op ⦋n⦌)).symm (affineSimplexIn hs v)


theorem affineSingularSimplexIn_inclusion {s : Set E} (hs : Convex ℝ s) {n : ℕ}
    (v : Fin (n + 1) → s) :
    (TopCat.toSSet.map (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(s, E)))).app
      (op ⦋n⦌) (affineSingularSimplexIn hs v) =
        affineSingularSimplex (fun i ↦ (v i : E)) := rfl

end DifferentialGeometry.Homology
