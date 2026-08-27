module

public import SphereSixComplex.Topology.MapHomotopyEquivalence

/-!
# Splitting and cancellation criteria for homotopy equivalences

`IsHomotopyEquivalence f` says exactly that `f` is an isomorphism in the homotopy category.  This
file records the elementary consequences of that description which are needed to run an
*interleaving* argument: invariance under homotopy, the two cancellation laws, and the statement
that a map which is simultaneously a split epimorphism and a split monomorphism in the homotopy
category is an isomorphism there.

The splitting criterion is what makes an interleaved chain

```
A → B → C → D
```

whose two long composites `A → C` and `B → D` are homotopy equivalences force *every* map in the
chain to be a homotopy equivalence.  No Whitehead theorem and no CW hypotheses are involved: the
argument is a formal computation in the homotopy category, so it applies verbatim to the
non-triangulable quotient spaces of a varying torus family.
-/

@[expose] public section

open ContinuousMap

namespace SphereSixComplex

universe u v w t

variable {X : Type u} {Y : Type v} {Z : Type w} {W : Type t}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace W]

/-- Being a homotopy equivalence only depends on the homotopy class of the map. -/
public theorem isHomotopyEquivalence_of_homotopic {f g : C(X, Y)} (h : f.Homotopic g)
    (hg : IsHomotopyEquivalence (g : X → Y)) :
    IsHomotopyEquivalence (f : X → Y) := by
  obtain ⟨e, he⟩ := hg
  have hte : e.toFun = g := DFunLike.ext _ _ (congrFun he)
  refine ⟨⟨f, e.invFun, ?_, ?_⟩, rfl⟩
  · refine ((ContinuousMap.Homotopic.refl e.invFun).comp h).trans ?_
    rw [← hte]
    exact e.left_inv
  · refine (h.comp (ContinuousMap.Homotopic.refl e.invFun)).trans ?_
    rw [← hte]
    exact e.right_inv

/-- Left cancellation: if `g ∘ f` and `g` are homotopy equivalences then so is `f`. -/
public theorem isHomotopyEquivalence_of_comp_left {f : C(X, Y)} {g : C(Y, Z)}
    (hgf : IsHomotopyEquivalence ((g.comp f : C(X, Z)) : X → Z))
    (hg : IsHomotopyEquivalence (g : Y → Z)) :
    IsHomotopyEquivalence (f : X → Y) := by
  obtain ⟨e, he⟩ := hg
  have hte : e.toFun = g := DFunLike.ext _ _ (congrFun he)
  have hcomp : IsHomotopyEquivalence ((e.invFun.comp (g.comp f) : C(X, Y)) : X → Y) := by
    obtain ⟨e₂, he₂⟩ := hgf
    exact ⟨e₂.trans e.symm, funext fun x ↦ congrArg e.invFun (congrFun he₂ x)⟩
  refine isHomotopyEquivalence_of_homotopic ?_ hcomp
  rw [← hte]
  simpa using e.left_inv.symm.comp (ContinuousMap.Homotopic.refl f)

/-- Right cancellation: if `g ∘ f` and `f` are homotopy equivalences then so is `g`. -/
public theorem isHomotopyEquivalence_of_comp_right {f : C(X, Y)} {g : C(Y, Z)}
    (hgf : IsHomotopyEquivalence ((g.comp f : C(X, Z)) : X → Z))
    (hf : IsHomotopyEquivalence (f : X → Y)) :
    IsHomotopyEquivalence (g : Y → Z) := by
  obtain ⟨e, he⟩ := hf
  have hte : e.toFun = f := DFunLike.ext _ _ (congrFun he)
  have hcomp : IsHomotopyEquivalence (((g.comp f).comp e.invFun : C(Y, Z)) : Y → Z) := by
    obtain ⟨e₂, he₂⟩ := hgf
    exact ⟨e.symm.trans e₂, funext fun x ↦ congrFun he₂ (e.invFun x)⟩
  refine isHomotopyEquivalence_of_homotopic ?_ hcomp
  rw [← hte]
  simpa using (ContinuousMap.Homotopic.refl g).comp e.right_inv.symm

/-- A map which is a split epimorphism and a split monomorphism in the homotopy category is an
isomorphism there.  Concretely: in a chain `X → Y → Z → W`, if the two long composites `X → Z`
and `Y → W` are homotopy equivalences, then the middle map `Y → Z` is a homotopy equivalence. -/
public theorem isHomotopyEquivalence_middle_of_interleaving (f : C(X, Y)) (g : C(Y, Z))
    (h : C(Z, W))
    (hgf : IsHomotopyEquivalence ((g.comp f : C(X, Z)) : X → Z))
    (hhg : IsHomotopyEquivalence ((h.comp g : C(Y, W)) : Y → W)) :
    IsHomotopyEquivalence (g : Y → Z) := by
  obtain ⟨e, he⟩ := hgf
  obtain ⟨e', he'⟩ := hhg
  have heq : e.toFun = g.comp f := DFunLike.ext _ _ (congrFun he)
  have heq' : e'.toFun = h.comp g := DFunLike.ext _ _ (congrFun he')
  set p : C(Z, Y) := f.comp e.invFun with hp
  set q : C(Z, Y) := e'.invFun.comp h with hq
  have hGp : (g.comp p).Homotopic (ContinuousMap.id Z) := by
    have hcomp : g.comp p = e.toFun.comp e.invFun := by
      rw [hp, heq, ContinuousMap.comp_assoc]
    rw [hcomp]
    exact e.right_inv
  have hqG : (q.comp g).Homotopic (ContinuousMap.id Y) := by
    have hcomp : q.comp g = e'.invFun.comp e'.toFun := by
      rw [hq, heq', ContinuousMap.comp_assoc]
    rw [hcomp]
    exact e'.left_inv
  have hqp : q.Homotopic p := by
    have h1 : (q.comp (g.comp p)).Homotopic (q.comp (ContinuousMap.id Z)) :=
      (ContinuousMap.Homotopic.refl q).comp hGp
    have h2 : ((q.comp g).comp p).Homotopic ((ContinuousMap.id Y).comp p) :=
      hqG.comp (ContinuousMap.Homotopic.refl p)
    have hassoc : q.comp (g.comp p) = (q.comp g).comp p :=
      (ContinuousMap.comp_assoc _ _ _).symm
    simp only [ContinuousMap.comp_id, ContinuousMap.id_comp] at h1 h2
    rw [hassoc] at h1
    exact h1.symm.trans h2
  exact ⟨⟨g, q, hqG, ((ContinuousMap.Homotopic.refl g).comp hqp).trans hGp⟩, rfl⟩

/-- In an interleaved chain `X → Y → Z → W` whose long composites are homotopy equivalences,
the first map is a homotopy equivalence. -/
public theorem isHomotopyEquivalence_first_of_interleaving (f : C(X, Y)) (g : C(Y, Z))
    (h : C(Z, W))
    (hgf : IsHomotopyEquivalence ((g.comp f : C(X, Z)) : X → Z))
    (hhg : IsHomotopyEquivalence ((h.comp g : C(Y, W)) : Y → W)) :
    IsHomotopyEquivalence (f : X → Y) :=
  isHomotopyEquivalence_of_comp_left hgf
    (isHomotopyEquivalence_middle_of_interleaving f g h hgf hhg)

/-- In an interleaved chain `X → Y → Z → W` whose long composites are homotopy equivalences,
the last map is a homotopy equivalence. -/
public theorem isHomotopyEquivalence_last_of_interleaving (f : C(X, Y)) (g : C(Y, Z))
    (h : C(Z, W))
    (hgf : IsHomotopyEquivalence ((g.comp f : C(X, Z)) : X → Z))
    (hhg : IsHomotopyEquivalence ((h.comp g : C(Y, W)) : Y → W)) :
    IsHomotopyEquivalence (h : Z → W) :=
  isHomotopyEquivalence_of_comp_right hhg
    (isHomotopyEquivalence_middle_of_interleaving f g h hgf hhg)

end SphereSixComplex

end
