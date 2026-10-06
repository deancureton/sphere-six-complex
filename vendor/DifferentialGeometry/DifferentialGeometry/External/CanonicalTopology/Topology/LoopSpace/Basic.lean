module

public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Topology.Instances.AddCircle.Real

@[expose] public section

/-!
# Parametrized continuous loops

The circle is `ℝ / ℤ`, and the loop topology is the compact-open topology.
This supplies the continuous objects of `def:rfs-continuous-loop-model`
and `def:rfs-regular-loops`. No regularity, immersion, or reparametrization
quotient is imposed here. The evaluation fibration and the signed homotopy
group identification are separate, still missing theorems.
-/

noncomputable section

open ContinuousMap

namespace DifferentialGeometry.Topology

/-- The period-one parameter circle. -/
abbrev loopCircle := UnitAddCircle

/-- Parametrized continuous loops, with Mathlib's compact-open topology. -/
abbrev freeLoop (Q : Type*) [TopologicalSpace Q] := C(loopCircle, Q)

/-- The subspace of nullhomotopic parametrized continuous loops. -/
abbrev contractibleLoop (Q : Type*) [TopologicalSpace Q] :=
  {γ : freeLoop Q // γ.Nullhomotopic}

/-- The exponential law identifies free homotopies with paths in mapping space. -/
theorem homotopic_iff_joined {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [LocallyCompactSpace X] (f g : C(X, Y)) : f.Homotopic g ↔ Joined f g := by
  constructor
  · rintro ⟨H⟩
    exact ⟨⟨H.curry, H.curry_zero, H.curry_one⟩⟩
  · rintro ⟨p⟩
    exact ⟨⟨p.toContinuousMap.uncurry,
      fun x => congrArg (fun h : C(X, Y) => h x) p.source,
      fun x => congrArg (fun h : C(X, Y) => h x) p.target⟩⟩

namespace FreeLoop

variable {P Q R K : Type*}
  [TopologicalSpace P] [TopologicalSpace Q] [TopologicalSpace R] [TopologicalSpace K]

/-- Evaluation at the specified parameter zero. -/
def evaluation : C(freeLoop Q, Q) := ⟨fun γ => γ 0, continuous_eval_const 0⟩

/-- The continuous section consisting of constant loops. -/
def constants : C(Q, freeLoop Q) := ContinuousMap.const'

@[simp] theorem evaluation_apply (γ : freeLoop Q) : evaluation γ = γ 0 := rfl

@[simp] theorem constants_apply (q : Q) (θ : loopCircle) : constants q θ = q := rfl

@[simp] theorem evaluation_constants : (evaluation (Q := Q)).comp constants = .id Q := rfl

/-- Postcomposition needs only continuity of the target map. -/
def postcompose (f : C(P, Q)) : C(freeLoop P, freeLoop Q) :=
  ⟨ContinuousMap.comp f, continuous_postcomp f⟩

@[simp] theorem postcompose_apply (f : C(P, Q)) (γ : freeLoop P) (θ : loopCircle) :
    postcompose f γ θ = f (γ θ) := rfl

@[simp] theorem postcompose_id : postcompose (.id Q) = .id (freeLoop Q) := rfl

@[simp] theorem postcompose_comp (g : C(Q, R)) (f : C(P, Q)) :
    postcompose (g.comp f) = (postcompose g).comp (postcompose f) := rfl

theorem evaluation_postcompose (f : C(P, Q)) :
    evaluation.comp (postcompose f) = f.comp evaluation := rfl

theorem postcompose_constants (f : C(P, Q)) :
    (postcompose f).comp constants = constants.comp f := rfl

/-- A continuous family has a jointly continuous adjoint, without any condition on `K`. -/
def adjoint (Γ : C(K, freeLoop Q)) : C(K × loopCircle, Q) := Γ.uncurry

@[simp] theorem adjoint_apply (Γ : C(K, freeLoop Q)) (k : K) (θ : loopCircle) :
    adjoint Γ (k, θ) = Γ k θ := rfl

theorem continuous_family_iff (Γ : K → freeLoop Q) :
    Continuous Γ ↔ Continuous (fun p : K × loopCircle => Γ p.1 p.2) := by
  constructor
  · intro h
    exact (adjoint ⟨Γ, h⟩).continuous
  · exact continuous_of_continuous_uncurry Γ

/-- The exponential law identifies free homotopies of loops with paths in loop space. -/
theorem homotopic_iff_joined (γ η : freeLoop Q) : γ.Homotopic η ↔ Joined γ η := by
  exact DifferentialGeometry.Topology.homotopic_iff_joined γ η

/-- Contractibility is preserved throughout any free homotopy. -/
theorem nullhomotopic_of_homotopic {γ η : freeLoop Q} (h : γ.Homotopic η)
    (hγ : γ.Nullhomotopic) : η.Nullhomotopic := by
  obtain ⟨q, hq⟩ := hγ
  exact ⟨q, h.symm.trans hq⟩

end FreeLoop

namespace ContractibleLoop

variable {P Q R : Type*} [TopologicalSpace P] [TopologicalSpace Q] [TopologicalSpace R]

/-- Inclusion of the contractible-loop subspace into the full loop space. -/
def inclusion : C(contractibleLoop Q, freeLoop Q) := ⟨Subtype.val, continuous_subtype_val⟩

/-- Constant loops belong to the contractible-loop subspace, continuously in their value. -/
def constants : C(Q, contractibleLoop Q) :=
  ⟨fun q => ⟨.const loopCircle q, nullhomotopic_of_constant q⟩,
    continuous_const'.subtype_mk _⟩

/-- Evaluation on contractible loops. -/
def evaluation : C(contractibleLoop Q, Q) := FreeLoop.evaluation.comp inclusion

@[simp] theorem constants_apply (q : Q) (θ : loopCircle) : (constants q).val θ = q := rfl

@[simp] theorem evaluation_constants : (evaluation (Q := Q)).comp constants = .id Q := rfl

/-- Continuous maps preserve loop contractions by composing the actual homotopy. -/
def postcompose (f : C(P, Q)) : C(contractibleLoop P, contractibleLoop Q) :=
  ⟨fun γ => ⟨f.comp γ.val, γ.property.comp_right f⟩,
    ((continuous_postcomp f).comp continuous_subtype_val).subtype_mk _⟩

@[simp] theorem postcompose_apply (f : C(P, Q)) (γ : contractibleLoop P) (θ : loopCircle) :
    (postcompose f γ).val θ = f (γ.val θ) := rfl

@[simp] theorem postcompose_id : postcompose (.id Q) = .id (contractibleLoop Q) := rfl

@[simp] theorem postcompose_comp (g : C(Q, R)) (f : C(P, Q)) :
    postcompose (g.comp f) = (postcompose g).comp (postcompose f) := rfl

theorem inclusion_postcompose (f : C(P, Q)) :
    inclusion.comp (postcompose f) = (FreeLoop.postcompose f).comp inclusion := rfl

end ContractibleLoop

end DifferentialGeometry.Topology
