module

public import SphereSixComplex.Topology.OrderedCechTupleAlgebra
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.TotalComplex

/-!
# Realizing formal tuple operators on coproducts of local models

Given a contravariant diagram of chain complexes on the nonempty finite subsets of a totally
ordered index type, the ordered Čech bicomplex in simplicial degree `n` is the coproduct of the
local models over all tuples `Fin (n + 1) → ι`, indexed by their supports.  Every structure map
we need — faces, the alternating boundary, the sort-with-sign operator, the first-repetition
operator and the two homotopies of Stacks 01FM — is a signed sum of face maps of local models,
i.e. the realization of a formal operator on tuples which does not enlarge supports.

This file defines the coproducts for a class of tuples closed under faces (all tuples, weakly
increasing tuples, strictly increasing tuples), the realization of an admissible formal operator,
the resulting alternating-face bicomplexes and total complexes, and the transfer of formal chain
maps and formal chain homotopies to actual ones.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Finsupp SphereSixComplex.OrderedCechTuple

namespace SphereSixComplex

variable {ι : Type} [LinearOrder ι]

/-- A nonempty finite set of cover indices. -/
public abbrev CoverSupport (ι : Type) := {s : Finset ι // s.Nonempty}

/-- The support of an ordered tuple as a nonempty finite set of cover indices. -/
public def tupleSupport {n : ℕ} (a : Fin (n + 1) → ι) : CoverSupport ι :=
  ⟨Finset.univ.image a, ⟨a 0, Finset.mem_image_of_mem a (Finset.mem_univ 0)⟩⟩

public theorem tupleSupport_subset_iff {n m : ℕ} (a : Fin (n + 1) → ι) (b : Fin (m + 1) → ι) :
    (tupleSupport b).1 ⊆ (tupleSupport a).1 ↔ Set.range b ⊆ Set.range a := by
  simp only [tupleSupport, ← Finset.coe_subset, Finset.coe_image, Finset.coe_univ, Set.image_univ]

/-- A contravariant diagram of chain complexes on nonempty finite sets of cover indices: the
generic local intersection-chain input of the ordered Čech construction. -/
public structure SupportChainModels (ι : Type) where
  /-- A chain model for each nonempty finite intersection. -/
  model : CoverSupport ι → ChainComplex AddCommGrpCat ℕ
  /-- Restriction along `s ⊆ t`, directed like inclusion of the corresponding intersections. -/
  face : ∀ {s t : CoverSupport ι}, s.1 ⊆ t.1 → (model t ⟶ model s)
  /-- Identity inclusions act as identity chain maps. -/
  face_id : ∀ s, face (Finset.Subset.refl s.1) = 𝟙 (model s)
  /-- Restriction maps compose functorially. -/
  face_comp : ∀ {r s t : CoverSupport ι} (hrs : r.1 ⊆ s.1) (hst : s.1 ⊆ t.1),
    face hst ≫ face hrs = face (hrs.trans hst)

/-- A class of ordered tuples, one predicate per simplicial degree, closed under faces. -/
public structure TupleClass (ι : Type) where
  /-- The tuples of the class in each simplicial degree. -/
  mem : ∀ n : ℕ, (Fin (n + 1) → ι) → Prop
  /-- Faces preserve the class. -/
  removeNth_mem : ∀ (n : ℕ) (a : Fin (n + 2) → ι) (i : Fin (n + 2)),
    mem (n + 1) a → mem n (Fin.removeNth i a)

namespace TupleClass

/-- All ordered tuples: the ordered Čech convention of the existing finite-cover comparison. -/
public abbrev all : TupleClass ι where
  mem _ _ := True
  removeNth_mem _ _ _ _ := trivial

/-- Weakly increasing tuples: the semi-ordered complex of Stacks 01FM. -/
public abbrev monotone : TupleClass ι where
  mem _ a := Monotone a
  removeNth_mem _ _ i ha := ha.comp (Fin.strictMono_succAbove i).monotone

/-- Strictly increasing tuples: the ordered (alternating) complex, one summand per support. -/
public abbrev strictMono : TupleClass ι where
  mem _ a := StrictMono a
  removeNth_mem _ _ i ha := ha.comp (Fin.strictMono_succAbove i)

end TupleClass

/-- A formal operator is admissible between two classes if, on tuples of the source class, it does
not enlarge supports and lands in the target class. -/
public structure Admissible (P Q : TupleClass ι) {n m : ℕ}
    (T : Formal ι (n + 1) →ₗ[ℤ] Formal ι (m + 1)) : Prop where
  range_subset : ∀ a, P.mem n a → ∀ b ∈ (T (single a 1)).support, Set.range b ⊆ Set.range a
  preserves : ∀ a, P.mem n a → ∀ b ∈ (T (single a 1)).support, Q.mem m b

namespace SupportChainModels

variable (M : SupportChainModels ι)

/-- The coproduct of local models over the tuples of a class in one simplicial degree. -/
public abbrev cechObject (P : TupleClass ι) (n : ℕ) : ChainComplex AddCommGrpCat ℕ :=
  ∐ fun a : {a : Fin (n + 1) → ι // P.mem n a} ↦ M.model (tupleSupport a.1)

/-- The face map from the model of `a` to the model of `b`, or zero if `b` is not supported in
`a`. -/
public def faceOrZero {n m : ℕ} (a : Fin (n + 1) → ι) (b : Fin (m + 1) → ι) :
    M.model (tupleSupport a) ⟶ M.model (tupleSupport b) :=
  if h : (tupleSupport b).1 ⊆ (tupleSupport a).1 then M.face h else 0

open scoped Classical in
/-- The coproduct inclusion of the summand of `b`, or zero if `b` is not in the class. -/
public def ιOrZero (P : TupleClass ι) {m : ℕ} (b : Fin (m + 1) → ι) :
    M.model (tupleSupport b) ⟶ M.cechObject P m :=
  if h : P.mem m b then
    Sigma.ι (fun a : {a : Fin (m + 1) → ι // P.mem m a} ↦ M.model (tupleSupport a.1)) ⟨b, h⟩
  else 0

/-- The signed sum of face maps out of the summand of `a` prescribed by a formal combination of
tuples: `b` contributes the face map of the inclusion of supports followed by the coproduct
inclusion of `b`. -/
public def realizeAux {n : ℕ} (a : Fin (n + 1) → ι) (Q : TupleClass ι) {m : ℕ} :
    Formal ι (m + 1) →ₗ[ℤ] (M.model (tupleSupport a) ⟶ M.cechObject Q m) :=
  Finsupp.linearCombination ℤ fun b ↦ M.faceOrZero a b ≫ M.ιOrZero Q b

/-- Realize a formal operator on tuples as a chain map between coproducts of local models: the
summand of `a` is sent to the signed sum of face maps prescribed by `T a`. -/
public def realize (P Q : TupleClass ι) {n m : ℕ} (T : Formal ι (n + 1) →ₗ[ℤ] Formal ι (m + 1)) :
    M.cechObject P n ⟶ M.cechObject Q m :=
  Sigma.desc fun a ↦ M.realizeAux a.1 Q (T (single a.1 1))

variable {M}

@[reassoc]
public theorem ι_realize (P Q : TupleClass ι) {n m : ℕ}
    (T : Formal ι (n + 1) →ₗ[ℤ] Formal ι (m + 1)) (a : {a : Fin (n + 1) → ι // P.mem n a}) :
    Sigma.ι (fun a : {a : Fin (n + 1) → ι // P.mem n a} ↦ M.model (tupleSupport a.1)) a ≫
        M.realize P Q T =
      M.realizeAux a.1 Q (T (single a.1 1)) := by
  unfold realize
  exact Sigma.ι_desc _ _

public theorem realizeAux_single {n m : ℕ} (a : Fin (n + 1) → ι) (Q : TupleClass ι)
    (b : Fin (m + 1) → ι) :
    M.realizeAux a Q (single b 1) = M.faceOrZero a b ≫ M.ιOrZero Q b := by
  rw [realizeAux, Finsupp.linearCombination_single, one_smul]

/-- Face maps of nested supports compose. -/
public theorem faceOrZero_comp_faceOrZero {n m k : ℕ} (a : Fin (n + 1) → ι) (b : Fin (m + 1) → ι)
    (c : Fin (k + 1) → ι) (hba : Set.range b ⊆ Set.range a) (hcb : Set.range c ⊆ Set.range b) :
    M.faceOrZero a b ≫ M.faceOrZero b c = M.faceOrZero a c := by
  unfold faceOrZero
  rw [dite_eq_left ((tupleSupport_subset_iff a b).2 hba), dite_eq_left ((tupleSupport_subset_iff b c).2 hcb),
    dite_eq_left ((tupleSupport_subset_iff a c).2 (hcb.trans hba)), M.face_comp]

public theorem faceOrZero_self {n : ℕ} (a : Fin (n + 1) → ι) : M.faceOrZero a a = 𝟙 _ := by
  unfold faceOrZero
  rw [dite_eq_left (Finset.Subset.refl _), M.face_id]

public theorem ιOrZero_of_mem (Q : TupleClass ι) {m : ℕ} {b : Fin (m + 1) → ι} (hb : Q.mem m b) :
    M.ιOrZero Q b =
      Sigma.ι (fun a : {a : Fin (m + 1) → ι // Q.mem m a} ↦ M.model (tupleSupport a.1)) ⟨b, hb⟩ := by
  unfold ιOrZero
  exact dite_eq_left hb

/-- Precomposing with a face map is compatible with realization, on combinations supported in the
support of the source tuple. -/
public theorem faceOrZero_comp_realizeAux {n m k : ℕ} (a : Fin (n + 1) → ι) (b : Fin (m + 1) → ι)
    (hba : Set.range b ⊆ Set.range a) (R : TupleClass ι) (u : Formal ι (k + 1))
    (hu : ∀ c ∈ u.support, Set.range c ⊆ Set.range b) :
    M.faceOrZero a b ≫ M.realizeAux b R u = M.realizeAux a R u := by
  have := linearMap_apply_eq_of_forall_mem_support
    (L := (Preadditive.leftComp _ (M.faceOrZero a b)).toIntLinearMap ∘ₗ M.realizeAux b R)
    (R := M.realizeAux a R) (w := u) fun c hc ↦ by
      change M.faceOrZero a b ≫ M.realizeAux b R (single c 1) = M.realizeAux a R (single c 1)
      rw [realizeAux_single, realizeAux_single, ← Category.assoc,
        faceOrZero_comp_faceOrZero _ _ _ hba (hu c hc)]
  exact this

/-- Postcomposing a realized combination with a realized admissible operator is realizing the
image combination. -/
public theorem realizeAux_comp_realize {n m k : ℕ} (a : Fin (n + 1) → ι) (Q R : TupleClass ι)
    (w : Formal ι (m + 1)) (hw : ∀ b ∈ w.support, Set.range b ⊆ Set.range a ∧ Q.mem m b)
    {S : Formal ι (m + 1) →ₗ[ℤ] Formal ι (k + 1)} (hS : Admissible Q R S) :
    M.realizeAux a Q w ≫ M.realize Q R S = M.realizeAux a R (S w) := by
  have := linearMap_apply_eq_of_forall_mem_support
    (L := (Preadditive.rightComp _ (M.realize Q R S)).toIntLinearMap ∘ₗ M.realizeAux a Q)
    (R := M.realizeAux a R ∘ₗ S) (w := w) fun b hb ↦ by
      change M.realizeAux a Q (single b 1) ≫ M.realize Q R S = M.realizeAux a R (S (single b 1))
      rw [realizeAux_single, ιOrZero_of_mem _ (hw b hb).2, Category.assoc, ι_realize,
        faceOrZero_comp_realizeAux _ _ (hw b hb).1 _ _ (hS.range_subset b (hw b hb).2)]
  exact this

public theorem realize_congr (P Q : TupleClass ι) {n m : ℕ}
    {T T' : Formal ι (n + 1) →ₗ[ℤ] Formal ι (m + 1)}
    (h : ∀ a, P.mem n a → T (single a 1) = T' (single a 1)) :
    M.realize P Q T = M.realize P Q T' :=
  Sigma.hom_ext _ _ fun a ↦ by rw [ι_realize, ι_realize, h a.1 a.2]

public theorem realize_add (P Q : TupleClass ι) {n m : ℕ}
    (T T' : Formal ι (n + 1) →ₗ[ℤ] Formal ι (m + 1)) :
    M.realize P Q (T + T') = M.realize P Q T + M.realize P Q T' :=
  Sigma.hom_ext _ _ fun a ↦ by
    rw [ι_realize, Preadditive.comp_add, ι_realize, ι_realize, LinearMap.add_apply,
      map_add]

public theorem realize_neg (P Q : TupleClass ι) {n m : ℕ}
    (T : Formal ι (n + 1) →ₗ[ℤ] Formal ι (m + 1)) :
    M.realize P Q (-T) = -M.realize P Q T :=
  Sigma.hom_ext _ _ fun a ↦ by
    rw [ι_realize, Preadditive.comp_neg, ι_realize, LinearMap.neg_apply, map_neg]

public theorem realize_sub (P Q : TupleClass ι) {n m : ℕ}
    (T T' : Formal ι (n + 1) →ₗ[ℤ] Formal ι (m + 1)) :
    M.realize P Q (T - T') = M.realize P Q T - M.realize P Q T' :=
  Sigma.hom_ext _ _ fun a ↦ by
    rw [ι_realize, Preadditive.comp_sub, ι_realize, ι_realize, LinearMap.sub_apply,
      map_sub]

public theorem realize_zsmul (P Q : TupleClass ι) {n m : ℕ} (z : ℤ)
    (T : Formal ι (n + 1) →ₗ[ℤ] Formal ι (m + 1)) :
    M.realize P Q (z • T) = z • M.realize P Q T :=
  Sigma.hom_ext _ _ fun a ↦ by
    rw [ι_realize, Preadditive.comp_zsmul, ι_realize, LinearMap.smul_apply, map_smul]

public theorem realize_zero (P Q : TupleClass ι) {n m : ℕ} :
    M.realize P Q (0 : Formal ι (n + 1) →ₗ[ℤ] Formal ι (m + 1)) = 0 :=
  Sigma.hom_ext _ _ fun a ↦ by rw [ι_realize, comp_zero, LinearMap.zero_apply, map_zero]

public theorem realize_finset_sum (P Q : TupleClass ι) {n m : ℕ} {α : Type} (s : Finset α)
    (T : α → (Formal ι (n + 1) →ₗ[ℤ] Formal ι (m + 1))) :
    M.realize P Q (∑ i ∈ s, T i) = ∑ i ∈ s, M.realize P Q (T i) :=
  Sigma.hom_ext _ _ fun a ↦ by
    rw [ι_realize, Preadditive.comp_sum, LinearMap.sum_apply, map_sum]
    exact Finset.sum_congr rfl fun i _ ↦ (ι_realize P Q (T i) a).symm

public theorem realize_id (P : TupleClass ι) {n : ℕ} :
    M.realize P P (LinearMap.id : Formal ι (n + 1) →ₗ[ℤ] Formal ι (n + 1)) = 𝟙 _ :=
  Sigma.hom_ext _ _ fun a ↦ by
    rw [ι_realize, LinearMap.id_apply, realizeAux_single, faceOrZero_self, Category.id_comp,
      Category.comp_id, ιOrZero_of_mem _ a.2]

/-- Realization is compatible with composition of admissible operators. -/
public theorem realize_comp (P Q R : TupleClass ι) {n m k : ℕ}
    {T : Formal ι (n + 1) →ₗ[ℤ] Formal ι (m + 1)} (hT : Admissible P Q T)
    {S : Formal ι (m + 1) →ₗ[ℤ] Formal ι (k + 1)} (hS : Admissible Q R S) :
    M.realize P R (S ∘ₗ T) = M.realize P Q T ≫ M.realize Q R S :=
  Sigma.hom_ext _ _ fun a ↦ by
    rw [ι_realize, ← Category.assoc, ι_realize, LinearMap.comp_apply,
      M.realizeAux_comp_realize a.1 Q R _ (fun b hb ↦ ⟨hT.range_subset a.1 a.2 b hb,
        hT.preserves a.1 a.2 b hb⟩) hS]

variable (M)

omit [LinearOrder ι] in
/-- The alternating boundary is admissible on every class of tuples. -/
public theorem admissible_boundary (P : TupleClass ι) (n : ℕ) :
    Admissible P P (boundary : Formal ι (n + 2) →ₗ[ℤ] Formal ι (n + 1)) where
  range_subset _ _ _ hb := range_subset_of_mem_support_boundary hb
  preserves a ha b hb := by
    obtain ⟨i, rfl⟩ := exists_eq_removeNth_of_mem_support_boundary hb
    exact P.removeNth_mem _ _ i ha

/-- The realized boundary squares to zero. -/
public theorem realize_boundary_realize_boundary (P : TupleClass ι) (n : ℕ) :
    M.realize P P (boundary : Formal ι (n + 3) →ₗ[ℤ] Formal ι (n + 2)) ≫
        M.realize P P (boundary : Formal ι (n + 2) →ₗ[ℤ] Formal ι (n + 1)) = 0 := by
  rw [← M.realize_comp P P P (admissible_boundary P (n + 1)) (admissible_boundary P n)]
  have h : (boundary ∘ₗ boundary : Formal ι (n + 3) →ₗ[ℤ] Formal ι (n + 1)) = 0 :=
    LinearMap.ext fun v ↦ boundary_boundary v
  rw [h, realize_zero]

/-- The alternating-face bicomplex of the local models over a class of tuples, as a chain
complex of chain complexes. -/
public def cechComplex (P : TupleClass ι) :
    HomologicalComplex₂ AddCommGrpCat (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  ChainComplex.of (M.cechObject P)
    (fun n ↦ M.realize P P (boundary : Formal ι (n + 2) →ₗ[ℤ] Formal ι (n + 1)))
    (M.realize_boundary_realize_boundary P)

public theorem cechComplex_X (P : TupleClass ι) (n : ℕ) :
    (M.cechComplex P).X n = M.cechObject P n :=
  rfl

public theorem cechComplex_d (P : TupleClass ι) (n : ℕ) :
    (M.cechComplex P).d (n + 1) n =
      M.realize P P (boundary : Formal ι (n + 2) →ₗ[ℤ] Formal ι (n + 1)) := by
  unfold cechComplex
  exact ChainComplex.of_d (M.cechObject P)
    (fun n ↦ M.realize P P (boundary : Formal ι (n + 2) →ₗ[ℤ] Formal ι (n + 1))) n

/-- The total complex of the ordered Čech bicomplex over a class of tuples. -/
public abbrev cechTotal (P : TupleClass ι) : ChainComplex AddCommGrpCat ℕ :=
  (M.cechComplex P).total (ComplexShape.down ℕ)

/-- Realize a family of admissible formal operators commuting with the boundary on the source
class as a morphism of bicomplexes. -/
public def realizeChainMap (P Q : TupleClass ι)
    (T : ∀ n, Formal ι (n + 1) →ₗ[ℤ] Formal ι (n + 1))
    (hT : ∀ n, Admissible P Q (T n))
    (hcomm : ∀ (n : ℕ) (a : Fin (n + 2) → ι), P.mem (n + 1) a →
      boundary (T (n + 1) (single a 1)) = T n (boundary (single a 1))) :
    M.cechComplex P ⟶ M.cechComplex Q where
  f n := M.realize P Q (T n)
  comm' i j hij := by
    obtain rfl : i = j + 1 := hij.symm
    change M.realize P Q (T (j + 1)) ≫ (M.cechComplex Q).d (j + 1) j =
      (M.cechComplex P).d (j + 1) j ≫ M.realize P Q (T j)
    rw [cechComplex_d, cechComplex_d]
    exact ((M.realize_comp P Q Q (hT (j + 1)) (admissible_boundary Q j)).symm.trans
      (M.realize_congr P Q fun a ha ↦ hcomm j a ha)).trans
        (M.realize_comp P P Q (admissible_boundary P j) (hT j))

public theorem realizeChainMap_f (P Q : TupleClass ι)
    (T : ∀ n, Formal ι (n + 1) →ₗ[ℤ] Formal ι (n + 1))
    (hT : ∀ n, Admissible P Q (T n))
    (hcomm : ∀ (n : ℕ) (a : Fin (n + 2) → ι), P.mem (n + 1) a →
      boundary (T (n + 1) (single a 1)) = T n (boundary (single a 1))) (n : ℕ) :
    (M.realizeChainMap P Q T hT hcomm).f n = M.realize P Q (T n) :=
  rfl

/-- Realized chain maps compose as their formal operators do. -/
public theorem realizeChainMap_comp (P Q R : TupleClass ι)
    (T : ∀ n, Formal ι (n + 1) →ₗ[ℤ] Formal ι (n + 1)) (hT : ∀ n, Admissible P Q (T n))
    (hcommT : ∀ (n : ℕ) (a : Fin (n + 2) → ι), P.mem (n + 1) a →
      boundary (T (n + 1) (single a 1)) = T n (boundary (single a 1)))
    (S : ∀ n, Formal ι (n + 1) →ₗ[ℤ] Formal ι (n + 1)) (hS : ∀ n, Admissible Q R (S n))
    (hcommS : ∀ (n : ℕ) (a : Fin (n + 2) → ι), Q.mem (n + 1) a →
      boundary (S (n + 1) (single a 1)) = S n (boundary (single a 1)))
    (hST : ∀ n, Admissible P R (S n ∘ₗ T n))
    (hcommST : ∀ (n : ℕ) (a : Fin (n + 2) → ι), P.mem (n + 1) a →
      boundary ((S (n + 1) ∘ₗ T (n + 1)) (single a 1)) = (S n ∘ₗ T n) (boundary (single a 1))) :
    M.realizeChainMap P Q T hT hcommT ≫ M.realizeChainMap Q R S hS hcommS =
      M.realizeChainMap P R (fun n ↦ S n ∘ₗ T n) hST hcommST := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, realizeChainMap_f, realizeChainMap_f, realizeChainMap_f]
  exact (M.realize_comp P Q R (hT n) (hS n)).symm

/-- The identity operators realize to the identity of the bicomplex. -/
public theorem realizeChainMap_id (P : TupleClass ι)
    (hT : ∀ n, Admissible P P (LinearMap.id : Formal ι (n + 1) →ₗ[ℤ] Formal ι (n + 1)))
    (hcomm : ∀ (n : ℕ) (a : Fin (n + 2) → ι), P.mem (n + 1) a →
      boundary ((LinearMap.id : Formal ι (n + 2) →ₗ[ℤ] Formal ι (n + 2)) (single a 1)) =
        (LinearMap.id : Formal ι (n + 1) →ₗ[ℤ] Formal ι (n + 1)) (boundary (single a 1))) :
    M.realizeChainMap P P (fun _ ↦ LinearMap.id) hT hcomm = 𝟙 _ := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.id_f, realizeChainMap_f]
  exact M.realize_id P

/-- The components of a realized chain homotopy: the realized formal homotopy in degree `i`,
placed in the slot `(i, i + 1)`. -/
public def realizeHomotopyHom (P Q : TupleClass ι)
    (h : ∀ n, Formal ι (n + 1) →ₗ[ℤ] Formal ι (n + 2)) (i j : ℕ) :
    (M.cechComplex P).X i ⟶ (M.cechComplex Q).X j :=
  if hij : i + 1 = j then by subst hij; exact M.realize P Q (h i) else 0

public theorem realizeHomotopyHom_succ (P Q : TupleClass ι)
    (h : ∀ n, Formal ι (n + 1) →ₗ[ℤ] Formal ι (n + 2)) (i : ℕ) :
    M.realizeHomotopyHom P Q h i (i + 1) = M.realize P Q (h i) := by
  unfold realizeHomotopyHom
  exact dite_eq_left rfl

public theorem realizeHomotopyHom_of_ne (P Q : TupleClass ι)
    (h : ∀ n, Formal ι (n + 1) →ₗ[ℤ] Formal ι (n + 2)) {i j : ℕ} (hij : i + 1 ≠ j) :
    M.realizeHomotopyHom P Q h i j = 0 := by
  unfold realizeHomotopyHom
  exact dite_eq_right hij

/-- Realize a family of admissible formal homotopies satisfying the signed homotopy identity on
the source class as a chain homotopy between realized chain maps. -/
public def realizeHomotopy (P Q : TupleClass ι)
    {T T' : ∀ n, Formal ι (n + 1) →ₗ[ℤ] Formal ι (n + 1)}
    {hT : ∀ n, Admissible P Q (T n)} {hT' : ∀ n, Admissible P Q (T' n)}
    {hcomm : ∀ (n : ℕ) (a : Fin (n + 2) → ι), P.mem (n + 1) a →
      boundary (T (n + 1) (single a 1)) = T n (boundary (single a 1))}
    {hcomm' : ∀ (n : ℕ) (a : Fin (n + 2) → ι), P.mem (n + 1) a →
      boundary (T' (n + 1) (single a 1)) = T' n (boundary (single a 1))}
    (h : ∀ n, Formal ι (n + 1) →ₗ[ℤ] Formal ι (n + 2))
    (hh : ∀ n, Admissible P Q (h n))
    (hident : ∀ (n : ℕ) (a : Fin (n + 2) → ι), P.mem (n + 1) a →
      boundary (h (n + 1) (single a 1)) + h n (boundary (single a 1)) =
        T (n + 1) (single a 1) - T' (n + 1) (single a 1))
    (hzero : ∀ a : Fin 1 → ι, P.mem 0 a →
      boundary (h 0 (single a 1)) = T 0 (single a 1) - T' 0 (single a 1)) :
    Homotopy (M.realizeChainMap P Q T hT hcomm) (M.realizeChainMap P Q T' hT' hcomm') where
  hom := M.realizeHomotopyHom P Q h
  zero i j hij := M.realizeHomotopyHom_of_ne P Q h hij
  comm i := by
    cases i with
    | zero =>
      rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex, zero_add,
        realizeHomotopyHom_succ, realizeChainMap_f, realizeChainMap_f, cechComplex_d]
      have e : M.realize P Q (T 0) =
          M.realize P Q (boundary ∘ₗ h 0) + M.realize P Q (T' 0) := by
        rw [← realize_add]
        exact M.realize_congr P Q fun a ha ↦ by
          have := hzero a ha
          rw [eq_sub_iff_add_eq] at this
          simp only [LinearMap.add_apply, LinearMap.comp_apply]
          exact this.symm
      rw [e, M.realize_comp P Q Q (hh 0) (admissible_boundary Q 0)]
      rfl
    | succ k =>
      rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex, realizeHomotopyHom_succ,
        realizeHomotopyHom_succ, realizeChainMap_f, realizeChainMap_f, cechComplex_d,
        cechComplex_d]
      have e : M.realize P Q (T (k + 1)) =
          M.realize P Q (h k ∘ₗ boundary) + M.realize P Q (boundary ∘ₗ h (k + 1)) +
            M.realize P Q (T' (k + 1)) := by
        rw [← realize_add, ← realize_add]
        exact M.realize_congr P Q fun a ha ↦ by
          have := hident k a ha
          rw [eq_sub_iff_add_eq] at this
          simp only [LinearMap.add_apply, LinearMap.comp_apply]
          rw [← this]
          abel
      rw [e, M.realize_comp P P Q (admissible_boundary P k) (hh k),
        M.realize_comp P Q Q (hh (k + 1)) (admissible_boundary Q (k + 1))]
      rfl

end SupportChainModels

end SphereSixComplex
