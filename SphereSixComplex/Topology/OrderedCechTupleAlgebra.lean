module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.Lattice
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Module

/-!
# Formal algebra of ordered Čech tuples

The ordered Čech complex of a cover indexed by a totally ordered type `ι` has one summand for
every tuple `Fin (n + 1) → ι`, and all of its structure maps are signed sums of face maps.  This
file isolates the purely combinatorial part: the free abelian groups on tuples of every length,
the operators `cons`, faces and the alternating boundary, and the two contractions of the
Stacks Project (Tag 01FM, `lemma-alternating-usual`) which compare the full complex with the
semi-ordered complex (weakly increasing tuples) and the ordered complex (strictly increasing
tuples).

Both operators are defined by recursion on the length of a tuple: the sort-with-sign operator
`κ` and its homotopy peel off the first occurrence of the minimum, and the first-repetition
operator duplicates the head when it repeats and otherwise recurses along the tail.  These
recursions unfold to the closed formulas of the source, and the two chain-homotopy identities are
proved by induction on the length using the cone identity `∂ (x :: v) = v - x :: ∂ v`.

No chain complexes of local models appear here; realizing these operators on coproducts of local
models is done in `SphereSixComplex.Topology.OrderedCechRealization`.
-/

@[expose] public section

noncomputable section

open Finsupp

namespace SphereSixComplex

namespace OrderedCechTuple

variable {ι : Type} {n : ℕ}

/-- Formal integer combinations of ordered tuples of length `n`. -/
public abbrev Formal (ι : Type) (n : ℕ) := (Fin n → ι) →₀ ℤ

/-- Prepend a fixed index to every tuple. -/
public def consMap (x : ι) : Formal ι n →ₗ[ℤ] Formal ι (n + 1) :=
  Finsupp.lmapDomain ℤ ℤ (fun b : Fin n → ι ↦ Fin.cons x b)

/-- Delete the `i`-th entry of every tuple. -/
public def faceMap (i : Fin (n + 1)) : Formal ι (n + 1) →ₗ[ℤ] Formal ι n :=
  Finsupp.lmapDomain ℤ ℤ (Fin.removeNth i)

/-- The alternating boundary, including the augmentation `Formal ι 1 → Formal ι 0`. -/
public def boundary : Formal ι (n + 1) →ₗ[ℤ] Formal ι n :=
  ∑ i : Fin (n + 1), ((-1 : ℤ) ^ i.val) • faceMap i

public theorem consMap_single (x : ι) (a : Fin n → ι) (z : ℤ) :
    consMap x (single a z) = single (Fin.cons x a) z := by
  simp [consMap, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

public theorem faceMap_single (i : Fin (n + 1)) (a : Fin (n + 1) → ι) (z : ℤ) :
    faceMap i (single a z) = single (Fin.removeNth i a) z := by
  simp [faceMap, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

public theorem boundary_single (a : Fin (n + 1) → ι) (z : ℤ) :
    boundary (single a z) = ∑ i : Fin (n + 1), single (Fin.removeNth i a) ((-1 : ℤ) ^ i.val * z) := by
  simp [boundary, LinearMap.sum_apply, faceMap_single, Finsupp.smul_single]

public theorem removeNth_zero_cons (x : ι) (a : Fin n → ι) :
    Fin.removeNth (α := fun _ ↦ ι) 0 (Fin.cons x a) = a := by
  ext k
  simp [Fin.removeNth_apply]

public theorem removeNth_succ_cons (x : ι) (a : Fin (n + 1) → ι) (j : Fin (n + 1)) :
    Fin.removeNth (α := fun _ ↦ ι) j.succ (Fin.cons x a) =
      Fin.cons x (Fin.removeNth (α := fun _ ↦ ι) j a) := by
  ext k
  refine Fin.cases ?_ (fun k ↦ ?_) k
  · simp [Fin.removeNth_apply]
  · simp [Fin.removeNth_apply, Fin.succ_succAbove_succ]

/-- The cone identity: the boundary of a coned tuple is the tuple minus the cone on its
boundary. -/
public theorem boundary_consMap (x : ι) (v : Formal ι (n + 1)) :
    boundary (consMap x v) = v - consMap x (boundary v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]; exact sub_add_sub_comm _ _ _ _
  | single a z =>
    rw [consMap_single, boundary_single, boundary_single, map_sum, Fin.sum_univ_succ,
      removeNth_zero_cons, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    · simp
    · refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [consMap_single, removeNth_succ_cons, ← Finsupp.single_neg, Fin.val_succ, pow_succ]
      congr 1
      ring

/-- The cone identity in the lowest degree, where the augmentation absorbs the second term. -/
public theorem boundary_consMap_zero (x : ι) (v : Formal ι 0) :
    boundary (consMap x v) = v := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, map_add, hf, hg]
  | single a z =>
    rw [consMap_single, boundary_single, Fin.sum_univ_one, removeNth_zero_cons]
    simp

public theorem boundary_boundary (v : Formal ι (n + 2)) :
    boundary (boundary v) = 0 := by
  induction n with
  | zero =>
    induction v using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => rw [map_add, map_add, hf, hg, add_zero]
    | single a z =>
      rw [← Fin.cons_self_tail a, ← consMap_single, boundary_consMap, map_sub,
        boundary_consMap_zero, sub_self]
  | succ n ih =>
    induction v using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => rw [map_add, map_add, hf, hg, add_zero]
    | single a z =>
      rw [← Fin.cons_self_tail a, ← consMap_single, boundary_consMap, map_sub, boundary_consMap,
        ih, map_zero, sub_zero, sub_self]

/-- Every tuple occurring in the boundary of `a` is a face of `a`. -/
public theorem exists_eq_removeNth_of_mem_support_boundary {a : Fin (n + 1) → ι} {b : Fin n → ι}
    (hb : b ∈ (boundary (single a 1)).support) : ∃ i, b = Fin.removeNth i a := by
  classical
  rw [boundary_single] at hb
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 (Finsupp.support_finsetSum hb)
  exact ⟨i, Finset.mem_singleton.1 (Finsupp.support_single_subset hi)⟩

/-- The support of every tuple in the boundary of `a` is contained in the support of `a`. -/
public theorem range_subset_of_mem_support_boundary {a : Fin (n + 1) → ι} {b : Fin n → ι}
    (hb : b ∈ (boundary (single a 1)).support) : Set.range b ⊆ Set.range a := by
  obtain ⟨i, rfl⟩ := exists_eq_removeNth_of_mem_support_boundary hb
  exact Set.range_comp_subset_range i.succAbove a

variable [LinearOrder ι]

/-- Tuples occurring in the image of `consMap x` are cons-tuples. -/
public theorem exists_eq_cons_of_mem_support_consMap {x : ι} {w : Formal ι n} {b : Fin (n + 1) → ι}
    (hb : b ∈ (consMap x w).support) : ∃ b' ∈ w.support, b = Fin.cons x b' := by
  classical
  obtain ⟨b', hb', rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hb)
  exact ⟨b', hb', rfl⟩

omit [LinearOrder ι] in
public theorem removeNth_zero_eq_tail (a : Fin (n + 1) → ι) :
    Fin.removeNth (α := fun _ ↦ ι) 0 a = Fin.tail a := by
  ext k
  simp [Fin.removeNth_apply, Fin.tail]

public theorem monotone_cons {x : ι} {b : Fin n → ι} (hx : ∀ i, x ≤ b i) (hb : Monotone b) :
    Monotone (Fin.cons x b : Fin (n + 1) → ι) := by
  intro i j hij
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => exact le_rfl
    | succ j => simpa using hx j
  | succ i =>
    induction j using Fin.cases with
    | zero => exact absurd hij (not_le.2 (Fin.succ_pos i))
    | succ j => simpa using hb (Fin.succ_le_succ_iff.1 hij)

public theorem monotone_of_mem_support_boundary {a : Fin (n + 1) → ι} (ha : Monotone a)
    {b : Fin n → ι} (hb : b ∈ (boundary (single a 1)).support) : Monotone b := by
  obtain ⟨i, rfl⟩ := exists_eq_removeNth_of_mem_support_boundary hb
  exact ha.comp (Fin.strictMono_succAbove i).monotone

public theorem strictMono_of_mem_support_boundary {a : Fin (n + 1) → ι} (ha : StrictMono a)
    {b : Fin n → ι} (hb : b ∈ (boundary (single a 1)).support) : StrictMono b := by
  obtain ⟨i, rfl⟩ := exists_eq_removeNth_of_mem_support_boundary hb
  exact ha.comp (Fin.strictMono_succAbove i)

/-! ### The stable minimum -/

/-- The first position at which a tuple attains its minimum. -/
public def minIndex (a : Fin (n + 1) → ι) : Fin (n + 1) :=
  Fin.find (fun j ↦ ∀ k, a j ≤ a k) (Finite.exists_min a)

public theorem minIndex_le (a : Fin (n + 1) → ι) (k : Fin (n + 1)) : a (minIndex a) ≤ a k :=
  Fin.find_spec (Finite.exists_min a) k

public theorem lt_of_lt_minIndex {a : Fin (n + 1) → ι} {j : Fin (n + 1)} (h : j < minIndex a) :
    a (minIndex a) < a j := by
  obtain ⟨k, hk⟩ := not_forall.1 (Fin.find_min (Finite.exists_min a) h)
  exact (minIndex_le a k).trans_lt (not_le.1 hk)

public theorem minIndex_eq_iff {a : Fin (n + 1) → ι} {j : Fin (n + 1)} :
    minIndex a = j ↔ (∀ k, a j ≤ a k) ∧ ∀ i < j, a j < a i := by
  rw [minIndex, Fin.find_eq_iff]
  constructor
  · rintro ⟨hj, hmin⟩
    refine ⟨hj, fun i hi ↦ ?_⟩
    obtain ⟨k, hk⟩ := not_forall.1 (hmin i hi)
    exact (hj k).trans_lt (not_le.1 hk)
  · rintro ⟨hj, hlt⟩
    exact ⟨hj, fun i hi hall ↦ not_le.2 (hlt i hi) (hall j)⟩

public theorem minIndex_of_monotone {a : Fin (n + 1) → ι} (ha : Monotone a) : minIndex a = 0 :=
  minIndex_eq_iff.2 ⟨fun k ↦ ha (Fin.zero_le k), fun i hi ↦ absurd hi (Fin.not_lt_zero i)⟩

public theorem removeNth_succAbove_apply_predAbove (a : Fin (n + 2) → ι) (k : Fin (n + 1)) :
    Fin.removeNth ((minIndex a).succAbove k) a (k.predAbove (minIndex a)) = a (minIndex a) := by
  rw [Fin.removeNth_apply, Fin.succAbove_succAbove_predAbove]

/-- Deleting an entry other than the stable minimum keeps the stable minimum, at the position
predicted by `Fin.succAbove_succAbove_predAbove`. -/
public theorem minIndex_removeNth_succAbove (a : Fin (n + 2) → ι) (k : Fin (n + 1)) :
    minIndex (Fin.removeNth ((minIndex a).succAbove k) a) = k.predAbove (minIndex a) := by
  rw [minIndex_eq_iff]
  refine ⟨fun k' ↦ ?_, fun i hi ↦ ?_⟩
  · rw [removeNth_succAbove_apply_predAbove, Fin.removeNth_apply]
    exact minIndex_le a _
  · rw [removeNth_succAbove_apply_predAbove, Fin.removeNth_apply]
    apply lt_of_lt_minIndex
    calc ((minIndex a).succAbove k).succAbove i
        < ((minIndex a).succAbove k).succAbove (k.predAbove (minIndex a)) :=
          Fin.strictMono_succAbove _ hi
      _ = minIndex a := Fin.succAbove_succAbove_predAbove _ _

omit [LinearOrder ι] in
/-- The simplicial identity in `removeNth` form, oriented for the cone recursion. -/
public theorem removeNth_predAbove_removeNth_succAbove (a : Fin (n + 2) → ι) (j : Fin (n + 2))
    (k : Fin (n + 1)) :
    Fin.removeNth (k.predAbove j) (Fin.removeNth (j.succAbove k) a) =
      Fin.removeNth k (Fin.removeNth j a) :=
  (Fin.removeNth_removeNth_eq_swap a k j).symm

/-- The sign bookkeeping for the simplicial identity. -/
public theorem neg_one_pow_succAbove_add_predAbove (j : Fin (n + 2)) (k : Fin (n + 1)) :
    (-1 : ℤ) ^ ((j.succAbove k).val + (k.predAbove j).val) = -(-1) ^ (j.val + k.val) := by
  rcases lt_or_ge k.castSucc j with h | h
  · rw [Fin.succAbove_of_castSucc_lt _ _ h, Fin.predAbove_of_castSucc_lt _ _ h, Fin.val_castSucc,
      Fin.val_pred]
    have hj : k.val < j.val := by simpa [Fin.lt_def] using h
    rw [show j.val + k.val = k.val + (j.val - 1) + 1 by omega, pow_succ]
    ring
  · rw [Fin.succAbove_of_le_castSucc _ _ h, Fin.predAbove_of_le_castSucc _ _ h, Fin.val_succ,
      Fin.coe_castPred]
    rw [show k.val + 1 + j.val = j.val + k.val + 1 by omega, pow_succ]
    ring

/-! ### Sorting with sign -/

/-- The sort-with-sign operator `κ` of Stacks 01FM: a tuple is sent to its stable sorting, with
the sign of the sorting permutation.  It is defined by peeling off the stable minimum. -/
public def sortWithSign : ∀ n, Formal ι n →ₗ[ℤ] Formal ι n
  | 0 => LinearMap.id
  | n + 1 => Finsupp.linearCombination ℤ fun a ↦
      ((-1 : ℤ) ^ (minIndex a).val) •
        consMap (a (minIndex a)) (sortWithSign n (single (Fin.removeNth (minIndex a) a) 1))

/-- The homotopy `h` of Stacks 01FM (`equation-first-homotopy`) in cone-recursive form. -/
public def sortHomotopy : ∀ n, Formal ι n →ₗ[ℤ] Formal ι (n + 1)
  | 0 => 0
  | n + 1 => Finsupp.linearCombination ℤ fun a ↦
      consMap (a (minIndex a)) (single a 1) -
        ((-1 : ℤ) ^ (minIndex a).val) •
          consMap (a (minIndex a)) (sortHomotopy n (single (Fin.removeNth (minIndex a) a) 1))

public theorem sortWithSign_single_succ (a : Fin (n + 1) → ι) :
    sortWithSign (n + 1) (single a 1) =
      ((-1 : ℤ) ^ (minIndex a).val) •
        consMap (a (minIndex a)) (sortWithSign n (single (Fin.removeNth (minIndex a) a) 1)) := by
  simp only [sortWithSign, Finsupp.linearCombination_single, one_smul]

public theorem sortHomotopy_single_succ (a : Fin (n + 1) → ι) :
    sortHomotopy (n + 1) (single a 1) =
      consMap (a (minIndex a)) (single a 1) -
        ((-1 : ℤ) ^ (minIndex a).val) •
          consMap (a (minIndex a)) (sortHomotopy n (single (Fin.removeNth (minIndex a) a) 1)) := by
  simp only [sortHomotopy, Finsupp.linearCombination_single, one_smul]

public theorem sortWithSign_single_one (a : Fin 1 → ι) : sortWithSign 1 (single a 1) = single a 1 := by
  rw [sortWithSign_single_succ, Fin.fin_one_eq_zero (minIndex a), Fin.val_zero, pow_zero, one_smul,
    removeNth_zero_eq_tail]
  change consMap (a 0) (single (Fin.tail a) 1) = _
  rw [consMap_single, Fin.cons_self_tail]

public theorem sortWithSign_one (v : Formal ι 1) : sortWithSign 1 v = v := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, hf, hg]
  | single a z => rw [← Finsupp.smul_single_one a z, map_smul, sortWithSign_single_one]

omit [LinearOrder ι] in
/-- The boundary of a tuple, split at an arbitrary position. -/
public theorem boundary_single_eq_succAbove (a : Fin (n + 2) → ι) (j : Fin (n + 2)) :
    boundary (single a 1) =
      ((-1 : ℤ) ^ j.val) • single (Fin.removeNth j a) 1 +
        ∑ k : Fin (n + 1),
          ((-1 : ℤ) ^ (j.succAbove k).val) • single (Fin.removeNth (j.succAbove k) a) 1 := by
  rw [boundary_single, Fin.sum_univ_succAbove _ j]
  simp only [mul_one, Finsupp.smul_single_one]

/-- The sort homotopy on a face of `a` not at the stable minimum, expressed through the faces of
`a` with its stable minimum removed. -/
public theorem sortHomotopy_single_removeNth_succAbove (a : Fin (n + 2) → ι) (k : Fin (n + 1)) :
    sortHomotopy (n + 1) (single (Fin.removeNth ((minIndex a).succAbove k) a) 1) =
      consMap (a (minIndex a)) (single (Fin.removeNth ((minIndex a).succAbove k) a) 1) -
        ((-1 : ℤ) ^ (k.predAbove (minIndex a)).val) •
          consMap (a (minIndex a))
            (sortHomotopy n (single (Fin.removeNth k (Fin.removeNth (minIndex a) a)) 1)) := by
  rw [sortHomotopy_single_succ, minIndex_removeNth_succAbove, removeNth_succAbove_apply_predAbove,
    removeNth_predAbove_removeNth_succAbove]

/-- The first homotopy identity of Stacks 01FM on basis tuples. -/
public theorem boundary_sortHomotopy_add_single (a : Fin (n + 1) → ι) :
    boundary (sortHomotopy (n + 1) (single a 1)) + sortHomotopy n (boundary (single a 1)) =
      single a 1 - sortWithSign (n + 1) (single a 1) := by
  induction n with
  | zero =>
    have hmin : minIndex a = 0 := Fin.fin_one_eq_zero _
    rw [sortHomotopy_single_succ, sortWithSign_single_one, hmin,
      show sortHomotopy 0 = (0 : Formal ι 0 →ₗ[ℤ] Formal ι 1) from rfl, LinearMap.zero_apply,
      LinearMap.zero_apply, map_zero, smul_zero, sub_zero, add_zero, boundary_consMap,
      boundary_single, Fin.sum_univ_one, Fin.val_zero, pow_zero, one_mul, removeNth_zero_eq_tail,
      consMap_single, Fin.cons_self_tail, sub_self]
  | succ n ih =>
    set j₀ := minIndex a with hj₀
    set m := a j₀ with hm
    set s : ℤ := (-1) ^ j₀.val with hs
    set a' := Fin.removeNth j₀ a with ha'
    have hkey : sortHomotopy (n + 1) (boundary (single a 1)) =
        s • sortHomotopy (n + 1) (single a' 1) + consMap m (boundary (single a 1)) -
          s • consMap m (single a' 1) + s • consMap m (sortHomotopy n (boundary (single a' 1))) := by
      have hsplit := boundary_single_eq_succAbove a j₀
      conv_lhs => rw [hsplit]
      rw [map_add, map_smul, map_sum]
      have hterm : ∀ k : Fin (n + 1),
          sortHomotopy (n + 1)
              (((-1 : ℤ) ^ (j₀.succAbove k).val) •
                single (Fin.removeNth (j₀.succAbove k) a) 1) =
            ((-1 : ℤ) ^ (j₀.succAbove k).val) •
                consMap m (single (Fin.removeNth (j₀.succAbove k) a) 1) +
              (s * (-1) ^ k.val) •
                consMap m (sortHomotopy n (single (Fin.removeNth k a') 1)) := by
        intro k
        rw [map_smul, sortHomotopy_single_removeNth_succAbove, ← hj₀, ← hm, ← ha', smul_sub,
          smul_smul, ← pow_add, neg_one_pow_succAbove_add_predAbove, pow_add, ← hs, neg_smul,
          sub_neg_eq_add]
      rw [Finset.sum_congr rfl fun k _ ↦ hterm k, Finset.sum_add_distrib]
      have hsum1 : ∑ k : Fin (n + 1),
          ((-1 : ℤ) ^ (j₀.succAbove k).val) •
            consMap m (single (Fin.removeNth (j₀.succAbove k) a) 1) =
          consMap m (boundary (single a 1)) - s • consMap m (single a' 1) := by
        rw [hsplit, map_add, map_smul, map_sum, add_sub_cancel_left]
        simp only [map_smul]
      have hsum2 : ∑ k : Fin (n + 1),
          (s * (-1) ^ k.val) • consMap m (sortHomotopy n (single (Fin.removeNth k a') 1)) =
          s • consMap m (sortHomotopy n (boundary (single a' 1))) := by
        rw [boundary_single, map_sum, map_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        rw [mul_one, ← Finsupp.smul_single_one (Fin.removeNth k a') ((-1 : ℤ) ^ k.val), map_smul,
          map_smul, smul_smul]
      rw [hsum1, hsum2, ← hs, ← ha']
      abel
    rw [sortHomotopy_single_succ, sortWithSign_single_succ, ← hj₀, ← hm, ← hs, ← ha', map_sub,
      map_smul, boundary_consMap, boundary_consMap, hkey]
    have hih := congrArg (consMap m) (ih a')
    rw [map_add, map_sub] at hih
    rw [← sub_eq_zero]
    calc _ = s • (consMap m (boundary (sortHomotopy (n + 1) (single a' 1))) +
          consMap m (sortHomotopy n (boundary (single a' 1)))) -
            s • (consMap m (single a' 1) - consMap m (sortWithSign (n + 1) (single a' 1))) := by
          simp only [smul_sub, smul_add]
          abel
      _ = 0 := by rw [hih, sub_self]

/-- The first homotopy identity of Stacks 01FM: `∂ h + h ∂ = 1 - κ`. -/
public theorem boundary_sortHomotopy_add (v : Formal ι (n + 1)) :
    boundary (sortHomotopy (n + 1) v) + sortHomotopy n (boundary v) =
      v - sortWithSign (n + 1) v := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    simp only [map_add]
    rw [add_add_add_comm, hf, hg]
    abel
  | single a z =>
    rw [← Finsupp.smul_single_one a z]
    simp only [map_smul]
    rw [← smul_add, ← smul_sub, boundary_sortHomotopy_add_single]

/-- `κ` is a chain map. -/
public theorem boundary_sortWithSign (v : Formal ι (n + 1)) :
    boundary (sortWithSign (n + 1) v) = sortWithSign n (boundary v) := by
  cases n with
  | zero => rw [sortWithSign_one]; rfl
  | succ n =>
    have h1 := congrArg boundary (boundary_sortHomotopy_add v)
    have h2 := boundary_sortHomotopy_add (boundary v)
    rw [map_add, map_sub, boundary_boundary, zero_add] at h1
    rw [boundary_boundary, map_zero, add_zero] at h2
    rw [h2] at h1
    exact (sub_right_inj.1 h1).symm

public theorem sortWithSign_single_of_monotone {a : Fin (n + 1) → ι} (ha : Monotone a) :
    sortWithSign (n + 1) (single a 1) = single a 1 := by
  induction n with
  | zero => exact sortWithSign_single_one a
  | succ n ih =>
    rw [sortWithSign_single_succ, minIndex_of_monotone ha, Fin.val_zero, pow_zero, one_smul,
      removeNth_zero_eq_tail, ih (a := Fin.tail a) (fun i j h ↦ ha (Fin.succ_le_succ_iff.2 h)),
      consMap_single, Fin.cons_self_tail]

public theorem range_subset_of_mem_support_sortWithSign {a b : Fin (n + 1) → ι}
    (hb : b ∈ (sortWithSign (n + 1) (single a 1)).support) : Set.range b ⊆ Set.range a := by
  induction n with
  | zero =>
    rw [sortWithSign_single_one] at hb
    rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hb)]
  | succ n ih =>
    rw [sortWithSign_single_succ] at hb
    obtain ⟨b', hb', rfl⟩ := exists_eq_cons_of_mem_support_consMap (Finsupp.support_smul hb)
    rw [Fin.range_cons]
    exact Set.union_subset (Set.singleton_subset_iff.2 ⟨_, rfl⟩)
      ((ih hb').trans (Set.range_comp_subset_range _ _))

public theorem monotone_of_mem_support_sortWithSign {a b : Fin (n + 1) → ι}
    (hb : b ∈ (sortWithSign (n + 1) (single a 1)).support) : Monotone b := by
  induction n with
  | zero =>
    intro i j _
    rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j]
  | succ n ih =>
    rw [sortWithSign_single_succ] at hb
    obtain ⟨b', hb', rfl⟩ := exists_eq_cons_of_mem_support_consMap (Finsupp.support_smul hb)
    refine monotone_cons (fun i ↦ ?_) (ih hb')
    obtain ⟨k, hk⟩ := (range_subset_of_mem_support_sortWithSign hb').trans
      (Set.range_comp_subset_range _ _) ⟨i, rfl⟩
    rw [← hk]
    exact minIndex_le a k

public theorem range_subset_of_mem_support_sortHomotopy {a : Fin (n + 1) → ι}
    {b : Fin (n + 2) → ι} (hb : b ∈ (sortHomotopy (n + 1) (single a 1)).support) :
    Set.range b ⊆ Set.range a := by
  induction n with
  | zero =>
    rw [sortHomotopy_single_succ] at hb
    change b ∈ (consMap _ (single a 1) - _ • consMap _ ((0 : Formal ι 0 →ₗ[ℤ] Formal ι 1) _)).support
      at hb
    rw [LinearMap.zero_apply, map_zero, smul_zero, sub_zero] at hb
    obtain ⟨b', hb', rfl⟩ := exists_eq_cons_of_mem_support_consMap hb
    rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hb'), Fin.range_cons]
    exact Set.union_subset (Set.singleton_subset_iff.2 ⟨_, rfl⟩) subset_rfl
  | succ n ih =>
    rw [sortHomotopy_single_succ] at hb
    rcases Finset.mem_union.1 (Finsupp.support_sub hb) with hb | hb
    · obtain ⟨b', hb', rfl⟩ := exists_eq_cons_of_mem_support_consMap hb
      rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hb'), Fin.range_cons]
      exact Set.union_subset (Set.singleton_subset_iff.2 ⟨_, rfl⟩) subset_rfl
    · obtain ⟨b', hb', rfl⟩ := exists_eq_cons_of_mem_support_consMap (Finsupp.support_smul hb)
      rw [Fin.range_cons]
      exact Set.union_subset (Set.singleton_subset_iff.2 ⟨_, rfl⟩)
        ((ih hb').trans (Set.range_comp_subset_range _ _))

/-! ### The first-repetition operator -/

open scoped Classical in
/-- Kill every tuple which is not strictly increasing. -/
public def strictProjection (n : ℕ) : Formal ι n →ₗ[ℤ] Formal ι n :=
  Finsupp.linearCombination ℤ fun a ↦ if StrictMono a then single a 1 else 0

open scoped Classical in
/-- The first-repetition operator of Stacks 01FM (`equation-second-homotopy`) in recursive form:
duplicate the head when it repeats, otherwise recurse along the tail with a sign. -/
public def firstRepeatHomotopy : ∀ n, Formal ι n →ₗ[ℤ] Formal ι (n + 1)
  | 0 => 0
  | 1 => 0
  | n + 2 => Finsupp.linearCombination ℤ fun a ↦
      if a 0 = a 1 then consMap (a 0) (single a 1)
      else -consMap (a 0) (firstRepeatHomotopy (n + 1) (single (Fin.tail a) 1))

public theorem strictProjection_single_of_strictMono {a : Fin n → ι} (ha : StrictMono a) :
    strictProjection n (single a 1) = single a 1 := by
  simp [strictProjection, Finsupp.linearCombination_single, ha]

public theorem strictProjection_single_of_not_strictMono {a : Fin n → ι} (ha : ¬ StrictMono a) :
    strictProjection n (single a 1) = 0 := by
  simp [strictProjection, Finsupp.linearCombination_single, ha]

public theorem firstRepeatHomotopy_single_of_eq {a : Fin (n + 2) → ι} (h : a 0 = a 1) :
    firstRepeatHomotopy (n + 2) (single a 1) = consMap (a 0) (single a 1) := by
  simp only [firstRepeatHomotopy, Finsupp.linearCombination_single, one_smul, ite_eq_left h]

public theorem firstRepeatHomotopy_single_of_ne {a : Fin (n + 2) → ι} (h : a 0 ≠ a 1) :
    firstRepeatHomotopy (n + 2) (single a 1) =
      -consMap (a 0) (firstRepeatHomotopy (n + 1) (single (Fin.tail a) 1)) := by
  simp only [firstRepeatHomotopy, Finsupp.linearCombination_single, one_smul, ite_eq_right h]

public theorem strictMono_cons {x : ι} {b : Fin n → ι} (hx : ∀ i, x < b i) (hb : StrictMono b) :
    StrictMono (Fin.cons x b : Fin (n + 1) → ι) := by
  intro i j hij
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => exact absurd hij (lt_irrefl _)
    | succ j => simpa using hx j
  | succ i =>
    induction j using Fin.cases with
    | zero => exact absurd hij (Fin.not_lt_zero _)
    | succ j => simpa using hb (Fin.succ_lt_succ_iff.1 hij)

public theorem strictMono_of_strictMono_cons {x : ι} {b : Fin n → ι}
    (h : StrictMono (Fin.cons x b : Fin (n + 1) → ι)) : StrictMono b := fun i j hij ↦ by
  simpa using h (Fin.succ_lt_succ_iff.2 hij)

public theorem not_strictMono_of_eq {a : Fin (n + 2) → ι} (h : a 0 = a 1) : ¬ StrictMono a :=
  fun hs ↦ (hs (show (0 : Fin (n + 2)) < 1 from Fin.zero_lt_one)).ne h

public theorem strictMono_fin_one (a : Fin 1 → ι) : StrictMono a :=
  Fin.strictMono_iff_lt_succ.2 fun i ↦ i.elim0

omit [LinearOrder ι] in
public theorem cons_cons_apply_one (x : ι) (c : Fin n → ι) :
    (Fin.cons x (Fin.cons x c) : Fin (n + 2) → ι) 1 = x := by
  rw [show (1 : Fin (n + 2)) = Fin.succ 0 from rfl, Fin.cons_succ, Fin.cons_zero]

/-- Killing repetitions kills every tuple starting with a repeated head. -/
public theorem strictProjection_consMap_consMap (x : ι) (w : Formal ι n) :
    strictProjection (n + 2) (consMap x (consMap x w)) = 0 := by
  induction w using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, map_add, map_add, hf, hg, add_zero]
  | single c z =>
    rw [consMap_single, consMap_single, ← Finsupp.smul_single_one, map_smul,
      strictProjection_single_of_not_strictMono
        (not_strictMono_of_eq ((Fin.cons_zero _ _).trans (cons_cons_apply_one x c).symm)),
      smul_zero]

/-- The first-repetition operator duplicates a repeated head. -/
public theorem firstRepeatHomotopy_consMap_consMap (x : ι) (w : Formal ι n) :
    firstRepeatHomotopy (n + 2) (consMap x (consMap x w)) =
      consMap x (consMap x (consMap x w)) := by
  induction w using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single c z =>
    rw [consMap_single, consMap_single, ← Finsupp.smul_single_one, map_smul,
      firstRepeatHomotopy_single_of_eq ((Fin.cons_zero _ _).trans (cons_cons_apply_one x c).symm),
      Fin.cons_zero, map_smul, consMap_single]

/-- Killing repetitions commutes with prepending a strictly smaller head. -/
public theorem strictProjection_consMap_of_lt (x : ι) (w : Formal ι n)
    (hw : ∀ c ∈ w.support, ∀ i, x < c i) :
    strictProjection (n + 1) (consMap x w) = consMap x (strictProjection n w) := by
  induction w using Finsupp.induction with
  | zero => simp
  | single_add c z f hc hz ih =>
    have hsupp : (single c z + f).support = {c} ∪ f.support := by
      rw [Finsupp.support_add_eq, Finsupp.support_single c hz]
      rw [Finsupp.support_single c hz]
      exact Finset.disjoint_singleton_left.2 hc
    have hc' : ∀ i, x < c i :=
      hw c (by rw [hsupp]; exact Finset.mem_union_left _ (Finset.mem_singleton_self c))
    have hcf : ∀ d ∈ f.support, ∀ i, x < d i := fun d hd ↦
      hw d (by rw [hsupp]; exact Finset.mem_union_right _ hd)
    have hsingle : strictProjection (n + 1) (consMap x (single c z)) =
        consMap x (strictProjection n (single c z)) := by
      rw [consMap_single, ← Finsupp.smul_single_one c z,
        ← Finsupp.smul_single_one (Fin.cons (α := fun _ ↦ ι) x c) z, map_smul, map_smul, map_smul]
      by_cases hs : StrictMono c
      · rw [strictProjection_single_of_strictMono hs,
          strictProjection_single_of_strictMono (strictMono_cons hc' hs), consMap_single]
      · rw [strictProjection_single_of_not_strictMono hs,
          strictProjection_single_of_not_strictMono (fun h ↦ hs (strictMono_of_strictMono_cons h)),
          map_zero]
    simp only [map_add, hsingle, ih hcf]

/-- The first-repetition operator commutes with prepending a strictly smaller head, up to sign. -/
public theorem firstRepeatHomotopy_consMap_of_lt (x : ι) (w : Formal ι n)
    (hw : ∀ c ∈ w.support, ∀ i, x < c i) :
    firstRepeatHomotopy (n + 1) (consMap x w) = -consMap x (firstRepeatHomotopy n w) := by
  cases n with
  | zero =>
    rw [show firstRepeatHomotopy 1 = (0 : Formal ι 1 →ₗ[ℤ] Formal ι 2) from rfl,
      show firstRepeatHomotopy 0 = (0 : Formal ι 0 →ₗ[ℤ] Formal ι 1) from rfl, LinearMap.zero_apply,
      LinearMap.zero_apply, map_zero, neg_zero]
  | succ n =>
    change firstRepeatHomotopy (n + 2) (consMap x w) = _
    induction w using Finsupp.induction with
    | zero => simp
    | single_add c z f hc hz ih =>
      have hsupp : (single c z + f).support = {c} ∪ f.support := by
        rw [Finsupp.support_add_eq, Finsupp.support_single c hz]
        rw [Finsupp.support_single c hz]
        exact Finset.disjoint_singleton_left.2 hc
      have hc' : x < c 0 :=
        hw c (by rw [hsupp]; exact Finset.mem_union_left _ (Finset.mem_singleton_self c)) 0
      have hcf : ∀ d ∈ f.support, ∀ i, x < d i := fun d hd ↦
        hw d (by rw [hsupp]; exact Finset.mem_union_right _ hd)
      have hne : (Fin.cons x c : Fin (n + 2) → ι) 0 ≠ (Fin.cons x c : Fin (n + 2) → ι) 1 := by
        rw [Fin.cons_zero, show (1 : Fin (n + 2)) = Fin.succ 0 from rfl, Fin.cons_succ]
        exact hc'.ne
      have hsingle : firstRepeatHomotopy (n + 2) (consMap x (single c z)) =
          -consMap x (firstRepeatHomotopy (n + 1) (single c z)) := by
        rw [consMap_single, ← Finsupp.smul_single_one c z,
          ← Finsupp.smul_single_one (Fin.cons (α := fun _ ↦ ι) x c) z, map_smul,
          firstRepeatHomotopy_single_of_ne hne, Fin.cons_zero, Fin.tail_cons, smul_neg, map_smul,
          map_smul]
      simp only [map_add, hsingle, ih hcf, neg_add]

/-- The second homotopy identity of Stacks 01FM on weakly increasing tuples:
`∂ h + h ∂ = 1 - e`, where `e` kills every tuple with a repetition. -/
public theorem boundary_firstRepeatHomotopy_add {a : Fin (n + 1) → ι} (ha : Monotone a) :
    boundary (firstRepeatHomotopy (n + 1) (single a 1)) +
        firstRepeatHomotopy n (boundary (single a 1)) =
      single a 1 - strictProjection (n + 1) (single a 1) := by
  induction n with
  | zero =>
    rw [show firstRepeatHomotopy 1 = (0 : Formal ι 1 →ₗ[ℤ] Formal ι 2) from rfl,
      show firstRepeatHomotopy 0 = (0 : Formal ι 0 →ₗ[ℤ] Formal ι 1) from rfl, LinearMap.zero_apply,
      LinearMap.zero_apply, map_zero, add_zero, strictProjection_single_of_strictMono (strictMono_fin_one a),
      sub_self]
  | succ n ih =>
    have hab : single a 1 = consMap (a 0) (single (Fin.tail a) 1) := by
      rw [consMap_single, Fin.cons_self_tail]
    have htail : Monotone (Fin.tail a) := fun i j hij ↦ ha (Fin.succ_le_succ_iff.2 hij)
    by_cases h : a 0 = a 1
    · -- the head repeats: duplicate it
      rw [firstRepeatHomotopy_single_of_eq h, boundary_consMap]
      have hzero : strictProjection (n + 2) (single a 1) = 0 :=
        strictProjection_single_of_not_strictMono (not_strictMono_of_eq h)
      rw [hzero, sub_zero]
      cases n with
      | zero =>
        have hbd : boundary (single a 1) = 0 := by
          rw [boundary_single, Fin.sum_univ_two]
          have h10 : Fin.removeNth (α := fun _ ↦ ι) 1 a = Fin.removeNth 0 a := by
            funext k
            rw [Fin.fin_one_eq_zero k]
            simp [Fin.removeNth_apply, h]
          rw [h10, ← Finsupp.single_add]
          simp
        rw [hbd, map_zero, map_zero, sub_zero, add_zero]
      | succ n =>
        have hb : single (Fin.tail a) 1 = consMap (a 0) (single (Fin.tail (Fin.tail a)) 1) := by
          rw [consMap_single, show a 0 = Fin.tail a 0 from h, Fin.cons_self_tail]
        have hbd : boundary (single a 1) =
            consMap (a 0) (consMap (a 0) (boundary (single (Fin.tail (Fin.tail a)) 1))) := by
          rw [hab, boundary_consMap, hb, boundary_consMap, map_sub, sub_sub_cancel]
        rw [hbd, firstRepeatHomotopy_consMap_consMap]
        abel
    · -- the head is strictly smaller than the rest
      have hlt : a 0 < a 1 := lt_of_le_of_ne (ha (Fin.zero_le 1)) h
      have hface : ∀ c ∈ (boundary (single (Fin.tail a) 1)).support, ∀ i, a 0 < c i := by
        intro c hc i
        obtain ⟨j, rfl⟩ := exists_eq_removeNth_of_mem_support_boundary hc
        exact hlt.trans_le (htail (Fin.zero_le _))
      have hb0 : ∀ c ∈ (single (Fin.tail a) (1 : ℤ)).support, ∀ i, a 0 < c i := fun c hc i ↦ by
        rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hc)]
        exact hlt.trans_le (htail (Fin.zero_le _))
      have h1 : boundary (firstRepeatHomotopy (n + 1 + 1) (single a 1)) =
          -firstRepeatHomotopy (n + 1) (single (Fin.tail a) 1) +
            consMap (a 0) (boundary (firstRepeatHomotopy (n + 1) (single (Fin.tail a) 1))) := by
        rw [firstRepeatHomotopy_single_of_ne h, map_neg, boundary_consMap, neg_sub, sub_eq_neg_add]
      have h2 : firstRepeatHomotopy (n + 1) (boundary (single a 1)) =
          firstRepeatHomotopy (n + 1) (single (Fin.tail a) 1) +
            consMap (a 0) (firstRepeatHomotopy n (boundary (single (Fin.tail a) 1))) := by
        rw [hab, boundary_consMap, map_sub, firstRepeatHomotopy_consMap_of_lt _ _ hface,
          sub_neg_eq_add]
      have h3 : strictProjection (n + 1 + 1) (single a 1) =
          consMap (a 0) (strictProjection (n + 1) (single (Fin.tail a) 1)) := by
        rw [hab, strictProjection_consMap_of_lt _ _ hb0]
      have hih := congrArg (consMap (a 0)) (ih htail)
      rw [map_add, map_sub] at hih
      rw [h1, h2, h3, hab, ← hih]
      abel

public theorem strictProjection_zero (v : Formal ι 0) : strictProjection 0 v = v := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, hf, hg]
  | single a z =>
    rw [← Finsupp.smul_single_one a z, map_smul,
      strictProjection_single_of_strictMono (fun i ↦ i.elim0)]

public theorem strictProjection_one (v : Formal ι 1) : strictProjection 1 v = v := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, hf, hg]
  | single a z =>
    rw [← Finsupp.smul_single_one a z, map_smul,
      strictProjection_single_of_strictMono (strictMono_fin_one a)]

omit [LinearOrder ι] in
/-- A linear identity which holds on the basis tuples in the support of `w` holds at `w`. -/
public theorem linearMap_apply_eq_of_forall_mem_support {m : ℕ} {N : Type*} [AddCommGroup N]
    {L R : Formal ι m →ₗ[ℤ] N} {w : Formal ι m}
    (h : ∀ c ∈ w.support, L (single c 1) = R (single c 1)) : L w = R w := by
  rw [← Finsupp.sum_single w, map_finsuppSum, map_finsuppSum]
  exact Finsupp.sum_congr fun c hc ↦ by
    rw [← Finsupp.smul_single_one c (w c), LinearMap.map_smul, LinearMap.map_smul, h c hc]

/-- `e` is a chain map on weakly increasing tuples. -/
public theorem boundary_strictProjection {a : Fin (n + 1) → ι} (ha : Monotone a) :
    boundary (strictProjection (n + 1) (single a 1)) =
      strictProjection n (boundary (single a 1)) := by
  cases n with
  | zero => rw [strictProjection_single_of_strictMono (strictMono_fin_one a), strictProjection_zero]
  | succ n =>
    have h1 := congrArg boundary (boundary_firstRepeatHomotopy_add ha)
    rw [map_add, map_sub, boundary_boundary, zero_add] at h1
    have h2 : boundary (firstRepeatHomotopy (n + 1) (boundary (single a 1))) +
        firstRepeatHomotopy n (boundary (boundary (single a 1))) =
        boundary (single a 1) - strictProjection (n + 1) (boundary (single a 1)) := by
      have := linearMap_apply_eq_of_forall_mem_support
        (L := boundary ∘ₗ firstRepeatHomotopy (n + 1) + firstRepeatHomotopy n ∘ₗ boundary)
        (R := LinearMap.id - strictProjection (n + 1)) (w := boundary (single a 1))
        (fun c hc ↦ by
          simpa using boundary_firstRepeatHomotopy_add (monotone_of_mem_support_boundary ha hc))
      simpa using this
    rw [boundary_boundary, map_zero, add_zero] at h2
    rw [h2] at h1
    exact (sub_right_inj.1 h1).symm

public theorem strictMono_of_mem_support_strictProjection {a b : Fin n → ι}
    (hb : b ∈ (strictProjection n (single a 1)).support) : StrictMono b := by
  by_cases ha : StrictMono a
  · rw [strictProjection_single_of_strictMono ha] at hb
    rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hb)]
    exact ha
  · rw [strictProjection_single_of_not_strictMono ha] at hb
    simp at hb

public theorem range_subset_of_mem_support_strictProjection {a b : Fin n → ι}
    (hb : b ∈ (strictProjection n (single a 1)).support) : Set.range b ⊆ Set.range a := by
  by_cases ha : StrictMono a
  · rw [strictProjection_single_of_strictMono ha] at hb
    rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hb)]
  · rw [strictProjection_single_of_not_strictMono ha] at hb
    simp at hb

public theorem range_subset_of_mem_support_firstRepeatHomotopy {a : Fin (n + 1) → ι}
    {b : Fin (n + 2) → ι} (hb : b ∈ (firstRepeatHomotopy (n + 1) (single a 1)).support) :
    Set.range b ⊆ Set.range a := by
  induction n with
  | zero =>
    rw [show firstRepeatHomotopy 1 = (0 : Formal ι 1 →ₗ[ℤ] Formal ι 2) from rfl] at hb
    simp at hb
  | succ n ih =>
    by_cases h : a 0 = a 1
    · rw [firstRepeatHomotopy_single_of_eq h] at hb
      obtain ⟨b', hb', rfl⟩ := exists_eq_cons_of_mem_support_consMap hb
      rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hb'), Fin.range_cons]
      exact Set.union_subset (Set.singleton_subset_iff.2 ⟨_, rfl⟩) subset_rfl
    · rw [firstRepeatHomotopy_single_of_ne h, Finsupp.support_neg] at hb
      obtain ⟨b', hb', rfl⟩ := exists_eq_cons_of_mem_support_consMap hb
      rw [Fin.range_cons]
      exact Set.union_subset (Set.singleton_subset_iff.2 ⟨_, rfl⟩)
        ((ih hb').trans (Set.range_comp_subset_range Fin.succ a))

public theorem monotone_of_mem_support_firstRepeatHomotopy {a : Fin (n + 1) → ι}
    (ha : Monotone a) {b : Fin (n + 2) → ι}
    (hb : b ∈ (firstRepeatHomotopy (n + 1) (single a 1)).support) : Monotone b := by
  induction n with
  | zero =>
    rw [show firstRepeatHomotopy 1 = (0 : Formal ι 1 →ₗ[ℤ] Formal ι 2) from rfl] at hb
    simp at hb
  | succ n ih =>
    by_cases h : a 0 = a 1
    · rw [firstRepeatHomotopy_single_of_eq h] at hb
      obtain ⟨b', hb', rfl⟩ := exists_eq_cons_of_mem_support_consMap hb
      rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hb')]
      exact monotone_cons (fun i ↦ ha (Fin.zero_le i)) ha
    · rw [firstRepeatHomotopy_single_of_ne h, Finsupp.support_neg] at hb
      obtain ⟨b', hb', rfl⟩ := exists_eq_cons_of_mem_support_consMap hb
      have htail : Monotone (Fin.tail a) := fun i j hij ↦ ha (Fin.succ_le_succ_iff.2 hij)
      refine monotone_cons (fun i ↦ ?_) (ih htail hb')
      obtain ⟨k, hk⟩ := (range_subset_of_mem_support_firstRepeatHomotopy hb').trans
        (Set.range_comp_subset_range Fin.succ a) ⟨i, rfl⟩
      rw [← hk]
      exact ha (Fin.zero_le k)

end OrderedCechTuple

end SphereSixComplex
