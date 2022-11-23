import Mathlib
universe u

namespace project

structure HeapNodeAux (α : Type u) (h : Type u) where
  val : α
  rank : Nat
  children : h

-- A `Heap` is a forest of binomial trees.
inductive Heap (α : Type u) : Type u where
  | heap (ns : List (HeapNodeAux α (Heap α))) : Heap α
  deriving Inhabited

open Heap
-- A `BinTree` is a binomial tree. If a `BinTree` has rank `k`, its children
-- have ranks between `0` and `k - 1`. They are ordered by rank. Additionally,
-- the value of each child must be greater than or equal to the value of its
-- parent node.
abbrev BinTree α := HeapNodeAux α (Heap α)

def Heap.nodes : Heap α → List (BinTree α)
  | heap ns => ns


@[simp]
theorem Heap.nodes_def : nodes (heap xs) = xs := rfl
  

variable {α : Type u}

def hRank : List (BinTree α) → Nat
  | []   => 0
  | h::_ => h.rank

def isEmpty : Heap α → Bool
  | heap [] => true
  | _       => false

def empty : Heap α :=
  heap []

def singleton (a : α) : Heap α :=
  heap [{ val := a, rank := 1, children := heap [] }]

-- Combine two binomial trees of rank `r`, creating a binomial tree of rank
-- `r + 1`.
@[specialize] def combine (le : α → α → Bool) (n₁ n₂ : BinTree α) : BinTree α :=
  if le n₂.val n₁.val then
     { n₂ with rank := n₂.rank + 1, children := heap $ n₂.children.nodes ++ [n₁] }
  else
     { n₁ with rank := n₁.rank + 1, children := heap $ n₁.children.nodes ++ [n₂] }

-- Merge two forests of binomial trees. The forests are assumed to be ordered
-- by rank and `mergeNodes` maintains this invariant.
@[specialize] def mergeNodes (le : α → α → Bool) : List (BinTree α) → List (BinTree α) → List (BinTree α)
  | [], h  => h
  | h,  [] => h
  | f@(h₁ :: t₁), s@(h₂ :: t₂) => 
    if h₁.rank < h₂.rank then h₁ :: mergeNodes le t₁ s
    else if h₂.rank < h₁.rank then h₂ :: mergeNodes le t₂ f
    else
      let merged := combine le h₁ h₂
      let r      := merged.rank
      if r != hRank t₁ then
        if r != hRank t₂ then merged :: mergeNodes le t₁ t₂ else mergeNodes le (merged :: t₁) t₂
      else
        if r != hRank t₂ then mergeNodes le t₁ (merged :: t₂) else merged :: mergeNodes le t₁ t₂
termination_by _ h₁ h₂ => h₁.length + h₂.length
decreasing_by simp_wf; simp_arith [*]

@[specialize] def merge (le : α → α → Bool) : Heap α → Heap α → Heap α
  | heap h₁, heap h₂ => heap (mergeNodes le h₁ h₂)

@[specialize] def head? (le : α → α → Bool) : Heap α → Option α
  | heap []      => none
  | heap (h::hs) => some $
    hs.foldl (init := h.val) fun r n => if le r n.val then r else n.val

@[inline] def head [Inhabited α] (le : α → α → Bool) (h : Heap α) : α :=
  head? le h |>.getD default

@[specialize] def findMin (le : α → α → Bool) : List (BinTree α) → Nat → BinTree α × Nat → BinTree α × Nat
  | [],    _,   r          => r
  | h::hs, idx, (h', idx') => if le h'.val h.val then findMin le hs (idx+1) (h', idx') else findMin le hs (idx+1) (h, idx)
    -- It is important that we check `le h'.val h.val` here, not the other way
    -- around. This ensures that head? and findMin find the same element even
    -- when we have `le h'.val h.val` and `le h.val h'.val` (i.e. le is not
    -- irreflexive).

def deleteMin (le : α → α → Bool) : Heap α → Option (α × Heap α)
  | heap [] => none
  | heap [h] => some (h.val, h.children)
  | heap hhs@(h::hs) =>
    let (min, minIdx) := findMin le hs 1 (h, 0)
    let rest          := hhs.eraseIdx minIdx
    let tail          := merge le (heap rest) min.children
    some (min.val, tail)

@[inline] def tail? (le : α → α → Bool) (h : Heap α) : Option (Heap α) :=
  deleteMin le h |>.map (·.snd)

@[inline] def tail (le : α → α → Bool) (h : Heap α) : Heap α :=
  tail? le h |>.getD empty

partial def toList (le : α → α → Bool) (h : Heap α) : List α :=
  match deleteMin le h with
  | none          => []
  | some (hd, tl) => hd :: toList le tl

partial def toArray (le : α → α → Bool) (h : Heap α) : Array α :=
  go #[] h
  where
    go (acc : Array α) (h : Heap α) : Array α :=
      match deleteMin le h with
      | none => acc
      | some (hd, tl) => go (acc.push hd) tl

partial def toListUnordered : Heap α → List α
  | heap ns => ns.bind fun n => n.val :: toListUnordered n.children

partial def toArrayUnordered (h : Heap α) : Array α :=
  go #[] h
  where
    go (acc : Array α) : Heap α → Array α
      | heap ns => Id.run do
        let mut acc := acc
        for n in ns do
          acc := acc.push n.val
          acc := go acc n.children
        return acc



inductive All (P: α → Prop) : List α → Prop 
| nil: All P []
| cons: P x → All P xs → All P (x :: xs)

mutual
  inductive IsBinTree : BinTree α → Prop where
  | C: IsRankedTree 1 a.rank a.children.nodes → IsBinTree a

  /-IsRankedTree n m ts :<=> the list ts contains the children of the parentnode of a binomial tree, IsRankedTree 
  assures that the order of the rank of the children is n, n+1, n+2,.....,m-1 and if n = m, then ts is empty-/
  inductive IsRankedTree : Nat → Nat → List (BinTree α)  → Prop where
  | nil : n = m → IsRankedTree n m []
  | cons : t.rank = n → IsRankedTree (n + 1) m ts → IsBinTree t → IsRankedTree n m (t::ts)
end

/-IsHeap rank [t₁,...,tₙ] :<=> Each tree in the list t₁ upto tₙ should have a smaller rank than the tree
that follows so tₙ.rank < tₙ₊₁. Also each tree in the list should be a binomial tree so IsBinTree t should hold for each tree t-/
inductive IsHeapForest' : Nat → List (BinTree α) → Prop where
| nil : IsHeapForest' rank []
| cons : rank < t.rank → IsBinTree t → IsHeapForest' t.rank ts → IsHeapForest' rank (t::ts)

abbrev IsHeapForest : List (BinTree α) → Prop := IsHeapForest' 0

/-IsHeap (heap [ts]) holds if IsHeapForest 0 ts holds, 0 is used because every binomial tree has a rank higher than 0-/
def IsHeap (h : Heap α): Prop :=
  IsHeapForest h.nodes


mutual
  inductive IsSearchTree (le : α → α → Bool) : BinTree α → Prop where
  | C : IsMinTree le a.val a.children.nodes → IsSearchTree le a

  /-IsMinHeap le ns val :<=> assures that val(value of parent node) is less or equal than the value
  of the nodes in ns(the children). Maintains minimum heap property-/
  inductive IsMinTree (le : α → α → Bool) : α → List (BinTree α) → Prop where
  | nil : IsMinTree le val []  
  | cons : le val n.val → IsMinTree le val ns → IsSearchTree le n → IsMinTree le val (n::ns) 
end

/-IsSearchForrest le (heap [t₁,...,tₙ]) :<=> IsMinHeap holds if for each tree t in the list t₁ upto tₙ, IsSearchTree le t holds-/
inductive IsMinHeap (le : α → α → Bool) : Heap α → Prop where
| nil : IsMinHeap le (heap [])
| cons : IsSearchTree le n → IsMinHeap le (heap ns) → IsMinHeap le (heap (n::ns))

theorem deleteMin_empty_IsHeap :  deleteMin le xs = none → isEmpty xs := by
intro h₁
unfold deleteMin at h₁
cases xs
rename_i a
cases a
. rfl
. dsimp at h₁
  rename_i b
  cases b <;> contradiction


theorem children_IsHeap : IsHeap (heap [h]) → IsHeap h.children := by
intro h₁
unfold IsHeap
cases h₁
unfold IsHeapForest
cases h.children with | heap h₂ =>
dsimp

sorry


--maybe add more conclusions
-- shouldn't we add a hypothesis that says the heap isn't empty?
theorem deleteMin_non_empty_IsHeap (h₁ : IsHeap xs) (h₂ : IsMinHeap le xs) (hne: deleteMin le xs ≠ none): deleteMin le xs = some (y, ys) → IsHeap ys ∧ IsMinHeap le ys :=
match xs with
| heap [] => by
  intro h₃
  unfold deleteMin at h₃
  dsimp at h₃
  contradiction
| heap [h] => by
  intro h₃
  unfold deleteMin at h₃
  dsimp at h₃
  rw[Option.some_inj] at h₃
  rw[Prod.eq_iff_fst_eq_snd_eq] at h₃
  simp at h₃
  apply And.intro
  . cases h₃
    rename_i b c
    unfold IsHeapForest at b
    cases b
    rw[←c]
    unfold IsHeap
    unfold IsHeap at h₁
    dsimp at h₁
    cases h₁
    rename_i h₃ h₄ h₅
    cases h₆ : h.children
    rename_i ns
    dsimp
    cases ns with
    | nil => constructor
    | cons n ns =>
      cases h₃ with | C hs =>
      constructor
      . rw[h₆] at hs
        dsimp at *
        cases hs with | cons h₇ h₈ h₉ =>
        rw[h₇]
        decide
      . rw[h₆] at hs
        dsimp at hs
        cases hs
        assumption
      . rw[h₆] at hs
        dsimp at hs
        cases hs with | cons eq rt bt=>
        have hf : IsHeap h.children := by
          rw[h₆]
          constructor
          . rw[eq]
            decide
          . assumption
          . cases ns
            . sorry
            . rename_i e f g
              induction g with
              | nil => sorry
              | cons => 
                rename_i l m n
                -- always get stuck in the last case of the constructor
                sorry

        sorry
        
  . sorry
| heap (h::hs) => by
  intro h₃
  cases h₂
  cases h₁
  unfold deleteMin at h₃
  dsimp at h₃
  split at h₃
  . contradiction
  . rename_i a b c d e f
    cases c
    rename_i g h i
    cases i
    . 
      sorry
    . sorry
  . rw[Option.some_inj] at h₃
    
    sorry
