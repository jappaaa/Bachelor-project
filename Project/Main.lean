import Mathlib.Data.Nat.Basic

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


mutual
  /-IsBinTree sets the lower bound and the upper bound for the ranks of the children of a tree-/
  inductive IsBinTree : BinTree α → Prop where
  | mk: IsRankedTree 1 t.rank t.children.nodes → IsBinTree t

  /-IsRankedTree n m ts :<=> the list ts contains the children of the parentnode of a binomial tree, IsRankedTree 
  assures that the order of the rank of the children is n, n+1, n+2,.....,m-1 and if n = m, then ts is empty-/
  inductive IsRankedTree : Nat → Nat → List (BinTree α)  → Prop where
  | nil : IsRankedTree n n []
  | cons : t.rank = n  → IsRankedTree (n + 1) m ts → IsBinTree t → IsRankedTree n m (t::ts)
end

/-IsHeapForest' rank [t₁,...,tₙ] :<=> Each tree in the list t₁ upto tₙ should have a smaller rank than the tree
that follows so tₙ.rank < tₙ₊₁. Also each tree in the list should be a binomial tree so IsBinTree t should hold for each tree t-/
inductive IsHeapForest' : Nat → List (BinTree α) → Prop where
| nil : IsHeapForest' rank []
| cons : rank < t.rank → IsBinTree t → IsHeapForest' t.rank ts → IsHeapForest' rank (t::ts)

/-abbreviation for IsHeapForest' 0 ts , the 0 ensures that the rank of the first tree in the list is at least 1-/
abbrev IsHeapForest : List (BinTree α) → Prop := IsHeapForest' 0

/-IsHeap h calls IsHeapForest with the list of trees extracted from h-/
def IsHeap (h : Heap α): Prop :=
  IsHeapForest h.nodes


mutual
  inductive IsSearchTree (le : α → α → Bool) : BinTree α → Prop where
  | mk : IsMinTree le t.val t.children.nodes → IsSearchTree le t

  /-IsMinHeap le val ns :<=> assures that val(value of parent node) is less or equal than the value
  of the nodes in ns (the children). Maintains minimum heap property-/
  inductive IsMinTree (le : α → α → Bool) : α → List (BinTree α) → Prop where
  | nil : IsMinTree le val []  
  | cons : le val t.val → IsMinTree le val ts → IsSearchTree le t → IsMinTree le val (t::ts) 
end

/-IsMinHeap le (heap [t₁,...,tₙ]) :<=> IsMinHeap holds if for each tree t in the list t₁ upto tₙ, IsSearchTree le t holds-/
inductive IsMinHeap (le : α → α → Bool) : Heap α → Prop where
| nil : IsMinHeap le (heap [])
| cons : IsSearchTree le t → IsMinHeap le (heap ts) → IsMinHeap le (heap (t::ts)) 


theorem IsHeap_empty : IsHeap (@empty α) := by
  constructor


theorem IsMinHeap_empty : IsMinHeap le (@empty α) := by
  constructor


theorem singleton_IsHeap : IsHeap (singleton a) := by
  constructor
  . dsimp
    decide
  . constructor
    dsimp
    constructor
  . constructor

  
theorem singleton_IsMinHeap : IsMinHeap le (singleton a) := by
  constructor
  . constructor
    dsimp
    constructor
  . constructor


theorem IsRankedTree_append (rt : IsRankedTree n m xs) (ha: IsBinTree a) (hrank: a.rank = m) :
  IsRankedTree n (m + 1) (xs ++ [a]) := by
  induction xs generalizing n
  case nil =>
    simp
    cases rt
    constructor
    . assumption
    . constructor
    . assumption
  case cons _ _ ih =>
    cases rt
    constructor
    . assumption
    . apply ih
      assumption
    . assumption


theorem combine_IsBinTree (le : α → α → Bool) (a b : BinTree α) : 
  IsBinTree a → IsBinTree b → a.rank = b.rank → IsBinTree (combine le a b) := by
    intros ha hb hab
    constructor
    unfold combine
    split
    . dsimp
      cases hb
      apply IsRankedTree_append
      repeat assumption
    . dsimp
      cases ha
      apply IsRankedTree_append
      repeat assumption
      simp_all


theorem IsMinTree_append (h : IsMinTree le m xs) (ha : IsSearchTree le a) (hba: le m a.val = true) : 
  IsMinTree le m (xs ++ [a]) := by
    induction xs with
    | nil =>
      simp
      constructor <;> assumption
    | cons _ _ ih => 
      cases h
      constructor
      . assumption
      . simp
        apply ih
        assumption
      . assumption


variable {le : α → α → Bool} (not_le_le : ∀ x y, ¬ le x y → le y x)
theorem combine_IsSearchTree (a b : BinTree α) : 
  IsSearchTree le a → IsSearchTree le b → IsSearchTree le (combine le a b) := by
    intros ha hb
    constructor
    unfold combine
    split
    . dsimp
      cases hb
      apply IsMinTree_append
      repeat assumption
    . dsimp
      cases ha
      apply IsMinTree_append
      repeat assumption
      apply not_le_le
      assumption


  


