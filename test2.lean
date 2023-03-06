
structure HeapNodeAux (α : Type u) (h : Type u) where
  val : α
  rank : Nat
  children : h

inductive Heap (α : Type u) : Type u where
  | heap (ns : List (HeapNodeAux α (Heap α))) : Heap α
  deriving Inhabited

open Heap

abbrev BinTree α := HeapNodeAux α (Heap α)

def Heap.nodes : Heap α → List (BinTree α)
  | heap ns => ns

def hRank : List (BinTree α) → Nat
  | []   => 0
  | h::_ => h.rank

@[specialize] def combine (le : α → α → Bool) (n₁ n₂ : BinTree α) : BinTree α :=
  if le n₂.val n₁.val then
     { n₂ with rank := n₂.rank + 1, children := heap $ n₂.children.nodes ++ [n₁] }
  else
     { n₁ with rank := n₁.rank + 1, children := heap $ n₁.children.nodes ++ [n₂] }

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


theorem temp : mergeNodes le [] h = h := by
  unfold mergeNodes
