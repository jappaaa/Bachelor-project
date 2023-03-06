import Project.Main

universe u

namespace project

variable {le : α → α → Bool} 
(not_le_le : ∀ x y, ¬ le x y → le y x) 
(le_trans : ∀ x y z, le x y → le y z → le x z)
(le_rfl : ∀ z, le z z)

theorem IsBinTree_findMin : ∀ hs idx h' idx', IsHeapForest' r hs → IsBinTree h' → IsBinTree (findMin le hs idx (h', idx')).fst
  | [], idx, h', idx', _, hh' => by
    simp[findMin]
    assumption
  | h :: hs, idx, h', idx', hhs, hh' => by
    simp[findMin]
    cases hhs
    split <;> apply IsBinTree_findMin <;> assumption

theorem IsSearchTree_findMin : ∀ hs idx h' idx', IsMinHeap le (.heap hs) → IsSearchTree le h' → IsSearchTree le (findMin le hs idx (h', idx')).fst
  | [], idx, h', idx', _, hh' => by
    simp[findMin]
    assumption
  | h :: hs, idx, h', idx', hhs, hh' => by
    simp[findMin]
    cases hhs
    split <;> apply IsSearchTree_findMin <;> assumption


theorem findMin_is_minimum_head : ∀ hs idx h' idx', le (findMin le hs idx (h', idx')).fst.val h'.val
  | [], idx, h', idx' => by
    simp[findMin]
    apply le_rfl
  | t :: ts, idx, h', idx' => by
    unfold findMin
    split
    . apply findMin_is_minimum_head
    . have ih := findMin_is_minimum_head ts (idx + 1) t idx
      apply le_trans
      assumption
      apply not_le_le
      assumption

theorem findMin_is_minimum_tail : ∀ hs idx h' idx', le (findMin le hs idx (h', idx')).fst.val h'.val → ∀ x ∈ hs, le (findMin le hs idx (h', idx')).fst.val x.val 
  | [], idx, h', idx' => by
    intros _ _ hin
    cases hin    
  | t :: ts, idx, h', idx' => by
    intros hle t₂ hel
    cases hel
    . unfold findMin
      split
      . unfold findMin at hle
        split at hle
        . apply le_trans <;> assumption
        . contradiction
      . apply findMin_is_minimum_head <;> assumption
    . unfold findMin
      split
      . unfold findMin at hle
        split at hle
        . apply findMin_is_minimum_tail <;> assumption
        . contradiction
      . apply findMin_is_minimum_tail
        . unfold findMin at hle
          split at hle
          . contradiction
          . apply findMin_is_minimum_head <;> assumption
        . assumption

theorem findMin_is_minimum : ∀ hs idx h' idx', le (findMin le hs idx (h', idx')).fst.val h'.val ∧ ∀ x ∈ hs, le (findMin le hs idx (h', idx')).fst.val x.val := by
  intros
  apply And.intro
  . apply findMin_is_minimum_head <;> assumption
  . apply findMin_is_minimum_tail <;> try assumption
    apply findMin_is_minimum_head <;> assumption