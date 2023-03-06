import Project.Main
import Project.Merge
import Project.findMin

universe u

namespace project

variable {le : α → α → Bool} 
(not_le_le : ∀ x y, ¬ le x y → le y x) 
(le_trans : ∀ x y z, le x y → le y z → le x z)
(le_rfl : ∀ z, le z z)


theorem deleteMin_empty_IsHeap :  deleteMin le xs = none → isEmpty xs := by
intro heq
unfold deleteMin at heq
cases xs with | heap ts =>
cases ts with 
| nil =>
  rfl
| cons _ ts =>
  dsimp at heq
  cases ts <;> contradiction


theorem IsHeapForest'_of_IsRankedTree (h₁ : r ≠ 0) : 
    IsRankedTree r s nodes → IsHeapForest' (r - 1) nodes 
  | .nil => by 
    constructor
  | .cons (t := t) (ts := ts) eq rt _ => by
    constructor
    . rw[←eq]
      apply Nat.pred_lt
      simp
      rw[eq]
      assumption
    . assumption
    . have : t.rank = (r + 1) - 1 := by
        simp_all
      rw[this]
      apply IsHeapForest'_of_IsRankedTree
      . simp
      . assumption

theorem children_IsHeap : IsHeap (.heap [h]) → IsHeap h.children := by
  intro h₁
  cases h with | mk val rank children =>
  dsimp at *
  cases h₁ with | cons lt bt h₁ =>
  dsimp at *
  cases children with | heap nodes =>
  dsimp at *
  cases bt with | mk rt =>
  dsimp at rt
  apply IsHeapForest'_of_IsRankedTree (r := 1)
  . simp
  . assumption

theorem IsMinHeap_of_IsMinTree : IsMinTree le val nodes → IsMinHeap le (.heap nodes)
  | .nil => by
    constructor
  | .cons _ _ _=> by
    constructor
    . assumption
    . apply IsMinHeap_of_IsMinTree
      . assumption

theorem children_IsMinHeap : IsMinHeap le (.heap [h]) → IsMinHeap le h.children := by
  intro imh
  cases h with | mk val rank children =>
  dsimp at *
  cases imh with | cons st imh =>
  cases children with | heap nodes =>
  cases imh with | nil =>
  cases st with | mk mt =>
  dsimp at mt
  apply IsMinHeap_of_IsMinTree
  repeat assumption


theorem IsHeapForest'_eraseIdx {id : ℕ} : IsHeapForest' r a → IsHeapForest' r (List.eraseIdx a id)
  | .nil => by
    simp 
    constructor
  | .cons (t := t) (ts := ts) lt bt h₁ => by
    unfold List.eraseIdx
    split
    . constructor
    . simp_all
      apply IsHeapForest'_weaken
      . assumption
      . apply le_of_lt 
        assumption
    . rename_i eq
      have hf : IsHeapForest' r (t ::ts) := by
        apply IsHeapForest'_of_IsHeapForest' <;> assumption
      constructor
      . simp_all
      . simp_all
      . rw[eq] at hf
        cases hf
        apply IsHeapForest'_eraseIdx
        assumption 
    

theorem IsHeap_delete_BinTree {id : Nat} : IsHeap (.heap (a :: b)) → IsHeap (.heap (a :: List.eraseIdx b id)) := by
  intros h₁
  cases h₁
  constructor
  . assumption
  . assumption
  . apply IsHeapForest'_eraseIdx
    assumption


theorem IsMinHeap_eraseIdx {id : Nat} : IsMinHeap le (.heap b) → IsMinHeap le (.heap (List.eraseIdx b id))
  | .nil => by
    simp
    constructor
  | .cons (n := n) (ns := ns) st mh => by
    unfold List.eraseIdx
    split
    . constructor
    . rename_i heq
      rw[← List.tail_eq_of_cons_eq heq]
      assumption
    . rename_i heq
      constructor
      . rw[← List.head_eq_of_cons_eq heq]
        assumption
      . apply IsMinHeap_eraseIdx
        rw[← List.tail_eq_of_cons_eq heq]
        assumption

theorem IsMinHeap_delete_BinTree {id : Nat} : IsMinHeap le (.heap (a :: b)) → IsMinHeap le (.heap (a :: List.eraseIdx b id)) := by
  intros imh
  cases imh
  constructor
  . assumption
  . apply IsMinHeap_eraseIdx
    assumption


theorem rank_zero_IsRankedTree : IsRankedTree (n + 1) 0 ts → False
  | .cons (ts := ts) _ rt _ => by
    cases rt with
    | cons => 
      apply rank_zero_IsRankedTree
      assumption
  

theorem min_rank_IsBinTree : IsBinTree t → 0 < t.rank := by
  intro bt
  cases t with | mk val r children =>
  cases r
  . cases bt with | mk rt =>
    simp at rt
    generalize eq : (children.nodes) = ts
    rw[eq] at rt
    cases rt
    . simp
      apply rank_zero_IsRankedTree
      assumption
  . simp_arith

theorem deleteMin_non_empty_minimum : deleteMin le (.heap xs) = some (y, ys) → ∀ x ∈ xs, le y x.val := by
  intros heq t hel
  unfold deleteMin at heq
  split at heq
  . contradiction
  . simp_all
  . simp_all
    dsimp at heq
    rw[← heq.left]
    cases hel
    . rename_i heq₂
      rw[← heq₂]
      apply findMin_is_minimum_head <;> simp_all; assumption
    . apply findMin_is_minimum_tail
      . simp_all
      repeat assumption
      . apply findMin_is_minimum_head
        . simp_all
        repeat assumption
      . assumption


theorem deleteMin_non_empty (h₁ : IsHeap xs) (h₂ : IsMinHeap le xs) : deleteMin le xs = some (y, ys) → IsHeap ys ∧ IsMinHeap le ys :=
match xs with
| .heap [] => by
  intro eq
  unfold deleteMin at eq
  dsimp at eq
  contradiction
| .heap [h] => by
  intro eq
  unfold deleteMin at eq
  dsimp at eq
  rw[Option.some_inj, Prod.eq_iff_fst_eq_snd_eq] at eq
  simp at eq
  apply And.intro
  . rw[← eq.right]
    apply children_IsHeap
    assumption 
  . rw[← eq.right]
    apply children_IsMinHeap
    assumption
| .heap (h::hs) => by
  intro dmeq
  unfold deleteMin at dmeq
  dsimp at dmeq
  split at dmeq
  . contradiction
  . rename_i heq
    rw[Option.some_inj] at dmeq
    rw[Prod.eq_iff_fst_eq_snd_eq] at dmeq
    simp at *
    rw[←dmeq.right]
    rw[←heq.left]
    apply And.intro
    . apply children_IsHeap
      rw[heq.right] at h₁
      assumption
    . apply children_IsMinHeap
      rw[heq.right] at h₂
      assumption
  . rename_i xs₂ t₁ ts hne₂ heqh
    rw[Option.some_inj] at dmeq
    unfold findMin at dmeq
    split at dmeq
    . contradiction
    . split at dmeq
      . simp at *
        rename_i ts n btxn bt ts₂ bt₂ n₂ lebt eqeq
        rw[←dmeq.right]
        apply And.intro
        . unfold merge
          split
          rename_i ys₂ xs₃ ts₃ ts₄ heq heq₂
          simp at heq
          unfold List.eraseIdx at heq
          have ihts₃ : IsHeap (.heap ts₃) := by
            split at heq
            . simp_all
            . simp_all
              unfold IsHeap
              simp
              unfold IsHeapForest
              cases h₁
              apply IsHeapForest'_weaken
              . assumption
              . simp_arith
            . rename_i heq₃ _
              rw[← heq]
              apply IsHeap_delete_BinTree
              rw[← heq₃, ← heqh.left, ← heqh.right] 
              assumption
          have ihts₄ : IsHeap (.heap ts₄) := by
            clear heq 
            rw [← heq₂]
            have (And.intro ml mr) := eqeq
            rw [← ml, ← mr] at *; clear eqeq ml mr
            apply children_IsHeap
            constructor
            . have fm : IsBinTree (findMin le ts₂ (1 + 1) (t₁, 0)).fst := by
                apply IsBinTree_findMin
                . cases h₁ with | cons _ _ hf =>
                  rw[heqh.right] at hf 
                  cases hf
                  assumption
                . cases h₁
                  simp_all
              apply min_rank_IsBinTree 
              assumption
            . apply IsBinTree_findMin
              . rw[heqh.right] at h₁
                cases h₁ with | cons _ _ hf =>
                  cases hf
                  assumption
              . unfold IsHeap at h₁
                unfold IsHeapForest at h₁
                cases h₁ with | cons _ ht _ =>
                rw[heqh.left] at ht
                assumption
            . constructor
          unfold IsHeap at *
          unfold IsHeapForest at *
          simp at *
          have min_zero : 0 = min 0 0 := by
            simp
          rw[min_zero]
          apply IsHeap_merge <;> assumption
        . unfold merge
          split
          rename_i ys₂ xs₃ ts₃ ts₄ heq heq₂
          simp at heq
          unfold List.eraseIdx at heq
          have h₁₂ : IsMinHeap le (.heap ts₃) := by
            split at heq
            . rw[← heq]
              constructor
            . rename_i ts₅ heq₃ _
              rw[← heqh.right] at heq₃
              have eq : hs = ts₅ := by
                apply List.tail_eq_of_cons_eq
                assumption
              rw[← heq, ← eq]
              cases h₂
              assumption
            . rename_i heq₃ _
              rw[← heq]
              apply IsMinHeap_delete_BinTree
              rw[← heq₃, ← heqh.left, ← heqh.right]
              assumption                                                           
          have h₁₃ : IsMinHeap le (.heap ts₄) := by
            rw[← heq₂]
            apply children_IsMinHeap
            constructor
            . apply IsSearchTree_findMin
              . rw[heqh.right] at h₂
                cases h₂ with | cons _ mh => 
                cases mh
                assumption
              . rw[← eqeq.left, ← heqh.left]
                cases h₂
                assumption
            . constructor
          apply IsMinHeap_merge
          simp
          repeat assumption
      . simp at dmeq
        have (And.intro _ heq) := dmeq
        clear dmeq
        unfold merge at heq
        split at heq
        rename_i bt ts _ _ _ _ _ _ _ ts₂ ts₃ heq₃ heq₄
        rw[← heq]
        apply And.intro
        . have ihts₂ : IsHeap (.heap ts₂) := by
            rw[← heq₃]
            unfold IsHeap
            unfold IsHeapForest
            apply IsHeapForest'_eraseIdx
            simp at heqh
            constructor
            . apply min_rank_IsBinTree
              rw[← heqh.left]
              cases h₁
              assumption
            . rw[← heqh.left]
              cases h₁
              assumption
            . cases h₁
              rw[← heqh.left, ← heqh.right]
              assumption
          have h₂₄ : IsHeap (.heap ts₃) := by
            rw[← heq₄]
            apply children_IsHeap
            constructor
            . have ibt : IsBinTree (findMin le ts (1 + 1) (bt, 1)).fst := by
                simp at heqh
                rw[heqh.right] at h₁
                apply IsBinTree_findMin <;>
                  cases h₁ with | cons _ _ hf =>
                  cases hf
                  assumption
              apply min_rank_IsBinTree ibt
            . simp at heqh
              rw[heqh.right] at h₁
              apply IsBinTree_findMin <;>
                cases h₁ with | cons _ _ hf =>
                cases hf
                assumption
            . constructor
          unfold IsHeap at *
          unfold IsHeapForest at *
          simp at *
          have min_zero : 0 = min 0 0 := by
            simp
          rw[min_zero]
          apply IsHeap_merge <;> assumption
        . simp at heqh
          have imhts₂ : IsMinHeap le (.heap ts₂) := by
            rw[← heq₃]
            apply IsMinHeap_eraseIdx
            rw[← heqh.left, ← heqh.right]
            assumption
          have imhts₃ : IsMinHeap le (.heap ts₃) := by
            rw[← heq₄]
            apply children_IsMinHeap
            constructor
            . apply IsSearchTree_findMin <;>
              . rw[heqh.right] at h₂
                cases h₂ with | cons _ mh =>
                cases mh
                assumption
            . constructor
          apply IsMinHeap_merge <;> assumption

