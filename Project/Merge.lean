import Project.Main
universe u

namespace project

variable {le : α → α → Bool} 
(not_le_le : ∀ x y, ¬ le x y → le y x) 

theorem empty_heap_merge_left : mergeNodes le [] h = h := by
  unfold mergeNodes
  split
  . rfl 
  . rfl
  . rename_i heq
    cases heq

theorem empty_heap_merge_right : mergeNodes le h [] = h := by
  unfold mergeNodes
  split
  . rfl
  . rfl
  . rename_i heq
    cases heq
  
theorem IsHeapForest'_weaken : IsHeapForest' n xs → m ≤ n → IsHeapForest' m xs := by
  intros hf hle
  cases hf with 
  | nil => constructor
  | cons hlt _ _ => 
    constructor <;> try assumption
    . apply Nat.lt_of_le_of_lt hle hlt

theorem rank_combine : t₁.rank = t₂.rank → (combine le t₁ t₂).rank = t₁.rank + 1:= by
  intro
  unfold combine
  split
  . dsimp
    simp
    simp_all
  . dsimp

theorem IsHeapForest'_strengthen_pred (hf : IsHeapForest' r (t :: ts)) (hpos : t.rank > 0) : IsHeapForest' (t.rank - 1) (t :: ts) := by
  cases hf
  constructor <;> try assumption
  . apply Nat.sub_lt_self
    . decide
    . assumption

theorem IsHeapForest'_strengthen : IsHeapForest' rx ts → ry < hRank ts → IsHeapForest' ry ts := by
  intros hf _
  cases hf
  . constructor
  . constructor
    repeat assumption

theorem hrank_of_cons : hRank (t :: ts) = t.rank := rfl

theorem Nat.min_eq (x y : Nat) : min x y = if x ≤ y then x else y := rfl

theorem Bool.not_eq_false' (x : Bool) : (!x) = false ↔ x = true := by
  cases x <;> simp

theorem min_hRank_mergeNodes (ht₁ : IsHeapForest' r xs) (ht₂ : IsHeapForest' r ys) : min (hRank xs) (hRank ys) ≤ hRank (mergeNodes le xs ys) := 
  match xs, ys with 
  | [], h  => by
    rw[Nat.min_eq]
    split 
    . rw[empty_heap_merge_left]
      assumption
    . rw[empty_heap_merge_left]
  | h,  [] => by
    rw[empty_heap_merge_right, Nat.min_eq]
    split
    . rfl
    . simp at *
      apply Nat.le_of_lt
      assumption
  | (h₁ :: t₁), (h₂ :: t₂) => by
    unfold mergeNodes
    split
    . repeat rw[hrank_of_cons]
      rw[Nat.min_eq]
      split
      . rfl
      . simp at *
        apply Nat.le_of_lt
        assumption
    . split
      . repeat rw[hrank_of_cons]
        rw[Nat.min_eq]
        split
        . assumption
        . rfl
      . dsimp
        split
        . split
          . simp at *
            have heq : h₁.rank = h₂.rank := by
              apply Nat.le_antisymm <;> assumption
            repeat rw[hrank_of_cons]
            rw[rank_combine heq]
            rw[Nat.min_eq]
            split <;> apply Nat.le_succ
          . repeat rw[hrank_of_cons] 
            have hf : IsHeapForest' r (combine le h₁ h₂ :: t₁) := by
              simp at *
              have heq : h₁.rank = h₂.rank := by
                apply Nat.le_antisymm <;> assumption
              constructor
              . rw[rank_combine heq] at *
                cases ht₁
                apply Nat.lt_succ_of_lt 
                assumption
              . cases ht₁
                cases ht₂
                apply combine_IsBinTree <;> assumption
              . cases ht₁ with | cons _ _ hf =>
                  rw[rank_combine heq] at *
                  match hf with
                  | .nil => 
                    constructor
                  | .cons (t := t) (ts := ts) lt _ _ =>
                    constructor
                    . rw[hrank_of_cons] at *
                      rename_i neq
                      unfold bne at neq
                      rw[Nat.not_beq_eq_true_eq] at neq
                      have : h₁.rank + 1 ≤  t.rank := by
                        apply Nat.succ_le_of_lt lt
                      apply lt_of_le_of_ne <;> assumption
                    repeat assumption
            have hf₂ : IsHeapForest' r t₂ := by
              cases ht₂
              apply IsHeapForest'_weaken
              . assumption
              . apply Nat.le_of_lt
                assumption
            have ih := min_hRank_mergeNodes hf hf₂
            transitivity (min (hRank (combine le h₁ h₂ :: t₁)) (hRank t₂))
            . rw[hrank_of_cons] at *
              simp at *
              have heq : h₁.rank = h₂.rank := by
                apply Nat.le_antisymm <;> assumption
              rw[rank_combine heq] at *
              repeat rw[Nat.min_eq]
              split
              . split
                . apply Nat.le_succ
                . simp at *
                  rename_i heq₂ _ hlt
                  unfold bne at heq₂
                  rw [Bool.not_eq_false', beq_iff_eq] at heq₂
                  simp [← heq₂] at hlt 
              . split
                . apply Nat.le_succ
                . rename_i heq₂ _ hnle
                  unfold bne at heq₂
                  rw [Bool.not_eq_false', beq_iff_eq] at heq₂
                  simp [← heq₂] at hnle
            . apply ih
        . split
          . repeat rw[hrank_of_cons]
            have hf : IsHeapForest' r t₁ := by
              cases ht₁
              apply IsHeapForest'_weaken
              . assumption
              . apply Nat.le_of_lt
                assumption
            have hf₂ : IsHeapForest' r (combine le h₁ h₂ :: t₂) := by
              simp at *
              have heq : h₁.rank = h₂.rank := by
                apply Nat.le_antisymm <;> assumption
              constructor
              . cases ht₁
                rw[rank_combine heq] at *
                apply Nat.lt_succ_of_lt
                assumption
              . cases ht₁
                cases ht₂
                apply combine_IsBinTree <;> assumption
              . rw[rank_combine heq] at *
                cases ht₂ with | cons _ _ hf₂ =>
                  match hf₂ with
                  | .nil => 
                    constructor
                  | .cons (t := t) (ts := ts) lt _ _ => 
                    rename_i hneq
                    rw[hrank_of_cons] at *
                    constructor
                    . rw[← heq] at lt
                      unfold bne at hneq
                      rw[Nat.not_beq_eq_true_eq] at hneq
                      apply lt_of_le_of_ne <;> assumption
                    repeat assumption
            have ih := min_hRank_mergeNodes hf hf₂
            transitivity (min (hRank t₁) (hRank (combine le h₁ h₂ :: t₂)))
            . rw[hrank_of_cons] at *
              simp at *
              have heq : h₁.rank = h₂.rank := by
                apply Nat.le_antisymm <;> assumption
              rw[rank_combine heq] at *
              repeat rw[Nat.min_eq]
              split
              . split
                . cases ht₁ with | cons _ _ hf₃ =>
                    cases hf₃
                    . contradiction
                    . rw[hrank_of_cons]
                      apply Nat.le_of_lt
                      assumption
                . apply Nat.le_succ
              . split
                . cases ht₁ with | cons _ _ hf₃ =>
                    cases hf₃
                    . contradiction
                    . rw[hrank_of_cons]
                      apply Nat.le_of_lt
                      assumption
                . apply Nat.le_succ
            . apply ih
          . repeat rw[hrank_of_cons]
            simp at *
            have heq : h₁.rank = h₂.rank := by
              apply Nat.le_antisymm <;> assumption
            rw[rank_combine heq]
            rw[Nat.min_eq]
            split <;> apply Nat.le_succ
  termination_by _  => xs.length + ys.length
  decreasing_by simp_wf; simp_arith [*]

theorem hRank_mergeNodes_cons (ht₁ : IsHeapForest' r (u :: y)) (ht₂ : IsHeapForest' r (c :: z)) : u.rank = c.rank → u.rank + 1 ≤ hRank (mergeNodes le (u :: y) (c :: z)) := by
  intros heq
  unfold mergeNodes
  split
  . have : u.rank ≠ c.rank := by
      apply ne_of_lt
      assumption
    contradiction 
  . split
    . have hneq : c.rank ≠ u.rank := by
        apply ne_of_lt
        assumption
      have : c.rank = u.rank := by
        apply Eq.symm heq
      contradiction 
    . dsimp
      split
      . split
        . rw[hrank_of_cons]
          rw[rank_combine heq] at *
        . have hf : IsHeapForest' r (combine le u c :: y) := by
            constructor
            . rw[rank_combine heq] at *
              cases ht₁ with | cons lt _ _ =>
                apply Nat.lt_succ_of_lt lt
            . cases ht₁
              cases ht₂
              apply combine_IsBinTree <;> assumption
            . cases ht₁ with | cons _ _ hf =>
                cases ht₂ with | cons =>
                  match hf with
                  | .nil =>
                    constructor
                  | .cons (t := t) (ts := ts) lt _ _ =>
                    rename_i neq
                    rw[rank_combine heq, hrank_of_cons] at *
                    unfold bne at neq
                    rw[Nat.not_beq_eq_true_eq] at neq
                    have : u.rank + 1 ≤ t.rank := by
                      apply Nat.succ_le_of_lt lt
                    constructor
                    . apply lt_of_le_of_ne <;> assumption
                    . assumption
                    . assumption
          have hf₂ : IsHeapForest' r z := by
            cases ht₂
            apply IsHeapForest'_weaken
            . assumption
            . apply Nat.le_of_lt 
              assumption
          have min_le : min (hRank (combine le u c :: y)) (hRank z) ≤ hRank (mergeNodes le (combine le u c :: y) z) := by
            apply min_hRank_mergeNodes hf hf₂
          repeat rw[hrank_of_cons] at *
          rw[Nat.min_eq] at min_le
          rw[rank_combine heq] at *
          split at min_le
          . assumption
          . unfold bne at *
            rw[Nat.not_beq_eq_true_eq] at *
            simp_all
      . split
        . have hf : IsHeapForest' r (combine le u c :: z) := by
            constructor
            . rw[rank_combine heq] at *
              cases ht₂ with | cons lt _ _ =>
                rw[← heq] at lt
                apply Nat.lt_succ_of_lt lt
            . cases ht₁
              cases ht₂
              apply combine_IsBinTree <;> assumption
            . cases ht₁ with | cons =>
                cases ht₂ with  | cons _ _ hf =>
                  match hf with
                  | .nil =>
                    constructor
                  | .cons (t := t) (ts := ts) lt _ _ =>
                    rename_i neq
                    rw[rank_combine heq, hrank_of_cons] at *
                    unfold bne at neq
                    rw[Nat.not_beq_eq_true_eq] at neq
                    have hle : c.rank + 1 ≤ t.rank := by
                      apply Nat.succ_le_of_lt lt
                    constructor
                    . rw[← heq] at hle
                      apply lt_of_le_of_ne <;> assumption
                    . assumption
                    . assumption
          have hf₂ : IsHeapForest' r y := by
            cases ht₁
            apply IsHeapForest'_weaken
            . assumption
            . apply Nat.le_of_lt 
              assumption
          have min_le : min (hRank y) (hRank (combine le u c :: z)) ≤ hRank (mergeNodes le y (combine le u c :: z)) := by
            apply min_hRank_mergeNodes hf₂ hf
          repeat rw[hrank_of_cons] at *
          rw[Nat.min_eq] at min_le
          rw[rank_combine heq] at *
          split at min_le
          . unfold bne at *
            rw[Nat.not_beq_eq_true_eq] at *
            simp_all
          . assumption
        . rw[hrank_of_cons, rank_combine heq]

theorem IsHeapForest'_of_IsHeapForest' : IsBinTree r → y < r.rank → IsHeapForest' r.rank x → IsHeapForest' y (r :: x) := by
  intros
  constructor <;> assumption

theorem IsHeap_merge (hxs : IsHeapForest' rx xs) (hys : IsHeapForest' ry ys) :  IsHeapForest' (min rx ry) (mergeNodes le xs ys) :=
  match xs, ys with
  | [], h  => by
    rw [empty_heap_merge_left]
    apply IsHeapForest'_weaken hys
    apply min_le_right 
  | h,  [] =>  by
    rw[empty_heap_merge_right]
    apply IsHeapForest'_weaken hxs
    apply min_le_left
  | (h₁ :: t₁), (h₂ :: t₂) => by
    unfold mergeNodes
    split
    . constructor
      . cases hxs
        rw[Nat.min_eq]
        split
        . assumption
        . rename_i nle
          simp at nle
          apply Nat.lt_trans nle
          assumption
      . cases hxs
        assumption
      . cases hxs with | cons hlt bt hf =>
          rename_i hlt₂
          have : h₁.rank = min h₁.rank (h₂.rank - 1) := by
            have hle : h₁.rank ≤ (h₂.rank - 1) := by
              apply Nat.le_pred_of_lt hlt₂
            have : min h₁.rank (h₂.rank - 1) = h₁.rank := by
              apply min_eq_left hle
            rw[this]
          rw [this]; clear this
          apply IsHeap_merge
          . assumption
          . apply IsHeapForest'_strengthen_pred
            . assumption
            . cases bt with | mk =>
                have hge : h₁.rank ≥ 0 := by
                  cases h₁.rank
                  . simp 
                  . simp
                have hle : 0 ≤ h₁.rank := by
                  apply hge
                have : 0 < h₂.rank := by
                  apply lt_of_le_of_lt hle hlt₂
                assumption
    . split
      . constructor
        . rw[Nat.min_eq]
          split
          . cases hys
            apply Nat.lt_of_le_of_lt <;> assumption
          . cases hys
            assumption
        . cases hys
          assumption
        . have heq : min h₂.rank (h₁.rank -1) = h₂.rank := by
            have : h₂.rank ≤ (h₁.rank - 1) := by
              apply Nat.le_pred_of_lt
              assumption
            apply min_eq_left
            assumption
          rw[← heq]
          apply IsHeap_merge 
          . cases hys
            assumption
          . constructor
            . cases hxs
              apply Nat.pred_lt
              simp
              cases rx <;> apply Nat.not_eq_zero_of_lt; repeat assumption
            . cases hxs
              assumption
            . cases hxs
              assumption
      . dsimp
        split
        . split
          . rename_i hneq hneq₂ 
            simp at * 
            have heq : h₁.rank = h₂.rank := by
              apply Nat.le_antisymm <;> assumption
            constructor
            . have : (combine le h₁ h₂).rank = h₁.rank + 1 := by
                apply rank_combine heq
              rw[this]; clear this
              rw[Nat.min_eq]
              split
              . cases hxs
                apply Nat.lt_succ_of_lt 
                assumption
              . cases hys
                rw[heq]
                apply Nat.lt_succ_of_lt
                assumption
            . cases hxs
              cases hys
              apply combine_IsBinTree <;> assumption
            . rw[rank_combine heq] at *
              cases hxs with | cons _ _ ht₁ => 
              cases hys with | cons _ _ ht₂ =>
              have ih := IsHeap_merge ht₁ ht₂
              have min_le : min (hRank t₁) (hRank t₂) ≤ hRank (mergeNodes le t₁ t₂) := by 
                rw[← heq] at ht₂
                apply min_hRank_mergeNodes ht₁ ht₂
              by_cases (t₁ = [] ∧ t₂ = [])
              . have (And.intro he₁ he₂) := h
                simp[he₁, he₂]
                constructor
              . apply IsHeapForest'_strengthen
                . apply ih
                . rw[Nat.min_eq] at min_le
                  split at min_le
                  . match ht₁ with
                    | .nil =>
                      rw[empty_heap_merge_left] at *
                      match ht₂ with
                      | .nil => simp at h
                      | .cons (t := bt) hlt _ _ =>
                        rw[hrank_of_cons] at *
                        rw[← heq] at hlt
                        unfold bne at hneq₂
                        rw[Nat.not_beq_eq_true_eq] at hneq₂
                        have n : h₁.rank + 1 ≤ bt.rank := by
                          apply Nat.succ_le_of_lt hlt 
                        apply lt_of_le_of_ne <;> assumption
                    | .cons (t := t) (ts := ts) hlt _ _ =>
                      rw[hrank_of_cons] at *
                      have : h₁.rank < hRank (mergeNodes le (t :: ts) t₂) := by
                        apply lt_of_lt_of_le <;> assumption
                      unfold bne at hneq
                      rw[Nat.not_beq_eq_true_eq] at hneq
                      have : h₁.rank + 1 ≤ t.rank := by
                        apply Nat.succ_le_of_lt hlt
                      have : h₁.rank + 1 < t.rank := by
                        apply lt_of_le_of_ne <;> assumption
                      apply lt_of_lt_of_le <;> assumption
                  . match ht₂ with
                    | .nil => 
                      rw[empty_heap_merge_right] at *
                      match ht₁ with
                      | .nil =>
                        simp at h
                      | .cons (t := t) (ts := ts) lt _ _ => 
                        rw[hrank_of_cons] at *
                        unfold bne at hneq
                        rw[Nat.not_beq_eq_true_eq] at hneq
                        have : h₁.rank + 1 ≤ t.rank := by
                          apply Nat.succ_le_of_lt lt
                        apply lt_of_le_of_ne <;> assumption
                    | .cons (t := t) (ts := ts) lt _ _ =>
                      rw[hrank_of_cons] at *
                      rw[← heq] at lt
                      have : h₁.rank + 1 ≤ t.rank := by
                        apply Nat.succ_le_of_lt lt
                      unfold bne at hneq₂
                      rw[Nat.not_beq_eq_true_eq] at hneq₂
                      have : h₁.rank + 1 < t.rank := by
                        apply lt_of_le_of_ne <;> assumption
                      apply lt_of_lt_of_le <;> assumption
          . apply IsHeap_merge
            simp at *
            have heq : h₁.rank = h₂.rank := by
              apply Nat.le_antisymm <;> assumption
            . constructor
              . cases hxs with | cons lt _ _ =>
                  rw[rank_combine heq]
                  have : h₁.rank < h₁.rank + 1 := by
                    apply Nat.lt_succ_self
                  apply lt_trans lt this
              . cases hxs 
                cases hys
                apply combine_IsBinTree <;> assumption
              . match hxs with
                | .cons _ _ hf =>
                  have : (combine le h₁ h₂).rank = h₁.rank + 1 := by
                    apply rank_combine heq
                  simp only [this] at *; clear this
                  match hf with
                  | .nil =>
                    constructor
                  | .cons (t := t) (ts := ts) lt _ _ =>
                    constructor
                    . have : h₁.rank + 1 ≤ t.rank := by
                        apply Nat.succ_le_of_lt lt
                      apply lt_of_le_of_ne this
                      rw[hrank_of_cons] at *
                      unfold bne at *
                      rw[Nat.not_beq_eq_true_eq] at *
                      assumption
                    . assumption
                    . assumption
            . cases hys with | cons lt _ hf =>
                have : ry ≤ h₂.rank := by
                    apply le_of_lt lt
                apply IsHeapForest'_weaken hf this
        . split
          . apply IsHeap_merge
            . cases hxs with | cons lt _ hf =>
                have : rx ≤ h₁.rank := by
                    apply le_of_lt lt
                apply IsHeapForest'_weaken hf this
            . constructor
              . simp at *
                have heq : h₁.rank = h₂.rank := by
                  apply Nat.le_antisymm <;> assumption
                rw[rank_combine heq] at *
                cases hys
                rw[heq]
                apply Nat.lt_succ_of_lt
                assumption
              . cases hxs with | cons =>
                  cases hys with | cons =>
                    simp at *
                    have : h₁.rank = h₂.rank := by
                      apply Nat.le_antisymm <;> assumption
                    apply combine_IsBinTree <;> assumption
              . simp at *
                have heq : h₁.rank = h₂.rank := by
                  apply Nat.le_antisymm <;> assumption
                rw[rank_combine heq] at *
                cases hys with | cons _ _ hf =>
                  match hf with 
                  | .nil =>
                    constructor
                  | .cons (t := t) (ts := ts) lt _ _ =>
                    rw[← heq] at lt
                    have b : h₁.rank + 1 ≤ t.rank := by
                      apply Nat.succ_le_of_lt lt
                    rw[hrank_of_cons] at *
                    constructor
                    . unfold bne at *
                      rw[Nat.not_beq_eq_true_eq] at *
                      apply lt_of_le_of_ne <;> assumption
                    repeat assumption      
          . simp at * 
            have heq : h₁.rank = h₂.rank := by
              apply Nat.le_antisymm <;> assumption
            constructor
            . rw[Nat.min_eq]
              split
              . rw[rank_combine heq] at *
                cases hxs
                apply Nat.lt_succ_of_lt
                assumption
              . rw[rank_combine heq] at *
                cases hys
                rw[heq]
                apply Nat.lt_succ_of_lt
                assumption                
            . cases hxs
              cases hys
              apply combine_IsBinTree <;> assumption
            . rw[rank_combine heq] at *
              cases hxs with | cons _ _ hf =>
              cases hys with | cons _ _ hf₂ =>
              have ih := IsHeap_merge hf hf₂ 
              have hle : min (hRank t₁) (hRank t₂) ≤ hRank (mergeNodes le t₁ t₂) := by 
                rw[← heq] at hf₂
                apply min_hRank_mergeNodes hf hf₂
              by_cases (t₁ = [] ∧ t₂ = [])
              . have he₁ := h.left
                have he₂ := h.right
                simp[he₁, he₂]
                constructor
              . apply IsHeapForest'_strengthen
                . apply ih
                . rw[Nat.min_eq] at hle
                  split at hle
                  . match hf₂ with
                    | .nil =>
                      rw[empty_heap_merge_right] at *
                      match hf with
                      | .nil =>
                        contradiction
                      | .cons (t := t) (ts := ts) _ _ _ =>
                        rw[hrank_of_cons] at *
                        unfold bne at *
                        rw[Bool.not_eq_false', beq_iff_eq] at *
                        simp at *
                        contradiction
                    | .cons (t := t) (ts := ts) _ _ _ => 
                      match hf with
                      | .nil => 
                        rw[empty_heap_merge_left] at *
                        rw[hrank_of_cons] at *
                        unfold bne at *
                        rw[Bool.not_eq_false', beq_iff_eq] at *
                        simp at *
                        contradiction
                      | .cons (t := t₂) (ts := ts₂) _ _ _ =>
                        repeat rw[hrank_of_cons] at *
                        unfold bne at *
                        rw[Bool.not_eq_false', beq_iff_eq] at *
                        simp at *
                        have ht₁ : IsHeapForest' h₁.rank (t₂ :: ts₂) := by
                          apply IsHeapForest'_of_IsHeapForest' <;> assumption
                        have ht₂ : IsHeapForest' h₁.rank (t :: ts) := by
                          rw[← heq] at *
                          apply IsHeapForest'_of_IsHeapForest' <;> assumption
                        have : t₂.rank + 1 ≤ hRank (mergeNodes le (t₂ :: ts₂) (t :: ts)) := by
                          apply hRank_mergeNodes_cons ht₁ ht₂
                          simp_all
                        rename_i heq₂ _
                        rw[heq₂]
                        apply Nat.lt_of_succ_le this
                  . match hf₂ with
                    | .nil =>
                      rw[empty_heap_merge_right] at *
                      cases hf
                      . contradiction
                      . rw[hrank_of_cons] at *
                        unfold bne at *
                        rw[Bool.not_eq_false', beq_iff_eq] at *
                        simp at *
                        contradiction
                    | .cons (t := t) (ts := ts) _ _ _ =>
                      rw[hrank_of_cons] at *
                      unfold bne at *
                      rw[Bool.not_eq_false', beq_iff_eq] at *
                      simp at *
                      match hf with
                      | .nil =>
                        contradiction
                      | .cons (t := t₂) (ts := ts₂) _ _ _ =>
                        rw[hrank_of_cons] at *
                        simp at *
                        have ht₁ : IsHeapForest' h₁.rank (t₂ :: ts₂) := by
                          apply IsHeapForest'_of_IsHeapForest' <;> assumption
                        have ht₂ : IsHeapForest' h₁.rank (t :: ts) := by
                          rw[← heq] at *
                          apply IsHeapForest'_of_IsHeapForest' <;> assumption
                        have : t₂.rank + 1 ≤ hRank (mergeNodes le (t₂ :: ts₂) (t :: ts)) := by
                          apply hRank_mergeNodes_cons ht₁ ht₂
                          simp_all
                        rename_i heq₂ _
                        rw[heq₂]
                        apply Nat.lt_of_succ_le this 
termination_by _  => xs.length + ys.length
decreasing_by simp_wf; simp_arith [*]


theorem IsMinHeap_merge : IsMinHeap le (.heap hx) → IsMinHeap le (.heap hy) → IsMinHeap le (.heap (mergeNodes le hx hy)) := 
  match hx, hy with
  | [], h => by
    intros _ hys
    cases hys
    . simp[mergeNodes]
      constructor
    . constructor <;> assumption
  | h, [] => by
    intros hxs _
    cases hxs
    . simp[mergeNodes]
      constructor
    . constructor <;> assumption
  | (h₁ :: t₁), (h₂ :: t₂) => by
    intros hxs hys
    unfold mergeNodes
    split
    . constructor
      . cases hxs
        assumption
      . cases hxs
        apply IsMinHeap_merge <;> assumption
    . split
      . constructor
        . cases hys
          assumption
        . cases hys
          apply IsMinHeap_merge <;> assumption
      . dsimp
        split
        . split
          . constructor
            . apply combine_IsSearchTree
              . assumption
              . cases hxs
                assumption
              . cases hys
                assumption
            . apply IsMinHeap_merge
              . cases hxs
                assumption
              . cases hys
                assumption
          . apply IsMinHeap_merge
            . constructor
              . apply combine_IsSearchTree
                . assumption
                . cases hxs
                  assumption
                . cases hys
                  assumption
              . cases hxs
                assumption
            . cases hys
              assumption
        . split
          . apply IsMinHeap_merge
            . cases hxs
              assumption
            . constructor
              . apply combine_IsSearchTree
                . assumption
                . cases hxs
                  assumption
                . cases hys
                  assumption
              . cases hys
                assumption
          . constructor
            . apply combine_IsSearchTree
              . assumption
              . cases hxs
                assumption 
              . cases hys
                assumption
            . apply IsMinHeap_merge
              . cases hxs
                assumption
              . cases hys
                assumption
  termination_by _  => hx.length + hy.length
  decreasing_by simp_wf; simp_arith [*]