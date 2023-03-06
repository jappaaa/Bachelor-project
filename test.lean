  def sub : Nat → Nat → Nat
    | 0, m => 0
    | n, 0 => n
    | n+1, m+1 =>  sub n m 

#eval sub 10 1

variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := 
  Iff.intro
    (fun hpq => And.intro hpq.right hpq.left)
    (fun hqp => And.intro hqp.right hqp.left)

example : p ∨ q ↔ q ∨ p := 
  Iff.intro
    (fun hpq => 
      Or.elim hpq
        (fun hp : p => 
          show q ∨ p from Or.inr hp)
        (fun hq : q =>
          show q ∨ p from Or.inl hq))
    (fun hqp => 
      Or.elim hqp
        (fun hq : q => 
          show p ∨ q from Or.inr hq)
        (fun hp : p =>
          show p ∨ q from Or.inl hp))

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := 
  Iff.intro
    (fun h₁ =>
      have h₃: p ∧ q := h₁.left
      And.intro h₃.left (And.intro h₃.right h₁.right))
    (fun h₂ => 
      have h₄: q ∧ r := h₂.right
      And.intro (And.intro h₂.left h₄.left) h₄.right)

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := 
  Iff.intro
    (fun h₁ =>
      Or.elim h₁
        (fun h₂: p ∨ q =>
          Or.elim h₂ 
            (fun h₅: p =>
              show p ∨ (q ∨ r) from Or.inl h₅)
            (fun h₆: q =>
              have h₇: q ∨ r := Or.inl h₆
              show p ∨ (q ∨ r) from Or.inr h₇))
        (fun h₃: r =>
          have h₄: q ∨ r := Or.inr h₃
          show p ∨ (q ∨ r) from Or.inr h₄))
    (fun h₂ =>
      Or.elim h₂
        (fun h₃: p =>
          have h₅: p ∨ q := Or.inl h₃
          show (p ∨ q) ∨ r from Or.inl h₅)
        (fun h₄: q ∨ r =>
          Or.elim h₄ 
            (fun h₅: q =>
              have h₇: p ∨ q := Or.inr h₅
              show (p ∨ q) ∨ r from Or.inl h₇)
            (fun h₆: r =>
              show (p ∨ q) ∨ r from Or.inr h₆)))

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := 
  Iff.intro
    (fun h₁ =>
      have h₂: q ∨ r := h₁.right
      Or.elim h₂
        (fun h₃: q =>
          show (p ∧ q) ∨ (p ∧ r) from Or.inl (And.intro h₁.left h₃))
        (fun h₄: r =>
          show (p ∧ q) ∨ (p ∧ r) from Or.inr (And.intro h₁.left h₄)))
    (fun h₁ =>
      Or.elim h₁
        (fun h₂: p ∧ q =>
          And.intro h₂.left (Or.inl h₂.right))
        (fun h₃: p ∧ r =>
          And.intro h₃.left (Or.inr h₃.right)))

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := 
  Iff.intro
    (fun h₁ =>
      Or.elim h₁
        (fun h₂: p =>
          show (p ∨ q) ∧ (p ∨ r) from And.intro (Or.inl h₂) (Or.inl h₂))
        (fun h₂: q ∧ r =>
          show (p ∨ q) ∧ (p ∨ r) from And.intro (Or.inr h₂.left) (Or.inr h₂.right)))
    (fun h₁ =>
      have h₂: p ∨ q := h₁.left
      have h₃: p ∨ r := h₁.right
      Or.elim h₂
        (fun h₄: p =>
          Or.inl h₄)
        (fun h₄: q =>
          Or.elim h₃
            (fun h₅: p =>
              Or.inl h₅)
            (fun h₅: r =>
              Or.inr (And.intro h₄ h₅))))

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := 
  Iff.intro
    (fun h₁ =>
      fun h₂ =>
        h₁ h₂.left h₂.right)
    (fun h₁ =>
      fun h₂ =>
        fun h₃ =>
          have h₄: p ∧ q := And.intro h₂ h₃
          h₁ h₄)

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := 
  Iff.intro
    (fun h₁ =>
      fun h₂: p ∨ q =>
      Or.elim h₂
        (fun h₃: p =>
          )
        (fun h3: q =>
          ))
    (fun h₁ =>
      _)
example : ¬p ∨ ¬q → ¬(p ∧ q) := 
  fun h₁ => show ¬(p ∧ q) from (
    fun h₂: p ∧ q => show False from (
      Or.elim h₁
        (fun h₃: ¬p =>
          show False from h₃ h₂.left)
        (fun h₃: ¬q =>
          show False from h₃ h₂.right)
    )
  )
example : ¬(p ∧ ¬p) := 
  fun h₁ : p ∧ ¬p =>
  show False from (
    have h₂: p := h₁.left
    have h₃: ¬p := h₁.right
    h₃ h₂
  )
example : p ∧ ¬q → ¬(p → q) := 
  fun h₁ => 
    fun h₂: p → q => show False from (
      have h₃: ¬q := h₁.right
      have h₄: p := h₁.left
      h₃ (h₂ h₄)
    )
example : ¬p → (p → q) := 
  fun h₁ =>
    fun h₂ =>
      absurd h₂ h₁
example : (¬p ∨ q) → (p → q) :=
  fun h₁ =>
    fun h₂ =>
      Or.elim h₁
      (fun h₃: ¬p =>
        show q from absurd h₂ h₃)
      (fun h₃: q =>
        h₃)
example : p ∨ False ↔ p := 
  Iff.intro
  (fun h₁ =>
    Or.elim h₁
    (fun h₂: p =>
      h₂)
    (fun h₂: False => 
      False.elim h₂))
  (fun h₁ =>
    Or.inl h₁)
example : p ∧ False ↔ False := 
  Iff.intro
  (fun h₁ =>
    h₁.right)
  (fun h₂ =>
    have h₃: p := False.elim h₂
    And.intro h₃ h₂)
example : (p → q) → (¬q → ¬p) := 
  fun h₁ =>
    fun h₂ =>
      fun h₃: p => show False from(
        have h₄: q := h₁ h₃
        h₂ h₄
      )

variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := 
  Iff.intro
  (fun h₁ =>
    And.intro 
    (fun y: α =>
      (h₁ y).left)
    (fun u: α =>
      (h₁ u).right))
  (fun h₁ =>
    fun y: α =>
      have h₂: p y := h₁.left y
      have h₃: q y := h₁.right y
      And.intro h₂ h₃)
example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := 
  fun h₁ =>
    fun h₂ =>
      fun y: α =>
        (h₁ y) (h₂ y)
example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := 
  fun h₁ =>
    Or.elim h₁
    (fun h₂: ∀ x, p x =>
      fun y: α =>
        Or.inl (h₂ y))
    (fun h₂: ∀ x, q x => 
      fun y: α =>
        Or.inr (h₂ y))
  
variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ x : α, r) ↔ r) := 
  fun h₁ => 
    Iff.intro
    (fun h₂ =>
      h₂ h₁)
    (fun h₂ =>
      fun h₃ =>
        h₂)

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := 
  Iff.intro
  (fun h₁ =>
    fun h₂ =>
    fun y: α =>
      have h₃ : r → p y := h₁ y
      h₃ h₂)
  (fun h₁ =>
    fun y: α =>
      fun h₂ =>
      have h₃: ∀ (x : α), p x := h₁ h₂
      h₃ y)

variable (men : Type) (barber : men)
variable  (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := 
    have h₁: shaves barber barber ↔ ¬ shaves barber barber := h barber
    have h₂: shaves barber barber → ¬ shaves barber barber := h₁.mp
    show False from(
      fun h₃: shaves barber barber =>
        have h₄: ¬ shaves barber barber := h₂ h₃
        h₄ h₃
    )


open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ x : α, r) → r := 
  fun h₁ =>
    Exists.elim h₁
    (fun w =>
      fun hr: r =>
      hr)

example (a : α) : r → (∃ x : α, r) := 
  fun h₁ =>
    Exists.intro a h₁

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := 
  Iff.intro
  (fun h₁: ∃ x, p x ∧ r =>
    Exists.elim h₁
    (fun y: α =>
      fun h₂: p y ∧ r =>
        have h₃: ∃ x, p x := Exists.intro y h₂.left
        And.intro h₃ h₂.right))
  (fun h₁: (∃ x, p x) ∧ r =>
    have h₂: ∃ x, p x := h₁.left
    Exists.elim h₂
    (fun w: α =>
      fun h₃: p w =>
      have h₄: p w ∧ r := And.intro h₃ h₁.right
      Exists.intro w h₄))

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := 
  Iff.intro
  (fun h₁ =>
    Exists.elim h₁
    (fun w: α =>
      fun h₂: p w ∨ q w =>
        Or.elim h₂
        (fun h₃: p w =>
          have h₄: ∃ x, p x := Exists.intro w h₃
          Or.inl h₄)
        (fun h₃: q w =>
          have h₄: ∃ x, q x := Exists.intro w h₃
          Or.inr h₄)))
  (fun h₁ =>
    Or.elim h₁
    (fun h₂: ∃ x, p x =>
      Exists.elim h₂
      (fun w: α =>
        fun h₃: p w =>
          have h₄: p w ∨ q w := Or.inl h₃
          Exists.intro w h₄))
    (fun h₂: ∃ x, q x =>
      Exists.elim h₂
      (fun w: α =>
        fun h₃: q w =>
          have h₄: p w ∨ q w := Or.inr h₃
          Exists.intro w h₄))

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := 
  Iff.intro
  (fun h₁ =>
    fun y: α =>
      have h₂: p y := h₁ y
      have h₃: ∃ x, p x := Exists.intro y h₂
      byContradiction
      (fun h₄: ∃ x, ¬ p x =>
        show False from h₄ h₃))
  (fun h₁ =>
    )
example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := 
  Iff.intro
  (fun h₁ =>
    Exists.elim h₁
    (fun y: α =>
      fun h₂: p y =>
        byContradiction
        (fun h₃: ∀ x, ¬ p x =>
          h₃ h₂)))
  (fun h₁ =>
    )


variable (p q r : Prop)

example : p ∧ q ↔ q ∧ p := by
apply Iff.intro
. intro h
  apply And.intro 
  . exact h.right
  . exact h.left
. intro h 
  apply And.intro
  . exact h.right
  . exact h.left


example : p ∨ q ↔ q ∨ p := by
apply Iff.intro
. intro h
  apply Or.elim h
  . intro hp
    apply Or.inr hp
  . intro hq
    apply Or.inl hq
. intro h
  apply Or.elim h
  . intro hq
    apply Or.inr hq
  . intro hp
    apply Or.inl hp

example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intros
  apply Eq.trans
  apply Eq.symm
  assumption
  assumption  

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
apply Iff.intro
. intro h
  cases h with
  | intro hpq hr => constructor; exact hpq.left; constructor; exact hpq.right; assumption
. intro h
  cases h with 
  | intro hp hqr => constructor; constructor; assumption; exact hqr.left; exact hqr.right



example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
apply Iff.intro
. intro h
  cases h with 
  | inl hpq => 
    apply Or.elim hpq
    . intro hp
      apply Or.inl
      assumption
    . intro hq
      apply Or.inr
      apply Or.inl
      assumption
  | inr hr => 
    apply Or.inr
    apply Or.inr
    assumption
. intro h
  cases h with
  | inl hp => 
    apply Or.inl
    apply Or.inl
    assumption
  | inr hqr =>  
    apply Or.elim hqr
    . intro hq
      apply Or.inl
      apply Or.inr
      assumption
    . intro hr
      apply Or.inr
      assumption


example (p q : Prop) : p ∧ q → q ∧ p := by
  intro h
  cases h with
  | intro hp hq => apply And.intro; exact hq; exact hp



-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
apply Iff.intro
. intro h
  have hp := h.left
  have hqr := h.right
  apply Or.elim hqr
  . intro hq
    apply Or.inl
    constructor
    repeat assumption
  . intro hr
    apply Or.inr
    constructor 
    repeat assumption
. intro h
  apply Or.elim h
  . intro hpq
    constructor
    exact hpq.left
    apply Or.inl 
    exact hpq.right
  . intro hpr 
    constructor
    exact hpr.left
    apply Or.inr 
    exact hpr.right



example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by 
apply Iff.intro
. intro h
  cases h with
  | inl hp => constructor; apply Or.inl; exact hp; apply Or.inl; exact hp
  | inr hqr => constructor; apply Or.inr; exact hqr.left; apply Or.inr; exact hqr.right
. intro h
  match h with 
  | ⟨ Or.inl hp, Or.inl hp2 ⟩ => apply Or.inl; assumption 
  | ⟨ Or.inl hp, Or.inr hr ⟩ => apply Or.inl; assumption
  | ⟨ Or.inr hq, Or.inl hp ⟩ => apply Or.inl; assumption
  | ⟨ Or.inr hq, Or.inr hr ⟩ => apply Or.inr; constructor; repeat assumption
      

def f (x y z : Nat) : Nat :=
  match x, y, z with
  | 5, _, _ => y
  | _, 5, _ => y
  | _, _, 5 => y
  | _, _, _ => 1

example (x y z : Nat) : x ≠ 5 → y ≠ 5 → z ≠ 5 → z = w → f x y w = 1 := by
  intros
  simp [f]
  split
  . contradiction
  . contradiction
  . contradiction
  . rfl    
        
theorem append_nil (as : List α) : append as nil = as := 
rfl

theorem append_assoc (as bs cs : List α)
        : append (append as bs) cs = append as (append bs cs) :=
sorry

open List

def length (t: List α) : Nat :=
  match t with
  | nil => 0
  | cons a as =>  1 + (length as) 

example : p ∨ q → q ∨ p := by
  intro h
  match h with
  | Or.inl h1  => apply Or.inr; exact h1
  | Or.inr h2 => apply Or.inl; exact h2