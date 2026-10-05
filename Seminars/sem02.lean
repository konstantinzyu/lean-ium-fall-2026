/-!
# Seminar 2
Propositions as types
-/

/- Implicit arguments -/

def id1 : (α : Type) → α → α := λ _ x ↦ x

#check id1
#check id1 Nat 5
#check id1 Prop True
#check_failure id1 5

def id2 : {α : Type} → α → α := λ x ↦ x

#check id2
#check id2 5
#check id2 True
#check_failure id2 Nat 5
#check @id2
#check @id2 Nat 5

def compose {α β γ : Type} (f : α → β) (g : β → γ) :
  α → γ := λ x ↦ g (f x)

/- Structures -/

structure PointNatNat : Type where
  mk ::
  x : Nat
  y : Nat

#check PointNatNat
#check PointNatNat.mk
#check PointNatNat.x
#check PointNatNat.y


#check PointNatNat.mk 1 2
#check ({ x := 1, y := 2 } : PointNatNat)
#check ({ y := 2, x := 1 } : PointNatNat)
#check_failure {x := 1, y := 2}

#check_failure {x := 1, y := 2 : Nat}
#check {x := 1, y := 2 : PointNatNat}
#check {x := 1, y := (2 : Nat) : PointNatNat}

def pp : PointNatNat := {x := 0, y := 0}

#eval {pp with x := 3}

#check (⟨0, 1⟩ : PointNatNat)
#eval pp.1
#eval pp.2

structure PointNatNatNat extends PointNatNat where
  z : Nat

#check {x := 0, y := 0, z := 0 : PointNatNatNat}
#check PointNatNatNat.toPointNatNat

structure Prod' (A B : Type) : Type where
  fst : A
  snd : B

#check Prod' Nat Prop

#check Prod
#print Prod
#check Prod Nat Nat
#check Nat × Nat

structure PointType where
  A : Type
  x : A
  y : A

#check { A := Nat, x := 0, y := 0 : PointType }

/- Propositions as Types -/
#check Prop
#check False
#check True

section CH
  axiom And' : Prop → Prop → Prop
  axiom Implies : Prop → Prop → Prop

  variable (p q r : Prop)

  #check Implies (And' p q) (And' q p)

  variable (Proof : Prop → Type)

  variable (modus_ponens : Proof (Implies p q) → Proof p → Proof q)
  variable (implies_intro : (Proof p → Proof q) → Proof (Implies p q))

  /-
  First, we can get rid of `Proof` and identify `Proof p` with `p` itself!
  Second, above axioms show that:
    modus_ponens p q  : Implies p q → (p → q)
    implies_intro p q : (p → q) → Implies p q

  So, we can try identifying Implies p q with the λction space (p → q)
  -/

  #check p

  variable (t : p)
  #check t

  #check (p → q → p)
end CH

/- Implication -/
variable {p q r : Prop}

theorem t1 : p → q → p := λ hp _ ↦ hp

#check t1
#print t1

theorem t1' : p → q → p :=
  λ hp : p ↦
  λ hq : q ↦
  show p from hp

theorem t2 (hp : p) : q → p := t1 hp

example : p → p := sorry
example : (p → q) → (q → r) → p → r := sorry
example : (p → (q → r)) → (p → q) → p → r := sorry

/- And -/
#check And
#print And
#check And p q
#check p ∧ q

example : p → q → p ∧ q := λ hp hq ↦ ⟨hp, hq⟩
example : p ∧ q → q ∧ p := sorry

/- Or -/

#check Or
#print Or
#check Or p q
#check p ∨ q
#check Or.inl
#check Or.inr
#check Or.elim

example : p ∨ q → q ∨ p :=
  λ h ↦ Or.elim h (λ hp ↦ Or.inr hp) (λ hq ↦ Or.inl hq)

/- True -/

#check True
#check True.intro
#check trivial
#print trivial

example : p → True :=
  λ _ ↦ trivial
example : (p ∨ True) ∧ True := sorry

/- False -/

#check False
#check False.elim

example : False → p := False.elim

/- Not -/
#check Not
#print Not
#check Not p
#check ¬ p

example : (p → ¬ p → q) :=
  λ hp hnp ↦ False.elim (hnp hp)

example : (p → q) → (¬ q → ¬ p) := sorry

/- Iff -/

#check Iff
#print Iff
#check Iff p q
#check p ↔ q

example : p ↔ p ∧ p :=
  ⟨λ hp ↦ ⟨hp, hp⟩,
  λ hpp ↦ hpp.left⟩
example : p ∧ q ↔ q ∧ p := sorry

/- Local definitions -/
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (λ h : p ∧ (q ∨ r) ↦
      have hp : p := h.left
      Or.elim (h.right)
        (λ hq : q ↦
          show (p ∧ q) ∨ (p ∧ r) from Or.inl ⟨hp, hq⟩)
        (λ hr : r ↦
          show (p ∧ q) ∨ (p ∧ r) from Or.inr ⟨hp, hr⟩))
    (λ h : (p ∧ q) ∨ (p ∧ r) ↦
      Or.elim h
        (λ hpq : p ∧ q ↦
          have hp : p := hpq.left
          let hq : q := hpq.right
          show p ∧ (q ∨ r) from ⟨hp, Or.inl hq⟩)
        (λ hpr : p ∧ r ↦
          have hp : p := hpr.left
          have hr : r := hpr.right
          show p ∧ (q ∨ r) from ⟨hp, Or.inr hr⟩))

/- Classical logic -/

#check Classical.em

example : ¬¬ p → p :=
  λ h ↦ Or.elim (Classical.em p)
    (λ hp ↦ hp)
    (λ hnp ↦ False.elim (h hnp))
example : ¬(p ∧ ¬q) → (p → q) := sorry
/-!
# Exercises
-/

section hw
  /- Classical.em is not required: -/

example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    (λ ⟨⟨hp, hq⟩, hr⟩ ↦ ⟨hp, ⟨hq, hr⟩⟩)
    (λ ⟨hp, ⟨hq, hr⟩⟩ ↦ ⟨⟨hp, hq⟩, hr⟩)

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
    (λ h ↦ Or.elim h
      (λ hpq ↦ Or.elim hpq
        (λ hp ↦ Or.inl hp)
        (λ hq ↦ Or.inr (Or.inl hq)))
      (λ hr ↦ Or.inr (Or.inr hr)))
    (λ h ↦ Or.elim h
      (λ hp ↦ Or.inl (Or.inl hp))
      (λ hqr ↦ Or.elim hqr
        (λ hq ↦ Or.inl (Or.inr hq))
        (λ hr ↦ Or.inr hr)))

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  Iff.intro
    (λ h ↦ Or.elim h
      (λ hp ↦ ⟨Or.inl hp, Or.inl hp⟩)
      (λ ⟨hq, hr⟩ ↦ ⟨Or.inr hq, Or.inr hr⟩))
    (λ ⟨hpq, hpr⟩ ↦ Or.elim hpq
      (λ hp ↦ Or.inl hp)
      (λ hq ↦ Or.elim hpr
        (λ hp ↦ Or.inl hp)
        (λ hr ↦ Or.inr ⟨hq, hr⟩)))


example : (p → (q → r)) ↔ (p ∧ q → r) :=
  Iff.intro
    (λ h ↦ (λ ⟨hp, hq⟩ ↦ h hp hq))
    (λ h ↦ (λ hp hq ↦ h ⟨hp, hq⟩))

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  Iff.intro
    (λ h ↦ ⟨λ hp ↦ h (Or.inl hp), λ hq ↦ h (Or.inr hq)⟩)
    (λ h ↦ (λ hpq ↦ Or.elim hpq
      (λ hp ↦ h.left hp)
      (λ hq ↦ h.right hq)))

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  Iff.intro
    (λ h ↦ ⟨λ hp ↦ h (Or.inl hp), λ hq ↦ h (Or.inr hq)⟩)
    (λ h ↦ (λ hpq ↦ Or.elim hpq
      (λ hp ↦ h.left hp)
      (λ hq ↦ h.right hq)))
/- Здесь частный случай с r = False -/

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  λ h ⟨hp, hq⟩  ↦ Or.elim h (λ hnp ↦ hnp hp) (λ hnq ↦ hnq hq)

example : ¬(p ∧ ¬p) :=
  λ ⟨hp, hnp⟩ ↦ hnp hp

example : p ∧ ¬q → ¬(p → q) :=
  λ ⟨hp, hnq⟩ h ↦ hnq (h hp)

example : ¬p → (p → q) :=
  λ hnp hp ↦ False.elim (hnp hp)

example : (¬p ∨ q) → (p → q) :=
  λ h ↦ Or.elim h
    (λ hnp hp ↦ False.elim (hnp hp))
    (λ hq _ ↦ hq)

example : p ∨ False ↔ p :=
  Iff.intro
    (λ h ↦ Or.elim h
      (λ hp ↦ hp)
      (λ hf ↦ False.elim hf))
    (λ hp ↦ Or.inl hp)

example : p ∧ False ↔ False :=
  Iff.intro
    (λ ⟨_, hf⟩ ↦ hf)
    (λ hf ↦ False.elim hf)

example : (p → q) → (¬q → ¬p) :=
  λ hpq hnq hp ↦ hnq (hpq hp)

  /- Classical.em is required: -/
example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
  λ him ↦ Or.elim (Classical.em q)
    (λ hq ↦ Or.inl (λ _ ↦ hq))
    (λ hnq ↦ Or.inr (λ hp ↦ Or.elim (him hp)
      (λ hq ↦ False.elim (hnq hq))
      (λ hr ↦ hr)))

example : ¬(p ∧ q) → ¬p ∨ ¬q :=
  λ h ↦ Or.elim (Classical.em p)
    (λ hp ↦ Or.elim (Classical.em q)
      (λ hq ↦ False.elim (h ⟨hp, hq⟩))
      (λ hnq ↦ Or.inr hnq))
    (λ hnp ↦ Or.inl hnp)

example : ¬(p → q) → p ∧ ¬q :=
  λ h ↦ Or.elim (Classical.em p)
    (λ hp ↦ Or.elim (Classical.em q)
      (λ hq ↦ False.elim (h (λ _ ↦ hq)))
      (λ hnq ↦ ⟨hp, hnq⟩))
    (λ hnp ↦ False.elim (h (λ hp ↦ False.elim (hnp hp))))

example : (p → q) → (¬p ∨ q) :=
  λ h ↦ Or.elim (Classical.em p)
    (λ hp ↦ Or.inr (h hp))
    (λ hnp ↦ Or.inl hnp)

example : (¬q → ¬p) → (p → q) :=
  λ h ↦ Or.elim (Classical.em q)
    (λ hq _ ↦ hq)
    (λ hnq hp ↦ False.elim (h hnq hp))

example : p ∨ ¬p := Classical.em _

example : (((p → q) → p) → p) :=
  λ h ↦ Or.elim (Classical.em p)
    (λ hp ↦ hp)
    (λ hnp ↦ False.elim (hnp (h (λ hp ↦ False.elim (hnp hp)))))

end hw
