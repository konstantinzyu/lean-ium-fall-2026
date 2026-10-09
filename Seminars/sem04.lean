/-!
# Seminar 4
Inductive types
-/

/- Simple enumerations -/
inductive Bool' : Type where
  | false : Bool'
  | true: Bool'

#check Bool'.false
#check Bool'.true
#check Bool'.casesOn
#print Bool'.casesOn
#check Bool'.rec
#print Bool'.rec

def Bool'.not (b : Bool') : Bool' :=
  Bool'.casesOn Bool'.true Bool'.false b

#eval Bool'.true.not
#eval Bool'.false.not


/- Can't use recursos directly:
def Bool'.not' (b : Bool') : Bool' :=
  Bool'.rec Bool'.true Bool'.false b
-/

def Bool'.not' (b : Bool') : Bool' :=
  match b with
  | false => true
  | true  => false

#eval Bool'.true.not'
#eval Bool'.false.not'
#print Bool'.not'

set_option pp.all true
#print Bool'.not'
#check Bool'.not'.match_1
#print Bool'.not'.match_1
set_option pp.all false

def Bool'.and (a b : Bool') : Bool' :=
  match a, b with
  | false, false => false
  | false, true  => false
  | true , false => false
  | true , true  => true

def Bool'.and' (a b : Bool') : Bool' :=
  match a, b with
  | false, false
  | false, true
  | true , false => false
  | true , true  => true

def Bool'.and'' (a b : Bool') : Bool' :=
  match a, b with
  | true , true  => true
  | _    , _     => false

def Bool'.and''' : Bool' → Bool' → Bool'
  | true, true => true
  | _, _       => false

#print Bool

inductive Unit' : Type where
  | unit

#check Unit'.casesOn
#check Unit'.rec

#print Unit
#print PUnit
#check ()

inductive Empty' where

#check Empty'.casesOn
#check Empty'.rec
#print Empty

#print True
#print False

/- Parameters -/
inductive PointNatNat where
  | mk : Nat → Nat → PointNatNat

#check PointNatNat.casesOn
#check PointNatNat.rec

def PointNatNat.fst (x : PointNatNat) : Nat :=
  match x with
  | mk a _ => a

def PointNatNat.snd (x : PointNatNat) : Nat :=
  let ⟨_, b⟩ := x; b

structure PointNatNat' : Type where
  mk ::
  fst : Nat
  snd : Nat

inductive Prod' (α β : Type) : Type where
  | mk : α → β → Prod' α β

#check Prod'.mk
#check Prod'.casesOn
#check Prod'.rec

#print Prod
#print And

inductive Sum' (α β : Type) where
  | inl (a : α)
  | inr (a : β) : Sum' α β

#check Sum'.casesOn
#check Sum'.rec

#print Sum
#print Or

#print Exists
#print Subtype

/- Recursion -/

inductive Nat' where
  | zero : Nat'
  | succ : Nat' → Nat'

#check Nat'.casesOn
#check Nat'.rec

def Nat'.add (m n : Nat') : Nat' :=
  match n with
  | zero => m
  | Nat'.succ n => (Nat'.add m n).succ

#eval Nat'.add Nat'.zero.succ.succ Nat'.zero.succ.succ

#print Nat
#print Nat.add

partial def f (m : Nat) : Nat := f m
unsafe def absurd' (a : Nat) : False := absurd' a

inductive List' (α : Type) : Type where
  | nil : List' α
  | cons : α → List' α → List' α

#print List'.casesOn
#print List'.rec

def concat {α : Type} (x y : List' α) : List' α :=
  match x with
  | List'.nil => y
  | List'.cons a x => List'.cons a (concat x y)

inductive empty : Type where
  | mk : empty → empty

inductive good : Type where
  | x : good
  | y : (Nat → good) → good

/-
inductive bad : Type where
  | x : bad
  | y : (bad → Nat) → bad -/

/- W-Types -/

inductive W (A : Type) (B : A → Type) : Type where
  | sup (a : A) (f : B a → W A B)

abbrev WNat : Type :=
  let B (b : Bool) :=
    match b with
    | false => Empty
    | true  => Unit
  W Bool B

def WNat.zero : WNat := W.sup false Empty.elim
def WNat.succ (n : WNat) : WNat := W.sup true (λ _ ↦ n)

abbrev WList (α : Type) : Type :=
  let B (b : Unit ⊕ α) :=
    match b with
    | Sum.inl _ => Empty
    | Sum.inr _  => Unit
  W (Unit ⊕ α) B

def WList.nil {α : Type} : WList α :=
  W.sup (Sum.inl ()) Empty.elim
def WList.cons {α : Type} (x : α) (xs : WList α) : WList α :=
  W.sup (Sum.inr x) (λ _ ↦ xs)

/- Inductive families -/
inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons : α → {n : Nat} → Vec α n → Vec α (n + 1)

#check Vec.casesOn
#check Vec.rec

inductive Eq' {α : Type} (a : α) : α → Prop where
  | refl : Eq' a a

#check Eq'.casesOn
#check Eq'.rec

#check Eq.trans
theorem Eq'.symm {α : Type} {a b : α} (h : Eq' a b) : Eq' b a :=
  Eq'.rec Eq'.refl h

theorem Eq'.trans {α : Type} {a b c : α} (h₁ : Eq' a b) (h₂ : Eq' b c) : Eq' a c :=
  Eq'.rec h₁ h₂

#print Eq
#check rfl
#check (0 = 0)
#check (0 = 1)

#check Eq.symm

example : 2 + 2 = 4 := rfl
example (n : Nat) : n + 0 = n := rfl
-- example (n : Nat) : 0 + n = n := rfl

theorem foo (n : Nat) : 0 + n = n :=
  match n with
  | 0 => rfl
  | n+1 => congrArg Nat.succ (foo n)

/- Mutual induction -/
mutual
  inductive Even : Nat → Prop where
  | zero : Even 0
  | succ : (n : Nat) → Odd n → Even (n + 1)

  inductive Odd : Nat → Prop where
  | succ : (n : Nat) → Even n → Odd (n + 1)
end

example {n : Nat} (h : Even n) : Even (n + 2) :=
  Even.succ (n + 1) (Odd.succ n h)

/-!
# Exercises
-/
section hw
  abbrev Var := Nat

  /- Define the type of propositional formulas:
    if φ and ψ are formulas, so are φ → ψ -/
  inductive Form : Type where

  /- Define a boolean evaluation of a formula -/
  def eval (v : Var → Bool) (φ : Form) : Bool := sorry


  /- Define an interpretation of a formula as Prop -/
  def interp (v : Var → Prop) (φ : Form) : Prop := sorry

  /- If every interpretation of a formula is provable,
    than formula is tautological -/
  theorem correct (φ : Form) :
    (∀ (v : Var → Prop), interp v φ) →
    (∀ (v : Var → Bool), eval v φ = true) := by
    sorry

  /- Prove the other direction in classical logic -/
  theorem complete
    (φ : Form)
    (decide : Prop → Bool)
    (h : ∀ p : Prop, p ↔ decide p = true) :
      (∀ (v : Var → Bool), eval v φ = true) →
      (∀ (v : Var → Prop), interp v φ) := by
    sorry
end hw
