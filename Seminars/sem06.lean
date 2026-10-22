import Lean
/-!
# Seminar 6
Typeclasses
-/

/- Tactics for inductive types (debt from sem05) -/
section induction
  theorem Nat.add_assoc' (a b c : Nat) : a + b + c = a + (b + c) := by
    sorry

  #check Nat.mod.inductionOn
  example (a : Nat) {b : Nat} (h : 0 < b) : a % b < b := by
    induction a, b using Nat.mod.inductionOn with
    | ind a b h₁ ih =>
      rw [Nat.mod_eq_sub_mod h₁.2]
      exact ih h
    | base a b h₁ =>
      have hlt : a < b := Nat.lt_of_not_ge (fun hba => h₁ ⟨h, hba⟩)
      rw [Nat.mod_eq_of_lt hlt]
      exact hlt

  example (a b c : Nat) (h : a.succ.succ = b.succ.succ) : a + c = b + c := by
    injection h with h'
    injection h' with h''
    rw [h'']

  example (a b : Nat) (h : a.succ = 0) : b = b + 7 := by
    injection h

  example (a b : Nat) (h : a.succ = 0) : b = b + 7 := by
    contradiction
end induction

/- The same proof for different types -/
section
  open Nat (mul_add add_mul add_assoc)
  example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y := by
    rw [mul_add]
    repeat rw [add_mul]
    repeat rw [add_assoc]
end

section
  open Int (mul_add add_mul add_assoc)
  example (x y : Int) : (x + y) * (x + y) = x * x + y * x + x * y + y * y := by
    rw [mul_add]
    repeat rw [add_mul]
    repeat rw [add_assoc]
end

-- We can make this proof polymorphic.
theorem add_sq {α : Type} {add mul : α → α → α}
    (mul_add : ∀ x y z : α, mul x (add y z) = add (mul x y) (mul x z))
    (add_mul : ∀ x y z : α, mul (add x y) z = add (mul x z) (mul y z))
    (add_assoc : ∀ x y z : α, add (add x y) z = add x (add y z))
    {x y : α} :
    mul (add x y) (add x y) = add (add (add (mul x x) (mul y x)) (mul x y)) (mul y y) := by
  rw [mul_add]
  repeat rw [add_mul]
  repeat rw [add_assoc]

protected theorem Nat.add_sq (x y : Nat) :
    (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  add_sq Nat.mul_add Nat.add_mul Nat.add_assoc

protected theorem Int.add_sq (x y : Int) :
    (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  add_sq Int.mul_add Int.add_mul Int.add_assoc

/- Package operations and laws; let instance search supply the package. -/
class AddSq (α : Type) where
  add : α → α → α
  mul : α → α → α
  mul_add : ∀ x y z : α, mul x (add y z) = add (mul x y) (mul x z)
  add_mul : ∀ x y z : α, mul (add x y) z = add (mul x z) (mul y z)
  add_assoc : ∀ x y z : α, add (add x y) z = add x (add y z)

#print AddSq
#check @AddSq.add

namespace AddSq
  theorem add_sq {α : Type} [AddSq α] {x y : α} :
      mul (add x y) (add x y) = add (add (add (mul x x) (mul y x)) (mul x y)) (mul y y) := by
    rw [mul_add]
    repeat rw [add_mul]
    repeat rw [add_assoc]
end AddSq

instance : AddSq Nat where
  add := Nat.add
  mul := Nat.mul
  mul_add := Nat.mul_add
  add_mul := Nat.add_mul
  add_assoc := Nat.add_assoc

#synth AddSq Nat
#check (inferInstance : AddSq Nat)
#check @AddSq.add_sq

def doubleImplicit {α : Type} {s : AddSq α} (x : α) : α :=
  @AddSq.add α s x x

def doubleClass {α : Type} [AddSq α] (x : α) : α :=
  AddSq.add x x

#eval doubleClass (3 : Nat)
-- #eval doubleImplicit (3 : Nat)
#eval doubleImplicit (s := inferInstance) (3 : Nat)

theorem Nat.add_sq' (x y : Nat) :
    (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  AddSq.add_sq

/- Notation -/
namespace Toy
  class Add (α : Type) where
    add : α → α → α

  local infixl:65 " Ш " => Add.add

  local instance : Add Nat where
    add := Nat.add

  #check 2 Ш 3
  #eval 2 Ш 3

  local instance : Add Int where
    add := Int.mul

  #eval (2 : Int) Ш 3

  section
    local instance : Add Nat where
      add := Nat.max
    #eval (2 : Nat) Ш 3
  end

  #eval (2 : Nat) Ш 3
end Toy

#print Add
#check @HAdd.hAdd
#synth HAdd Nat Nat Nat

#print OfNat
#synth OfNat Int 2

/- Hierarchies -/
namespace Algebra
  class AddSemigroup (α : Type) extends Add α where
    add_assoc : ∀ x y z : α, x + y + z = x + (y + z)

  class Distributive (α : Type) extends AddSemigroup α, Mul α where
    mul_add : ∀ x y z : α, x * (y + z) = x * y + x * z
    add_mul : ∀ x y z : α, (x + y) * z = x * z + y * z

  #check AddSemigroup.toAdd
  #check Distributive.toAddSemigroup

  section
    variable {α : Type} [Distributive α]
    #synth AddSemigroup α
    #synth Add α
    #synth Mul α
  end

  instance : Distributive Nat where
    add := Nat.add
    mul := Nat.mul
    add_assoc := Nat.add_assoc
    mul_add := Nat.mul_add
    add_mul := Nat.add_mul

  #synth AddSemigroup Nat

  -- Return to our original example, now with ordinary notation.
  theorem add_sq {α : Type} [Distributive α] (x y : α) :
      (x + y) * (x + y) = x * x + y * x + x * y + y * y := by
    rw [Distributive.mul_add]
    repeat rw [Distributive.add_mul]
    repeat rw [AddSemigroup.add_assoc]

  example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
    add_sq x y

  /- Instances with instance parameters -/

  instance {α β : Type} [AddSemigroup α] [AddSemigroup β] :
      AddSemigroup (α × β) where
    add p q := (p.1 + q.1, p.2 + q.2)
    add_assoc p q r := by
      apply Prod.ext
      · exact AddSemigroup.add_assoc p.1 q.1 r.1
      · exact AddSemigroup.add_assoc p.2 q.2 r.2

  #synth AddSemigroup (Nat × Nat × Nat)
  #eval (1, 2, 3) + (4, 5, 6)
end Algebra

/- Three degrees of bundling, using the same algebraic structure. -/
namespace Packaging

namespace Bundled
  structure AddSemigroup where
    Carrier : Type u
    add : Carrier → Carrier → Carrier
    add_assoc : ∀ a b c, add (add a b) c = add a (add b c)

  def naturals : AddSemigroup where
    Carrier := Nat
    add := Nat.add
    add_assoc := Nat.add_assoc

  example (S : AddSemigroup) (a b c : S.Carrier) :
      S.add (S.add a b) c = S.add a (S.add b c) :=
    S.add_assoc a b c
end Bundled

namespace SemiBundled
  class AddSemigroup (α : Type u) extends Add α where
    add_assoc : ∀ a b c : α, a + b + c = a + (b + c)

  instance : AddSemigroup Nat where
    add := Nat.add
    add_assoc := Nat.add_assoc

  example {α : Type u} [AddSemigroup α] (a b c : α) :
      a + b + c = a + (b + c) := AddSemigroup.add_assoc a b c
end SemiBundled

namespace Unbundled
  class IsAddSemigroup (α : Type u) [Add α] : Prop where
    add_assoc : ∀ a b c : α, a + b + c = a + (b + c)

  instance : IsAddSemigroup Nat where
    add_assoc := Nat.add_assoc

  example {α : Type u} [Add α] [IsAddSemigroup α] (a b c : α) :
      a + b + c = a + (b + c) := IsAddSemigroup.add_assoc a b c
end Unbundled

#check Bundled.AddSemigroup
#check SemiBundled.AddSemigroup
#check Unbundled.IsAddSemigroup

#check_failure Bundled.AddSemigroup.toAdd
#check SemiBundled.AddSemigroup.toAdd
#check_failure Unbundled.IsAddSemigroup.toAdd

#check_failure (fun {α : Type} [Unbundled.IsAddSemigroup α] (a : α) => a + a)
end Packaging

namespace LargeTerms

set_option synthInstance.maxSize 1000000

class Op (α : Type) where op : α → α → α

namespace SemiBundled

class L1 (α : Type) extends Op α where p1 : True
class L2 (α : Type) extends L1 α where p2 : True
class L3 (α : Type) extends L2 α where p3 : True

instance : L3 Nat where
  op := Nat.add
  p1 := True.intro
  p2 := True.intro
  p3 := True.intro

instance {α β : Type} [L3 α] [L3 β] : L3 (α × β) where
  op x y := (Op.op x.1 y.1, Op.op x.2 y.2)
  p1 := True.intro
  p2 := True.intro
  p3 := True.intro

end SemiBundled

namespace Unbundled

class L1 (α : Type) [Op α] where p1 : True
class L2 (α : Type) [Op α] [L1 α] where p2 : True
class L3 (α : Type) [Op α] [L1 α] [L2 α] where p3 : True

instance : Op Nat := ⟨Nat.add⟩
instance : L1 Nat := ⟨True.intro⟩
instance : L2 Nat := ⟨True.intro⟩
instance : L3 Nat := ⟨True.intro⟩

instance {α β : Type} [Op α] [Op β] : Op (α × β) where
  op x y := (Op.op x.1 y.1, Op.op x.2 y.2)

instance {α β : Type}
    [Op α] [Op β] [L1 α] [L1 β] : L1 (α × β) where
  p1 := True.intro

instance {α β : Type}
    [Op α] [Op β] [L1 α] [L1 β]
    [L2 α] [L2 β] : L2 (α × β) where
  p2 := True.intro

instance {α β : Type}
    [Op α] [Op β] [L1 α] [L1 β]
    [L2 α] [L2 β] [L3 α] [L3 β] : L3 (α × β) where
  p3 := True.intro

end Unbundled

section
open Lean Elab Command Meta

elab "#exprTree " t:term : command => do
  let e ← liftTermElabM do
    let e ← Term.elabTerm t none
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e
  logInfo m!"{repr e}"

elab "#exprTreeSize " t:term : command => do
  let e ← liftTermElabM do
    let e ← Term.elabTerm t none
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e
  logInfo m!"{e.sizeWithoutSharing}"

#exprTree (inferInstance : SemiBundled.L3 (Nat × Nat))
#exprTree (inferInstance : Unbundled.L3 (Nat × Nat))

abbrev P0 := Nat × Nat
abbrev P1 := P0 × P0
abbrev P2 := P1 × P1
abbrev P3 := P2 × P2

#time #exprTreeSize (inferInstance : SemiBundled.L3 P1)
#time #exprTreeSize (inferInstance : SemiBundled.L3 P2)
#time #exprTreeSize (inferInstance : SemiBundled.L3 P3)

#time #exprTreeSize (inferInstance : Unbundled.L3 P1)
#time #exprTreeSize (inferInstance : Unbundled.L3 P2)
#time #exprTreeSize (inferInstance : Unbundled.L3 P3)
end
end LargeTerms


namespace SlowSearch

inductive Path where
  | root : Path
  | left : Path → Path
  | right : Path → Path

namespace SemiBundled

class Need (n : Nat) (p : Path) : Prop where
  ok : True

class Left (n : Nat) (p : Path) extends Need n p where
  extra : True

class Right (n : Nat) (p : Path) extends Need n p where
  extra : True

instance {n : Nat} {p : Path}
    [Need n (.left p)] : Left (n + 1) p where
  ok := True.intro
  extra := True.intro

instance {n : Nat} {p : Path}
    [Need n (.right p)] : Right (n + 1) p where
  ok := True.intro
  extra := True.intro

end SemiBundled

namespace Unbundled

class Need (n : Nat) (p : Path) : Prop where
  ok : True

class Left (n : Nat) (p : Path) [Need n p] : Prop where
  extra : True

class Right (n : Nat) (p : Path) [Need n p] : Prop where
  extra : True

instance {n : Nat} {p : Path}
    [Need (n + 1) p] [Need n (.left p)] :
    Left (n + 1) p where
  extra := True.intro

instance {n : Nat} {p : Path}
    [Need (n + 1) p] [Need n (.right p)] :
    Right (n + 1) p where
  extra := True.intro

end Unbundled

#time #check_failure (inferInstance : SemiBundled.Need 8 .root)
#time #check_failure (inferInstance : SemiBundled.Need 10 .root)
#time #check_failure (inferInstance : SemiBundled.Need 12 .root)

#time #check_failure (inferInstance : Unbundled.Need 8 .root)
#time #check_failure (inferInstance : Unbundled.Need 10 .root)
#time #check_failure (inferInstance : Unbundled.Need 12 .root)

end SlowSearch
