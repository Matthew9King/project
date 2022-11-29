import Std.Tactic.Ext

@[ext] structure Foo (α β : Type) where
  a : α
  b : β



variable {α β : Type}
variable (z w : Foo α β)



theorem bar (h : z.a = w.a) (h' : z.b = w.b) : z = w := by
  ext
  exact h
  exact h'


theorem comp_assoc (f g h : α → α) : (f∘g)∘h=f∘(g∘h) := by 
  exact rfl

structure group (G : Type) where 
  mul : G→G→G
  e : G 
  assoc : ∀ (a b c : G), mul (mul a b) c = mul a (mul b c)
  is_ident : ∀g : G, mul e g = g ∧ mul g e = g 
  Ex_inv : ∀g : G, ∃g_inv, mul (g_inv) g = e ∧ mul g (g_inv) = e

structure permutation (α : Type) where 
  to_fun : α → α 
  IsInv : ∃ g, g ∘ to_fun = id ∧ to_fun ∘ g = id 

variable (c : permutation α)

def comp (a b : permutation α) : permutation α where 
  to_fun := a.to_fun ∘ b.to_fun 
  IsInv := by
    have ⟨a', l1⟩ := a.IsInv 
    have ⟨b', l2⟩ := b.IsInv 
    apply Exists.intro (b'∘a')
    apply And.intro
    --left
    have thatpart : (b'∘a')∘ a.to_fun ∘ b.to_fun = b' ∘ (a'∘ a.to_fun) ∘ b.to_fun := rfl
    rw[thatpart]
    have thatpart2 : a'∘a.to_fun = id := l1.left
    rw[thatpart2]
    have l3 : b'∘id = b' := rfl
    have h : b'∘ id ∘ b.to_fun = (b'∘ id)∘ b.to_fun := rfl 
    rw[h, l3]
    exact l2.left
    --right
    have thatpart : (a.to_fun∘b.to_fun)∘b'∘ a' = a.to_fun∘(b.to_fun∘b')∘ a' := rfl
    rw[thatpart]
    rw[l2.right]
    have thatpart2 : a.to_fun∘id = a.to_fun := rfl
    have h : a.to_fun∘id∘a' = (a.to_fun∘id)∘a' := rfl 
    rw[h, thatpart2]
    exact l1.right

def eIden : (permutation α) where
  to_fun := id
  IsInv := by
    apply Exists.intro id 
    apply And.intro 
    exact rfl 
    exact rfl


-- STILL NEED HELP WITH GETTING THE MONOID THING MADE
theorem eIdent {a: permutation α} : comp eIden a = a ∧ comp a eIden = a := by
  apply And.intro
  have l1 : (comp eIden a).to_fun = a.to_fun := by
    have sl1 : (comp eIden a).to_fun = eIden.to_fun ∘ a.to_fun := rfl
    rw[sl1]
    have that : eIden.to_fun = @id α := by rfl
    rw[that]
    rfl

  have ⟨a', l4⟩ := a.IsInv
  have ⟨c', l5⟩ := (comp eIden a).IsInv
  rw[l1] at l5 
  have that : c' = a' := by 
    have sla : c' ∘(a.to_fun∘id) = id := l5.left
    rw[←l4.left] at sla
    have sla2 : c'∘ (a.to_fun ∘ a') ∘ a.to_fun = (a'∘a.to_fun) := sla
    rw[l4.left] at sla2 
    rw[l4.right] at sla2
    have h : id∘ a.to_fun = a.to_fun := rfl
    rw[h] at sla2
    have slb : (c'∘ a.to_fun) ∘ a' = id ∘ a' := by 
      rw[sla2]
    have slb2 : c' ∘ (a.to_fun ∘ a') = id ∘ a' := slb
    rw[l4.right] at slb2
    exact slb2
  have l1b : (comp eIden a).IsInv = a.IsInv := rfl
  

  have l2 : (comp a eIden).to_fun = a.to_fun := by
    have sl1 : (comp a eIden).to_fun = a.to_fun ∘ eIden.to_fun := rfl 
    rw[sl1]
    have that : eIden.to_fun = @id α := by rfl 
    rw[that]
    rfl
  have ⟨a', l4⟩ := a.IsInv
  have ⟨c', l5⟩ := (comp a eIden).IsInv
  rw[l2] at l5
  have sl1 : a' = c' := by
    have sl1a : c' ∘ (a.to_fun ∘ a') = id ∘ a' := by
      rw[←l5.left]
      rfl 
    rw[l4.right] at sl1a 
    have ob : c'∘ id = c' := rfl 
    have ob2 : id ∘ a' = a' := rfl 
    rw[←ob, ←ob2]
    exact Eq.symm sl1a
  have invpart : (comp a eIden).IsInv = a.IsInv := rfl



--NEED HELP TO UN-SORRY THIS
theorem exists_inv {g : permutation α} : ∃j, comp j g = eIden ∧ comp g j = eIden := by
  have ⟨g', l1⟩ := g.IsInv 

  
theorem associat {a b c : permutation α} : comp (comp a b) c = comp a (comp b c) := rfl

theorem perms_grp (α : Type) : (group (permutation α)) := by 
  sorry
  

  

  
