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

@[ext] structure group (G : Type) where 
  mul : G→G→G
  e : G 
  assoc : ∀ (a b c : G), mul (mul a b) c = mul a (mul b c)
  is_ident : ∀g : G, mul e g = g ∧ mul g e = g 
  Ex_inv : ∀g : G, ∃g_inv, mul (g_inv) g = e ∧ mul g (g_inv) = e

@[ext] structure permutation (α : Type) where 
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

theorem eIdent {a: permutation α} : comp eIden a = a ∧ comp a eIden = a := by
  apply And.intro
  have l1 : (comp eIden a).to_fun = a.to_fun := by
    have sl1 : (comp eIden a).to_fun = eIden.to_fun ∘ a.to_fun := rfl
    rw[sl1]
    have that : eIden.to_fun = @id α := by rfl
    rw[that]
    rfl

  have ⟨c', l5⟩ := (comp eIden a).IsInv
  rw[l1] at l5 
  ext n 
  have partext : permutation.to_fun (comp eIden a) = permutation.to_fun a := l1 
  rw[partext]
  rfl 

--NEED HELP TO UN-SORRY THIS (I need to figure out how to do this without h hypothesis)
theorem exists_inv {g g': permutation α} (h : g'.to_fun ∘ g.to_fun = id ): (∃j, comp j g = eIden ∧ comp g j = eIden) := by 
  apply Exists.intro g' 
  apply And.intro 
  ext m 
  have that1 : (comp g' g).to_fun = id := h
  rw[that1]
  rfl 

  ext m 
  have ⟨g0, l2⟩ := g.IsInv 
  have that2 : g.to_fun ∘ g'.to_fun = id := by
    have sl2 : g.to_fun ∘ g'.to_fun ∘ g.to_fun ∘ g0 = g.to_fun ∘ id ∘ g0 := by 
      rw[←h] 
      rfl
    rw[l2.right] at sl2
    have sll : g.to_fun ∘ id = g.to_fun := rfl 
    have sllb : g'.to_fun ∘ id = g'.to_fun := rfl
    have sl2a : g.to_fun ∘ (g'.to_fun ∘ id) = (g.to_fun ∘ id) ∘ g0 := sl2 
    rw[sll, sllb] at sl2a 
    rw[l2.right] at sl2a 
    exact sl2a 
  have ugh : permutation.to_fun (comp g g') = g.to_fun ∘ g'.to_fun := rfl 
  rw[ugh]
  rw[that2] 
  rfl 

theorem associat {a b c : permutation α} : comp (comp a b) c = comp a (comp b c) := rfl

theorem perms_grp (α : Type) : (group (permutation α)) := sorry
   
    

  

  

  
