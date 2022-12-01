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


theorem exists_inv {h : permutation α} : (∃j, comp j h = eIden ∧ comp h j = eIden) := by 
  have ⟨b, l1⟩ := h
  have ⟨k, l2⟩ := l1
  let g : permutation α := by
    have sl1 : _ := And.intro l2.right l2.left
    have kinv : ∃g, g ∘ k = id ∧ k ∘ g = id := Exists.intro b sl1 
    exact ⟨k, kinv⟩ 
  apply Exists.intro g
  apply And.intro 
  simp [comp,eIden]
  exact l2.left

  simp[comp,eIden]
  exact l2.right

theorem associat {a b c : permutation α} : comp (comp a b) c = comp a (comp b c) := rfl

theorem perms_grp (α : Type) : (group (permutation α)) := sorry
   
    

  

  

  
