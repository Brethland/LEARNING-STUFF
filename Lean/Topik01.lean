example (A B : Prop) : A ∧ ¬ B → ¬ B ∧ A :=
assume h, and.intro (and.right h) (and.left h)

lemma em (A : Prop) : A ∨ ¬ A :=
show A ∨ ¬ A, from sorry

example : true := trivial

example (A B : Prop) (a : A) (b : B) : A ∧ B :=
  show A ∧ B, from and.intro a b

section exercises

variables A B C D : Prop

example : A ∧ (A → B) → B :=
  assume ⟨h₁ , h₂⟩, h₂ h₁

example : A → ¬ (¬ A ∧ B) :=
  assume : A, assume ⟨ h₁ , h₂ ⟩,
  show false, from h₁ this

example : ¬ (A ∧ B) → (A → ¬ B) :=
  assume h, assume a, assume b,
  h ⟨ a , b ⟩

example (h₁ : A ∨ B) (h₂ : A → C) (h₃ : B → D) : C ∨ D :=
  or.elim h₁
    (assume a, or.inl (h₂ a))
    (assume b, or.inr (h₃ b))

example (h : ¬ A ∧ ¬ B) : ¬ (A ∨ B) :=
  assume : A ∨ B,
  or.elim this
  (assume a, have ¬ A, from h.left,
   show false, from this a)
  (assume b, have ¬ B, from h.right,
   show false, from this b)  

example : ¬ (A ↔ ¬ A) :=
  assume m : A ↔ ¬ A,
  or.elim (em A)
    (assume c,  (m.mp c) c)
    (assume c, c (m.mpr c))

end exercises
