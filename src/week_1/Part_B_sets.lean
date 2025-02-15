import tactic

-- Let `Ω` be a "big underlying set" and let `X` and `Y` and `Z` be subsets

variables (Ω : Type) (X Y Z : set Ω) (a b c x y z : Ω)

namespace xena

/-!

# subsets

Let's think about `X ⊆ Y`. Typeset `⊆` with `\sub` or `\ss`
-/

-- `X ⊆ Y` is the same as `∀ a, a ∈ X → a ∈ Y` , by definition.

lemma subset_def : X ⊆ Y ↔ ∀ a, a ∈ X → a ∈ Y :=
begin
  -- true by definition
  refl
end

lemma subset_refl : X ⊆ X :=
begin
  -- This is also true by refl
  refl,
end

-- but the solution is
lemma subset_refl' : X ⊆ X :=
begin
  -- we have Ω : Type and X : set Ω  and goal is X ⊆  X
  rw subset_def, -- how we have ∀ (a : Ω), a ∈ X → a ∈ X
  -- goal now "for all a, ..." and `intro` makes progress with this.
  intros a ha, -- gives ha : a in X with goal a ∈ X
  exact ha, -- so ha is the goal, by assumption would have also worked.
end
-- I'm not sure the above proof adds more clarity than just the refl proof.

lemma subset_trans (hXY : X ⊆ Y) (hYZ : Y ⊆ Z) : X ⊆ Z :=
begin
  -- If you start with `rw subset_def at *` then you
  -- will have things like `hYZ : ∀ (a : Ω), a ∈ Y → a ∈ Z`
  -- You need to think of `hYZ` as a function, which has two
  -- inputs: first a term `a` of type `Ω`, and second a proof `haY` that `a ∈ Y`.
  -- It then produces one output `haZ`, a proof that `a ∈ Z`.
  -- You can also think of it as an implication:
  -- "if a is in Ω, and if a ∈ Y, then a ∈ Z". Because it's an implication,
  -- you can `apply hYZ`. This is a really useful skill!
  -- have hXY : X ⊆ Y and  hYZ : Y ⊆ Z and goal is X ⊆ Z
  rw subset_def at *, -- the astrix here means apply to all
  -- After this we have
  --   hXY: ∀ (a : Ω), a ∈ X → a ∈ Y
  --   hYZ: ∀ (a : Ω), a ∈ Y → a ∈ Z
  -- and goal of ∀ (a : Ω), a ∈ X → a ∈ Z
  -- So all the _ ⊆ _ have been changed to the definition of ⊆.
  -- NOTE: the above rw just makes it clearer what is going on.
  --       because this is the 'definition' of subset it isn't strictly necessary
  --       commenting out the above rw subset_det at *, line and this proof still works
  --
  -- Since out goal is a ∀ we can intro a to make a an arbitary value
  intro a, -- gives a : Ω with goal a ∈ X → a ∈ Z
  intro haX, -- gives haX : a ∈ X
  -- In this proof we're going to go backwards.
  -- our goal is to prove a ∈ Z and we have
  -- hYZ: a ∈ Y → a ∈ Z
  apply hYZ, -- and so by applying hYZ we only have to prove a ∈ Y. This is our new goal
  apply hXY, -- doing the same, makes the goal x ∈ X, which is haX above, 
  exact haX,
end

/-!

# Equality of sets

Two sets are equal if and only if they have the same elements.
The name of this theorem is `set.ext_iff`.
-/

example : X = Y ↔ (∀ a, a ∈ X ↔ a ∈ Y) :=
begin
  exact set.ext_iff
end

-- My additional notes
-- the proof of set.ext_iff is found by right clicking it and going to definition
-- it's a term mode proof, but here it is rewritten as a tactic mode proof 
-- for pedagogical reasons.
theorem ext_iff' {s t : set Ω} : s = t ↔ ∀ x, x ∈ s ↔ x ∈ t :=
begin
  -- it's a iff so we split
  split, {
    intro h, -- h : s = t, goal is ∀ x : Ω
    intro x, -- makes x : Omega and arbitary element
    rw h, -- proves the goal
  }, {
    intro h, -- h : ∀ (x : Ω), x ∈ s ↔ x ∈ t 
    -- with goal s = t,
    -- looking at the term proof of this it uses ext
    -- looking up ext.lean and it seems quite a powerful tatic
    -- and I'm not sure what it means yet, probably why a proof of this theory was
    -- missed out of this lesson.  Here it converts the goal of s = t
    -- Ah, I see it is now explained below.
    ext, -- to given x : Ω with goal x ∈ s ↔ x ∈ t.
    rw h, -- this now closes the goal.
  }
  -- Note the above in term mode was written simply as ⟨λ h x, by rw h, ext⟩
end

-- In practice, you often have a goal `⊢ X = Y` and you want to reduce
-- it to `a ∈ X ↔ a ∈ Y` for an arbitary `a : Ω`. This can be done with
-- the `ext` tactic. 


lemma subset.antisymm (hXY : X ⊆ Y) (hYX : Y ⊆ X) : X = Y :=
begin
  -- start with `ext a`,
  ext a, -- does same as my comments above.
  -- the a here gives the name of the 'element' so here we have a : Ω
  -- and the goal is now a ∈ X ↔ a ∈ Y
  split, -- since goal is an ↔ we split it
  {
    -- the goal here is a ∈ X → a ∈ Y which is proved by hXY since
    -- hXY is a proof that X ⊆ Y.
    apply hXY
  },
  { -- goal here is a ∈ Y → x ∈ X which is proved since hYX is a proof the Y ⊆ X
    apply hYX
  }
end

/-!

### Unions and intersections

Type `\cup` or `\un` for `∪`, and `\cap` or `\i` for `∩`

-/

lemma union_def : a ∈ X ∪ Y ↔ a ∈ X ∨ a ∈ Y :=
begin
  -- true by definition
  refl,
end

lemma inter_def : a ∈ X ∩ Y ↔ a ∈ X ∧ a ∈ Y :=
begin
  -- true by definition
  refl,
end


-- You can rewrite with those lemmas above if you're not comfortable with
-- assuming they're true by definition.

-- union lemmas

lemma union_self : X ∪ X = X :=
begin
  -- ext means by applying functional extensionality and set extensionality.
  -- here we just have the X : set Ω and so X is a set of values of type Ω
  -- and we need to introduce an element of X to prove results about it.
  -- ext a here, says let a : Ω, 
  ext a, -- with goal now a ∈ X ∪ X ↔ a ∈ X
  split, -- we can now split the ↔.
  {intro h, rw union_def at h, cases h; assumption,},
  {intro h, rw union_def, left, assumption}
end

lemma subset_union_left : X ⊆ X ∪ Y :=
begin
  -- ext doesn't work here for some reason
  intros x h,  -- makes x : Ω and h : x ∈ X.
  rw union_def, 
  -- This seems to me to be a good example of why a rw union_def helps even though
  -- it isn't needed.  Before the rw union_def we had h: x ∈ X and needed to prove
  -- x ∈ X ∪ Y.  It wasn't immediately obvious to me that left was the required next
  -- step. but after rw union_def we have the goal of
  -- x ∈ X ∨ x ∈ Y.  And now it's obvious that left is one of our assumptions
  -- and so it can be closed easily with the following.
  left,
  assumption, 
  -- This proof is shorter than the official solution.
end

lemma subset_union_right : Y ⊆ X ∪ Y :=
begin
  -- based on what we learnt above, this is quite simply.
  intros a h,
  right,
  assumption,
end

lemma union_subset_iff : X ∪ Y ⊆ Z ↔ X ⊆ Z ∧ Y ⊆ Z :=
begin
  split,
  {
    intro h,
    split,
    { -- goal here is X ⊆ Z, which is saying by definition that if a ∈ X then x ∈ Z
      -- so intros a h here, gives a : Ω and haX a ∈ X, goal is a ∈ Z
      intros a haX,
      apply h, left, assumption},    
    { -- goal here is  Y ⊆ Z so we do the intros again
      intros a haY,
      apply h, right, assumption}
  },
  {
    -- goal here is X ⊆ Z ∧ Y ⊆ Z → X ∪ Y ⊆ Z
    rintro ⟨hXsubZ, hYsubZ⟩ a haXuY,
    -- the above gives: hAXuY : a ∈ X ∪ Y
    -- with hXsubZ: X ⊆ Z  and  hYsubZ: Y ⊆ Z
    -- goal is a ∈ Z
    -- to prove this we need to know the different cases of hAXuY : a ∈ X ∪ Y
    cases haXuY,
    -- REMINDER from solution, the above rintro followed by cases can be simplified as
    -- rintros ⟨hXZ, hYZ⟩ a (haX | haY),
    {apply hXsubZ, assumption},
    {apply hYsubZ, assumption}
  }
end

variable (W : set Ω)

lemma union_subset_union (hWX : W ⊆ X) (hYZ : Y ⊆ Z) : W ∪ Y ⊆ X ∪ Z :=
begin
  -- we don't need this as it's being rewritten to be the defintion
  -- but it makes the next step clearer seeing what the definition is.
  rw subset_def,
  -- goal is now a ∀, so intro to get an arbitrary element.
  -- and remember the cases hint.
  rintro a (haW | haY),
  {
    -- our goal is a ∈ X ∪ Z
    -- but we have a ∈ W and hWX : W ⊆ X
    -- so our proof says a ∈ X ∪ Z if we can prove a ∈ X
    -- by by hWX we can proove a ∈ X if we can prove a ∈ W
    -- and we can prove this as it's one of our hypothesis    
    apply subset_union_left _,
    apply hWX,
    assumption,
  },
  {
    -- goal here is a ∈ X ∪ Z and we have
    -- a ∈ Y and hYZ : Y ⊆ Z
    -- so arguing like above,
    apply subset_union_right _,
    apply hYZ,
    assumption,
  }
end

-- Note, the official solution has a much shorter way of saying the above.
-- Remember to use left or right for goals of the form a ∈ X ∪ Z
lemma union_subset_union' (hWX : W ⊆ X) (hYZ : Y ⊆ Z) : W ∪ Y ⊆ X ∪ Z :=
begin
  rintros a (haW | haY),
  { left,
    exact hWX haW },
  { right,
    exact hYZ haY }
end

lemma union_subset_union_left (hXY : X ⊆ Y) : X ∪ Z ⊆ Y ∪ Z :=
begin
  -- Following the style of the solution above
  rintro a (haX | haZ),
  {
    left, 
    exact hXY haX,
  },
  {
    right, exact haZ,
  }
end

-- etc etc

-- I guess the etc etc comment here is because there are numerous lemma that can be written that are
-- all proved in a similar way.  Probably the mathlib has many of them.

-- intersection lemmas

lemma inter_subset_left : X ∩ Y ⊆ X :=
begin
    -- using rintro to combine intros with cases
    rintro a ⟨haX , haY⟩,
    exact haX,
end

-- don't forget `ext` to make progress with equalities of sets

lemma inter_self : X ∩ X = X :=
begin
  ext a,
  split,
  {intro h, cases h with haX; assumption,},
  {intro h,split; assumption}
end

lemma inter_comm : X ∩ Y = Y ∩ X :=
begin
  ext a,
  -- there's a lot of symmetry in this proof, so making good use of the ;
  -- following the two splits which means the following tactics apply to both parts following the split.
  split;
  {rintro ⟨haX , haY⟩, split; assumption },  
end

-- Interestingly the solution doesn't need a second split.
lemma inter_comm' : X ∩ Y = Y ∩ X :=
begin
  ext a,
  split;
  { rintro ⟨h1, h2⟩,
    -- I'm not yet clear on what these ⟨ ⟩  do in this exact.
    -- Similar I guess to when used in rintros but I don't think it has been explained.
    -- rintro ⟨ ⟩ is an intro followed by a cases
    -- so maybe this is like a split followed by exact
    exact ⟨h2, h1⟩ }
end

lemma inter_assoc : X ∩ (Y ∩ Z) = (X ∩ Y) ∩ Z :=
begin
  ext a,
  split,
  -- this is cool, copired above style with intro and exact
  -- but used nested ⟨⟩ brackets to match the grouping in the goal.
  -- rintro?, -- See following comment, uncomment this to have link to rintro documentation
  {rintro ⟨h1, ⟨h2, h3⟩⟩, exact⟨⟨h1, h2⟩, h3⟩,},
  {rintro ⟨⟨h1, h2⟩, h3⟩, exact⟨h1, ⟨h2, h3⟩⟩,}
end
-- Note, the official solution is the same as this, but you don't need the nested ⟨ ⟩ 
-- when the implicit ordering matches.
-- it also suggests using rintro? to view the syntax


/-!

### Forall and exists

-/

lemma not_exists_iff_forall_not : ¬ (∃ a, a ∈ X) ↔ ∀ b, ¬ (b ∈ X) :=
begin
  split,
  {
    intros h1 a h2, 
    -- our goal here is false and we have h1 : ¬ ∃ a ∈ X and h2 : a ∈ X.
    -- which are contradictory. 
    -- the h1 : ¬ ∃ a ∈ X and h2 : a ∈ X.
    -- can be interpreted as h1 : a ∈ X → false , and so
    apply h1, -- converts goal of false to goal of ∃ a : a ∈ X, which is h2
    use a,
    exact h2
  },
  { 
    rintro h1 ⟨a,haX⟩,
    -- h1: ∀ (b : Ω), b ∉ X
    -- haX: a ∈ X, goal is false
    exact h1 a haX,
    -- or broken down, this would be
    -- apply h1 a,
    -- exact haX,
  }
end

example : ¬ (∀ a, a ∈ X) ↔ ∃ b, ¬ (b ∈ X) :=
begin
  split,
  {
    -- the goal here is to prove that if not all elements of type Ω are in X
    -- then there exists and element, b, of type Ω such that b ∉ X,
    intro h, -- h: ¬∀ (a : Ω), a ∈ X
    -- goal is ∃ (b : Ω), b ∉ X
    -- h says that not all elements of type Ω are in X,
    -- goal says there exists b : Ω, b ∉ X,
    -- these are complimentary, we just want to say using h let a be
    -- such an element of type Ω that is not in X and use this to prove the goal.
    -- But this seem tricky to argue in Lean.
    --
    -- The proof argument here goes something like this.
    -- goal says there exists an element of type Ω that is not in X
    -- aiming for a contractition, assume there does not exist and element of Ω that is not in X

    -- Therefore let a be any element of type Ω, by the contradiction we have a ∈ X.
    -- now by h, not all elements of type Ω are in x, 
    -- use this to ...

    -- by h we have not all elements of Ω are in X, so use this to 
    -- let a be such an element.
    by_contra h2,
    -- the above line gives us the contradiction as h2: ¬∃ (b : Ω), b ∉ X
    -- we now need to prove false
    apply h,
    intro a,
    by_contra h,
    apply h2,
    use a,
  },
  {
    -- goal is (∃ (b : Ω), b ∉ X) → (¬∀ (a : Ω), a ∈ X)
    intro h, -- h: ∃ (b : Ω), b ∉ X
    cases h with b h2,
    intro h,
    apply h2,
    apply h,
  }
end

end xena

