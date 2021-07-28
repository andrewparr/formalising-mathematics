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
  sorry
end

lemma union_subset_union_left (hXY : X ⊆ Y) : X ∪ Z ⊆ Y ∪ Z :=
begin
  sorry
end

-- etc etc

-- intersection lemmas

lemma inter_subset_left : X ∩ Y ⊆ X :=
begin
  sorry
end

-- don't forget `ext` to make progress with equalities of sets

lemma inter_self : X ∩ X = X :=
begin
  sorry
end

lemma inter_comm : X ∩ Y = Y ∩ X :=
begin
  sorry
end

lemma inter_assoc : X ∩ (Y ∩ Z) = (X ∩ Y) ∩ Z :=
begin
  sorry
end

/-!

### Forall and exists

-/

lemma not_exists_iff_forall_not : ¬ (∃ a, a ∈ X) ↔ ∀ b, ¬ (b ∈ X) :=
begin
  sorry,
end

example : ¬ (∀ a, a ∈ X) ↔ ∃ b, ¬ (b ∈ X) :=
begin
  sorry,
end

end xena

