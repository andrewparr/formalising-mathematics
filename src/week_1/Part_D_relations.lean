import tactic

/-!

# Equivalence relations are the same as partitions

In this file we prove that there's a bijection between
the equivalence relations on a type, and the partitions of a type. 

Three sections:

1) partitions
2) equivalence classes
3) the proof

## Overview

Say `α` is a type, and `R : α → α → Prop` is a binary relation on `α`. 
The following things are already in Lean:

`reflexive R := ∀ (x : α), R x x`
`symmetric R := ∀ ⦃x y : α⦄, R x y → R y x`
`transitive R := ∀ ⦃x y z : α⦄, R x y → R y z → R x z`

`equivalence R := reflexive R ∧ symmetric R ∧ transitive R`

In the file below, we will define partitions of `α` and "build some
interface" (i.e. prove some propositions). We will define
equivalence classes and do the same thing.
Finally, we will prove that there's a bijection between
equivalence relations on `α` and partitions of `α`.

-/

/-

# 1) Partitions

We define a partition, and prove some lemmas about partitions. Some
I prove myself (not always using tactics) and some I leave for you.

## Definition of a partition

Let `α` be a type. A *partition* on `α` is defined to be
the following data:

1) A set C of subsets of α, called "blocks".
2) A hypothesis (i.e. a proof!) that all the blocks are non-empty.
3) A hypothesis that every term of type α is in one of the blocks.
4) A hypothesis that two blocks with non-empty intersection are equal.
-/

/-- The structure of a partition on a Type α. -/ 
@[ext] structure partition (α : Type) :=
(C : set (set α))
(Hnonempty : ∀ X ∈ C, (X : set α).nonempty)
(Hcover : ∀ a, ∃ X ∈ C, a ∈ X)
(Hdisjoint : ∀ X Y ∈ C, (X ∩ Y : set α).nonempty → X = Y)

/-

## Basic interface for partitions

Here's the way notation works. If `α` is a type (i.e. a set)
then a term `P` of type `partition α` is a partition of `α`,
that is, a set of disjoint nonempty subsets of `α` whose union is `α`.

The collection of sets underlying `P` is `P.C`, the proof that
they're all nonempty is `P.Hnonempty` and so on.

-/

namespace partition

-- let α be a type, and fix a partition P on α. Let X and Y be subsets of α.
variables {α : Type} {P : partition α} {X Y : set α}

/-- If X and Y are blocks, and a is in X and Y, then X = Y. -/
theorem eq_of_mem (hX : X ∈ P.C) (hY : Y ∈ P.C) {a : α} (haX : a ∈ X)
  (haY : a ∈ Y) : X = Y :=
-- Proof: follows immediately from the disjointness hypothesis.
P.Hdisjoint _ _ hX hY ⟨a, haX, haY⟩

-- Before we start, lets break down the above term mode proof.
theorem eq_of_mem' (hX : X ∈ P.C) (hY : Y ∈ P.C) {a : α} (haX : a ∈ X)
  (haY : a ∈ Y) : X = Y :=
begin
  exact P.Hdisjoint _ _ hX hY ⟨a, haX, haY⟩,
end


/-- If a is in two blocks X and Y, and if b is in X,
  then b is in Y (as X=Y) -/
theorem mem_of_mem (hX : X ∈ P.C) (hY : Y ∈ P.C) {a b : α}
  (haX : a ∈ X) (haY : a ∈ Y) (hbX : b ∈ X) : b ∈ Y :=
begin
  -- you might want to start with `have hXY : X = Y`
  -- and prove it from the previous lemma
  have hXY : X = Y,
  -- following the hint, after this line the goal is to prove that X=Y.
  -- Following that, the goal goes back to the goal of b ∈ Y but to help
  -- you then have the hXY : X = Y.
  {
    -- proving have, that is proving X = Y
    -- this can be proved with just duplicating the proof used above. i.e.
    --    exact P.Hdisjoint _ _ hX hY ⟨a, haX, haY⟩,
    -- but probably what is meant is to use the proof like below.
    exact eq_of_mem hX hY haX haY,
  },
  -- back to proving b ∈ Y.
  rw ←hXY, -- hXY is X = Y, so we need to rw this backwards, with ← to change the Y to an X
  -- now goal is b ∈ X, which is hbX
  exact hbX,
end

/-- Every term of type `α` is in one of the blocks for a partition `P`. -/
theorem mem_block (a : α) : ∃ X : set α, X ∈ P.C ∧ a ∈ X :=
begin
  -- an interesting way to start is
  -- `obtain ⟨X, hX, haX⟩ := P.Hcover a,`
  obtain ⟨X, hX, haX⟩ := P.Hcover a,
  -- this line spits out the individual proved theorems from P.Hcover
  -- it's now easy to just use X (for the there exists) split the ∧ and show the other parts
  -- are already proven.
  use X,
  split,
  exact hX,
  exact haX,
end

theorem mem_block' (a : α) : ∃ X : set α, X ∈ P.C ∧ a ∈ X :=
begin
  -- an interesting way to start is
  -- `obtain ⟨X, hX, haX⟩ := P.Hcover a,`
  obtain ⟨X, hX, haX⟩ := P.Hcover a,
  -- this line spits out the individual proved theorems from P.Hcover
  -- it's now easy to just use X (for the there exists) split the ∧ and show the other parts
  -- are already proven.
  use X,
  -- note instead of a split followed by two exacts, you can just do this
  exact ⟨hX, haX⟩,
end

-- The above comment says "an interesting way to start is ... "
-- But what is the alternative way to start?

end partition

/-

# 2) Equivalence classes.

We define equivalence classes and prove a few basic results about them.

-/

section equivalence_classes

/-!

## Definition of equivalence classes 

-/

-- Notation and variables for the equivalence class section:

-- let α be a type, and let R be a binary relation on α.
variables {α : Type} (R : α → α → Prop)

/-- The equivalence class of `a` is the set of `b` related to `a`. -/
def cl (a : α) :=
{b : α | R b a}

-- What is this saying?
-- From looking ahead a little. `cl R a ` is the set
-- which of b ∈ α, such that `R a b` is true.

-- ? How is this defining the equivalence class. 
-- The binary releation hasn't been specified to be an equivalence relation.

/-!

## Basic lemmas about equivalence classes

-/

/-- Useful for rewriting -- `b` is in the equivalence class of `a` iff
`b` is related to `a`. True by definition. -/
theorem mem_cl_iff {a b : α} : b ∈ cl R a ↔ R b a :=
begin
  -- true by definition
  refl
end

-- From definition above. cl R a is the set which contains all b : α
-- such that R b a is true. So yes, it's true by definition and this still has
-- nothing so far to do with equivalence relations.


-- Assume now that R is an equivalence relation.
variables {R} (hR : equivalence R)
include hR

-- Ah ha!  This could have been made clearer above..  The cl is NOT defining an equivalence
-- relation as I said. It's only a binary relation.   When you insist that it satisfies the
-- criteria for an equivalence, then it's an equivalence relation.
-- This defintion is in logic.lean and is
-- def equivalence := reflexive r ∧ symmetric r ∧ transitive r
-- so is the above is saying hR is a proof that R is an equivalence.
-- without providing that proof. Which we can't because R is a generic binary relation.

/-- x is in cl(x) -/
lemma mem_cl_self (a : α) :
  a ∈ cl R a :=
begin
  -- Note that `hR : equivalence R` is a package of three things.
  -- You can extract the things with
  -- `rcases hR with ⟨hrefl, hsymm, htrans⟩,` or
  -- `obtain ⟨hrefl, hsymm, htrans⟩ := hR,`
  rcases hR with ⟨hrefl, hsymm, htrans⟩,
  -- Note after looking up documentation of rcases, in case you
  -- don't know how many parts are in hR you can just do
  -- rcases? hR,
  -- The Lean infoview then gives you the following which can replace it
  -- rcases hR with ⟨hR_left, hR_right_left, hR_right_right⟩,
  -- goal is a ∈ cl R a
  -- and this is satisfied the the refeletivity requirement.
  exact hrefl a,
end

example (a : α) : a ∈ cl R a :=
begin
  -- a quick example show using hR.1 to use the part we want directly.
  exact hR.1 a,
end


lemma cl_sub_cl_of_mem_cl {a b : α} :
  a ∈ cl R b →
  cl R a ⊆ cl R b :=
begin
  -- remember `set.subset_def` says `X ⊆ Y ↔ ∀ a, a ∈ X → a ∈ Y
  -- First lets decode what this lemma is saying.
  --   a ∈ cl R b, means a is in the equivalence class of b
  --   implies the equivalence class of a is a subset of the equivalence class of b.
  -- We will need to use the hypothesis of R being an equivalence relation. So lets split it.
  obtain ⟨hrefl, hsymm, htrans⟩ := hR,
  -- The follow aren't necessary but they allow you to see the definition of what the three
  -- componets of the equivalence relation are.
  rw reflexive at hrefl,
  rw symmetric at hsymm,
  rw transitive at htrans,
  -- there's a reason this lemma follows the previous proof of mem_cl_self
  intro haRb, -- we have a in cl R b
  have hbRb : b ∈ cl R b,
  exact hrefl b,
  intros c hcRa,
  rw mem_cl_iff at haRb hcRa,
  rw mem_cl_iff,
  -- we now have hcRa : R c a, and haRb : R a b
  -- and want to prove R c b, which uses transitivity.
  exact htrans hcRa haRb,
end

-- Now we have the above proof. The following is the above "golfed"
lemma cl_sub_cl_of_mem_cl' {a b : α} :
  a ∈ cl R b →
  cl R a ⊆ cl R b :=
begin
  obtain ⟨hrefl, hsymm, htrans⟩ := hR,
  intros haRb c hcRa,
  rw mem_cl_iff at *,
  exact htrans hcRa haRb,
end
-- apart from or ording this is the same as the official solution.

lemma cl_eq_cl_of_mem_cl {a b : α} :
  a ∈ cl R b →
  cl R a = cl R b :=
begin
  -- remember `set.subset.antisymm` says `X ⊆ Y → Y ⊆ X → X = Y`

  -- This proof is saying that if a is in the equivalence class of b
  -- then the equivalence class of a is the same as the equivalence class of b.
  
  -- goal is an applies, so lets intro the hypothesis
  intro haRb,
  -- goal is now cl R a = cl R b
  -- now each of cl R a and cl R b are sets, so this is saying two sets are equal
  -- I'd like to split this to get the two goals of each one a subset of the other.
  -- but that doesn't work here. Hence the hint above, we need to use
  apply set.subset.antisymm,
  -- We now have two goals
  {
    -- goal  cl R a ⊆ cl R b
    -- this is just what we proved above.
    exact cl_sub_cl_of_mem_cl hR haRb,
  },
  {
    -- goal cl R b ⊆ cl R 
    -- Here we can't just use the earlier proof, so lets break up the equivalence of R.
    -- but we can apply
    apply cl_sub_cl_of_mem_cl hR,
    -- to change the goal to b ∈ cl R a
    obtain ⟨hrefl, hsymm, htrans⟩ := hR,
    exact hsymm haRb,
  }

end

end equivalence_classes -- section

/-!

# 3) The theorem

Let `α` be a type (i.e. a collection of stuff).

There is a bijection between equivalence relations on `α` and
partitions of `α`.

We prove this by writing down constructions in each direction
and proving that the constructions are two-sided inverses of one another.
-/

open partition

example (α : Type) : {R : α → α → Prop // equivalence R} ≃ partition α :=
-- We define constructions (functions!) in both directions and prove that
-- one is a two-sided inverse of the other
{ -- Here is the first construction, from equivalence
  -- relations to partitions.
  -- Let R be an equivalence relation.
  to_fun := λ R, {
    -- Let C be the set of equivalence classes for R.
    C := { B : set α | ∃ x : α, B = cl R.1 x},
    -- I claim that C is a partition. We need to check the three
    -- hypotheses for a partition (`Hnonempty`, `Hcover` and `Hdisjoint`),
    -- so we need to supply three proofs.
    Hnonempty := begin
      -- this cases line changes the 
      --    R: {R // equivalence R}
      -- to being
      --    R: α → α → Prop
      --    hR: equivalence R
      -- I.e. the two components, I'm not sure yet what the // does to group them
      -- together.
      cases R with R hR,
      -- If X is an equivalence class then X is nonempty.
      show ∀ (X : set α), (∃ (a : α), X = cl R a) → X.nonempty,
      rintros _ ⟨a, rfl⟩,
      use a,
      obtain ⟨hrefl, hsymm, htrans⟩ := hR,
      apply hrefl,
    end,
    Hcover := begin
      cases R with R hR,
      -- The equivalence classes cover α
      show ∀ (a : α), ∃ (X : set α) (H : ∃ (b : α), X = cl R b), a ∈ X,
      intro a,
      use cl R a,
      split,
        use a,
      apply hR.1,
    end,
    Hdisjoint := begin
      cases R with R hR,
      -- If two equivalence classes overlap, they are equal.
      show ∀ (X Y : set α), (∃ (a : α), X = cl R a) →
        (∃ (b : α), Y = cl _ b) → (X ∩ Y).nonempty → X = Y,
      intros X Y,
      rintro ⟨a, rfl⟩,
      rintro ⟨b, rfl⟩,
      rintro ⟨c, hca, hcb⟩,
      dsimp at *, -- solution offers this as a tidy up
      apply cl_eq_cl_of_mem_cl hR,
      -- goal is a ∈ cl R b
      -- hR is that R is an equivalence which has three parts
      --    reflexive R ∧ symmetric R ∧ transitive R
      -- but remember this is actually bracketed like this
      --    reflexive R ∧ ( symmetric R ∧ transitive R )
      -- so hR.2 is the ( symmetric R ∧ transitive R ) part
      -- and to get the transitive part directly we need
      -- hR.2.2
      apply hR.2.2,
      change R a c,
      apply hR.2.1, -- this is using the symmetric property
      exact hca,
      exact hcb,
    end },
  -- Conversely, say P is an partition. 
  inv_fun := λ P, 
    -- Let's define a binary relation `R` thus:
    --  `R a b` iff *every* block containing `a` also contains `b`.
    -- Because only one block contains a, this will work,
    -- and it turns out to be a nice way of thinking about it. 
    ⟨λ a b, ∀ X ∈ P.C, a ∈ X → b ∈ X, begin
      -- I claim this is an equivalence relation.
    split,
    { -- It's reflexive
      show ∀ (a : α)
        (X : set α), X ∈ P.C → a ∈ X → a ∈ X,
      intros a X hXC haX,
      assumption,
    },
    split,
    { -- it's symmetric
      show ∀ (a b : α),
        (∀ (X : set α), X ∈ P.C → a ∈ X → b ∈ X) →
         ∀ (X : set α), X ∈ P.C → b ∈ X → a ∈ X,
      intros a b h X hX hbX,
      obtain ⟨Y, hY, haY⟩ := P.Hcover a,
      specialize h Y hY haY,
      exact mem_of_mem hY hX h hbX haY,
    },
    { -- it's transitive
      unfold transitive,
      show ∀ (a b c : α),
        (∀ (X : set α), X ∈ P.C → a ∈ X → b ∈ X) →
        (∀ (X : set α), X ∈ P.C → b ∈ X → c ∈ X) →
         ∀ (X : set α), X ∈ P.C → a ∈ X → c ∈ X,
      intros a b c hbX hcX X hX haX,
      apply hcX,
      assumption,
      apply hbX;
      assumption,
    }
  end⟩,
  -- If you start with the equivalence relation, and then make the partition
  -- and a new equivalence relation, you get back to where you started.
  left_inv := begin
    rintro ⟨R, hR⟩,
    -- Tidying up the mess...
    suffices : (λ (a b : α), ∀ (c : α), a ∈ cl R c → b ∈ cl R c) = R,
      simpa,
    -- ... you have to prove two binary relations are equal.
    ext a b,
    -- so you have to prove an if and only if.
    show (∀ (c : α), a ∈ cl R c → b ∈ cl R c) ↔ R a b,
    split,
    { 
      intros hab,
      apply hR.2.1,
      apply hab,
      apply hR.1,
    },
    {
      intros hab c hac,
      apply hR.2.2,
      change R b a,
      apply hR.2.1,
      exact hab,
      exact hac,
    },
  end,
  -- Similarly, if you start with the partition, and then make the
  -- equivalence relation, and then construct the corresponding partition 
  -- into equivalence classes, you have the same partition you started with.  
  right_inv := begin
    -- Let P be a partition
    intro P,
    -- It suffices to prove that a subset X is in the original partition
    -- if and only if it's in the one made from the equivalence relation.
    ext X,
    show (∃ (a : α), X = cl _ a) ↔ X ∈ P.C,
    dsimp only,
    split,
    {
      rintro ⟨a, rfl⟩,
      obtain ⟨X, hX, haX⟩ := P.Hcover a,
      convert hX,
      ext b,
      rw mem_cl_iff,
      split,
      {
        intro haY,
        obtain ⟨Y, hY, hbY⟩ := P.Hcover b,
        specialize haY Y hY hbY,
        convert hbY,
        exact eq_of_mem hX hY haX haY,
      },
      { 
        intros hbX Y hY hbY,
        apply mem_of_mem hX hY hbX hbY haX,
      }
    },
    {
      intro hX,
      rcases P.Hnonempty X hX with ⟨a, ha⟩,
      use a,
      ext b,
      split,
      {
        intro hbX,
        rw mem_cl_iff,
        intros Y hY hbY,
        exact mem_of_mem hX hY hbX hbY ha,
      },
      {
        rw mem_cl_iff,
        intro haY,
        obtain ⟨Y, hY, hbY⟩ := P.Hcover b,
        specialize haY Y hY hbY,
        exact mem_of_mem hY hX haY ha hbY,
      }
    }
    
  end }

/--
The above hasn't really been explained, we have so far only proved theorems
and then we have this structure without any explanation.
These are my notes in trying to understand this.

Clicking on the ≃ symble and going to definition give the following:

  `α ≃ β` is the type of functions from `α → β` with a two-sided inverse.
  @[nolint has_inhabited_instance]
  structure equiv (α : Sort*) (β : Sort*) :=
  (to_fun    : α → β)
  (inv_fun   : β → α)
  (left_inv  : left_inverse inv_fun to_fun)
  (right_inv : right_inverse inv_fun to_fun)

So the above structure is providing the elements of this equiv structure.
In order to prove it is an equivalence relation.

to_fun is a function from α to β, in our case α is an equivalence relation 
and β is the partition. So to_fun defines a function from the equivalence relation
to the partition.
From the definition of partition above we have to show that it has:
  (Hnonempty : ∀ X ∈ C, (X : set α).nonempty)
  (Hcover : ∀ a, ∃ X ∈ C, a ∈ X)
  (Hdisjoint : ∀ X Y ∈ C, (X ∩ Y : set α).nonempty → X = Y)

Which is what is being proved in to_fun.


-/