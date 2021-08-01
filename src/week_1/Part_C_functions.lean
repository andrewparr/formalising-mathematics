import tactic

-- injective and surjective functions are already in Lean.
-- They are called `function.injective` and `function.surjective`.
-- It gets a bit boring typing `function.` a lot so we start
-- by opening the `function` namespace

open function

-- We now move into the `xena` namespace

namespace xena

-- let X, Y, Z be "types", i.e. sets, and let `f : X → Y` and `g : Y → Z`
-- be functions

variables {X Y Z : Type} {f : X → Y} {g : Y → Z}

-- let a,b,x be elements of X, let y be an element of Y and let z be an
-- element of Z

variables (a b x : X) (y : Y) (z : Z)

/-!
# Injective functions
-/

-- let's start by checking the definition of injective is
-- what we think it is.

-- This definition is saying the function f maps distinct elements to distinct elements
lemma injective_def : injective f ↔ ∀ a b : X, f a = f b → a = b :=
begin
  -- true by definition
  refl
end

-- You can now `rw injective_def` to change `injective f` into its definition.

-- The identity function id : X → X is defined by id(x) = x. Let's check this

-- Note. The defintion if id is
-- def id {α : Sort u} (a : α) : α := a

lemma id_def : id x = x :=
begin
  -- true by definition
  refl
end

-- you can now `rw id_def` to change `id x` into `x`

/-- The identity function is injective -/
lemma injective_id : injective (id : X → X) :=
begin
  -- following the comments, lets change the statement that id is injective to its defintion
  rw injective_def,
  -- we now have ∀ (a, b), id a = id b → a = b
  -- so we use intro to make an a and a b
  intros a b,
  -- use rw id_def twice to change the id a and then id b to a and b
  rw id_def,
  rw id_def,
  --tautology, -- we have to prove a = b → a = b, which can be proved with tautology,
  -- or by intro and exact as we haven't covered tautology yet.
  intro h, 
  exact h,
end

-- function composition g ∘ f is satisfies (g ∘ f) (x) = g(f(x)). This
-- is true by definition. Let's check this

lemma comp_def : (g ∘ f) x = g (f x) :=
begin
  -- true by definition
  refl
end

/-- Composite of two injective functions is injective -/
lemma injective_comp (hf : injective f) (hg : injective g) : injective (g ∘ f) :=
begin
  -- you could start with `rw injective_def at *` if you like.
  -- In some sense it doesn't do anything, but it might make you happier.
  rw injective_def at *, -- it makes it clearer.
  intros a b h,
  rw comp_def at h,
  rw comp_def at h,
  apply hf,
  apply hg,
  exact h,
end

example (hf : injective f) (hg : injective g) : injective (g ∘ f) :=
begin
  -- example to show you don't need the rw for definational statements
  -- they just make it clearer when using interactive theorem prover.
  intros a b h,
  apply hf,
  apply hg,
  exact h,
end

/-!

### Surjective functions

-/

-- Let's start by checking the definition of surjectivity is what we think it is

lemma surjective_def : surjective f ↔ ∀ y : Y, ∃ x : X, f x = y :=
begin
  -- true by definition
  refl
end

/-- The identity function is surjective -/
lemma surjective_id : surjective (id : X → X) :=
begin
  -- you can start with `rw surjective_def` if you like.
  -- rw surjective_def,
  intro a,
  use a,
  rw id_def,
end

-- If you started with `rw surjective_def` -- try deleting it.
-- Probably your proof still works! This is because
-- `surjective_def` is true *by definition*. The proof is `refl`.

-- For this next one, the `have` tactic is helpful.

/-- Composite of two surjective functions is surjective -/
lemma surjective_comp (hf : surjective f) (hg : surjective g) : surjective (g ∘ f) :=
begin
  rw surjective_def at *, -- again not necessary but helps to see what to do.
  intro z,
  {
    -- I can't seem to rw comp_def here, so just recall that (g ∘ f) x = g (f x)
    -- therefore we need to prove that
    --  ∃ (x : X), g (f x) = z
    -- we have hg: ∀ (y : Z), ∃ (x : Y), g x = y and z : Z
    -- The hint said the `have` tactic is helpful, but I couldn't get it to work
    -- and the solution doesn't use it anyway.
    -- we have a z and so hg z should give us a y.  But this is done with cases
    cases hg z with y hy,
    -- we now do this again, now with y to get an z using hf
    cases hf y with x hx,
    use x,
    -- goal is now (g ∘ f) x = z, which is g (f x) = z
    -- hx tells us f x = y
    -- The followin shoe line is required.  But it isn't explained what it does.
    -- before the goal is (g ∘ f) x = z, after it the goal is g (f x) = z
    -- these are the same!
    show g(f(x)) = z,
    -- I don't know why I couldn't just have rw hx, rw hy without this show line!
    rw hx,
    rw hy,
  },
end

/-
  The documentation for show is:
  `show t` finds the first goal whose target unifies with `t`.
  It makes that the main goal, performs the unification,
  and replaces the target with the unified version of `t`.
  On page 19 of https://leanprover-community.github.io/mathematics_in_lean/mathematics_in_lean.pdf
  It talks about the show tactic to structure the proof.  The text says the show is not needed but
  it helps to structure the proof. Above however it seems to be needed.
-/

/-!

### Bijective functions

In Lean a function is defined to be bijective if it is injective and surjective.
Let's check this.

-/

lemma bijective_def : bijective f ↔ injective f ∧ surjective f :=
begin
  -- true by definition
  refl
end

-- You can now use the lemmas you've proved already to make these
-- proofs very short.

/-- The identity function is bijective. -/
lemma bijective_id : bijective (id : X → X) :=
begin
  sorry,
end

/-- A composite of bijective functions is bijective. -/
lemma bijective_comp (hf : bijective f) (hg : bijective g) : bijective (g ∘ f) :=
begin
  sorry,
end

end xena
