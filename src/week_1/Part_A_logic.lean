-- We import all of Lean's standard tactics
import tactic

/-!
# Logic

We will develop the basic theory of following five basic logical symbols

* `→` ("implies" -- type with `\l`)
* `¬` ("not" -- type with `\not` or `\n`)
* `∧` ("and" -- type with `\and` or `\an`)
* `↔` ("iff" -- type with `\iff` or `\lr`)
* `∨` ("or" -- type with `\or` or `\v`

# Tactics you will need to know

* `intro`
* `exact`
* `apply`
* `rw`
* `cases`
* `split`
* `left`
* `right`

See `README.md` in `src/week_1` for an explanation of what these
tactics do.

Note that there are plenty of other tactics, and indeed once you've
"got the hang of it" you might want to try tactics such as `cc`, 
`tauto` and its variant `tauto!`, `finish`, and `library_search`.

# What to do

The `example`s are to demonstrate things to you. They sometimes
use tactics you don't know. You can look at them but you don't
need to touch them. 

The `theorem`s and `lemma`s are things which have no proof. You need to change
the `sorry`s into proofs which Lean will accept.

This paragraph is a comment, by the way. One-line comments
are preceded with `--`.
-/

-- We work in a "namespace". All this means is that whenever it
-- looks like we've defined a new theorem called `id`, its full
-- name is `xena.id`. Which is good because `id` is already
-- defined in Lean.
namespace xena

-- Throughout this namespace, P Q and R will be arbitrary (variable)
-- true-false statements.
variables (P Q R : Prop)

/-!
## implies (→)

To prove the theorems in this section, you will need to know about
the tactics `intro`, `apply` and `exact`. You might also like
the `assumption` tactic.
-/

/-- Every proposition implies itself. -/
theorem id : P → P :=
begin
  -- Prove this using `intro` and `exact`
  intro h, -- this gives us h : P and changes goal to P
  exact h -- our goal is P and h is a proof of P so our goal is exact h.
end

/-
Note that → isn't associative!
Try working out `false → (false → false) and (false → false) → false
-/

example : (false → (false → false)) ↔ true := by simp
example : ((false → false) → false) ↔ false := by simp

-- in Lean, `P → Q → R` is _defined_ to mean `P → (Q → R)`
-- Here's a proof of what I just said.
example : (P → Q → R) ↔ (P → (Q → R)) :=
begin
  -- look at the goal!
  refl -- true because ↔ is reflexive
end

theorem imp_intro : P → Q → P :=
begin
  -- remember that by definition the goal is P → (Q → P).
  -- Prove this proposition using `intro` and `exact`.
  -- Experiment. Can you prove it using `intros` and `assumption`?
  intro hP, -- gives us hP : P with goal Q → P
  intro hQ, -- give us hQ : Q
  exact hP
end

theorem imp_intro' : P → Q → P :=
begin
  -- remember that by definition the goal is P → (Q → P).
  -- Experiment. Can you prove it using `intros` and `assumption`?
  intros hP hQ, -- gives us hP : P and hQ : Q in one line
  assumption -- proves the goal using the hypotheses we have
end


/-- If we know `P`, and we also know `P → Q`, we can deduce `Q`. -/
lemma modus_ponens : P → (P → Q) → Q :=
begin
  -- You might find the `apply` tactic useful here.
  intros hP hPQ, -- gives use hP : P and hPQ : P → Q and goal Q
  apply hPQ, -- if we have to prove Q and we have proof of P → Q, then it's sufficient to prove P
  exact hP
end

/-- implication is transitive -/
lemma imp_trans : (P → Q) → (Q → R) → (P → R) :=
begin
  -- The tactics you know should be enough
  intros hPQ hQR hP, -- goal left as R
  apply hQR, -- changes goal from R to Q
  apply hPQ, -- chnages goal from Q to P
  exact hP
end

-- This one is a "relative modus ponens" -- in the
-- presence of P, if Q -> R and Q then R.
lemma forall_imp : (P → Q → R) → (P → Q) → (P → R) :=
begin
  -- `intros hPQR hPQ hP,` would be a fast way to start.
  -- Make sure you understand what is going on there, if you use it.
  intros hPQR hPQ hP, -- hPQR : P → Q → R, hPQ : P → Q, hP : P
  -- the goal here is R
  apply hPQR, -- we want R, and we have P → Q → R and so it is sufficient to prove both P and Q
  {exact hP}, -- when you have two goals it's common practive to use {} to separate goals out
  -- the goal in {} is just P and that is exactly hP,
  apply hPQ, -- to prove Q it is sufficient to prove P
  exact hP,
end

/- My notes on what the above is saying.
  The statement says that if P implies that (Q implies R) and that P implies Q
  Then are also have P implies R.
  Suppose
    hP is I'm English.
    hQ is I drink tea.
    hR is I dunk biscuits in my tea.
    P → R, says English people dunk biscuits in their tea.
    That's what you want to prove to prove this you have the proof that
    hPQR which is If you are English then your dunk bisbuits in your tea.
    and hPQ which is If you are English then you drink tea.
-/

/-

### not

`not P`, with notation `¬ P`, is *defined* to mean `P → false` in Lean,
i.e., the proposition that P implies false. You can easily check with
a truth table that P → false and ¬ P are equivalent.

We develop a basic interface for `¬`.
-/


-- I'll prove this one for you
theorem not_iff_imp_false : ¬ P ↔ (P → false) :=
begin
  -- true by definition
  refl
end

theorem not_not_intro : P → ¬ (¬ P) :=
begin
  intro hP,
  rw not_iff_imp_false,
  -- You can use `rw not_iff_imp_false` to change `¬ X` into `X → false`. 
  -- But you don't actually have to, because they are the same *by definition*
  -- Here we have hP : need to prove ¬P → false
  -- intro nP here gives hP : P and nP : ¬ P 
  -- with the goal of false - but not sure how that helps.
  -- tauto, here finishes the goal
  -- finish, so does finish
  -- hint, here also tells you tauto and finish will finish this goal
  -- suggest, -- this suggests exact not_not_intro hP
  -- exact not_not_intro hP,  -- this also finishes the goal
  -- apply not_not_intro hP, -- this also closed the goal
  -- In an attempt to see what is going on, 
  -- the goal here is ¬ P → false 
  apply not_not_intro, -- this changes the goal of ¬¬ P to P
  -- NOTE: the goal was ¬¬ P before the rw not_iff_imp_false, line
  -- these are (as stated above) definitionally equivalent.
  -- after this line the goal is P which is exactly hP
  exact hP,
end

-- Here is a funny alternative proof! Can you work out how it works?
example : P → ¬ (¬ P) :=
begin
  apply modus_ponens,
  -- Recall modus ponens says 
  -- "If we know P, and we also know P → Q, we can deduce Q. "
  -- That is P → (P → Q) → Q 
  -- Here P is P, and Q is ¬ ¬ P
  -- which is definitionally equivalent to ¬ P → false
  -- which is P → true ?
  -- if this is the case then apply modus_ponens would take
  -- P and P → true to make true. So it works!
end

-- Here is a proof which does not use tactics at all, but uses lambda calculus.
-- It is called a "term mode" proof. We will not be discussing term mode
-- much in this course. It is a cool way to do basic logic proofs, but
-- it does not scale well in practice.
example : P → ¬ (¬ P) :=
λ hP hnP, hnP hP

/- What is going on with this "term mode" proof above?
  The equivalent tactic proof is shown below.
   λ hP hnP is the equivalent to
   intros hP hnP
   hnP is just apply hnP
   hP is just apply hP (or better written as exact hP)
-/
example : P → ¬ (¬ P) :=
begin
  intros hP hnP,
  apply hnP,
  apply hP, -- it would be better to write exact hP here
end


-- This is "modus tollens". Some mathematicians think of it as
-- "proof by contradiction".
theorem modus_tollens : (P → Q) → (¬ Q → ¬ P) :=
begin
  intros hPQ hnQ, -- hPQ : P → Q, hnQ : ¬ Q 
  -- the goal here is -P, which we know from above is equivalent to
  -- P → false and so
  intro hP, -- gives us hP : P and goal false
  apply hnQ,
  apply hPQ,
  exact hP,
end

-- OK, based on what was said above. Let's try and write this as a term mode proof
-- Clearly it's more complicated than I suggested, I had to drop into tatic mode
-- for this to work. So you can't just list the Props to "apply" them.
-- Still this is a "compact" form of the above.
example : (P → Q) → (¬ Q → ¬ P) :=
λ hPQ hnQ hP, by {apply hnQ, apply hPQ, exact hP}


-- This one cannot be proved using constructive mathematics!
-- You _have_ to use a tactic like `by_contra` (or, if you're happy
-- to cheat, the full "truth table" tactic `tauto!`.
-- Try it without using these, and you'll get stuck!
theorem double_negation_elimination : ¬ (¬ P) → P :=
begin
  -- tauto!, -- This will solve it in one line, but surely a cheat when learning lean.
  intro hnnP, -- hnnP : ¬¬P
  by_contradiction hnP, -- note by_contra achieves the same thing with less letters and less clear to me.
  -- exact hnnP hnP, -- This works, I found this from using library_search.
  --   This is possibly just a shortcut way of writting the following clearer proof.
  -- A clearly method.
  -- after using by_contradiction above our goal is false.
  -- we have hnnP : ¬¬P which is saying ¬P → false
  -- so we can apply this to false
  apply hnnP, -- This says to prove false we have to prove ¬ P
  -- but this is exactly hnP we got from the by_contradiction line above.
  exact hnP,
end

/-!

### and

The hypothesis `hPaQ : P ∧ Q` in Lean, is equivalent to
hypotheses `hP : P` and `hQ : Q`. 

If you have `hPaQ` as a hypothesis, and you want to get to
`hP` and `hQ`, you can use the `cases` tactic.

If you have `⊢ P ∧ Q` as a goal, and want to turn the goal
into two goals `⊢ P` and `⊢ Q`, then use the `split` tactic.

Note that after `split` it's good etiquette to use braces
e.g.

example (hP : P) (hQ : Q) : P ∧ Q :=
begin
  split,
  { exact hP },
  { exact hQ }
end

but for this sort of stuff I think principled indentation
is OK

```
example (hP : P) (hQ : Q) : P ∧ Q :=
begin
  split,
    exact hP,
  exact hQ
end
```

-/

theorem and.elim_left : P ∧ Q → P :=
begin
  -- I would recommend starting with
  -- `intro hPaQ,` and then `cases hPaQ with hP hQ`.
  intro hPaQ,
  cases hPaQ with hP hQ,
  exact hP,
end

theorem and.elim_right : P ∧ Q → Q :=
begin
  intro hPaQ,
  exact hPaQ.right, -- another way without using cases
  -- note exact hPaQ.2 also works
end

-- fancy term mode proof
example : P ∧ Q → Q := λ hPaQ, hPaQ.2

-- my fancy term mode proof of hte first case
example : P ∧ Q → P := λ hPaQ, hPaQ.1

-- note, .1 and .2 are used here rather than .left and .right
-- but .left works in this term proof and as commented above
-- hPaQ.2 works in the tactic proof.  So these are probaly
-- just different ways of saying the same thing.

theorem and.intro : P → Q → P ∧ Q :=
begin
  -- remember the `split` tactic.
  intros hP hQ,
  split,
    exact hP,
  exact hQ,
end

/-- the eliminator for `∧` -/ 
theorem and.elim : P ∧ Q → (P → Q → R) → R :=
begin
  intro hPaQ, -- give  hPaQ : P ∧ Q
  intro hPQR, -- gives hPQR : P → Q → R (with goal of R)
  apply hPQR, -- makes two goals P and Q these are the left and right of hPaQ
    exact hPaQ.1,
  exact hPaQ.2
end

/-- The recursor for `∧` -/
theorem and.rec : (P → Q → R) → P ∧ Q → R :=
begin
  intros hPQR hPaQ,
  apply hPQR,
    exact hPaQ.1,
  exact hPaQ.2,
end

/-- `∧` is symmetric -/
theorem and.symm : P ∧ Q → Q ∧ P :=
begin
  -- this is interesting. If I just used normal intro hPaQ
  -- I would get hPaQ : P ∧ Q. Which is fine and I can use hPaQ.1 for proof of P
  -- and hPaQ.2 for proof of Q. However using rintros as below I get directly
  -- hP : P and hQ : Q
  rintros ⟨hP, hQ⟩,
  split, -- goal here is Q ∧ R so we split to get the two goals we need to prove
    exact hQ,
  exact hP,
end

-- term mode proof
example : P ∧ Q → Q ∧ P :=
λ ⟨hP, hQ⟩, ⟨hQ, hP⟩

/- My notes, thoughts on above.
 λ ⟨hP, hQ⟩ does the same as the rintos line I have above
 the ⟨hQ, hP⟩ is obviously a term mode of writing the split and exacts that I have above.
-/

/-- `∧` is transitive -/
theorem and.trans : (P ∧ Q) → (Q ∧ R) → (P ∧ R) :=
begin
  -- The `rintro` tactic will do `intro` and `cases` all in one go.
  -- If you like, try starting this proof with `rintro ⟨hP, hQ⟩` if you want
  -- to experiment with it. Get the pointy brackets with `\<` and `\>`,
  -- or both at once with `\<>`.
  rintro ⟨hP, hQ⟩,
  rintro ⟨hQ', hR⟩, -- end up with to hypothesis of Q here
  exact ⟨hP, hR⟩, -- and the exact can also be used to prove P ∧ R in one go
end

-- OK, lets see if I can write that as a term mode proof following previous example 
example : (P ∧ Q) → (Q ∧ R) → (P ∧ R) :=
λ ⟨hP, hQ⟩ ⟨hQ', hR⟩, ⟨hP, hR⟩ 
-- that seems to have worked.

/-
Recall that the convention for the implies sign →
is that it is _right associative_, by which
I mean that `P → Q → R` means `P → (Q → R)` by definition.
Now note that if `P` implies `Q → R`
then this means that `P` and `Q` together, imply `R`,
so `P → Q → R` is logically equivalent to `(P ∧ Q) → R`.

We proved that `P → Q → R` implied `(P ∧ Q) → R`; this was `and.rec`.
Let's go the other way.
-/

lemma imp_imp_of_and_imp : ((P ∧ Q) → R) → (P → Q → R) :=
begin
  --intros hPaQ hP hQ,
  intros hPaQ hP hQ,
  apply hPaQ,
  exact ⟨hP, hQ⟩,
end

-- Note the solutions have a shorter way with just
lemma imp_imp_of_and_imp' : ((P ∧ Q) → R) → (P → Q → R) :=
begin
  --intros hPaQ hP hQ,
  intros hPaQ hP hQ,
  exact hPaQ ⟨hP, hQ⟩,
end

-- and this way probably leads to a term mode proof
--lemma imp_imp_of_and_imp'' : ((P ∧ Q) → R) → (P → Q → R) :=
--λ hPaQ hP hQ, ⟨hPaQ hP hQ⟩
-- but the above doesn't work.


/-!

### iff

The basic theory of `iff`.

In Lean, to prove `P ∧ Q` you have to prove `P` and `Q`.
Similarly, to prove `P ↔ Q` in Lean, you have to prove `P → Q`
and `Q → P`. Just like `∧`, you can uses `cases h` if you have
a hypothesis `h : P ↔ Q`, and `split` if you have a goal `⊢ P ↔ Q`.
-/

/-- `P ↔ P` is true for all propositions `P`, i.e. `↔` is reflexive. -/
theorem iff.refl : P ↔ P :=
begin
  -- start with `split`
  split,
  -- note id is already a proof of P → P so we just need to apply it
  { apply id },
  { apply id }
  -- how does this work, the goal is P → P, apply what what is apply doing 
  -- from https://leanprover-community.github.io/mathlib_docs/tactics.html#apply
  -- The apply tactic tries to match the current goal against the conclusion of the type of term.
  -- it maches the current goal against the conculsion
  -- If it succeeds, then the tactic returns as many subgoals as the number of premises that
  -- have not been fixed by type inference or type class resolution.
end

-- If you get stuck, there is always the "truth table" tactic `tauto!`
example : P ↔ P :=
begin
  tauto!, -- the "truth table" tactic.
end

-- refl tactic also works
example : P ↔ P :=
begin
  refl -- `refl` knows that `=` and `↔` are reflexive.
end

/-- `↔` is symmetric -/
theorem iff.symm : (P ↔ Q) → (Q ↔ P) :=
begin
  intro hPiffQ,
  split,
  -- hey it looks like you can also use .1 and .2 to get the two different direction
  -- hypotheses from the ↔
  exact hPiffQ.2,
  exact hPiffQ.1,  
end

-- NB there is quite a devious proof of this using `rw`.

-- show-off term mode proof
example : (P ↔ Q) → (Q ↔ P) :=
λ ⟨hPQ, hQP⟩, ⟨hQP, hPQ⟩

/-- `↔` is commutative -/
theorem iff.comm : (P ↔ Q) ↔ (Q ↔ P) :=
begin
  split,
  -- using same technique above after a split can just apply previous result.
    apply iff.symm,
  apply iff.symm,
end

-- without rw or cc this is painful!
/-- `↔` is transitive -/
theorem iff.trans :  (P ↔ Q) → (Q ↔ R) → (P ↔ R) :=
begin
  intros hPQ hQR, -- hPQ : P ↔ Q, hQR : Q ↔ R
  -- goal here is P ↔ R
  rw hPQ, -- changes the P in goal to R to make goal Q ↔ R
  rw hQR, -- changes the Q in goal to R to make goal R ↔ R
  -- which is automatically solved so we're done.
end

-- This can be done constructively, but it's hard. You'll need to know
-- about the `have` tactic to do it. Alternatively the truth table
-- tactic `tauto!` will do it.
theorem iff.boss : ¬ (P ↔ ¬ P) :=
begin
  -- goal is ¬ (P ↔ ¬ P) so rintro does the intros and cases to make
  rintro ⟨h1, h2⟩, -- h1 : P → ¬ P, h2 : ¬ P → P
  -- both h1 and h2 are contradictory, but how do you use this to prove false?
  -- by_contradiction does not holp here.
  have hnP : ¬ P, {  -- this is the syntax for saying we want to have hnP : ¬ P
    -- here inside these {} we need our proof of hP
    -- goal is ¬ P which is the same as P → false and so
    intro hP, -- gives hP : P with goal of false
    exact h1 hP hP, -- I cheeted and looked up the answer!
    -- why does this line close the goal.
    -- suggest, -- does offer this though, so if I'd tried that I wouldn't have needed to cheet!
  },
  -- goal here is false, but we have hnP : ¬ P here to help,
  exact hnP (h2 hnP), -- this line was offered to me by suggest.
end

theorem iff.boss' : ¬ (P ↔ ¬ P) :=
begin
  -- the cheating way with tauto!
  tauto!,
end

-- Now we have iff we can go back to and.

/-!
### ↔ and ∧
-/

/-- `∧` is commutative -/
theorem and.comm : P ∧ Q ↔ Q ∧ P :=
begin
  split,
  {
    intro h,
    split,
      exact h.2,
    exact h.1,
  },{
    intro h,
    split,
      exact h.2,
    exact h.1,
  }
end

-- note the solution is quite neat
-- and uses apply to use an already proved result.
theorem and.comm' : P ∧ Q ↔ Q ∧ P :=
begin
  split; -- semicolon means "apply next tactic to all goals generated by this one"
  apply and.symm,
end



-- fancy term-mode proof
example : P ∧ Q ↔ Q ∧ P :=
⟨and.symm _ _, and.symm _ _⟩

-- Note that ∧ is "right associative" in Lean, which means
-- that `P ∧ Q ∧ R` is _defined to mean_ `P ∧ (Q ∧ R)`.
-- Associativity can hence be written like this:
/-- `∧` is associative -/
theorem and_assoc : ((P ∧ Q) ∧ R) ↔ (P ∧ Q ∧ R) :=
begin
  split,
  rintro ⟨hPnQ, pR⟩,
  split, exact hPnQ.1,
  exact ⟨hPnQ.2, pR⟩,
  rintro ⟨hP, hQnR⟩,
  split, exact ⟨hP, hQnR.1⟩,
  exact hQnR.2,
end

-- note solution provides the short-cut way of writting this as
theorem and_assoc' : ((P ∧ Q) ∧ R) ↔ (P ∧ Q ∧ R) :=
begin
  split,
  { rintro ⟨⟨hP, hQ⟩, hR⟩,
    exact ⟨hP, hQ, hR⟩ },
  { rintro ⟨hP, hQ, hR⟩,
    exact ⟨⟨hP, hQ⟩, hR⟩ },
end

/-!

## Or

`P ∨ Q` is true when at least one of `P` and `Q` are true.
Here is how to work with `∨` in Lean.

If you have a hypothesis `hPoQ : P ∨ Q` then you 
can break into the two cases `hP : P` and `hQ : Q` using
`cases hPoQ with hP hQ`

If you have a _goal_ of the form `⊢ P ∨ Q` then you
need to decide whether you're going to prove `P` or `Q`.
If you want to prove `P` then use the `left` tactic,
and if you want to prove `Q` then use the `right` tactic.

-/

-- recall that P, Q, R are Propositions. We'll need S for this one.
variable (S : Prop)

-- You will need to use the `left` tactic for this one.
theorem or.intro_left : P → P ∨ Q :=
begin
  intro hP,
  left,
  exact hP,
end

theorem or.intro_right : Q → P ∨ Q :=
begin
  intro hQ,
  right,
  exact hQ,
end

/-- the eliminator for `∨`. -/
theorem or.elim : P ∨ Q → (P → R) → (Q → R) → R :=
begin
  intro hPoQ,
  cases hPoQ with hP hQ, -- here we split P ∨ Q in the two case with P or with Q
  {
    intro hPR,
    intro hQR,
    apply hPR,
    exact hP,
  },
  {
    intro hPR,
    intro hQR,
    apply hQR,
    exact hQ,
  }
end

/-- `∨` is symmetric -/
theorem or.symm : P ∨ Q → Q ∨ P :=
begin
  intro h,
  cases h,
  {right, assumption},
  {left, assumption}
end

/-- `∨` is commutative -/
theorem or.comm : P ∨ Q ↔ Q ∨ P :=
begin
  sorry,
end

/-- `∨` is associative -/
theorem or.assoc : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R :=
begin
  sorry,
end

/-!
### More about → and ∨
-/

theorem or.imp : (P → R) → (Q → S) → P ∨ Q → R ∨ S :=
begin
  sorry,
end

theorem or.imp_left : (P → Q) → P ∨ R → Q ∨ R :=
begin
  sorry,
end

theorem or.imp_right : (P → Q) → R ∨ P → R ∨ Q :=
begin
  sorry,
end

theorem or.left_comm : P ∨ Q ∨ R ↔ Q ∨ P ∨ R :=
begin
  -- Try rewriting `or.comm` and `or.assoc` to do this one quickly.
  sorry,
end

/-- the recursor for `∨` -/
theorem or.rec : (P → R) → (Q → R) → P ∨ Q → R :=
begin
  sorry,
end

theorem or_congr : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) :=
begin
  sorry,
end

/-!

### true and false

`true` is a true-false statement, which can be proved with the `trivial` tactic.

`false` is a true-false statment which can only be proved if you manage
to find a contradiction within your assumptions.

If you manage to end up with a hypothesis `h : false` then there's quite
a funny way to proceed, which we now explain.

If you have `h : P ∧ Q` then you can uses `cases h with hP hQ` to split
into two cases. 

If you have `h : false` then what do you think happens if we do `cases h`?
Hint: how many cases are there?
-/


/-- eliminator for `false` -/
theorem false.elim : false → P :=
begin
  sorry,
end

theorem and_true_iff : P ∧ true ↔ P :=
begin
  sorry,
end

theorem or_false_iff : P ∨ false ↔ P :=
begin
  sorry,
end

-- false.elim is handy for this one
theorem or.resolve_left : P ∨ Q → ¬P → Q :=
begin
  sorry,
end

-- this one you can't do constructively
theorem or_iff_not_imp_left : P ∨ Q ↔ ¬P → Q :=
begin
  sorry,
end

end xena

