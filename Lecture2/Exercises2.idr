module Exercises2

-- * Implement an AST and evaluator for simple arithmetic
-- expressions. Include an unsafe feature, such as division, and
-- report the source location of dynamic errors.


-- * Implement a well-typed interpreter for the simply-typed
-- λ-calculus. The interpreter should map DSL expressions to their
-- corresponding Idris objects - for instance, λ-abstractions should
-- map to Idris functions. Use some of the same techniques used in the
-- lecture. Pick a base type of your choice.


-- * Write DSL notation for your language.


-- ** Use error reflection to improve a type error message for your
-- well-typed interpreter. Unfortunately, the best documentation right
-- are the following paper drafts:
--  - http://itu.dk/people/drc/drafts/error-reflection-submission.pdf
--  - http://itu.dk/people/drc/drafts/idris-quasiquote-preproceedings.pdf
-- However, try to start with the example in the lecture and figure it
-- out before reading papers.


-- *** Modify the DSL from the lecture to allow assignments to change
-- a variable's type. Hint: make each statement give its input and
-- output contexts. Don't bother updating the error reflection.
-- Hint: What are the rules for Seq and While?


-- *** Embed an interesting DSL of your choice in Idris. What can you
-- guarantee with the type system? What can't you?
