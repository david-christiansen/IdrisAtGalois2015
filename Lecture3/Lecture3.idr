-- {hide}
-- These slides are intended to be used with live-code-talks-mode for Emacs.
-- {show}


-- # Dependently Typed Programming in Idris



-- ## David Raymond Christiansen


-- ### Session 3: Tactics and Effects
-- ### January 22, 2015



-- [[[(image :type imagemagick :file "galois.png" :width 0.3)]]]

-- {hide}
module Lecture3
import Data.Vect
import Effects
import Effect.File
import Effect.State
import Effect.StdIO
-- {show}


-- # Agenda

-- * Inside Idris
-- * Tactics and Proofs
-- * Syntax Extensions
-- *  Effects



-- # Compilation Process

-- [[[(image :type imagemagick :file "compiler.png" :max-height 0.7)]]]


-- # Elaborating Idris

-- ## Difficulties
-- * Solving implicit arguments
-- * Where blocks, with blocks, and case expressions
-- * Type class resolution
-- * Overloading


-- # A Tactic-Based Elaborator

-- The elaboration monad keeps track of a proof state, and has
-- operations for manipulating it.

-- ## Proof State
-- * A current proof term, potentially containing holes and guesses
-- * A focused hole
-- * A queue listing the unsolved holes
-- * A collection of open unification problems

-- ## Operations (Tactics)
-- * Place a guess into a the focused hole
-- * Mark a guess as the solution
-- * Introduce a lambda into a hole, with a new holes as the body
-- * Normalize the goal
-- * ...


-- # Totality and Proofs

-- Idris's totality checker ensures that definitions are defined for
-- all cases, and that all recursive calls are on a structurally
-- smaller input. This ensures consistency:

badProof : True = False
badProof = badProof

-- Remember: an infinite loop inhabits every type!

-- I recommend "%default total" at the top of your file.


-- # Interactive Proving and Tactics Scripts

-- In the first session, we wrote proofs like this.

plusZeroIdentity : (x : Nat) -> x `plus` 0 = x
plusZeroIdentity Z = Refl
plusZeroIdentity (S k) = cong (plusZeroIdentity k)

plusSRight : (x, y : Nat) -> x `plus` S y = S (x `plus` y)
plusSRight Z y = Refl
plusSRight (S k) y = cong (plusSRight k y)

plusIsCommutative : (x,y : Nat) -> x `plus` y = y `plus` x
plusIsCommutative Z y = sym $ plusZeroIdentity y
plusIsCommutative (S k) y =
  rewrite plusSRight y k
  in cong (plusIsCommutative k y)


-- # Interactive Proving and Tactics Scripts

-- We can also use the tactic system

plusZeroIdentity' : (x : Nat) -> x `plus` 0 = x
plusZeroIdentity' x = ?plusZeroIdentity'_rhs

plusSRight' : (x, y : Nat) -> x `plus` S y = S (x `plus` y)
plusSRight' x y = ?plusSRight'_rhs

plusIsCommutative' : (x,y : Nat) -> x `plus` y = y `plus` x
plusIsCommutative' x y = ?plusIsCommutative'_rhs



-- # Automatic Implicits

data Less : (j, k : Nat) -> Type where
  ZeroLess : Less 0 k
  SuccLess : Less j k -> Less (S j) (S k)

forSureSmaller : (x, y : Nat) -> {auto ok : Less x y} -> ()
forSureSmaller x y = ()

{-
yep : ()
yep = forSureSmaller 2 15

nope : ()
nope = forSureSmaller 15 2
-}


-- # Tactics for Implicits

-- Implicit arguments need not be solved by unification - default
-- values can be provided, and tactic scripts can construct
-- them.

forSureSame : (x, y : Nat) -> {default tactics {refine Refl; solve;}  ok : x = y} -> ()
forSureSame x y = ()

-- Custom tactics can be written to pattern-match a goal and write a
-- proof directly. If interested, ask me later for links.

-- This is usually not necessary in recent version of Idris!


-- # Provisional Definitions

-- When the types need rewriting, you can often do this separately to keep the code clear:

reverseVector : Vect n a -> Vect n a
reverseVector xs = go [] xs
  where
    go : Vect j a -> Vect k a -> Vect (j+k) a
    go acc []        = ?go_rhs1 -- acc
    go acc (x :: xs) = ?go_rhs2 -- go (x::acc) xs



-- # Syntax Extensions

-- Idris allows arbitrary syntax extensions. Example: type ascription.

syntax [tm] "∈" [ty] = the ty tm

-- Test 1: [1,2,3] ∈ Vect 3 Nat
-- Test 1: [1,2,3] ∈ List Integer

-- Please be judicious!


-- # The Effects Library

-- Edwin's effects library is for composing effectful operations with
-- associated resources.

-- Hello, world:
namespace Main
  hello : { [STDIO] } Eff ()
  hello = putStrLn "Hello, world!"

  {-
  main : IO ()
  main = run hello
  -}


-- # Resource State

-- ## Find the mistakes!

  -- lines : String -> { [FILE_IO ()] } Eff (List String)
  -- lines f = do open f Read
  --              case !eof of
  --                False => [| readine :: lines |]
  --                True => return []


-- # Composing Effectful Programs

-- Effectful programs can be combined:

  greet : List String -> { [STDIO] } Eff ()
  greet [] = return ()
  greet (n::ns) = do putStrLn (trim n); greet ns

  getNames : String -> { [FILE_IO ()] } Eff (List String)
  getNames file = do True <- open file Read | False => return []
                     ls <- allLines
                     close
                     return ls

    where allLines : { [FILE_IO (OpenFile Read)] } Eff (List String)
          allLines = case !eof of
                       False => [| readLine :: allLines |]
                       True => return []

  greetNames : { [FILE_IO (), STDIO] } Eff ()
  greetNames = greet !(getNames "names.txt")

  {-
  main : IO ()
  main = run greetNames
  -}


-- # Composing Effectful Programs
-- ## Multiple States

-- We can use the same effect twice with a label:

countEmpties : List String -> { ['Empty:::STATE Nat, 'NonEmpty::: STATE Nat] } Eff (Nat, Nat)
countEmpties [] = do empty    <-    'Empty :- get
                     nonEmpty <- 'NonEmpty :- get
                     return (empty, nonEmpty)
countEmpties (x::xs) = if x == ""
                         then do 'Empty :- update S
                                 countEmpties xs
                         else do 'NonEmpty :- update S
                                 countEmpties xs


-- # New Effects

-- The effects DSL is extended by adding a type for each new effect,
-- and then handlers for the contexts in which the effect makes sense.

data Counter : Effect where
  Init      : { () ==> Int } Counter ()
  Increment :        { Int } Counter ()
  Read      :        { Int } Counter Int


-- syntax "{" [inst] "}" [eff] =
--   eff inst (\result => inst)
-- syntax "{" [inst] "==>" "{" {b} "}" [outst] "}" [eff] =
--   eff inst (\b => outst)
-- syntax "{" [inst] "==>" [outst] "}" [eff] =
--   eff inst (\result => outst)


COUNTER : Type -> EFFECT
COUNTER t = MkEff t Counter


-- # New Effects

-- Handlers run effects. `handle` gets as arguments:
-- 1. Current state r
-- 2. Effectful operation
-- 3. Continuation desiring output and next state

instance Handler Counter m where
  handle () Init     k = k () 0
  handle r Increment k = k () (r+1)
  handle r Read      k = k r r


-- # Convenient interface

init : { [COUNTER ()] ==> [COUNTER Int] } Eff ()
init = call Init

incr : { [COUNTER Int] } Eff ()
incr = call Increment

read : { [COUNTER Int] } Eff Int
read = call Lecture3.Read


-- # Running effects

namespace Main
  main : IO ()
  main = do i <- run go
            print i
    where howManyDavids : List String -> { [COUNTER Int] } Eff Int
          howManyDavids [] = read
          howManyDavids (x::xs) = if x == "David"
                                    then do incr ; howManyDavids xs
                                    else howManyDavids xs

          go : { [COUNTER ()] ==> [COUNTER Int] } Eff Int
          go = do init; howManyDavids ["David", "Not David", "David", "someone else"]


-- # Thanks for attending!

-- ## More info
-- * idris-lang.org
-- * github.com/idris-lang/Idris-dev
-- * github.com/idris-hackers
-- * #idris on Freenode

-- ## Find me later
-- * david@davidchristiansen.dk
-- * itu.dk/people/drc
-- * github.com/david-christiansen

-- ## Exercises
-- Will be posted to the Galois blog entry, or at
-- github.com/david-christiansen/IdrisAtGalois2015


-- {hide}
-- Local Variables:
-- eval: (require 'custom)
-- eval: (eldoc-mode -1)
-- eval: (setq-local page-delimiter "^ *")
-- eval: (make-variable-buffer-local 'idris-metavariable-show-on-load)
-- eval: (setq idris-metavariable-show-on-load nil)
-- eval: (defun idris-talk-show-less (_b) (interactive) (idris-info-for-name :print-definition "Less"))
-- eval: (defun idris-talk-show-const2 (_b) (interactive) (idris-info-for-name :print-definition "const2'"))
-- eval: (defun idris-talk-show-loc (_b) (interactive) (idris-info-for-name :print-definition "SourceLocation"))
-- eval: (defun idris-talk-show-eval (_b) (interactive) (idris-info-for-name :print-definition "eval"))
-- eval: (defun idris-talk-find-code-file (_b) (interactive) (find-file (expand-file-name "Lecture2Code.idr")))
-- eval: (make-variable-buffer-local 'face-remapping-alist)
-- eval: (add-to-list 'face-remapping-alist '(live-code-talks-title-face (:height 2.0
--                                                                        :slant normal
--                                                                        :foreground "black" :family "Deja Vu Sans" :weight bold)))
-- eval: (add-to-list 'face-remapping-alist '(live-code-talks-subtitle-face (:height 1.5
--                                                                           :slant normal
--                                                                           :foreground "black" :family "Deja Vu Sans" :weight semibold)))
-- eval: (add-to-list 'face-remapping-alist '(live-code-talks-subsubtitle-face (:height 1.3
--                                                                              :slant normal
--                                                                              :foreground "black" :family "Deja Vu Sans")))
-- eval: (add-to-list 'face-remapping-alist
--                    '(live-code-talks-comment-face (:slant normal
--                                                    :foreground "black"
--                                                    :family "Deja Vu Sans")))
-- eval: (add-to-list 'face-remapping-alist
--                    '(idris-loaded-region-face (:background nil)))
-- idris-packages: ("effects")
-- End:
-- {show}

 
