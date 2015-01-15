-- {hide}
-- These slides are intended to be used with live-code-talks-mode for Emacs.
-- {show}


-- # Dependently Typed Programming in Idris



-- ## David Raymond Christiansen


-- ### Session 1: Introduction
-- ### January 15, 2015



-- [[[(image :type imagemagick :file "galois.png" :width 300)]]]

-- {hide}
module Main

import Debug.Error
-- {show}

-- # Agenda
-- 0. Motivation
-- 1. Hello, world!
-- 2. Datatypes and functions
-- 3. Pattern matching with dependent types
-- 4. Dependent functions and dependent pairs
-- 5. The equality type
-- 6. Using dependent pattern matching for views
-- 7. Documentation, help, and interactive editing
-- 8. Presentation of exercises


-- # Motivation

--[[[(image :type svg :file "overlap-1.svg" :width 300)]]]


-- # Motivation

--[[[(image :type svg :file "overlap-2.svg" :width 300)]]]


-- # Motivation

--[[[(image :type svg :file "overlap-3.svg" :width 300 :margin (55 . 0))]]]


-- # Type Systems Are Rubbish For Programming

-- A type-level lambda in Scala:

-- ({type F[A] = Either[A, String]})#F


-- # Type Systems Are Rubbish For Programming


-- sealed trait Nat {
--   type Plus[N <: Nat] <: Nat
-- }
-- trait Z extends Nat {
--   type Plus[N <: Nat] = N
-- }
-- trait S[M<:Nat] extends Nat {
--   type Plus[N <: Nat] = S[M#Plus[N]]
-- }


-- # Why write code twice?

-- data Nat = Z | S Nat

-- plus :: Nat -> Nat -> Nat
-- plus Z     k = k
-- plus (S j) k = S (plus j k)

-- type family Plus :: Nat -> Nat -> Nat where
--   Plus Z     k = k
--   Plus (S j) k = S (Plus j k)


-- ## Why do we need both?


-- # One Language to Rule Them All

-- [[[(image :type imagemagick :file "OneRing.png" :width 500)]]]

-- # One Language to Rule Them All

-- * One language for types and programs

-- * One language for compile-time and runtime computation

-- * Freely mix values and types in the same expressions


-- # Hello, world!



main : IO ()
main = do putStrLn "Who are you?"
          name <- getLine
          putStrLn $ "Hello, " ++ name


-- # Datatypes and functions
-- ## Natural Numbers

data Nat' = Z' | S' Nat'

%name Nat' j,k

plus' : Nat' -> Nat' -> Nat'
plus' Z'     k = k
plus' (S' j) k = S' (plus' k j)




-- # Datatypes and Functions
-- ## Lists

namespace MyList
  data List' a = Nil | (::) a (List' a)

  %name List' xs, ys, zs

  -- Should we do as in Haskell?
  zipWith : (a -> b -> c) -> List' a -> List' b -> List' c
  zipWith f [] _ = []
  zipWith f _ [] = []
  zipWith f (x :: xs) (y :: ys) = f x y :: zipWith f xs ys

  -- Or we can do as in F#
  zipWithF : (a -> b -> c) -> List' a -> List' b -> List' c
  zipWithF f [] [] = []
  zipWithF f [] (x :: xs) = error "Mismatched lengths"
  zipWithF f (x :: xs) [] = error "Mismatched lengths"
  zipWithF f (x :: xs) (y :: ys) = f x y :: zipWithF f xs ys



-- # Datatypes and Functions
-- ## Vect

data Vect : Nat -> Type -> Type where
  Nil : Vect Z a
  (::) : a -> Vect n a -> Vect (S n) a

%name Vect xs,ys,zs

||| Write some docs!
|||
||| It supports _markdown_, terms `S Z`.
|||
||| ```idris example
||| 40 + 2
||| ```
zipWith : (a -> b -> c) -> Vect n a -> Vect n b -> Vect n c
zipWith f [] [] = []
zipWith f (x :: xs) (y :: ys) = f x y :: zipWith f xs ys

append : Vect n a -> Vect m a -> Vect (plus n m) a
append [] ys = ys
append (x :: xs) ys = x :: append xs ys


-- # Dependent Functions
-- Dependent functions cause substitution of earlier argument
-- values into the types of later arguments:

||| Return `n` copies of `x`.
|||
||| @ n The number of copies
||| @ x The element to be copied
||| @ a The type of elements
repeat : (n : Nat) -> (x : a) -> Vect n a
repeat Z     x = []
repeat (S k) x = x :: repeat k x


take : (n : Nat) -> Vect (n+k) a -> Vect n a
take Z     xs = []
take (S n) (x :: xs) = x :: take n xs

-- # Dependent Pairs

-- Dependent pairs substitute their first projection into the type of
-- their second projection.

fourElts : (n : Nat ** Vect n Int)
fourElts = (4 ** [1,2,3,4])

filter : (a -> Bool) -> Vect n a -> (m ** Vect m a)
filter f []        = (_ ** [])
filter f (x :: xs) = case (filter f xs) of
                       (m ** res) =>
                          if f x
                            then (S m ** x::res)
                            else (  m **    res)



-- # Heterogeneous lists

namespace HList
  data HList : List Type -> Type where
    Nil  : HList []
    (::) : t -> HList ts -> HList $ t :: ts

  mixed : HList [String, Nat, Integer]
  mixed = ["Wow!", 42, 42]

  (++) : HList as -> HList bs -> HList $ as ++ bs
  []        ++ ys = ys
  (x :: xs) ++ ys = x :: xs ++ ys


-- # The Equality Type

-- The equality type encodes the fact that two objects are in fact the same

-- {{{Print definition|||idris-talk-show-eq}}}

-- We can prove:

||| Called `sym` in lib
symmetry : x = y -> y = x
symmetry Refl = Refl


||| Called `trans` in lib
transitivity : x = y -> y = z -> x = z
transitivity Refl Refl = Refl


||| Called `cong` in lib
congruence : {f : a -> b} -> x = y -> f x = f y
congruence Refl = Refl



-- # Being honest with Vect

sulp : Nat -> Nat -> Nat
sulp k Z     = k
sulp k (S j) = S (sulp k j)

sulpZeroNeutral : (k : Nat) -> sulp 0 k = k
sulpZeroNeutral Z = Refl
sulpZeroNeutral (S k) = cong $ sulpZeroNeutral k

sulpSuccLeftSucc : (j,k : Nat) -> sulp (S j) k = S (sulp j k)
sulpSuccLeftSucc j Z = Refl
sulpSuccLeftSucc j (S k) = cong (sulpSuccLeftSucc j k)

appendHard : Vect n a -> Vect m a -> Vect (sulp n m) a
appendHard {m=m} []  ys = rewrite sulpZeroNeutral m in ys
appendHard {n=S n} {m = m} (x :: xs) ys =
  rewrite sulpSuccLeftSucc n m
  in x :: appendHard xs ys




-- # Views with dependent patterns

-- We can use equalities induced by dependent pattern matching to view
-- ordinary data differently. For example, we can extract the last
-- element of a list instead of the first.

data SnocList : List a -> Type where
  Empty : SnocList []
  Snoc : (xs : List a) -> (x : a) -> SnocList $ xs ++ [x]

snocced : (xs : List a) -> SnocList xs
snocced []        = Empty
snocced (x :: xs) with (snocced xs)
  snocced (x :: [])          | Empty       = Snoc [] x
  snocced (x :: (ys ++ [y])) | (Snoc ys y) = Snoc (x::ys) y

rot : List a -> List a
rot xs with (snocced xs)
  rot []          | Empty       = []
  rot (ys ++ [x]) | (Snoc ys x) = x :: ys


-- # Propositions and types

-- ## Connectives
-- Disjunction: Either
-- Conjunction: Pair types
-- Truth: ()
-- Falsity: Void
-- Implication: (->)
-- Negation: A -> Void

-- ## Quantifiers
-- Universal: dependent functions (n : Nat) -> n + n = 2 * n
-- Existential: dependent pairs      (n : Nat ** n + 7 = 13)

-- This is the  {{{Brouwer-Heyting-Kolmogorov Interpretation|||(lambda (_b) (browse-url "https://en.wikipedia.org/wiki/Brouwer%E2%80%93Heyting%E2%80%93Kolmogorov_interpretation"))}}}



-- # Using the Tools

-- Idris contains integrated documentation as well as searching of
-- documentation and types.

-- {{{Open REPL|||(lambda (_x) (idris-repl))}}}

-- Commands:
--  * :type		Show type
--  * :doc		Show documentation
--  * :apropos	Search names, types, and documentation
--  * :search	Search by type
--  * :whocalls	Find the use sites of a name
--  * :callswho	Follow the call tree from a name


-- # Thanks for your attention!

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
-- Will be posted to the Galois blog entry

-- {hide}
-- Local Variables:
-- eval: (eldoc-mode -1)
-- eval: (make-variable-buffer-local 'idris-metavariable-show-on-load)
-- eval: (setq idris-metavariable-show-on-load nil)
-- eval: (defun idris-talk-show-eq (_b) (interactive) (idris-info-for-name :print-definition "(=)"))
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
-- End:
-- {show}
