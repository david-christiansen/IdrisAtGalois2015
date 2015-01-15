module Exercises1

-- Ways to get help:
-- 1. Ask David
-- 2. #idris on Freenode
-- 3. Idris mailing list


-- This tells Idris to reject programs that it can't tell are
-- total. Totality means that there are no missing type-correct
-- patterns and that each call will halt.
%default total
-- If your program isn't total, you can tell Idris to allow it with
-- the "partial" modifier. For example:
||| Infinite loops inhabit every type, even the empty ones!
partial
forever : Void
forever = forever


-- We don't import Data.Vect because namespace conflicts are
-- irritating. Thus:

data Vect : Nat -> Type -> Type where
  Nil : Vect 0 a
  (::) : a -> Vect n a -> Vect (S n) a
%name Vect xs,ys,zs

-- * Warmup: Implement some familiar utilities
head : Vect (S n) a -> a

tail : Vect (S n) a -> Vect n a

repeat : (n : Nat) -> a -> Vect n a

-- * Implement Functor, Applicative, and Monad for Vect.
instance Functor (Vect n) where

instance Applicative (Vect n) where

instance Monad (Vect n) where



-- * Define takeWhile for Vect.  takeWhile p xs should return the
-- longest prefix of xs for which p holds. What should the return type
-- be?
takeWhile : (a -> Bool) -> Vect n a -> (m ** Vect m a)-- ?ret

-- * Define an analogous function dropWhile that returns the elements
-- following the longest prefix that satisfies p.
dropWhile : (a -> Bool) -> Vect n a -> (m ** Vect m a)-- ?ret

-- ** Prove that the list versions of takeWhile and dropWhile split the
-- list at the same point
takeDropOk : (p : a -> Bool) -> (xs : List a) -> takeWhile p xs ++ dropWhile p xs = xs

-- * Implement reverse for vectors
-- Hint: use an accumulator, and be prepared to rewrite the Nats
reverseV : Vect n a -> Vect n a


-- List membership
||| Member x xs is a proof that x is contained in xs.
|||
||| It also tells you specifically _where_ x is in xs.
data Member : a -> List a -> Type where
  ||| The element we want is at the head
  ||| @ x The element
  ||| @ xs the tail
  Here  : Member x (x :: xs)
  ||| The element we want is contained in the tail somewhere
  There : Member x xs -> Member x (y :: xs)

-- (*) Show that the empty list has no members
nilIsEmpty : Member x [] -> Void
nilIsEmpty Here impossible
-- impossible states that the pattern doesn't type-check. This
-- distinguishes between not-implemented-yet. We only need one pattern
-- because the system automatically checks the rest.

instance Uninhabited (Member x []) where

-- (*) Use DecEq to construct a proof that an element is present, if possible
findMember : DecEq a => (x : a) -> (xs : List a) -> Maybe $ Member x xs

-- (**) Show that list membership is decidable.
-- Hint: think about the auxiliary lemmas needed in case of "No".
decMember : DecEq a => (x : a) -> (xs : List a) -> Dec $ Member x xs

-- (**) Show that if x is an element of a concatenation, it comes from
-- at least one input list. You may need to explicitly match some patterns.
listElt : (x : a) -> (xs, ys : List a) -> Member x (xs ++ ys) -> Either (Member x xs) (Member x ys)

-- *** Write a program that reads lines of input until the user
-- somehow signals that it should stop. Then, it should read a natural
-- number. If the number is n less than the number of strings read,
-- then the nth string (0-indexed) should be displayed. Otherwise, an
-- error should be displayed. Use the type system to guarantee the
-- relationship between n and the number of strings - the lookup must
-- be statically bounds-checked. Don't bother checking IO actions for
-- totality.
-- Hints: :doc LTE ; :doc LT ; :search LTE m n
-- Feel free to use "cast" to read n
namespace Main
  partial
  main : IO ()
  main = ?main_impl



