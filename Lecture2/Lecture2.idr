-- {hide}
-- These slides are intended to be used with live-code-talks-mode for Emacs.
-- {show}


-- # Dependently Typed Programming in Idris



-- ## David Raymond Christiansen


-- ### Session 2: Embedded DSLs
-- ### January 20, 2015



-- [[[(image :type imagemagick :file "galois.png" :width 300)]]]

-- {hide}
module Main

import Debug.Error
import Language.Reflection
import Language.Reflection.Errors
import Language.Reflection.Utils
-- {show}


-- # Agenda

-- * Representing variables
-- * Overloading binders (DSL blocks)
-- * Closed universes
-- * Domain-specific error messages
-- * Access to source locations


-- # de Bruijn Indices: A Refresher

-- de Bruijn indices count binders outwards from variables, as an
-- alternative to string names.

-- Named term: λx.λy.x y

-- de Bruijn indices: λ.λ.1 0


-- # Names vs. de Bruijn Indices

-- ## Explicit Names
-- * Resemble surface syntax
-- * Easy to read and write
-- * Difficult to connect to typing contexts
-- * α-equivalence is non-trivial

-- ## de Bruijn Indices
-- * Distant from surface syntax
-- * Difficult to read and write
-- * Easy to connect to typing contexts (list lookup)
-- * α-equivalence is syntactic equality
--   (extra important in dependent types)


-- # Terms indexed by free variables

namespace FreeVars
  data Less : Nat -> Nat -> Type where
    ZeroLess : Less Z (S k)
    SuccLess : Less j k -> Less (S j) (S k)

  data Term1 : Nat -> Type where
    App1 : Term1 n -> Term1 n -> Term1 n
    Lam1 : Term1 (S n) -> Term1 n
    Var1 : (ix : Nat) -> Less ix n -> Term1 n

  const1 : Term1 0
  const1 = Lam1 (Lam1 (Var1 (S Z) (SuccLess ZeroLess)))


-- # Automate the Proof

-- The proof that j < k uniquely determines j!
-- {{{Examine definition|||idris-talk-show-less}}}

  const1' : Term1 0
  const1' = Lam1 (Lam1 (Var1 _ (SuccLess ZeroLess)))

  data Term2 : Nat -> Type where
    App2 : Term2 n -> Term2 n -> Term2 n
    Lam2 : Term2 (S n) -> Term2 n
    Var2 : {ix : Nat} -> Less ix n -> Term2 n

  const2 : Term2 0
  const2 = Lam2 (Lam2 (Var2 (SuccLess ZeroLess)))


-- # Terrible for Programming!

-- ## DSL blocks let you write with names,
-- ## but get de Bruijn-indexed terms.

  dsl term2
    variable = Var2
    index_first = ZeroLess
    index_next = SuccLess
    lambda = Lam2

  -- You can also override let, dependent functions, and other binders.

  const2' : Term2 0
  const2' = term2 (\f, x => f `App2` x)
  -- {{{Examine definition|||idris-talk-show-const2}}}

-- # A Well-Typed Interpreter

-- Term1 and Term2 guarantee scope safety, but not type safety.
-- Let's replace our free variable count with a list of their types.
-- Our interpreter can then map our terms to their Idris equivalents.

-- ## Types

-- We must restrict terms to the types we support. Elements of Ty are
-- codes for types, that we can map to Idris types. This is a closed
-- universe.

data Ty = INT | ARR Ty Ty

%name Ty t,t',t''

interp : Ty -> Type
interp INT        = Int
interp (ARR t t') = interp t -> interp t'


-- # Typing contexts

-- A context becomes a list of Ty, and a variable selects an element.
-- It combines the Nat and the Less from before, with added types.
data Index : List Ty -> Ty -> Type where
  Here : Index (t :: ts) t
  There : Index ts t -> Index (t'::ts) t

%name Index ix

exampleIx : Index [INT, ARR INT INT, ARR INT (ARR INT INT)] (ARR INT INT)
exampleIx = There Here


-- # Terms

||| Well-typed terms.
||| @ ctxt the context in which the term is well-typed\
||| @ t the type of the term in `ctxt`
data Term : (ctxt : List Ty) -> (t : Ty) -> Type where
  CstI : (i : Int) -> Term ctxt INT
  Plus : (x, y : Term ctxt INT) -> Term ctxt INT
  App : (f : Term ctxt (ARR t t')) ->
        (x : Term ctxt t) ->
        Term ctxt t'
  Lam : (body : Term (t::ctxt) t') ->
        Term ctxt (ARR t t')
  Var : Index ctxt t -> Term ctxt t

%name Term tm,tm',tm''


-- # The Interpreter
-- ## Run-time environments
||| Run-time environments contain the right type of value for each
||| variable in `ctxt`
data Env : (ctxt : List Ty) -> Type where
  Nil : Env []
  (::) : interp t -> Env ctxt -> Env (t :: ctxt)

%name Env env

lookup : Env ctxt -> Index ctxt t -> interp t
lookup (x :: env) Here       = x
lookup (x :: env) (There ix) = lookup env ix


-- # The Interpreter

eval : Env ctxt -> Term ctxt t -> interp t
eval env (CstI x) = x
eval env (Plus tm tm') = eval env tm + eval env tm'
eval env (App tm tm') = eval env tm $ eval env tm'
eval env (Lam tm) = \x => eval (x::env) tm
eval env (Var ix) = lookup env ix

answer : Int
answer =
  eval [] $
    Plus (App (Lam (Plus (Var Here) (Var Here))) (CstI 20))
         (CstI 2)

doubler : Int -> Int
doubler = eval [] $ Lam (Plus (Var Here) (Var Here))


-- # Domain-Specific Error Messages

%language ErrorReflection

intNotFun : Term [] INT
--intNotFun = App (CstI 2) (CstI 23)

funMustBeArr : Err -> Maybe (List ErrorReportPart)
funMustBeArr (CantUnify _ `(Term ~_ ~t) `(Term ~_ (ARR ~t' ~t'')) _ _ _) =
  Just [ TermPart t
       , TextPart "is not a function type"
       , TermPart t', TextPart "->", TermPart t''
       , TextPart "and therefore cannot be applied."
       ]

funMustBeArr _ = Nothing

%error_handlers Main.App f funMustBeArr

intStillNotFun : Term [] INT
--intStillNotFun = App (CstI 2) (CstI 23)


-- # Source locations






-- {hide}
-- Local Variables:
-- eval: (require 'custom)
-- eval: (eldoc-mode -1)
-- eval: (make-variable-buffer-local 'idris-metavariable-show-on-load)
-- eval: (setq idris-metavariable-show-on-load nil)
-- eval: (defun idris-talk-show-less (_b) (interactive) (idris-info-for-name :print-definition "Less"))
-- eval: (defun idris-talk-show-const2 (_b) (interactive) (idris-info-for-name :print-definition "const2'"))
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
 
 
