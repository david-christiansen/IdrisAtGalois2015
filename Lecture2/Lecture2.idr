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
-- * Extended Example
-- * Domain-specific error messages
-- * Access to source locations



-- # de Bruijn Indices: A Refresher

-- de Bruijn indices count binders outwards from variables, as an
-- alternative to string names.

-- [[[(image :type imagemagick :file "deBruijn.png" :max-width 0.8 :max-height 0.6)]]]


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
  ||| A proof that j < k
  data Less : (j, k : Nat) -> Type where
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

-- # A Typed Imperative Language

-- In the rest of the lecture, we embed a simple imperative language
-- in Idris, making it as convenient as possible.


-- # Types, Contexts, and Variables

||| DSL types
data Ty = STRING | INT

%name Ty t,t',t''

||| Well-typed de Bruijn indices, to be used as lvalues
||| @ ctxt the typing context, with recent variables on the left
||| @ t the type at the index pointed to
data HasType : (ctxt : List Ty) -> (t : Ty) -> Type where
  ||| Zero: the type is the first element of the context
  Here : HasType (t::ts) t
  ||| Successor: the type is in the tail of the context
  There : HasType ts t -> HasType (t'::ts) t


-- # Expressions

data Expr : (ctxt : List Ty) -> (t : Ty) -> Type where
  Var : HasType ctxt t -> Expr ctxt t

  CstI : Int -> Expr ctxt INT
  CstS : String -> Expr ctxt STRING

  -- SToI should crash at runtime if the string is invalid
  SToI : Expr ctxt STRING -> Expr ctxt INT
  Plus : Expr ctxt INT -> Expr ctxt INT -> Expr ctxt INT
  LessThan : Expr ctxt INT -> Expr ctxt INT -> Expr ctxt INT

  IToS : Expr ctxt INT -> Expr ctxt STRING
  Append : Expr ctxt STRING -> Expr ctxt STRING -> Expr ctxt STRING



-- # Statements

data Stmt : List Ty -> Type where
  Skip : Stmt ctxt
  Seq : Stmt ctxt -> Stmt ctxt -> Stmt ctxt
  While : Expr ctxt INT -> Stmt ctxt -> Stmt ctxt

  ||| Introduce and initialize a variable
  Let : Expr ctxt t -> Stmt (t::ctxt) -> Stmt ctxt

  Print : Expr ctxt STRING -> Stmt ctxt

  Read : HasType ctxt STRING -> Stmt ctxt
  Mutate : HasType ctxt t -> Expr ctxt t -> Stmt ctxt



-- # An Interpreter
-- ## Memory

||| Use Idris values to represent DSL values. DSL types _code for_
||| Idris types.
Value : Ty -> Type
Value STRING = String
Value INT    = Int

%name Value val

||| In-memory storage for typed variables.
data Store : List Ty -> Type where
  Nil : Store []
  (::) : Value t -> Store ts -> Store (t :: ts)

%name Store store


-- # An Interpreter
-- ## Interacting with Memory

read : HasType ctxt t -> Store ctxt -> Value t
read Here      (val :: store) = val
read (There x) (val :: store) = read x store

write : HasType ctxt t -> Value t -> Store ctxt -> Store ctxt
write Here      val (_    :: store) = val :: store
write (There x) val (val' :: store) = val' :: write x val store

alloc : Value t -> Store ctxt -> Store (t::ctxt)
alloc = (::)

free : Store (t::ctxt) -> Store ctxt
free (_::store) = store

-- {hide}
-- this is not interesting for the talk but is needed in the code
stringToInt : String -> Either String Int
stringToInt str =
  let i = cast str
  in if i == 0
       then if str == "0"
              then return 0
              else Left $ "Invalid string \"" ++ str ++ "\""
       else return i
-- {show}


-- # An Interpreter
-- ## Evaluating Expressions

covering
eval : Store ctxt -> Expr ctxt t -> Either String (Value t)
eval store (Var x) = pure $ read x store
eval store (CstI x) = pure x
eval store (CstS x) = pure x
eval store (Plus x y) = [| eval store x + eval store y |]
eval store (LessThan x y) =
  map boolToInt [| eval store x < eval store y |]
  where boolToInt : Bool -> Int
        boolToInt b = if b then 1 else 0
eval store (IToS x) = map show $ eval store x
eval store (SToI x) =
  case stringToInt !(eval store x) of
    Left err => Left err
    Right i => Right i
eval store (Append x y) = [| eval store x ++ eval store y |]


-- # An Interpreter
-- ## Crashing on errors

evalIO : Store ctxt -> Expr ctxt t -> IO (Value t)
evalIO store expr = case eval store expr of
                      Left err  => error err
                      Right val => pure val

-- # An Interpreter
-- ## Execution of Statements

covering
run : Store ctxt -> Stmt ctxt -> IO (Store ctxt)
run store Skip = return store
run store (Seq x y) =
  do store' <- run store x
     run store' y
run store loop@(While c body) =
  do cond <- evalIO store c
     if cond == 0
       then return store
       else do store' <- run store body
               run store' loop
run store (Let expr body) =
  do let store' = alloc !(evalIO store expr) store
     store'' <- run store' body
     return (free store'')
run store (Print x) = do putStrLn !(evalIO store x)
                         return store
run store (Read addr) = do l <- map trim getLine
                           return (write addr l store)
run store (Mutate x e) = return (write x !(evalIO store e) store)


-- # Example Program

countUp : Stmt []
countUp =
  Let (CstI 2) $
    Seq (Print (IToS (Var Here)))
        (Seq (While (LessThan (Var Here) (CstI 10))
                    (Seq (Mutate Here
                                 (Plus (Var Here)
                                       (CstI 1)))
                         (Print (IToS (Var Here)))))
             (Print (CstS "done")))



-- # Concrete Syntax

-- This language will provide only let bindings.


-- Variables are not wrapped in a constructor. This is to allow them
-- to be used as lvalues in statements like Mutate and Read.

dsl lang
  variable    = id
  index_first = Here
  index_next  = There
  let         = Let

||| Convert raw lvalues into variable expressions as needed
implicit
convVar : (ix : HasType ctxt t) -> Expr ctxt t
convVar = Var


-- # Concrete Syntax

-- We can now write more readable bindings

countUpBetter : Stmt []
countUpBetter =
  lang (let x = CstI 2 in
        Seq (Print (IToS x))
            (Seq (While (LessThan x (CstI 10))
                        (Seq (Mutate x
                                     (Plus x (CstI 1)))
                             (Print (IToS x))))
                 (Print (CstS "done"))))


-- # Concrete Syntax

-- We can allow string and integer literals with an implicit coercion
-- and a fromInteger implementation, respectively

implicit
convStr : String -> Expr ctxt STRING
convStr = CstS

fromInteger : Integer -> Expr ctxt INT
fromInteger x = CstI (fromInteger x)


-- # Concrete Syntax
-- ## Handy infix operators

infix 1 :=
(:=) : HasType ctxt t -> Expr ctxt t -> Stmt ctxt
(:=) = Mutate

(<) : Expr ctxt INT -> Expr ctxt INT -> Expr ctxt INT
(<) = LessThan

(+) : Expr ctxt INT -> Expr ctxt INT -> Expr ctxt INT
(+) = Plus

infix 1 +=
(+=) : HasType ctxt INT -> Expr ctxt INT -> Stmt ctxt
x += i = x := x + i


-- # Concrete Syntax
-- ## Now with operators and literals

countUpYetBetter : Stmt []
countUpYetBetter =
  lang (let x = 2 in
        Seq (Print (IToS x))
            (Seq (While (x < 10)
                        (Seq (x += 1)
                             (Print (IToS x))))
                 (Print "done")))


-- # Concrete Syntax
-- ## do-Notation

-- Like Scala's for comprehesions, Idris's do-notation is rewritten
-- purely syntactically, and types are used to disambguate overloaded
-- names.

(>>=) : Stmt ctxt -> (() -> Stmt ctxt) -> Stmt ctxt
(>>=) first andThen = Seq first (andThen ())

countUpGreat : Stmt []
countUpGreat =
  lang (do let x = 2
           Print (IToS x)
           While (x < 10) $ do
             x += 1
             Print (IToS x)
           Print "done")


-- # Reflect on your Mistakes!
-- ## Domain-Specific Language, General-Purpose Errors

{-
borken : Stmt []
borken = lang (do let x = ""
                  let i = 9999
                  While 1 $ do
                    Print "Enter a number"
                    Read x
                    i := x
                    Print (IToS i))
-}


-- # Reflect on your Mistakes!
-- ## Rewriting Errors

%language ErrorReflection

betterVarErrors : Err -> Maybe (List ErrorReportPart)
betterVarErrors (CantUnify _ tm `(HasType (List.(::) ~t ~_) ~found) err _ _) =
  Just [ TextPart "Expected a variable with type", TermPart t
       , TextPart "but got a variable with type ", TermPart found
       ]
betterVarErrors _ = Nothing

-- %error_handlers convVar ix betterVarErrors


-- # Reflect on your Mistakes!
-- ## Domain-Specific Language, Domain-Specific Errors

{-
borken : Stmt []
borken = lang (do let x = ""
                  let i = 9999
                  While 1 $ do
                    Print "Enter a number"
                    Read x
                    i := x
                    Print (IToS i))
-}


-- # Source Locations

-- SourceLocation represents points or spans in code.

-- {{{Examine definition|||idris-talk-show-loc}}}

-- We can ask the compiler to provide it as an implicit argument.

-- {{{View example|||idris-talk-find-code-file}}}



-- # Next Week

-- * Compiler overview
-- * Interactive proving and tactic scripts
-- * Syntax extensions
-- * The effects library


-- {hide}
-- Local Variables:
-- eval: (require 'custom)
-- eval: (eldoc-mode -1)
-- eval: (make-variable-buffer-local 'idris-metavariable-show-on-load)
-- eval: (setq idris-metavariable-show-on-load nil)
-- eval: (defun idris-talk-show-less (_b) (interactive) (idris-info-for-name :print-definition "Less"))
-- eval: (defun idris-talk-show-const2 (_b) (interactive) (idris-info-for-name :print-definition "const2'"))
-- eval: (defun idris-talk-show-loc (_b) (interactive) (idris-info-for-name :print-definition "SourceLocation"))
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
-- End:
-- {show}
 
 
