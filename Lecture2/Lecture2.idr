module Lecture2

import Debug.Error


-- AST

data Ty = STRING | INT

%name Ty t,t',t''

data HasType : List Ty -> Ty -> Type where
  Here : HasType (t::ts) t
  There : HasType ts t -> HasType (t'::ts) t

data Expr : List Ty -> Ty -> Type where
  Var : HasType ctxt t -> Expr ctxt t

  CstI : Int -> Expr ctxt INT
  CstS : String -> Expr ctxt STRING

  -- crash at runtime if invalid
  SToI : {default tactics {sourceLocation} loc : SourceLocation} ->
         Expr ctxt STRING -> Expr ctxt INT
  Plus : Expr ctxt INT -> Expr ctxt INT -> Expr ctxt INT
  LessThan : Expr ctxt INT -> Expr ctxt INT -> Expr ctxt INT
  
  IToS : Expr ctxt INT -> Expr ctxt STRING
  Append : Expr ctxt STRING -> Expr ctxt STRING -> Expr ctxt STRING


data Stmt : List Ty -> Type where
  Skip : Stmt ctxt
  Seq : Stmt ctxt -> Stmt ctxt -> Stmt ctxt
  While : Expr ctxt INT -> Stmt ctxt -> Stmt ctxt
  Let : Expr ctxt t -> Stmt (t::ctxt) -> Stmt ctxt
  Print : Expr ctxt STRING -> Stmt ctxt
  Read : HasType ctxt STRING -> Stmt ctxt
  Mutate : HasType ctxt t -> Expr ctxt t -> Stmt ctxt


-- Semantics

Value : Ty -> Type
Value STRING = String
Value INT    = Int

%name Value val

data Store : List Ty -> Type where
  Nil : Store []
  (::) : Value t -> Store ts -> Store (t::ts)

%name Store store

read : HasType ctxt t -> Store ctxt -> Value t
read Here (val :: store) = val
read (There x) (val :: store) = read x store

write : HasType ctxt t -> Value t -> Store ctxt -> Store ctxt
write Here val (_ :: store) = val :: store
write (There x) val (val' :: store) = val' :: write x val store

alloc : Value t -> Store ctxt -> Store (t::ctxt)
alloc = (::)

free : Store (t::ctxt) -> Store ctxt
free (_::store) = store

stringToInt : String -> Either String Int
stringToInt str =
  let i = cast str
  in if i == 0
       then if str == "0"
              then return 0
              else Left $ "Invalid string \"" ++ str ++ "\""
       else return i

covering
eval : Store ctxt -> Expr ctxt t -> Either (SourceLocation, String) (Value t)
eval store (Var x) = pure $ read x store
eval store (CstI x) = pure x
eval store (CstS x) = pure x
eval store (Plus x y) = [| eval store x + eval store y |]
eval store (LessThan x y) =
  map boolToInt [| eval store x < eval store y |]
  where boolToInt : Bool -> Int
        boolToInt b = if b then 1 else 0
eval store (IToS x) = map show $ eval store x
eval store (SToI {loc} x) =
  case stringToInt !(eval store x) of
    Left err => Left (loc, err)
    Right i => Right i
eval store (Append x y) = [| eval store x ++ eval store y |]

evalIO : Store ctxt -> Expr ctxt t -> IO (Value t)
evalIO store expr = case eval store expr of
                      Left (loc, err) => error {loc} err
                      Right val => pure val
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


-- Code generation



-- Concrete syntax

dsl lang
  variable    = id
  index_first = Here
  index_next  = There
  let         = Let


(>>=) : Stmt ctxt -> (() -> Stmt ctxt) -> Stmt ctxt
(>>=) first andThen = Seq first (andThen ())

implicit
convVar : HasType ctxt t -> Expr ctxt t
convVar = Var

implicit
convStr : String -> Expr ctxt STRING
convStr = CstS

fromInteger : Integer -> Expr ctxt INT
fromInteger x = CstI (fromInteger x)

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


foo : Stmt []
foo = lang (do let x = 2
               Print (IToS x)
               While (x < 10) $ do
                 x += 1
                 Print (IToS x)
               Print (CstS "done"))

readInts : Stmt []
readInts = lang (do let x = ""
                    let i = 9999
                    While 1 $ do
                      Print "Enter a number"
                      Read x
                      i := SToI x
                      Print (IToS i))


-- Stuff

namespace Main
  main : IO ()
  main = run [] readInts $> pure ()
  
