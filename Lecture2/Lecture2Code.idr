module Lecture2Code

import Control.Monad.Identity
import Control.Monad.State
import Debug.Error
import Language.Reflection
import Language.Reflection.Errors


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
namespace SExpr
  data SExpr = Symbol String
             | Nil
             | (::) SExpr SExpr
             | SStr String
             | SInt Int

  toList : SExpr -> Maybe $ List SExpr
  toList [] = Just []
  toList (a :: b) = map (a ::) (toList b)
  toList _ = Nothing

  fromList : List SExpr -> SExpr
  fromList xs = foldr (::) Nil xs

  instance Show SExpr where
    show (Symbol x) = x
    show [] = "nil"
    show cons@(x :: y) =
      case toList cons of
        Just elts => "(" ++ foldr (++) "" (intersperse " " (map show elts)) ++ ")"
        Nothing => "(" ++ show x ++ " . " ++ show y ++ ")"
    show (SStr x) = show x
    show (SInt x) = show x

  fresh : State Int String
  fresh = do i <- get
             put (i + the Int 1)
             return $ ("v" ++ show i)

  namespace Names
    data Names : List Ty -> Type where
      Nil : Names []
      (::) : String -> Names ctxt -> Names (t :: ctxt)

    getName : Names ctxt -> HasType ctxt t -> String
    getName (n :: _)  Here = n
    getName (_ :: ns) (There i) = getName ns i

    newName : Names ctxt -> State Int (Names $ t :: ctxt)
    newName ns = [| fresh :: pure ns |]

  genExpr : Names ctxt -> Expr ctxt t -> State Int SExpr
  genExpr ns (Var x) = return . Symbol $ getName ns x
  genExpr ns (CstI x) = return (SInt x)
  genExpr ns (CstS x) = return (SStr x)
  genExpr ns (SToI x) = return $ fromList [Symbol "string-to-number", !(genExpr ns x)]
  genExpr ns (Plus x y) = return $ fromList [Symbol "+", !(genExpr ns x), !(genExpr ns y)]
  genExpr ns (LessThan x y) = return [Symbol "<", !(genExpr ns x), !(genExpr ns y)]
  genExpr ns (IToS x) = return [Symbol "number-to-string", !(genExpr ns x)]
  genExpr ns (Append x y) = return [Symbol "concat", !(genExpr ns x), !(genExpr ns y)]

  inSeq : Stmt ctxt -> List (Stmt ctxt)
  inSeq (Seq x y) = inSeq x ++ inSeq y
  inSeq stmt = [stmt]

  getStmt : Names ctxt -> Stmt ctxt -> State Int SExpr
  getStmt ns Skip = return Nil
  getStmt ns s@(Seq y z) = do body <- map fromList $ traverse (getStmt ns) (inSeq s)
                              return (Symbol "progn" :: body)
  getStmt ns (While y z) = return [Symbol "while", !(genExpr ns y), !(getStmt ns z)]
  getStmt ns (Let y z) =
    do n <- fresh
       return [Symbol "let",
                [[Symbol n, !(genExpr ns y)]],
                !(getStmt (n::ns) z)]
  getStmt ns (Print y) = return [Symbol "message", !(genExpr ns y)]
  getStmt ns (Read y) = return [Symbol "setq", Symbol (getName ns y),
                                [Symbol "read-string", SStr "> "]]
  getStmt ns (Mutate y z) = return [Symbol "setq", Symbol (getName ns y), !(genExpr ns z)]


  compile : Stmt [] -> SExpr
  compile prog = runIdentity . map fst $ runStateT (getStmt [] prog) 0


-- Concrete syntax

dsl lang
  variable    = id
  index_first = Here
  index_next  = There
  let         = Let


(>>=) : Stmt ctxt -> (() -> Stmt ctxt) -> Stmt ctxt
(>>=) first andThen = Seq first (andThen ())

implicit
convVar : (ix : HasType ctxt t) -> Expr ctxt t
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

Program : Type
Program = Stmt []

foo : Program
foo = lang (do let x = 2
               Print (IToS x)
               While (x < 10) $ do
                 x += 1
                 Print (IToS x)
               Print (CstS "done"))

readInts : Program
readInts = lang (do let x = ""
                    let i = 9999
                    While 1 $ do
                      Print "Enter a number"
                      Read x
                      i := SToI x
                      Print (IToS i))

%language ErrorReflection

betterVarErrors : Err -> Maybe (List ErrorReportPart)
betterVarErrors (CantUnify _ tm `(HasType (List.(::) ~t ~_) ~found) err _ _) =
  Just [ TextPart "Expected a variable with type", TermPart t
       , TextPart "but got a variable with type ", TermPart found
       ]
betterVarErrors _ = Nothing

%error_handlers convVar ix betterVarErrors

borken : Program
borken = lang (do let x = ""
                  let i = 9999
                  While 1 $ do
                    Print "Enter a number"
                    Read x
                    i := x
                    Print (IToS i))


-- Stuff

namespace Main
  main : IO ()
  main = run [] readInts $> pure ()

