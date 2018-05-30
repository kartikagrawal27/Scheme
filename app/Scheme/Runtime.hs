{-# LANGUAGE FlexibleContexts #-}

module Scheme.Runtime where

import Scheme.Core
import Scheme.Parse
import Scheme.Eval

import qualified Data.HashMap.Strict as H
import Text.ParserCombinators.Parsec hiding (Parser, State)
import Control.Monad
import Control.Monad.State
import Control.Monad.Except
import Data.Foldable

-- Discussed and implemented the MP together with ashekar2 and mahshwr3

--- ### Helper functions for lifting and lowering

lowerBool :: Val -> Bool
lowerBool (Boolean False) = False
lowerBool _ = True

lowerInt :: Val -> EvalState Int
lowerInt (Number i) = return i
lowerInt v = throwError $ TypeError v

lowerList :: Val -> EvalState [Val]
lowerList (List xx) = return xx
lowerList v = throwError $ TypeError v

liftIntVargOp :: (Int -> Int -> Int) -> Int -> Val
liftIntVargOp f c = PrimFunc p where
  p [] = return $ Number c
  p [x] = Number . f c <$> lowerInt x
  p xx = Number . foldl1 f <$> mapM lowerInt xx

liftBoolVargOp :: ([Bool] -> Bool) -> Val
liftBoolVargOp f = PrimFunc $ return . Boolean . f . map lowerBool

-- TODO
liftIntBinOp :: (Int -> Int -> Int) -> Val
liftIntBinOp f = PrimFunc p where
  p [(Number num1), (Number num2)] = return (Number (f num1 num2))
  p val = throwError (UnexpectedArgs val)

-- TODO
liftIntUnaryOp :: (Int -> Int) -> Val
liftIntUnaryOp f = PrimFunc p where
  p [Number num1] = return (Number (f num1))
  p v = throwError (UnexpectedArgs v)

liftBoolUnaryOp :: (Bool -> Bool) -> Val
liftBoolUnaryOp f = PrimFunc p where
  p [Boolean x] = return $ Boolean $ f x
  p [a] = return $ Boolean $ f True
  p v = throwError $ UnexpectedArgs v

-- TODO
liftCompOp :: (Int -> Int -> Bool) -> Val
liftCompOp f = PrimFunc p where
  p [] = return (Boolean True)
  p [Number x] = return (Boolean True)
  p (Number num1:Number num2:xs) = 
    if (f num1 num2) == True then
      p (Number num2:xs)
    else
      return (Boolean False)
  p v = throwError (UnexpectedArgs v)

--- ### Primtive operations

-- Primitive function `car`
-- TODO
car :: [Val] -> EvalState Val
car [List (x:xs)] = return x
car [DottedList (x:xs) num2] = return x
car num1 = throwError (UnexpectedArgs num1)

-- Primitive function `cdr`
-- TODO
cdr :: [Val] -> EvalState Val
cdr [List (x:xs)] = return (List xs)
cdr [DottedList (x:xs) num2] = return (DottedList xs num2)
cdr [DottedList [num1] num2] = return num2
cdr num1 = throwError (UnexpectedArgs num1)

-- Primitive function `cons`
-- TODO
cons :: [Val] -> EvalState Val
cons [num1, num2] = return (DottedList [num1] num2)
cons num1 = throwError (UnexpectedArgs num1)

list :: [Val] -> EvalState Val
list l = return (List l)

-- Primitive function `append`
append :: [Val] -> EvalState Val
append [] = return $ List []
append [x] = return x
append vv = foldlM append' (List []) (map flattenList vv) where
  append' (List []) x = return x
  append' (List xs) (List ys) = return $ List (xs ++ ys)
  append' (List xs) (DottedList ys y) = return $ DottedList (xs ++ ys) y
  append' _ acc = throwError $ TypeError acc

-- Primitive function `apply`
-- It applies a function to a list of parameters
-- TODO
-- Examples:
--   (apply + '(1 2 3))  => 6
--   (apply car '((1 2 3)))  => 1
applyPrim :: [Val] -> EvalState Val
applyPrim [func, List list] = apply func list
applyPrim error = throwError (UnexpectedArgs error)

-- Primitive function `eval`
-- It evaluates the single argument as an expression
-- All you have to do is to check the number of arguments and
-- feed the single argument to the evaluator!
-- TODO
-- Examples:
--   (eval '(+ 1 2 3))  => 6
evalPrim :: [Val] -> EvalState Val
evalPrim [x] = eval x
evalPrim vv = throwError $ UnexpectedArgs vv

-- Primitive function `=`, throwing type error for mismatch
-- `=` is a comparison operator for numbers and booleans
-- TODO
-- Examples:
--   (= 1 1) => #t
--   (= #f #t) => #f
--   (= #f #f) => #t
--   (= 'a 10) => Type error
--   (= 'a 'b) => Type error
equalSign :: [Val] -> EvalState Val
equalSign = const $ unimplemented "Primitive function `=`"

-- Primitive function `eq?`, not throwing any error
-- `eq?` is a comparison operator for atom values (numbers, booleans, and symbols)
-- Returns `#f` on type mismatch or unsupported types (functions etc)
-- TODO
-- Examples:
--   (eq? 1 1) => #t
--   (eq? #f #t) => #f
--   (eq? #f #f) => #t
--   (eq? 'a 10) => #f
--   (eq? 'a 'a) => #t
eq :: [Val] -> EvalState Val
eq = const $ unimplemented "Primitive function `eq?`"

-- Primitive function `list?` predicate
-- `(list? arg)` determines whether `arg` is a non-dotted list
-- or an empty list (null)
-- TODO
isList :: [Val] -> EvalState Val
isList [val] = return . Boolean $ case flattenList val of
                                  List _ -> True
                                  _ -> False
isList otherwise = throwError $ UnexpectedArgs otherwise

-- Primitive function `symbol?` predicate
-- TODO
isSymbol :: [Val] -> EvalState Val
isSymbol [Symbol _] = return (Boolean True)
isSymbol [_] = return (Boolean False)
isSymbol otherwise = throwError (UnexpectedArgs otherwise)

-- Primitive function `pair?` predicate
-- Any `List` or `DottedList` is a pair
-- TODO
isPair :: [Val] -> EvalState Val
isPair [List []] = return (Boolean False)
isPair [ls] = case flattenList ls of 
              (DottedList _ _) -> return $ Boolean True
              (List (x:xs)) -> return $ Boolean True
              (List []) -> return $ Boolean False
              a -> return $ Boolean False
isPair haha = throwError (UnexpectedArgs haha)

-- Primitive function `number?` predicate
-- TODO
isNumber :: [Val] -> EvalState Val
isNumber [Number _] = return (Boolean True)
isNumber [_] = return (Boolean False)
isNumber otherwise = throwError (UnexpectedArgs otherwise)

-- Primitive function `boolean?` predicate
-- TODO
isBoolean :: [Val] -> EvalState Val
isBoolean [Boolean _] = return (Boolean True)
isBoolean [_] = return (Boolean False)
isBoolean otherwise = throwError (UnexpectedArgs otherwise)

-- Primitive function `null?` predicate
-- An empty list or its *equivalent* value is null
-- Note: Think about what's equivalent
-- TODO
isNull :: [Val] -> EvalState Val
isNull [List []] = return (Boolean True)
isNull [l] = case (flattenList l) of 
            (List []) -> return (Boolean True)
            (List [_]) -> return (Boolean False)
            a -> return (Boolean False)
isNull otherwise = throwError (UnexpectedArgs otherwise)


-- isNull [(List [])] = return $ Boolean True
-- isNull [_] = return $ Boolean False
-- isNull vv = throwError $ UnexpectedArgs vv


--- ### Runtime

runtime = H.fromList [ ("+", liftIntVargOp (+) 0)
                     , ("modulo", liftIntBinOp (mod))
                     , ("cons", PrimFunc cons)
                     , ("car", PrimFunc car)
                     , ("cdr", PrimFunc cdr)
                     , ("list", PrimFunc list)
                     , ("append", PrimFunc append)
                     , ("abs", liftIntUnaryOp (abs))
                     , ("symbol?", PrimFunc isSymbol)
                     , ("list?", PrimFunc isList)
                     , ("=", PrimFunc equalSign)
                     , ("number?", PrimFunc isNumber)
                     , ("boolean?", PrimFunc isBoolean)
                     , ("null?", PrimFunc isNull)
                     , ("apply", PrimFunc applyPrim)
                     , ("-", liftIntVargOp (-) 0)
                     , ("*", liftIntVargOp (*) 1)
                     , ("/", liftIntVargOp (div) 1)
                     , ("and", liftBoolVargOp and)
                     , ("or", liftBoolVargOp or)
                     , ("eq?", PrimFunc eq)
                     , (">", liftCompOp (>))
                     , ("<", liftCompOp (<))
                     , (">=", liftCompOp (>=))
                     , ("<=", liftCompOp (<=))
                     , ("not", liftBoolUnaryOp (not))
                     , ("eval", PrimFunc evalPrim)
                     , ("pair?", PrimFunc isPair)
                     ]
