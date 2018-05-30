{-# LANGUAGE FlexibleContexts, LambdaCase #-}

module Scheme.Eval where

import Scheme.Core

import Prelude hiding (lookup)
import qualified Data.HashMap.Strict as H (HashMap, insert, lookup, empty, fromList, union)
import Control.Monad.State
import Control.Monad.Except

-- ### Evaluation helpers
-- Discussed and implemented the MP together with ashekar2 and mahshwr3

-- Evaluates a symbol to string
-- Throws an error if value is not a symbol
-- Examples:
--   getSym (Symbol "x")  ==> "x"
--   getSym (Number 1)    ==> Not a symbol: x
getSym :: Val -> EvalState String
getSym (Symbol x) = return x
getSym         v  = throwError $ NotASymbol v

-- `let` and `let*`
getBinding :: Val -> EvalState (String, Val)
getBinding (List [c, e]) = liftM2 (,) (getSym c) (eval e)
getBinding v = throwError $ NotAListOfTwo v

-- Evaluates a list of two to a tuple
-- Throws an error if value is not a list of two
-- This is useful in special form `cond`, since each clause
-- is expected to be exactly a two-element list
-- Examples:
--   getListOf2 (List (Number 1) (Symbol "x"))
--     ==> ((Number 1), (Symbol "x"))
--   getListOf2 (List (Number 1))
--     ==> Not a list of two elements: (1)
getListOf2 :: Val -> EvalState (Val, Val)
getListOf2 (List [c, e]) = return (c, e)
getListOf2 v = throwError $ NotAListOfTwo v

--- ### Keywords

-- When evaluating special forms, a list form starting with a keyword
-- is expected to match the special form syntax.
keywords :: [String]
keywords = [ "define"
           , "lambda"
           , "cond"
           , "let"
           , "let*"
           , "define-macro"
           , "quasiquote"
           , "unquote"
           ]

-- ### The monadic evaluator
-- Unlike evaluators in previous MPs, `eval` does not take any environment!
-- This is because the environment is encapsulated in the `EvalState` monad.
-- To access the environment, all you have to do is `get`, `modify` or `put`!
eval :: Val -> EvalState Val

-- Self-evaluating expressions
-- TODO: What's self-evaluating?
eval v@(Number _) = return v
eval v@(Boolean _) = return v

-- Symbol evaluates to the value bound to it
-- TODO
-- Discussed with Ajay Shekar (ashekar2)
eval (Symbol sym) = do 
                    env <- get
                    case H.lookup sym env of
                      Just a -> return a
                      _ -> throwError (UndefSymbolError sym)

-- Dotted list may just be an equivalent representation of List.
-- We simply try to flatten the list. If it's still dotted after
-- flattening, it's an invalid expression.
eval expr@(DottedList _ _) = case flattenList expr of
  DottedList _ _ -> throwError $ InvalidExpression expr
  v -> eval v

-- List evaluates as a form of the following
-- 1. Special form (`define`, `let`, `let*`, `cond`, `quote`, `quasiquote`,
--    `unquote`, `define-macro`, ...)
-- 2. Macro expansion (Macro)
-- 3. Function application (Func)
-- 4. Primitive function application (PrimFunc)
eval expr@(List lst) = evalList $ map flattenList lst where
    --- Evaluator for forms
    invalidSpecialForm :: String -> EvalState e
    invalidSpecialForm frm = throwError $ InvalidSpecialForm frm expr

    evalList :: [Val] -> EvalState Val

    evalList [] = throwError $ InvalidExpression expr

    -- quote
    -- TODO
    evalList [Symbol "quote", e] = return e

    -- unquote (illegal at surface evaluation)
    -- TODO: since surface-level `unquote` is illegal, all you need to do is
    -- to throw a diagnostic
    evalList [Symbol "unquote", e] = throwError (UnquoteNotInQuasiquote e)

    -- quasiquote
    evalList [Symbol "quasiquote", e] = evalQuasi 1 e where
      evalQuasi :: Int -> Val -> EvalState Val
      evalQuasi 0 (List [Symbol "unquote", v]) = throwError $ UnquoteNotInQuasiquote v
      evalQuasi 1 (List [Symbol "unquote", v]) = eval v
      evalQuasi n (List ee@[Symbol "quasiquote", _]) = List <$> evalQuasi (n+1) `mapM` ee
      evalQuasi n (List ee@[Symbol "unquote", _]) = List <$> evalQuasi (n-1) `mapM` ee
      evalQuasi n (List xx) = List <$> mapM (evalQuasi n) xx
      evalQuasi n (DottedList xx y) = DottedList <$> mapM (evalQuasi n) xx <*> evalQuasi n y
      evalQuasi _ v = return v

    -- Why comment these out? Because `if` can be defined as a macro!
    -- -- if-then
    -- evalList [Symbol "if", condE, thenE] =
    --   eval condE >>= \c -> if lowerBool c then eval thenE else return Void
    -- -- if-then-else
    -- evalList [Symbol "if", condE, thenE, elseE] =
    --   eval condE >>= \c -> eval $ if lowerBool c then thenE else elseE

    -- cond
    -- TODO: Handle `cond` here. Use pattern matching to match the syntax
    evalList ((Symbol "cond"): (x:xs)) = do
                                          (var1, env1) <- getListOf2 x
                                          case (var1) of
                                              Symbol "else" -> case xs of 
                                                                [] -> eval env1
                                                                otherwise -> invalidSpecialForm "cond"
                                              otherwise -> do
                                                          new_cond <- eval var1
                                                          case new_cond of 
                                                            (Boolean False) -> 
                                                              case xs of 
                                                                [] -> return Void
                                                                otherwise -> evalList ((Symbol "cond"):xs)
                                                            otherwise -> eval env1





    -- let
    -- TODO: Handle `let` here. Use pattern matching to match the syntax
    evalList [Symbol "let", List a@(x:xs), body] = do 
                                                    new_val <- mapM (\x -> getBinding x) a
                                                    new_env <- get
                                                    mapM (\(mlo, nlo) -> modify (H.insert mlo nlo)) new_val
                                                    rota <- eval body
                                                    put new_env
                                                    return rota


    -- let*
    -- TODO: Handle `let*` here. Use pattern matching to match the syntax
    evalList [Symbol "let*", List list, body] = do
                                                case list of 
                                                  [] -> do
                                                        evaluated_body <- eval body
                                                        return evaluated_body
                                                  otherwise -> do
                                                              (Symbol new_var, e1) <- getListOf2 (head list)
                                                              new_env <- get
                                                              eval_e1 <- eval e1
                                                              modify (H.insert new_var eval_e1)
                                                              myval <- evalList [Symbol "let*", List (tail list), body]
                                                              put new_env
                                                              return myval

    -- lambda
    -- TODO: Handle `lambda` here. Use pattern matching to match the syntax
    evalList [Symbol "lambda", List args, body] = do
                                                   env<-get
                                                   res <- (\argVal -> Func argVal body env) <$> mapM getSym args
                                                   return res

    -- define function
    evalList [Symbol "define", List (Symbol fname : args), body] = do 
                                                                   env <- get
                                                                   val <- (\argVal -> Func argVal body env) <$> mapM getSym args
                                                                   modify $ H.insert fname val
                                                                   return Void

    -- define variable
    -- TODO: Handle `define` for variables here. Use pattern matching
    -- to match the syntax
    evalList [Symbol "define", Symbol sym, exp] = do 
                                                  myval <- eval exp
                                                  modify $ H.insert sym myval
                                                  return Void

    -- define-macro
    -- TODO: Handle `define-macro` here. Use pattern matching to match
    -- the syntax
    evalList [Symbol "define-macro", List (Symbol fname : args), body] = do 
                                                                          evaluatedVal <- mapM getSym args
                                                                          modify (H.insert fname (Macro evaluatedVal body))
                                                                          return Void

    -- invalid use of keyword, throw a diagnostic
    evalList (Symbol sym : _) | elem sym keywords = invalidSpecialForm sym

    -- application
    evalList (fexpr:args) = eval fexpr >>= aux where
      -- Macro expansion
      -- TODO: implement macro evaluation
      -- Use do-notation!
      aux (Macro wow body) | length wow == length args = do
                                                            justav <- return (zip wow args)
                                                            new_env <- get
                                                            mapM (\(heyo,justav) -> modify (H.insert heyo justav)) justav
                                                            e_body <- eval body
                                                            put new_env
                                                            res <- eval e_body
                                                            return res

      -- Function application
      -- TODO: evaluate arguments, and feed `f` along with the evaluated
      -- arguments to `apply`
      aux f = do 
              evaluatedVal <- mapM (\par -> eval par) args
              res <- (apply f evaluatedVal)
              return (res)

eval val = throwError $ InvalidExpression val

-- Function application
apply :: Val -> [Val] -> EvalState Val
apply (Func wow body cenv) args | length wow == length args = do
                                                                modify (H.union cenv)
                                                                myEnv <- get
                                                                returned <- return (zip wow args)
                                                                mapM (\(a,b) -> modify (H.insert a b)) returned
                                                                new_bod <- eval body
                                                                put myEnv
                                                                return (new_bod)
-- Function
-- TODO: implement function application
-- Use do-notation!
apply (Func fmls body cenv) args | length fmls == length args = unimplemented "`apply` on functions"
-- Primitive
-- TODO: implement primitive function application
-- Since a primitive function has type `[Val] -> EvalState Val`, all you
-- need is to apply it to arguments
apply (PrimFunc p) args = p args
-- Other values are not applicable
-- TODO: you should simply throw a diagnostic
apply f args = throwError (CannotApply f args)
