{-# OPTIONS_GHC -fno-warn-missing-methods #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PartialTypeSignatures #-}

module TypeSystemLC where

import Prelude (undefined)

data Symbol x
data Lambda arg body
data Apply f x

-- Replace (x) (x) y 

data ITrue
data IFalse
data INothing

class SymbolValue symbol value | symbol -> value
instance SymbolValue (Symbol a) a
instance SymbolValue (Lambda a b) INothing
instance SymbolValue (Apply f x) INothing

-- kinda cheating but whatever
type family IsEqual a b where
  IsEqual INothing INothing = IFalse
  IsEqual a a = ITrue
  IsEqual a b = IFalse

class Substitute name value expression output | name value expression -> output
instance (SymbolValue name s1v, SymbolValue expression s2v, Substitute' name value expression (IsEqual s1v s2v) output) => Substitute name value expression output

class Depends a b c d | a b c -> d

class Substitute' name value expression flag output | name value expression flag -> output
instance Substitute' (Symbol x) value (Symbol y) ITrue value
instance Substitute' (Symbol x) value (Symbol y) IFalse (Symbol y)
instance (Substitute name value body output) => Substitute' name value (Lambda x body) IFalse (Lambda x output)
instance (Substitute name value expr1 output1, Substitute name value expr2 output2) => Substitute' name value (Apply expr1 expr2) IFalse (Apply output1 output2)

-- https://wiki.haskell.org/GHC/AdvancedOverlap
class LambdaPredicate expr isLambda | expr -> isLambda
instance LambdaPredicate (Lambda a b) ITrue
instance LambdaPredicate (Apply f x) IFalse
instance LambdaPredicate (Symbol x) IFalse

-- problem is that context isn't considered, this just sees Reduce Apply _ for both.

-- so we use it as an argument instead?? yes!!

-- this does the actual logic
class Reduce' expression isApplyingLambda output | expression isApplyingLambda -> output
-- instance (LambdaPredicate expr1 truth) => Reduce' (Apply expr1 expr2) truth
instance (Substitute arg expr body substituted, Reduce substituted output) => Reduce' (Apply (Lambda arg body) expr) ITrue output
instance Reduce' (Apply expr output) IFalse (Apply expr output)
instance Reduce' (Lambda a b) q (Lambda a b)
instance Reduce' (Symbol x) q (Symbol x)

class Reduce expression output | expression -> output
instance (Reduce expr1 outputExpr1, Reduce expr2 outputExpr2, LambdaPredicate outputExpr1 isLambda, Reduce' (Apply outputExpr1 outputExpr2) isLambda output) => Reduce (Apply expr1 expr2) output
instance (Reduce b outputB, Reduce' (Lambda a outputB) IFalse output) => Reduce (Lambda a b) output
instance (Reduce' (Symbol x) IFalse output) => Reduce (Symbol x) output

---------------------------

-- CAUTION does not handle duplicate function names correctly, need to implement capture-avoiding substitution

data X
data T
data F
data A
data B
data N
data V
data L
data R
data WL
data WB
data C
data H

type Id = Lambda (Symbol X) (Symbol X)
type True = Lambda (Symbol T) (Lambda (Symbol F) (Symbol T))
type False = Lambda (Symbol T) (Lambda (Symbol F) (Symbol F))
-- Not   = (\b.((b False) True));
type Not = Lambda (Symbol B) (Apply (Apply (Symbol B) False) True)
type Succ = Lambda (Symbol N) (Lambda (Symbol F) (Lambda (Symbol B) (Apply (Apply (Symbol N) (Symbol F)) (Apply (Symbol F) (Symbol B)))))
type Zero = Lambda (Symbol F) (Lambda (Symbol X) (Symbol X))
type IsZero = (Lambda (Symbol N) (Apply (Apply (Symbol N) (Lambda (Symbol X) False)) True))
-- type Y = (\f. ((\x.(f (x x))) (\x. (f (x x)))));
type Y = Lambda (Symbol F) (Apply (Lambda (Symbol X) (Apply (Symbol F) (Apply (Symbol X) (Symbol X)))) (Lambda (Symbol X) (Apply (Symbol F) (Apply (Symbol X) (Symbol X)))))

type Leaf = True -- take first argument
type Branch = (Lambda (Symbol V) (Lambda (Symbol L) (Lambda (Symbol R) (Lambda (Symbol WL) (Lambda (Symbol WB) (Apply (Apply (Apply (Symbol WB) (Symbol V)) (Symbol L)) (Symbol R)))))))

type Nil = True
type Cons = (Lambda (Symbol H) (Lambda (Symbol T) (Lambda (Symbol N) (Lambda (Symbol C) (Apply (Apply (Symbol C) (Symbol H)) (Symbol T))))))

type Head = (Lambda (Symbol L) (Apply (Apply (Symbol L) False) True)) -- If nil, return false, otherwise take the head aka first argument (True)
type Tail = (Lambda (Symbol L) (Apply (Apply (Symbol L) False) False)) -- If nil, return False, otherwise take the tail aka second argument (False)

-- Evaluate (\x.x) y = 

class TestApplyId x | -> x
    where idResult :: x
instance (Reduce (Apply Id (Symbol Y)) output) => TestApplyId output

class TestNotTrue x | -> x
    where notResult :: x
instance (Reduce (Apply Not True) output) => TestNotTrue output

class TestTrue' x | -> x
    where trueResult' :: x
instance (Reduce True output) => TestTrue' output

class TestTrue x | -> x
    where trueResult :: x
instance (Reduce (Apply True (Symbol A)) output) => TestTrue output

class TestTrue2 x | -> x
    where trueResult2 :: x
instance (Reduce (Apply (Lambda (Symbol F) (Symbol A)) (Symbol B)) output) => TestTrue2 output

class TestSucc x | -> x
    where succResult :: x
instance (Reduce (Apply Succ (Apply Succ Zero)) output) => TestSucc output

class TestZero x | -> x
    where zeroResult :: x
instance (Reduce (Apply IsZero Zero) output) => TestZero output

-- ok. logical functions don't work yet i think the F and T are causing name conflicts or something?
-- but i can take the successor of numbers!!

class TestLogic x | -> x
    where logicResult :: x
instance (Reduce (Apply (Apply True False) False) output) => TestLogic output

class One x | -> x
    where one :: x
instance (Reduce (Apply Succ Zero) output) => One output

class Two x | -> x
    where two :: x
instance (One aOne, Reduce (Apply Succ aOne) output) => Two output

class Three x | -> x
    where three :: x
instance (Two aTwo, Reduce (Apply Succ aTwo) output) => Three output

class ReduceY x | -> x
    where reduceY :: x
instance (Reduce Y output) => ReduceY output

class OneTwoThree x | -> x
    where oneTwoThree :: x
instance (One aOne, Two aTwo, Three aThree, Reduce (Apply (Apply Cons aOne) (Apply (Apply Cons aTwo) Nil){-(Apply (Apply Cons aTwo) (Apply (Apply Cons aThree) Nil))-}) output) => OneTwoThree output

class HeadOfList l x | l -> x
    where listHead :: l -> x
instance (Reduce (Apply Head l) output) => HeadOfList l output

-- value :: (Reduce (Apply IsZero (Apply Succ Zero)) a) => _
-- value = ()