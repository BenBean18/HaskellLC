{-# OPTIONS_GHC -fno-warn-missing-methods #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}

import Prelude ()

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

-- original:
-- class Substitute name value expression output | name value expression -> output
-- instance Substitute (Symbol x) value (Symbol x) value -- hmm overlapping instances
-- instance Substitute (Symbol x) value (Symbol y) (Symbol y) -- hmm overlapping instances
-- instance (Substitute name value body output) => Substitute name value (Lambda x body) (Lambda x output)
-- instance (Substitute name value expr1 output1, Substitute name value expr2 output2) => Substitute name value (Apply expr1 expr2) (Apply output1 output2)


-- latest progress:
-- class Substitute name value expression output | name value expression -> output
-- instance (SymbolValue s1 s1v, SymbolValue s2 s2v, IsEqual s1v s2v flag, Substitute' s1 value s2 flag output) => Substitute s1 value s2 output
-- -- instance (SymbolValue s1 s1v, SymbolValue s2 s2v, IsEqual s1v s2v, Substitute' s1 value s2 IFalse output) => Substitute s1 value s2 output
-- -- instance (SymbolValue s1 s1v, SymbolValue s2 s2v) => Substitute' s1 value s2 IFalse output

-- class Substitute' name value expression symbolsEqual output | name value expression symbolsEqual -> output
-- instance Substitute' (Symbol x) value (Symbol x) ITrue value
-- instance Substitute' (Symbol x) value (Symbol y) IFalse (Symbol y)
-- instance (Substitute' name value body symEq output) => Substitute' name value (Lambda x body) symEq (Lambda x output)
-- instance (Substitute' name value expr1 symEq output1, Substitute' name value expr2 symEq output2) => Substitute' name value (Apply expr1 expr2) symEq (Apply output1 output2)




-- class Substitute name value expression output | name value expression -> output
-- instance (SymbolValue s1 s1v, SymbolValue s2 s2v, IsEqual s1v s2v) => Substitute' s1 value s2 ITrue output
-- instance (SymbolValue s1 s1v, SymbolValue s2 s2v) => Substitute' s1 value s2 IFalse output
-- -- instance (Substitute' s1 value s2 ITrue output) => Substitute s1 value s2 output

-- class Substitute' name value expression symbolsEqual output | name value expression symbolsEqual -> output
-- instance Substitute' (Symbol x) value (Symbol x) ITrue value
-- instance Substitute' (Symbol x) value (Symbol y) IFalse (Symbol y)
-- instance (Substitute' name value body symEq output) => Substitute' name value (Lambda x body) symEq (Lambda x output)
-- instance (Substitute' name value expr1 symEq output1, Substitute' name value expr2 symEq output2) => Substitute' name value (Apply expr1 expr2) symEq (Apply output1 output2)

-- class Substitute name value expression output | name value expression -> output
-- instance (SymbolValue a x, SymbolValue b x) => Substitute a value b value
-- instance (SymbolValue a x, SymbolValue b y) => Substitute a value b value
-- -- instance Substitute (Symbol x) value (Symbol y) (Symbol y)
-- instance (Substitute name value body output) => Substitute name value (Lambda x body) (Lambda x output)
-- instance (Substitute name value expr1 output1, Substitute name value expr2 output2) => Substitute name value (Apply expr1 expr2) (Apply output1 output2)

-- Substitute (Symbol B) (Lambda var body) 

-- https://wiki.haskell.org/GHC/AdvancedOverlap
class LambdaPredicate expr isLambda | expr -> isLambda
instance LambdaPredicate (Lambda a b) ITrue
instance LambdaPredicate (Apply f x) IFalse
instance LambdaPredicate (Symbol x) IFalse

-- class Reduce expression output | expression -> output
-- instance (Substitute arg expr body output) => Reduce (Apply (Lambda arg body) expr) output
-- instance (LambdaPredicate expr IFalse) => Reduce (Apply expr output) (Apply expr output)

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

-- YAYAYAYAYAYAYAYYAYAYA

-- instance (Substitute arg expr body output) => Reduce (Apply (Lambda arg body) expr) output
-- instance (LambdaPredicate expr IFalse) => Reduce (Apply expr output) (Apply expr output)

-- instance (Reduce f f', Reduce x x') => Reduce (Apply (Apply f x) e2) (Apply (Apply f' x') e2)
-- in normal hs, handling (Apply (Lambda x body) y) would make handling (Apply f g) after not catch the (Lambda x body)
-- But in this wonderful world we get overlapping instances, have to declare explicitly
-- instance Reduce (Lambda a b) (Lambda a b)
-- instance Reduce (Symbol x) (Symbol x)

-- class Reduce expression output | expression -> output

-- class Reduce' expression flag output | expression -> flag output
-- instance (Substitute arg expr body output) => Reduce' (Apply (Lambda arg body) expr) ITrue output
-- instance (LambdaPredicate expr IFalse) => Reduce' (Apply expr output) IFalse (Apply expr output)

-- instance (LambdaPredicate expr flag, Reduce' flag expr output) => Reduce expr output


---------------------------

-- CAUTION does not handle duplicate function names correctly

data X
data T
data F
data A
data B
data N

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