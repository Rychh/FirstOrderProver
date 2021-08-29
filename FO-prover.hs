{-# LANGUAGE UnicodeSyntax, TypeSynonymInstances, FlexibleInstances, LambdaCase #-}

module Main where

import Data.List

import System.IO
import System.Random
import System.Timeout

import Text.Printf

import Control.Monad.State

import Test.QuickCheck hiding (Fun, (===))

import Lab2
import Lab4
import Formula
import Parser hiding (one)


-- todo zmien to:

genProps :: [Formula] -> Integer -> [(Formula, Formula)]
genProps [] _ = []
genProps (h:t) k = (h, (Prop (show k))):(genProps t (k+1))

findWithPairs :: Formula -> [(Formula, Formula)] -> Formula
findWithPairs phi ((k, a):t) =
  case k == phi of
    True -> a
    False -> findWithPairs phi t

replaceToProps :: Formula -> [(Formula, Formula)] -> Formula
replaceToProps T _ = T
replaceToProps F _ = F
replaceToProps phi@(Rel _ ts) k = findWithPairs phi k
replaceToProps (Not phi) k = Not (replaceToProps phi k)
replaceToProps (And phi psi) k = And (replaceToProps phi k) (replaceToProps psi k)
replaceToProps (Or phi psi) k = Or (replaceToProps phi k) (replaceToProps psi k)
replaceToProps (Implies phi psi) k = Implies (replaceToProps phi k) (replaceToProps psi k)
replaceToProps (Iff phi psi) k = Iff (replaceToProps phi k) (replaceToProps psi k)
replaceToProps (Exists x phi) k = Exists x (replaceToProps phi k)
replaceToProps (Forall x phi) k = Forall x (replaceToProps phi k)

genPropFormula :: Formula -> Formula
genPropFormula phi = replaceToProps phi (genProps (atomicFormulas phi) 2)



getFunct :: [Term] -> [Term]
getFunct [] = []
getFunct (h:t) =
  case h of
    Var a -> (getFunct t)
    Fun f [] -> (getFunct t)
    Fun f a -> nub $ [(Fun f a)] ++ (getFunct a) ++ (getFunct t)

getFunctions :: Formula -> [Term]
getFunctions T = []
getFunctions F = []
getFunctions (Rel r []) = []
getFunctions (Rel r ts) = getFunct ts
getFunctions (Not phi) = getFunctions phi
getFunctions (And phi psi) = nub $ getFunctions phi ++ getFunctions psi
getFunctions (Or phi psi) = nub $ getFunctions phi ++ getFunctions psi
getFunctions (Implies phi psi) = nub $ getFunctions phi ++ getFunctions psi
getFunctions (Iff phi psi) =nub $ getFunctions phi ++ getFunctions psi
getFunctions (Exists _ phi) =nub $ getFunctions phi
getFunctions (Forall _ phi) = nub $getFunctions phi

r :: [Term] -> Formula -> [Term]
r [] phi = (nub $ getFunctions phi)
r t phi = t ++ (nub $ getFunctions phi)


conjunctGroundInstances :: Formula -> Formula
conjunctGroundInstances = Prelude.foldr And T . ground . removeForall where
  ground phi = groundInstances phi (Prelude.map Var (vars phi) ++ (nub $ r (constants (sig phi)) phi))
prover :: FOProver
prover f =
  let skolemised = skolemise (Not f) in
  let f2 = conjunctGroundInstances skolemised in
  not (sat_DP (genPropFormula f2))


--prover :: Formula -> Bool
--prover phi =
--    let
--        phi' = removeForall $ skolemise $ Not phi
--        grounds = groundInstances phi' (Prelude.map Var (vars phi') ++ (nub $ r (constants (sig phi')) phi'))
----        groundInstances phi' $ if null $ constants (sig phi')
----            then map (\x -> Fun x []) (fv phi')
----            else nub $ constants (sig phi')
--
--        check x = not $ davids_putnam (nub $ concatMap (ecnf . genPropFormula) (nub x)) True
--
--        nextCs x = nub $ concatMap (nub . formula_constants) $ nub x
--        nextGrounds x = nub $ groundInstances phi' $ nub $ nextCs x
--
--        checkNext x =
--            let xx = nextGrounds x
--            in (check x || ((xx /= [] && xx /= x) && checkNext xx) )
--    in check [phi']
--        if null grounds then  else checkNext grounds


main :: IO ()
main = do
    eof <- hIsEOF stdin
    if eof
        then return ()
        else do
                line <- getLine -- read the input
                let phi = parseString line -- call the parser
                let res = prover phi -- call the prover
                if res
                  then putStrLn "1" -- write 1 if the formula is a tautology
                  else putStrLn "0" -- write 0 if the formula is not a tautology
