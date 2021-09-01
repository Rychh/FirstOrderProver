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


generateProps :: [Formula] -> Integer -> [(Formula, Formula)]
generateProps [] _ = []
generateProps (h:t) k = (h, (Prop (show k))):(generateProps t (k+1))

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

generatePropsFormula :: Formula -> Formula
generatePropsFormula phi = replaceToProps phi (generateProps (atomicFormulas phi) 2)

functionsFromTerns :: [Term] -> [Term]
functionsFromTerns [] = []
functionsFromTerns (h:t) =
  case h of
    Var a -> (functionsFromTerns t)
    Fun f [] -> (functionsFromTerns t)
    Fun f a -> nub $ [(Fun f a)] ++ ( nub $ functionsFromTerns a) ++ ( nub $ functionsFromTerns t)

functionsFromFormula :: Formula -> [Term]
functionsFromFormula T = []
functionsFromFormula F = []
functionsFromFormula (Rel r []) = []
functionsFromFormula (Rel r ts) = nub $ functionsFromTerns ts
functionsFromFormula (Not phi) = functionsFromFormula phi
functionsFromFormula (And phi psi) = nub $ functionsFromFormula phi ++ functionsFromFormula psi
functionsFromFormula (Or phi psi) = nub $ functionsFromFormula phi ++ functionsFromFormula psi
functionsFromFormula (Implies phi psi) = nub $ functionsFromFormula phi ++ functionsFromFormula psi
functionsFromFormula (Iff phi psi) =nub $ functionsFromFormula phi ++ functionsFromFormula psi
functionsFromFormula (Exists _ phi) =nub $ functionsFromFormula phi
functionsFromFormula (Forall _ phi) = nub $ functionsFromFormula phi

prover :: FOProver
prover formula =
    let
        cleared_formula = removeForall $ skolemise $ Not formula
        consts =  constants (sig cleared_formula)
        terms = if null $ consts
            then (Prelude.map Var (vars cleared_formula))
            else (nub $ consts ++ functionsFromFormula cleared_formula)
        ground = groundInstances cleared_formula terms
        formula' = Prelude.foldr And T ground
   in not (sat_DP (generatePropsFormula formula'))


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
