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


prover :: Formula -> Bool
prover phi =
    let
        phi' = removeForall $ skolemise $ Not phi
        grounds = groundInstances phi' $ if null $ constants (sig phi')
            then map (\x -> Fun x []) (fv phi')
            else nub $ constants (sig phi')

        check x = not $ davids_putnam (nub $ concatMap (ecnf . genPropFormula) (nub x)) True

        nextCs x = nub $ concatMap (nub . formula_constants) $ nub x
        nextGrounds x = nub $ groundInstances phi' $ nub $ nextCs x

        checkNext x =
            let xx = nextGrounds x
            in (check x || ((xx /= [] && xx /= x) && checkNext xx) )
    in
        if null grounds then check [phi'] else checkNext grounds

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
