{-# LANGUAGE UnicodeSyntax, TypeSynonymInstances, FlexibleInstances, LambdaCase #-}

module Main where

import Data.List

import System.IO
import System.Random
import System.Timeout

import Text.Printf

import Control.Monad.State

import Test.QuickCheck hiding (Fun, (===))

import Labs
import Formula
import Parser hiding (one)


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

prover :: Formula -> Bool
prover phi =
    let phi' = removeForall $ skolemise $ Not phi
    grounds = groundInstances phi' $ if null $ constants (sig phi')
        then map (\x -> Fun x []) (fv phi')
        else nub $ constants (sig phi')

    check x = not $ satDP $ nub $ concatMap (ecnf . relProp) (nub x)

    nextCs x = nub $ concatMap (nub . formula_constants) $ nub x
    nextGrounds x = nub $ groundInstances phi' $ nub $ nextCs x

    check Next x =
        let xx = nextGrounds x
        in (check x || ((xx /= [] && xx /= x) && checkNext xx) )
    in
        if null grounds then check [phi'] else checkNext grounds
