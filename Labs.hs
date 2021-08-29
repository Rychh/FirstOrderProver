{-# LANGUAGE UnicodeSyntax, TypeSynonymInstances, FlexibleInstances #-}

module Labs where

import System.IO
import Data.List
import Control.Monad
import Control.Monad.State

import Text.Parsec
--import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token
import Test.QuickCheck hiding (Fun, (===))

import Formula


update :: Eq a => (a -> b) -> a -> b -> a -> b
update f a b x | x == a = b
               | otherwise = f x

partitions :: [a] -> [[[a]]]
partitions [] = [[]]
partitions (x:xs) = [[x]:yss | yss <- partitions xs] ++ [(x:ys):yss | (ys:yss) <- partitions xs]

-- all possible ways to split n into the sum of stricly positive integers
catalan :: Int -> [[Int]]
catalan n = map (map length) $ partitions [1..n]

-- alternating merge of two (potentially infinite) lists
merge :: [a] -> [a] -> [a]
merge [] bs = bs
merge (a : as) bs = a : merge bs as

-- alternating merge of a (potentially infinite) list of (potentially infinite) lists
merges :: [[a]] -> [a]
merges [] = []
merges (as:ass) = merge as (merges ass)

-- collect all functions from a finite list to a (potentially infinite) list
functions :: Eq a => [a] -> [b] -> [a -> b]
functions [] _ = [undefined]
functions (a:as) bs = merges [[update f a b | f <- functions as bs] | b <- bs]

variants :: VarName -> [VarName]
variants x = x : [x ++ show n | n <- [0..]]

varsT :: Term -> [VarName]
varsT (Var x) = [x]
varsT (Fun _ ts) = nub $ concatMap varsT ts

vars :: Formula -> [VarName]
vars T = []
vars F = []
vars (Rel _ ts) = varsT (Fun "dummy" ts)
vars (Not phi) = vars phi
vars (And phi psi) = nub $ vars phi ++ vars psi
vars (Or phi psi) = nub $ vars phi ++ vars psi
vars (Implies phi psi) = nub $ vars phi ++ vars psi
vars (Iff phi psi) = nub $ vars phi ++ vars psi
vars (Exists x phi) = nub $ x : vars phi
vars (Forall x phi) = nub $ x : vars phi

freshIn :: VarName -> Formula -> Bool
x `freshIn` phi = not $ x `elem` vars phi

freshVariant :: VarName -> Formula -> VarName
freshVariant x phi = head [ y | y <- variants x, y `freshIn` phi ]

renameT :: VarName -> VarName -> Term -> Term
renameT x y (Var z)
  | z == x = Var y
  | otherwise = Var z
renameT x y (Fun f ts) = Fun f (map (renameT x y) ts)

rename :: VarName -> VarName -> Formula -> Formula
rename x y T = T
rename x y F = F
rename x y (Rel r ts) = Rel r (map (renameT x y) ts)
rename x y (Not phi) = Not (rename x y phi)
rename x y (And phi psi) = And (rename x y phi) (rename x y psi)
rename x y (Or phi psi) = Or (rename x y phi) (rename x y psi)
rename x y (Implies phi psi) = Implies (rename x y phi) (rename x y psi)
rename x y (Iff phi psi) = Iff (rename x y phi) (rename x y psi)
rename x y (Forall z phi)
  | z == x = Forall z phi
  | otherwise = Forall z (rename x y phi)
rename x y (Exists z phi)
  | z == x = Exists z phi
  | otherwise = Exists z (rename x y phi)


generalise :: Formula -> Formula
generalise phi = go $ fv phi
  where go [] = phi
        go (x:xs) = Forall x $ go xs

fresh :: Formula -> Formula
fresh phi = evalState (go phi) []
  where go :: Formula -> State [VarName] Formula
        go T = return T
        go F = return F
        go phi@(Rel _ _) = return phi
        go (Not phi) = liftM Not (go phi)
        go (And phi psi) = liftM2 And (go phi) (go psi)
        go (Or phi psi) = liftM2 Or (go phi) (go psi)
        go (Implies phi psi) = liftM2 Implies (go phi) (go psi)
        go (Iff phi psi) = liftM2 Iff (go phi) (go psi)
        go (Forall x phi) = go2 Forall x phi
        go (Exists x phi) = go2 Exists x phi

        go2 quantifier x phi =
          do xs <- get
             let y = head [y | y <- variants x, not $ y `elem` xs]
             let psi = rename x y phi
             put $ y : xs
             liftM (quantifier y) $ go psi

nnf :: Formula -> Formula
nnf T = T
nnf (Not T) = F
nnf F = F
nnf (Not F) = T
nnf (Rel r ts) = (Rel r ts)
nnf (Not (Rel r ts)) = (Not (Rel r ts))
-- nnf (Prop p) = (Prop p)
-- nnf (Not (Prop p)) = (Not (Prop p))
nnf (And phi psi) = (And (nnf phi) (nnf psi))
nnf (Not (And phi psi)) = nnf (Or (Not(phi)) (Not(psi)))
nnf (Or phi psi) = (Or (nnf phi) (nnf psi))
nnf (Not (Or phi psi)) = nnf (And (Not(phi)) (Not(psi)))
nnf (Implies phi psi) = nnf (Or (Not(phi)) psi)
nnf (Not (Implies phi psi)) = nnf (And phi (Not psi))
nnf (Iff phi psi) = nnf (Or (And phi psi) (Not (Or phi psi)))
nnf (Not (Iff phi psi)) = nnf (Or (And (Not phi) psi) (And phi (Not psi)))
nnf (Exists z phi) = (Exists z (nnf phi))
nnf (Not (Exists z phi)) = (Forall z (nnf (Not phi)))
nnf (Forall z phi) = (Forall z (nnf phi))
nnf (Not (Forall z phi)) = (Exists z (nnf (Not phi)))
nnf (Not (Not f)) = nnf f
nnf (Not f) = nnf (Not (nnf f))
nnf _ = error "not a propositional formula"

pnf :: Formula -> Formula
pnf = pnf' . nnf
pnf' (And (Forall x psi) phi) = pull And Forall x psi phi
pnf' (And phi (Forall x psi)) = pull And Forall x psi phi
pnf' (And (Exists x psi) phi) = pull And Exists x psi phi
pnf' (And phi (Exists x psi)) = pull And Exists x psi phi
pnf' (Or  (Forall x psi) phi) = pull Or  Forall x psi phi
pnf' (Or  phi (Forall x psi)) = pull Or  Forall x psi phi
pnf' (Or  (Exists x psi) phi) = pull Or  Exists x psi phi
pnf' (Or  phi (Exists x psi)) = pull Or  Exists x psi phi
pnf' (And psi phi) = pull_2 And psi phi
pnf' (Or  psi phi) = pull_2 Or  psi phi
pnf' f = f

is_forall_or_exists (Forall _ _) = True
is_forall_or_exists (Exists _ _) = True
is_forall_or_exists _ = False

pull and_or forall_exists x psi phi = forall_exists x' formula'
  where
    x' = freshVariant x (and_or psi phi)
    psi' = pnf' psi
    phi' = pnf' phi
    formula = rename x x' (and_or psi' phi' )
    formula' = if is_forall_or_exists  psi' || is_forall_or_exists phi' then pnf' formula else formula
pull_2 and_or psi phi = formula'
  where
    psi' = pnf' psi
    phi' = pnf' phi
    formula = and_or psi' phi'
    formula' = if is_forall_or_exists  psi' || is_forall_or_exists phi' then pnf' formula else formula

substT :: Substitution -> Term -> Term
substT σ (Var x) = σ x
substT σ (Fun f ts) = Fun f (map (substT σ) ts)

subst :: Substitution -> Formula -> Formula
subst _ T = T
subst _ F = F
subst σ (Rel r ts) = Rel r $ map (substT σ) ts
subst σ (Not phi) = Not $ subst σ phi
subst σ (And phi psi) = And (subst σ phi) (subst σ psi)
subst σ (Or phi psi) = Or (subst σ phi) (subst σ psi)
subst σ (Implies phi psi) = Implies (subst σ phi) (subst σ psi)
subst σ (Iff phi psi) = Iff (subst σ phi) (subst σ psi)
subst σ (Exists x phi) = Exists x (subst (update σ x (Var x)) phi)
subst σ (Forall x phi) = Forall x (subst (update σ x (Var x)) phi)

sigT :: Term -> Signature
sigT (Var _) = []
sigT (Fun f ts) = nub $ (f, length ts) : concatMap sigT ts

sig :: Formula -> Signature
sig T = []
sig F = []
sig (Rel r ts) = concatMap sigT ts
sig (Not phi) = sig phi
sig (And phi psi) = nub $ sig phi ++ sig psi
sig (Or phi psi) = nub $ sig phi ++ sig psi
sig (Implies phi psi) = nub $ sig phi ++ sig psi
sig (Iff phi psi) = nub $ sig phi ++ sig psi
sig (Exists _ phi) = sig phi
sig (Forall _ phi) = sig phi

constants :: Signature -> [Term]
constants s = [Fun c [] | (c, 0) <- s]

groundInstances :: Formula -> [Term] -> [Formula]
groundInstances phi ts = [subst s phi | s <- functions (fv phi) ts]

skolemise :: Formula -> Formula
skolemise = pnf . (go []) . fresh . nnf . generalise where
  go :: [Term] -> Formula -> Formula
  go _ T = T
  go _ F = F
  go _ phi@(Rel _ _) = phi
  go vns (Not phi) = Not (go vns phi)
  go vns (And phi psi) = And (go vns phi) (go vns psi)
  go vns (Or phi psi) = Or (go vns phi) (go vns psi)
  go vns (Implies phi psi) = Implies (go vns phi) (go vns psi)
  go vns (Iff phi psi) = Iff (go vns phi) (go vns psi)
  go vns (Forall x phi) = Forall x (go ((Var x):vns) phi)
  go vns (Exists x phi) = skol_rename x skol_fun new_phi where
    new_phi = go ((Var x):vns) phi
    skol_fun = Fun x vns


skol_renameT :: VarName -> Term -> Term -> Term
skol_renameT x y (Var z)
  | z == x = y
  | otherwise = Var z
skol_renameT x y (Fun f ts) = Fun f (map (skol_renameT x y) ts)

skol_rename :: VarName -> Term -> Formula -> Formula
skol_rename x y T = T
skol_rename x y F = F
skol_rename x y (Rel r ts) = Rel r (map (skol_renameT x y) ts)
skol_rename x y (Not phi) = Not (skol_rename x y phi)
skol_rename x y (And phi psi) = And (skol_rename x y phi) (skol_rename x y psi)
skol_rename x y (Or phi psi) = Or (skol_rename x y phi) (skol_rename x y psi)
skol_rename x y (Implies phi psi) = Implies (skol_rename x y phi) (skol_rename x y psi)
skol_rename x y (Iff phi psi) = Iff (skol_rename x y phi) (skol_rename x y psi)
skol_rename x y (Forall z phi) = Forall z (skol_rename x y phi)
skol_rename x y (Exists z phi) = Exists z (skol_rename x y phi)

atomicFormulas :: Formula -> [Formula]
atomicFormulas T = []
atomicFormulas F = []
atomicFormulas phi@(Rel _ ts) = [phi]
atomicFormulas (Not phi) = atomicFormulas phi
atomicFormulas (And phi psi) = nub $ atomicFormulas phi ++ atomicFormulas psi
atomicFormulas (Or phi psi) = nub $ atomicFormulas phi ++ atomicFormulas psi
atomicFormulas (Implies phi psi) = nub $ atomicFormulas phi ++ atomicFormulas psi
atomicFormulas (Iff phi psi) = nub $ atomicFormulas phi ++ atomicFormulas psi
atomicFormulas (Exists x phi) = atomicFormulas phi
atomicFormulas (Forall x phi) = atomicFormulas phi

sat :: Formula -> Bool
sat phi = or [ev int phi | int <- functions atoms [True, False]]
  where atoms = atomicFormulas phi

        ev :: (Formula -> Bool) -> Formula -> Bool
        ev int T = True
        ev int F = False
        ev int atom@(Rel _ _) = int atom
        ev int (Not φ) = not (ev int φ)
        ev int (Or φ ψ) = ev int φ || ev int ψ
        ev int (And φ ψ) = ev int φ && ev int ψ
        ev _ φ = error $ "unexpected formula: " ++ show φ

removeForall :: Formula -> Formula
removeForall (Forall _ φ) = removeForall φ
removeForall φ = φ

aedecide :: Formula -> Bool
aedecide = not . sat . foldr And T . ground . removeForall . skolemise . Not where
  ground phi = groundInstances phi (map Var (vars phi) ++ constants (sig phi))