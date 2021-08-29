{-# LANGUAGE UnicodeSyntax, TypeSynonymInstances, FlexibleInstances #-}

module Lab2 where

import System.IO
import Data.List
import Control.Monad
import Control.Monad.State



import Formula
import Lab4

type CNFClause = [Literal]
type CNF = [CNFClause]

data Literal = Pos PropName | Neg PropName deriving (Eq, Show, Ord)

literal2var :: Literal -> PropName
literal2var (Pos p) = p
literal2var (Neg p) = p

opposite :: Literal -> Literal
opposite (Pos p) = Neg p
opposite (Neg p) = Pos p

-- generation of fresh variable names
fresh_lab2 :: [PropName] -> PropName
fresh_lab2 vars = head $ filter (not . (`elem` vars)) $ map (("p"++) . show) [0..]

variables_lab2 :: Formula -> [PropName]
variables_lab2 = nub . go where
  go T = []
  go F = []
  go (Prop p) = [p]
  go (Not φ) = go φ
  go (And φ ψ) = go φ ++ go ψ
  go (Or φ ψ) = go φ ++ go ψ
  go (Implies φ ψ) = go φ ++ go ψ
  go (Iff φ ψ) = go φ ++ go ψ

cnf2formula :: CNF -> Formula
cnf2formula [] = T
cnf2formula lss = foldr1 And (map go lss) where
    go [] = F
    go ls = foldr1 Or (map go2 ls)
    go2 (Pos p) = Prop p
    go2 (Neg p) = Not (Prop p)

positive_literals :: CNFClause -> [PropName]
positive_literals ls = nub [p | Pos p <- ls]

negative_literals :: CNFClause -> [PropName]
negative_literals ls = nub [p | Neg p <- ls]

literals :: [Literal] -> [PropName]
literals ls = nub $ positive_literals ls ++ negative_literals ls

cnf :: Formula -> [[Literal]]
cnf f = result where
    r_1 = go (nnf f)
    r_2 = map (sort . nub) r_1
    result = nub  r_2
    go T = []
    go F = [[]]
    go (Prop p) = [[Pos p]]
    go (Not (Prop p)) = [[Neg p]]
    go (φ `And` ψ) = go φ ++ go ψ
    go (φ `Or` ψ) = distribute (go φ) (go ψ)

-- find all ways of joining the lists (c.f. example below)
distribute :: [[a]] -> [[a]] -> [[a]]
distribute xss yss = go xss yss yss where
    go [] _ _ = []
    go (_:xss) yss [] = go xss yss yss
    go (xs:xss) yss (ys:yss') = (xs ++ ys) : go (xs:xss) yss yss'

-- type CNFClause = [Literal]
-- type CNF = [CNFClause]
ecnf :: Formula -> CNF
ecnf f = cnf (And env new_f)
    where
        (env, new_f, _) = formula_ecnf (f, variables_lab2 f)

formula_ecnf :: (Formula, [PropName]) -> (Formula, Formula, [PropName])
formula_ecnf (Not (Or psi phi), pn) = formula_ecnf (And (Not psi) (Not phi), pn)
formula_ecnf (Not (And psi phi), pn) = formula_ecnf (Or (Not psi) (Not phi), pn)

formula_ecnf (Not (Implies psi phi), pn) = formula_ecnf (And psi (Not phi), pn)

formula_ecnf (Not (Iff psi phi), pn) = formula_ecnf (Or (And (Not psi) phi) (And psi (Not phi)), pn)
formula_ecnf (Not (Not f), pn) = formula_ecnf (f, pn)
formula_ecnf (Not (Prop p), pn) = (T, Not (Prop p), pn)
formula_ecnf (Not F, pn) = (T, T, pn)
formula_ecnf (Not T, pn) = (T, F, pn)


formula_ecnf (T, pn) = (T, T, pn)
formula_ecnf (F, pn) = (T, F, pn)
formula_ecnf (Prop p, pn) = (T, Prop p, pn)
formula_ecnf ((Or phi psi), pn) = (env, Or prop_phi prop_psi, new_pn) where
    (env, prop_psi, prop_phi, new_pn)= dupa_ecnf (phi, psi, pn)
formula_ecnf ((And phi psi), pn) = (env, And prop_phi prop_psi, new_pn) where
    (env, prop_psi, prop_phi, new_pn)= dupa_ecnf (phi, psi, pn)
formula_ecnf ((Iff phi psi), pn) = (env, Iff prop_phi prop_psi, new_pn) where
    (env, prop_psi, prop_phi, new_pn)= dupa_ecnf (phi, psi, pn)

formula_ecnf ((Implies phi psi), pn) = (env, Implies prop_phi prop_psi, new_pn) where
    (env, prop_psi, prop_phi, new_pn)= dupa_ecnf (phi, psi, pn)


dupa_ecnf :: (Formula, Formula, [PropName]) -> (Formula, Formula, Formula, [PropName])
dupa_ecnf (phi, psi, pn) = (env, prop_psi, prop_phi, pn_psi) where
    (prop_phi, pn_phi, env_phi) = one_formula (phi, pn)
    (prop_psi, pn_psi, env_psi) = one_formula (psi, pn_phi)
    env = And  env_phi env_psi

    one_formula (Prop p, pn) = (Prop p, pn, T)
    one_formula (Not (Prop p), pn) = (Not (Prop p), pn , T)
    one_formula (T, pn) = (T, pn , T)
    one_formula (Not T, pn) = (F, pn , T)
    one_formula (F, pn) = (F, pn , T)
    one_formula (Not F, pn) = (T, pn , T)
    one_formula (Not (Not f), pn) = one_formula (f,pn)
    one_formula (f, pn) = (new_prop, new_pn, new_env) where
        new_prop_name = fresh_lab2 pn
        new_prop = (Prop new_prop_name)
        (env, new_f, new_pn) = formula_ecnf (f, new_prop_name:pn)
        new_env = And env (Iff new_f new_prop)

find_affirmative_negative :: CNF -> Maybe Literal
find_affirmative_negative cn = find (check) literals where
  literals = sort $ nub $ concat cn
  check literal = (find ((opposite literal) ==) literals) == Nothing

delete_literal :: Literal -> CNF -> CNF
delete_literal literal cn = (filter (literal `notElem`) cn)

affirmative_negative :: CNF -> CNF
affirmative_negative cn = case (find_affirmative_negative cn) of
  Just literal -> affirmative_negative (delete_literal literal cn)
  Nothing -> cn

resolution :: CNF -> CNF
resolution [] = []
resolution [[]] = [[]]
resolution ([]:_) = [[]]
resolution cn = left_cn ++ (liftM2 (++) pos_cn neg_cn) where
  pos_lit = Pos (literal2var $ head $ head cn)
  neg_lit = opposite pos_lit
  pos_cn  = map (filter (pos_lit /=)) $ filter (pos_lit `elem`) cn
  neg_cn  = map (filter (neg_lit /=)) $ filter (neg_lit `elem`) cn
  left_cn = filter (\cls ->(pos_lit `notElem` cls) && (neg_lit `notElem` cls)) cn

not_tautology :: [Literal] -> Bool
not_tautology clause = (literals_len == vars_len) where
    literals_len = length (nub clause)
    vars_len = length (nub (map literal2var clause))

remove_tautologies :: CNF -> CNF
remove_tautologies c = filter not_tautology c

clear_clause :: Literal -> [Literal] -> [[Literal]]
clear_clause literal clause =
  case (find (literal==) clause, find ((opposite literal)==) clause) of
    (Just  _, Nothing) -> []
    (Nothing, Just  _) -> [(filter ((opposite literal)/=) clause)]
    otherwise -> [clause]

one_literal :: CNF -> CNF
one_literal cn = go cn where
  foo :: Literal -> [[Literal]] -> [Literal] -> [[Literal]]
  foo literal acc cls = (clear_clause literal cls) ++ acc

  go :: CNF -> CNF
  go c = case (find (\cls -> (length (nub cls)) == 1) c) of
    Just (lit:_) -> one_literal (foldl (foo lit) [] c)
    otherwise -> remove_tautologies c


davids_putnam :: CNF -> Bool -> Bool
davids_putnam [] _ = True
davids_putnam [[]] _ = False
davids_putnam cn True = davids_putnam new_cn (new_cn /= cn) where
  new_cn = sort $ nub $ map (nub . sort) $ affirmative_negative $ one_literal $ remove_tautologies cn
davids_putnam cn False = davids_putnam (resolution cn) True

sat_DP :: SATSolver
sat_DP formula = davids_putnam (ecnf formula) True