module HilbertStyle where

import Data.Function ((&))

infixr 6 :->
infixl 7 :\/
infixl 8 :/\

data Form = Bot | Var String | Form :/\ Form | Form :\/ Form | Form :-> Form deriving (Show, Eq, Read)

data Sequent = [Form] :=> [Form] deriving (Eq, Read, Show)

neg :: Form -> Form
neg f = f :-> Bot

subst :: Form -> String -> Form -> Form
subst Bot _ _ = Bot
subst f0@(Var v) v' f = if v == v' then f else f0
subst (a :-> b) v f = af :-> bf where { af = subst a v f ; bf = subst b v f }
subst (a :/\ b) v f = af :/\ bf where { af = subst a v f ; bf = subst b v f }
subst (a :\/ b) v f = af :\/ bf where { af = subst a v f ; bf = subst b v f }

{--

--}

hilbertAxTaut :: Form -> Bool
hilbertAxTaut (a :-> _ :-> a') = a == a'
hilbertAxTaut _ = False

hilbertAxInnMP :: Form -> Bool
hilbertAxInnMP ((a :-> b :-> c) :-> (a' :-> b') :-> (a'' :-> c'')) = a == a' && a == a'' && b == b' && c == c''
hilbertAxInnMP _ = False

hilbertAxExplosion :: Form -> Bool
hilbertAxExplosion ((a :-> Bot) :-> b :-> _) = a == b
hilbertAxExplosion _ = False

hilbertAxNegIntro :: Form -> Bool
hilbertAxNegIntro ((a :-> b) :-> (a' :-> nb) :-> na) = a == a' && nb == neg b && na == neg a
hilbertAxNegIntro _ = False

hilbertAxTND :: Form -> Bool
hilbertAxTND (a :\/ na) = na == neg a
hilbertAxTND _ = False


hilbertAxIntroConj :: Form -> Bool
hilbertAxIntroConj (a :-> b :-> a' :/\ b') = a == a' && b == b'
hilbertAxIntroConj _ = False

hilbertAxElimConjL :: Form -> Bool
hilbertAxElimConjL (a :/\ _ :-> a') = a == a'
hilbertAxElimConjL _ = False

hilbertAxElimConjR :: Form -> Bool
hilbertAxElimConjR (_ :/\ b :-> b') = b == b'
hilbertAxElimConjR _ = False

hilbertAxIntroDisjL :: Form -> Bool
hilbertAxIntroDisjL (a :-> a' :\/ _) = a == a'
hilbertAxIntroDisjL _ = False

hilbertAxIntroDisjR :: Form -> Bool
hilbertAxIntroDisjR (a :-> _ :\/ a') = a == a'
hilbertAxIntroDisjR _ = False

hilbertAxElimDisj :: Form -> Bool
hilbertAxElimDisj ((a :-> c) :-> (b' :-> c') :-> (a'' :\/ b'' :-> c'')) = a == a'' && b' == b'' && c == c' && c == c''
hilbertAxElimDisj _ = False

hilbertAx :: Form -> Bool
hilbertAx fm = or $ map (fm &) [hilbertAxTaut, hilbertAxInnMP, hilbertAxExplosion, hilbertAxNegIntro, hilbertAxTND,
                                hilbertAxElimDisj, hilbertAxIntroDisjR, hilbertAxIntroDisjL,
                                hilbertAxElimConjR, hilbertAxElimConjL, hilbertAxIntroConj]

modusPonens :: Form -> Form -> Form -> Bool
modusPonens (a :-> b) a' b' = a == a' && b == b'
modusPonens _ _ _ = False

apModusPonens :: Form -> Form -> Maybe Form
apModusPonens (a :-> b) a' = if a == a' then Just b else Nothing
apModusPonens _ _ = Nothing

infix 5 :|-

data Deriv = [Form] :|- Form deriving Show

dedLemImplElim :: Deriv -> Maybe [Deriv]
dedLemImplElim (fms :|- a :-> b) = Just $ (:[]) $ (a : fms) :|- b
dedLemImplElim _ = Nothing

dedLemImplIntro :: Form -> Deriv -> Maybe [Deriv]
dedLemImplIntro h (fms :|- a)
  | h `elem` fms = Just $ (:[]) $ (del_h fms) :|- h :-> a
  | otherwise = Nothing
    where
      del_h :: [Form] -> [Form]
      del_h [] = [] -- does not needed but anyway
      del_h (h' : fs)
        | h' == h = fs
        | otherwise = h' : (del_h fs)

type Goal = Deriv

data ProofState = ProofState { derived :: [Form]
                             , goals :: [Goal]
                             } deriving (Show)

proofStepAx :: Form -> ProofState -> Maybe ProofState
proofStepAx fm ps@(ProofState{derived = fms})
  | hilbertAx fm = Just $ ps {derived = fms ++ [fm]}
  | otherwise = Nothing

proofStepH :: Form -> ProofState -> Maybe ProofState
proofStepH _ (ProofState _ []) = Nothing
proofStepH h (ProofState der gls@((hs :|- _) : _))
  | h `elem` hs = Just $ ProofState (der ++ [h]) gls
  | otherwise = Nothing

proofStepMP :: Int -> Int -> ProofState -> Maybe ProofState
proofStepMP i j ps@ProofState{ derived = der }
  | i >= length der || j >= length der = Nothing
  | otherwise = let (a, b) = (der !! i, der !! j) in
                  case apModusPonens a b of
                    Nothing -> Nothing
                    Just c -> Just $ ps {derived = der ++ [c]}

proofFinGoal :: ProofState -> Maybe ProofState
proofFinGoal ProofState{ goals = [] } = Nothing -- TODO : is this a correct approach?
proofFinGoal (ProofState der ((_ :|- g):gs))
  | last der == g = Just $ ProofState [] gs
  | otherwise = Nothing


proofNewGoals :: (Goal -> Maybe [Goal]) -> ProofState -> Maybe ProofState
proofNewGoals _ ProofState{ goals = [] } = Nothing
proofNewGoals thm ProofState{ goals = g:gs } = case thm g of
                                            Nothing -> Nothing
                                            Just newGoals -> Just $ ProofState { derived = [] , goals = newGoals ++ gs }

-- TODO:  prettyPrint, prettyWrite?, basic IO
