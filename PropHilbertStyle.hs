module HilbertStyle where

import Data.Function ((&))

infixr 6 :->
infixl 7 :\/
infixl 8 :/\

data Form = Bot | Var String | Form :/\ Form | Form :\/ Form | Form :-> Form deriving (Show, Eq, Read)

data Sequent = [Form] :=> [Form] deriving (Eq, Read, Show)

neg :: Form -> Form
neg f = f :-> Bot

top :: Form
top = Bot :-> Bot

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
dedLemImplElim (fms :|- a :-> b) = Just $ [(a : fms) :|- b]
dedLemImplElim _ = Nothing

dedLemImplIntro :: Form -> Deriv -> Maybe [Deriv]
dedLemImplIntro h (fms :|- a)
  | h `elem` fms = Just $ [(del_h fms) :|- h :-> a]
  | otherwise = Nothing
    where
      del_h :: [Form] -> [Form]
      del_h [] = [] -- does not needed but anyway
      del_h (h' : fs)
        | h' == h = fs
        | otherwise = h' : (del_h fs)

type Goal = Deriv

data ProofState = ProofState { currGoal :: Goal
                             , derived :: [Form]
                             , openGoals :: [([Form], Goal)]
                             } deriving (Show)

noMoreGoals :: ProofState
noMoreGoals = ProofState{ currGoal = [] :|- top
                        , derived = []
                        , openGoals = []
                        }

derivStepAx :: Form -> ProofState -> Maybe ProofState
derivStepAx fm ps@(ProofState{derived = fms})
  | hilbertAx fm = Just $ ps {derived = fms ++ [fm]}
  | otherwise = Nothing

derivStepH :: Form -> ProofState -> Maybe ProofState
derivStepH h ps@ProofState{ derived = der , currGoal = hs :|- _ }
  | h `elem` hs = Just $ ps { derived = (der ++ [h]) }
  | otherwise = Nothing

derivStepMP :: Int -> Int -> ProofState -> Maybe ProofState
derivStepMP i j ps@ProofState{ derived = der }
  | i >= length der || j >= length der = Nothing
  | otherwise = let (a, b) = (der !! i, der !! j) in
                  case apModusPonens a b of
                    Nothing -> Nothing
                    Just c -> Just $ ps {derived = der ++ [c]}

proofCloseGoal :: ProofState -> Maybe ProofState
proofCloseGoal ps@ProofState{ derived = der , currGoal = _ :|- g }
  | last der == g = case openGoals ps of
                      [] -> Just noMoreGoals
                      (der', g'):gs -> Just $ ProofState{ currGoal = g'
                                                        , derived = der'
                                                        , openGoals = gs
                                                        }
  | otherwise = Nothing


proofReplaceGoal :: (Goal -> Maybe [Goal]) -> ProofState -> Maybe ProofState
proofReplaceGoal thm ps@ProofState{ currGoal = g , openGoals = gs } =
  case thm g of
    Nothing -> Nothing
    Just [] -> proofCloseGoal ps -- theorem immediately achieves our goal
    Just (newGoal:newGoals) -> Just $ ProofState{ currGoal = newGoal
                                                , derived = []
                                                , openGoals = newFreshGoals ++ gs
                                                } where newFreshGoals = map ((,) []) newGoals -- new goals with empty derivations

proofAssertNewGoal :: Form -> ProofState -> Maybe ProofState
proofAssertNewGoal fm ProofState{ currGoal = g@(hs :|- _) , derived = der , openGoals = gs } = Just ps
  where
    ps = ProofState{ currGoal = hs :|- fm
                   , derived = []
                   , openGoals = (der, g):gs
                   }

-- TODO: variations of proofAssertNewGoal, structural rules, prettyPrint, prettyWrite?, basic IO
