module PropHilbertParse where

import PropHilbertStyle
import Data.Char (toLower)

prettyPrintForm :: Form -> String
prettyPrintForm Bot = "⊥"
prettyPrintForm (Var s) = s
prettyPrintForm (Bot :-> Bot) = "⊤"
prettyPrintForm (f :-> Bot) = "¬" ++ prettyPrintForm f
prettyPrintForm (p :-> q) = "(" ++ prP ++ " → " ++ prQ ++ ")"
  where
    [prP, prQ] = map prettyPrintForm [p, q]

prettyPrintForm (p :/\ q) = "(" ++ prP ++ " ∧ " ++ prQ ++ ")"
  where
    [prP, prQ] = map prettyPrintForm [p, q]

prettyPrintForm (p :\/ q) = "(" ++ prP ++ " ∨ " ++ prQ ++ ")"
  where
    [prP, prQ] = map prettyPrintForm [p, q]


data FormToken = TPropVar String | TMetaVar String -- meta vars may be redundant
                | TOpenBracket | TClosedBracket
                | TBot | TTop
                | TOpImpl | TOpConj | TOpDisj | TOpNeg
                | TEnd | TError
                deriving (Eq, Show)


tokenise :: String -> [FormToken]
tokenise fmStr = aux $ words $ padSymbs fmStr
  where
    padSymbs :: String -> String
    padSymbs str = concatMap padIfSpec str
      where
        padIfSpec :: Char -> String
        padIfSpec '(' = " ( "
        padIfSpec ')' = " ) "
        padIfSpec '~' = " ~ "
        padIfSpec '¬' = " ~ "
        padIfSpec x = [x]
    aux :: [String] -> [FormToken]
    aux [] = [TEnd]
    aux ("":_) = [TError]
    aux (wrd:wrds)
      | wrd == "(" = TOpenBracket : aux wrds
      | wrd == ")" = TClosedBracket : aux wrds
      | wrdToLow `elem` ["_|_", "⊥", "bot", "false", "falsum", "0"] = TBot : aux wrds
      | wrdToLow `elem` ["T", "⊤", "top", "true", "taut", "1"] = TTop : aux wrds
      | wrdToLow `elem` ["neg", "not", "~", "¬"] = TOpNeg : aux wrds
      | wrdToLow `elem` ["->", "→", "le", "impl"] = TOpImpl : aux wrds
      | wrdToLow `elem` ["/\\", "∧", "&", "&&", "and"] = TOpConj : aux wrds
      | wrdToLow `elem` ["\\/", "∨", "||", "or"] = TOpDisj : aux wrds
--      | not . (all isLetter) $ wrd = [TError]
--      | isUpper (head wrd) = TMetaVar wrd : aux wrds
      | otherwise = TPropVar wrd : aux wrds
      where
        wrdToLow = map toLower wrd

data POpTag = PImpl | PDisj | PConj deriving (Eq, Show)
data ParsedToken = POpenBr | PClosBr
                 | POpImpl | POpDisj | POpConj | POpNeg
                 | PForm Form POpTag
                 deriving (Eq, Show)


{--
  Form ::= Impl
  Impl ::= Disj -> Impl | Disj
  Disj ::= Disj \/ Conj | Conj
  Conj ::= Conj /\ (Form) | Var | Bot


--}

parse :: [FormToken] -> Maybe Form -- this version does not distinguish PropVars from MetaVars
parse ltokens
  | TError `elem` ltokens = Nothing
  | otherwise = parseAux ltokens []
  where
    pOperators :: [ParsedToken]
    pOperators = [POpImpl, POpDisj, POpConj, POpNeg]

    parseAux :: [FormToken] -> [ParsedToken] -> Maybe Form

    parseAux [TEnd] [PForm fm _] = Just fm

    parseAux tokens (PClosBr : (PForm fm _) : POpenBr : stack) = parseAux tokens (PForm fm PConj : stack)
    parseAux tokens (PForm fm PConj : POpNeg : stack) = parseAux tokens (PForm (neg fm) PConj : stack)

    parseAux (TBot : tokens) stack = parseAux tokens (PForm Bot PConj : stack)
    parseAux (TTop : tokens) stack = parseAux tokens (PForm top PConj : stack)
    parseAux (TOpNeg : tokens) stack = parseAux tokens (POpNeg : stack)
    parseAux (TPropVar v : tokens) stack = parseAux tokens (PForm (Var v) PConj : stack)

    parseAux (TOpenBracket : tokens) [] = parseAux tokens [POpenBr]
    parseAux (TOpenBracket : tokens) stack@(st:_)
      | st `elem` POpenBr:pOperators = parseAux tokens (POpenBr:stack)
      | otherwise = Nothing

    parseAux tokens (PForm fm2 PConj : POpConj : PForm fm1 PConj : stack) = parseAux tokens (PForm (fm1 :/\ fm2) PConj : stack)
    parseAux tokens (PForm fm2 PDisj : POpDisj : PForm fm1 PDisj : stack) = parseAux tokens (PForm (fm1 :\/ fm2) PDisj : stack)
    parseAux tokens (PForm fm2 PImpl : POpImpl : PForm fm1 PDisj : stack) = parseAux tokens (PForm (fm1 :-> fm2) PImpl : stack)
    parseAux (TOpConj : tokens) stack = parseAux tokens (POpConj : stack)

    parseAux tokens@(op:_) (PForm fm PConj : stack)
      | op `elem` [TOpDisj, TOpImpl, TClosedBracket, TEnd] = parseAux tokens (PForm fm PDisj : stack)
      | otherwise = Nothing

    parseAux tokens@(op:ts) stack@(PForm fm PDisj : st)
      | op == TOpDisj = parseAux ts (POpDisj : stack)
      | op == TOpImpl = parseAux ts (POpImpl : stack)
      | op `elem` [TClosedBracket, TEnd] = parseAux tokens (PForm fm PImpl : st)
      | otherwise = Nothing

    parseAux (op:tokens) stack
      | op == TClosedBracket = parseAux tokens (PClosBr : stack)
      | otherwise = undefined

    parseAux _ _ = Nothing

readFm :: String -> Maybe Form
readFm str = parse . tokenise $ str
