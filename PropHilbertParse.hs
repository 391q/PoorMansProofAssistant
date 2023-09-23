module PropHilbertParse where

import PropHilbertStyle
import Data.Char (isLetter, isUpper, toLower)
import Control.Monad.State

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


data FormToken = TPropVar String | TMetaVar String
                | TOpenBracket | TClosedBracket
                | TBot | TTop
                | TOpImpl | TOpConj | TOpDisj | TOpNeg
                | TError
                | TForm Form -- ugly solution for stack in parsing
                deriving (Eq, Show)


tokenise :: String -> [FormToken]
tokenise fmStr = aux $ words $ padPars fmStr
  where
    padPars :: String -> String
    padPars str = concatMap padIfPar str
      where
        padIfPar :: Char -> String
        padIfPar '(' = " ( "
        padIfPar ')' = " ) "
        padIfPar x = [x]
    aux :: [String] -> [FormToken]
    aux [] = []
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
      | not . (all isLetter) $ wrd = [TError]
      | isUpper (head wrd) = TMetaVar wrd : aux wrds
      | otherwise = TPropVar wrd : aux wrds
      where
        wrdToLow = map toLower wrd


parse :: [FormToken] -> Maybe Form -- this version does not distinguish PropVars from MetaVars
parse tokens
  | TError `elem` tokens = Nothing
  | otherwise = parseAux tokens [] -- evalState $ parsingPDA tokens
  where
    parseAux :: [FormToken] -> [FormToken] -> Maybe Form
    parseAux [] [TForm fm] = Just fm
    parseAux ts (TBot:stack) = parseAux ts (TForm Bot : stack)
    parseAux ts (TTop:stack) = parseAux ts (TForm top : stack)
    parseAux ts (TPropVar v : stack) = parseAux ts (TForm (Var v) : stack)
    parseAux ts (TMetaVar v : stack) = parseAux ts (TForm (Var v) : stack) -- TODO : add contexts to use meta vars
    parseAux ts (TForm fm : TOpNeg : stack) = parseAux ts (TForm (neg fm) : stack)
    parseAux ts (TClosedBracket : f@(TForm _) : TOpenBracket : stack) = parseAux ts (f : stack)
    parseAux ts (TForm psi : maybeOp : TForm phi : stack) =
      case maybeOp of
        TOpImpl -> parseAux ts (TForm (phi :-> psi) : stack)
        TOpDisj -> parseAux ts (TForm (phi :\/ psi) : stack)
        TOpConj -> parseAux ts (TForm (phi :/\ psi) : stack)
        _ -> Nothing

    parseAux [] _ = Nothing
    parseAux (t:ts) stack = parseAux ts (t:stack)

readFm :: String -> Maybe Form
readFm str = parse . tokenise $ str
