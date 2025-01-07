module RegexParser  

import Prelude  
import Regex  
import Data.List  
import Data.List.Elem  

-- First, let's define what it means for a string to be parseable into a Regex  
public export  
data Parseable : String -> Regex -> Type where  
  -- Empty string parses to Empty  
  ParseEmpty : Parseable "" Empty  
  
  -- Single character parses to Chr  
  ParseChar : (c : Char) -> Parseable (pack [c]) (Chr c)  
  
  -- Concatenation: if s1 parses to r1 and s2 parses to r2, then s1++s2 parses to Concat r1 r2  
  ParseConcat : {s1, s2 : String} -> {r1, r2 : Regex} ->  
               Parseable s1 r1 ->   
               Parseable s2 r2 ->   
               Parseable (s1 ++ s2) (Concat r1 r2)  
               
  -- Alternation: if s parses to either r1 or r2  
  ParseAltL : {s : String} -> {r1, r2 : Regex} ->  
             Parseable s r1 ->   
             Parseable s (Alt r1 r2)  
             
  ParseAltR : {s : String} -> {r1, r2 : Regex} ->  
             Parseable s r2 ->   
             Parseable s (Alt r1 r2)  
             
  -- Star: either empty string or concatenation of matches  
  ParseStarEmpty : Parseable "" (Star r)  
  
  ParseStarCons : {s1, s2 : String} -> {r : Regex} ->  
                 Parseable s1 r ->   
                 Parseable s2 (Star r) ->   
                 Parseable (s1 ++ s2) (Star r)  

-- ... (previous Parseable and ParseResult definitions remain the same)  

-- Token type for lexical analysis  
data Token =   
    CharToken Char  
  | StarToken  
  | AltToken  
  | LParenToken  
  | RParenToken  

-- Lexer  
tokenize : String -> Either String (List Token)  
tokenize str = go (unpack str) []  
  where  
    go : List Char -> List Token -> Either String (List Token)  
    go [] acc = Right (reverse acc)  
    go ('*' :: rest) acc = go rest (StarToken :: acc)  
    go ('|' :: rest) acc = go rest (AltToken :: acc)  
    go ('(' :: rest) acc = go rest (LParenToken :: acc)  
    go (')' :: rest) acc = go rest (RParenToken :: acc)  
    go ('\\' :: x :: rest) acc = go rest (CharToken x :: acc)  
    go (c :: rest) acc = if isAlpha c || isDigit c  
                           then go rest (CharToken c :: acc)  
                           else Left $ "Invalid character: " ++ show c  

-- Recursive descent parser  
-- regex    → alt  
-- alt      → concat ('|' alt)?  
-- concat   → star (concat)?  
-- star     → atom ('*')?  
-- atom     → char | '(' regex ')'
mutual  
  parseRegexStr : List Token -> Either String (Regex, List Token)  
  parseRegexStr tokens = parseAltStr tokens  

  parseAltStr : List Token -> Either String (Regex, List Token)  
  parseAltStr tokens = do  
    (left, rest) <- parseConcatStr tokens  
    case rest of  
      (AltToken :: rest') => do  
        (right, remaining) <- parseAltStr rest'  
        Right (Alt left right, remaining)  
      _ => Right (left, rest)  

  parseConcatStr : List Token -> Either String (Regex, List Token)  
  parseConcatStr tokens = do  
    (first, rest) <- parseStarStr tokens  
    case rest of  
      [] => Right (first, [])  
      (AltToken :: _) => Right (first, rest)  
      (RParenToken :: _) => Right (first, rest)  
      _ => do  
        (second, remaining) <- parseConcatStr rest  
        Right (Concat first second, remaining)  

  parseStarStr : List Token -> Either String (Regex, List Token)  
  parseStarStr tokens = do  
    (atom, rest) <- parseAtomStr tokens  
    case rest of  
      (StarToken :: rest') => Right (Star atom, rest')  
      _ => Right (atom, rest)  

  parseAtomStr : List Token -> Either String (Regex, List Token)  
  parseAtomStr [] = Left "Unexpected end of input"  
  parseAtomStr (CharToken c :: rest) = Right (Chr c, rest)  
  parseAtomStr (LParenToken :: rest) = do  
    (inner, rest') <- parseRegexStr rest  
    case rest' of  
      (RParenToken :: remaining) => Right (inner, remaining)  
      _ => Left "Missing closing parenthesis"  
  parseAtomStr _ = Left "Expected character or group"  

-- Main parsing function  
export  
parseRegexString : String -> Either String Regex  
parseRegexString input = do  
  tokens <- tokenize input  
  (result, remaining) <- parseRegexStr tokens  
  case remaining of  
    [] => Right result  
    _ => Left "Unexpected tokens at end of input"  

   
