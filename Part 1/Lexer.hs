{-
  Descrizione:
  L'analizzatore lessicale riceve in input un programma LispKit 
  (Lisp semplificato), cioe' una lista di caratteri e deve riconoscere
  le componenti elementari del linguaggio e deve metterle in una forma 
  che sia semplice da manipolare nella successiva fase di analisi sintattica.
  Per esempio, deve riconoscere le costanti (per esempio i numeri interi
  oppure il valore true, eccetera), le parole chiave, gli identificatori, 
  gli operatori ed i simboli di separazione.

  Implementazione : funzione i
-}

module Lexer (
    Token(..),
    Symbol_T(..),
    Operator_T(..),
    Keyword_T(..),
    lexi
) where
    
import Prelude hiding (EQ)
import Data.Typeable

-- Tipi
--tpip per le keyword
data Keyword_T = LET | IN | END | LETREC | AND | IF | THEN | ELSE | LAMBDA
    deriving (Show,Eq)
--tipo per gli operatori
data Operator_T = EQ | LEQ | CAR | CDR | CONS | ATOM
    deriving (Show,Eq)
--tipi per i simboli (=
data Symbol_T = LPAREN | RPAREN | EQUALS | PLUS | MINUS | TIMES | DIVISION |COMMA| DOLLAR
    deriving (Show,Eq)
--tipi di token
data Token = Keyword Keyword_T | Operator Operator_T | Id String |
    Symbol Symbol_T | Number Integer | String String | Bool Bool | Nil
    deriving (Show,Eq)



-- Funzioni di supporto
-- Testa se il carattere e' un carattere alfabetico
isAlphaChar c = c `elem` (['a' .. 'z'] ++ ['A' .. 'Z'])

-- Riconosce se c e' un carattere numerico
isDigitChar c = c `elem` ['0' .. '9']

-- Testa se il carattere e' un carattere valido per comporre un identificatore, un operatore o una keyword, cioè se è alfabetico o numerico
isIdChar c = isAlphaChar c || isDigitChar c

-- Testa se il carattere e' un separatore
isSeparator c = c `elem` "()=$,"

-- Testa se e' uno spazio o accapo o un tab ecc
isSpace c = c `elem` [' ', '\n', '\f', '\r', '\t']

--Testa se e' un simbolo
isSymbol c = c `elem` "()=+-*/,"


{- data una stringa X la confronta con le parole chiavi e con gli operatori
   del Lisp Kit e se e' una di queste cose, restituisce la corrispondente
   coppia token_lexema, altrimenti la considera un identificatore e
   restituisce la coppia (ID, STRINGA(X)) -}
extractWord :: String -> Token
extractWord w = case w of
    "let"     -> Keyword LET
    "in"      -> Keyword IN
    "end"     -> Keyword END
    "letrec"  -> Keyword LETREC
    "and"     -> Keyword AND
    "if"      -> Keyword IF
    "then"    -> Keyword THEN
    "else"    -> Keyword ELSE
    "lambda"  -> Keyword LAMBDA
    
    "eq"      -> Operator EQ
    "leq"     -> Operator LEQ
    "car"     -> Operator CAR
    "cdr"     -> Operator CDR
    "cons"    -> Operator CONS
    "atom"    -> Operator ATOM
    
    "true"    -> Bool True
    "false"   -> Bool False
    
    "nil"     -> Nil
    
    otherwise -> Id w


-- Prende in input un carattere e lo traduce nel corrispettivo simbolo
toSymbol :: Char -> Symbol_T
toSymbol c = case c of
    '(' -> LPAREN
    ')' -> RPAREN
    '+' -> PLUS
    '-' -> MINUS
    '*' -> TIMES
    '/' -> DIVISION
    '=' -> EQUALS
    ',' -> COMMA

{- n input numero segno
   n è la stringa in input
   numero è il numero elaborato finora
   segno è il segno del numero, true sse e' negativo (rilevato da I) -}
n :: String -> Integer -> Bool -> (Token, String)
n "" _ _ = error "Unexpected end of string"
n input@(c:l) num sign
    | isDigitChar c =
        let d = read [c] :: Integer
        in n l (num*10 + d) sign
    | otherwise = (Number((if sign then -1 else 1) * num), input)


-- Stato SC per riconoscere le stringhe tra virgolette
{- sc input stringa
   stringa è la stringa elaborata finora -}
sc :: String -> String -> (Token, String)
sc "" _ = error "Unexpected end of string"
sc ('"':l) res = (String res, l)
sc (c:l) res = sc l (res ++ [c])


-- Stato S per raccogliere le stringhe che possono corrispondere ad identificatori, operatori prefissi o keyword
{- s input stringa
   stringa è l'identificatore elaborato finora -}
s :: String -> String -> (Token, String)
s "" _ = error "Unexpected end of string"
s input@(c:l) res
    | isIdChar c = s l (res ++ [c])
    | otherwise = (extractWord(res), input)

{- FUNZIONE PRINCIPALE i:
	riceve in input una Stringa (programma in lexi) e restituisce come output una lista di token
  -> input::[String] stringa in LispKit
  f::Char head ella stringa (singolo carattere)
  l::[Char] tail della stringa (lista di caratteri)
  analizza il carattere f e cambia di stato a seconda della sua natura, creando e concatenando i token 
-}
i :: String -> [Token]
i "" = error "Unexpected end of string"			  -- caso di errore, non c'e' input
i "$" = [(Symbol DOLLAR)]						  -- se e' dollaro fine analisi
i (' ':l) = i l                                   -- se e' uno spazio lo salta
i input@(f:l)
    | isSpace f = i l                             -- se e' una spaziatura la salta
    | isSymbol f = (Symbol $ toSymbol f) : (i l)  -- se è un ()=+-*/, allora crea Simbol Simbol_T
    | otherwise =                                 -- numero, stringa o identificatore
        let                                       -- definisce call => funzione che chiama n, s o sc a seconda di f
            call :: Char -> (Token, String)
            call '"' = sc l ""                    -- stringa
            call '~' = n l 0 True                 -- numero negativo
            call f
                | isDigitChar f = n input 0 False -- numero positivo
                | isAlphaChar f = s input ""      -- identificatore
            call _ = error ("Lexical error starting with " ++ input) --caso di errore della funzione call
            (token, next) = call f 	--output coppia token, next: con next si identifica la restante stringa da tradurre
        in 
            token : (i next)                       -- concatena token alla lista e prosegue con l'analisi dei restanti caratteri

-- Funzione principale per l'analisi lessicale, viene richiamata dall'esterno
lexi :: String -> [Token]
lexi = i
