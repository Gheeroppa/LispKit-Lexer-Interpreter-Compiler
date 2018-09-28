
module Analizzatore_sint_1(
  progdoll,
  dd
 )
where

import Lexer
import Prelude hiding (EQ,exp)

-- monade Exc
-- gestisce le eccezioni
data Exc a = Raise Exception | Return a
type Exception = String

-- Ridefinizione Show
-- La monade stampa il simbolo "$" se arriva alla fine
instance Show a => Show (Exc a) where
 show (Raise e) = "ERRORE:" ++ e
 show (Return x) = "RAGGIUNTO:" ++ (show x)

-- return x , incapsulo x
-- Raise e >>= prende e di tipo Exp, una funzione q di tipo m, ritorna un tipo Exp
-- Return x >>= come prima ma usa q per fare composizione ( applicata alla x )
instance Monad Exc where
 return x  = Return x
 (Raise e) >>= q   = Raise e
 (Return x) >>= q  = q x 

raise :: Exception -> Exc a
raise e = Raise e

-- recognize
-- funzione di ricerca per i terminali LET e LETREC
rec_key::[Token]-> Exc [Token]
rec_key ((Keyword LET):b)    = Return b
rec_key ((Keyword LETREC):b) = Return b 
rec_key (a:b)                = Raise ("trovato " ++ show(a) ++ ", atteso LET o LETREC")
rec_key  x                   = Raise ("ERRORE STRANO"  ++  show(x))

-- funzione di ricerca per il terminale IN
rec_in::[Token]->Exc[Token]
rec_in ((Keyword IN):b)= Return b
rec_in (a:b)           = Raise ("trovato " ++ show(a) ++ ", atteso IN")

-- funzione di ricerca per il terminale END
rec_end::[Token]->Exc[Token]
rec_end ((Keyword END):b)= Return b 
rec_end (a:b)            = Raise ("trovato " ++ show(a) ++ ", atteso END")

-- funzione di ricerca per il terminale THEN
rec_then ((Keyword THEN):b)= Return b
rec_then (a:b)             = Raise ("trovato " ++ show(a) ++ ", atteso THEN")

-- funzione di ricerca per il terminale ELSE
rec_else ((Keyword ELSE):b)= Return b
rec_else (a:b)             = Raise ("trovato " ++ show(a) ++ ", atteso ELSE")

-- funzione di ricerca per il terminale (
rec_lp ((Symbol LPAREN):b)=Return b 
rec_lp (a:b)              = Raise ("trovato " ++ show(a) ++ ", atteso ELSE")

-- funzione di ricerca per il terminale )
rec_rp ((Symbol RPAREN):b)=Return b 
rec_rp (a:b)              = Raise ("trovato " ++ show(a) ++ ", attesa )")

-- funzione di ricerca per il terminale ,
rec_virg ((Symbol VIRGOLA):b)=Return  b 
rec_virg (a:b)               = Raise ("trovato " ++ show(a) ++ ", attesa ,")

-- funzione di ricerca per il terminale =
rec_equals ((Symbol EQUALS):b)= Return b 
rec_equals (a:b)              = Raise ("trovato " ++ show(a) ++ ", atteso =")


-- funzione di ricerca per (PROG + $)
progdoll::[Token] -> String
progdoll x= show (prog x)

-- la funzione prog prende una lista di token e produce una monade con una lista di Token
-- concatena le funzioni costruite come le produzione della grammatica
prog:: [Token] -> Exc [Token]
prog a = do 
         x <- rec_key a
         y <- bind x
         z <- rec_in y
         w <- exp z
         rec_end w
   
-- per il nonTerminale EXP
exp::[Token]->Exc[Token]
exp a@((Keyword LET):b)    = (prog a)
exp a@((Keyword LETREC):b) = (prog a)
exp ((Keyword LAMBDA):b)   = do
                                x<-seq_var b
                                exp x
exp ((Operator CONS):b)    = do
                                x<-rec_lp b
                                y<-exp x
                                z<-rec_virg y
                                w<-exp z
                                rec_rp w
exp ((Operator LEQ):b)     = do
                                x<-rec_lp b
                                y<-exp x
                                z<-rec_virg y
                                w<- exp z
                                rec_rp w
exp ((Operator EQ):b)      = do
                                x<-rec_lp b
                                y<-exp x
                                z<- rec_virg y
                                w<-exp z
                                rec_rp w
exp ((Operator CAR):b)      = exp b
exp ((Operator CDR):b)      = exp b
exp ((Operator ATOM):b)     = exp b
exp ((Keyword IF):b)        = do
                                x<- exp b
                                y<-rec_then x
                                z<-exp y
                                w<-rec_else z
                                exp w
exp x                       =  expa x

-- per il nonTerminale BIND
-- la funzione riconosce la sequenza di coppie var=EXP
-- cerca prima il carattere/simbolo =, poi tramite la funzione Exp cerca un'espressione
-- al ritorno di questa si chiamera' quella per il nonTerminale X
bind ((Id a):b)            =  do
                                x<- rec_equals b
                                y<- exp x
                                funx y
bind (a:_)                  = Raise ("BINDER CON "++ show(a) ++" A SINISTRA")

-- per il nonTerminale X
-- Attenzione: la produzione di X contiene Epsilon; bisogna quindi valutare il FOLLOW
funx ((Keyword AND):b)     = bind b
funx a@((Keyword IN):b)    = Return a
funx (a:_)                 = Raise ("DOPO BINDERS; TROVATO"++show(a))


-- per il nonTerminale EXP_A
expa a = do
           x<- funt a
           fune1 x

-- per il nonTerminale T
funt a = do
           x<-funf a
           funt1 x

-- per il nonTerminale E1 (con simbolo + poi con simbolo -)
fune1 ((Symbol PLUS):b)    = do
                              x<- funt b
                              fune1 x
fune1 ((Symbol MINUS):b)   = do
                              x<-funt b
                              fune1 x
fune1 x                    = Return x

-- per il nonTerminale T1
funt1 ((Symbol TIMES):b)   = do
                              x<-funf b
                              funt1 x
funt1 ((Symbol DIVISION):b)= do
                              x<-funf b
                              funt1 x
funt1 x                    = Return x

-- per il nonTerminale F
funf (a:b)                 = if (exp_const a) then Return b 
                                              else fX (a:b)

-- per le produzioni di F
fX ((Id _):b)              = fuy b
fX ((Symbol LPAREN):b)     = do
                              x<- expa b
                              rec_rp x
fX (a:_)                   = Raise ("ERRORE in fX, TROVATO"++ show(a))


-- funzione di ricerca per il terminale exp_const
exp_const::Token ->Bool
exp_const (Number _)  =  True
exp_const Nil         =  True
exp_const (Bool _)    =  True
exp_const (String _)  =  True 
exp_const  _          = False

-- per il nonTerminale Y
fuy ((Symbol LPAREN):b)      =  do
                                 x<-seq_exp b
                                 rec_rp x
fuy x                        = Return x


-- per il nonTerminale Seq_Exp
seq_exp:: [Token]-> Exc[Token]
seq_exp a@((Symbol RPAREN):b)   = Return a
seq_exp a  = do
              x<-exp a
              list_exp x -- modifica separator (N)

-- per il nonTerminale List_Exp
-- nonTerminale aggiunto per rendere la grammatica GLK LL(1)
list_exp:: [Token]-> Exc[Token]
list_exp ((Symbol COMMA):b)  = do
                                seq_exp b
list_exp a = Return a

-- per il nonTerminale Seq_var
seq_var:: [Token]-> Exc[Token]
seq_var a@((Symbol RPAREN):b) = Return a
seq_var ((Id _):b) = seq_var b
seq_var (a:_) = Raise ("ERRORE in seq_var, TROVATO "++ show(a))