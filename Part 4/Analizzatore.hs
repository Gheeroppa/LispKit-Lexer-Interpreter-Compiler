module Analizzatore (
  progdoll,
  getLKC,
  LKC(..)
) where

import Lexer
import Prelude hiding (EQ,exp)
import Control.Applicative (Alternative())

-- monade Exc, usata per la gestione delle eccezioni
data Exc a = Raise Exception | Return a
type Exception = String

-- Ridefinizione Show, stampa del simbolo $ a fine controllo
instance Show a => Show (Exc a) where
 show (Raise e) = "ERRORE:" ++ e
 show (Return x) = "RAGGIUNTO:" ++ (show x)

-- Definizione del funtore
instance Functor Exc where
  fmap f (Raise e) = Raise e
  fmap f (Return v) = Return (f v)

-- Definizione del funtore applicativo
instance Applicative Exc where
  pure = Return
  (Raise e) <*> _ = Raise e
  (Return f) <*> something = fmap f something

{-  Definizione della monade:
	return x  = incapsula x
	Raise e >>= prende e di tipo Exp, una funzione q di tipo m, ritorna un tipo Exp
	Return x >>= come prima ma usa q per fare composizione ( applicata alla x )
-}
instance Monad Exc where
    return x  = Return x
    (Raise e) >>= q   = Raise e
    (Return x) >>= q  = q x

raise :: Exception -> Exc a
raise e = Raise e

{- LKC data, datatype per creare l'albero astratto partendo da quello concreto di derivazione
 ETY => segnale le produzioni Epsilon
 CARC => head della lista
 CDRC => tail della lista
 CALL LKC [LKC] => rapprenta le invocazioni di funzioni :  LKC (primo parametro) -> funzione invocata, [LKC] (secondo) lista parametri attuali
 LAMBDA [LKC] LKC => definizione di funzione: [LKC] (primo parametro) -> lista dei parametri formali, LKC -> corpo della funzione 
 LET e LETREC=> contengono il corpo e i binders (coppie variabile,espresione)
 La C finale in alcuni nomi e' stata messa per evitare clash con data-type preesistenti (es. lambda-lambdac)
-}
data LKC = ETY | VAR String | NUM Integer | BOO Bool | STRI String | NIL | ADD LKC LKC | SUB LKC LKC | MULT LKC LKC | 
   DIV LKC LKC | REM LKC LKC | EQC LKC LKC | LEQC LKC LKC | CARC LKC | CDRC LKC | CONSC LKC LKC | 
   ATOMC LKC | IFC LKC LKC LKC | LAMBDAC [LKC] LKC | CALL LKC [LKC] | LETC LKC [(LKC,LKC)] | 
   LETRECC LKC [(LKC,LKC)]
   deriving (Show,Eq)


{- FUNZIONE REC_KEY
    funzione currificata, il tipo dei costruttori (LKC -> [(LKC,LKC)]->LKC) e' come se tornasse una funzione
	Funzione che riconosce il costruttore corretto LETC o LETRECC
-}
rec_key :: [Token] -> Exc ([Token], (LKC -> [(LKC, LKC)] -> LKC))
rec_key ((Keyword LET):b)    = Return (b,LETC)
rec_key ((Keyword LETREC):b) = Return (b,LETRECC)
rec_key (a:b)                = Raise ("trovato " ++ show(a) ++", atteso LET o LETREC")
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
rec_then::[Token]->Exc[Token]
rec_then ((Keyword THEN):b)= Return b
rec_then (a:b)             = Raise ("trovato " ++ show(a) ++ ", atteso THEN")

-- funzione di ricerca per il terminale ELSE
rec_else::[Token]->Exc[Token]
rec_else ((Keyword ELSE):b)= Return b
rec_else (a:b)             = Raise ("trovato " ++ show(a) ++ ", atteso ELSE")

-- funzione di ricerca per il terminale ( left paren
rec_lp::[Token]->Exc[Token]
rec_lp ((Symbol LPAREN):b)=Return b
rec_lp (a:b)              = Raise ("trovato " ++ show(a) ++ ", atteso ELSE")

-- funzione di ricerca per il terminale ) right paren
rec_rp::[Token]->Exc[Token]
rec_rp ((Symbol RPAREN):b)=Return b
rec_rp (a:b)              = Raise ("trovato " ++ show(a) ++ ", in"++show(b) ++" attesa )")

-- funzione di ricerca per il terminale ,
rec_virg::[Token]->Exc[Token]
rec_virg ((Symbol COMMA):b)=Return  b
rec_virg (a:b)               = Raise ("trovato " ++ show(a) ++ ", attesa ,")

-- funzione di ricerca per il terminale =
rec_equals::[Token]->Exc[Token]
rec_equals ((Symbol EQUALS):b)= Return b
rec_equals (a:b)              = Raise ("trovato " ++ show(a) ++ ", atteso =")

-- funzione di ricerca per (PROG + $)
progdoll::[Token] -> String
progdoll x= show (prog x)

{-
    FUNZIONE generateLKC
	funzione che estre LKC da una EXC(Token,LKC)
-}
getLKC :: String -> LKC
getLKC x = extractLKC (prog(lexi x))

-- Richiamata dalla funzione precedente, estrae il valore LKC dalla monade finale
extractLKC :: Exc ([Token], LKC) -> LKC
extractLKC (Return (a, b)) = b
extractLKC (Raise x) = error x


{-
    FUNZIONE PROG:
	data una lista di token essa produce una monade composta da una lista di token e la corrispondente LKC
	
	Rappresenta le produzioni del non terminale Prog

	​1.1:   Prog​ ::= let Bind in Exp end
    1.2:   Prog​ ::= letrec Bind in Exp end
	Costruttore currificato proveniente dalla funzione rec_key: 
     - LETC LKC [(LKC,LKC)]    -- LETC Corpo [(var,exp)]
     - LETRECC LKC [(LKC,LKC)] -- LETRECC Corpo [(var,exp)]
    
-}
prog::[Token] -> Exc([Token],LKC)
prog a =
    do
        (x, trad_letc_letrecc)<-rec_key a  					--cerca LETC o LETRECC
        (y, trad_bind) <- bind x		   					--cerca + traduzione produzione BIND
        z    <- rec_in y									--cerca Token IN
        (w, trad_exp) <- exp z								--cerca + traduzione produzione EXP
        k <- rec_end w										--cerca Token END
        Return (k, (trad_letc_letrecc trad_exp trad_bind))  --produzione monade con lista di Token
     
{- 
	FUNZIONE EXP:
	lista di token ritorna monade composta da lista di token e LKC
	4 Exp ::= Prog | lambda(Seq_Var) Exp | ExpA | OPP(Seq_Exp) | if Exp then Exp else Exp
	
-}
exp::[Token]->Exc([Token],LKC)
exp a@((Keyword LET):b)    = (prog a)												--LET -> passa alla funzione prog

exp a@((Keyword LETREC):b) = (prog a)												--LETRECC -> passa a prog

exp ((Keyword LAMBDA):b)   = do														--LAMBA creazione di una finzione -> lambda(Seq_var) EXP
                                x     			  <-	rec_lp b					--cerca parentesi (
                                (z, trad_sec_var) <- 	seq_var x 					--cerca + traduzione Seq_var, non serve riconoscitore parentesi ) già in seq_var
                                (w, trad_exp)  	  <- 	exp z						--cerca + traduzione EXP 
                                Return(w, (  LAMBDAC trad_sec_var  trad_exp ))		--creazione monade
								
exp ((Operator CONS):b)    = do														--CONS (EXP,EXP)
                                x<-rec_lp b											--cerca (
                                (y, first_trad) <-exp x								--cerca + traduzione EXP
                                z<-rec_virg y										--cerca ,
                                (w, new_trad) <-exp z								--cerca + traduzione EXP
                                result <- rec_rp w									--cerca )
                                Return(result,  CONSC first_trad  new_trad)			--creazione monade
								
exp ((Operator LEQ):b)     = do														--LEQ (EXP,EXP)
                                x<-rec_lp b											--cerca parentesi (
                                (y, first_trad) <-exp x								--cerca + traduzione EXP
                                z<-rec_virg y										--cerca simbolo ,
                                (w, new_trad) <- exp z							 	--cerca + traduzione EXP
                                result <- rec_rp w									--cerca parentesi )
                                Return(result, ( LEQC first_trad  new_trad))		--creazione monade 
								
exp ((Operator EQ):b)      = do														--EQ(EXP,EXP)
                                x<-rec_lp b											--cerca parentesi (
                                (y, first_trad) <-exp x								--cerca + traduzione EXP
                                z<- rec_virg y										--cerca simbolo ,
                                (w, new_trad) <-exp z								--cerca + traduzione EXP
                                result<- rec_rp w									--cerca parentesi )
                                Return(result, ( EQC  first_trad  new_trad ))		--creazione monade
								
exp ((Operator CAR):b)      = do													--CAR EXP
                                (result, trad) <- exp b								--cerca + traduzione EXP
                                Return (result, ( CARC  trad))						--creazione monades
								
exp ((Operator CDR):b)      = do													--CDR EXP
                                (result, trad) <- exp b								--cerca + traduzione EXP
                                Return (result, ( CDRC  trad))						--creazione monade
								
exp ((Operator ATOM):b)     = do													--ATOM 	EXP										
                                (result, trad) <- exp b								--cerca + traduzione EXP
                                Return (result, ( ATOMC  trad))						--cerca + traduzione monade
								
exp ((Keyword IF):b)        = do													--IF EXP THEN EXP ELSE EXP
                                (x, trad_exp_if) <- exp b							--cerca + traduzione EXP
                                y<-rec_then x										--cerca simbolo then
                                (z, trad_exp_then) <-exp y							--cerca + traduzione EXP
                                w<-rec_else z										--cerca simbolo else
                                (result, trad_exp_else ) <- exp w					--cerca + traduzione EXP
                                Return(result, (IFC  trad_exp_if trad_exp_then trad_exp_else )) --costruzione monade
								
exp x                       =  expa x												--cerca + traduzione EXP


{-
    FUNZIONE BIND:
	2 Bind ::= var = Exp X
    la funzione riconosce la sequenza di coppie var=EXP
	
	Trad(Bind) deve assumere come valore la lista delle coppie [(Var ''x1'', LKC(Exp1)),...,(Var ‘‘xn’’, LKC(Expn))]:LKC*LKC list

	La funzione Buind viene richiamata continuamente fino a quando non inizia a effettuare un ritorno.
	Ritorna LKC[EXP], dovrei avere un'assegnazione di variabile valore avendo [variabile nome_variabile, EXP successiva (val)]
-}
bind::[Token]->Exc([Token],[(LKC,LKC)])
bind ((Id a):b)            =  do
                                x<- rec_equals b															--cerca simoblo =
                                (y,variable_value) <- exp x													--cerca + traduzione EXP
                                (next_tok, next_variable_value) <- funx y									--cerca + traduzione X
                                Return(next_tok, (lister(VAR a, variable_value) ++ next_variable_value))	--creazione monade, lista con (VAR nome_var, value_var) next_var

bind (a:_)                  = Raise ("BINDER CON "++ show(a) ++" A SINISTRA")								--intercettazione errore


{-
    FUNZIONE FUNX:
	3 X ::= and Bind | epsilon
	poiche' la produzione di X contiene epsilon bisogna valutare il FOLLOW
	Nella produzione e' presente Bind quindi la funzione FUNX tornera' una lista di coppie LKC
	Quando vado ad analizzare il FOLLOW trovo IN. Poiche' come output devo avere una coppia ma IN e' dove definisco l'albero allora
	posso far si che FUNX torni una lista vuota
-}
funx::[Token]->Exc([Token], [(LKC,LKC)])
funx ((Keyword AND):b)      = bind b										--trovato AND quindi passo alla funzione BIND
funx a@((Keyword IN):b)     = Return (a,[])									--follow trovato IN, ritorno a ed una lista vuota
funx (a:_)                  = Raise ("DOPO BINDERS; TROVATO " ++ show(a))	--intercettazione eccezione


{-  FUNZIONE EXPA:
	5 ExpA ::= T E1
-}
expa a = do
           (x, trad_funt)<- funt a	--cerca + traduzione T
           fune1 x trad_funt		--richiamo E1 passando la traduzione di T (attributi che E1 eredita)

{-  FUNZIONE T:
	7 T ::= F T1
-}
funt a = do
           (x, trad_funt)<-funf a	--cerca + traduzione F
           funt1 x trad_funt		--richimo T1 passando la traduzione di F (attributi che T1 eredita)

{-  FUNZIONE E1
	6 E1_a::= OPA T E1_b | epsilon
	La fuznione viene richiamata ereditanto il primo operando. Essa deve tradurre il secondo operando indipendentemente dal simbolo "+" o "-".
	In fine chiama ADD o SUB sul primo operando (ereditato) e la traduzione del secondo.
	
	Poiche' contiene epsilon controllo anche il FOLLOW.

    esempio "let x = 5 and y = 4 in y + x end $" ==> diventa 
        ...(ADD (VAR y) (VAR x))....
        in sostanza VAR y è l'elemento che ho ereditato prima di elaborare VAR x la stessa cosa si può applicare ad altri operatori
-}
fune1::[Token] -> LKC -> Exc([Token],LKC)
fune1 ((Symbol PLUS):b)  operand  = do											--ramo ADD
                                        (x, trad_funt) <- funt b				--cerca + traduzione T
                                        (y, trad_fune1) <- fune1 x trad_funt	--cerca + traduzione E1_b
                                        Return(y, ADD operand trad_fune1)		--costruzione monade

fune1 ((Symbol MINUS):b) operand  = do											--ramo SUB
                                        (x,trad_funt) <-funt b					--cerca + traduzione T
                                        (y, trad_fune1) <- fune1 x trad_funt	--cerca + traduzione E1_b
                                        Return(y, SUB operand trad_fune1)		--costruzione monade

fune1 x operand                     = Return(x, operand) 						--follow perche' ho epsilon in first

{-
    FUNZIONE FUNT1:
	8 T1_a ::= OPM F T1_b | epsilon
	
	Il tipo della fuznione deriva dagli attributi ereditati => MULT LKC LKC
															   DIV  LKC LKC
	Il primo operando e' un attributo ereditato
	Poiche' c'e' la epsilon devo controllare anche il ramo FOLLOW
-}
funt1::[Token] -> LKC ->Exc([Token],LKC)
funt1 ((Symbol TIMES):b) operand  = do											--ramo MULT
                                    (x, trad_funf) <-funf b						--cerca + traduzione F
                                    (z, trad_funt1) <- funt1 x trad_funf		--cerca + traduzione T1_b
                                    Return(z, MULT operand trad_funt1)			--costruzione monade

funt1 ((Symbol DIVISION):b) operand  = do										--ramo DIV
                                    (x, trad_funf) <-funf b						--cerca + traduzione F
                                    (z, trad_funt1) <- funt1 x trad_funf		--cerca + traduzione T1_b
                                    Return(z,(DIV operand trad_funt1))			--costruzione monade
									
funt1 x  operand                = Return(x, operand)							--ramo follow

{-
    FUNZIONE FUNF:
	9 F ::= var Y | exp_const | (ExpA)
-}
funf::[Token]->Exc([Token], LKC)
funf (a:b)  = do
                  result <- exp_const a					--cerca + traduzione exp_const => TRUE se e' un costante, FALSE se non lo e'
                  case result of
                       (True, lkc) ->  Return(b,lkc)	--se ha prodotto TRUE allora ritorno la costante LKC e il token relativo
                       (False, empty) -> do				--se FALSE allora controllo di non essere alla fine
                       (x, lkc) <- fX(a:b)				--richiamo fX per controllare 
                       Return(x, lkc)					--creazione monade

{-
    FUNZIONE FX:
	Controlla di non essere alla fine.
	Se rileva il Token Id:
      - VAR LKC => referenziato il nome di una variabile
      - CALL LKC [LKC] => dopo il token Id c'e' una sequenza di espressioni
-}
fX::[Token]->Exc([Token], LKC)
fX ((Id a):b)              =  do												--trovato Token Id
                                (x, trad_funy) <- fuy b							--cerca + traduzione Y
                                if(trad_funy == [ETY])							--controlla se la traduzione di Y e' vuota
                                    then Return(x, VAR a)						--se vuota allora torna la variabile LKC
                                    else Return(x, CALL (VAR a) trad_funy)		--se non vuota allora c'e' una sequenza di espressioni quindi CALL
-- espressione algebrica
fX ((Symbol LPAREN):b)     = do													--trovato Token parentesi (
                              (x, trad_expa)<- expa b							--cerca + traduzione EXPA
                              z <- rec_rp x										--cerca parentesi )
                              Return (z, trad_expa)								--costruzione monade
							  
fX (a:_)                   = Raise ("ERRORE in fX, TROVATO "++ show(a))			--gestione eccezioni


{-  FUNZIONE EXP_CONST
	funzione di ricerca per il terminale exp_const
-}
exp_const::Token ->Exc(Bool, LKC)
exp_const (Number n)  =  Return (True, NUM n)	--numero
exp_const Nil         =  Return (True, NIL)		--NULL
exp_const (Bool b)    =  Return (True, BOO b)	--boleano
exp_const (String s)  =  Return (True, STRI s)	--stringa
exp_const  _          =  Return (False, ETY)	--qualsiasi cosa che non sia le precedenti

{-
    FUNZIONE FUY
	10 Y ::= (Seq_Exp) | epsilon
	La fuzione ritorna una lista di LKC poiche' sarebbero i parametri di fuznione
    
	Poiche' nella produzione c'e' epsilon allora inserisco caso in cui torna ETY
-}
fuy::[Token] ->Exc([Token], [LKC])
fuy ((Symbol LPAREN):b) =  do								--trovata parentesi (
                          (x, trad_seq_exp) <- seq_exp b	--cerca + traduzione SEQ_EXP
                          z <- rec_rp x						--cerca parentesi )
                          Return (z, trad_seq_exp)			--creazione monade
						  
fuy x = Return (x, [ETY])									--secondo caso torna ETY

{-
    FUNZIONE DI SUPPORTO
	utilizza polimorfismo parametrico: qualsiasi tipo lo inserisco in una lista poioche' non e' stato dichiarato il tipo
-}
lister a = [a]

{-  FUNZIONE SEQ_EXP
	14 Seq_Exp ::= Exp Separator | epsilon
-}
seq_exp:: [Token]-> Exc([Token], [LKC])
seq_exp a@((Symbol RPAREN):b)  = Return (a, [])		--trovato simbolo ), torna a e lista vuota
seq_exp a  = do
            (x, trad_exp) <- exp a					--cerca + traduzione EXP
            (z,trad_separ) <- separator x			--cerca + traduzione SEPARATOR
            Return (z, [trad_exp] ++ trad_separ)	--costruzione monade
			
{-  FUNZIONE SEPARAOR
	15 Separator ::= , Exp Separator | epsilon
	non-terminale aggiunto per rendere grammatica LL(1)
-}
separator:: [Token]-> Exc([Token], [LKC])
separator ((Symbol COMMA):b)  = do								--trovato simbolo ,		
                                (z,trad_exp) <- exp b			--cerca + traduzione EXP
                                (t, trad_list)<- separator z	--cerca + traduzione SEPARATOR
                                Return (t, trad_exp:trad_list)	--costruzione monade
								
separator a = Return (a, [])									--ramo FOLLOW, ritorno a e lista vuota

{-  FUNZIONE SEQ_VAR
	16 Seq_Var ::= var Seq_Var | epsilon
	
	La funzione toglie la parentesi destra ) dall'ultima iterazione.
	Nella produzione c'e' epsilon quindi controllo ramo FOLLOW (se e' vuoto allora considera il primo dei successori)
-}
seq_var:: [Token]-> Exc([Token], [LKC])
seq_var a@((Symbol RPAREN):b)   = Return (a, [])						--trovata parentesi ) ritorno a e lista vuota

seq_var ((Id a):b) = do													--trovato Id
                    (z, trad_sec_var) <- seq_var b						--cerca + traduzione SEQ_VAR
                    Return (z, [VAR a] ++ trad_sec_var)					--costruzione monade
					
seq_var (a:_) =  Raise ("ERRORE in seq_var, TROVATO " ++ show(a))		--gestione eccezioni
