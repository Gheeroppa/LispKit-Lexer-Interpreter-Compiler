{-
  Modulo:   Interprete SECD
  Autore:   federico.ghirardelli@studenti.unipd.it
  A.A.:     2015-2016
-}

module Interprete(
  interprete,
  Valore(..),
  test,
) where

import Compilatore

-- tipo che modella gli R-valori delle variabili. Si tratta dei valori da mettere nella pila S e nell'ambiente dinamico E
-- In particolare CLO modella le chiusure, rappresentate da (C, E): codice e ambiente
-- VLISTA: lista di valori

-- OGA = place holder per l'ambiente
data Valore = V LKC| OGA |
              CLO [Secdexpr] [[Valore]]| 
              VLISTA [Valore]
              deriving(Show,Eq)

-- datatype dei valori del Dump D
-- CONTR è un costruttore che prende una lista di comandi della macchina SECD
--    Serve ad esempio per salvare C in D quando eseguo una Sel
--    Contiene il controllo cioe' le operazioni spostate da C in D
-- TRIPLA serve quando invoco (Ap) una funzione per salvarmi i valori (S E C)
data Dump = CONTR  [Secdexpr] | 
            TRIPLA [Valore][[Valore]][Secdexpr] | DUMMY
            deriving(Show,Eq)


-- prende il primo valore della lista e la seconda lista.
-- funzione che crea l'ambiente dinamico ricorsivo necessario per il trattamento della ricorsione.
-- Attenzione: Serve nel caso Rap
-- Prende la lista dei parametri attuali della funzione su entrambi i parametri
lazyE::[Valore]-> [Valore]->[Valore] 
lazyE [] _ = [] 
lazyE (a:b) c = ((lazyClo a c):(lazyE b c))

-- Pende il primo valore della lista e la seconda lista.
--  se il primo elem e' un valore restituisce quel valore
--  se e' una  vlist restituisce la vlist
--  se e' una chiusura allora ritorna una chiusura con la E aggiornata per vedere i nuovi valori definiti dalla funzione precedente
lazyClo:: Valore -> [Valore]->Valore
lazyClo (CLO a b) c = (CLO a ((lazyE c c):b))
lazyClo(V x) _= (V x) 
lazyClo(VLISTA x) _= (VLISTA x)
lazyClo x _= error ("LazyClo trova valore incompatibile" ++ (show x))

-- Funzioni per la ricerca degli R-valori dati i loro indirizzi; Usate da Ld
-- Si usa per trovare l' R-valore all'interno di una lista dato un indice
-- In pratica trova il valore a quell'indice della lista
index::Integer ->[a]->a
index n  s= if n==0 then (head s) else (index (n-1) (tail s))  

-- data una coppia (n1,n2) di E mi ritorna R-valore della variabile
locate::(Integer, Integer)-> [[Valore]]->Valore
locate  (a,b)  e = (index b (index a e));
  
-- V è un valore LKC che dovrebbe rappresentare un valore LKC numero
-- questa funzione si occupa di verificarlo    
extract_int (V (NUM x)) = x 
extract_int x = error ("trovato altro da intero" ++ (show x))


-- funzioni per le liste di Valori VLISTA
-- VLISTA vuole una lista di valori naturalmente

-- vhead
vhd (VLISTA (a:b)) = a 
vhd (VLISTA [])  = error "vhd trovata lista vuota"
vhd _ = error "vhd non trova VLISTA"

-- vtail
vtl (VLISTA (a:b)) = VLISTA b  
vtl (VLISTA [])  = error "vtl trovata lista vuota";
vtl _ = error "vtl non trova VLISTA"

-- guarda se il valore è un valore ATOM cioe' un bool
vatom (V k) = V (BOO True)
vatom _ = V (BOO False)     
             
-- crea un bool LKC da un bool               
bool2s_espressione:: Bool ->LKC            
bool2s_espressione b = if b then (BOO True) else (BOO False)

-- test di uguaglianza per il tipo Valore; si adatta ai tipi dei parametri con cui è invocata
-- se non è un numero o una lista di numeri allora e' una uguaglianza tra chiusure
eqValore::Valore -> Valore -> Bool
eqValore a@(V _) b = (eqV a b)
eqValore a@(VLISTA _) b = (eqVLISTA a b)
eqValore a  b = error ("uguaglianza tra chiusure"++ (show a) ++ (show b))

-- uguaglianza tra tipi VLISTA
eqVLISTA::Valore -> Valore ->Bool
eqVLISTA (VLISTA []) (VLISTA [])= True 
eqVLISTA (VLISTA(a:b)) (VLISTA (c:d)) = (eqValore a c) && (eqVLISTA (VLISTA b) (VLISTA d))
eqVLISTA _ _= False

-- uguaglianza tra numeri
eqV (V a) (V b)= a==b
eqV _ _= False

 
-- FUNZIONE PRINCIPALE
-- case of sul valore Secdexpr da eseguire  (che istruzione devo eseguire?)
--              S            E            C          D         
interprete:: [Valore] -> [[Valore]]-> [Secdexpr]-> [Dump]-> Valore
interprete s e c d = case (head c) of 
    -- se e' una Ld devo caricare su S il valore che compare nella posizione (n1,n2) di E
    -- x=(n1,n2) e chiamo ricorsivamente interprete avendo messo pero' l'istruzione su S e aggiornato C
    Ld(b, n) -> let x = (locate (b,n) e)  in (interprete (x:s) e (tail c) d)

    -- devo caricare su S una costante senza valutarla.
    -- Se la costante e' nil carico su S VLISTA [] e aggiorno C,
    -- altrimenti carico la costante V su S e aggiorno
    Ldc k -> case k of 
              NIL -> (interprete ((VLISTA []):s) e (tail c) d)
              _   -> (interprete ((V k):s) e (tail c) d)

    -- operano con gli operatori in S e mettono il risultato su S
    Add -> let operand1 = extract_int (head s)
               operand2 = extract_int(head (tail s))
            in  (interprete ((V(NUM (operand1 + operand2))):(tail (tail s))) e (tail c)  d)
                                      
    Sub -> let operand1 = extract_int (head s)
               operand2 = extract_int(head (tail s))
           in  (interprete ((V(NUM (operand1 - operand2))):(tail (tail s))) e (tail c)  d)
                                      
    Mult -> let operand1 = extract_int (head s)
                operand2 = extract_int(head (tail s))
            in  (interprete ((V(NUM (operand1 * operand2))):(tail (tail s))) e (tail c)  d)
                                      
    Div -> let operand1 = extract_int (head s)
               operand2 = extract_int(head (tail s))
          in  (interprete ((V(NUM (operand1 `div` operand2))):(tail (tail s))) e (tail c)  d)
                                     
    Rem -> let operand1 = extract_int (head s)
               operand2 = extract_int(head (tail s))
            in  (interprete ((V(NUM (operand1 `mod` operand2))):(tail (tail s))) e (tail c)  d)
                                     
    Leq -> let operand1 = extract_int (head s)
               operand2 = extract_int(head (tail s))
            in  (interprete ((V(bool2s_espressione (operand1 <= operand2))):(tail (tail s))) e (tail c)  d)
                                      
    -- prende w1 e w2 e li sostituisce con un bool se sono o non sono uguali
    Eq -> case s of
            (w1:w2:w3) -> (interprete ((V (bool2s_espressione (eqValore w1 w2))):w3) e (tail c) d)
            _ -> error "manca un argomento in Eq"

    -- head della lista presente su S
    Car -> (interprete ((vhd(head s) ):(tail s)) e (tail c) d)

    -- tail della lista presente su S
    Cdr -> (interprete ((vtl(head s) ):(tail s)) e (tail c) d)
                                      
    -- concatena due liste
    Cons -> case head (tail s) of
              (VLISTA x)-> (interprete  (VLISTA ((head s):x):(tail (tail s))) e (tail c) d)
              x-> error ("CONS: il secondo argomento non e' una lista" ++ (show  x))

    -- metto un BOO su S
    Atom ->  (interprete ((vatom (head s)):(tail s)) e (tail c) d)

    -- IF THEN ELSE.
    -- Avviene che C diventa sl1 o sl2 e salvo lo stato del programma in D.
    Sel sl1 sl2 -> case head s of
                    (V (BOO True)) -> (interprete (tail s) e sl1 ((CONTR (tail c)):d))
                    (V (BOO False)) -> (interprete (tail s) e sl2 ((CONTR (tail c)):d))
                    _ -> error "non c'e' bool su s quando si esegue SEL"

    --ripristina C con il backup presente in D (dopo SEL)
    Join -> case (head d) of
              (CONTR c1) -> (interprete s e c1 (tail d))
              _ -> error "JOIN: il dump non contiene controllo"
                                      
    -- crea la chiusura della funzione (corpo funzione, E) cioe' (sl ,e)
    -- istruzione che corrisponde alla definizione di una funzione (lambda)
    Ldf sl -> (interprete ((CLO sl e):s) e (tail c) d)

    --Apply serve per invocare una funzione
    -- Se su S c'e' una chiusura CLO e se dopo la chiusura c'e' la lista dei parametri attuali della funzione da invocare
    -- si carica il corpo della funzione c1 su C per eseguirla, si carica in E l'ambiente della chiusura in modo che la funzione abbia
    -- il suo ambiaente al momento della definizione della stessa (static binding).
    -- Salvo in D la tripla (S E C)
    Ap -> case (head s) of 
            (CLO c1 e1) -> case (head (tail s)) of
                            VLISTA x -> (interprete [] (x:e1) c1 ((TRIPLA (tail(tail s)) e (tail c)):d))
                            _  -> error "AP senza lista dei parametri"                                
            _  -> error "AP senza chiusura su s"

    -- Return ripristina la tripla in D al termine della funzione invocata. 
    Rtn ->  case (head d) of
              (TRIPLA s1 e1 c1) -> (interprete ((head s):s1) e1 c1 (tail d))
              _ ->  error  "RTN: non trovata TRIPLA su dump"     
                               
    -- invocazione di funzione ricorsiva.
    -- Se la testa di S e' una chiusura e il suo E' ha un segnaposto e dopo la chiusura ci sono i paramentri attuali in lista,
    -- allora carico in C la funzione da eseguire, in E il nuovo ambiente calcolato (che puo anche essere una chiusura) 
    -- e viene aggiornato D come per Ap fatta eccezione per il segnaposto che viene tolto.
    Rap -> case (head s) of
            (CLO c1 e1) ->  case e1 of
                              ([OGA]:re) -> case (head (tail s)) of
                                              (VLISTA vl2) -> (interprete [] ((lazyE vl2 vl2):re) c1 ((TRIPLA (tail (tail s)) (tail e) (tail c)):d))
                                              _ -> error "manca lista dei parametri dopo OGA";
                              _ -> error "manca [OGA] sull'ambiente di chiusura ric"
            _  -> error "RAP: non trovata chiusura su s"
                                 
    -- push mette il segnaposto in E togliendolo da C questo e' fatto quando si definisce una funzione ricorsiva.                            
    Push ->(interprete s  ([OGA]:e)  (tail c)  d)
    
    --con stop viene ritornato il risultato.
    Stop -> (head s)

  {-  altrimenti warning: Pattern match(es) are overlapped
    -- una qualsiasi altra operazione non riconosciuta
    _  -> error "operazione non riconosciuta"
  -}

-- facilita l'uso di interprete
-- x e' un programma Secdexpr da eseguire. Si aggiunge Stop alla fine.
fin x = (interprete [] [] (x ++ [Stop]) [])  

-- Esegue il tutto sulla stringa x e da il risultato finale
test x = fin $ comp_one x
