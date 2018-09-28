{-
  Modulo:   Test linguaggio LispKit
  Autore:   federico.ghirardelli@studenti.unipd.it
  A.A.:     2015-2016
-}


import Lexer
import Analizzatore
import Compilatore
import Interprete

main :: IO ()
main = return ()

-- applica il fattoriale a tutti gli elementi di una lista di interi
a = "letrec FACT = lambda (X) if eq(X,0) then 1 else X*FACT(X-1) and " ++
    "G = lambda (H L) if eq(L,nil) then L else cons(H(car(L)),G(H,cdr(L))) " ++
    "in G(FACT,cons(1,cons(2,cons(3,nil)))) end $";

b = "let x = cons(\"ab\",cons(\"cd\",nil)) in if true then cons(\"01\",x) " ++
    "else nil end $";

c = "let x = 5 and y = 6 in x*3 + y*2*x + x*y end $"

-- mostra come si possa utilizzare letrec anche con binder non-funzionali (le
-- variabili a sinistra non devono apparire a destra)
d = "let z = 3 in letrec x = 2+z and y = 2*z in x*y*z end end $"

-- considera una lista di liste Z e produce una lista semplice che contiene
-- tanti interi quante sono le liste contenute in Z e l'intero corrispondente ad
-- una lista contenuta in Z è la somma dei fattoriali dei suoi elementi: f2=fattoriale, f1=calcola somma dei 
--fattoriali degli elementi di una 
--lista di interi e f0 distribuisce f1 sulle liste contenute in Z *)
e = "letrec f0 = lambda (x) letrec f1 = lambda(y) letrec f2 = lambda (z) " ++
    "if eq(z,1) then 1 else z*f2(z-1) in if eq(y,nil) then 0 else " ++
    "f2(car(y)) + f1(cdr(y)) end in if eq(x,nil) then nil else " ++
    "cons(f1(car(x)),f0(cdr(x))) end in " ++
    "f0(cons(cons(3,cons(3,nil)),cons(cons(3,nil),nil))) end $"

-- mostra un esempio di funzione che restituisce una funzione locale
f = "let f1 = lambda () letrec f2 = lambda (z) if eq(z,1) then 1 " ++
    "else z*f2(z-1) in f2 end in let x = f1 () in x(8) end end $"

-- esempio di una chiusura
g = "let f = lambda(a b) a + b in f end $"

h = "let x = let y = 3 in letrec x = y+1 and f = lambda(z) z+x in f end end in x(2) end $"

