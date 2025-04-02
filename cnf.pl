/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Ulises Jimenez Guerrero. Universidad Veracruzana. Maestria en IA.

Implementacion del algoritmo CNF visto en clase de RC, capitulo 4.
Basado en la descripcion en el libro  Logic in Computer Science: Modelling 
and Reasoning about Systems, de M. Huth y M. Ryan. 
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Declaracion de los operadores logicos
Declaramos los operadores de negacion,
conjuncion, disyuncion e implicacion.
Se utiliza la precedencia clasica, donde el menor
valor tiene mayor precedencia
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
:- op(700, xfy, =>). % Implicacion
:- op(500, xfy, v). % Disyuncion
:- op(500, xfy, ^). % Conjuncion
:- op(400, fx, ~). % Negacion 
/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Predicado esLiteral/2 para verificar si un termino es literal:
 atomo o negacion de atomo. 
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
esLiteral(P, P) :-
    atomic(P).

esLiteral(~P, ~P):-
    atomic(P).
/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Paso 1. Eliminacion de la implicacion en una fbf.
implFree/2. Devuelve una formula equivalente sin implicaciones.
Basado en la equivalencia p --> q iff p ^ ~q
Se aplica de manera recursiva sobre cada elemento de la fbf.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

implFree(P, Res) :- %% Caso base. Literal.
    esLiteral(P, Res).

%% Casos compuestos. Disyuncion y conjuncion. Se elimina la
%% implicacion en cada miembro
implFree(P v Q, Res):- %% Disyuncion
    implFree(P, Res1), 
    implFree(Q, Res2),
    Res = (Res1 v Res2).


implFree(P ^ Q, Res):- %% Conjuncion
    implFree(P, Res1), 
    implFree(Q, Res2),
    Res = (Res1 ^ Res2).

implFree(~P, ~Res):-  %% Caso para negacion de formula compuesta.
    compound(P),
    implFree(P, Res).

%% Casos con implicacion. Uso de la ley de Morgan, se elimina
%% implicacion en cada miembro resultante.
implFree(P => Q, Res) :- %% Resultado de la forma ~p v q
    implFree(~P, Res1), 
    implFree(Q, Res2), 
    Res = (Res1 v Res2).

% ?- implFree(~p ^ q => p ^ (r => q), R).
%@ R = ~ (~p^q)v p^ ~r v q.

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Paso 2. Forma normal bajo negacion NNF. 
nnf/2. Devuelve la fbf de tal forma que solamente se niegan 
atomos, no formulas compuestas. Necesita una formula sin implicaciones. 
Las literales se mantienen intactas. Se evalua cada elemento de formulas 
compuestas no negadas. Se utilizan las leyes de Morgan para formulas
compuestas negadas.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
 
nnf(P, Res) :-  %% Caso base. Literal.
    esLiteral(P, Res).

nnf(~(~P), P). %% Caso especial. Doble negacion  

%% Casos compuestos. Implicacion y disyuncion afirmadas.
nnf(P^Q, Res) :-
    nnf(P, Res1),
    nnf(Q, Res2),
    Res = (Res1^Res2).

nnf(P v Q, Res) :-
    nnf(P, Res1),
    nnf(Q, Res2),
    Res = (Res1 v Res2).

%% Conjunciones y disyunciones negadas. Leyes de Morgan.
nnf(~(P^Q), Res) :- %% ~(p^q) iff ~p v ~q
    nnf(~P, Res1), %% ~p
    nnf(~Q, Res2), %% ~q
    Res = (Res1 v Res2). %% ~p v ~q

nnf(~(P v Q), Res) :- %% ~(pvq) iff ~p^~q
    nnf(~P, Res1), %% ~p
    nnf(~Q, Res2), %% ~q
    Res = (Res1^Res2). %% ~p^~q

%% ?- nnf(~ (~p^q)v p^(~r v q), NNF). 
%@ NNF = (p v ~q)v p^(~r v q) ;
%@ false.


/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Paso 3. CNF y distribucion de las conjunciones.
Funcion principal cnf/2, tipo interfaz. LLama a las otras funciones 
definidas anteriormente: impl_free, nnf y a su vez una nueva funcion 
distr/3, que se encarga de distribuir las conjunciones de manera adecuada.
Toma como entrada una formula bien formada en logica proposicional y 
regresa una forma equivalente en CNF. El trabajo principal lo hace 
cnfAux/2.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

cnf(Phi, Res):- %% Interfaz. Pide la fbf y devuelve su equivalente Res.
    implFree(Phi, Res1),
    nnf(Res1, Res2),
    cnfAux(Res2, Res), !. %% Corte. Se comenta al final.

cnfAux(P, Res):- %% Funcion auxiliar. Caso base con literal. 
    esLiteral(P, Res).

cnfAux(P1^P2, Res) :- %% Conjuncion. Aplicar recursivamente a 
    cnfAux(P1, Res1), %% cada elemento.
    cnfAux(P2, Res2),
    Res = (Res1 ^ Res2).

cnfAux(P1 v P2, Res):-  %% Disyuncion.Aplicar cnfAux/2 a cada elemento 
    cnf(P1, Res1),   %% y distribuir la disyuncion con distr/3.
    cnf(P2, Res2),
    distr(Res1, Res2, Res).

distr((P1 ^ P2), Q, Res):-  %% Caso 1, el primer elemento es una conjuncion.
    distr(P1, Q, Res1),   %% Se ditribuye (p^q) v r iff (p v r)^(q v r).
    distr(P2, Q, Res2),   %% A su vez, estos se distribuyen recursivamente.
    Res = (Res1 ^ Res2).

distr(P, Q1 ^ Q2, Res) :- %% Caso 2, el segundo elemento es una conjuncion.
    distr(P, Q1, Res1),   %% Se distribuye p v (q^r) iff (p v q)^(p v r).
    distr(P, Q2, Res2),   %% Se aplica recursivamente.
    Res = (Res1 ^ Res2).

distr(P, Q, (P v Q)).  %% Caso 3. Sin conjuncion, se une con disyuncion.

% ?- cnf(~p ^ q => p ^ (r => q), CNF).
%@ CNF = ((p v ~q)v p)^(p v ~q)v~r v q.

% ?- cnf(r => (s => (t ^ s => r)), CNF).
%@ CNF = ~r v ~s v (~t v ~s)v r.

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
La funcion distr/3 presenta un comportamiento ineficaz, donde es incapaz de
determinar de manera correcta el operador principal. Esto ocasiona que Prolog
reconsidere tomando diferentes operadores principales. Por lo tanto, solamente
el primer resultado es correcto, lo que lleva a incluir un corte. Esto es un
error de implementacion, que no se ha logrado corregir.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
