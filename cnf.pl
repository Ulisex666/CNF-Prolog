/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Ulises Jimenez Guerrero. Universidad Veracruzana. Maestria en IA.

Implementacion del algoritmo CNF visto en clase de RC, capitulo 4.
Basado en la descripcion en el libro  Logic in Computer Science: Modelling 
and Reasoning about Systems, de M. Huth y M. Ryan. 
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Declaracion de los operadores logicos
Declaramos los operadores de negacion, conjuncion, disyuncion e implicacion.
Se utiliza el orden clasico. En Prolog el menor valor tiene mayor 
precedencia
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
:- op(500, fy, ~). % Negacion 
:- op(600, xfy, ^). % Conjuncion
:- op(610, xfy, v). % Disyuncion
:- op(650, xfy, -->). % Implicacion
/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Predicado esLiteral/2 para decidir si una formula es literal o no. Esto
se cumple si es un atomo o una negacion de atomo.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
esLiteral(P):-
    atomic(P).

esLiteral(~P):-
    atomic(P).
/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Paso 1. Eliminacion de la implicacion en una fbf.
implFree/2. Devuelve una formula equivalente sin implicaciones.
Basado en la equivalencia p --> q iff p ^ ~q
Se aplica de manera recursiva sobre cada elemento de la fbf.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
implFree(P, P) :- %% Caso base. Literal.
    esLiteral(P).

implFree(~P, ~Res) :- %% Negacion de fbf. Aplicacion recursiva.
    compound(P),
    implFree(P, Res).

%% Casos compuestos. Disyuncion y conjuncion. Se elimina la
%% implicacion en cada miembro
implFree(P ^ Q, Res1 ^ Res2):- %% Conjuncion
    implFree(P, Res1), 
    implFree(Q, Res2). 

implFree(P v Q, Res1 v Res2):- %% Disyuncion
    implFree(P, Res1), 
    implFree(Q, Res2). 
%% Casos con implicacion. Uso de la ley de Morgan, se elimina
%% implicacion en cada miembro resultante
implFree(P --> Q, Res) :- %% Resultado de la forma ~p v q
    implFree(P, Res1), 
    implFree(Q, Res2), 
    Res = (~Res1 v Res2).

% ?- implFree(~p ^ q --> p ^ (r --> q), R). 
%@ R = ~ (~p^q)v p^(~r v q) ;
%@ false.
/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Paso 2. Forma normal bajo negacion NNF. 
nnf/2. Devuelve la fbf de tal forma que solamente se niegan 
atomos, no formulas compuestas. Necesita una formula sin implicaciones. 
Las literales se mantienen intactas. Se evalua cada elemento de formulas 
compuestas no negadas. Se utilizan las leyes de Morgan para formulas
compuestas negadas.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
nnf(~(~P), P). %% Doble negacion.

nnf(P, P) :-  %% Caso base. Literal.
    esLiteral(P).
%% Casos compuestos. Implicacion y disyuncion NO negadas.
nnf(P^Q, Res1^Res2) :-
    nnf(P, Res1),
    nnf(Q, Res2).

nnf(P v Q, Res1 v Res2) :-
    nnf(P, Res1),
    nnf(Q, Res2).
%% Conjunciones y disyunciones negadas. Leyes de Morgan.
nnf(~(P^Q), Res) :- %% ~(p^q) iff ~p v ~q
    nnf(~P, Res1), %% ~p
    nnf(~Q, Res2), %% ~q
    Res = Res1 v Res2. %% ~p v ~q

nnf(~(P v Q), Res) :- %% ~(pvq) iff ~p^~q
    nnf(~P, Res1), %% ~p
    nnf(~Q, Res2), %% ~q
    Res = Res1^Res2. %% ~p^~q

%% ?- nnf((~ (~p^q)v p^(~r v q)), NNF). 
%@ NNF = (p v ~q)v p^(~r v q) ;
%@ false.
/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
Paso 3. CNF y distribucion de las conjunciones.
Funcion principal cnf/2, tipo interfaz. LLama a las otras funciones definidas
anteriormente: impl_free/2, nnf/2 y a su vez una nueva funcion 
distr/3, que se encarga de distribuir las conjunciones de manera adecuada.
 Toma como entrada una formula bien formada en logica proposicional y 
regresa una forma equivalente en CNF. El trabajo principal lo hace cnfAux/2.
 - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
cnf(Phi, Res):- %% Interfaz. Pide la fbf y devuelve su equivalente Res.
    implFree(Phi, Res1),
    nnf(Res1, Res2),
    cnfAux(Res2, Res), !. %% Corte. Se comenta al final.

cnfAux(P, P):- %% Funcion auxiliar. Caso base. Literal 
    esLiteral(P).

cnfAux(P1^P2, Res1 ^ Res2) :- %% Cojuncion. Aplicar recursivamente a 
    cnfAux(P1, Res1),           %% cada elemento.
    cnfAux(P2, Res2).

cnfAux(P1 v P2, Res):-  %% Disyuncion.Aplicar cnfAux/2 a cada elemento 
    cnfAux(P1, Res1),     %% y distribuir la disyuncion con distr/3.
    cnfAux(P2, Res2),
    distr(Res1, Res2, Res).

distr(P, Q, Res):-  %% Caso 1, el primer elemento es una conjuncion.
    P = P1 ^ P2,         %% Se ditribuye (p^q) v r iff (p v r)^(q v r).
    distr(P1, Q, Res1), %% A su vez, estos se distribuyen recursivamente.
    distr(P2, Q, Res2),
    Res = Res1 ^ Res2.

distr(P, Q, Res) :- %% Caso 2, el segundo elemento es una conjuncion.
    Q = Q1 ^ Q2,         %% Se distribuye p v (q^r) iff (p v q)^(p v r).
    distr(P, Q1, Res1), %% Se aplica recursivamente.
    distr(P, Q2, Res2),
    Res = Res1 ^ Res2.

distr(P, Q, P v Q). %% Caso 3. Salida. Ningun elemento tiene disyunciones.
    
% ?- cnf(~p ^ q --> p ^ (r --> q), CNF).
%@ CNF = ((p v ~q)v p)^((p v ~q)v~r v q).

% ?- cnf(r --> (s --> (t ^ s --> r)), CNF).
%@ CNF = ~r v ~s v (~t v ~s)v r.
/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
NOTA SOBRE USO DEL CORTE: Despues de analizar el programa, se llego a la
conclusion de que se tiene resultados no deseados dada la forma en que se
definieron los operadores y la funcion distr/2. Prolog no logra reconocer
de forma adecuada los operadores principales, por lo que hace backtracking
intentado otras formas de separar la formula y da otros resultados 
incorrectos.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
