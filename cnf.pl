/* Prolog Mode Shortcuts %%
C-c l  -> Insert use_module(library()) 
C-c q  -> Insert comment block 
S-TAB  -> Expand with dabbrev 
F10  -> Consult with ediprolog  */ 
 
/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Declaracion de los operadores logicos
Declaramos los operadores de negacion,
conjuncion, disyuncion e implicacion.
Se utiliza la precedencia clasica, donde el menor
valor tiene mayor precedencia
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

:- op(500, fy, ~). % Negacion 
:- op(600, xfy, ^). % Conjuncion
:- op(610, xfy, v). % Disyuncion
:- op(650, xfy, -->). % Implicacion

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Paso 1. Eliminacion de la implicacion
IMPL_FREE(/phi). Devuelve una formula equivalente sin implicaciones.
Basado en la ley de Morgan, p --> q iff p ^ ~q
Se aplica de manera recursiva sobre cada elemento de /phi
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */


%% Casos base. Una literal ya se encuentra libre de implicaciones.
implFree(P, P) :- %% Atomo
    atomic(P).

implFree(~P, ~P) :- %% Negacion de atomo
    atomic(P).

implFree(~ ~P, P):-
    implFree(P, P).

%% Casos compuestos. Disyuncion y conjuncion. Se elemina la
%% implicacion en cada miembro
implFree(P ^ Q, Res1 ^ Res2):- %% Conjuncion
    implFree(P, Res1), % Recursividad en primer miembro
    implFree(Q, Res2). % Recursividad en segundo miembro

implFree(P v Q, Res1 v Res2):- %% Disyuncion
    implFree(P, Res1), % Recursividad en primer miembro
    implFree(Q, Res2). % Recursividad en segundo miembro

%% Casos con implicacion. Uso de la ley de Morgan, se elimina
%% implicacion en cada miembro resultante
implFree(P --> Q, Res) :- %% Resultado de la forma ~p v q
    implFree(P, Res1), % Recursividad en primer miembro
    implFree(Q, Res2), % Recursividad en segundo miembro
    Res = ~Res1 v Res2.

implFree(~(P --> Q), ~Res) :-
    implFree(P, Res1),
    implFree(Q, Res2),
    Res = ~Res1 v Res2.

% ?- implFree(~p ^ q --> p ^ (r --> q), R). 
%@ R = ~ (~p^q)v p^(~r v q) ;
%@ false.

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Paso 2. Forma normal bajo negacion NNF. 
NNF(IMPLFREE(/phi)). Devuelve la fbf de tal forma que solamente se niegan 
atomos, no formas compuestas. Necesita una formula sin implicaciones. 
Las literales se mantienen intactas. Se evalua cada elemento de formulas 
compuestas no negadas. Se utilizan las leyes de Morgan para formulas
compuestas negadas.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

%% Caso base. Literales. Se devuelve la formula original.
nnf(P, P) :-
    atomic(P).

nnf(~P, ~P) :-
    atomic(P).

nnf(~(~P), Res) :-
    nnf(P, Res).

%% Casos compuestos. Implicacion y disyuncion NO negadas.
nnf(P^Q, Res1^Res2) :-
    nnf(P, Res1),
    nnf(Q, Res2).

nnf(P v Q, Res1 v Res2) :-
    nnf(P, Res1),
    nnf(Q, Res2).

nnf(~(P^Q), Res1 v Res2) :-
    nnf(~P, Res1),
    nnf(~Q, Res2).

nnf(~(P v Q), Res1 ^ Res2) :-
    nnf(~P, Res1),
    nnf(~Q, Res2).

%% ?- implFree(~p ^ q --> p ^ (r --> q), IMPLFREE), nnf(IMPLFREE, NNF). 
%@ IMPLFREE = ~ (~p^q)v p^(~r v q),
%@ NNF = (p v ~q)v p^(~r v q) ;
%@ false.


/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Paso 3. CNF y distribucion de las conjunciones.
CNF((/phi)).
Funcion principal, tipo interfaz. LLama a las otras funciones definidas
anteriormente: impl_free, nnf y a su vez una nueva funcion distr, que se 
encargara de distribuir las conjunciones de manera adecuada, de forma que 
todas las disyunciones esten compuestas por literales. Toma como entrada una 
formula bien formada en logica proposicional y regresa una forma equivalente 
en CNF. El trabajo principal lo hace cnfAux.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

cnf(Phi, Res):-
    implFree(Phi, Res1),
    nnf(Res1, Res2),
    cnfAux(Res2, Res), !.

cnfAux(Psi, Psi):-
    atomic(Psi).

cnfAux(~Psi, ~Psi) :-
    atomic(Psi).

cnfAux(Psi1^Psi2, Res1 ^ Res2) :-
    cnfAux(Psi1, Res1),
    cnfAux(Psi2, Res2).

cnfAux(Psi1 v Psi2, Res):-
    cnfAux(Psi1, Res1),
    cnfAux(Psi2, Res2),
    distr(Res1, Res2, Res).

distr(Eta1, Eta2, Res):-
    Eta1 = P ^ Q,
    distr(P, Eta2, Res1),
    distr(Q, Eta2, Res2),
    Res = Res1 ^ Res2.

distr(Eta1, Eta2, Res) :-
    Eta2 = P ^ Q,
    distr(Eta1, P, Res1),
    distr(Eta1, Q, Res2),
    Res = Res1 ^ Res2.

distr(Eta1, Eta2, Eta1 v Eta2).
    
% ?- cnf(~p ^ q --> p ^ (r --> q), R).
%@ R = ((p v ~q)v p)^((p v ~q)v~r v q). 

% ?- cnf(~p^q --> p^(r --> q), CNF).
%@ CNF = ((p v ~q)v p)^((p v ~q)v~r v q).

% ?- cnf(r --> (s --> (t ^ s --> r)), CNF).
%@ CNF = ~r v ~s v (~t v ~s)v r.
