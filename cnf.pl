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
Leyes para la negacion
NOTA: Al utilizarlas en el programa, se obtiene de manera automatica
la forma normal conjuntiva
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
neg(P, ~P):-
    atomic(P).
neg(~P, P):-
    atomic(P).
neg(P^Q, Res1 v Res2):-
    neg(P, Res1),
    neg(Q, Res2).
neg(P v Q, Res1 ^ Res2):-
    neg(P, Res1),
    neg(Q, Res2).
/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Paso 1. Eliminacion de la implicacion
IMPL_FREE(/phi). Devuelve una formula equivalente sin implicaciones.
Basado en la ley de Morgan, p --> q iff p ^ ~q
Se aplica de manera recursiva sobre cada elemento de /phi
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

implFree(P, P) :-
    atomic(P).

implFree(~P, ~P) :-
    atomic(P).

implFree(P ^ Q, Res1 ^ Res2):-
    implFree(P, Res1),
    implFree(Q, Res2).

implFree(P v Q, Res1 v Res2):-
    implFree(P, Res1),
    implFree(Q, Res2).
    
implFree(X --> Y, ~Res1 v Res2) :-
    implFree(X, Res1),
    implFree(Y, Res2).

% ?- implFree(~p ^ q --> p ^ (r --> q), R). 
%@ R = ~ (~p^q)v p^(~r v q).




