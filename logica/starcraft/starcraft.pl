:- dynamic ruido/2,visitada/2,zerg/2.

segura(X,Y):-visitada(X,Y).

segura(X,Y):-not(zerg(X,Y)),
U is X-1,D is X+1,L is Y-1,R is Y+1,
(visitada(U,Y);
visitada(D,Y);
visitada(X,L);
visitada(X,R)).

zerg(X,Y):-ruido(X,Y),
U is X-1,D is X+1,L is Y-1,R is Y+1,
(X>1->ruido(U,Y),!;true,!),
(X<4->ruido(D,Y),!;true,!),
(Y>1->ruido(X,L),!;true,!),
(Y<4->ruido(X,R),!;true,!).

visitada(4,1).