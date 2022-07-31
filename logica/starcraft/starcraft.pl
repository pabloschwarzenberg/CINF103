:-dynamic ruido/1.
celda(1,1).
celda(1,2).
celda(1,3).
celda(1,4).
celda(2,1).
celda(2,2).
celda(2,3).
celda(2,4).
celda(3,1).
celda(3,2).
celda(3,3).
celda(3,4).
celda(4,1).
celda(4,2).
celda(4,3).
celda(4,4).
not(ruido(celda(1,1))).
not(ruido(celda(2,1))).
ruido(celda(2,4)).
ruido(celda(3,3)).
ruido(celda(4,4)).
zerg(celda(X,Y)):-N is X-1,S is X+1,L is Y-1,R is Y+1,(
(N >= 0,S =< 4,L >= 0,R =< 4,ruido(celda(N,Y)),ruido(celda(S,Y)),ruido(celda(X,L)),ruido(celda(X,R)));
(N < 0,S =< 4,L >= 0,R =< 4,ruido(celda(S,Y)),ruido(celda(X,L)),ruido(celda(X,R)));
(N >= 0,S > 4,L >= 0,R =< 4,ruido(celda(N,Y)),ruido(celda(X,L)),ruido(celda(X,R)));
(N >= 0,S =< 4,L < 0,R =< 4,ruido(celda(N,Y)),ruido(celda(S,Y)),ruido(celda(X,R)));
(N >= 0,S =< 4,L >= 0,R > 4,ruido(celda(N,Y)),ruido(celda(S,Y)),ruido(celda(X,L)))).


