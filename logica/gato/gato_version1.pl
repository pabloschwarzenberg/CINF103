:-dynamic a/1,b/1,c/1,d/1,e/1,f/1,g/1,h/1,i/1.

:-initialization(inicio).

inicio:- retractall(a(_)),retractall(b(_)),retractall(c(_)),
retractall(d(_)),retractall(e(_)),retractall(f(_))
,retractall(g(_)),retractall(h(_)),retractall(i(_)),
assert(a(0)),assert(b(0)),assert(c(0)),assert(d(0)),assert(e(0)),assert(f(0)),assert(g(0)),assert(h(0)),assert(i(0)),
turno(o).

mostrar:-a(A),b(B),c(C),d(D),e(E),f(F),g(G),h(H),i(I),
write(A),write(' | '),write(B),write(' | '),write(C),write('\n'),
write('------\n'),
write(D),write(' | '),write(E),write(' | '),write(F),write('\n'),
write('------\n'),
write(G),write(' | '),write(H),write(' | '),write(I),write('\n'),
write('\n').

jugar(Y):-write('Fila:\n'),read(I),write('Columna:\n'),read(J),mover(I,J,Y).

mover(1,1,P):-retract(a(0)),assert(a(P)).
mover(1,2,P):-retract(b(0)),assert(b(P)).
mover(1,3,P):-retract(c(0)),assert(c(P)).
mover(2,1,P):-retract(d(0)),assert(d(P)).
mover(2,2,P):-retract(e(0)),assert(e(P)).
mover(2,3,P):-retract(f(0)),assert(f(P)).
mover(3,1,P):-retract(g(0)),assert(g(P)).
mover(3,2,P):-retract(h(0)),assert(h(P)).
mover(3,3,P):-retract(i(0)),assert(i(P)).

seguir:-a(0);b(0);c(0);d(0);e(0);f(0);g(0);h(0);i(0).

turno(o):-seguir,\+ ganador(x),jugar(o),mostrar,turno(x).
turno(o):-seguir,   ganador(x),gana_gato,!.
turno(x):-seguir,\+ ganador(o),jugar(x),mostrar,turno(o).
turno(x):-seguir,   ganador(o),gana_raton,!.
turno(x):-not(seguir),ganador(x),gana_gato,!.
turno(o):-not(seguir),ganador(o),gana_raton,!.
turno(_):-not(seguir), \+ ganador(x),\+ ganador(o),empate,!.

% a b c
% d e f
% g h i

ganador(P):-a(P),b(P),c(P).
ganador(P):-d(P),e(P),f(P).
ganador(P):-g(P),h(P),i(P).
ganador(P):-a(P),d(P),g(P).
ganador(P):-b(P),e(P),h(P).
ganador(P):-c(P),f(P),i(P).
ganador(P):-a(P),e(P),i(P).
ganador(P):-c(P),e(P),g(P).

empate:-write('Empate!\n').
gana_raton:-write('Gana el raton!\n').
gana_gato:-write('Gana el gato!\n').