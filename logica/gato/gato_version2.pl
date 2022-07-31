:-initialization(inicio).

inicio:- write('\n'),turno([0,0,0,0,0,0,0,0,0],o).

turno(Tablero,o):-seguir(Tablero),\+ ganador(Tablero,x),mostrar(Tablero),jugar(Tablero,o,TS),turno(TS,x).
turno(Tablero,o):-seguir(Tablero),   ganador(Tablero,x),mostrar(Tablero),gana_gato,!.
turno(Tablero,x):-seguir(Tablero),\+ ganador(Tablero,o),mostrar(Tablero),jugar(Tablero,x,TS),turno(TS,o).
turno(Tablero,x):-seguir(Tablero),   ganador(Tablero,o),mostrar(Tablero),gana_raton,!.
turno(Tablero,o):-not(seguir(Tablero)),ganador(Tablero,o),gana_raton,!.
turno(Tablero,x):-not(seguir(Tablero)),ganador(Tablero,x),gana_gato,!.
turno(Tablero,_):-not(seguir(Tablero)), \+ ganador(Tablero,x),\+ ganador(Tablero,o),mostrar(Tablero),empate,!.

seguir([A11,A12,A13,A21,A22,A23,A31,A32,A33]):-A11=0;A12=0;A13=0;A21=0;A22=0;A23=0;A31=0;A32=0;A33=0.

ganador([A11,A12,A13,_,_,_,_,_,_],Jugador):-A11=Jugador,A11=A12,A12=A13.
ganador([_,_,_,A21,A22,A23,_,_,_],Jugador):-A21=Jugador,A21=A22,A22=A23.
ganador([_,_,_,_,_,_,A31,A32,A33],Jugador):-A31=Jugador,A31=A32,A32=A33.
ganador([A11,_,_,A21,_,_,A31,_,_],Jugador):-A11=Jugador,A11=A21,A21=A31.
ganador([_,A12,_,_,A22,_,_,A32,_],Jugador):-A12=Jugador,A12=A22,A22=A32.
ganador([_,_,A13,_,_,A23,_,_,A33],Jugador):-A13=Jugador,A13=A23,A23=A33.
ganador([A11,_,_,_,A22,_,_,_,A33],Jugador):-A11=Jugador,A11=A22,A22=A33.
ganador([_,_,A13,_,A22,_,A31,_,_],Jugador):-A31=Jugador,A31=A22,A22=A13.

empate:-write('Empate!\n').
gana_raton:-write('Gana el raton!\n').
gana_gato:-write('Gana el gato!\n').

mostrar(X):-mostrar(X,1).
mostrar(X,I):-mod(I,3)=\=0,nth1(I,X,Y),write(' '),write(Y),write(' |'),J is I+1,mostrar(X,J).
mostrar(X,I):-mod(I,3)=:=0,I=\=9,nth1(I,X,Y),write(' '),write(Y),write('\n---|---|---\n'),J is I+1,mostrar(X,J).
mostrar(X,I):-I=:=9,nth1(I,X,Y),write(' '),write(Y),write('\n\n'),!.

jugar(X,Y,NX):-write('Fila:\n'),read(I),write('Columna:\n'),read(J),mover(X,I,J,Y,NX).

mover([0,A12,A13,A21,A22,A23,A31,A32,A33],1,1,Y,TableroModificado):-TableroModificado=[Y,A12,A13,A21,A22,A23,A31,A32,A33].
mover([A11,0,A13,A21,A22,A23,A31,A32,A33],1,2,Y,TableroModificado):-TableroModificado=[A11,Y,A13,A21,A22,A23,A31,A32,A33].
mover([A11,A12,0,A21,A22,A23,A31,A32,A33],1,3,Y,TableroModificado):-TableroModificado=[A11,A12,Y,A21,A22,A23,A31,A32,A33].
mover([A11,A12,A13,0,A22,A23,A31,A32,A33],2,1,Y,TableroModificado):-TableroModificado=[A11,A12,A13,Y,A22,A23,A31,A32,A33].
mover([A11,A12,A13,A21,0,A23,A31,A32,A33],2,2,Y,TableroModificado):-TableroModificado=[A11,A12,A13,A21,Y,A23,A31,A32,A33].
mover([A11,A12,A13,A21,A22,0,A31,A32,A33],2,3,Y,TableroModificado):-TableroModificado=[A11,A12,A13,A21,A22,Y,A31,A32,A33].
mover([A11,A12,A13,A21,A22,A23,0,A32,A33],3,1,Y,TableroModificado):-TableroModificado=[A11,A12,A13,A21,A22,A23,Y,A32,A33].
mover([A11,A12,A13,A21,A22,A23,A31,0,A33],3,2,Y,TableroModificado):-TableroModificado=[A11,A12,A13,A21,A22,A23,A31,Y,A33].
mover([A11,A12,A13,A21,A22,A23,A31,A32,0],3,3,Y,TableroModificado):-TableroModificado=[A11,A12,A13,A21,A22,A23,A31,A32,Y].