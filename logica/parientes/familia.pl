masculino(hernan).
femenino(lorena).
femenino(eloisa).
femenino(carmen).
femenino(teresa).
hija(eloisa,lorena).
hija(eloisa,hernan).
hija(lorena,teresa).
hijo(hernan,carmen).
abuela(X,Y) :- femenino(X),madre(X,Z),padre(Z,Y).
abuela(X,Y) :- femenino(X),madre(X,Z),madre(Z,Y).
madre(X,Y) :- femenino(X),hija(Y,X).
madre(X,Y) :- femenino(X),hijo(Y,X).
padre(X,Y) :- masculino(X),hija(Y,X).
padre(X,Y) :- masculino(X),hijo(Y,X).