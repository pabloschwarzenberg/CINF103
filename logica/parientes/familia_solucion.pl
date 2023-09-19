masculino(hernan).
masculino(pedro).
masculino(matias).
femenino(lorena).
femenino(eloisa).
femenino(carmen).
femenino(teresa).
femenino(monica).
hija(eloisa,lorena).
hija(eloisa,hernan).
hija(lorena,teresa).
hija(carmen,pedro).
hija(monica,carmen).
hijo(hernan,carmen).
hijo(matias,monica).
hermano(X,Y) :- hijo(X,Z),padre(Z,X),padre(Z,Y).
hermano(X,Y) :- hijo(X,Z),madre(Z,X),madre(Z,Y).   
hermana(X,Y) :- hija(X,Z),padre(Z,X),padre(Z,Y).
hermana(X,Y) :- hija(X,Z),madre(Z,X),madre(Z,Y).
abuela(X,Y) :- femenino(X),madre(X,Z),padre(Z,Y).
abuela(X,Y) :- femenino(X),madre(X,Z),madre(Z,Y).
madre(X,Y) :- femenino(X),hija(Y,X).
madre(X,Y) :- femenino(X),hijo(Y,X).
padre(X,Y) :- masculino(X),hija(Y,X).
padre(X,Y) :- masculino(X),hijo(Y,X).
tia(X,Y) :- hermana(X,Z),padre(Z,Y).
tia(X,Y) :- hermana(X,Z),madre(Z,Y).
tio(X,Y) :- hermano(X,Z),padre(Z,Y).
tio(X,Y) :- hermano(X,Z),madre(Z,Y).