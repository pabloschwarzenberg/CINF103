depredador(X):-mamifero(X),alimenta(X,Y),presa(Y).
presa(X):-animal(X).
animal(X):-mamifero(X).
mamifero(leon).
mamifero(cebra).
alimenta(leon,cebra).
