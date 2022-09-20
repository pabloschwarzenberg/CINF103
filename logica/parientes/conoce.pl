conoce(juan,camilo).
conoce(alex,camilo).
conoce(juan,alex).
es_conocido(X,Y) :- conoce(X,Y);conoce(Y,X).

