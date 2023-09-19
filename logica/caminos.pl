link(a,b).
link(b,c).
path(X,Y):-link(X,Y).
path(X,Y):-path(X,Z),link(Z,Y).