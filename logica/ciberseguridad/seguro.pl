contiene(ejemplo_com,formulario).
contiene(formulario,campo(nombre)).
contiene(formulario,campo(usuario)).
vulnerable(sql_injection,campo(usuario)).

inseguro(X):-contiene(X,Y),vulnerable(_,Y).
inseguro(X):-contiene(X,Y),inseguro(Y).
