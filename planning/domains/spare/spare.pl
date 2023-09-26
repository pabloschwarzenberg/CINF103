:- dynamic en/2.

neumatico(repuesto).
neumatico(pinchado).
en(pinchado,eje).
en(repuesto,maletero).
quitar(X,Y):-neumatico(X),en(X,Y),retract(en(X,Y)),assert(en(X,suelo)),assert(en(nada,Y)).
poner(X,Y):-neumatico(X),not(en(X,Y)),en(nada,Y),en(X,suelo),retract(en(X,suelo)),
            retract(en(nada,Y)),assert(en(X,Y)).

reparar :- en(pinchado,eje),
quitar(repuesto,_),
quitar(_,eje),
poner(repuesto,eje).