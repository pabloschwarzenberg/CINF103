%Merritt, D. (2017). Building expert systems in Prolog. Springer Science & Business Media.
:- dynamic relacion/3,relacion/4.

ask(Atributo,Valor):-
relacion(si,Atributo,Valor),
!.

ask(Atributo,Valor):-
relacion(no,Atributo,Valor),
!,fail.
    
ask(Atributo,Valor):-
write(Atributo:Valor),
write("?(si/no) "),
read(R),
asserta(relacion(R,Atributo,Valor)),
R==si.

ask(Atributo,Objeto,Valor,_):-
relacion(si,Atributo,Objeto,X),
X==Valor,
!.

ask(Atributo,Objeto,Valor,_):-
relacion(si,Atributo,Objeto,X),
X\=Valor,
!,fail.
    
ask(Atributo,Objeto,Valor,Opciones):-
write(Atributo),
write(" de "),
write(Objeto),
write(" es "),
write(Opciones),
write("?"),
read(R),
(member(R,Opciones) -> asserta(relacion(si,Atributo,Objeto,R)),R==Valor; writeln("Opción desconocida"),ask(Atributo,Objeto,Valor,Opciones)).

clase(X):-ask(clase,X).
tiene(X):-ask(tiene,X).
moteado(X):-ask(moteado,X).
rayas_transversales(X):-ask(rayas_transversales,X).
bandas(X):-ask(bandas,X).
color(X,Y):-ask(color,X,Y,[blanco,castano,cafe]).
forma(X,Y):-ask(forma,X,Y,[corazon]).

identificar:-
retractall(relacion(_,_,_)),
retractall(relacion(_,_,_,_)),
especie(X),
write(X).

especie(chuncho_austral) :- clase(ave),moteado(alas),bandas(cola),color(bandas(cola),castano).
especie(chuncho_nortino) :- clase(ave),moteado(alas),bandas(cola),color(bandas(cola),blanco).
sespecie(lechuza) :- clase(ave),tiene(disco_facial),forma(disco_facial,corazon).
especie(tucuquere) :- clase(ave),tiene(penachos),not(tiene(dedos_emplumados)).
especie(nuco) :- clase(ave),tiene(penachos),tiene(dedos_emplumados).
especie(concon) :- clase(ave),rayas_transversales(pecho).
especie(pequen) :- clase(ave),moteado(plumaje).