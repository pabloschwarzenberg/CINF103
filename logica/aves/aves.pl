:- dynamic disco_facial_corazon/1,penachos/1,rayas_transversales/1,rayas_verticales/1,moteado/1,emplumados/1,forma/2,estrigiforme/1.

especie(X,lechuza) :- ave(X),forma(disco_facial(X),corazon).
especie(X,tucuquere) :- ave(X),penachos(X),not(emplumados(dedos(X))).
especie(X,nuco) :- ave(X),penachos(X),emplumados(dedos(X)).
especie(X,concon) :- ave(X),rayas_transversales(pecho(X)).
especie(X,pequen) :- ave(X),moteado(plumaje(X)).
especie(X,chuncho_austral) :- ave(X),moteado(alas(X)),cafe(bandas(cola(X))),castano(bandas(cola(X))).
especie(X,chuncho_nortino) :- ave(X),moteado(alas(X)),cafe(bandas(cola(X))),blanco(bandas(cola(X))).

ave(x).
moteado(plumaje(x)).

% assert(ave(x))
% assert(disco_facial(x)).
% assert(forma(disco_facial(x),corazon)).
% que_es(x).