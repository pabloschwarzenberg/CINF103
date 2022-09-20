from pyswip import Prolog
prolog = Prolog()
prolog.consult("familia.pl")
for res in prolog.query("padre(hernan,X)."):
    print(res)
#para agregar un hecho
print("Agregamos un hecho")
prolog.assertz("hija(patricia,hernan)")
for res in prolog.query("padre(hernan,X)."):
    print(res)