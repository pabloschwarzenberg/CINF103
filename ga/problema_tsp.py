from individuo_tsp import Individuo_tsp
from genetico import *

ga=AlgoritmoGenetico(lambda: Individuo_tsp(),
stop_function=lambda x: x.generacion>x.generaciones,
n=5000,
p=0.1,
g=200)
ga.evolucionar()