import tsplib95
import random
import networkx as nx
from individuo import *

class Individuo_tsp(Individuo):
    def __init__(self):
        super(Individuo_tsp,self).__init__()
        self.problem  = tsplib95.load('burma14.tsp')
        self.ciudades = 14
        self.genotipo = [i for i in range(1,self.ciudades+1)]
        random.shuffle(self.genotipo)

    def evaluar(self):
        costo_total=0
        i=0
        while i<self.ciudades:
            zi=self.genotipo[i]
            if(i==self.ciudades-1):
                zj=self.genotipo[0]
            else:
                zj=self.genotipo[i+1]
            costo=self.problem.get_weight(zi,zj)
            costo_total=costo_total+costo
            i=i+1
        self.fitness=costo_total
        return costo_total

    def mutar(self):
        i=random.randint(0,self.ciudades-1)
        j=random.randint(0,self.ciudades-1)
        aux=self.genotipo[i]
        self.genotipo[i]=self.genotipo[j]
        self.genotipo[j]=aux

    def cruzar(self,other):
        hijo=[0]*self.ciudades
        j=random.randint(0,self.ciudades-1)
        i=0
        while i<self.ciudades:
            if i<j:
                if self.genotipo[i] not in hijo:
                    hijo[i]=self.genotipo[i]
            else:
                if other.genotipo[i] not in hijo:
                    hijo[i]=other.genotipo[i]
            i=i+1
        nuevo=Individuo_tsp()
        nuevo.genotipo=hijo
        nuevo.reparar()
        return nuevo

    def reparar(self):
        for i in range(1,self.ciudades+1):
            if i not in self.genotipo:
                p=self.genotipo.index(0)
                self.genotipo[p]=i           

    def generar_vecino(self):
        nuevo=Individuo_tsp()
        nuevo.genotipo=self.genotipo
        nuevo.mutar()
        return nuevo

if __name__ == "__main__":
    i=Individuo_tsp()
    print(i.evaluar())