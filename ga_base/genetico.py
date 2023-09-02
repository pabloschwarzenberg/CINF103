import random
import heapq
from individuo import *

class AlgoritmoGenetico:
    def __init__(self,breed_function,stop_function=lambda x: x.generacion<x.generaciones,n=100,p=0.1,g=100):
        self.poblacion=[]
        self.mejor=None
        self.p=p
        self.breed_function=breed_function
        self.stop_function=stop_function
        self.n=n
        self.generacion=0
        self.generaciones=g
        self.media=0
        i=0
        while i<n:
            x=breed_function()
            x.evaluar()
            self.media+=x.fitness
            if self.mejor is None or self.mejor.fitness>=x.fitness:
                self.mejor=x
            self.poblacion.append(x)
            i=i+1
        self.media=self.media/len(self.poblacion)

    def seleccion(self):
        torneo=[]
        for i in range(5):
            x=random.choice(self.poblacion)
            heapq.heappush(torneo,(x.fitness,x))
        x=heapq.heappop(torneo)[1]
        y=heapq.heappop(torneo)[1]
        return x,y

    def crear_generacion(self):
        poblacion=[]
        poblacion.append(self.mejor)
        i=1
        self.media=self.mejor.fitness
        while i < len(self.poblacion):
            x,y=self.seleccion()
            z=x.cruzar(y)
            q=random.uniform(0,1)
            if q<self.p:
                z.mutar()
            z.evaluar()
            self.media+=z.fitness
            if z.fitness <= self.mejor.fitness:
                self.mejor=z
            poblacion.append(z)
            i=i+1
        self.poblacion=poblacion
        self.media=self.media/len(self.poblacion)

    def evolucionar(self):
        archivo=open("evolution.csv","w")
        self.generacion=0
        while not self.stop_function(self):
            log=[self.generacion,self.mejor,self.mejor.fitness,self.media]
            archivo.write(";".join(list(map(str,log)))+"\n")
            print("Generacion ",self.generacion," ",self.mejor," ",self.media)
            self.crear_generacion()
            self.generacion+=1
        print("Generacion ",self.generacion," ",self.mejor," ",self.media)
        log=[self.generacion,self.mejor,self.mejor.fitness,self.media]
        archivo.write(";".join(list(map(str,log)))+"\n")
        archivo.close()