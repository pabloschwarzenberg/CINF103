from individuo_tsp import *
from math import exp,log

class Annealing:
    def __init__(self,T0=1000):
        self.current=None
        self.best=None
        self.T0=T0
        self.T=self.T0
        self.t=1
        self.ni=0
    
    def resolver(self):
        s=Individuo_tsp()
        #s.genotipo=[12,5,4,3,14,7,13,8,1,2,9,11,10,6]
        s.evaluar()
        self.current=s
        self.best=s
        self.T=self.T0
        self.t=1
        self.ni=0
        while self.ni<100000:
            next=self.current.generar_vecino()
            next.evaluar()
            delta=next.fitness-self.current.fitness
            if delta<0:
                self.current=next
            else:
                p=random.uniform(0,1)
                pa=min(1,exp(-delta/self.T))
                if p<pa:
                    self.current=next
            if self.current.fitness < self.best.fitness:
                self.best=self.current
                self.ni=0
                print(self.t," ",self.T," ",self.current.fitness," ",self.best.fitness)
            else:
                self.ni+=1
            self.t=self.t+1
            self.T=self.T0/log(self.t+1)
            if self.t % 1000 == 0:
                print(self.t," ",self.T," ",self.current.fitness," ",self.best.fitness)
        return self.best

metaheuristica=Annealing()
solucion=metaheuristica.resolver()
print(solucion.genotipo)