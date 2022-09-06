from individuo_tsp import *

class Annealing:
    def __init__(self):
        self.current=None
        self.best=None
        self.T0=4000
        self.t=1
    
    def anneal(self):
        s=Individuo_tsp()
        s.evaluar()
        self.current=s
        self.best=s
        self.t=1
        while True:
            next=s.mutar()
            next.evaluar()
            p=random.uniform(0,1)
            if (p>min(1,exp()))
