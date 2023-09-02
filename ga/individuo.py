class Individuo:
    def __init__(self):
        self.genotipo=[]
        self.fenotipo=[]
        self.fitness=1
        self.crear()

    def __str__(self):
        return " ".join(list(map(str,self.genotipo)))+" = "+str(self.fitness)

    def __lt__(self,other):
        return self.fitness < other.fitness

    def crear(self):
        pass
    
    def evaluar(self):
        pass

    def mutar(self):
        pass

    def cruzar(self,other):
        pass