import random
import heapq

class Individuo:
    def __init__(self):
        self.genotipo=[0,1,2,3,4,5,6,7]
        random.shuffle(self.genotipo)
        self.fenotipo=[]
        self.fitness=1000

    def __str__(self):
        return " ".join(list(map(str,self.genotipo)))+" = "+str(self.fitness)

    def generar_fenotipo(self):
        self.fenotipo=[]
        for i in range(8):
            self.fenotipo.append([0]*8)
        columna=0
        for fila in self.genotipo:
            self.fenotipo[fila][columna]=1
            columna=columna+1

    def revisar_filas(self,fila,columna):
        ataques=0
        i=fila
        j=columna+1
        while j<8:
            if(self.fenotipo[i][j]==1):
                ataques=ataques+1
                break
            j=j+1
        j=columna-1
        while j>=0:
            if(self.fenotipo[i][j]==1):
                ataques=ataques+1
                break
            j=j-1
        return ataques

    def revisar_columnas(self,fila,columna):
        ataques=0
        i=fila+1
        j=columna
        while i<8:
            if(self.fenotipo[i][j]==1):
                ataques=ataques+1
                break
            i=i+1
        i=fila-1
        while i>=0:
            if(self.fenotipo[i][j]==1):
                ataques=ataques+1
                break
            i=i-1
        return ataques

    def revisar_diagonales(self,fila,columna):
        ataques=0
        i=fila+1
        j=columna+1
        while i<8 and j<8:
            if(self.fenotipo[i][j]==1):
                ataques=ataques+1
                break
            i=i+1
            j=j+1
        i=fila-1
        j=columna-1
        while i>=0 and j>=0:
            if(self.fenotipo[i][j]==1):
                ataques=ataques+1
                break
            i=i-1
            j=j-1
        i=fila+1
        j=columna-1
        while i<8 and j>=0:
            if(self.fenotipo[i][j]==1):
                ataques=ataques+1
                break
            i=i+1
            j=j-1
        i=fila-1
        j=columna+1
        while i>=0 and j<8:
            if(self.fenotipo[i][j]==1):
                ataques=ataques+1
                break
            i=i-1
            j=j+1
        return ataques

    def evaluar(self):
        ataques=0
        i=0
        self.generar_fenotipo()
        while i<8:
            fila=self.genotipo[i]
            columna=i
            ataques+=self.revisar_columnas(fila,columna)
            ataques+=self.revisar_filas(fila,columna)
            ataques+=self.revisar_diagonales(fila,columna)
            i=i+1
        self.fitness=ataques
        return ataques

    def __lt__(self,other):
        return self.fitness < other.fitness

    def mutar(self):
        i=random.randint(0,7)
        self.genotipo[i]=random.randint(0,7)

    def cruzar(self,other):
        hijo=[0]*8
        j=random.randint(0,7)
        i=0
        while i<8:
            if i<j:
                hijo[i]=self.genotipo[i]
            else:
                hijo[i]=other.genotipo[i]
            i=i+1
        nuevo=Individuo()
        nuevo.fenotipo=hijo
        return nuevo

class AlgoritmoGenetico:
    def __init__(self,n=50,p=0.1):
        self.poblacion=[]
        self.mejor=None
        self.p=p
        i=0
        while i<n:
            x=Individuo()
            x.evaluar()
            if self.mejor is None or self.mejor.fitness>x.fitness:
                self.mejor=x
            self.poblacion.append(x)
            i=i+1

    def seleccion(self):
        torneo=[]
        for i in range(5):
            x=random.choice(self.poblacion)
            heapq.heappush(torneo,(x.fitness,x))
        x=heapq.heappop(torneo)[1]
        y=heapq.heappop(torneo)[1]
        return x,y

    def crear_generacion(self):
        i=0
        poblacion=[]
        while i < len(self.poblacion):
            x,y=self.seleccion()
            z=x.cruzar(y)
            q=random.uniform(0,1)
            if q<self.p:
                z.mutar()
            z.evaluar()
            if z.fitness < self.mejor.fitness:
                self.mejor=z
            poblacion.append(z)
            i=i+1
        self.poblacion=poblacion

    def evolucionar(self):
        generacion=0
        while generacion<100:
            print("Generacion ",generacion," ",self.mejor)
            self.crear_generacion()
            generacion+=1

ga=AlgoritmoGenetico()
ga.evolucionar()