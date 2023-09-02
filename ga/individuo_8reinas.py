import random
from individuo import *

class Individuo_8reinas(Individuo):
    def __init__(self):
        super(Individuo_8reinas,self).__init__()

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

    def crear(self):
        self.genotipo=[0,1,2,3,4,5,6,7]
        random.shuffle(self.genotipo)

    def evaluar(self):
        self.fenotipo=[]
        for i in range(8):
            self.fenotipo.append([0]*8)
        columna=0
        for fila in self.genotipo:
            self.fenotipo[fila][columna]=1
            columna=columna+1
        ataques=0
        i=0
        while i<8:
            fila=self.genotipo[i]
            columna=i
            ataques+=self.revisar_columnas(fila,columna)
            ataques+=self.revisar_filas(fila,columna)
            ataques+=self.revisar_diagonales(fila,columna)
            i=i+1
        self.fitness=ataques
        return ataques

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
        nuevo=Individuo_8reinas()
        nuevo.genotipo=hijo
        return nuevo