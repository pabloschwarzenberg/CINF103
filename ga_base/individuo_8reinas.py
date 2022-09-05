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