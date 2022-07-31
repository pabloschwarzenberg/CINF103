from search import DijkstraFinder

class Grafo:
    def __init__(self,ady):
        self.ady=ady

    def obtener_vecinos(self,u):
        vecinos=[]
        arcos=len(self.ady)
        for i in range(arcos):
            if i==u:
                for j in range(arcos):
                    if self.ady[i][j]!=-1:
                        vecinos.append(j)
        return vecinos

    def calcular_distancia(self,u,v):
        return self.ady[u][v]

if __name__ == "__main__":
    g=Grafo(
        [
            [-1, -1,  -1,   4,  -1,  -1,  -1],
            [-1, -1,  -1,   9,  -1,  -1,   2],
            [-1, -1,  -1, 5.5, 6.5,  -1, 3.5],
            [ 4,  9, 5.5,  -1,   1,   3,  -1],
            [-1, -1, 6.5,   1,  -1,  -1,  -1],
            [-1, -1,  -1,   3,  -1,  -1,  -1],
            [ 6,  2, 3.5,  -1,  -1, 6.5,  -1]
        ]
    )
    ds=DijkstraFinder(g)
    solucion=[]
    ds.find(6,3,solucion)
    print(solucion)   