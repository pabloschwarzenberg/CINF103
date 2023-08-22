from queue import PriorityQueue

def contains(lista,valor,key=lambda x: x[1]):
    for i in range(len(lista)):
        if key(lista[i])==valor:
            return i
    return -1

class BacktrackingFinder:
    def __init__(self,context):
        self.context=context
        self.contador=0

    def find(self,origen,destino,camino):
        self.recursive_find(origen,destino,[],camino)
        print(self.contador)

    def recursive_find(self,origen,destino,camino,solucion):
        if len(camino)>0 and self.context.calcular_distancia(camino[-1],destino)==0:
            if len(solucion)==0 or (len(solucion)!=0 and len(solucion)>len(camino)):
                solucion.clear()
                for paso in camino:
                    solucion.append(paso)
            return

        if(len(camino)==0):
            posicion=origen
        else:
            posicion=camino[-1]
        vecinos=self.context.obtener_vecinos(posicion)
        self.contador+=len(vecinos)
        for vecino in vecinos:
            if vecino not in camino:
                camino.append(vecino)
                self.recursive_find(origen,destino,camino.copy(),solucion)
                camino.pop()

class DijkstraFinder:
    def __init__(self,context,early_stop=False):
        self.context=context
        self.contador=0
        self.early_stop=early_stop

    def find(self,origen,destino,camino):
        Q=[]
        S=[]

        Q.append([0,origen,-1])
        while len(Q)!=0:
            u=min(Q, key=lambda x: x[0])
            p=contains(Q,u[1])
            S.append(Q.pop(p))
            if self.early_stop and u[1]==destino:
                break

            vecinos=self.context.obtener_vecinos(u[1])
            self.contador+=len(vecinos)
            for vecino in vecinos:
                d=u[0]+self.context.calcular_distancia(u[1],vecino)
                p=contains(Q,vecino)
                if p==-1:
                    if contains(S,vecino)==-1:
                        Q.append([d,vecino,u[1]])
                else:
                    if Q[p][0]>d:
                        Q[p]=[d,vecino,u[1]]

        p=contains(S,destino)
        while(p!=-1):
            camino.append(S[p][1])
            anterior=S[p][2]
            p=contains(S,anterior)
        camino.reverse()
        camino.pop(0)
        print(self.contador)

class AstarFinder:
    def __init__(self,context):
        self.context=context
        self.contador=0

    def find(self,origen,destino,camino):
        Q=[]
        S=[]

        Q.append([0,origen,-1,0])
        while len(Q)!=0:
            u=min(Q, key=lambda x: x[0])
            p=contains(Q,u[1])
            S.append(Q.pop(p))
            if u[1]==destino:
                break

            vecinos=self.context.obtener_vecinos(u[1])
            self.contador+=len(vecinos)
            for vecino in vecinos:
                d=u[0]+self.context.calcular_distancia(u[1],vecino)
                f=d+self.context.calcular_distancia(vecino,destino)
                p=contains(Q,vecino)
                if p==-1:
                    if contains(S,vecino)==-1:
                        Q.append([f,vecino,u[1],d])
                else:
                    if Q[p][3]>d:
                        Q[p]=[f,vecino,u[1],d]

        p=contains(S,destino)
        while(p!=-1):
            camino.append(S[p][1])
            anterior=S[p][2]
            p=contains(S,anterior)
        camino.reverse()
        camino.pop(0)
        print(self.contador)