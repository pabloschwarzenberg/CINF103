__version__ = "1.0"

class Pieza:
    def __init__(self,color,tipo,fila,columna,sprite):
        self.tipo=tipo
        self.color=color
        self.fila=fila
        self.columna=columna
        self.sprite=sprite
        self.piezas_capturadas=[]

    def atacar(self,tablero,fila,columna):
        pieza=tablero[fila][columna]
        if pieza is not None:
            if self.color!=pieza.color and self.ataque_valido(fila,columna):
                self.capturar(pieza)
                tablero[fila][columna]=None
                return True
            else:
                return False
        else:
            return self.movida_valida(fila,columna)
                
    def ataque_valido(self,fila,columna):
        return self.movida_valida(fila,columna)

    def movida_valida(self,fila,columna):
        m=[fila,columna]
        posibles=self.movidas_posibles()
        if posibles==[]:
            return False
        else:
            if m in posibles:
                return True
            else:
                return False

    def movidas_posibles(self):
        movidas_posibles=[]
        if self.tipo=="C":
            movidas_posibles=self.movidas_caballo()
        return movidas_posibles

    def movidas_caballo(self):
        posibilidades=[]
        for i in [-2,2]:
            for j in [-1,1]:
                m=[self.fila+i,self.columna+j]
                if m[0]>=0 and m[0]<8 and m[1]>=0 and m[1]<8:
                    posibilidades.append(m)
                m=[self.fila+j,self.columna+i]
                if m[0]>=0 and m[0]<8 and m[1]>=0 and m[1]<8:
                    posibilidades.append(m)
        return posibilidades

    def capturar(self,pieza):
        pieza.sprite.opacity=0
        self.piezas_capturadas.append(pieza)
