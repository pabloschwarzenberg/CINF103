import cocos
import pyglet
from pieza import *

class Ajedrez(cocos.layer.Layer):
    is_event_handler=True

    def __init__(self):
        super(Ajedrez, self ).__init__()
        self.tablero= [[None]*8,[None]*8,[None]*8,[None]*8,[None]*8,[None]*8,[None]*8,[None]*8]
        self.pieza_seleccionada=None

        self.imagen_tablero=cocos.sprite.Sprite("resources/tablero.png")
        self.imagen_tablero.position=212,212
        self.atlas=pyglet.image.load("resources/piezas.png")
        self.imagenes=pyglet.image.ImageGrid(self.atlas,1,18)

        self.add(self.imagen_tablero,z=0)
        self.cargar_tablero("tablero.txt")

        self.simulacion=[]
        self.schedule_interval(self.simular,0.5)

    def cargar_tablero(self,nombre_archivo):
        archivo=open(nombre_archivo,"r")
        i=0
        for linea in archivo:
            linea=linea.strip().split(" ")
            j=0
            for celda in linea:
                if celda != "V":
                    self.crearPieza(celda,i,j)
                j+=1
            i+=1
        archivo.close()

    def crearPieza(self,codigo,i,j):
        x,y=self.posicion_centro_celda(i,j)
        if codigo[0]=="N":
            imagen=9
        else:
            imagen=0
        if codigo[1]=="C":
            imagen+=1
        elif codigo[1]=="A":
            imagen+=2
        elif codigo[1]=="Q":
            imagen+=3
        elif codigo[1]=="K":
            imagen+=4
        elif codigo[1]=="P":
            imagen+=8
        sprite=cocos.sprite.Sprite(self.imagenes[imagen])
        sprite.x=x
        sprite.y=y
        pieza=Pieza(codigo[0],codigo[1],i,j,sprite)
        self.tablero[i][j]=pieza
        self.add(sprite,z=1)

    def posicion_centro_celda(self,i,j):
        return 26+53*j,26+53*(7-i)

    def seleccionar_celda(self,x,y):
        i=7-y//53
        j=x//53
        return i,j

    def simular(self,*args,**kwargs):
        if len(self.simulacion)==0:
            return

    def mover(self,pieza,i,j):
        x,y=self.posicion_centro_celda(i,j)
        pieza.sprite.x=x
        pieza.sprite.y=y
        self.tablero[pieza.fila][pieza.columna]=None
        pieza.fila=i
        pieza.columna=j
        self.tablero[i][j]=pieza

    def deshacer_movida(self):
        x,y=self.posicion_centro_celda(self.pieza_seleccionada.fila,self.pieza_seleccionada.columna)
        self.pieza_seleccionada.sprite.x=x
        self.pieza_seleccionada.sprite.y=y
        self.pieza_seleccionada=None

    def on_mouse_drag(self, x, y, dx, dy, buttons, modifiers):
        if self.pieza_seleccionada is not None:
            self.pieza_seleccionada.sprite.x=x
            self.pieza_seleccionada.sprite.y=y

    def on_mouse_release(self,x,y,buttons,modifiers):
        if self.pieza_seleccionada is not None:
            i,j=self.seleccionar_celda(x,y)
            if i<0:
                i=0
            if j<0:
                j=0
            if i>7:
                i=7
            if j>7:
                j=7
            if self.pieza_seleccionada.atacar(self.tablero,i,j):
                self.mover(self.pieza_seleccionada,i,j)
                self.pieza_seleccionada=None
            else:
                self.deshacer_movida()

    def on_mouse_press(self, x, y, buttons, modifiers):
        i,j=self.seleccionar_celda(x,y)
        pieza=self.tablero[i][j]
        if isinstance(pieza,Pieza):
            self.pieza_seleccionada=pieza

if __name__ == "__main__":
    cocos.director.director.init(width=424,height=424)
    juego = Ajedrez()
    escena_principal = cocos.scene.Scene (juego)
    cocos.director.director.run (escena_principal)
