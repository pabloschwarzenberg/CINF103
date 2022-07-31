import cocos
import pyglet
import random
import sys
import math
from state import *
from cocos.director import director

class Laberinto:
    def __init__(self):
        self.sprite=cocos.sprite.Sprite("resources/laberinto.png")
        self.sprite.position=270,270
        self.mapa= [
            [0,0,0,0,0,0,0,0,0],
            [0,1,0,1,1,1,0,1,0],
            [0,0,0,0,0,0,0,0,0],
            [1,1,0,1,0,1,0,1,1],
            [0,1,0,1,1,1,0,1,0],
            [0,1,0,0,0,0,0,1,0],
            [0,0,0,1,1,1,0,0,0],
            [0,1,0,1,0,1,0,1,0],
            [0,0,0,0,0,0,0,0,0]
        ]

    def celda_mas_lejana(self,x,y):
        d_mas_lejana=0
        p_mas_lejana=(x,y)
        for i in range(9):
            fd=abs(x-i)
            for j in range(9):
                if self.mapa[i][j]==0:
                    d=fd+abs(y-j)
                    if d>d_mas_lejana:
                        d_mas_lejana=d
                        p_mas_lejana=(i,j)
        return p_mas_lejana

    def posicionar(self,i,j,objeto):
        x,y=self.posicion_centro_celda(i,j)
        if self.mapa[i][j]==0:
            self.mapa[i][j]=objeto
            objeto.sprite.x=x
            objeto.sprite.y=y

    def posicion_centro_celda(self,i,j):
        return 30+60*j,30+60*(8-i)

    def objeto_en_celda(self,i,j):
        if i<0 or j<0 or i>8 or j>8:
            return None
        else:
            return self.mapa[i][j]

    def colision(self,objeto):
        x=objeto.sprite.x
        y=objeto.sprite.y
        i,j=self.en_celda(x,y)
        if i<0 or j<0 or i>8 or j>8:
            return True
        if self.mapa[i][j]!=0 and self.mapa[i][j]!=objeto:
            return True
        else:
            return False

    def en_celda(self,x,y):
        i=8-(y-30)//60
        j=(x-30)//60
        return i,j

class JuegoPacman(cocos.layer.Layer):
    is_event_handler=True

    def __init__(self):
        super(JuegoPacman, self ).__init__()
        self.laberinto=Laberinto()
        self.pacman=Pacman(self)

        self.atlas_items=pyglet.image.load("resources/comida.png")
        self.imagen_item=pyglet.image.ImageGrid(self.atlas_items,1,16)

        self.fantasma1=Fantasma(self)

        self.comida0=Comida(0,True,10,self.imagen_item[0])
        self.laberinto.posicionar(8,0,self.comida0)

        self.comida1=Comida(1,False,20,self.imagen_item[1])
        self.laberinto.posicionar(0,8,self.comida1)

        self.etiqueta_marcador=cocos.text.Label("Score:",(190,450),font_size=16,bold=True)
        self.marcador=cocos.text.Label(str(self.pacman.puntaje).zfill(2),(270,450),font_size=16,bold=True)

        self.add(self.laberinto.sprite,z=0)
        self.add(self.pacman.sprite,z=1)
        self.add(self.fantasma1.sprite,z=2)
        self.add(self.comida0.sprite,z=1)
        self.add(self.comida1.sprite,z=1)
        self.add(self.etiqueta_marcador,z=1)
        self.add(self.marcador,z=1)
        self.schedule_interval(self.simular,0.5)

    def simular(self,*args,**kwargs):
        self.marcador.element.text=str(self.pacman.puntaje).zfill(2)
        self.fantasma1.animar()

    def on_key_press(self, symbol, modifiers):
        if symbol == pyglet.window.key.RIGHT:
            self.pacman.mover(60,0)
        elif symbol == pyglet.window.key.LEFT:
            self.pacman.mover(-60,0)
        elif symbol == pyglet.window.key.UP:
            self.pacman.mover(0,60)
        elif symbol == pyglet.window.key.DOWN:
            self.pacman.mover(0,-60)

class Pacman:
    def __init__(self,game):
        self.atlas=pyglet.image.load("resources/pacman.png")
        self.animaciones=pyglet.image.ImageGrid(self.atlas,1,16)
        self.frame=0
        self.sprite=cocos.sprite.Sprite(self.animaciones[self.frame])
        self.vidas=3
        self.laberinto=game.laberinto
        self.puntaje=0
        self.perseguir=False
        self.spawn()

    def spawn(self):
        x,y=self.laberinto.posicion_centro_celda(0,0)
        self.sprite.x=x
        self.sprite.y=y
        self.laberinto.mapa[0][0]=self

    def mover(self,dx,dy):
        self.frame+=1
        if self.frame>2:
            self.frame=0
        self.sprite.image=self.animaciones[self.frame]
        ox=self.sprite.x
        oy=self.sprite.y
        self.sprite.x+=dx
        self.sprite.y+=dy

        if ox<self.sprite.x:
            self.sprite.rotation=180
        else:
            self.sprite.rotation=0
        if oy<self.sprite.y:
            self.sprite.rotation=90
        elif oy>self.sprite.y:
            self.sprite.rotation=270

        i0,j0=self.laberinto.en_celda(ox,oy)
        i,j=self.laberinto.en_celda(self.sprite.x,self.sprite.y)
        if(self.laberinto.colision(self)):
            objeto=self.laberinto.objeto_en_celda(i,j)
            if isinstance(objeto,Comida):
                objeto.sprite.opacity=0
                self.puntaje+=objeto.puntos
                self.laberinto.mapa[i0][j0]=0
                self.laberinto.mapa[i][j]=self
                if objeto.superpower:
                    self.perseguir=True
            else:
                self.sprite.x-=dx
                self.sprite.y-=dy
        else:
            self.laberinto.mapa[i0][j0]=0
            self.laberinto.mapa[i][j]=self

class Fantasma:
    def __init__(self,game):
        self.atlas=pyglet.image.load("resources/fantasma.png")
        self.animaciones=pyglet.image.ImageGrid(self.atlas,1,16)
        self.frame=0
        self.sprite=cocos.sprite.Sprite(self.animaciones[self.frame])
        self.laberinto=game.laberinto
        self.fsm=FiniteStateMachine(self,EstadoAparecer(),game)

    def animar(self):
        self.fsm.update()

    def calcular_distancia(self,origen,destino):
        return abs(origen[0]-destino[0])+abs(origen[1]-destino[1])

    def obtener_vecinos(self,posicion):
        alternativas=[]
        for movimiento in [[1,0],[0,1],[-1,0],[0,-1]]:
            candidato=(posicion[0]+movimiento[0],posicion[1]+movimiento[1])
            if self.movimiento_posible(candidato):
                alternativas.append(candidato)
        return alternativas

    def movimiento_posible(self,movimiento):
        objeto=self.laberinto.objeto_en_celda(movimiento[0],movimiento[1])
        if not(objeto is None) and (isinstance(objeto,Pacman) or isinstance(objeto,Comida) or (isinstance(objeto,int) and int(objeto)==0)):
            return True
        else:
            return False

class Comida:
    def __init__(self,tipo,superpower,puntos,imagen):
        self.tipo=tipo
        self.superpower=superpower
        self.puntos=puntos
        self.sprite=cocos.sprite.Sprite(imagen)

if __name__ == "__main__":
    sys.setrecursionlimit(1500)
    cocos.director.director.init(width=540,height=540)
    juego = JuegoPacman()
    escena_principal = cocos.scene.Scene (juego)
    cocos.director.director.run (escena_principal)