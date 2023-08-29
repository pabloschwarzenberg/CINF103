from search import *

class AccionAparecer:
    def execute(self,agent,game):
        x,y=agent.laberinto.posicion_centro_celda(3,4)
        agent.sprite.x=x
        agent.sprite.y=y
        agent.camino=[]
        x,y=agent.laberinto.posicion_centro_celda(0,0)
        agent.target=[x,y] 

class AccionAnimar:
    def __init__(self,base_frame):
        self.base_frame=base_frame

    def execute(self,agent,game):
        agent.frame+=1
        if agent.frame>self.base_frame+1:
            agent.frame=self.base_frame
        agent.sprite.image=agent.animaciones[agent.frame]

class AccionPerseguir:
    def execute(self,agent,game):
        agent.target=agent.laberinto.en_celda(game.pacman.sprite.x,game.pacman.sprite.y)

class AccionEscapar:
    def execute(self,agent,game):
        x,y=agent.laberinto.en_celda(game.pacman.sprite.x,game.pacman.sprite.y)
        agent.target=agent.laberinto.celda_mas_lejana(x,y)

class AccionEncontrarCamino:
    def execute(self,agent,game):
        if len(agent.camino)==0 or agent.camino[-1][0]!=agent.target[0] or agent.camino[-1][1]!=agent.target[1]:
            agent.camino=[]
            origen=agent.laberinto.en_celda(agent.sprite.x,agent.sprite.y)
            df=AstarFinder(agent)
            df.find(origen,agent.target,agent.camino)

class AccionAvanzar:
    def execute(self,agent,game):
        if len(agent.camino)!=0:
            movimiento=agent.camino.pop(0)
            i,j=movimiento[0],movimiento[1]
            agent.sprite.x,agent.sprite.y=agent.laberinto.posicion_centro_celda(i,j)
            objeto=agent.laberinto.objeto_en_celda(i,j)
            if isinstance(objeto,type(game.pacman)):
                print("Atrapado")
                agent.laberinto.mapa[i][j]=0
                objeto.spawn()
                AccionAparecer().execute(agent,game)

class TransicionPerseguir:
    def test(self,agent,game):
        if not game.pacman.perseguir:
            return True
        else:
            return False
    
    def target(self):
        return EstadoPerseguir()

class TransicionEscapar:
    def test(self,agent,game):
        if game.pacman.perseguir:
            return True
        else:
            return False

    def target(self):
        return EstadoEscapar()

class EstadoAparecer:
    def enter(self,agent,game):
        agent.frame=0
        
    def getActions(self):
        return [AccionAparecer()]

    def getTransitions(self):
        return [TransicionPerseguir()]

class EstadoPerseguir:
    def enter(self,agent,game):
        agent.frame=0
        
    def getActions(self):
        return [AccionAnimar(0),AccionPerseguir(),AccionEncontrarCamino(),AccionAvanzar()]

    def getTransitions(self):
        return [TransicionEscapar()]

class EstadoEscapar:
    def enter(self,agent,game):
        agent.frame=12

    def getActions(self):
        return [AccionAnimar(12),AccionEscapar(),AccionEncontrarCamino(),AccionAvanzar()]

    def getTransitions(self):
        return [TransicionPerseguir()]

class FiniteStateMachine:
    def __init__(self,agent,start,game):
        self.agent=agent
        self.current=start
        self.game=game
        self.current.enter(agent,game)

    def update(self):
        for action in self.current.getActions():
            action.execute(self.agent,self.game)
        for transition in self.current.getTransitions():
            if transition.test(self.agent,self.game):
                self.current=transition.target()
                self.current.enter(self.agent,self.game)
                break