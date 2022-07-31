class JuegoGato:
  #Comienza el raton, valor=1
  def __init__(self,estado=[0]*9,turno=1):
    self.tablero=estado
    self.completo=False
    self.ganador=None
    self.jugador=turno

  def reiniciar(self):
    self.tablero=[0]*9
    self.completo=False
    self.ganador=None
    self.jugador=1

  def generar_jugadas_posibles(self):
    posibles=[]
    for i in range(9):
      if self.tablero[i]==0:
        posibles.append(i)
    return posibles

  def estado_final(self):
    self.evaluar()
    if self.ganador is not None or self.completo:
      return True
    else:
      return False

  def evaluar(self):
    if 0 not in self.tablero:
      self.completo=True
    else:
      self.completo=False
    estado=[]
    for i in [0,3,6]:
      estado.append(sum(self.tablero[i:i+3]))
    for i in [0,1,2]:
      estado.append(self.tablero[i]+self.tablero[i+3]+self.tablero[i+6])
    estado.append(self.tablero[0]+self.tablero[4]+self.tablero[8])
    estado.append(self.tablero[2]+self.tablero[4]+self.tablero[6])
    for valor in estado:
      if valor==3 or valor==-3:
        self.ganador=valor//3
        return
    if self.completo:
      self.ganador=0
    else:
      self.ganador=None

  def calcular_utilidad(self):
    return self.ganador

  def jugar(self,jugada):
    self.tablero[jugada]=self.jugador
    self.jugador*=-1

  def deshacer_jugada(self,jugada):
    self.tablero[jugada]=0
    self.jugador*=-1

# 1: Ratón (Inicia, es el jugador humano)
#-1: Gato (Responde, es el computador)
# cuando gana el gato el valor es -1
# cuando gana el ratón el valor es 1
# un empate tiene utilidad 0
# etapa  1: maximizar
# etapa -1: minimizar
# para tener un minimax tradicional, multiplicamos por -1 la utilidad
# así cuando gana raton: -1, gana gato: 1, y gato es Max
def minimax(juego,etapa,secuencia,secuencias):
  if juego.estado_final():
    secuencias.append(secuencia.copy())
    return [-1*juego.calcular_utilidad()]
  if etapa==1:
    valor=[-1000,None]
  else:
    valor=[1000,None]
  jugadas_posibles=juego.generar_jugadas_posibles()
  for jugada in jugadas_posibles:
    juego.jugar(jugada)
    secuencia.append(jugada)
    opcion=minimax(juego,etapa*-1,secuencia,secuencias)
    #maximizar
    if etapa==1:
      if valor[0]<opcion[0]:
        valor=[opcion[0],jugada]
    else:
    #minimizar
      if valor[0]>opcion[0]:
        valor=[opcion[0],jugada]
    juego.deshacer_jugada(jugada)
    secuencia.pop()
  return valor

def alfabeta(juego,etapa,alfa,beta,secuencia,secuencias):
  if juego.estado_final():
    secuencias.append(secuencia.copy())
    return [-1*juego.calcular_utilidad()]
  if etapa==1:
    valor=[-1000,None]
  else:
    valor=[1000,None]
  jugadas_posibles=juego.generar_jugadas_posibles()
  for jugada in jugadas_posibles:
    juego.jugar(jugada)
    secuencia.append(jugada)
    opcion=alfabeta(juego,etapa*-1,alfa,beta,secuencia,secuencias)
    if etapa==1:
      if valor[0]<opcion[0]:
        valor=[opcion[0],jugada]
      if valor[0]>alfa:
        alfa=valor[0]
      if valor[0]>=beta:
        juego.deshacer_jugada(jugada)
        secuencia.pop()
        break
    else:
      if valor[0]>opcion[0]:
        valor=[opcion[0],jugada]
      if valor[0]<beta:
        beta=valor[0]
      if valor[0]<=alfa:
        juego.deshacer_jugada(jugada)
        secuencia.pop()
        break
    juego.deshacer_jugada(jugada)
    secuencia.pop()
  return valor

def negamax(juego,secuencia,secuencias):
  if juego.estado_final():
    secuencias.append(secuencia.copy())
    utilidad=juego.calcular_utilidad()*juego.jugador
    return [utilidad,None]
  jugadas_posibles=juego.generar_jugadas_posibles()
  valor=[-1000,None]
  for jugada in jugadas_posibles:
    juego.jugar(jugada)
    secuencia.append(jugada)
    opcion=negamax(juego,secuencia,secuencias)
    #multiplicamos por -1 el valor de la utilidad
    #de ahí el nombre negamax
    #siempre maximizamos
    if valor[0] < opcion[0]*-1:
      valor=[opcion[0]*-1,jugada]
    juego.deshacer_jugada(jugada)
    secuencia.pop()
  return valor

def negascout(juego,alfa,beta,secuencia,secuencias):
  if juego.estado_final():
    secuencias.append(secuencia.copy())
    utilidad=juego.calcular_utilidad()*juego.jugador
    return [utilidad,None]
  jugadas_posibles=juego.generar_jugadas_posibles()
  m=[-1000,None]
  n=beta
  for jugada in jugadas_posibles:
    juego.jugar(jugada)
    secuencia.append(jugada)
    t=negascout(juego,-n,-max(alfa,m[0]),secuencia,secuencias)
    t=[t[0]*-1,jugada]
    if t[0]>m[0]:
      if n==beta:
        m=t
      else:
        m=negascout(juego,-beta,-t[0],secuencia,secuencias)
        m=[-m[0],jugada]
    juego.deshacer_jugada(jugada)
    secuencia.pop()
    if m[0]>=beta:
      return m
    n=max(alfa,m[0])+1
  return m

if __name__ == "__main__":
  juego=JuegoGato([-1,0,0,0,1,0,1,-1,1],-1)
  o1=[]
  o2=[]
  o3=[]
  r1=minimax(juego,-1,[],o1)
  r2=negamax(juego,[],o2)
  r3=alfabeta(juego,-1,-1000,1000,[],o3)
  print(r1,o1)
  print(r2,o2)
  print(r3,o3)
