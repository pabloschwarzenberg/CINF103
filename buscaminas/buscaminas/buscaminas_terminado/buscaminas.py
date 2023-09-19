import random
from tkinter import *
from tkinter import messagebox

def crearTablero():
    tablero=[]
    posiciones=[]
    for i in range(8):
        fila=[0,0,0,0,0,0,0,0]
        tablero.append(fila)
        for j in range(8):
            posiciones.append([i,j])
    contador=0
    while contador<10:
        posicion=random.choice(posiciones)
        posiciones.remove(posicion)
        fila=posicion[0]
        columna=posicion[1]
        tablero[fila][columna]=1
        contador=contador+1
    return tablero

def descubrir(tablero,fila,columna):
    resultado=0
    if tablero[fila][columna]==1:
        return -1
    else:
        x=0
        y=0
        for i in [-1,0,1]:
            for j in [-1,0,1]:
                x=fila+i
                y=columna+j
                if x<0 or x>7 or y<0 or y>7:
                    continue
                else:
                    if tablero[x][y]==1:
                        resultado=resultado+1
        return resultado

def click(evento):
    fila=evento.widget.x
    columna=evento.widget.y
    n=descubrir(tablero,fila,columna)
    if n==-1:
        estado.create_image((40,40),image=triste)
        evento.widget["text"]="*"
        evento.widget["bg"]="#cc0000"
        messagebox.showinfo("Fin del Juego","Hiciste click sobre una mina.")
        exit(1)
    else:
        estado.create_image((40,40),image=feliz)
        evento.widget["text"]=str(n)
        evento.widget["bg"]="#ccffcc"

principal = Tk()
principal.title("Buscaminas")
botones=[]
estado=Canvas(principal, bg="#FFFFFF", width=80, height=80)
feliz=PhotoImage(file="feliz.png")
triste=PhotoImage(file="triste.png")
estado.grid(row=8,column=0,columnspan=8)
tablero=crearTablero()

for i in range(8):
    fila=[]
    for j in range(8):
        b1=Button(principal,text="",bg="#ffffcc",font=("Helvetica",16),width="4",height="2")
        b1.bind("<Button-1>",click)
        b1.x=i
        b1.y=j
        b1.grid(row=i,column=j)
        fila.append(b1)
    botones.append(fila)

mainloop()
