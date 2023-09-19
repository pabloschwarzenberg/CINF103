import random
from tkinter import *
from tkinter import messagebox
import random

def crearTablero():
    tablero=[]
    posiciones=[]
    for i in range(8):
        fila=[]
        for j in range(8):
            fila.append(0)
            posiciones.append([i,j])
        tablero.append(fila)
    return tablero

def descubrir(tablero,fila,columna):
    resultado=0
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
feliz=PhotoImage(file="feliz.gif")
triste=PhotoImage(file="triste.gif")
estado.grid(row=8,column=0)
tablero=crearTablero()

for i in range(8):
    fila=[]
    for j in range(8):
        b1=Button(principal,text="",bg="#ffffcc",font=("Helvetica",20),width="4",height="2")
        b1.bind("<Button-1>",click)
        b1.x=i
        b1.y=j
        b1.grid(row=i,column=j)
        fila.append(b1)
    botones.append(fila)

mainloop()
