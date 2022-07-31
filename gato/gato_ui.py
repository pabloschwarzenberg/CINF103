import aisearch
from tkinter import *
from tkinter import messagebox

class Gato:
    def __init__(self):
        self.principal = Tk()
        self.principal.title("Gato")
        self.botones=[]
        self.gato=PhotoImage(file="gato.gif")
        self.raton=PhotoImage(file="raton.gif")
        self.vacio=PhotoImage(file="vacio.gif")
        self.juego=aisearch.JuegoGato()
        for i in range(3):
            fila=[]
            for j in range(3):
                b1=Button(self.principal,image=self.vacio,width="80",height="80")
                b1.bind("<Button-1>",self.click)
                b1.x=i
                b1.y=j
                b1.grid(row=i,column=j)
                fila.append(b1)
            self.botones.append(fila)

    def victoria(self):
        if self.juego.estado_final():
            if self.juego.ganador == 1:
                messagebox.showinfo("Juego del Gato", "Has ganado!")
            elif self.juego.ganador == 0:
                messagebox.showinfo("Juego del Gato", "Empate")
            else:
                messagebox.showinfo("Juego del Gato", "Has perdido")
            self.juego.reiniciar()
            for i in range(3):
                for j in range(3):
                    self.botones[i][j]["image"] = self.vacio
            return True
        else:
            return False
    def click(self,evento):
        if self.juego.tablero[evento.widget.x * 3 + evento.widget.y]==0:
            self.juego.jugar(evento.widget.x * 3 + evento.widget.y)
            evento.widget["image"] = self.raton
            if not self.victoria():
                o=[]
                #m=aisearch.negascout(self.juego,-1000,1000, [], o)
                m=aisearch.alfabeta(self.juego,1,-1000,1000, [], o)
                #m=aisearch.minimax(self.juego, 1, [], o)
                #m=aisearch.negamax(self.juego,[],o)
                print(len(o))
                self.juego.jugar(m[1])
                self.botones[m[1]//3][m[1]%3]["image"]=self.gato
                self.victoria()
juego=Gato()
mainloop()
