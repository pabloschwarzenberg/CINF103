from tkinter import *

principal = Tk()
principal.title("8 Reinas")
reina=PhotoImage(file="reina.png")
blanco=PhotoImage(file="blanco.png")
negro=PhotoImage(file="negro.png")
botones=[]

def click(evento):
    evento.widget["image"] = reina

def mostrar(cromosoma):
    for i in range(len(cromosoma)):
        botones[cromosoma[i]-1][i]["image"]=reina

for i in range(8):
    fila=[]
    c= 1 if i%2==0 else 0
    for j in range(8):
        celda= blanco if c%2==1 else negro
        b1=Button(principal,text="",bg="#ffffff",font=("Helvetica",20),image=celda,width="80",height="80")
        c+=1
        b1.bind("<Button-1>",click)
        b1.x=i
        b1.y=j
        b1.grid(row=i,column=j)
        fila.append(b1)
    botones.append(fila)

mostrar([1,6,2,5,7,4,8,3])
mainloop()
