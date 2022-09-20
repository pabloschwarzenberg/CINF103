def eliminar_vacios(lista):
    resultado=[]
    for e in lista:
        if e!='':
            resultado.append(e)
    return resultado

estudiantes={}
secuencias={}

progreso=open("dataset_base.csv","r")
header=progreso.readline().strip()
header_ejercicios=""
header_orden=""
for i in range(53):
    header_ejercicios=header_ejercicios+";e"+str(i)
    header_orden=header_orden+";o"+str(i)
header=header+header_ejercicios+header_orden+"\n"
for linea in progreso:
    linea=linea.strip().split(";")
    secuencia=linea[8]+":"+linea[9]+":"+linea[10]+":"+linea[11]
    secuencia=secuencia.split(":")
    secuencia=eliminar_vacios(secuencia)
    secuencia=list(map(int,secuencia))
    
    resueltos=[0]*53
    orden=[0]*53
    k=1
    for ejercicio in secuencia:
        resueltos[ejercicio]=1
        orden[ejercicio]=k
        k=k+1
    resueltos=list(map(str,resueltos))
    linea.extend(resueltos)
    orden=list(map(str,orden))
    linea.extend(orden)
    estudiantes[linea[0]]=linea
progreso.close()

dataset=open("dataset.csv","w")
dataset.write(header)
for rut in estudiantes.keys():
    linea=estudiantes[rut]
    linea=";".join(linea)+"\n"
    dataset.write(linea)
dataset.close()