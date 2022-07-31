class Perceptron:
    def __init__(self,eta,epochs):
        self.eta=eta
        self.epochs=epochs
        self.W=[1,1,1]

    def activacion(self,z):
        if z>=0:
            return 1
        else:
            return -1

    def salida(self,x):
        z=self.W[0]+self.W[1]*x[0]+self.W[2]*x[1]
        return self.activacion(z)

    def entrenar(self,X,Y):
        for i in range(self.epochs):
            errores=0
            for j in range(len(X)):
                yp=self.salida(X[j])
                if(yp!=Y[j][0]):
                    delta=self.eta*(Y[j][0]-yp)
                    self.W[0]+=delta
                    self.W[1]+=delta*X[j][0]
                    self.W[2]+=delta*X[j][1]
                    errores+=1
            print("En iteracion ",i," hay ",errores," errores")
        print("W=",self.W[0],self.W[1],self.W[2])

def loadIrisDataset():
    X=[]
    Y=[]
    archivo=open("iris.data")
    for linea in archivo:
        linea=linea.strip().split(",")
        if linea[4]!="Iris-virginica":
            x=[0,0]
            y=[0]
            if(linea[4]=="Iris-setosa"):
                y[0]=-1
            elif (linea[4]=="Iris-versicolor"):
                y[0]=1
            x[0]=float(linea[0])
            x[1]=float(linea[2])
            X.append(x)
            Y.append(y)
    print("Se cargaron ",len(X)," muestras en el dataset")
    return X,Y

X,Y=loadIrisDataset()
perceptron=Perceptron(0.01,10)
perceptron.entrenar(X,Y)