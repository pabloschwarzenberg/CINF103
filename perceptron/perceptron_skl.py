from sklearn.linear_model import Perceptron
import numpy as np

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
X=np.array(X)
Y=np.array(Y).reshape(len(Y))
p= Perceptron(eta0=0.01,max_iter=10)
p.fit(X, Y, [0,0],[0])
print(p.coef_)
print(p.intercept_)