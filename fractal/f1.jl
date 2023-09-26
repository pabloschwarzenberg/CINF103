using Pkg
Pkg.add("Fatou")
Pkg.add("PyPlot")
using Fatou
using PyPlot

c = -0.06 + 0.67im
nf = juliafill(:(z^2+$c),∂=[-1.5,1.5,-1,1],N=80,n=1501,cmap="gnuplot",iter=true)
plot(fatou(nf), bare=true)