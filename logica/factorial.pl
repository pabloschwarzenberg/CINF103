factorial(0,1).
factorial(1,1).
factorial(N,R):-
    N>1,
    M is N-1,
    factorial(M,S),
    R is N*S.
