%Levesque, H. (2012). Thinking as Computation.
cap(F,_,F,_).
cap(_,C,_,C).
cap(F1,C1,F2,C2):-F1+C1=:=F2+C2.
cap(F1,C1,F2,C2):-F1-C1=:=F2-C2.
col(1).
col(2).
col(3).
col(4).
col(5).
col(6).
col(7).
col(8).
resolver(Q1,Q2,Q3,Q4,Q5,Q6,Q7,Q8) :-
col(Q1),
col(Q2),\+ cap(2,Q2,1,Q1),
col(Q3),\+ cap(3,Q3,1,Q1), \+ cap(3,Q3,2,Q2),
col(Q4),\+ cap(4,Q4,1,Q1), \+ cap(4,Q4,2,Q2), \+ cap(4,Q4,3,Q3),
col(Q5),\+ cap(5,Q5,1,Q1), \+ cap(5,Q5,2,Q2), \+ cap(5,Q5,3,Q3), \+ cap(5,Q5,4,Q4),
col(Q6),\+ cap(6,Q6,1,Q1), \+ cap(6,Q6,2,Q2), \+ cap(6,Q6,3,Q3), \+ cap(6,Q6,4,Q4), \+ cap(6,Q6,5,Q5),
col(Q7),\+ cap(7,Q7,1,Q1), \+ cap(7,Q7,2,Q2), \+ cap(7,Q7,3,Q3), \+ cap(7,Q7,4,Q4), \+ cap(7,Q7,5,Q5),\+ cap(7,Q7,6,Q6),
col(Q8),\+ cap(8,Q8,1,Q1), \+ cap(8,Q8,2,Q2), \+ cap(8,Q8,3,Q3), \+ cap(8,Q8,4,Q4), \+ cap(8,Q8,5,Q5),\+ cap(8,Q8,6,Q6),\+ cap(8,Q8,7,Q7).
