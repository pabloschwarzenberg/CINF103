%Levesque, H. (2012). Thinking as Computation.
ataca(F,_,F,_).
ataca(_,C,_,C).
ataca(F1,C1,F2,C2):-F1+C1=:=F2+C2.
ataca(F1,C1,F2,C2):-F1-C1=:=F2-C2.
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
col(Q2),\+ ataca(2,Q2,1,Q1),
col(Q3),\+ ataca(3,Q3,1,Q1), \+ ataca(3,Q3,2,Q2),
col(Q4),\+ ataca(4,Q4,1,Q1), \+ ataca(4,Q4,2,Q2), \+ ataca(4,Q4,3,Q3),
col(Q5),\+ ataca(5,Q5,1,Q1), \+ ataca(5,Q5,2,Q2), \+ ataca(5,Q5,3,Q3), \+ ataca(5,Q5,4,Q4),
col(Q6),\+ ataca(6,Q6,1,Q1), \+ ataca(6,Q6,2,Q2), \+ ataca(6,Q6,3,Q3), \+ ataca(6,Q6,4,Q4), \+ ataca(6,Q6,5,Q5),
col(Q7),\+ ataca(7,Q7,1,Q1), \+ ataca(7,Q7,2,Q2), \+ ataca(7,Q7,3,Q3), \+ ataca(7,Q7,4,Q4), \+ ataca(7,Q7,5,Q5),\+ ataca(7,Q7,6,Q6),
col(Q8),\+ ataca(8,Q8,1,Q1), \+ ataca(8,Q8,2,Q2), \+ ataca(8,Q8,3,Q3), \+ ataca(8,Q8,4,Q4), \+ ataca(8,Q8,5,Q5),\+ ataca(8,Q8,6,Q6),\+ ataca(8,Q8,7,Q7).
