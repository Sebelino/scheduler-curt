
%timeEntry('7am').
timeEntry(Time) :-
    between(1,12,N),
    atom_number(AN,N),
    member(Period,['am','pm']),
    atom_concat(AN,Period,Time).

