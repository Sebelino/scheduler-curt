%

timeEntry(Time) :-
    between(1,12,Hour),
    atom_number(AtomHour,Hour),
    member(Period,['am','pm']),
    atom_concat(AtomHour,Period,Time).

timeEntry(Time) :-
    between(1,12,Hour),
    atom_number(AtomHour,Hour),
    between(0,59,Minute),
    atom_number(AtomMinute,Minute),
    member(Period,['am','pm']),
    atomic_list_concat([AtomHour,':',AtomMinute,Period],Time).
