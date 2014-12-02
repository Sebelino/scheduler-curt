%

:- module(times,[timeEntry/1,
			     formatTime/2,
			     timestamp2readable/2,
			     capitalize/2,
                 lessThan/2]).
:- use_module(library(julian),[form_time/1,
                               form_time/2,
                               delta_time/3,
                               julian_calendar_gregorian:month_number/2,
                               compare_time/3]).

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


formatTime([evt(Activity,TimeA,TimeB)],[evt(Activity,TimestampA,TimestampB)]) :-
    convertTime(TimeA,TimestampA),
    convertTime(TimeB,TimestampB).

formatTime([evt(Activity,TimeA,TimeB,Dayspec)],[evt(Activity,TimestampA,TimestampB)]) :-
    convertTime(TimeA,Dayspec,TimestampA),
    convertTime(TimeB,Dayspec,TimestampB).

formatTime([Reading],[Reading]) :-
    compose(Reading,Sym,_),
    \+ Sym = evt.

convertTime(MTime,Dayspec,TimeStamp2) :-
    convertTime(MTime,TimeStamp1),
    form_time(today,Today),
    between(1,7,NDays),
    delta_time(Today,days(NDays),Weekday),
    form_time([dow(Dayspec)],Weekday),
    !,
    form_time([Weekday,Y-Mo-D]),
    atomic_list_concat([t,_,_,_,H,Mi],'_',TimeStamp1),
    atom_number(YA,Y),
    atom_number(MoA,Mo),
    atom_number(DA,D),
    atomic_list_concat([t,YA,MoA,DA,H,Mi],'_',TimeStamp2).

% '7pm' -> '2014_12_1_19_0'
% '11:15am' -> '2014_12_1_11_15'
convertTime(MTime,TimeStamp) :-
    meridiem2clock(MTime,Hour,Minute),
    form_time([now,Y-Mo-D]),
    atom_number(YA,Y),
    atom_number(MoA,Mo),
    atom_number(DA,D),
    atomic_list_concat([t,YA,MoA,DA,Hour,Minute],'_',TimeStamp).


% '7pm' -> '19', '7am' -> '7'
meridiem2clock(MTime,Hour,'0') :-
    atom_length(MTime,L),
    B is L-2,
    sub_atom(MTime,B,2,0,Trail),
    member(Trail,['am','pm']),
    sub_atom(MTime,0,_,2,HA),
    atom_number(HA,H),
    (Trail = 'am', (H < 12, N = H ; H = 12, N = 0) ; Trail = 'pm', (H < 12, N is H+12 ; H = 12, N = H)),
    atom_number(Hour,N), !.

% '7:15pm' -> ('19','15')
meridiem2clock(MTime,Hour,Minute) :-
    atomic_list_concat([HA,MPart],':',MTime),
    atom_length(MPart,L),
    B is L-2,
    sub_atom(MPart,B,2,0,Trail),
    member(Trail,['am','pm']),
    sub_atom(MPart,0,_,2,Minute),
    atom_number(HA,H),
    (Trail = 'am', (H < 12, N = H ; H = 12, N = 0) ; Trail = 'pm', (H < 12, N is H+12 ; H = 12, N = H)),
    atom_number(Hour,N), !.

stamp2time(Stamp,Time) :-
    atomic_list_concat([t,Y,Mo,D,H,Mi],'_',Stamp),
    padNumber(Mo,PMo),
    padNumber(D,PD),
    padNumber(H,PH),
    padNumber(Mi,PMi),
    atomic_list_concat([Y,'-',PMo,'-',PD,'T',PH,':',PMi,':','00'],RFC),
    atom_string(RFC,SRFC),
    form_time(rfc3339(SRFC),Time).

lessThan(Stamp1,Stamp2) :-
    stamp2time(Stamp1,Time1),
    stamp2time(Stamp2,Time2),
    compare_time(<,Time1,Time2).


padNumber(Number,Number) :- atom_length(Number,2).
padNumber(Number,PNumber) :-
    atom_length(Number,1),
    atomic_list_concat(['0',Number],PNumber).

% 2014_... -> 7:0 29 November 2014
timestamp2readable(Stamp,Readable) :-
    ourFormat2List(Stamp,[Y,Mo,D,H,Mi]),
    padNumber(H,PH),
    padNumber(Mi,PMi),
    atomic_list_concat([PH,PMi],':',T),
    atom_number(Mo,NMo),
    month_number(RMo,NMo),
    capitalize(RMo,UMo),
    atomic_list_concat([D,Y],', ',DY),
    atomic_list_concat([T,UMo,DY],' ',Readable).

ourFormat2List(Our,T) :-
    atomic_list_concat(['t'|T],'_',Our).


% november -> 'November'
capitalize(Lower,Upper) :-
    atom_codes(Lower,[H|T]),
    to_upper(H,UpperH),
    atom_codes(Upper,[UpperH|T]).

