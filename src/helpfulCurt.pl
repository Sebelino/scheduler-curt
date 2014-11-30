/*************************************************************************

    File: helpfulCurt.pl
    Copyright (C) 2004,2005,2006 Patrick Blackburn & Johan Bos

    This file is part of BB1, version 1.3 (November 2006).

    BB1 is free software; you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation; either version 2 of the License, or
    (at your option) any later version.

    BB1 is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with BB1; if not, write to the Free Software Foundation, Inc., 
    59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

*************************************************************************/

:- module(curt,[curt/0,infix/0,prefix/0]).

:- use_module(callInference,[callTP/3,
                             callTPandMB/6]).

:- use_module(readLine,[readLine/1]).

:- use_module(comsemPredicates,[infix/0,
                                prefix/0,
                                memberList/2,
                                compose/3,
				selectFromList/3,
				printRepresentations/1]).

:- use_module(kellerStorage,[kellerStorage/2]).

:- use_module(modelChecker2,[satisfy/4]).

:- use_module(backgroundKnowledge,[backgroundKnowledge/2]).

:- use_module(elimEquivReadings,[elimEquivReadings/2]).

:- use_module(curtPredicates,[curtHelp/0,
                              curtOutput/1,
                              updateReadings/1,
                              updateModels/1,
                              updateHistory/1,
                              clearHistory/0,
                              list2string/2,
                              selectReadings/3]).

:- use_module(library(julian),[form_time/1,month_number/2]).

/*========================================================================
   Dynamic Predicates
========================================================================*/

:- dynamic history/1, readings/1, models/1.

history([]).
readings([]).
models([]).


/*========================================================================
   Start Curt
========================================================================*/

curt:- 
   curtTalk(run).


/*========================================================================
   Control
========================================================================*/

curtTalk(quit).

curtTalk(run):-
   readLine(Input),
   curtUpdate(Input,CurtsMoves,State), 
   curtOutput(CurtsMoves),
   curtTalk(State).


/*========================================================================
   Update Curt's Information State
========================================================================*/

curtUpdate([],[clarify],run):- !.

curtUpdate([bye],[bye],quit):- !,
   updateReadings([]),
   updateModels([]),
   clearHistory.

curtUpdate([new],[],run):- !,
   updateReadings([]),
   updateModels([]),
   clearHistory.

curtUpdate([help],[],run):- !,
   curtHelp.

curtUpdate([infix],[],run):- !,
   infix.

curtUpdate([prefix],[],run):- !,
   prefix.

curtUpdate([select,X],[],run):-
   number(X),
   readings(R1),
   selectReadings(X,R1,R2), !,
   updateReadings(R2),
   models(M1),
   selectReadings(X,M1,M2),
   updateModels(M2).

curtUpdate([summary],[],run):-
   readings(Readings),
   elimEquivReadings(Readings,Unique),
   updateReadings(Unique),
   updateModels([]).

curtUpdate([knowledge],[],run):-
   readings(R), 
   findall(K,(memberList(F,R),backgroundKnowledge(F,K)),L),
   printRepresentations(L).
   
curtUpdate([readings],[],run):- !,
   readings(R),
   printRepresentations(R).

curtUpdate([models],[],run):- !,
   models(M),
   printRepresentations(M).

curtUpdate([history],[],run):- !,
   history(H),
   printRepresentations(H).


curtUpdate([show,my,appointments],[],run):- !,
   models([M]),
   showModel(M).

showModel(model(_,Interpretation)):-
    member(f(3,evt,[ (DEvent,DTimeA,DTimeB)]),Interpretation),
    member(f(0,Event,DEvent),Interpretation),
    member(f(0,TimeA,DTimeA),Interpretation),
    member(f(0,TimeB,DTimeB),Interpretation),
    timestamp2readable(TimeA,RTimeA),
    timestamp2readable(TimeB,RTimeB),
    capitalize(Event,UEvent),
    atomic_list_concat(['*',UEvent,'from',RTimeA,'to',RTimeB],' ',Output),
    format(Output,[]).

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

% november -> 'November'
capitalize(Lower,Upper) :-
    atom_codes(Lower,[H|T]),
    to_upper(H,UpperH),
    atom_codes(Upper,[UpperH|T]).

ourFormat2List(Our,T) :-
    atomic_list_concat(['t'|T],'_',Our).

curtUpdate(Input,Moves,run):-
   kellerStorage(Input,Readings), !,
   updateHistory(Input),
   (
      Readings=[que(X,R,S)|_],
      models(OldModels),
      answerQuestion(que(X,R,S),OldModels,Moves)
   ;  
      \+ Readings=[que(_,_,_)|_],
      formatTime(Readings,NewReadings),
      consistentReadings(NewReadings,[]-ConsReadings,[]-Models),
      operateModels(Models,NewModels),
      (
         ConsReadings=[],
         Moves=[contradiction]
      ;
         \+ ConsReadings=[],
         informativeReadings(ConsReadings,[]-InfReadings),   
         (
            InfReadings=[],
            Moves=[obvious]
         ;  
            \+ InfReadings=[],
            Moves=[accept]
         ),
         combine(ConsReadings,CombinedReadings), 
         updateReadings(CombinedReadings),
         updateModels(NewModels)
      )
   ).

curtUpdate(_,[noparse],run).

operateModels([Model],[NewModel]) :-
    operateModel(Model,NewModel).

operateModel(model(Domain,Interpretation),NewModel) :-
    member(f(1,time,TimeDomain),Interpretation),
    filterEntries(Interpretation,TimeDomain,TimeEntries),
    length(TimeEntries,TELength),
    length(TimeDomain,TDLength),
    Excess is TELength - TDLength,
    expandDomain(Domain,Excess,NewDomain),
    stripOtherElements(Interpretation,NewDomain,NewTimeDomain),
    associate(TimeEntries,NewTimeDomain,Association),
    distinguish(TimeEntries,Association,NewTE),
    replaceTimeEntries(TimeEntries,NewTE,Interpretation,NewI),
    reworkTime(NewTE,NewI,NewerI),
    reworkEvent(NewerI,Association,NewestI),
    NewModel = model(NewDomain,NewestI).

reworkEvent(Interpretation,Association,[f(3,evt,NewTriples)|IntermediateI]) :-
    member(f(3,evt,Triples),Interpretation),
    newTriples(Triples,Association,NewTriples),
    delete(Interpretation,f(3,evt,Triples),IntermediateI).

newTriples([],_,[]).
newTriples([(T,A,B)|Ts],Association,[(T,A,B),(T,NA,NB)|NewTs]) :-
    findall(NewA,
        member([NewA,A,_],Association),
    NewAs),
    findall(NewB,
        member([NewB,B,_],Association),
    NewBs),
    delete(NewAs,A,NewAs2),
    delete(NewBs,B,NewBs2),
    NewAs2 = [NA],
    NewBs2 = [NB],
    newTriples(Ts,Association,NewTs).
newTriples([(T,A,B)|Ts],Association,[(T,A,B)|NewTs]) :-
    findall(NewA,
        member([NewA,A,_],Association),
    NewAs),
    findall(NewB,
        member([NewB,B,_],Association),
    NewBs),
    delete(NewAs,A,NewAs2),
    delete(NewBs,B,NewBs2),
    \+ NewAs2 = [_],
    \+ NewBs2 = [_],
    newTriples(Ts,Association,NewTs).

associate([],_,[]).

associate([f(0,C,Element)|T],Domain,[[Element,Element,C]|NewT]) :-
    member(Element,Domain),
    delete(Domain,Element,NewDomain),
    associate(T,NewDomain,NewT).

associate([f(0,C,Element)|T],Domain,[[AnotherE,Element,C]|NewT]) :-
    \+ member(Element,Domain),
    member(AnotherE,Domain),
    delete(Domain,AnotherE,NewDomain),
    associate(T,NewDomain,NewT).

stripOtherElements(Interpretation,FullDomain,TimeDomain) :-
    member(f(1,time,OldTimeDomain),Interpretation),
    findall(D,(
        member(f(0,_,D),Interpretation),
        \+ member(D,OldTimeDomain)
    ),OtherDomain),
    subtract(FullDomain,OtherDomain,TimeDomain).

reworkTime(TimeEntries,Interpretation,[f(1,time,Times)|NewI]) :-
    delete(Interpretation,f(1,time,_),NewI),
    extractDomain(TimeEntries,Times).

replaceTimeEntries(TE,NewTE,Interpretation,NewI) :-
    subtract(Interpretation,TE,Intermediate),
    append(Intermediate,NewTE,NewI).

distinguish([],_,[]).
distinguish([f(0,C,E)|T],Assocs,[f(0,C,TE)|NewT]) :-
    member([TE,E,C],Assocs),
    distinguish(T,Assocs,NewT).

extractDomain(Interpretation,Domain) :-
    findall(X,member(f(0,_,X),Interpretation),Domain).

expandDomain(D,Excess,NewD) :-
    length(D,DLength),
    NewLength is DLength + Excess,
    findall(X,between(1,NewLength,X),Range),
    range2domain(Range,NewD).

range2domain([],[]).
range2domain([N|Ns],[D|Ds]) :-
    atom_number(A,N),
    atom_concat('d',A,D),
    range2domain(Ns,Ds).

filterEntries(I,D,Output) :-
    findall(f(0,C,(Element)),(
        member(f(0,C,Element),I),
        member(Element,D)
    ),Output).

formatTime([evt(movie,TimeA,TimeB)],[evt(movie,TimestampA,TimestampB)]) :-
    convertTime(TimeA,TimestampA),
    convertTime(TimeB,TimestampB).

formatTime([Reading],[Reading]) :-
    compose(Reading,Sym,_),
    \+ Sym = evt.

convertTime(MHour,TimeStamp) :-
    addM(MHour,Hour),
    form_time([now,Y-Mo-D]),
    form_time([now,_:_:_]),
    atom_number(YA,Y),
    atom_number(MoA,Mo),
    atom_number(DA,D),
    atomic_list_concat(['t',YA,MoA,DA,Hour,'0'],'_',TimeStamp).

% '7pm' -> '19', '7am' -> '7'
addM(MTime,Time) :-
    atom_length(MTime,L),
    B is L-2,
    sub_atom(MTime,B,2,0,Trail),
    member(Trail,['am','pm']),
    sub_atom(MTime,0,_,2,HA),
    atom_number(HA,H),
    (Trail = 'am', N = H ; Trail = 'pm', N is H+12),
    atom_number(Time,N).



%formatTime([movie,from,'7am',to,'9am',on,friday],
%    [movie,from,t2014_11_28_19_0_0,to,t2014_11_28_21_0_0,on,friday]).

/*========================================================================
   Combine New Utterances with History
========================================================================*/

combine(New,New):-
   readings([]).

combine(Readings,Updated):-
   readings([Old|_]),
   findall(and(Old,New),memberList(New,Readings),Updated).


/*========================================================================
   Select Consistent Readings
========================================================================*/

consistentReadings([],C-C,M-M).

consistentReadings([New|Readings],C1-C2,M1-M2):-
   readings(Old),
   (
      consistent(Old,New,Model), !,
      NewModel = Model,
      consistentReadings(Readings,[New|C1]-C2,[NewModel|M1]-M2) 
   ;
      consistentReadings(Readings,C1-C2,M1-M2) 
   ).



/*========================================================================
   Consistency Checking calling Theorem Prover and Model Builder
========================================================================*/

consistent([Old|_],New,Model):-
   backgroundKnowledge(and(Old,New),BK),
   DomainSize=15,
   callTPandMB(not(and(and(BK,Old),New)),and(and(BK,Old),New),DomainSize,Proof,Model,Engine),
   format('~nMessage (consistency checking): ~p found a result.',[Engine]),
   \+ Proof=proof, Model=model([_|_],_).

consistent([],New,Model):-
   backgroundKnowledge(New,BK),
   DomainSize=15,
   callTPandMB(not(and(BK,New)),and(BK,New),DomainSize,Proof,Model,Engine),
   format('~nMessage (consistency checking): ~p found a result.',[Engine]),
   \+ Proof=proof, Model=model([_|_],_).


/*========================================================================
   Select Informative Readings
========================================================================*/

informativeReadings([],I-I).

informativeReadings([New|L],I1-I2):-
   readings(Old),
   (
      informative(Old,New), !,
      informativeReadings(L,[New|I1]-I2) 
   ;
      informativeReadings(L,I1-I2) 
   ).


/*========================================================================
   Informativity Checking calling Theorem Prover
========================================================================*/

informative([Old|_],New):-
   backgroundKnowledge(and(Old,New),BK),
   DomainSize=15,
   callTPandMB(not(and(and(BK,Old),not(New))),and(and(BK,Old),not(New)),DomainSize,Proof,Model,Engine),
   format('~nMessage (informativity checking): ~p found a result.',[Engine]),
   \+ Proof=proof, Model=model([_|_],_).  

informative([],New):-
   backgroundKnowledge(New,BK),
   DomainSize=15,
   callTPandMB(not(and(BK,not(New))),and(BK,not(New)),DomainSize,Proof,Model,Engine),
   format('~nMessage (informativity checking): ~p found a result.',[Engine]),
   \+ Proof=proof, Model=model([_|_],_).


/*========================================================================
    Answer Questions
========================================================================*/

answerQuestion(que(X,R,S),Models,Moves):-
   (
      Models=[Model|_],
      satisfy(some(X,and(R,S)),Model,[],Result), 
      \+ Result=undef,
      !,     
      findall(A,satisfy(and(R,S),Model,[g(X,A)],pos),Answers),
      realiseAnswer(Answers,que(X,R,S),Model,String),
      Moves=[sensible_question,answer(String)]
   ;
      Moves=[unknown_answer]
   ).


/*========================================================================
    Realise all answers
========================================================================*/

realiseAnswer([],_,_,'none').

realiseAnswer([Value],Q,Model,String):-
   realiseString(Q,Value,Model,String).

realiseAnswer([Value1,Value2|Values],Q,Model,String):-
   realiseString(Q,Value1,Model,String1),
   realiseAnswer([Value2|Values],Q,Model,String2),
   list2string([String1,and,String2],String).


/*========================================================================
    Realise a single answer
========================================================================*/

realiseString(que(X,R,S),Value,Model,String):-
   kellerStorage:lexEntry(pn,[symbol:Symbol,syntax:Answer|_]),
   satisfy(eq(Y,Symbol),Model,[g(Y,Value)],pos), !,
   checkAnswer(some(X,and(eq(X,Symbol),and(R,S))),Proof),
   (
      Proof=proof, !,
      list2string(Answer,String)
   ;
      list2string([maybe|Answer],String)
   ).

realiseString(que(X,R,S),Value,Model,String):-
   kellerStorage:lexEntry(noun,[symbol:Symbol,syntax:Answer|_]), 
   compose(Formula,Symbol,[X]),
   satisfy(Formula,Model,[g(X,Value)],pos), !,
   checkAnswer(some(X,and(Formula,and(R,S))),Proof),
   (
      Proof=proof, !,
      list2string([a|Answer],String)
   ;
      list2string([maybe,a|Answer],String)
   ).

realiseString(_,Value,_,Value).


/*========================================================================
   Answer Checking
========================================================================*/

checkAnswer(Answer,Proof):-
   readings([F|_]),
   backgroundKnowledge(F,BK),
   callTP(imp(and(F,BK),Answer),Proof,Engine),
   format('~nMessage (answer checking): ~p found result "~p".',[Engine,Proof]).


/*========================================================================
   Info
========================================================================*/

info:-
   format('~n> ---------------------------------------------------------- <',[]),
   format('~n> helpfulCurt.pl, by Patrick Blackburn and Johan Bos         <',[]),
   format('~n>                                                            <',[]),
   format('~n> ?- curt.                - start a dialogue with Curt       <',[]),
   format('~n>                                                            <',[]),
   format('~n> Type "help" to get more information about features         <',[]),
   format('~n> ---------------------------------------------------------- <',[]),
   format('~n~n',[]).



/*========================================================================
   Display info at start
========================================================================*/

:- info.

 
