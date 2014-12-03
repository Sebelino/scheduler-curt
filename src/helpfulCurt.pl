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

:- module(curt,[curt/0,infix/0,prefix/0,currentDomain/2,crossproduct/3]).

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

:- use_module(library(julian),[form_time/1,
                               form_time/2,
                               julian_calendar_gregorian:month_number/2,
                               compare_time/3]).

:- use_module(times,[lessThan/2,
                     timestamp2readable/2,
                     capitalize/2]).

:- use_module(situationalKnowledge,[pairs2formulas/3,formulas2conjunctions/2]).


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


curtUpdate([show,my,appointments],[],run):-
    (
        models([M]),
        showModel(M)
    ) ;
    (
        models([]),
        format('Curt: Your schedule contains no events.',[])
    ).

curtUpdate(Input,Moves,run):-
   kellerStorage(Input,Readings), !,
   updateHistory(Input),
   (
      Readings=[que(X,R,S)|_],
      models(OldModels),
      answerQuestion(que(X,R,S),OldModels,Moves)
   ;  
      \+ Readings=[que(_,_,_)|_],
      operateReadings(Readings,NewReadings),
      consistentReadings(NewReadings,[]-ConsReadings,[]-Models),
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
         updateModels(Models)
      )
   ).

curtUpdate(_,[noparse],run).

showModel(model(_,Interpretation)):-
    member(f(3,evt,Events),Interpretation),
    showModel(Interpretation,Events).
showModel(_,[]).
showModel(Interpretation,[ (DEvent,DTimeA,DTimeB)|T]):-
    member(f(0,Event,DEvent),Interpretation),
    member(f(0,TimeA,DTimeA),Interpretation),
    member(f(0,TimeB,DTimeB),Interpretation),
    timestamp2readable(TimeA,RTimeA),
    timestamp2readable(TimeB,RTimeB),
    capitalize(Event,UEvent),
    atomic_list_concat(['*',UEvent,'from',RTimeA,'to',RTimeB],' ',Output),
    format(Output,[]),nl,
    showModel(Interpretation,T).

operateReadings([Reading],[NewReading]) :-
    operateReading(Reading,NewReading).

operateReading(evt(T,A,B),and(evt(T,A,B),lt(A,B))) :-
    lessThan(A,B),
    models([]).

operateReading(evt(_,A,B),and(foo,not(foo))) :-
    \+ lessThan(A,B).
operateReading(impspec(evt(_,A,B),_),and(foo,not(foo))) :-
    \+ lessThan(A,B).

operateReading(evt(T,A,B),Reading) :-
    lessThan(A,B),
    SomeFormulas = [
        evt(T,A,B),
        lt(A,B)
    ],
    % Times
    currentDomain(time,CurrentTimes),
    crossproduct(CurrentTimes,[A,B],Pairs),
    stripEqualPairs(Pairs,NewPairs),
    Context = all(X,imp(eq(X,e1),not(eq(X,e2)))),
    pairs2formulas(NewPairs,map(e1,e2,Context),TimeFormulas),
    % Titles
    currentDomain(title,CurrentTitles),
    crossproduct(CurrentTitles,[T],TitlePairs),
    stripEqualPairs(TitlePairs,NewTitlePairs),
    pairs2formulas(NewTitlePairs,map(e1,e2,Context),TitleFormulas),
    % Finish
    append([SomeFormulas,TimeFormulas,TitleFormulas],Formulas),
    formulas2conjunctions(Formulas,Reading).

operateReading(impspec(evt(Title,From,To),At),Reading) :-
    lessThan(From,To),
    SomeFormulas = [
        title(Title),
        time(From),
        time(To),
        time(At),
        lt(From,To),
        impspec(Title,From,To,At)
    ],
    currentDomain(time,CurrentTimes),
    append(CurrentTimes,[From,To,At],AllTimes),
    Context = all(X,imp(eq(X,time1),not(eq(X,time2)))),
    context2formulas(AllTimes,AllTimes,map(time1,time2,Context),OtherFormulas),
    append(SomeFormulas,OtherFormulas,Formulas),
    formulas2conjunctions(Formulas,Reading).

context2formulas(X,Y,map(Var1,Var2,Context),Formulas):-
    crossproduct(X,Y,Pairs),
    stripEqualPairs(Pairs,NewPairs),
    pairs2formulas(NewPairs,map(Var1,Var2,Context),Formulas).

context2conjunctions(X,Y,Map,Reading):-
    context2formulas(X,Y,Map,Formulas),
    formulas2conjunctions(Formulas,Reading).

currentDomain(_,[]) :- models([]).
currentDomain(Domain,Timestamps) :-
    models([model(_,I)]),
    findall(C,(
        member(f(0,C,Element),I),
        member(f(1,Domain,Elements),I),
        member(Element,Elements)
    ),Timestamps).

stripEqualPairs(Pairs,NewPairs) :-
    findall([E1,E2],(
        member([E1,E2],Pairs),
        \+ E1 = E2
    ),NewPairs).

crossproduct(E1s,E2s,Product) :-
    findall([E1,E2],(
        member(E1,E1s),
        member(E2,E2s)
    ),Product).

operateModels([],[]).
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
    replaceTimeEntries(TimeEntries,NewTE,Interpretation,I2),
    reworkTime(NewTE,I2,I3),
    reworkEvent(I3,Association,I4),
    %addLt(I4,I5),
    I5 = I4,
    NewModel = model(NewDomain,I5).

addLt(Interpretation,NewI) :-
    member(f(3,evt,Triples),Interpretation),
    findall( (A,B),member( (_,A,B),Triples),LtPairs),
    stripFalseLtPairs(LtPairs,Interpretation,TrueLtPairs),
    LtEntries = [f(2,lt,TrueLtPairs)],
    append(Interpretation,LtEntries,NewI).

stripFalseLtPairs([],_,[]).
stripFalseLtPairs([(E1,E2)|LtPairs],Interpretation,[(E1,E2)|TrueLtPairs]) :-
    member(f(0,Stamp1,E1),Interpretation),
    member(f(0,Stamp2,E2),Interpretation),
    lessThan(Stamp1,Stamp2),
    stripFalseLtPairs(LtPairs,Interpretation,TrueLtPairs).
stripFalseLtPairs([(E1,E2)|LtPairs],Interpretation,TrueLtPairs) :-
    member(f(0,Stamp1,E1),Interpretation),
    member(f(0,Stamp2,E2),Interpretation),
    \+ lessThan(Stamp1,Stamp2),
    stripFalseLtPairs(LtPairs,Interpretation,TrueLtPairs).

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

 
