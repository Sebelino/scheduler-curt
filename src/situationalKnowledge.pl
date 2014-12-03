/*************************************************************************

    File: situationalKnowledge.pl
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

:- module(situationalKnowledge,[situationalKnowledge/1,pairs2formulas/3,formulas2conjunctions/2]).

:- dynamic situationalKnowledge/1.

:- use_module(comsemPredicates,[compose/3]).

formulas2conjunctions([],and(foo,not(foo))).
formulas2conjunctions([F],F).
formulas2conjunctions([H|T],and(H,Tree)) :-
    formulas2conjunctions(T,Tree).

% Wrap a context for a formula around every element in the list.
% [a,b],and(x,Var) -> [and(x,a),and(x,b)]
list2formulas(List,map(Var,Context),Formulas) :-
    findall(Formula,(
        member(E,List),
        substitute(Var,E,Context,Formula)
    ),Formulas).

pairs2formulas(Pairs,map(Var1,Var2,Context),Formulas) :-
    term_to_atom(Context,ContextAtom),
    findall(Formula,(
        member([E1,E2],Pairs),
        replace(Var1,E1,ContextAtom,NewContextAtom),
        replace(Var2,E2,NewContextAtom,NewerContextAtom),
        term_to_atom(Formula,NewerContextAtom)
    ),Formulas).

% String replacement.
replace(Var,E,Atom,NewAtom) :-
    atomic_list_concat(Parts,Var,Atom),
    atomic_list_concat(Parts,E,NewAtom).

% Compound term substitution.
substitute(Var,E,Term,Term) :-
    simple(Term),
    Var == Term,
    E == Term, !.
substitute(X,_,Term,Term) :-
    simple(Term),
    \+ X == Term, !.
substitute(X,E,Term,NewTerm) :-
    compose(Term,Symbol,ArgList),
    findall(NewArg,(
        member(Arg,ArgList),
        substitute(X,E,Arg,NewArg)
    ),NewArgList),
    compose(NewTerm,Symbol,NewArgList).

/*========================================================================
   Axioms for Situational Knowledge
========================================================================*/

% If there is an event (T,A,B), then T is a title and A, B are times.
situationalKnowledge(Axiom):-
    Axiom = all(T,all(A,all(B,imp(evt(T,A,B),and(title(T),and(time(A),time(B))))))).

% For all events, start time != end time.
situationalKnowledge(Axiom):-
    Axiom = all(T,imp(title(T),all(A,imp(time(A),all(B,imp(time(B),imp(evt(T,A,B),not(eq(A,B))))))))).

% Titles are not times.
situationalKnowledge(Axiom):-
    Axiom = all(X,imp(title(X),not(time(X)))).

% Times are not titles.
situationalKnowledge(Axiom):-
    Axiom = all(X,imp(time(X),not(title(X)))).

% Implication calendar rule.
situationalKnowledge(Axiom):-
    Axiom = all(X,imp(time(X),all(Y,imp(time(Y),all(Z,imp(time(Z),all(T2,imp(title(T2),imp(some(A,and(time(A),some(B,and(time(B),some(T1,and(title(T1),and(evt(T1,A,B),and(impspec(T2,X,Y,Z),and(lt(A,Z),lt(Z,B)))))))))),evt(T2,X,Y)))))))))).

%% Two different times cannot be equal.
%situationalKnowledge(Axiom):-
%    currentTimes(Times),
%    crossproduct(Times,Times,Pairs),
%    Context = all(X,imp(and(time(X),and(eq(X,time1),eq(X,time2))),eq(time1,time2))),
%    pairs2formulas(Pairs,map(time1,time2,Context),Formulas),
%    formulas2conjunctions(Formulas,Tree),
%    Axiom = Tree.

%situationalKnowledge(Axiom):-
%    Axiom = all(T,all(A,all(B,imp(evt(T,A,B),lt(A,B))))).

%situationalKnowledge(Axiom):-
%    Axiom = all(A,all(B,imp(lt(A,B,not(lt(B,A)))))).
