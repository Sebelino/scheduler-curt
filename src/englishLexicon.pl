/*************************************************************************

    File: englishLexicon.pl
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

:- use_module(times,[timeEntry/1,dayEntry/1,exactDateEntry/3]).

/*
 * wh-embedding verbs
 * cf karttunen 77 for the complete classification according to 'type'
 */
lexEntry(ivtbar,[symbol:knowledge,syntax:[know],inf:inf,num:sg,type:factive]).
lexEntry(ivtbar,[symbol:knowledge,syntax:[knows],inf:fin,num:sg,type:factive]).
lexEntry(ivtbar,[symbol:knowledge,syntax:[know],inf:fin,num:pl,type:factive]).

lexEntry(ivtbar,[symbol:report,syntax:[report],inf:inf,num:sg,type:resolutive]).
lexEntry(ivtbar,[symbol:report,syntax:[reports],inf:fin,num:sg,type:resolutive]).
lexEntry(ivtbar,[symbol:report,syntax:[report],inf:fin,num:pl,type:resolutive]).

lexEntry(ivtbar,[symbol:believe,syntax:[believe],inf:inf,num:sg,type:propos]).
lexEntry(ivtbar,[symbol:believe,syntax:[believes],inf:fin,num:sg,type:propos]).
lexEntry(ivtbar,[symbol:believe,syntax:[believe],inf:fin,num:pl,type:propos]).

lexEntry(ivtbar,[symbol:wonder,syntax:[wonder],inf:inf,num:sg,type:question]).
lexEntry(ivtbar,[symbol:wonder,syntax:[wonders],inf:fin,num:sg,type:question]).
lexEntry(ivtbar,[symbol:wonder,syntax:[wonder],inf:fin,num:pl,type:question]).

/*========================================================================
   Determiners
========================================================================*/

lexEntry(det,[syntax:[every],mood:decl,type:uni]).
lexEntry(det,[syntax:[a],mood:decl,type:indef]).
lexEntry(det,[syntax:[the],mood:decl,type:def]).
lexEntry(det,[syntax:[which],mood:int,type:wh]).


/*========================================================================
   Nouns
========================================================================*/

lexEntry(evt,[symbol:movie,syntax:[movie]]).
lexEntry(evt,[symbol:class,syntax:[class]]).
lexEntry(evt,[symbol:meeting,syntax:[meeting]]).
lexEntry(evt,[symbol:exercise,syntax:[exercise]]).
lexEntry(evt,[symbol:breakfast,syntax:[breakfast]]).
lexEntry(evt,[symbol:lunch,syntax:[lunch]]).
lexEntry(evt,[symbol:dinner,syntax:[dinner]]).

lexEntry(evt,[symbol:monday,syntax:[monday]]).
lexEntry(evt,[symbol:tuesday,syntax:[tuesday]]).
lexEntry(evt,[symbol:wednesday,syntax:[wednesday]]).
lexEntry(evt,[symbol:thursday,syntax:[thursday]]).
lexEntry(evt,[symbol:friday,syntax:[friday]]).
lexEntry(evt,[symbol:saturday,syntax:[saturday]]).
lexEntry(evt,[symbol:sunday,syntax:[sunday]]).

lexEntry(evt,[symbol:tomorrow,syntax:[tomorrow]]).
lexEntry(evt,[symbol:nextweek,syntax:[next,week]]).

lexEntry(time,[symbol:Syntax,syntax:[Syntax]]) :-
    timeEntry(Syntax).

lexEntry(time,[symbol:Syntax,syntax:[Syntax]]) :-
    dayEntry(Syntax).

lexEntry(time,[symbol:[Date,Month,Year],syntax:[Date,Month,Year]]) :-
    exactDateEntry(Date,Month,Year).

lexEntry(adj,[symbol:my,syntax:[my]]).
lexEntry(adj,[symbol:all,syntax:[all]]).

lexEntry(noun,[symbol:appointment,syntax:[appointments]]).
lexEntry(noun,[symbol:appointment,syntax:[events]]).
lexEntry(noun,[symbol:appointment,syntax:[schedule]]).

lexEntry(noun,[symbol:animal,syntax:[animal]]).
lexEntry(noun,[symbol:beverage,syntax:[beverage]]).
lexEntry(noun,[symbol:building,syntax:[building]]).
lexEntry(noun,[symbol:cup,syntax:[cup]]).
lexEntry(noun,[symbol:burger,syntax:[burger]]).
lexEntry(noun,[symbol:boxer,syntax:[boxer]]).
lexEntry(noun,[symbol:boss,syntax:[boss]]).
lexEntry(noun,[symbol:car,syntax:[car]]).
lexEntry(noun,[symbol:chainsaw,syntax:[chainsaw]]).
lexEntry(noun,[symbol:criminal,syntax:[criminal]]).
lexEntry(noun,[symbol:customer,syntax:[customer]]).
lexEntry(noun,[symbol:drug,syntax:[drug]]).
lexEntry(noun,[symbol:episode,syntax:[episode]]).
lexEntry(noun,[symbol:fdshake,syntax:[five,dollar,shake]]).
lexEntry(noun,[symbol:footmassage,syntax:[foot,massage]]).
lexEntry(noun,[symbol:gimp,syntax:[gimp]]).
lexEntry(noun,[symbol:glass,syntax:[glass]]).
lexEntry(noun,[symbol:gun,syntax:[gun]]).
lexEntry(noun,[symbol:hammer,syntax:[hammer]]).
lexEntry(noun,[symbol:hashbar,syntax:[hash,bar]]).
lexEntry(noun,[symbol:person,syntax:[person]]).
lexEntry(noun,[symbol:husband,syntax:[husband]]).
lexEntry(noun,[symbol:joke,syntax:[joke]]).
lexEntry(noun,[symbol:man,syntax:[man]]).
lexEntry(noun,[symbol:needle,syntax:[needle]]).
lexEntry(noun,[symbol:owner,syntax:[owner]]).
lexEntry(noun,[symbol:piercing,syntax:[piercing]]).
lexEntry(noun,[symbol:plant,syntax:[plant]]).
lexEntry(noun,[symbol:qpwc,syntax:[quarter,pounder,with,cheese]]).
lexEntry(noun,[symbol:radio,syntax:[radio]]).
lexEntry(noun,[symbol:restaurant,syntax:[restaurant]]).
lexEntry(noun,[symbol:robber,syntax:[robber]]).
lexEntry(noun,[symbol:suitcase,syntax:[suitcase]]).
lexEntry(noun,[symbol:shotgun,syntax:[shotgun]]).
lexEntry(noun,[symbol:sword,syntax:[sword]]).
lexEntry(noun,[symbol:vehicle,syntax:[vehicle]]).
lexEntry(noun,[symbol:weapon,syntax:[weapon]]).
lexEntry(noun,[symbol:wife,syntax:[wife]]).
lexEntry(noun,[symbol:woman,syntax:[woman]]).
lexEntry(noun,[symbol:woman,syntax:[woman]]).

/*========================================================================
   Proper Names
========================================================================*/

lexEntry(pn,[symbol:butch,syntax:[butch]]).
lexEntry(pn,[symbol:esmarelda,syntax:[esmarelda]]).
lexEntry(pn,[symbol:honey_bunny,syntax:[honey,bunny]]).
lexEntry(pn,[symbol:jimmy,syntax:[jimmy]]).
lexEntry(pn,[symbol:jody,syntax:[jody]]).
lexEntry(pn,[symbol:jules,syntax:[jules]]).
lexEntry(pn,[symbol:lance,syntax:[lance]]).
lexEntry(pn,[symbol:marsellus,syntax:[marsellus]]).
lexEntry(pn,[symbol:marsellus,syntax:[marsellus,wallace]]).
lexEntry(pn,[symbol:marvin,syntax:[marvin]]).
lexEntry(pn,[symbol:mia,syntax:[mia]]).
lexEntry(pn,[symbol:mia,syntax:[mia,wallace]]).
lexEntry(pn,[symbol:pumpkin,syntax:[pumpkin]]).
lexEntry(pn,[symbol:thewolf,syntax:[the,wolf]]).
lexEntry(pn,[symbol:vincent,syntax:[vincent]]).
lexEntry(pn,[symbol:vincent,syntax:[vincent,vega]]).
lexEntry(pn,[symbol:yolanda,syntax:[yolanda]]).


/*========================================================================
   Quantified Noun Phrases
========================================================================*/

lexEntry(qnp,[symbol:person,syntax:[who],mood:int,type:wh]).
lexEntry(qnp,[symbol:thing,syntax:[what],mood:int,type:wh]).


/*========================================================================
   Intransitive Verbs
========================================================================*/

lexEntry(iv,[symbol:collapse,syntax:[collapse],inf:inf,num:sg]).
lexEntry(iv,[symbol:collapse,syntax:[collapses],inf:fin,num:sg]).
lexEntry(iv,[symbol:collapse,syntax:[collapse],inf:fin,num:pl]).

lexEntry(iv,[symbol:dance,syntax:[dance],inf:inf,num:sg]).
lexEntry(iv,[symbol:dance,syntax:[dances],inf:fin,num:sg]).
lexEntry(iv,[symbol:dance,syntax:[dance],inf:fin,num:pl]).

lexEntry(iv,[symbol:die,syntax:[die],inf:inf,num:sg]).
lexEntry(iv,[symbol:die,syntax:[dies],inf:fin,num:sg]).
lexEntry(iv,[symbol:die,syntax:[die],inf:fin,num:pl]).

lexEntry(iv,[symbol:growl,syntax:[growl],inf:inf,num:sg]).
lexEntry(iv,[symbol:growl,syntax:[growls],inf:fin,num:sg]).
lexEntry(iv,[symbol:growl,syntax:[growl],inf:fin,num:pl]).

lexEntry(iv,[symbol:playairguitar,syntax:[play,air,guitar],inf:inf,num:sg]).
lexEntry(iv,[symbol:playairguitar,syntax:[plays,air,guitar],inf:fin,num:sg]).
lexEntry(iv,[symbol:playairguitar,syntax:[play,air,guitar],inf:fin,num:pl]).

lexEntry(iv,[symbol:smoke,syntax:[smoke],inf:inf,num:sg]).
lexEntry(iv,[symbol:smoke,syntax:[smokes],inf:fin,num:sg]).
lexEntry(iv,[symbol:smoke,syntax:[smoke],inf:fin,num:pl]).

lexEntry(iv,[symbol:snort,syntax:[snort],inf:inf,num:sg]).
lexEntry(iv,[symbol:snort,syntax:[snorts],inf:fin,num:sg]).
lexEntry(iv,[symbol:snort,syntax:[snort],inf:fin,num:pl]).

lexEntry(iv,[symbol:shriek,syntax:[shriek],inf:inf,num:sg]).
lexEntry(iv,[symbol:shriek,syntax:[shrieks],inf:fin,num:sg]).
lexEntry(iv,[symbol:shriek,syntax:[shriek],inf:fin,num:pl]).

lexEntry(iv,[symbol:walk,syntax:[walk],inf:inf,num:sg]).
lexEntry(iv,[symbol:walk,syntax:[walks],inf:fin,num:sg]).
lexEntry(iv,[symbol:walk,syntax:[walk],inf:fin,num:pl]).


/*========================================================================
   Transitive Verbs
========================================================================*/

lexEntry(tv,[symbol:clean,syntax:[clean],inf:inf,num:sg]).
lexEntry(tv,[symbol:clean,syntax:[cleans],inf:fin,num:sg]).
lexEntry(tv,[symbol:clean,syntax:[clean],inf:fin,num:pl]).

lexEntry(tv,[symbol:drink,syntax:[drink],inf:inf,num:sg]).
lexEntry(tv,[symbol:drink,syntax:[drinks],inf:fin,num:sg]).
lexEntry(tv,[symbol:drink,syntax:[drink],inf:fin,num:pl]).

lexEntry(tv,[symbol:date,syntax:[date],inf:inf,num:sg]).
lexEntry(tv,[symbol:date,syntax:[dates],inf:fin,num:sg]).
lexEntry(tv,[symbol:date,syntax:[date],inf:fin,num:pl]).

lexEntry(tv,[symbol:discard,syntax:[discard],inf:inf,num:sg]).
lexEntry(tv,[symbol:discard,syntax:[discards],inf:fin,num:sg]).
lexEntry(tv,[symbol:discard,syntax:[discard],inf:fin,num:pl]).

lexEntry(tv,[symbol:eat,syntax:[eat],inf:inf,num:sg]).
lexEntry(tv,[symbol:eat,syntax:[eats],inf:fin,num:sg]).
lexEntry(tv,[symbol:eat,syntax:[eat],inf:fin,num:pl]).

lexEntry(tv,[symbol:enjoy,syntax:[enjoy],inf:inf,num:sg]).
lexEntry(tv,[symbol:enjoy,syntax:[enjoys],inf:fin,num:sg]).
lexEntry(tv,[symbol:enjoy,syntax:[enjoy],inf:fin,num:pl]).

lexEntry(tv,[symbol:hate,syntax:[hate],inf:inf,num:sg]).
lexEntry(tv,[symbol:hate,syntax:[hates],inf:fin,num:sg]).
lexEntry(tv,[symbol:hate,syntax:[hate],inf:fin,num:pl]).

lexEntry(tv,[symbol:have,syntax:[have],inf:inf,num:sg]).
lexEntry(tv,[symbol:have,syntax:[has],inf:fin,num:sg]).
lexEntry(tv,[symbol:have,syntax:[have],inf:fin,num:pl]).

lexEntry(tv,[symbol:kill,syntax:[kill],inf:inf,num:sg]).
lexEntry(tv,[symbol:kill,syntax:[kills],inf:fin,num:sg]).
lexEntry(tv,[symbol:kill,syntax:[kill],inf:fin,num:pl]).

lexEntry(tv,[symbol:know,syntax:[know],inf:inf,num:sg]).
lexEntry(tv,[symbol:know,syntax:[knows],inf:fin,num:sg]).
lexEntry(tv,[symbol:know,syntax:[know],inf:fin,num:pl]).

lexEntry(tv,[symbol:like,syntax:[like],inf:inf,num:sg]).
lexEntry(tv,[symbol:like,syntax:[likes],inf:fin,num:sg]).
lexEntry(tv,[symbol:like,syntax:[like],inf:fin,num:pl]).

lexEntry(tv,[symbol:love,syntax:[love],inf:inf,num:sg]).
lexEntry(tv,[symbol:love,syntax:[loves],inf:fin,num:sg]).
lexEntry(tv,[symbol:love,syntax:[love],inf:fin,num:pl]).

lexEntry(tv,[symbol:pickup,syntax:[pick,up],inf:inf,num:sg]).
lexEntry(tv,[symbol:pickup,syntax:[picks,up],inf:fin,num:sg]).
lexEntry(tv,[symbol:pickup,syntax:[pick,up],inf:fin,num:pl]).

lexEntry(tv,[symbol:shoot,syntax:[shot],inf:inf,num:sg]).
lexEntry(tv,[symbol:shoot,syntax:[shot],inf:fin,num:sg]). % interesting. they allow past tense :-)
lexEntry(tv,[symbol:shoot,syntax:[shoots],inf:fin,num:sg]).
lexEntry(tv,[symbol:shoot,syntax:[shoot],inf:fin,num:pl]).

lexEntry(tv,[symbol:show,syntax:[show],inf:fin,num:sg]).
lexEntry(tv,[symbol:show,syntax:[list],inf:fin,num:sg]).
lexEntry(tv,[symbol:show,syntax:[display],inf:fin,num:sg]).


/*========================================================================
   Copula
========================================================================*/

lexEntry(cop,[pol:pos,syntax:[is],inf:fin,num:sg]).
lexEntry(cop,[pol:neg,syntax:[is,not],inf:fin,num:sg]).
lexEntry(cop,[pol:pos,syntax:[are],inf:fin,num:pl]).
lexEntry(cop,[pol:neg,syntax:[are,not],inf:fin,num:pl]).


/*========================================================================
   Prepositions
========================================================================*/

lexEntry(prep,[symbol:from,syntax:[from]]).
lexEntry(prep,[symbol:to,syntax:[to]]).
lexEntry(prep,[symbol:on,syntax:[on]]).
lexEntry(prep,[symbol:after,syntax:[after]]).
lexEntry(prep,[symbol:in,syntax:[in]]).

/*========================================================================
   Adjectives
========================================================================*/

lexEntry(adj,[symbol:big,syntax:[big]]).
lexEntry(adj,[symbol:blue,syntax:[blue]]).
lexEntry(adj,[symbol:female,syntax:[female]]).
lexEntry(adj,[symbol:happy,syntax:[happy]]).
lexEntry(adj,[symbol:kahuna,syntax:[kahuna]]).
lexEntry(adj,[symbol:male,syntax:[male]]).
lexEntry(adj,[symbol:married,syntax:[married]]).
lexEntry(adj,[symbol:red,syntax:[red]]).
lexEntry(adj,[symbol:sad,syntax:[sad]]).
lexEntry(adj,[symbol:small,syntax:[small]]).
lexEntry(adj,[symbol:tall,syntax:[tall]]).


/*========================================================================
   Relative Pronouns
========================================================================*/

lexEntry(relpro,[syntax:[who]]).
lexEntry(relpro,[syntax:[that]]).

/*
 * wh-embedders
 */
lexEntry(whemb,[syntax:[that],type:propos]).
lexEntry(whemb,[syntax:[whether],type:question]).
lexEntry(whemb,[syntax:[if],type:question]).

/*========================================================================
   Coordinations
========================================================================*/

lexEntry(coord,[syntax:[and],type:conj]).
lexEntry(coord,[syntax:[or],type:disj]).


/*========================================================================
   Auxiliary Verbs
========================================================================*/

lexEntry(av,[syntax:[does],inf:fin,num:sg,pol:pos]).
lexEntry(av,[syntax:[does,not],inf:fin,num:sg,pol:neg]).
lexEntry(av,[syntax:[did],inf:fin,num:sg,pol:pos]).
lexEntry(av,[syntax:[did,not],inf:fin,num:sg,pol:neg]).


