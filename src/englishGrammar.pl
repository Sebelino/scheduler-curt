/*************************************************************************

    File: englishGrammar.pl
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

/*========================================================================
   Texts
========================================================================*/

:- use_module(times,[formatTime/2]).

t([sem:T])--> 
   s([coord:no,sem:S]),
   {combine(t:T,[s:S])}.

t([sem:T])--> 
   s([coord:yes,sem:S]),
   {combine(t:T,[s:S])}.

t([sem:T])--> 
   np([coord:_,num:_,gap:_,sem:NP]),
   {combine(t:T,[np:NP])}.

t([sem:T2])--> 
   eventspec([sem:Eventspec]),
   {combine(t:T1,[eventspec:Eventspec])},
   {formatTime([T1],[T2])}.

t([sem:T2])--> 
   impspec([sem:Impspec]),
   {combine(t:T1,[impspec:Impspec])},
   {formatTime([T1],[T2])}.

t([sem:T])--> 
   show([sem:Show]),
   {combine(t:T,[show:Show])}.

t([sem:T])--> 
   noun([sem:Noun]),
   {combine(t:T,[noun:Noun])}.

t([sem:T])--> 
   q([sem:Q]),
   {combine(t:T,[q:Q])}.


/*========================================================================
   Sentences
========================================================================*/

s([coord:no,sem:Sem])--> 
   np([coord:_,num:Num,gap:[],sem:NP]), 
   vp([coord:_,inf:fin,num:Num,gap:[],sem:VP]), 
   {combine(s:Sem,[np:NP,vp:VP])}.

s([coord:yes,sem:Sem])--> 
   s([coord:ant,sem:S1]), 
   s([coord:con,sem:S2]), 
   {combine(s:Sem,[s:S1,s:S2])}.

s([coord:yes,sem:Sem])--> 
   s([coord:either,sem:S1]), 
   s([coord:or,sem:S2]), 
   {combine(s:Sem,[s:S1,s:S2])}.

s([coord:ant,sem:Sem])--> 
   [if], 
   s([coord:no,sem:S]),
   {combine(s:Sem,[if:S])}.

s([coord:either,sem:Sem])--> 
   [either], 
   s([coord:no,sem:S]),
   {combine(s:Sem,[either:S])}.

s([coord:con,sem:Sem])--> 
   [then], 
   s([coord:no,sem:S]),
   {combine(s:Sem,[then:S])}.

s([coord:con,sem:Sem])-->
   s([coord:no,sem:S]),
   {combine(s:Sem,[then:S])}.

s([coord:or,sem:Sem])-->
   [or], 
   s([coord:no,sem:S]),
   {combine(s:Sem,[or:S])}.

sinv([gap:G,sem:S])-->
   av([inf:fin,num:Num,sem:Sem]),
   np([coord:_,num:Num,gap:[],sem:NP]),
   vp([coord:_,inf:inf,num:Num,gap:G,sem:VP]), 
   {combine(sinv:S,[av:Sem,np:NP,vp:VP])}.


/*========================================================================
   Questions
========================================================================*/

q([sem:Sem])--> 
   whnp([num:Num,sem:NP]), 
   vp([coord:_,inf:fin,num:Num,gap:[],sem:VP]), 
   {combine(q:Sem,[whnp:NP,vp:VP])}.

q([sem:Sem])--> 
   whnp([num:_,sem:NP]), 
   sinv([gap:[np:NP],sem:S]),
   {combine(q:Sem,[sinv:S])}.

/*
 * Embedded Questions
 */

%todo: really coord:no for s? Bill knows that either Jane loves Mary or …
tbar([sem:TBar]) -->
	whemb([sem:WHemb])
	, s([coord:no,sem:S])
	, { combine(tbar:TBar,[whemb:WHemb,s:S]) }
	.

% for empty complementizers 'Mia knows Vincent snorts'
tbar([sem:TBar]) -->
	s([coord:no,sem:S])
	, { combine(tbar:TBar,[s:S]) }
	.

% for 'mia knows who likes vincent'
tbar([sem:TBar]) -->
	q([sem:Q])
	, { combine(tbar:TBar,[q:Q]) }
	.

/*========================================================================
   Noun Phrases
========================================================================*/

np([coord:no,num:sg,gap:[np:NP],sem:NP])--> [].

np([coord:yes,num:pl,gap:[],sem:NP])--> 
   np([coord:no,num:sg,gap:[],sem:NP1]), 
   coord([type:conj,sem:C]), 
   np([coord:_,num:_,gap:[],sem:NP2]), 
   {combine(np:NP,[np:NP1,coord:C,np:NP2])}.

np([coord:yes,num:sg,gap:[],sem:NP])--> 
   np([coord:no,num:sg,gap:[],sem:NP1]), 
   coord([type:disj,sem:C]), 
   np([coord:_,num:sg,gap:[],sem:NP2]), 
   {combine(np:NP,[np:NP1,coord:C,np:NP2])}.

np([coord:no,num:sg,gap:[],sem:NP])--> 
   det([mood:decl,type:_,sem:Det]), 
   n([coord:_,sem:N]), 
   {combine(np:NP,[det:Det,n:N])}.

np([coord:no,num:sg,gap:[],sem:NP])--> 
   pn([sem:PN]), 
   {combine(np:NP,[pn:PN])}.

np([coord:no,num:sg,gap:[],sem:NP])--> 
   qnp([mood:decl,sem:QNP]), 
   {combine(np:NP,[qnp:QNP])}.

/* Custom */

eventspec([sem:Eventspec])--> 
    evt([sem:Event]), 
    prep([sem:From]), 
    time([sem:TimeA]), 
    prep([sem:To]), 
    time([sem:TimeB]), 
    dayspec([sem:Dayspec]),
    {combine(eventspec:Eventspec,[evt:Event,prep:From,time:TimeA,prep:To,time:TimeB,dayspec:Dayspec])}.

eventspec([sem:Eventspec])--> 
    evt([sem:Event]), 
    prep([sem:From]), 
    time([sem:TimeA]), 
    prep([sem:To]), 
    time([sem:TimeB]), 
    {combine(eventspec:Eventspec,[evt:Event,prep:From,time:TimeA,prep:To,time:TimeB])}.

dayspec([sem:Dayspec])-->
    prep([sem:On]),
    evt([sem:Weekday]),
    {combine(dayspec:Dayspec,[prep:On,evt:Weekday])}.

dayspec([sem:Dayspec])-->
    prep([sem:On]),
    time([sem:ExactDate]),
    {combine(dayspec:Dayspec,[prep:On,time:ExactDate])}.

dayspec([sem:Dayspec])-->
    prep([sem:In]),
    time([sem:Dayoffset]),
    {combine(dayspec:Dayspec,[prep:In,time:Dayoffset])}.

dayspec([sem:Dayspec])-->
    evt([sem:Specificday]),
    {combine(dayspec:Dayspec,[evt:Specificday])}.

impspec([sem:Impspec])--> 
    eventspec([sem:Eventspec]),
    ['if'],
    time([sem:AtTime]), 
    ['event'], 
    {combine(impspec:Impspec,[eventspec:Eventspec,time:AtTime])}.

show([sem:Show])--> 
    tv([inf:_,num:_,sem:TV]), 
    adj([sem:Adj]), 
    noun([sem:Noun]), 
    {combine(show:Show,[tv:TV,adj:Adj,noun:Noun])}.


/*========================================================================
   WH Noun Phrases
========================================================================*/

whnp([num:sg,sem:NP])--> 
   qnp([mood:int,sem:QNP]), 
   {combine(whnp:NP,[qnp:QNP])}.

whnp([num:sg,sem:NP])--> 
   det([mood:int,type:_,sem:Det]), 
   n([coord:_,sem:N]), 
   {combine(whnp:NP,[det:Det,n:N])}.


/*========================================================================
   Nouns
========================================================================*/

n([coord:yes,sem:N])--> 
   n([coord:no,sem:N1]), 
   coord([type:_,sem:C]),  
   n([coord:_,sem:N2]),
   {combine(n:N,[n:N1,coord:C,n:N2])}.

n([coord:C,sem:Sem])--> 
   adj([sem:A]), 
   n([coord:C,sem:N]), 
   {combine(n:Sem,[adj:A,n:N])}.

n([coord:no,sem:N])--> 
   noun([sem:Noun]),
   {combine(n:N,[noun:Noun])}.

n([coord:no,sem:Sem])--> 
   noun([sem:N]), 
   nmod([sem:PP]),
   {combine(n:Sem,[noun:N,nmod:PP])}. 

nmod([sem:N])--> 
   pp([sem:PP]),
   {combine(nmod:N,[pp:PP])}.

nmod([sem:N])--> 
   rc([sem:RC]),
   {combine(nmod:N,[rc:RC])}.

nmod([sem:Sem])--> 
   pp([sem:PP]), 
   nmod([sem:NMod]),
   {combine(nmod:Sem,[pp:PP,nmod:NMod])}.


/*========================================================================
   Verb Phrases
========================================================================*/

vp([coord:no,inf:Inf,num:Num,gap:[],sem:VP]) -->
	ivtbar([inf:Inf,num:Num,sem:IVTBAR,type:question]) % verb
	, tbar([sem:TBAR]) % embedded sentence
	,
	{
		TBAR = [que(_,_,_)]
		, combine(vp:VP,[ivtbar:IVTBAR,tbar:TBAR])
	}
	.

vp([coord:no,inf:Inf,num:Num,gap:[],sem:VP]) -->
	ivtbar([inf:Inf,num:Num,sem:IVTBAR,type:propos]) % verb
	, tbar([sem:TBAR]) % embedded sentence
	,
	{
		\+ TBAR = [que(_,_,_)]
		, combine(vp:VP,[ivtbar:IVTBAR,tbar:TBAR])
	}
	.

vp([coord:no,inf:Inf,num:Num,gap:[],sem:VP]) -->
	ivtbar([inf:Inf,num:Num,sem:IVTBAR,type:resolutive]) % verb
	, tbar([sem:TBAR]) % embedded sentence
	, { combine(vp:VP,[ivtbar:IVTBAR,tbar:TBAR]) }
	.

vp([coord:no,inf:Inf,num:Num,gap:[],sem:VP]) -->
	ivtbar([inf:Inf,num:Num,sem:IVTBAR,type:factive]) % verb
	, tbar([sem:TBAR]) % embedded sentence
	, { combine(vp:VP,[ivtbar:IVTBAR,tbar:TBAR]) }
	.

vp([coord:yes,inf:Inf,num:Num,gap:[],sem:VP])--> 
   vp([coord:no,inf:Inf,num:Num,gap:[],sem:VP1]), 
   coord([type:_,sem:C]), 
   vp([coord:_,inf:Inf,num:Num,gap:[],sem:VP2]),
   {combine(vp:VP,[vp:VP1,coord:C,vp:VP2])}.

vp([coord:no,inf:Inf,num:Num,gap:[],sem:VP])--> 
   av([inf:Inf,num:Num,sem:Mod]), 
   vp([coord:_,inf:inf,num:Num,gap:[],sem:V2]), 
   {combine(vp:VP,[av:Mod,vp:V2])}.

vp([coord:no,inf:Inf,num:Num,gap:[],sem:VP])--> 
   cop([inf:Inf,num:Num,sem:Cop]), 
   np([coord:_,num:_,gap:[],sem:NP]), 
   {combine(vp:VP,[cop:Cop,np:NP])}.

vp([coord:no,inf:Inf,num:Num,gap:[],sem:VP])--> 
   iv([inf:Inf,num:Num,sem:IV]), 
   {combine(vp:VP,[iv:IV])}.

vp([coord:no,inf:I,num:Num,gap:G,sem:VP])-->   
   tv([inf:I,num:Num,sem:TV]), 
   np([coord:_,num:_,gap:G,sem:NP]), 
   {combine(vp:VP,[tv:TV,np:NP])}.


/*========================================================================
   Prepositional Phrases
========================================================================*/

pp([sem:PP])--> 
   prep([sem:Prep]), 
   np([coord:_,num:_,gap:[],sem:NP]), 
   {combine(pp:PP,[prep:Prep,np:NP])}.


/*========================================================================
   Relative Clauses
========================================================================*/

rc([sem:RC])--> 
   relpro([sem:RP]), 
   vp([coord:_,inf:fin,num:sg,gap:[],sem:VP]), 
   {combine(rc:RC,[relpro:RP,vp:VP])}.


/*========================================================================
   Lexical Rules
========================================================================*/

iv([inf:Inf,num:Num,sem:Sem])--> 
   {lexEntry(iv,[symbol:Sym,syntax:Word,inf:Inf,num:Num])},
   Word,
   {semLex(iv,[symbol:Sym,sem:Sem])}.

ivtbar([inf:Inf,num:Num,sem:Sem,type:Type])
-->	{lexEntry(ivtbar,[symbol:Sym,syntax:Word,inf:Inf,num:Num,type:Type])}
	, Word
	, {semLex(ivtbar,[symbol:Sym,sem:Sem,type:Type])}
.

tv([inf:Inf,num:Num,sem:Sem])--> 
   {lexEntry(tv,[symbol:Sym,syntax:Word,inf:Inf,num:Num])},
   Word,
   {semLex(tv,[symbol:Sym,sem:Sem])}.

cop([inf:Inf,num:Num,sem:Sem])--> 
   {lexEntry(cop,[pol:Pol,syntax:Word,inf:Inf,num:Num])},
   Word,
   {semLex(cop,[pol:Pol,sem:Sem])}.

det([mood:M,type:Type,sem:Det])--> 
   {lexEntry(det,[syntax:Word,mood:M,type:Type])},
   Word,
   {semLex(det,[type:Type,sem:Det])}. 

pn([sem:Sem])--> 
   {lexEntry(pn,[symbol:Sym,syntax:Word])},
   Word,
   {semLex(pn,[symbol:Sym,sem:Sem])}.

relpro([sem:Sem])--> 
   {lexEntry(relpro,[syntax:Word])},
   Word,
   {semLex(relpro,[sem:Sem])}.

% WH-embedding
% We don't use symbols because wh-embedders are translated to
% logic right away (using the respective storage method)
whemb([sem:Sem])
-->	{lexEntry(whemb,[syntax:Word,type:T])}
	, Word
	, {semLex(whemb,[sem:Sem,type:T])}
.

prep([sem:Sem])--> 
   {lexEntry(prep,[symbol:Sym,syntax:Word])},
   Word,
   {semLex(prep,[symbol:Sym,sem:Sem])}.

adj([sem:Sem])--> 
   {lexEntry(adj,[symbol:Sym,syntax:Word])},
   Word,
   {semLex(adj,[symbol:Sym,sem:Sem])}.

av([inf:Inf,num:Num,sem:Sem])--> 
   {lexEntry(av,[syntax:Word,inf:Inf,num:Num,pol:Pol])},
   Word,
   {semLex(av,[pol:Pol,sem:Sem])}.

coord([type:Type,sem:Sem])--> 
   {lexEntry(coord,[syntax:Word,type:Type])},
   Word, 
   {semLex(coord,[type:Type,sem:Sem])}.

qnp([mood:M,sem:NP])--> 
   {lexEntry(qnp,[symbol:Symbol,syntax:Word,mood:M,type:Type])},
   Word,
   {semLex(qnp,[type:Type,symbol:Symbol,sem:NP])}.

noun([sem:Sem])--> 
   {lexEntry(noun,[symbol:Sym,syntax:Word])},
   Word,
   {semLex(noun,[symbol:Sym,sem:Sem])}.

evt([sem:Sem])--> 
   {lexEntry(evt,[symbol:Sym,syntax:Word])},
   Word,
   {semLex(evt,[symbol:Sym,sem:Sem])}.

time([sem:Sem])--> 
   {lexEntry(time,[symbol:Sym,syntax:Word])},
   Word,
   {semLex(time,[symbol:Sym,sem:Sem])}.
