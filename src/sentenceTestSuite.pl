/*************************************************************************

    File: sentenceTestSuite.pl
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

:- module(sentenceTestSuite,[sentence/2]).


/*========================================================================
   Sentences
========================================================================*/

sentence([lunch,from,'3pm',to,'5pm',if,'1pm',event],1).

sentence([show,my,appointments],1).

sentence([movie,from,'7am',to,'9am',on,friday],1).

sentence([movie,from,'7am',to,'9am'],1).

sentence([movie,from,'7pm',to,'9pm',in,'3days'],1).

sentence([movie],1).

sentence([movie,from,movie],1).

sentence([a,movie],1).

sentence([a,movie,walks],1).



