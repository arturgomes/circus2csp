# This is a Circus to CSPm translator

***
#### Version used:

> Glasgow Haskell Compiler, Version 7.8.3, stage 2 booted by GHC version 7.6.2

> Isabelle/HOL 2016-1

####Main files used from Jaza to the Circus Translator to CSP

* Animate.lhs
	+ Here you find the animator functions and also where we include the Omega mappings and Circus to CSP mappings.
* AST.lhs
	+ Both Z and Circus AST are found here.
* CircusUI.lhs
	+ Circus Parser Interface build on based on Jaza UI (TextUI.lhs)
* DefSets.lhs
	+ Functions used for manipulating lists (Z Sets and sequences, as well as calculating the provisos from the Circus Refinement laws)
* MappingFunCircusCSP.lhs
	+ Mapping Functions - Circus to CSP
* MappingFunStatelessCircus.lhs
	+ Mapping Omega Functions from Circus to Circus
* Parse.lhs
	+ Circus Parser on top of JAZA
* TextUI.lhs
	+ This file is used for the interface of Jaza, before the Circus Parser.


***
#### Isabelle/HOL

* The version used is Isabelle2016-1
* The files translated with haskabelle can be found in:
  + ./test_haskabelle/haskabelle/
  + AST.thy
  + MinimalExample.thy
  + Prelude.thy
  + MappingFunStatelessCircus.thy
  + OmegaDefs.thy
  + TestingMappingFunStatelessCircus.thy

***

Artur: you need to explain in here what the various bits are and how to make them work.

In particular, whihch versions of the GHC compiler and Isabelle should be used.