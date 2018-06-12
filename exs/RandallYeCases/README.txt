This directory contains several case studies, and for each subdirectory it is a case study.

# Overview
There are several folders in this directory.

|--Common                               [Common to each case]
|--ESEL                                 [ESEL case]
|--ReactiveBuffer                       [Distributed reactive buffer case]
|--SteamBoiler                          [Steam boiler control system case]

Each case has very similar directory/file tree shown below. 

The Circus program can be parsed and typechecked by CZT (http://sourceforge.net/projects/czt/files/czt-ide/). The latest stable release is czt_1_5_0_bin.jar.

The CSP || Z program is model-checked by the modified ProB version under "Tools/ProB" of this repository.

## Common

|--Common
| |--csp_libs                           [Z notation related expressions and operators implementations in CSP]
| | |--lib_basic.csp                    [Some basic definitions]
| | |--lib_card.csp                     [Cardinality of set and sequence]
| | |--lib_fun.csp                      [Function related]
| | |--lib_log.csp                      [Logic related]
| | |--lib_num.csp                      [Number related]
| | |--lib_rel.csp                      [Relation related]
| | |--lib_seq.csp                      [Sequence related]
| | |--lib_set.csp                      [Set related]

## Reactive Buffer

|-- ReactiveBuffer
| |--Implementation                     [the implementation or refinement of the specification]
| | |--Circus                           [the Circus program of the implementation]
| | | |--DisBuffer.tex
| | |--CSP_Z                            [the linked CSP || Z program corresponding to the Circus program above]
| | | |--ReactiveBuffer-s1.csp
| | | |--ReactiveBuffer-s1.tex
| |--Specification                      [the specification]
| | |--Circus                           [the Circus program of the specification]
| | | |--buffer_spec.tex
| | |--CSP_Z                            [the linked CSP || Z program corresponding to the Circus specification]
| | | |--BufferSpec2-s1.csp
| | | |--BufferSpec2-s1.tex

## ESEL

|--ESEL
| |--Common                             [Common definitions, specifications etc]
| | |--ESELHeader.tex                   [Common definitions for three \Circus\ models]
| |--ESEL Specification                 [ESELSpec]
| | |--Circus                           [Circus model]
| | | |--ESELSpec.pdf
| | | |--ESELSpec.tex
| | |--CSP_Z                            [Translated CSP || Z program]
| | | |--ESEL_3-PID_2-INT0_1            [Specification constants where MAX_ESEL=2, MAX_PID=3, MAX_INT=1]
| | | | |--ESELSpec_csp.csp
| | | | |--ESELSpec_z.tex
| |--ESEL System 1                      [ESELSystem1]
| | |--Circus
| | | |--ESELSystem1.pdf
| | | |--ESELSystem1.tex
| | |--CSP_Z
| | | |--ESEL_3-PID_2-INT0_1
| | | | |--ESELSystem1_csp.csp
| | | | |--ESELSystem1_z.tex
| |--ESEL System 2                      [ESELSystem2]
| | |--Circus
| | | |--ESELSystem2.pdf
| | | |--ESELSystem2.tex
| | |--CSP_Z
| | | |--ESEL_3-PID_2-GW_2-INT0_1
| | | | |--ESELSystem2_csp.csp
| | | | |--ESELSystem2_z.tex
| |--Property Checkers                  [Some additional test processes for property checking]
| | |--AllDisplayChecker                [P1: check if all ESELs engaged in display events]
| | | |--ESELAllDisplayChecker.tex      [AllDisplayChecker]
| | | |--ESELSpecAllDisplayChecker.tex  
| | | |--ESELSystem1AllDisplayChecker.tex
| | | |--ESELSystem2AllDisplayChecker.tex
| | |--InitChecker                      [P2: initialisation checker]
| | | |--ESELInitChecker.tex
| | | |--ESELSpecInitChecker.tex
| | | |--ESELSystem1InitChecker.tex
| | | |--ESELSystem2InitChecker.tex
| | |--PriceChecker                     [P3: check if right price is shown on right display or error report]
| | | |--ESELPriceChecker.tex
| | | |--ESELSpecChecker.pdf
| | | |--ESELSpecChecker.tex
| | | |--ESELSystem1Checker.pdf
| | | |--ESELSystem1Checker.tex
| | | |--ESELSystem2Checker.pdf
| | | |--ESELSystem2Checker.tex

## Steam Boilder
|--SteamBoiler
| |--Circus                             [Circus model]
| | |--steam_boiler.pdf
| | |--steam_boiler.tex
| |--CSP_Z                              [Specification constants]
| | |--C_70
| | | |--SteamBoiler_csp.csp
| | | |--SteamBoiler_z.tex
| |--Reports                            [Some references]
| | |--steam-boiler-original.pdf
| | |--steam-boiler-singleenv.pdf
