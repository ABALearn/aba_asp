Instructions to replicate the experiments reported in the paper: 
"Learning to Contest Argumentative Claims"
Emanuele De Angelis, Maurizio Proietti, and Francesca Toni
------------------------------------------------------------------

Learning problems reported in Table 1 and Table 2 (files with extension '.bk.*.aba'):

acute.csv.bk.*.aba
autism.csv.bk.*.aba
breastw.csv.bk.*.aba
krkp.csv.bk.*.aba
mushroom.csv.bk.*.aba
voting.csv.bk.*.aba

where * is a placeholder for 'scratch' and 'redress.p0', including the backround knowledge of the ABA framework.

For each learning problem P, P.redress.p0.aba and P.scratch.aba have the same content, but have been renamed for running the two experimental processes indipendently.

* How to run RASP-ABAlearn *

Prerequisites. 
Make sure you have installed the following software:
- SWI-Prolg: https://www.swi-prolog.org/
- Clingo: https://potassco.org/clingo/

1) Starting SWI-Prolog

  aba-learning/aba-asp$ swipl

2) Loading ASP-ABAlearn_B

  ?- consult('aba_asp.pl').

3) Running RASP-ABAlearn

- 'Redress from scratch' (S)

  ?- consult('./ruleml2025/acute.scratch.goal').  

- 'Incremental redress' (R)

  ?- consult('./ruleml2025/acute.redress.goal').  
