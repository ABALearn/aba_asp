Instructions to replicate the experiments reported in the paper: 
"Learning Brave Assumption-Based Argumentation Frameworks via ASP"
Emanuele De Angelis, Maurizio Proietti, and Francesca Toni
27TH EUROPEAN CONFERENCE ON ARTIFICIAL INTELLIGENCE (ECAI 2024)
Paper ID: M1488 (https://www.ecai2024.eu/)
------------------------------------------------------------------

ASP-ABALearn_B
--------------
The subfolder 'ASP-ABAlearn_B' includes the ASP-ABAlearn_B 
specifications of the Learning problems reported in Table 1
(files with extension '.bk.aba'):

01_flies_birds.bk.aba
02_flies_birds_planes.bk.aba
03_innocent.bk.aba
04_nixon_diamond.bk.aba
05_nixon_diamond_2.bk.aba
06_tax_law.bk.aba
07_tax_law_2.bk.aba
08_acute.pp.csv.bk.aba
09_autism.pp.csv.bk.aba
10_breastw.pp.csv.bk.aba

The subfolder also includes the file 'ecai2024_config.pl' with 
the settings used to run the experiments, and the Prolog goals 
to run the ASP-ABAlearn_B strategy on a given Learning problem 
(files with extension '.bk.goal').

An ASP-ABAlearn_B specification consists of the definition 
of a background knowledge (BK) with additional annotations 
to represent assumptions (assumption/1 predicate) and 
contraries (contrary/2 predicate).
Positive and negative examples are provided as arguments of 
the Prolog goals.

Let us consider the Learning problem 'innocent' of Table 1.

The ASP-ABAlearn_B specification is included in '03_innocent.bk.aba':
- lines 2-21 encode the background knowledge;
- line 24 encodes the assumption not_guilty(X);
- line 26 encodes the contrary guilty(X) of the assuption not_guilty(X). 

The Prolog goal to run ASP-ABAlearn_B is included in '03_innocent.bk.goal':

:- aba_asp('./ecai2024/ASP-ABAlearn_B/03_innocent.bk',
    [innocent(mary),innocent(bob)],
    [innocent(david),innocent(john)]).

The predicate aba_asp/3 invokes ASP-ABAlearn_B on the Learning problem
specified in './ecai2024/ASP-ABAlearn_B/03_innocent.bk'.
The second and third arguments specify the positive and negative example,
respectively.


How to run ASP-ABAlearn_B on a specific learning problem.

Prerequisites. 
Make sure you have installed the following software:
- SWI-Prolg: https://www.swi-prolog.org/
- Clingo: https://potassco.org/clingo/

1) Starting SWI-Prolog

  aba-learning/aba-asp$ swipl

2) Loading ASP-ABAlearn_B

  ?- consult('aba_asp.pl').

3) Configuring ASP-ABAlearn_B 

  ?- consult('ecai2024/ASP-ABAlearn_B/ecai2024_config.pl').

4) Running ASP-ABAlearn_B on a Learning problem (e.g., innocent)

  ?- consult('ecai2024/ASP-ABAlearn_B/03_innocent.bk.goal').

ASP-ABAlearn_B produces two output files:
- ecai2024/ASP-ABAlearn_B/03_innocent.bk.sol.aba
- ecai2024/ASP-ABAlearn_B/03_innocent.bk.sol.asp
including the ABA framework and its ASP encoding, respectively,
encoding the solution of the ABA Learning problem 'innocent'.


ILASP
-----

To run ILASP, we have added to the BK the mode declarations used by
ILASP to specify the structure of candidate ASP rules to be learnt
(their heads, by using #modeh, and their bodies, by using #modeb).
Positive and negative examples are encoded in ILASP by using the
#pos declaration.

Learning problems reported in Table 1:
01_flies_birds.las
02_flies_birds_planes.las
03_innocent.las
04_nixon_diamond.las
05_nixon_diamond_2.las
06_tax_law.las
07_tax_law_2.las
08_acute.las
09_autism.las
10_breastw.las

'acute.extended.las' is obtained from '08_acute.las' by extending the 
background knowledge with additional information matching the use of 
assumptions and their contraries automatically introduced by ASP-ABALearn_B