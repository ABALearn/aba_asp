% Flies example from DK-95

bird(A) :- A=woodstock.
bird(A) :- A=gwaihir.
penguin(A) :- A=pingu.
penguin(A) :- A=pinga.
superpenguin(A) :- A=x_pingu.
superpenguin(A) :- A=x_pinga.
bird(A) :- penguin(A).
penguin(A) :- superpenguin(A).

#modeh(flies(var(t1))).
#modeb(flies(var(t1))).
#modeb(bird(var(t1))).
#modeb(penguin(var(t1))).
#modeb(superpenguin(var(t1))).

#constant(t1, woodstock).
#constant(t1, gwaihir).
#constant(t1, pingu).
#constant(t1, pinga).
#constant(t1, x_pingu).
#constant(t1, x_pinga).

%E=#pos(E+,E-).
#pos({flies(woodstock),flies(gwaihir),flies(x_pingu),flies(x_pinga)},
     {flies(pingu),flies(pinga)}).

%emanuele@Emanueles-Air ILASP-4.4.0-macOS-M1 % ./ILASP --version=2 ecai/flies_birds.bk.las
%flies(V1) :- superpenguin(V1).
%flies(V1) :- bird(V1); not penguin(V1).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Pre-processing                          : 0.035s
%% Hypothesis Space Generation             : 0.044s
%% Counterexample search                   : 0s
%%   - CDOEs                               : 0s
%%   - CDPIs                               : 0s
%% Hypothesis Search                       : 0.012s
%% Total                                   : 0.093s
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%