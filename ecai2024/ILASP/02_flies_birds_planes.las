% Flies example from DK-95 + planes

bird(A) :- penguin(A).
penguin(A) :- superpenguin(A).
bird(A) :- A=woodstock.
bird(A) :- A=tweety.
penguin(A) :- A=pingu.
superpenguin(A) :- A=x_pingu.
plane(X) :- X=b777.
plane(X) :- X=a380.
plane(X) :- X=b747.
under_maint(X) :- X=b747.

#modeh(flies(var(t1))).

#modeb(flies(var(t1))).
#modeb(bird(var(t1))).
#modeb(penguin(var(t1))).
#modeb(superpenguin(var(t1))).
#modeb(plane(var(t1))).
#modeb(under_maint(var(t1))).

#constant(t1, woodstock).
#constant(t1, tweety).
#constant(t1, pingu).
#constant(t1, x_pingu).
#constant(t1, b777).
#constant(t1, a380).
#constant(t1, b747).

%E=#pos(E+,E-).
#pos({flies(woodstock),flies(tweety),flies(x_pingu),flies(b777),flies(a380)},
     {flies(pingu),flies(b747)}).

%emanuele@Emanueles-Air ILASP-4.4.0-macOS-M1 % ./ILASP --version=2 ecai/flies_birds_planes.bk.las 
%flies(V1) :- superpenguin(V1).
%flies(V1) :- bird(V1); not penguin(V1).
%flies(V1) :- plane(V1); not under_maint(V1).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Pre-processing                          : 0.032s
%% Hypothesis Space Generation             : 0.146s
%% Counterexample search                   : 0.001s
%%   - CDOEs                               : 0s
%%   - CDPIs                               : 0.001s
%% Hypothesis Search                       : 0.065s
%% Total                                   : 0.246s
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%