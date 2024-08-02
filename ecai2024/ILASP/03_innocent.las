% BK
innocent(X) :- defendant(X), not_guilty(X).

liar(alex).

witness_con(mary,alex).
witness_con(david,carol).
witness_con(john,carol).

away(bob).

defendant(mary).
defendant(david).
defendant(john).

person(alex).
person(bob).
person(carol).
person(mary).
person(david).
person(john).

#modeh(innocent(var(t1))).

#modeb(innocent(var(t1))).
#modeb(defendant(var(t1))).
#modeb(not_guilty(var(t1))).
#modeb(liar(var(t1))).
#modeb(witness_con(var(t1),var(t1))).
#modeb(away(var(t1))).
#modeb(person(var(t1))).

#constant(t1, alex).
#constant(t1, bob).
#constant(t1, carol).
#constant(t1, mary).
#constant(t1, david).
#constant(t1, john).

%E=#pos(E+,E-).
#pos({innocent(mary),innocent(bob)},
     {innocent(david),innocent(john)}).

%emanuele@Emanueles-Air ILASP-4.4.0-macOS-M1 % ./ILASP --version=2 ecai/innocent.bk.las          
%innocent(V1) :- away(V1).
%innocent(V1) :- liar(V2); witness_con(V1,V2).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Pre-processing                          : 0.031s
%% Hypothesis Space Generation             : 1.199s
%% Counterexample search                   : 0.001s
%%   - CDOEs                               : 0s
%%   - CDPIs                               : 0.001s
%% Hypothesis Search                       : 0.595s
%% Total                                   : 1.839s
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
