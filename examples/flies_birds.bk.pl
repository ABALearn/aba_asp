% Flies example from DK-95

bird(A) :- A=woodstock.
bird(A) :- A=gwaihir.
penguin(A) :- A=pingu.
penguin(A) :- A=pinga.
superpenguin(A) :- A=x_pingu.
superpenguin(A) :- A=x_pinga.
bird(A) :- penguin(A).
penguin(A) :- superpenguin(A).

%domain(A) :- bird(A).

% aba_asp('./examples/flies_birds.bk.pl',[flies(woodstock),flies(gwaihir),flies(x_pingu),flies(x_pinga)],[flies(pingu),flies(pinga)]).