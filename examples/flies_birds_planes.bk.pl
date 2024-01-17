% Flies example from DK-95 + planes and cats

bird(A) :- penguin(A).
penguin(A) :- superpenguin(A).
bird(A) :- A=woodstock.
bird(A) :- A=gwaihir.
penguin(A) :- A=pingu.
penguin(A) :- A=pinga.
superpenguin(A) :- A=x_pingu.
superpenguin(A) :- A=x_pinga.
cat(X) :- X=tom.
plane(X) :- X=b777.
plane(X) :- X=a380.
plane(X) :- X=b747.
damaged(X) :- X=b747. % 13

d(A) :- bird(A).
d(A) :- plane(A).
d(A) :- cat(A).

domain(A) :- d(A).

% aba_asp('./examples/flies_birds_planes.bk.pl',[flies(woodstock),flies(gwaihir),flies(x_pingu),flies(x_pinga),flies(b777),flies(a380)],[flies(pingu),flies(pinga),flies(b747),flies(tom)]).