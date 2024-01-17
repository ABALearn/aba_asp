% AA-CBR example 2

% BK

f1(a).
f2(a).
f1(b).
f2(b).
f3(b).

%cn(a) neg example
%cn(b) pos example

cn(X) :- domain(X), alpha(X). 

domain(a).
domain(b).

assumption(alpha(X)) :- domain(X).
contrary(alpha(X),c_alpha(X)) :- assumption(alpha(X)).

% aba_asp('./examples/aacbr2.bk.pl',[cn(b)],[cn(a)]).

/* brave

1st sol:
cn(A) :- domain(A), alpha(A).
c_alpha(A) :- alpha_3(A), f1(A).
c_alpha_3(A) :- alpha_4(A), f2(A).
c_alpha_4(A) :- alpha_3(A), f1(A).


2nd sol:
cn(A) :- domain(A), alpha(A).
c_alpha(A) :- alpha_1(A), f1(A).
c_alpha_1(A) :- f3(A).


MANUAL
==>  cn(A) :- domain(A), alpha(A).

RL
c_alpha(X) :- X=a.

Fold* (apply all possible foldings before deleting equalities)
c_alpha(X) :- f1(X), f2(X).

AssI
==> c_alpha(X) :- f1(X), f2(X), alpha1(X).

RL
c_alpha1(X) :- X=b.

Fold*
==> c_alpha1(X) :- f1(X), f2(X), f3(X).

*/
