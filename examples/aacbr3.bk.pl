% AA-CBR example 2

% BK

f1(a).
f2(a).
f1(b).
f2(b).
f3(b).
f1(c).
f2(c).
f3(c).
f4(c).


%cn(a) pos example
%cn(b),cn(c) neg example

cn(X) :- domain(X), alpha(X). 

domain(a).
domain(b).
domain(c).

assumption(alpha(X)) :- domain(X).
contrary(alpha(X),c_alpha(X)) :- assumption(alpha(X)).

% aba_asp('./examples/aacbr3.bk.pl',[cn(a)],[cn(b)]).