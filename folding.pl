:- use_module(library(dialect/hprolog),[ memberchk_eq/2 ]).
:- use_module('asp_utils').

:- dynamic tokens/1.
tokens(1).

% folding(+Ri,+R, -F)
% Rs: rules for folding, and
% F is the result of applying folding to R
% nd (w/tokens)
folding(Ri,R, F) :-
  lopt(folding_mode(nd)),
  aba_rules(Ri,Rs), % AR = ABA Rules
  copy_term(R,rule(_,H,Ts)),
  folding(Rs,H,Ts, Fs),
  new_rule(H,Fs,F).
% greedy
folding(Ri,R, F) :-
  lopt(folding_mode(greedy)),
  lopt(folding_selection(mgr)),
  utl_rules(Ri,U),
  R = rule(I,_,_),
  % member(gen(G,[id(I)|_]),U),
  ( member(gen(G,[id(I)|_]),U) -> true ; member(fp(G,[id(I)|_]),U) ),
  copy_term(G,F).
folding(Ri,R, F) :-
  lopt(folding_mode(greedy)),
  lopt(folding_selection(any)),
  aba_rules(Ri,Rs), % AR = ABA Rules
  copy_term(R,rule(_,H,Ts)),
  fold_greedy(Rs,H,[],Ts, Fs),
  !,
  new_rule(H,Fs,F).   
% all
folding(Ri,R, F) :-
  lopt(folding_mode(all)),
  aba_rules(Ri,Rs),
  copy_term(R,rule(_,H,Ts)),
  fold(Rs,[],Ts,[], Fs),
  new_rule(H,Fs,F).

% folding(+Rs,+H,+Ts, -Fs)
% Rs: rules for folding
% H: head of the clause to be folded
% Ts: To be folded
% Fs: result
% non-deterministic
:- discontiguous folding/4.
folding(Rs,H,Ts, Fs) :-
  tokens(T),
  fold_all(T,Rs,H,[],Ts, Zs),
  folding_aux(Rs,H,Zs, Fs).
% fold_all auxiliary predicate
folding_aux(_,_,Fs, Fs).
folding_aux(Rs,H,[T|Ts], Fs) :-
  folding(Rs,H,[T|Ts], Fs).
folding_aux(Rs,H,Ts, Fs1) :-
  nselect(P,Ts, E,R),
  folding(Rs,H,R, Fs),
  combine(P,E,Fs, Fs1). 

% nselect(+P,+Ts, -E,-R)
% Ts is a list consisting of at least two elements,
% E is the element of Ts at position P, and
% R is Ts without E 
nselect(I,[H1,H2|T], E,R) :-
  nth1(I,[H1,H2|T], E,R).

% combine(+P,+E,+Fs, -Fs1)
% Fs1 is the result of adding E into Fs at position P
combine(P,E,F,C) :-
  combine_aux(1,P,E,F,[], C).
% combine auxiliary predicate
combine_aux(I,P,E,F,CI, CO) :-
  I==P,
  !,
  append(CI,[E|F],CO).
combine_aux(I,P,E,[H|T],CI, CO) :-
  I < P,
  J is I+1,
  append(CI,[H],CI1),
  combine_aux(J,P,E,T,CI1, CO).

% fold_all(+C,+Rs,+H,+Fs,+Ts, -Zs)
% C: tokens left for folding
% Rs: rules for folding
% H: head of the clause to be folded
% Fs: already Folded
% Ts: To be folded
% Zs: result
fold_all(C,_,_,Fs,[], Fs) :-
  C>=0,
  write(' '), write(C), write(': DONE'), nl.
fold_all(C,Rs,H,FsI,[T|Ts], FsO) :-
  C>=1,
  member(R,Rs), copy_term(R,R1), R1 = rule(I,F,As), memberchk(T,As),
  write(' '), write(C), write(': folding '), show_term([T|Ts]), write(' with '), write(I), write(': '), show_rule(R1), nl,
  apply_folding(As,[T|Ts], ResTs,NewTs),
  % check if new elements to be folded bind variables occurring elsewhere
  term_variables((H,FsI,ResTs),V1),
  term_variables(NewTs,V2),
  intersection_empty(V1,V2),
  append(ResTs,NewTs, Ts1),
  C1 is C-1,
  fold_all(C1,Rs,H,[F|FsI],Ts1, FsO).
fold_all(C,_,_,_,[T|Ts], _) :-
  C==0,
  write(' '), write(C), write(': FAIL - No more folding tokens left for '), show_term([T|Ts]), nl, fail.

% fold_greedy(+Rs,+H,+Fs,+Ts, -Zs)
% Rs: rules for folding
% H: head of the clause to be folded
% Fs: already Folded
% Ts: To be folded
% Zs: result
fold_greedy(Rs,H,FsI,Tbf, FsO) :-
  member(T,Tbf),
  member(R,Rs), 
  copy_term(R,R1), R1 = rule(I,H1,As), 
  memberchk(T,As),    % I can be used for folding an element in Tbf
  % get elements that cannot be folded using R1 (ResTbf) and
  % those elements occurring in R1 and not occurring in Tbf (NewTbf)
  apply_folding(As,Tbf, ResTbf,NewTbf),
  % 
  \+ memberchk_eq(H1,FsI),
  % check if new elements to be folded bind variables occurring elsewhere
  term_variables((H,FsI,ResTbf),V1),
  term_variables(NewTbf,V2),
  intersection_empty(V1,V2),
  write(' folding '), show_term(Tbf), write(' with '), write(I), write(': '), show_rule(R1), nl,
  % add new equalities to Tbf
  append(Tbf,[H1|NewTbf],Tbf1),
  fold_greedy(Rs,H,[H1|FsI],Tbf1, FsO).
fold_greedy(_,_,Fs,_, Fs) :-
  Fs = [_|_], % something has been folded
  write(' '), write('DONE'), nl.

% apply_folding(+Ls,+Ts, -ResTs,-NewTs)
% Ls: elements for folding
% Ts: elements to be folded
% ResTs consists of the elements in Ts not folded by R, and
% NewTs are newly introduced equalities (equalities in Ls)
% apply_folding([],Ts, Ts,[]).
% apply_folding([E|B],TsI, TsO,NewTs) :-
%   selectchk(E,TsI,TsI1),
%   !,
%   apply_folding(B,TsI1, TsO,NewTs).
% apply_folding([E|B],TsI, TsO,[E|NewTs]) :-
%   eq(E),
%   apply_folding(B,TsI, TsO,NewTs).
apply_folding([],Ts, Ts,[]).
apply_folding([E|B],TsI, TsO,NewTs) :-
  select(E,TsI,TsI1),
  apply_folding(B,TsI1, TsO,NewTs).
apply_folding([E|B],TsI, TsO,[E|NewTs]) :-
  eq(E),
  \+ member(E,TsI),
  apply_folding(B,TsI, TsO,NewTs).

% TODO: code for replacing the first member in fold_greedy
% % tbf(+T,+Ts)
% % T is an element of Ts to be folded
% tbf(T,[V1=V2|Ts]) :-
%   var(V1),
%   var(V2),
%   !,
%   tbf(T,Ts).
% tbf(T,[T|_]).
% tbf(T,[_|Ts]) :-
%   tbf(T,Ts).

% eq(E) holds iff E is a term of the form  V=C,
% where V is a variable and C is a ground term
eq(V=C) :-
  var(V), ground(C).

% intersection_empty(L1,L2) holds iff
% the intersection of L1 and L2 is empty
intersection_empty(L1,L2) :- 
  intersection(L1,L2,L3),
  L3==[].

% intersection(L1,L2,I)
% I is the intersection of L1 and L2
intersection([],_,[]).
intersection([E|L],L2,[E|L3]) :-
  memberchk_eq(E,L2),
  !,
  intersection(L,L2,L3).
intersection([_|L],L2,L3) :-
  intersection(L,L2,L3).

% append_difflist
append_difflist(L1-T1, T1-T2, L1-T2).

% fold(Rs,As,Ts,FsI, FsO)
% Rs: rules for folding
% As: folded elements
% Ts: elements to be folded
% FsI: already folded
% FsO: fold result
fold(Rs,As,[T|Ts],FsI, FsO) :- 
  select_rule(Rs,T,R),    % R is a (copy of a) clause in Rs that can be used for folding T
  R = rule(_,H,[T|Bs]),   % select_rule sorts the elements in the body so that the head of Bs matches T   
  match(Bs,As,Ts, Ns),    % Ns consists of equalities in Bs that do not match with any element in As@Ts
  \+ memberchk_eq(H,FsI), % H does not belong to the list of elements obtained by folding
  append(Ts,Ns, Ts1),     % New elements to be folded Ts@Ns
  fold(Rs,[T|As],Ts1,[H|FsI], FsO).
fold(Rs,As,[_|Ts],FsI, FsO) :- 
  fold(Rs,As,Ts,FsI, FsO).
fold(_,[_|_],[],Fs, Fs).  % [] nothing left to be folded, [_|_] something has been folded
                          % Note fold is called with As=[]

%
select_rule(Rs,T,R1) :-
  member(R,Rs),
  R = rule(I,H,Bs),
  select(B,Bs,Bs1),
  variant(T,B),
  copy_term((H,B,Bs1),(CpyH,CpyB,CpyBs)),
  R1 = rule(I,CpyH,[CpyB|CpyBs]).

%
match([],_,_,[]).
match([B|Bs],As,Ts, Ls) :- 
  select(T,As,As1),
  subsumes_term(B,T), % B is more general than T
  B=T,
  match(Bs,As1,Ts, Ls).
match([B|Bs],As,Ts, Ls) :- 
  select(T,Ts,Ts1),
  subsumes_term(B,T),
  B=T,
  match(Bs,As,Ts1, Ls).
match([B|Bs],As,Ts, [B|Ls]) :-
  functor(B,=,2),
  does_not_subsume(B,As),
  does_not_subsume(B,Ts),
  match(Bs,As,Ts, Ls).

% does_not_subsume(+X,+Ls)
% there is no element Y in Ls s.t. X subsumes Y 
does_not_subsume(_,[]).
does_not_subsume(X,[Y|_]) :-
  subsumes_term(X,Y),
  !,
  fail.
does_not_subsume(X,[_|Ls]) :-
  does_not_subsume(X,Ls).