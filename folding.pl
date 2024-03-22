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
  select_rule(Rs,T,R1),    % R1 is a (copy of a) clause in Rs that can be used for folding T
  R1 = rule(I,F,[T|As]),   % select_rule sorts the elements in the body so that its head matches T   
  write(' '), write(C), write(': folding '), show_term([T|Ts]), write(' with '), write(I), write(': '), show_rule(R1), nl,
  %apply_folding(As,[T|Ts], ResTs,NewTs),
  %match(As,[],Ts, ResTs,NewTs),  % NewTs consists of equalities in As that do not match with any element in As@Ts  
  match2(As,Ts, _,NewTs,ResTs), % NewTs consists of equalities in As that do not match with any element in As@Ts  
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
% Fs: Folded
% Ts: To be folded
% Zs: result
fold_greedy(Rs,H,FsI,Tbf, FsO) :-
  select(T,Tbf,RTbf),
  select_rule(Rs,T, R1), R1 = rule(I,H1,[T|As]), 
  match2(As,RTbf, M,NewTbf,ResTbf),
  % H1 does not occur in the accumulator of foldings performed so far
  \+ memberchk_eq(H1,FsI),
  % check if new elements to be folded bind variables occurring elsewhere
  term_variables(M,V1), term_variables(NewTbf,V2), intersection_empty(V1,V2),
  write(' folding '), show_term(Tbf), write(' with '), write(I), write(': '), show_rule(R1), nl,
  % add new equalities to Tbf
  append(Tbf,[H1|NewTbf],Tbf1),
  fold_greedy(Rs,H,[H1|FsI],Tbf1, FsO).
fold_greedy(_,_,Fs,_, Fs) :-
  Fs = [_|_], % something has been folded
  write(' '), write('DONE'), nl.

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
  R = rule(_,H,[T|Bs]),   % select_rule sorts the elements in the body so that its head matches T   
  % TODO: add check on ResTs 
  match(Bs,As,Ts, _ResTs,Ns),  % Ns consists of equalities in Bs that do not match with any element in As@Ts
  \+ memberchk_eq(H,FsI), % H does not belong to the list of elements obtained by folding
  append(Ts,Ns, Ts1),     % New elements to be folded Ts@Ns
  fold(Rs,[T|As],Ts1,[H|FsI], FsO).
fold(Rs,As,[_|Ts],FsI, FsO) :- 
  fold(Rs,As,Ts,FsI, FsO).
fold(_,[_|_],[],Fs, Fs).  % [] nothing left to be folded, [_|_] something has been folded
                          % Note fold is called with As=[]

% R is a rule in Rs that can be used to fold T
select_rule(Rs,T,R) :-
  % take any rule in Rs
  member(rule(I,H,Bs),Rs),
  % select any term B in the body of Bs
  select(B,Bs,Bs1),
  % check if B is more general than T
  subsumes_term(B,T),
  % make a copy of the rule
  copy_term((H,B,Bs1),(CpyH,CpyB,CpyBs)),
  % create the new rule, where the head of the body is (the copy of) the matching element
  R = rule(I,CpyH,[CpyB|CpyBs]).

% match(As,Bs, Ms,ARs,BRs) holds iff Ms consists of elements in As that 
% have been unified with a (possibly) more specific element in Bs.
% ARs and BRs consists of elements in As and Bs, respectively, not in Ms
match2([],Bs, [],[],Bs).
match2([A|As],Bs, [A|Ms],ARs,BRs) :- 
  match(A,Bs, Bs1),
  match2(As,Bs1, Ms,ARs,BRs).
match2([A|As1],Bs, Ms,[A|ARs],BRs) :-
  functor(A,=,2), 
  \+ match(A,Bs),
  match2(As1,Bs, Ms,ARs,BRs).

% match(A,Bs, Rs) holds iff there exists an element B in Bs s.t. 
% A subsumes B and R is Bs without B.
match(A,[B|Bs], Bs) :-
  subsumes_term(A,B),
  A = B.
match(A,[B|Bs], [B|RBs]) :-
  match(A,Bs, RBs).

% match(A,Bs) holds iff there exists an element B in Bs s.t. A subsumes B
match(A,Bs) :-
  match(A,Bs, _),
  !.
