% This file is part of the ABALearn project.
% Copyright (C) 2023, 2024  The ABALearn's Authors

% This program is free software: you can redistribute it and/or modify
% it under the terms of the GNU General Public License as published by
% the Free Software Foundation, either version 3 of the License, or
% (at your option) any later version.

% This program is distributed in the hope that it will be useful,
% but WITHOUT ANY WARRANTY; without even the implied warranty of
% MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
% GNU General Public License for more details.

:- dynamic current_new_pred/1.
current_new_pred(0).

:- consult(folding).

:- use_module(library(dialect/hprolog),[ memberchk_eq/2 ]).

% Gen procedure
genT(R2,Ep,En, Ro) :-
  gen1(R2,Ep,En, Ro).
genT(R2,Ep,En, Ro) :-
  lopt(folding_mode(nd)),
  retract(tokens(T)), % max number of folding
  T1 is T+1,
  lopt(folding_steps(M)),
  ( T1 > M -> fail ; true ),
  nl, write('* Increasing folding tokens to: '), write(T1), nl, 
  assert(tokens(T1)),
  genT(R2,Ep,En, Ro).

% gen 1
gen1(Ri,Ep,En, Rf) :-
  write('gen1: folding selection'), nl,
  select_foldable(Ri,Ep,En, S,Ri1), % Ri1 = Ri\S
  !,
  write(' to fold: '), show_rule(S), nl,
  write(' begin folding'), nl, 
  folding(Ri1,S, F),  % F = fold-all(S)
  write(' folding result: '), show_rule(F), nl,
  gen2(Ri1,Ep,En,F, Rf).
gen1(Ri,_Ep,_En, Ro) :-
  write('gen1: nothing to fold.'), nl,
  % remove last subsumed rule (due to failure of select_foldable, the latest rule still occurs in Ri)
  aba_ni_rules_replace(Ri,[], Ro).
% gen2
gen2(Ri,Ep,En,F, Rf) :-
  aba_i_rules_append(Ri,[F], Ri1),
  entails(Ri1,Ep,En),
  write('gen2: extended ABA entails <E+,E-> - using folding'), nl,
  !,
  gen1(Ri1,Ep,En, Rf). % back to gen
% gen2 - RELTO assumption found
gen2(Ri,Ep,En,F, Rf) :-
  lopt(asm_intro(relto)),
  write('gen2: extended ABA does not entail <E+,E-> - looking for assumption relative to'), nl,
  exists_assumption_relto(Ri,F, FwA),
  !,
  gen3(Ri,Ep,En,F,FwA, Rf).
% gen2 - RELTO NEW assumption or SECHK assumption chk
gen2(Ri,Ep,En,F, Rf) :-
  new_assumption(Ri,Ep,En,F, Ra,Rg,A,FwAP),
  write('gen2: generating NEW assumption: '), show_term(A), nl,
  write(' assumption introduction result: '), show_rule(FwAP), nl,
  compute_conseq(Rg, Cs),
  ( Cs \==[] -> 
    member(RgAS, Cs)
    ; 
    ( write('gen2: extended ABA w/new assumption has no extensions!'), nl, fail ) 
  ), 
  gen4(Ri,Ep,En,F,Ra,A,RgAS, Rf).
% gen3 - OLD assumption found
gen3(Ri,Ep,En,_F,FwA, Rf) :-
  aba_i_rules_append(Ri,[FwA], Ri1),
  entails(Ri1,Ep,En), % if Ri1 w/mg_alpha entails E+,E-,
  !,
  write('OK, assumption introduction result: '), show_rule(FwA), nl,
  gen1(Ri1,Ep,En, Rf). % back to gen
gen3(_Ri,_Ep,_En,F,_APF, _Rf) :-
  F = rule(_,_,B),
  write('KO, cannot introduce an assumption for '), show_term(B), nl,
  fail.
% gen4 - RELTO NEW assumption
gen4(_Ri,Ep,En,_F,Ra,A,RgAS, Rf) :-
  lopt(asm_intro(relto)),
  !,
  write('gen4: relto using current consequences ...'), nl,
  % Ri is replaced by Ra (ABA rules with the new assumption)
  gen6(Ra,Ep,En,A,RgAS, Rf). % go to role
% gen4 - SECHK assumption chk
gen4(Ri,Ep,En,F,Ra,A,RgAS, Rf) :-
  lopt(asm_intro(sechk)),
  write('gen4: sechk using current consequences ...'), nl,
  gen5(Ri,Ep,En,F,Ra,A,RgAS, Rf).
% gen5 - SECHK assumption found 
gen5(Ri,Ep,En,F,_Ra,A,RgAS, Rf) :-
  write('gen5: extended ABA does not entail <E+,E-> - looking for assumption in the stable extension'), nl,
  functor(A,AF,N),
  A =.. [AF|V],
  exists_assumption_sechk(AF/N,Ri,RgAS, APF/N),
  !,
  F = rule(_,H1,B1),
  A1 =.. [APF|V],
  new_rule(H1,[A1|B1], FwA),
  gen3(Ri,Ep,En,F,FwA, Rf).
% gen5 - SECHK NEW assumption
gen5(_Ri,Ep,En,_F,Ra,A,RgAS, Rf) :-
  % Ri is replaced by Ra (ABA rules with the new assumption)
  gen6(Ra,Ep,En,A,RgAS, Rf). % go to rote-learning
% gen6 - rote learning 
gen6(Ra,Ep,En,A,RgAS, Rf) :-
  write('gen6: rote learning of new contrary'), nl,
  functor(A,AF,N),
  atom_concat('c_',AF,C_A), 
  % rote learning
  findall(R, ( functor(C,C_A,N),member(C,RgAS), e_rote_learn(C,R) ), Rs),
  aba_ni_rules_append(Ra,Rs,Ra1),
  ( lopt(learning_mode(cautious)) -> 
    ( write(' checking entailment ... '), 
      ( entails(Ra1,Ep,En) -> ( write('OK') , nl) ; ( write('KO'), nl , fail ) )
    ) ; true  
  ),
  ( lopt(folding_selection(mgr)) -> init_mgr(Ra1,Rs,Ra2) ; Ra1=Ra2 ),
  gen1(Ra2,Ep,En, Rf). % back to gen

%
new_assumption(Ri,Ep,En,F, Ra,Rg,A,FwA) :-
  % assumption introduction
  F = rule(_,H,B),
  term_variables(B,V),
  % new assumption
  gen_new_name(Alpha),
  A =.. [Alpha|V],
  new_rule(H,[A|B], FwA),
  % create assumption(alpha).
  copy_term(A,A1),
  U1=assumption(A1),
  % create alpha :- not c_alpha, B.
  copy_term((A,B),(A2,B2)),
  A2 =.. [Alpha|V2],
  atom_concat('c_',Alpha,C_Alpha),
  C2 =.. [C_Alpha|V2],
  new_rule(A2,[not C2|B2], U2),
  % create contrary(alpha,c_alpha).
  copy_term((A2,C2),(A3,C3)),
  U3=contrary(A3,C3),
  % create Ra (Ri w/assumption)
  aba_i_rules_append(Ri,[FwA],Ri1),
  aba_asms_append(Ri1, [U1],Ri2), 
  aba_cnts_append(Ri2, [U3],Ri3),  
  utl_rules_append(Ri3,[U2],Ra),
  copy_term((C2,B2),(C3,B3)),
  % create Rg (Ra w/generator of c_alpha)
  asp_plus(Ra,Ep,En,[(C3,B3)], Rg).

% gen_new_name(-NewName)
% NewName is a fresh new predicate name of the form alpha_N (N is an integer)
gen_new_name(NewName) :-
  retract(current_new_pred(N)),
  M is N + 1,
  assert(current_new_pred(M)),
  number_codes(M,C),
  atom_codes(A,C),
  atom_concat('alpha_',A,NewName).

% select_foldable: any
select_foldable(Ri,Ep,En, S,Ro) :-
  lopt(folding_selection(any)),
  % select any nonintensional rule
  aba_ni_rules_select(X,Ri,Ri1),
  !,
  select_foldable_aux(X,Ri1,Ep,En, S,Ro).
% select_foldable: mgr
select_foldable(Ri,_Ep,_En, S,Ro) :-
  lopt(folding_selection(mgr)),
  % select any more general nonintensional rule
  select_mgr_to_fold(S,Ri,Ro).
% select_foldable auxiliary predicate
select_foldable_aux(X,Ri,Ep,En, S,Ro) :-
  write(' evaluating subsumption of '), show_rule(X), nl,
  subsumed(Ri,Ep,En, X),
  !,
  write(' * subsumed: deleted!'), nl, 
  select_foldable(Ri,Ep,En, S,Ro).
select_foldable_aux(S,Ri,_,_, S,Ri) :-
  write(' not subsumed: carry on ...'), nl.

%
init_mgr(R,L, R1) :-
  write('gen: computing greedy foldings'), nl,
  ( L=[] -> R=R1
  ;
    ( % add generalisations of new facts to the utility rules
      generate_generalisations(L,R, G),
      utl_rules_append(R,G,R1)
    )
  ).
%
generate_generalisations([],_, []).
generate_generalisations([S|Ss],R, [G|Gs]) :- 
  copy_term(S,rule(I,H,Ts)),
  aba_i_rules(R,NI),
  fold_greedy(NI,H,[],Ts, Fs),
  !,
  findall(P1/N1,(member(A1,Fs),functor(A1,P1,N1)),L1),
  functor(H,P,N),
  new_rule(H,Fs,F),
  length(L1,L),
  G=gf([id(I),P/N,Ts,L|L1],F),
  write(' greedy folding: '), 
  copy_term(G,G1), numbervars(G1,0,_), write(G1), nl,
  generate_generalisations(Ss,R, Gs).

%
mgr(G1,G2) :-
  copy_term(G1,rule(_,H1,B1)),
  copy_term(G2,rule(_,H2,B2)),
  subsumes_chk_conj([H1|B1],[H2|B2]).

%
select_mgr_to_fold(X,Ri,Ro) :-
  aba_ni_rules_member(Z,Ri),
  Z = rule(K,_,_), ID=id(K),
  % select any gf
  utl_rules_select(gf([ID,P/N|T],G),Ri,Ri1),
  % J is the id of any rule more general than rule with id I
  select_all_gf(P/N,Ri1, L,Ri2),
  select_mgr_to_fold_aux(gf([ID,P/N|T],G),L,Ri2,[], J,Ri3,GFs),
  % select rule with identifier J
  X = rule(J,_,_), 
  utl_rules_append(Ri3,GFs,Ri4),
  aba_ni_rules_select(X,Ri4,Ro).
%
select_all_gf(P/N,Ri1, [gf([ID2,P/N|P2],G2)|L],Ri3) :-
  utl_rules_select(gf([ID2,P/N|P2],G2),Ri1,Ri2),
  !,
  select_all_gf(P/N,Ri2, L,Ri3).
select_all_gf(_,Ri, [],Ri).
% select_mgr_to_fold_aux/7
select_mgr_to_fold_aux(G,[],Ri,CMGR, ID,Ro,GFs) :-
  select_mgr_to_fold_aux(G,Ri,CMGR, ID,Ro,GFs).
select_mgr_to_fold_aux(gf([ID1,P/N,_Tbf1,L1|_P1],G1),[gf([ID2,P/N,Tbf2,L2|P2],G2)|Gs],Ri1,CMGR, ID,Ro,GFs) :-
  L2=<L1,
  mgr(G2,G1),
  !,
  write(' * ['), write(ID2), write('] '), show_rule(G2), nl, 
  write(' *   is more general than'), nl, 
  write(' * ['), write(ID1), write('] '), show_rule(G1), nl,
  ID1=id(I), X = rule(I,_,_),  
  % select rule with identifier I
  aba_ni_rules_select(X,Ri1,Ri2),
  write(' * > '), write(I), write(' < deleted!'), nl,
  select_mgr_to_fold_aux(gf([ID2,P/N,Tbf2,L2|P2],G2),Gs,Ri2,CMGR, ID,Ro,GFs).
select_mgr_to_fold_aux(gf([ID1,P/N,Tbf1,L1|P1],G1),[gf([ID2,P/N,_Tbf2,L2|_P2],G2)|Gs],Ri1,CMGR, ID,Ro,GFs) :-
  L1=<L2,
  mgr(G1,G2),
  !,
  write(' * ['), write(ID1), write('] '), show_rule(G1), nl, 
  write(' *   is more general than'), nl, 
  write(' * ['), write(ID2), write('] '), show_rule(G2), nl,
  ID2=id(I), X = rule(I,_,_),  
  % select rule with identifier I
  aba_ni_rules_select(X,Ri1,Ri2),
  write(' * > '), write(I), write(' < deleted!'), nl,
  select_mgr_to_fold_aux(gf([ID1,P/N,Tbf1,L1|P1],G1),Gs,Ri2,CMGR, ID,Ro,GFs).
select_mgr_to_fold_aux(Gf1,[Gf2|Gs],Ri,CMGR, ID,Ro,GFs) :-
  select_mgr_to_fold_aux(Gf1,Gs,Ri,[Gf2|CMGR], ID,Ro,GFs).  
% select_mgr_to_fold_aux/6
select_mgr_to_fold_aux(gf([id(ID)|_],_),R,[], ID,R,[]).
select_mgr_to_fold_aux(gf([ID1,P/N,Tbf1,L1|P1],G1),Ri1,[gf([ID2,P/N,_Tbf2,L2|_P2],G2)|Gs], ID,Ro,GFs) :-
  L1=<L2,
  mgr(G1,G2),
  !,
  write(' * ['), write(ID1), write('] '), show_rule(G1), nl, 
  write(' *   is more general than (2)'), nl, 
  write(' * ['), write(ID2), write('] '), show_rule(G2), nl,
  ID2=id(I), X = rule(I,_,_),  
  % select rule with identifier I
  aba_ni_rules_select(X,Ri1,Ri2),
  write(' * > '), write(I), write(' < deleted!'), nl,
  select_mgr_to_fold_aux(gf([ID1,P/N,Tbf1,L1|P1],G1),Ri2,Gs, ID,Ro,GFs).
select_mgr_to_fold_aux(gf([ID1,P/N,Tbf1,L1|P1],G1),Ri,[G2|Gs], ID,Ro,[G2|GFs]) :-
  select_mgr_to_fold_aux(gf([ID1,P/N,Tbf1,L1|P1],G1),Ri,Gs, ID,Ro,GFs).  
% subsumption(+Ri,+Ep,+En, -Ro)
% Ro is the result obained by removing all subsumed nonintensional rules from Ri
subsumption(Ri,Ep,En, Ro) :-
  aba_ni_rules(Ri,NiR), length(NiR,N),  write(' evaluating subsumption of '), write(N), write(' rules'), nl,
  aba_ni_rules_select(R,Ri,Ri1),
  write(' evaluating subsumption of '), show_rule(R), nl, 
  subsumed(Ri1,Ep,En, R),
  !,
  write(' subsumed: deleted.'), nl, 
  subsumption(Ri1,Ep,En, Ro).
subsumption(Ri,_,_, Ri).

% nonintensional(+R)
% R is nonintensional if in the body of R there is an equality of the form X=C, 
% where X is a variable and C is a constant.
nonintensional(R) :-
  R = rule(J,_,B),
  rlid(I),
  J>=I,
  member((V=C),B),
  var(V),
  ground(C),
  !.   

% looking for a more general alpha 
exists_assumption_sechk(AlphaF/N,R,A, AlphaPF/N) :-
  aba_asms_member(assumption(Alpha),R),
  functor(Alpha,AlphaPF,N),
  AlphaPF \== AlphaF,
  mg_alpha(AlphaPF/N,AlphaF/N,A).
% exists_assumption_sechk utility predicate
mg_alpha(AlphaPF/N,AlphaF/N,A) :-
  functor(Alpha,AlphaF,N),
  select(Alpha,A,A1),
  !,
  Alpha =.. [_|Args], 
  AlphaP =.. [AlphaPF|Args],
  select(AlphaP,A1,A2),
  mg_alpha(AlphaPF/N,AlphaF/N,A2).
mg_alpha(_,_,_).

% looking for an existing alpha for F
exists_assumption_relto(R,F, FwA) :-
  % rule to be folded
  F = rule(_,H1,B1),
  % take any rule in R w/N1+1 atoms
  length(B1,N1), N2 is N1+1, length(B2,N2),
  aba_i_rules_member(rule(_,_,B2),R),
  % take any assumption in R
  aba_asms_member(assumption(A1),R),
  % check if (a variant of A1) occurs in the body B2 
  select(A2,B2,R2), variant(A1,A2),
  % check if B1 is a variant of R2 (B2 w/o assumption)
  permutation_variant(R2,B1, P2),
  functor(A1,P,N),
  write(' found: '), write(P/N), write(' ... '),
  copy_term([A2|P2],[A3|P3]),
  P3 = B1,
  new_rule(H1,[A3|B1], FwA).

% MODE: permutation_functor(+T1,+T2, -T3)
% SEMANTICS: T3 is a permutation of T1 sorted by functors occurring in T2.
permutation_functor([],[],[]).
permutation_functor(As,[B|Bs], [A|P1]) :-
  functor(B,P,N), functor(A,P,N),
  select(A,As,As1),
  permutation_functor(As1,Bs, P1).


% MODE: permutation_variant(+L1,+L2, -L3)
% SEMANTICS: L3 is a permutation of L1 which is a variant of L2
% length 1
permutation_variant(L1,L2, L1) :-
  L1 = [_], L2 = [_],
  !,
  L1 =@= L2.
% length 2
permutation_variant(L1,L2, L1) :-
  L1 = [_,_],
  L2 = [_,_],
  L1 =@= L2.
permutation_variant(L1,L2, P1) :-
  L1 = [X,Y],
  P1 = [Y,X],
  !,
  P1 =@= L2.
% length >= 3
permutation_variant(L1,L2, P1) :-
  L1 = [_,_,_|T1],
  L2 = [_,_,_|T2],
  !,
  length(T1,N), length(T2,N),
  permutation_functor(L1,L2, P1), % P1 is a permutation of L1
  P1 =@= L2.                      % P1 is a variant of L2

% MODE: subsumes_chk_conj(+T1,+T2)
% TYPE: subsumes_chk_conj(list(term),list(term))
% SEMANTICS: list T1 subsumes list T2, that is, there exists a sublist T3
% consisting of elements in T2 which is subsumed by T1.
subsumes_chk_conj(Gs,Ss) :-
  subsumes_chk_conj(Gs,Ss,[],[]).
%
subsumes_chk_conj([],_,_,_).
subsumes_chk_conj([G|Gs],L,GAcc,SAcc) :-
  member(S,L),
  subsumes_chk([G|GAcc],[S|SAcc]),
  subsumes_chk_conj(Gs,L,[G|GAcc],[S|SAcc]).


% MODE: select_subsumed(+T1,+L1, -T2,-L2)
% TYPE: select_subsumed(term,list(term),term,list(term))
% SEMANTICS: T2 is an element in L1 s.t. T1 subsumes T2, L2 is L1\T2.
select_subsumed(G,[S|T],S,T) :-
  subsumes_chk(G,S).
select_subsumed(G,[H|T],S,[H|T1]) :-
  select_subsumed(G,T,S,T1).