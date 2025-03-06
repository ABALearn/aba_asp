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
  folding(Ri1,S, F),  % F = fold-all(S)
  write(' folding result: '), show_rule(F), nl,
  gen2(Ri1,Ep,En,F, Rf).
gen1(Ri,_Ep,_En, Ro) :-
  write('gen1: nothing to fold.'), nl,
  % remove last subsumed rule (due to failure of select_foldable, the latest rule still occurs in Ri)
  aba_ni_rules_replace(Ri,[], Ro).
% gen2
gen2(Ri,Ep,En,F, Rf) :-
  aba_p_rules_append(Ri,[F], Ri1),
  entails(Ri1,Ep,En),
  write('gen2: extended ABA entails <E+,E-> - using folding'), nl,
  !,
  update_fwt([F],Ri1, Ri2),
  gen1(Ri2,Ep,En, Rf). % back to gen
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
  aba_p_rules_append(Ri,[FwA], Ri1),
  entails(Ri1,Ep,En), % if Ri1 w/mg_alpha entails E+,E-,
  !,
  write('OK, assumption introduction result: '), show_rule(FwA), nl,
  gen1(Ri1,Ep,En, Rf). % back to gen
gen3(_Ri,_Ep,_En,F,_APF, _Rf) :-
  rule_bd(F,B),
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
  rule_hd(F,H1), rule_bd(F,B1),
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
  rule_hd(F,H), rule_bd(F,B),
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
  aba_p_rules_append(Ri,[FwA],Ri1),
  aba_asms_append(Ri1, [U1],Ri2), 
  aba_cnts_append(Ri2, [U3],Ri3),  
  utl_rules_append(Ri3,[U2],Ra),
  functor(C2,P,N),
  % create Rg (Ra w/generator of c_alpha)
  asp(Ra,Ep,En,[P/N], Rg).

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
init_mgr(R,L, R2) :-
  write('gen: computing greedy foldings'), nl,
  ( L=[] -> R=R2
  ;
    ( % add generalisations of new facts to the utility rules
      generate_generalisations(L,R, G),
      utl_rules_select(gf(M),R,R1),
      append(M,G,K), keysort(K,S),
      utl_rules_append(R1,[gf(S)],R2)
    )
  ).
%
generate_generalisations([],_, []).
generate_generalisations([S|Ss],R, [L-[I,P/N,F]|Gs]) :- 
  copy_term(S,CpyS),
  rule_id(CpyS,I), rule_bd(CpyS,Ts), rule_hd(CpyS,H), 
  fold_greedy(R,Ts, Fs), length(Fs,L),
  functor(H,P,N),
  new_rule(H,Fs,F),
  generate_generalisations(Ss,R, Gs).

% mgr/2
mgr(G1,G2) :-
  copy_term(G1,CpyG1), rule_hd(CpyG1,H1), rule_bd(CpyG1,B1),
  copy_term(G2,CpyG2), rule_hd(CpyG2,H2), rule_bd(CpyG2,B2),
  %subsumes_chk_conj([H1|B1],[H2|B2]).
  ord_subsumes_chk_conj([H1|B1],[H2|B2]).

% select_mgr_to_fold/3
select_mgr_to_fold(X,Ri,Ro) :- 
  % select any gf
  utl_rules_select(gf([G|Gs]),Ri,R1),
  select_mgr_to_fold_aux(R1,G,Gs,1, S,R2,Rs),
  % select rule with identifier S
  rule_id(X,S),
  utl_rules_append(R2,[gf(Rs)],R3),
  aba_ni_rules_select(X,R3,Ro).

% select_mgr_to_fold_aux/7
select_mgr_to_fold_aux(R1,G1,Gs,I, S,R2,Rs) :-
  nth1(I,Gs,G2),
  !,
  select_mgr_to_fold_aux_tail(R1,G1,G2,Gs,I, S,R2,Rs).
select_mgr_to_fold_aux(R1,_-[S,_,_],Gs,_, S,R1,Gs).
% select_mgr_to_fold_aux_tail/8
select_mgr_to_fold_aux_tail(R1,G1,G2,Gs,I, S,R3,Rs) :-
  select_mgr_to_fold_aux_chk(R1,G1,G2,I, G3,R2,J),
  !,
  nth1(I,Gs,_,Gs1),
  select_mgr_to_fold_aux(R2,G3,Gs1,J, S,R3,Rs).
select_mgr_to_fold_aux_tail(R1,N1-[ID1,P/N,G1],_,Gs,I, S,R2,Rs) :-
  J is I+1,
  select_mgr_to_fold_aux(R1,N1-[ID1,P/N,G1],Gs,J, S,R2,Rs).
% select_mgr_to_fold_aux_chk/7
select_mgr_to_fold_aux_chk(R1,N1-[ID1,P/N,G1],N2-[ID2,P/N,G2],I, N1-[ID1,P/N,G1],R2,I) :-
  N1=<N2,
  mgr(G1,G2),
  !,
  write(' * ['), write(ID1), write('] '), show_rule(G1), nl, 
  write(' *   is more general than'), nl, 
  write(' * ['), write(ID2), write('] '), show_rule(G2), nl,
  rule_id(X,ID2),
  % select rule with identifier ID1
  aba_ni_rules_select(X,R1,R2),
  write(' * > '), write(ID2), write(' < deleted!'), nl.
select_mgr_to_fold_aux_chk(R1,N1-[ID1,P/N,G1],N2-[ID2,P/N,G2],_, N2-[ID2,P/N,G2],R2,0) :-
  N1=N2,
  mgr(G2,G1),
  !,
  write(' * ['), write(ID2), write('] '), show_rule(G1), nl, 
  write(' *   is more general than'), nl, 
  write(' * ['), write(ID1), write('] '), show_rule(G2), nl,
  rule_id(X,ID1),
  % select rule with identifier ID2
  aba_ni_rules_select(X,R1,R2),
  write(' * > '), write(ID1), write(' < deleted!'), nl.    

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
  rule_id(R,J), rule_bd(R,B),
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
  rule_hd(F,H1), rule_bd(F,B1),
  % take any rule in R w/N1+1 atoms
  length(B1,N1), N2 is N1+1, length(B2,N2), 
  aba_p_rules_member(M,R), rule_bd(M,B2),
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

% MODE: ord_subsumes_chk_conj(+T1,+T2)
% TYPE: ord_subsumes_chk_conj(list(term),list(term))
% SEMANTICS: list T1 subsumes list T2, that is, there exists a sublist T3
% consisting of elements in T2 which is subsumed by T1.
ord_subsumes_chk_conj(Gs,Ss) :-
  ord_subsumes_chk_conj(Gs,Ss,[],[]).
%
ord_subsumes_chk_conj([],_,_,_).
ord_subsumes_chk_conj([A|As],Bs,AAcc,BAcc) :-
  ord_select_subsumed(A,Bs, B,Cs),
  subsumes_chk([A|AAcc],[B|BAcc]),
  ord_subsumes_chk_conj(As,Cs,[A|AAcc],[B|BAcc]).

% MODE: ord_select_subsumed(+T1,+L1, -T2,-L2)
% TYPE: ord_select_subsumed(term,list(term),term,list(term))
% SEMANTICS: T2 is an element in L1 s.t. T1 subsumes T2, L2 is L1\T2.
ord_select_subsumed(A,Bs, C,Cs) :-
  functor(A,F,P),
  ord_select_subsumed_chk_aux(A,F/P,Bs, C,Cs).

% MODE: ord_select_subsumed_chk_aux(+T1,+F/P,+L1, -T2,-L2)
% TYPE: ord_select_subsumed_chk_aux(term,term/term,list(term),term,list(term))
% SEMANTICS: T2 is an element in L1 s.t. T1 subsumes T2, L2 is L1\T2.
ord_select_subsumed_chk_aux(A,F/P,[B|Bs], C,Cs) :-
  functor(B,F,P),
  !,
  ord_select_subsumed_chk_aux_tl(A,F/P,B,Bs, C,Cs).
ord_select_subsumed_chk_aux(A,F/P,[_|Bs], C,Cs) :-
  ord_select_subsumed_chk_aux(A,F/P,Bs, C,Cs).  
% ord_select_subsumed_chk_aux_tl
ord_select_subsumed_chk_aux_tl(A,_,B,Bs, B,Bs) :-
  subsumes_chk(A,B).
ord_select_subsumed_chk_aux_tl(A,F/P,_,[B|Bs], C,Cs) :-
  functor(B,F,P),
  ord_select_subsumed_chk_aux_tl(A,F/P,B,Bs, C,Cs).

% MODE: select_subsumed(+T1,+L1, -T2,-L2)
% TYPE: select_subsumed(term,list(term),term,list(term))
% SEMANTICS: T2 is an element in L1 s.t. T1 subsumes T2, L2 is L1\T2.
select_subsumed(G,[S|T],S,T) :-
  subsumes_term(G,S).
select_subsumed(G,[H|T],S,[H|T1]) :-
  select_subsumed(G,T,S,T1).