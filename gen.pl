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
  select_foldable(Ri, S,Ri1), % Ri1 = Ri\S
  !,
  write(' to fold: '), show_rule(S), nl,
  write(' begin folding'), nl, 
  folding(Ri1,S, F),  % F = fold-all(S)
  write(' folding result: '), show_rule(F), nl,
  gen2(Ri1,Ep,En,F, Rf).
gen1(Ri,_Ep,_En, Ri) :-
  write('gen1: noting to fold.'), nl. 
% gen2
gen2(Ri,Ep,En,F, Rf) :-
  aba_i_rules_append(Ri,[F], Ri1),
  entails(Ri1,Ep,En),
  write('gen2: extended ABA entails <E+,E-> - using folding'), nl,
  !,
  gen7(Ri1,Ep,En, Rf). % go to subsumption
% gen2 - RELTO assumption found
gen2(Ri,Ep,En,F, Rf) :-
  lopt(asm_intro(relto)),
  write('gen2: extended ABA does not entail <E+,E-> - looking for assumption relative to'), nl,
  exists_assumption_relto(Ri,F, APF/_),
  !,
  gen3(Ri,Ep,En,F,APF, Rf).
% gen2 - RELTO NEW assumption or SECHK assumption chk
gen2(Ri,Ep,En,F, Rf) :-
  new_assumption(Ri,Ep,En,F, Ra,Rg,A,FwAP),
  write('gen2: generating NEW assumption: '), show_term(A), nl,
  write(' assumption introduction result: '), show_rule(FwAP), nl,
  compute_conseq(Rg, Cs),
  ( Cs \==[] -> 
    member(RgAS, Cs)
    ; 
    ( write('gen2: There is no answer set!'), nl, halt ) 
  ), 
  gen4(Ri,Ep,En,F,Ra,A,RgAS, Rf).
% gen3 - OLD assumption found
gen3(Ri,Ep,En,F,APF, Rf) :-
  F = rule(_,H,B),
  term_variables(B,V),
  AP =.. [APF|V],
  new_rule(H,[AP|B], FwAP),
  aba_i_rules_append(Ri,[FwAP], Ri1),
  write('gen3: found: '), show_term(AP), write(' ... '),
  entails(Ri1,Ep,En), % if Ri1 w/mg_alpha does not entails E+,E-,
  !,
  write('OK, assumption introduction result: '), show_rule(FwAP), nl,
  gen7(Ri1,Ep,En, Rf). % go to subsumption
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
  exists_assumption_sechk(AF/N,Ri,RgAS, APF/N),
  !,
  gen3(Ri,Ep,En,F,APF, Rf).
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
  ( lopt(learning_mode(cautious)) -> entails(Ra1,Ep,En) ; true  ),
  ( lopt(folding_selection(mgr)) -> update_mgr(Ra1,Rs,Ra2) ; Ra1=Ra2 ),
  gen7(Ra2,Ep,En, Rf). % go to subsumption
% gen7 - subsumption
gen7(Ri,Ep,En, Rf) :-
  write('gen7: checking subsumption'), nl,
  ( ( lopt(folding_selection(mgr)), \+ tbl_occurs_in_BK ) -> Ri=Ri1 ; subsumption(Ri,Ep,En, Ri1) ),
  gen1(Ri1,Ep,En, Rf). % back to gen


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

% select_foldable(+R, -S,-Ri)
select_foldable(R, S,R1) :-
  lopt(folding_selection(any)),
  aba_ni_rules_select(S,R,R1),
  !.  
select_foldable(R, S,R2) :-
  lopt(folding_selection(mgr)),
  % select a nonintensional rule
  aba_ni_rules_select(S,R,R1),
  S = rule(I,_,_),
  % s.t. there exists a generalisation for I
  % utl_rules_member(gen(_,[id(I)|_]),R),
  ( utl_rules_member(gen(_,[id(I)|_]),R) ; utl_rules_member(fp(_,[id(I)|_]),R) ),
  !,
  ( tbl_occurs_in_BK -> 
    R2=R1 
  ; 
    remove_msr(R1,id(I),R2) 
  ).

%
init_mgr(R, R1) :-
  write('gen: initializing generalisations'), nl,
  % select all nonintensional rules
  aba_ni_rules(R,L),
  ( L=[] -> R=R1
  ;
    ( % add their generalisations to the utility rules
      aba_i_rules(R,I),
      generate_generalisations(L,I, G),
      filter_generalisations(G, G1),
      utl_rules_append(R,G1,R1)
    )
  ).
update_mgr(R,L, R1) :-
  write('gen: updating generalisations'), nl,
  aba_i_rules(R,I),
  generate_generalisations(L,I, G),
  filter_generalisations(G, G1),
  utl_rules_append(R,G1,R1).
%
generate_generalisations([],_, []).
generate_generalisations([S|Ss],R, [G|Gs]) :- 
  copy_term(S,rule(I,H,Ts)),
  fold_greedy(R,H,[],Ts, Fs),
  !,
  new_rule(H,Fs,F),
  findall(P1/N1,(member(A1,Fs),functor(A1,P1,N1)),L1),
  functor(H,P,N),
  G=gen(F,[id(I),P/N|L1]),
  write(' ffp: '), 
  copy_term(G,G1), numbervars(G1,0,_), write(G1), nl,
  generate_generalisations(Ss,R, Gs).
%
filter_generalisations(L1, R3) :-
  select(gen(G1,[ID1,P/N|P1]),L1,L2),
  select(gen(G2,[ID2,P/N|P2]),L2,L3),
  subset(P1,P2), % P1 is a subset of P2
  mgr(G1,G2),
  !,
  write(' '), show_rule(G1), write(' is more general than '), show_rule(G2), nl,
  update_msr(ID1,ID2,L3,L4),
  % filter_generalisations([gen(G1,[ID1,P/N|P1])|L4], R3).
  filter_generalisations([gen(G1,[ID1,P/N|P1]),fp(G2,[ID2,P/N|P2])|L4], R3).
filter_generalisations(L1, L1).

%
mgr(G1,G2) :-
  copy_term(G1,rule(_,H1,B1)),
  copy_term(G2,rule(_,H2,B2)),
  H1 = H2,
  subsumes_chk_conj(B1,B2).

%
update_msr(G,S,L, [msr(I,G)|L4]) :-
  select(msr(I,S),L,L1),
  !,
  update_msr(G,S,L1, L4).
update_msr(G,S,L, [msr(S,G)|L]).

%
remove_msr(R,id(I), R3) :-
  utl_rules_select(msr(id(J),id(I)),R, R1),
  !,
  aba_ni_rules_select(rule(J,H,B),R1, R2),
  write(' removing more specific nonintensional rule '), show_rule(rule(J,H,B)), nl,
  remove_msr(R2,id(I), R3).
remove_msr(R,_, R).

% subsumption(+Ri,+Ep,+En, -Ro)
% Ro is the result obained by removing all subsumed nonintensional rules from Ri
subsumption(Ri,Ep,En, Ro) :-
  aba_ni_rules(Ri,NiR), length(NiR,N),  write(' evaluating subsumption of '), write(N), write(' rules'), nl,
  aba_ni_rules_select(R,Ri,Ri1),
  subsumed(Ri1,Ep,En, R),
  !,
  write(' subsumed: '), show_rule(R), nl, 
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
exists_assumption_relto(R,F, A/N) :-
  % rule to be folded
  F = rule(_,_,B1),
  % take any rule in R and its assumption
  aba_i_rules_member(rule(_,_,B2),R),
  aba_asms_member(assumption(Alpha),R),
  copy_term(Alpha,Alpha1),
  select(Alpha1,B2,R2),
  % B1 and R2 (B2 w/o assumption) are variant
  permutation_variant(B1,R2),
  functor(Alpha,A,N).


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
permutation_variant(L1,L2) :-
  L1 = [_], L2 = [_],
  !,
  L1 =@= L2.
% length 2
permutation_variant(L1,L2) :-
  L1 = [_,_],
  L2 = [_,_],
  L1 =@= L2.
permutation_variant(L1,L2) :-
  L1 = [X,Y],
  P1 = [Y,X],
  !,
  P1 =@= L2.
% length >= 3
permutation_variant(L1,L2) :-
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
subsumes_chk_conj(A,B) :-
  sort(A,S1),
  sort(B,S2),
  subsumes_list(S1,S2,SL),
  subsumes_chk(S1,SL).

% MODE: subsumes_list(+T1,+T2, -T3,-T4)
% TYPE: subsumes_list(list(term),list(term),list(term),list(term))
% SEMANTICS: T3 is a list consisting of elements in T2 each of which
% is subsumed by an element in T1. T4 is T2\T3.
subsumes_list([],_,[]).
subsumes_list([G|T],B,[S|SL]) :-
  select_subsumed(G,B,S,R),
  subsumes_list(T,R,SL).

% MODE: select_subsumed(+T1,+L1, -T2,-L2)
% TYPE: select_subsumed(term,list(term),term,list(term))
% SEMANTICS: T2 is an element in L1 s.t. T1 subsumes T2, L2 is L1\T2.
select_subsumed(G,[S|T],S,T) :-
  subsumes_chk(G,S).
select_subsumed(G,[H|T],S,[H|T1]) :-
  % elements are sorted, if H has the same functor of K keep going on looking for a subsumed element in L1
  functor(G,P1,N1),
  functor(H,P1,N1),
  select_subsumed(G,T,S,T1).