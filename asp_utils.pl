% This file is part of the ABALearn project.
% Copyright (C) 2023, 2024 The ABALearn's Authors

% This program is free software: you can redistribute it and/or modify
% it under the terms of the GNU General Public License as published by
% the Free Software Foundation, either version 3 of the License, or
% (at your option) any later version.

% This program is distributed in the hope that it will be useful,
% but WITHOUT ANY WARRANTY; without even the implied warranty of
% MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
% GNU General Public License for more details.

:- module(asp_utils,
    [  asp/5
    ,  dump_rule/1
    ,  dump_rules/1
    ,  dump_rules/2
    ,  new_rule/3
    ,  normalize_args/3
    ,  read_bk/2
    ,  bksize/1
    ,  rules_aba_utl/2
    ,  aba_rules/2
    ,  aba_p_rules/2
    ,  aba_p_rules_append/3
    ,  aba_p_rules_replace/3
    ,  aba_p_rules_select/3
    ,  aba_p_rules_member/2
    ,  aba_ni_rules/2
    ,  aba_ni_rules_append/3
    ,  aba_ni_rules_replace/3
    ,  aba_ni_rules_select/3
    ,  aba_ni_rules_member/2
    ,  aba_asms/2
    ,  aba_asms_append/3
    ,  aba_asms_replace/3
    ,  aba_asms_select/3
    ,  aba_asms_member/2
    ,  aba_cnts/2
    ,  aba_cnts_append/3
    ,  aba_cnts_replace/3
    ,  aba_cnts_select/3
    ,  aba_cnts_member/2
    ,  utl_rules/2
    ,  utl_rules_append/3
    ,  utl_rules_replace/3
    ,  utl_rules_select/3
    ,  utl_rules_member/2
    ,  show_rule/1
    ,  show_term/1
    ,  op(300,fy,not)
    ,  rlid/1
    ,  ic/2
    ,  bk_preds/1
    ,  update_fwt/3
    ,  ftw_term_key/2
    ,  ftw_key_ids/3
    ]).

:- use_module(library(dialect/hprolog),
    [ memberchk_eq/2 ]).

:- dynamic rid/1.

:- dynamic rlid/1.

:- dynamic bk_preds/1.

:- dynamic bksize/1.

% rule_id(I): I is a fresh new rule identifier 
rule_id(I) :-
  retract(rid(I)),
  I1 is I+1,
  assert(rid(I1)).

% new_rule(H,B, R): R is the term representing
% a rule whose head is H and body is B
new_rule(H,B, R) :-
  ( is_list(B) -> true; throw(new_rule:not_a_list(B)) ),
  rule_id(I),
  normalize_atom(H, H1,HE),
  normalize_eqs(B, BE,A),
  normalize_atoms(A,BE, A1,BE1),
  append(HE,BE1,E),
  append(E,A1,B1),
  R = rule(I, H1,B1).
% new_rule/3 utility predicate
% normalize_atom/3
normalize_atom(H, H1,B) :-
  H  =.. [P|A],
  normalize_args(A, N,B),
  H1 =.. [P|N].
% normalize_atoms/2 
normalize_atoms([],E, [],E).
normalize_atoms([A1|A1s],E1, [A2|A2s],E4) :-
  normalize_atom(A1, A2,E2),
  append(E2,E1,E3),
  normalize_atoms(A1s,E3, A2s,E4).
% normalize_args/3
normalize_args([], [],[]).
normalize_args([C|As], [V|Vs],[V=C|Bs]) :-
  atomic(C),
  !,
  normalize_args(As, Vs,Bs).
normalize_args([A|As], [A|Vs],Bs) :-
  normalize_args(As, Vs,Bs).
% normalize_eqs/3
normalize_eqs([],[],[]).
normalize_eqs([V=C|L], [V=C|Es],As) :-
  var(V),
  ground(C),
  !,
  normalize_eqs(L, Es,As).
normalize_eqs([C=V|L], [V=C|Es],As) :-
  ground(C),
  var(V),
  !,
  normalize_eqs(L,Es,As).
normalize_eqs([V1=V2|L], Es,As) :-
  var(V1),
  var(V2),
  !,
  V1=V2,
  normalize_eqs(L, Es,As).
normalize_eqs([A|L], Es,[A|As]):-
  normalize_eqs(L, Es,As).
% normalize_body/3
normalize_body(B, B1) :-
  normalize_eqs(B, E1,A),
  normalize_atoms(A, A1),
  append(E1,A1,B1).

% new_asp_rule(H,B, R): R is the term representing
% an asp rule whose head is H and body is B
new_asp_rule(H,B, R) :-
  ( is_list(B) -> true; throw(new_rule:not_a_list(B)) ),
  R = asp_rule(H,B).

%
rules_aba_utl(Rs, AE) :-
  findall(R1, (member(R1,Rs),functor(R1,rule,3)), R), 
  findall(R2, (member(R2,Rs),functor(R2,assumption,1)), A), 
  findall(R3, (member(R3,Rs),functor(R3,contrary,2)), C),
  findall(N, 
    ( member(contrary(Alpha,C_Alpha),C), 
      member(rule(_,_,BwA),R), 
      select(Alpha,BwA,B),
      check_asm_dom(Alpha,B),
      copy_term((Alpha,C_Alpha,B),(Alpha1,C_Alpha1,B1)),
      new_rule(Alpha1,[not C_Alpha1|B1], N) 
    ), 
  U),
  update_fwt(R, aba_enc(R,[],A,C,[fwt([])|U]), AE).

%
check_asm_dom(Alpha,[]) :-
  functor(Alpha,P,N),
  write('ERROR: '), write(P/N), write(' : is not range restricted!'), nl, 
  halt. 
check_asm_dom(_,[_|_]).

% update_fwt(+ABA1,+Rs, ABA2)
update_fwt(Rs,aba_enc(R,N,A,C,U1), aba_enc(R,N,A,C,[fwt(FwT2)|U2])) :-
  select(fwt(FwT1),U1, U2),
  update_fwt_list(Rs,FwT1, FwT2).

% update_fwt_list(+Rs,+FwTI, -FwTO)
update_fwt_list([],FwT, FwT).
update_fwt_list([rule(I,_,As)|Rs],FwTI, FwTO) :-
  update_fwt(I,As,FwTI, FwTI1),
  !,
  update_fwt_list(Rs,FwTI1, FwTO).

% update_fwt(+I,+As,+FwTI, -FwTO)
% add the identifier I of the rule having in the body the atoms As to the table FwTI
update_fwt(_,[],FwT, FwT).
update_fwt(I,[A|As],FwTI, FwTO) :-
  ftw_term_key(A, P/N),
  add_item_ftw(P/N,I,FwTI, FwTI1),
  !,
  update_fwt(I,As,FwTI1, FwTO).  

%
ftw_term_key(X=Y, P/N) :-
  var(X), ground(Y),
  !,
  functor(Y,P,N).
ftw_term_key(X=Y, P/N) :-
  var(Y), ground(X),
  !,
  functor(Y,P,N).
ftw_term_key(A, P/N) :-
  functor(A,P,N).

%
add_item_ftw(P/N,I,FwTI, FwTO) :-
  select((P/N,Is),FwTI, FwTI1),
  !,
  append(Is,[I],Is1),
  FwTO = [(P/N,Is1)|FwTI1].
add_item_ftw(P/N,I,FwTI, [(P/N,[I])|FwTI]).

%
ftw_key_ids(P/N,[T|Ts],I) :-
  ftw_key_ids_aux(P/N,[T|Ts],I),
  !.
ftw_key_ids(K,FwT,I) :- 
  abalearn_error((write('ftw_key_ids: wrong arguments: '), write(ftw_key_ids(K,FwT,I)))).
%
ftw_key_ids_aux(P/N,FwT,I) :-  
  memberchk((P/N,I),FwT).
ftw_key_ids_aux(_,_,[]).

% read_bk(+File, -Rules):
% read a read of rules of from File and
% generate a list of rule/3 terms representing them.
read_bk(FileName, Rules) :-
  % initialize rule identifier
  retractall(rid(_)),
  assert(rid(1)),
  atom_concat(FileName,'.aba',File),
  catch( open(File, read, Stream, [alias(bk)]), Catcher,
         (write(open(File, read, Stream)), write(': '), write(Catcher), nl, fail)),
  read_bk_aux(Stream, Rules),
  rid(ID),
  retractall(rlid(_)),  
  assert(rlid(ID)), % ID of the first learnt rule
  close(Stream),
  retractall(bksize(_)),
  BKSize is ID-1, 
  assert(bksize(BKSize)),
  preds_in_BK(Rules).
% read_bk/2 utility predicate: 
% read all terms from Stream and
% generate the corresponding rule/3 terms
read_bk_aux(Stream, [R|Rs]) :-
  read(Stream,Term),
  Term \== end_of_file,
  !,
  bk_term(Term,R),
  read_bk_aux(Stream, Rs).
read_bk_aux(_, []).
%
bk_term(Term, R) :-
  Term = ( Head :- Body ),
  !,
  conj_to_list(Body,B),
  ( functor(Head,contrary,2) ->
    R = Head
  ;
    new_rule(Head,B, R)
  ).
bk_term(Term, R) :-
  ( functor(Term,assumption,1) ->
    R = Term
  ;
    new_rule(Term,[], R)
  ).

% conj_to_list(C, L): 
% C is a conjunction of the form (A1,...,An);
% L is a list of the form [A1,...,An]
conj_to_list(X,[]) :-
  X==true,
  !.
conj_to_list(B,L) :-
  ( nonvar(B), functor(B,',',_) ->
    ( B = (B1,B2), L=[B1|H], conj_to_list(B2,H) )
  ;
    L=[B]
  ).

%
preds_in_BK(Rules) :-
  preds_in_BK(Rules,P),
  sort(P,S),
  assert(bk_preds(S)).
preds_in_BK([],[]).
preds_in_BK([rule(_,H,_)|Rs],[F/N|P]) :-
  functor(H,F,N),
  !,
  preds_in_BK(Rs,P).
preds_in_BK([_|Rs],P) :-
  preds_in_BK(Rs,P).
 
% SEMANTICS: writes all rules to file
dump_rules(Rs) :-
  dump_rules(Rs,'asp.clingo') .
dump_rules(Rs,File) :-
  tell(File),
  aba_rules(Rs,A), utl_rules(Rs,U),
  dump_rules_aux(A),
  nl,
  dump_rules_aux(U),
  told.  
% write rules
dump_rules_aux([]).
dump_rules_aux([R|Rs]) :-
  copy_term(R,CpyR),
  numbervars(CpyR,0,_),
  dump_rule(CpyR),
  dump_rules_aux(Rs).
% write rule
dump_rule(R) :-
  R = rule(_,H,B),
  !,
  write(H),      % head of the rule
  ( B==[] ->
    ( write('.'), nl ) % fact or int. constr. 
  ;
    ( write(' :- '), write_bd(B) ) % rule w/nonempty body
  ).
dump_rule(R) :-
  R = ic(B),
  !,
  ( write(' :- '), write_bd(B) ). 
dump_rule(R) :-
  R = directive(D,A),
  !,
  write('#'), write(D), write(' '), write(A), write('.'), nl.
dump_rule(R) :-
  % ignore gen/2, msr/2
  functor(R,F,N),
  memberchk(F/N,[gf/1,mgr/1,fwt/1]),
  !.
dump_rule(R) :-
  told,
  write('ERROR: unrecognized rule: '), 
  copy_term(R,CpyR),
  numbervars(CpyR,0,_), 
  write(CpyR),
  nl,
  halt.

% dump_rule/1 utility predicate
write_bd([H]) :-
  !,
  write(H), write('.'), nl.
write_bd([H|T]) :-
  write(H), write(', '),
  write_bd(T).

write_show([]).
write_show([P/N|Ps]) :-
   write('#show '), write(P/N), write('.'), nl,
  write_show(Ps).

% asp: ASP encoding of Ri
asp(Ri,Ep,En,[], Ro) :-
  !,
  ic(Ep,En, I), 
  utl_rules_append(Ri,I,Ro).
asp(Af,Ep,En,[P/N|Ls], ASP) :-
  functor(C,P,N), % C is the atom with functor P/N
  aba_cnts(Af, Cs), % Cs: list of contraries in the ABA framework Af
  member(contrary(A,C),Cs), % C is a contrary (i.e., it belongs to Cs)
  !, % P/N is the predicate of a contrary
  utl_rules(Af,Us), % U is the list of utility rules in Af
  member(rule(_,A,[not C|B]),Us), % A :- not C, B
  copy_term((C,B),(C1,B1)), % get a copy of the contrary C and its context B
  C1 =.. [P|V], % get the variables of C1
  atom_concat(P,'_P',C_P), % primed version of the predicate P
  CP1 =.. [C_P|V], % primed version of the contrary
  new_rule({CP1},B1, G), % {p_P} :- B
  new_rule(C1,[CP1], R), % p :- p_P
  copy_term(CP1,CP2),
  utl_rules_append(Af,[G,R,directive(minimize,{1,CP2:CP2})], Af1),
  asp(Af1,Ep,En,Ls, ASP).
asp(Af,Ep,En,[P/N|Ls], ASP) :-
  atom_concat(P,'_P',P_P),
  findall(E1, ( member(E,Ep), functor(E,P,N), E =..[P|A], E1 =..[P_P|A] ), EpP),
  !, % P/N is the predicate of a contrary
  ep_choice(EpP, EpG), 
  new_rule({EpG},[], G),
  length(V,N), A =.. [P|V], A_P =.. [P_P|V], 
  new_rule(A,[A_P], R), % p :- p_P
  copy_term(A_P,A_P1),
  utl_rules_append(Af,[G,R,directive(minimize,{1,A_P1:A_P1})], Af1),
  asp(Af1,Ep,En,Ls, ASP). 

%
ep_choice([E],E).
ep_choice([E|Es],(E;Gs)) :-
  ep_choice(Es,Gs).

%
ep_generators_pp([], []).
ep_generators_pp([(F/N,F_P/N)|Ls], [R,directive(minimize,{1,F_PP:F_PP})|Gs]) :-
  length(V,N),
  FP =.. [F|V],
  F_PP =.. [F_P|V],
  new_rule(FP,[F_PP],R), 
  ep_generators_pp(Ls, Gs).

% ic(+Ep,+En, I), I is the list of integrity constratints
% generated from positive Ep and negative examples En
ic([],[], []).
ic([],[N|Ns], [ic([N])|Rs]) :-
  ic([],Ns, Rs).
ic([P|Ps],Ns, [ic([not P])|Rs]) :-
  ic(Ps,Ns, Rs).

%
ic(B, ic(B)).

% -----------------------------------------------------------------------------
% aba_enc(R,N,A,C,O)
% R list of rules
% N list of nonintensional rules (to be processed)
% A list of assumptions
% C list of contraries
% U list of utility rules
%
% aba_rules(+ABAf, O), O is the list of ABA rules in ABAf
aba_rules(aba_enc(R,N,_,_,_), O) :-
  append(R,N,O).
%
% aba_p_rules(?ABAf,?R)
% aba_p_rules_append(?ABAf1,?R,?ABAf2)
% aba_p_rules_replace(?ABAf1,?R,?ABAf2)
% aba_p_rules_select(?R,?ABAf1,?ABAf2)
% aba_p_rules_member(?R,?ABAf)
aba_p_rules(aba_enc(R,_,_,_,_),R).
aba_p_rules_append(aba_enc(R1,N,A,C,U),R, aba_enc(R2,N,A,C,U)) :-
  append(R1,R,R2).
aba_p_rules_replace(aba_enc(_,N,A,C,U),R, aba_enc(R,N,A,C,U)).
aba_p_rules_select(R,aba_enc(R1,N,A,C,U), aba_enc(R2,N,A,C,U)) :-
  select(R,R1,R2).
aba_p_rules_member(R,aba_enc(R1,_,_,_,_)) :-
  member(R,R1).
%
% aba_ni_rules(?ABAf,?N)
% aba_ni_rules_append(?ABAf1,?N,?ABAf2)
% aba_ni_rules_replace(?ABAf1,?N,?ABAf2)
% aba_ni_rules_select(?N,?ABAf1,?ABAf2)
% aba_ni_rules_member(?N,?ABAf)
aba_ni_rules(aba_enc(_,N,_,_,_),N).
aba_ni_rules_append(aba_enc(R,N1,A,C,U),N, aba_enc(R,N2,A,C,U)) :-
  append(N1,N,N2).
aba_ni_rules_replace(aba_enc(R,_,A,C,U),N, aba_enc(R,N,A,C,U)).
aba_ni_rules_select(N,aba_enc(R,N1,A,C,U), aba_enc(R,N2,A,C,U)) :-
  select(N,N1,N2).
aba_ni_rules_member(N,aba_enc(_,N1,_,_,_)) :-
  member(N,N1).
%
% aba_asms(?ABAf,?A)
% aba_asms_append(?ABAf1,?A,?ABAf2)
% aba_asms_replace(?ABAf1,?A,?ABAf2)
% aba_asms_select(?A,?ABAf1,?ABAf2)
% aba_asms_member(?A,?ABAf)
aba_asms(aba_enc(_,_,A,_,_),A).
aba_asms_append(aba_enc(R,N,A1,C,U),A, aba_enc(R,N,A2,C,U)) :-
  append(A1,A,A2).
aba_asms_replace(aba_enc(R,N,_,C,U),A, aba_enc(R,N,A,C,U)).
aba_asms_select(A,aba_enc(I,N,A1,C,U), aba_enc(I,N,A2,C,U)) :-
  select(A,A1,A2).
aba_asms_member(A, aba_enc(_,_,A1,_,_)) :-
  member(A,A1).
%
% aba_cnts(?ABAf,?C)
% aba_cnts_append(?ABAf1,?C,?ABAf2)
% aba_cnts_replace(?ABAf1,?C,?ABAf2)
% aba_cnts_select(?C,?ABAf1,?ABAf2)
% aba_cnts_member(?C,?ABAf)
aba_cnts(aba_enc(_,_,_,C,_),C).
aba_cnts_append(aba_enc(R,N,A,C1,U),C, aba_enc(R,N,A,C2,U)) :-
  append(C1,C,C2).
aba_cnts_replace(aba_enc(R,N,A,_,U),C, aba_enc(R,N,A,C,U)).
aba_cnts_select(C,aba_enc(I,N,A,C1,U), aba_enc(I,N,A,C2,U)) :-
  select(C,C1,C2).
aba_cnts_member(C, aba_enc(_,_,_,C1,_)) :-
  member(C,C1).
%
% utl_rules(?ABAf,?U)
% utl_rules_append(?ABAf1,?U,?ABAf2)
% utl_rules_replace(?ABAf1,?U,?ABAf2)
% utl_rules_select(?U,?ABAf1,?ABAf2)
% utl_rules_member(?U,?ABAf)
utl_rules(aba_enc(_,_,_,_,U), U).
utl_rules_append(aba_enc(R,N,A,C,U1),U, aba_enc(R,N,A,C,U2)) :-
  append(U1,U,U2).
utl_rules_replace(aba_enc(R,N,A,C,_),U, aba_enc(R,N,A,C,U)).
utl_rules_select(U,aba_enc(R,N,A,C,U1), aba_enc(R,N,A,C,U2)) :-
  select(U,U1,U2).
utl_rules_member(U, aba_enc(_,_,_,_,U1)) :-
  member(U,U1).

% pretty print a rule
show_rule(R) :-
  copy_term(R,CpyR),
  numbervars(CpyR,0,_),
  CpyR = rule(_,H,B),
  write(H), write(' <- '), write(B).

% pretty print a term
show_term(A) :-
  copy_term(A,CpyA),
  numbervars(CpyA,0,_),
  write(CpyA).