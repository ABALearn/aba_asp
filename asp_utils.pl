:- module(asp_utils,
    [  asp/2
    ,  asp/4
    ,  asp_star/4
    ,  asp_plus/5
    ,  dump_rule/1
    ,  dump_rules/1
    ,  dump_rules/2
    ,  new_rule/3
    ,  normalize_args/3
    ,  read_bk/2
    ,  bksize/1
    ,  rules_aba_utl/2
    ,  aba_rules/2
    ,  aba_i_rules/2
    ,  aba_i_rules_append/3
    ,  aba_i_rules_replace/3
    ,  aba_i_rules_select/3
    ,  aba_i_rules_member/2
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
    ]).

:- use_module(library(dialect/hprolog),
    [ memberchk_eq/2 ]).

:- dynamic rid/1.
rid(1).

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
rules_aba_utl(Rs, aba_enc(R,[],A,C,U)) :-
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
  U).

%
check_asm_dom(Alpha,[]) :-
  functor(Alpha,P,N),
  write('ERROR: '), write(P/N), write(' : is not range restricted!'), nl, 
  halt. 
check_asm_dom(_,[_|_]).  

% read_bk(+File, -Rules):
% read a read of rules of from File and
% generate a list of rule/3 terms representing them.
read_bk(FileName, Rules) :-
  atom_concat(FileName,'.aba',File),
  catch( open(File, read, Stream, [alias(bk)]), Catcher,
         (write(open(File, read, Stream)), write(': '), write(Catcher), nl, fail)),
  retractall(rlid(_)),
  read_bk_aux(Stream, Rules),
  rid(ID),
  assert(rlid(ID)), % ID of the first learnt rule
  close(Stream),
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
  memberchk(F/N,[gen/2,msr/2,fp/2]),
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
asp(Ri, Ri).
asp(Ri,Ep,En, Ro) :-
  ic(Ep,En, I),              % (c), (d)
  utl_rules_append(Ri,I,Ri1),
  asp(Ri1, Ro).
% asp_plus: ASP+
asp_plus(Ri,Ep,En,Ts, Ro) :-
  generators(Ts, G),         % (b.2) learnable predicates
  utl_rules_append(Ri,G,Ri1),
  asp(Ri1,Ep,En, Ro).
% asp_star: ASP* (w/primed predicates)
asp_star(Ri,Ep,En, Ro) :-
  % Cs: set of contrary predicates
  aba_cnts(Ri, C),
  aba_rules(Ri, R),
  findall((Alpha,C_Alpha,B), 
    ( member(contrary(Alpha,C_Alpha),C), member(rule(_,_,BwA),R), select(Alpha,BwA,B) ), Cs),
  generators_pp(Cs, Gs),     % (e)
  utl_rules_append(Ri,Gs, Ri1),
  ep_generators_pp(Ep, Gs1), 
  utl_rules_append(Ri1,Gs1, Ri2),
  asp(Ri2,Ep,En, Ro).

%
generators([], []).
generators([(CP,B)|Fs], [G,O|Gs]) :-
  new_rule({CP},B, G),
  O=directive(minimize,{1,CP:CP}),
  generators(Fs, Gs).

%
generators_pp([], []).
generators_pp([(AP,CP,B)|Fs], [G,R,A,O|Gs]) :-
  CP =..[C|V],
  atom_concat(C,'_P',C_P),
  C_PP =.. [C_P|V],
  new_rule({C_PP},B, G),            % {p_P} :- B
  copy_term((CP,C_PP),(CP1,C_PP1)),
  new_rule(CP1,[C_PP1],R),          % p :- p_P
  copy_term((AP,CP,B),(AP2,CP2,B2)), 
  new_rule(AP2,[not CP2|B2], A),
  copy_term(C_PP,C_PP3),
  O=directive(minimize,{1,C_PP3:C_PP3}),
  generators_pp(Fs, Gs).

%
ep_generators_pp(Ep, [G|Gs]) :-
  findall(E1, ( member(E,Ep), E =..[F|A], atom_concat(F,'_P',F_P), E1 =..[F_P|A]), EpP),
  ep_choice(EpP, EpG), 
  new_rule({EpG},[], G),
  setof((F/N,F_P/N), [E]^( member(E,Ep), functor(E,F,N), atom_concat(F,'_P',F_P) ), Fs), 
  ep_generators_pp_aux(Fs, Gs).

%
ep_choice([E],E).
ep_choice([E|Es],(E;Gs)) :-
  ep_choice(Es,Gs).

%
ep_generators_pp_aux([], []).
ep_generators_pp_aux([(F/N,F_P/N)|Ls], [R,directive(minimize,{1,F_PP:F_PP})|Gs]) :-
  length(V,N),
  FP =.. [F|V],
  F_PP =.. [F_P|V],
  new_rule(FP,[F_PP],R), 
  ep_generators_pp_aux(Ls, Gs).

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
% aba_enc(I,N,A,C,U)
% I list of intensional rules
% N list of nonintensional rules
% A list of assumptions
% C list of contraries
% U list of utility rules
%
% aba_rules(+ABAf, R), R is the list of ABA rules in ABAf
aba_rules(aba_enc(I,N,_,_,_), R) :-
  append(I,N,R).
%
% aba_i_rules(?ABAf1,?R)
% aba_i_rules_append(?ABAf1,?R,?ABAf2)
% aba_i_rules_replace(?ABAf1,?R,?ABAf2)
% aba_i_rules_select(?R,?ABAf1,?ABAf2)
% aba_i_rules_member(?R,?ABAf)
aba_i_rules(aba_enc(I,_,_,_,_),I).
aba_i_rules_append(aba_enc(I1,N,A,C,U),R, aba_enc(I2,N,A,C,U)) :-
  append(I1,R,I2).
aba_i_rules_replace(aba_enc(_,N,A,C,U),R, aba_enc(R,N,A,C,U)).
aba_i_rules_select(R,aba_enc(I1,N,A,C,U), aba_enc(I2,N,A,C,U)) :-
  select(R,I1,I2).
aba_i_rules_member(R, aba_enc(I,_,_,_,_)) :-
  member(R,I).
%
% aba_ni_rules(?ABAf1,?R)
% aba_ni_rules_append(?ABAf1,?R,?ABAf2)
% aba_ni_rules_replace(?ABAf1,?R,?ABAf2)
% aba_ni_rules_select(?R,?ABAf1,?ABAf2)
% aba_ni_rules_member(?R,?ABAf)
aba_ni_rules(aba_enc(_,N,_,_,_),N).
aba_ni_rules_append(aba_enc(I,N1,A,C,U),R, aba_enc(I,N2,A,C,U)) :-
  append(N1,R,N2).
aba_ni_rules_replace(aba_enc(I,_,A,C,U),R, aba_enc(I,R,A,C,U)).
aba_ni_rules_select(R,aba_enc(I,N1,A,C,U), aba_enc(I,N2,A,C,U)) :-
  select(R,N1,N2).
aba_ni_rules_member(R, aba_enc(_,N,_,_,_)) :-
  member(R,N).
%
% aba_asms(?ABAf1,?R)
% aba_asms_append(?ABAf1,?R,?ABAf2)
% aba_asms_replace(?ABAf1,?R,?ABAf2)
% aba_asms_select(?R,?ABAf1,?ABAf2)
% aba_asms_member(?R,?ABAf)
aba_asms(aba_enc(_,_,A,_,_),A).
aba_asms_append(aba_enc(I,N,A1,C,U),R, aba_enc(I,N,A2,C,U)) :-
  append(A1,R,A2).
aba_asms_replace(aba_enc(I,N,_,C,U),R, aba_enc(I,N,R,C,U)).
aba_asms_select(R,aba_enc(I,N,A1,C,U), aba_enc(I,N,A2,C,U)) :-
  select(R,A1,A2).
aba_asms_member(R, aba_enc(_,_,A,_,_)) :-
  member(R,A).
%
% aba_cnts(?ABAf1,?R)
% aba_cnts_append(?ABAf1,?R,?ABAf2)
% aba_cnts_replace(?ABAf1,?R,?ABAf2)
% aba_cnts_select(?R,?ABAf1,?ABAf2)
% aba_cnts_member(?R,?ABAf)
aba_cnts(aba_enc(_,_,_,C,_),C).
aba_cnts_append(aba_enc(I,N,A,C1,U),R, aba_enc(I,N,A,C2,U)) :-
  append(C1,R,C2).
aba_cnts_replace(aba_enc(I,N,A,_,U),R, aba_enc(I,N,A,R,U)).
aba_cnts_select(R,aba_enc(I,N,A,C1,U), aba_enc(I,N,A,C2,U)) :-
  select(R,C1,C2).
aba_cnts_member(R, aba_enc(_,_,_,C,_)) :-
  member(R,C).
%
% utl_rules(?ABAf,?R)
% utl_rules_append(?ABAf1,?R,?ABAf2)
% utl_rules_replace(?ABAf1,?R,?ABAf2)
% utl_rules_select(?R,?ABAf1,?ABAf2)
% utl_rules_member(?R,?ABAf)
utl_rules(aba_enc(_,_,_,_,R), R).
utl_rules_append(aba_enc(I,N,A,C,U1),R, aba_enc(I,N,A,C,U2)) :-
  append(U1,R,U2).
utl_rules_replace(aba_enc(I,N,A,C,_),R, aba_enc(I,N,A,C,R)).
utl_rules_select(R,aba_enc(I,N,A,C,U1), aba_enc(I,N,A,C,U2)) :-
  select(R,U1,U2).
utl_rules_member(R, aba_enc(_,_,_,_,U)) :-
  member(R,U).

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