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
:- use_module(library(clpfd)).

:- consult('rote_learning.pl'),
   consult('gen.pl'),
   consult('io.pl').

:- initialization(set_lopt(folding_mode(nd))).
:- initialization(set_lopt(folding_steps(10))).
%:- initialization(set_lopt(folding_mode(lazy))).
:- initialization(set_lopt(folding_selection(any))).
:- initialization(set_lopt(folding_space(all))).
:- initialization(set_lopt(asm_intro(relto))).
:- initialization(set_lopt(learning_mode(cautious))).
:- initialization(set_lopt(verbosity(debugging))).
:- initialization(set_lopt(log_stream(user_output))).
:- initialization(set_lopt(post_folding_test_entailment(true))).

:- initialization(listing(lopt/1)).

% aba_asp(+BK,+Ep,+En)
% aba_asp(BK,Ep0,En0,Ep,En)
% BK: file including the background knowledge
% (Ep0) Ep: (already covered) positive examples
% (En0) En: (already covered) negative examples
aba_asp(BK,Ep,En) :-
  aba_asp(BK,[],[],Ep,En, _Ro).
aba_asp(BK,Ep0,En0,Ep,En) :-
  aba_asp(BK,Ep0,En0,Ep,En, _Ro).  

% aba_asp(+BK,+Ep,+En, -Ro)
% Ro: learnt ABA framework
aba_asp(BK,Ep0,En0,Ep,En, Ro) :-
  % initialize solution counter
  retractall(sol_counter(_)),
  assert(sol_counter(0)),
  % initialize tokens (for folding)
  retractall(tokens(_)),
  assert(tokens(1)),
  %%%
  nl, write('Current learning options:'), nl,
  listing(lopt/1),
  %
  read_bk(BK, Rs),
  check_aba(Rs,Ep,En),
  rules_aba_utl(Rs, R1), % partition the list of rules Rs into two sublists ABA and UTL
                         % ABA = rules of the ABA framework
                         % UTL = utility rules (e.g., assumption, contrary)
  init_new_pred_gen(R1), % initialize generator of new assumption names
  aba_asp_proc(BK,R1,Ep0,En0,Ep,En, Ro).
%
aba_asp_proc(BK,R1,Ep0,En0,Ep,En, Ro) :-
  statistics(runtime,[T1,_]),     % cpu time
  statistics(system_time,[S1,_]), % system time
  statistics(walltime,[W1,_]),    % wall time                     % rules counter
  %%%
  roLe(R1,Ep0,En0,Ep,En, RL,R2),    % RoLe
  ( lopt(folding_selection(mgr)) -> ( utl_rules_append(R2,[gf([])],R3), init_mgr(R3,RL, R4) ) ; R2=R4 ),
  genT(R4,Ep0,En0,Ep,En, Ro),    % GEN
  %%%
  statistics(runtime,[T2,_]),     T is T2-T1,   
  statistics(system_time,[S2,_]), S is S2-S1,
  statistics(walltime,[W2,_]),    W is W2-W1,
  nl,
  write('BK size (rules):   '), bksize(BKSize), write(BKSize), nl,
  write('Positive examples: '), length(Ep,EpN), write(EpN), nl,
  write('Negative examples: '), length(En,EnN), write(EnN), nl,
  write('ABA size (rules):  '), 
  aba_rules(Ro,Rules), length(Rules,RulesSize),
  write(RulesSize), nl, 
  write('Learning (CPU,Sys,Wall,CPU+Sys) time: '), 
  write(T), write(','), 
  write(S), write(','), 
  write(W), write(','), Lt is T+S, write(Lt), nl,
  % output files
  atom_concat(BK,'.sol.aba',Out),
  retract(sol_counter(N)), M is N+1, assert(sol_counter(M)),
  nl, write('Writing solution no. '), write(M), write(' to '), write(Out), nl, nl,
  write_sol(Ro,Out),
  atom_concat(BK,'.sol.asp',OutASP),
  dump_rules(Ro,OutASP),
  ( lopt(check_ic) -> 
    ( asp(Ro,Ep0,En0,Ep,En,[], RoASPwIC), atom_concat(BK,'.sol_chk.asp',OutASPwIC),  dump_rules(RoASPwIC,OutASPwIC) ) 
  ;
    true
  ).
aba_asp_proc(_,_,_,_,_,_, _) :-
  sol_counter(N),
  nl, 
  ( N == 0 ->
    write('* No solution found! ')
  ; 
    write('* There are no more solutions! ')
  ). 

%
:- dynamic lopt/1.
set_lopt(folding_mode(nd)) :-
  !,
  retractall(lopt(folding_mode(_))),
  assert(lopt(folding_mode(nd))),
  ( lopt(folding_steps(_)) -> true ; set_lopt(folding_steps(5)) ).
set_lopt(folding_mode(X)) :-
  member(X,[greedy,all,lazy]),
  !,
  retractall(lopt(folding_mode(_))),
  assert(lopt(folding_mode(X))).
set_lopt(folding_steps(X)) :-
  !,
  retractall(lopt(folding_steps(_))),
  assert(lopt(folding_steps(X))).
set_lopt(asm_intro(X)) :-
  member(X,[sechk,relto]),
  !,
  retractall(lopt(asm_intro(_))),
  assert(lopt(asm_intro(X))).
set_lopt(learning_mode(X)) :-
  member(X,[brave,cautious]),
  !,
  retractall(lopt(learning_mode(_))),
  assert(lopt(learning_mode(X))).
set_lopt(folding_selection(X)) :-
  member(X,[any,mgr]),
  !,
  retractall(lopt(folding_selection(_))),
  assert(lopt(folding_selection(X))).
set_lopt(check_ic) :-
  !,
  retractall(lopt(check_ic)),
  assert(lopt(check_ic)). 
set_lopt(folding_space(X)) :-
  member(X,[bk,all]),
  !,
  retractall(lopt(folding_space(_))),
  assert(lopt(folding_space(X))).
set_lopt(verbosity(X)) :-
  memberchk(X,[off,error,warning,info,fine,finer,finest,debugging]),
  !,
  retractall(lopt(verbosity(_))),
  verbosity_value(X,V),
  assert(lopt(verbosity(V))).
set_lopt(log_stream(S)) :-
  atomic(S),
  !,
  retractall(lopt(log_stream(_))),
  assert(lopt(log_stream(S))).
set_lopt(post_folding_test_entailment(V)) :-
  atomic(V),
  member(V,[true,false]),
  !,
  retractall(lopt(post_folding_test_entailment(_))),
  assert(lopt(post_folding_test_entailment(V))).  
set_lopt(X) :-
  throw(wrong_lopt(X)).  

write_sol(Rs,File) :-
  tell(File),
  % intensional and nonintensional rules
  aba_rules(Rs,R),
  write_rules(R),
  nl,
  % assumptions
  aba_asms(Rs,A),
  % contraries
  aba_cnts(Rs,C),
  append(A,C,AC),
  write_ac(AC),
  told.

% write rule
write_rules([]). 
write_rules([R|Rs]) :-
  is_rule(R),
  !,
  copy_term(R,CpyR),
  numbervars(CpyR,0,_),  
  rule_hd(CpyR,H), rule_bd(CpyR,B),
  write(H), write(' :- '), write_conj(B),
  write_rules(Rs).
write_rules([_|Rs]) :-
  write_rules(Rs). 

%
write_conj([]) :-
  write('.'), nl.
write_conj([H]) :-
  !,
  write(H), write('.'), nl.
write_conj([H|T]) :-
  write(H), write(', '),
  write_conj(T).

%
write_ac([]).
write_ac([R|Rs]) :-
  R = assumption(_),
  !,
  copy_term(R,CpyR),
  numbervars(CpyR,0,_),    
  write(CpyR), write('.'), nl,
  write_ac(Rs). 
write_ac([R|Rs]) :-
  R = contrary(_,_),
  !,
  copy_term(R,CpyR),
  numbervars(CpyR,0,_),
  CpyR = contrary(A,_),
  write(CpyR), write(' :- '), write(assumption(A)),  write('.'), nl,
  write_ac(Rs).
write_ac([_|Rs]) :-
  write_ac(Rs). 

%
check_aba(Rules,Ep,_En) :-
  collect_consts(Rules,[], Cs),
  check_ep_consts(Ep,Cs).

%
collect_consts([],Ci, Co) :-
  sort(Ci,Co).
collect_consts([R|Rs],Ci, Co) :-
  rule_bd(R,B),
  !,  
  collect_consts_aux(B,Ci, Ci1),
  collect_consts(Rs,Ci1, Co).
collect_consts([_|Rs],Ci, Co) :-
  collect_consts(Rs,Ci, Co).  
% assumption: rules are normalized
% (i.e., constants occur in the body 
% of rules as equalities of the form 
% Var=constant)
collect_consts_aux([],Ci, Ci).
collect_consts_aux([X=C|Bs],Ci, Cs) :-
  var(X),
  ground(C),
  !,
  collect_consts_aux(Bs,[C|Ci], Cs).
collect_consts_aux([_|Bs],Ci, Cs) :-
  collect_consts_aux(Bs,Ci, Cs).

%
check_ep_consts([],_).
check_ep_consts([E|Es],Ci) :-
  E =.. [_|Args],
  check_ep_consts_aux(Args,Ci),
  check_ep_consts(Es,Ci).

%
check_ep_consts_aux([],_).
check_ep_consts_aux([Arg|Args],Ci) :-
  nonvar(Arg),
  !,
  ( member(Arg,Ci) ->
    check_ep_consts_aux(Args,Ci)
  ;
    ( write('ERROR: unknown constant: '), write(Arg), nl, nl, halt )
  ).
check_ep_consts_aux([Arg|Args],Ci) :-
  var(Arg),
  check_ep_consts_aux(Args,Ci).
