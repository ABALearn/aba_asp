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

:- module(clingo,
    [  compute_conseq/2 % compute brave/cautious conseq. and assert them
    ,  entails/3
    ,  subsumed/4
    ]).


:- use_module('asp_utils').

% write the computed consequences (read from cc.clingo) as a prolog list L into cc.pl
compute_conseq(Rs, Cs) :-
  lopt(learning_mode(brave)),
  % write rules to file
  dump_rules(Rs),
  % invoke clingo to compute the consequences of Rs and write them to cc.clingo
  shell('clingo asp.clingo --out-ifs=, --opt-mode=optN --quiet=1 > cc.clingo 2>> clingo.stderr.txt',_),
  shell('cat cc.clingo | grep \'^OPTIMUM FOUND\'  > /dev/null',EXIT_CODE),
  EXIT_CODE == 0, % exit status of grep: 0 stands for 'One or more lines were selected.'
  !,
  % TODO: assuming one solution
  shell('cat cc.clingo | grep -A1 \'^Answer:\' | tail -n -2 | awk \'/Answer:/ {f=NR}; f && NR==f+1 { print "[",$0,"]."}\' > cc.pl'),
  see('cc.pl'),
  % read 'cc.clingo' and assert it into the database
  read_all(Cs),
  seen,
  shell('rm -f clingo.stderr.log',_).
compute_conseq(Rs, Cs) :-
  lopt(learning_mode(cautious)),
  % write rules to file
  dump_rules(Rs),
  % invoke clingo to compute the consequences of Rs and write them to cc.clingo
  shell('clingo asp.clingo --out-ifs=, --opt-mode=ignore --enum-mode=cautious > cc.clingo 2>> clingo.stderr.log',_),
  shell('cat cc.clingo | grep \'^SATISFIABLE\'  > /dev/null',EXIT_CODE),
  EXIT_CODE == 0, % exit status of grep: 0 stands for 'One or more lines were selected.'
  !,
  shell('echo \'[\' > cc.pl'),
  shell('cat cc.clingo | grep -A1 \'^Answer:\' | tail -n -1 >> cc.pl'),
  shell('echo \'].\' >> cc.pl'),
  see('cc.pl'),
  % read 'cc.clingo' and assert it into the database
  read_all(Cs), % Cs is a singleton
  seen,
  shell('rm -f clingo.stderr.log',_).
compute_conseq(_, []) :-
  shell('cat cc.clingo | grep \'^UNSATISFIABLE\' > /dev/null',EXIT_CODE),
  EXIT_CODE == 0,
  !.
% assert all terms from file
read_all([A|As]) :-
  read(A),
  A \== end_of_file,
  !,
  read_all(As).
read_all([]).

% -----------------------------------------------------------------------------
% Ri subsumes rule R
subsumed(Ri,Ep,En, R) :-
  lopt(learning_mode(brave)),
  !,
  R = rule(_,H,B),
  ic([not H|B],I),
  utl_rules_append(Ri,[I], Ri1),
  % asp w/ic for Ep and En
  asp(Ri1,Ep,En,[], Ro),
  % write rules to file
  dump_rules(Ro),
  % invoke clingo to compute the consequences of Rs and write them to cc.clingo
  shell('clingo asp.clingo --out-ifs=, --opt-mode=ignore > cc.clingo 2>> clingo.stderr.txt',_EXIT_CODE),
  shell('cat cc.clingo | grep \'^SATISFIABLE\'  > /dev/null',EXIT_CODE),
  EXIT_CODE == 0. % exit status of grep: 0 stands for 'One or more lines were selected.'
subsumed(Ri1,_Ep,_En, R) :-
  lopt(learning_mode(cautious)),
  % write rules to file
  dump_rules(Ri1),
  % invoke clingo to compute the consequences of Rs and write them to cc.clingo
  shell('clingo asp.clingo --out-ifs=, --opt-mode=ignore --enum-mode=cautious > cc.clingo 2>> clingo.stderr.log',_EXIT_CODE),
  shell('cat cc.clingo | grep \'^SATISFIABLE\'  > /dev/null',EXIT_CODE),
  EXIT_CODE == 0, % exit status of grep: 0 stands for 'One or more lines were selected.'
  shell('echo \'[\' > cc.pl'),
  shell('cat cc.clingo | grep -A1 \'^Answer:\' | tail -n -1 >> cc.pl'),
  shell('echo \'].\' >> cc.pl'),
  see('cc.pl'),
  % read 'cc.clingo' and assert it into the database
  read(As),
  seen,
  copy_term(R,CpyS),
  CpyS = rule(_,H,B),
  unify_eqs(B),
  !,
  member(H,As).
% subsumed (cautious) predicate
unify_eqs([]).
unify_eqs([V=C|E]) :-
  V=C,
  unify_eqs(E).

% -----------------------------------------------------------------------------
% R entails all elements in Ep and R does not entail any element of En
entails(R,Ep,En) :-
  lopt(learning_mode(brave)),
  !,
  asp(R,Ep,En,[], A),
  % write rules to file
  dump_rules(A),
  % invoke clingo to compute the consequences of Rs and write them to cc.clingo
  shell('clingo asp.clingo --out-ifs=, --opt-mode=ignore > cc.clingo 2>> clingo.stderr.txt',_EXIT_CODE),
  shell('cat cc.clingo | grep \'^SATISFIABLE\'  > /dev/null',EXIT_CODE),
  EXIT_CODE == 0. % exit status of grep: 0 stands for 'One or more lines were selected.'
entails(R,Ep,En) :-
  lopt(learning_mode(cautious)),
  !,
  dump_rules(R),
  % invoke clingo to compute the consequences of Rs and write them to cc.clingo
  shell('clingo asp.clingo --out-ifs=, --opt-mode=ignore --enum-mode=cautious > cc.clingo 2>> clingo.stderr.log',_EXIT_CODE),
  shell('cat cc.clingo | grep \'^SATISFIABLE\'  > /dev/null',EXIT_CODE),
  EXIT_CODE == 0, % exit status of grep: 0 stands for 'One or more lines were selected.'
  shell('echo \'[\' > cc.pl'),
  shell('cat cc.clingo | grep -A1 \'^Answer:\' | tail -n -1 >> cc.pl'),
  shell('echo \'].\' >> cc.pl'),
  see('cc.pl'),
  % read 'cc.clingo' and assert it into the database
  read(As),
  seen,
  entails_cautious(Ep,En,As).
% entails (cautious) utility predicate
entails_cautious([],[],_Cs).
entails_cautious([E|Ep],En,Cs) :-
  member(E,Cs),
  !,
  entails_cautious(Ep,En,Cs).
entails_cautious([],[E|En],Cs) :-
  \+ member(E,Cs),
  !,
  entails_cautious([],En,Cs).
