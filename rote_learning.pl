% Rote Learning procedures

:- use_module('asp_utils').
:- use_module('asp_engine').

% roLe(+Ri,+Ep,+En, -Ro)
% rote learning of Ep and En
roLe(Ri,Ep,En, Ro) :-
  lopt(learning_mode(brave)),
  !,
  asp_star(Ri,Ep,En, S),
  compute_conseq(S, CS),            % fails if S is unsatisfiable
  member(As, CS),                 
  findall(R2, ( member(C1,As),      % C is a conseq. of R extended w/generators & ic
                C1 =.. [P1|A],
                atom_concat(P2,'_P',P1),
                C2 =.. [P2|A],
                e_rote_learn(C2,R2) % R2 is the rote learning of C
              ), LC),
  % add learnt positive and contraries to Ri
  aba_rules_append(Ri,LC,Ro).

roLe(Ri,Ep,En, Ro) :-
  lopt(learning_mode(cautious)),
  !,
  % learn positive examples
  asp(Ri, A), 
  compute_conseq(A, [CA]),
  findall(R1, ( member(P,Ep),      % P is a positive example
                \+ member(P,CA),   % P is not a consequence of R
                e_rote_learn(P,R1) % R1 is the rote learning of P
              ), LP),
  % learn contraries (c_alpha)
  asp_star(Ri,Ep,En, S),
  compute_conseq(S, [CS]),          % fails if S is unsatisfiable
  utl_rules(Ri,U),
  findall(R2, ( % C_Alpha is a contrary of an assumption
                member(rule(_,contrary(_,C_Alpha),_),U),
                copy_term(C_Alpha,C_Alpha1),
                C_Alpha1 =.. [C|V],
                % C_AlphaP is the primed version of C_Alpha1
                atom_concat(C,'_P',CP),
                C_AlphaP =.. [CP|V],
                % C_AlphaP is a conseq. of R extended w/generators & ic
                member(C_AlphaP,CS),
                % C_Alpha1 is not a conseq. of R (the member above instantiates the arguments of C_Alpha1)
                \+ member(C_Alpha1,CA),
                % R2 is the rote learning of C 
                e_rote_learn(C_Alpha1,R2) 
              ), LC),
  % add learnt positive and contraries to Ri
  aba_rules_append(Ri,LP,R1), aba_rules_append(R1,LC,Ro),
  % check entailment
  entails(Ro,Ep,En).

% e_rote_learn(+E, -R)
% R is the result of applying the rote learning rule to E
e_rote_learn(E, R) :- 
  E =.. [P|C],
  length(C,L),
  length(V,L),
  H =.. [P|V], % head
  rote_learn_aux(V,C, B), % body
  new_rule(H,B, R),
  write('ert: '), show_rule(R), nl.
%
rote_learn_aux([],[], []).
rote_learn_aux([V|Vs],[C|Cs], [V=C|Bs]) :-
  rote_learn_aux(Vs,Cs, Bs).