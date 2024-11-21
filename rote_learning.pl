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

% Rote Learning procedures

:- use_module('asp_utils').
:- use_module('asp_engine').

roLe(Ri,Ep,En, RL,Ro) :-
  bk_preds(Ps),
  findall(F/N, ( member(E,Ep), functor(E,F,N) ), EPs),
  sort(EPs,SEPs),
  member(P,SEPs),
  member(P,Ps),
  !,
  roLe_aux(Ri,Ep,En, RL,Ro).
roLe(Ri,Ep,_En, LC,Ro) :- 
  findall(R, ( member(E,Ep), e_rote_learn(E,R) ), LC),
  aba_ni_rules_append(Ri,LC,Ro).

% roLe(+Ri,+Ep,+En, -RL,-Ro)
% rote learning of Ep and En
roLe_aux(Ri,Ep,En, LC,Ro) :-
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
  aba_ni_rules_append(Ri,LC,Ro).

roLe_aux(Ri,Ep,En, RL,Ro) :-
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
  aba_cnts(Ri,U),
  findall(R2, ( % C_Alpha is a contrary of an assumption
                member(contrary(_,C_Alpha),U),
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
  aba_ni_rules_append(Ri,LP,R1), aba_ni_rules_append(R1,LC,Ro),
  % check entailment
  entails(Ro,Ep,En),
  append(LP,LC,RL).

% e_rote_learn(+E, -R)
e_rote_learn(E, R) :- 
  new_rule(E,[], R),
  write('ert: '), show_rule(R), nl.