% BK
quaker(a).
quaker(b).
quaker(e).

democrat(c).

republican(a).
republican(b).
republican(d).

person(a).
person(b).
person(c).
person(d).
person(e).

pacifist(X) :- quaker(X), normal_quaker(X).

democrat(X) :- person(X), votes_dem(X).
republican(X) :- person(X), votes_rep(X).

#modeh(pacifist(var(t1))).

#modeb(pacifist(var(t1))).
#modeb(quaker(var(t1))).
#modeb(republican(var(t1))).
#modeb(democrat(var(t1))).
#modeb(person(var(t1))).
#modeb(normal_quaker(var(t1))).
#modeb(votes_dem(var(t1))).
#modeb(votes_rep(var(t1))).

#constant(t1, a).
#constant(t1, b).
#constant(t1, c).
#constant(t1, d).
#constant(t1, e).

%E=#pos(E+,E-).
#pos({pacifist(a),pacifist(c),pacifist(e)},
     {pacifist(b),pacifist(d)}).