% BK
quaker(a).
quaker(b).

republican(a).
republican(b).

person(a).
person(b).

#modeh(pacifist(var(t1))).

#modeb(pacifist(var(t1))).
#modeb(quaker(var(t1))).
#modeb(republican(var(t1))).
#modeb(person(var(t1))).

#constant(t1, a).
#constant(t1, b).

%E=#pos(E+,E-).
#pos({pacifist(a)},
     {pacifist(b)}).