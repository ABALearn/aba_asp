% BK
pays_taxes_in_uk(X) :- person(X), nonexempt(X).

person(a).
person(b).
person(c).
person(d).

low_income(a).
high_income(b).
high_income(c).
high_income(d).

resident(a,uk).
resident(b,uk).
resident(c,fr).
resident(d,xx).

country(uk).
country(fr).
country(xx).

tax_agreement(fr,uk).


#modeh(pays_taxes_in_uk(var(t1))).

#modeb(pays_taxes_in_uk(var(t1))).
#modeb(person(var(t1))).
#modeb(nonexempt(var(t1))).
#modeb(low_income(var(t1))).
#modeb(high_income(var(t1))).
#modeb(resident(var(t1),var(t2))).
#modeb(country(var(t2))).
#modeb(tax_agreement(var(t2),var(t2))).

#constant(t1, a).
#constant(t1, b).
#constant(t1, c).
#constant(t1, d).

#constant(t2, uk).
#constant(t2, fr).
#constant(t2, xx).

%E=#pos(E+,E-).
#pos({pays_taxes_in_uk(b),pays_taxes_in_uk(d)},
     {pays_taxes_in_uk(a),pays_taxes_in_uk(c)}).

%emanuele@Emanueles-Air ILASP-4.4.0-macOS-M1 % ./ILASP --version=2 ecai/tax_law_2.bk.las 
%pays_taxes_in_uk(V1) :- high_income(V1); tax_agreement(V2,V3); not resident(V1,V2).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Pre-processing                          : 0.033s
%% Hypothesis Space Generation             : 0.798s
%% Counterexample search                   : 0.001s
%%   - CDOEs                               : 0s
%%   - CDPIs                               : 0.001s
%% Hypothesis Search                       : 0.115s
%% Total                                   : 0.952s
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%