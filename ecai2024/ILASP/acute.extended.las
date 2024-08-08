%BK
c_alpha_20(A) :- alpha_21(A), a3(A).
c_alpha_21(A) :- alpha_20(A), a4(A).

alpha_20(A) :- not c_alpha_20(A), a4(A).
alpha_21(A) :- not c_alpha_21(A), a3(A).


a3(3).
%
a3(6).
%
a4(9).
a5(9).
a6(9).
%
a3(12).
%
a3(15).
%
a4(18).
a5(18).
a6(18).
%
a4(21).
a5(21).
%
a4(24).
a5(24).
a6(24).
%
a4(27).
a5(27).
a6(27).
%
a4(30).
a5(30).
a6(30).
%
a3(33).
%
a4(36).
a5(36).
a6(36).
%
a4(39).
%
a3(42).
%
a4(45).
%
a4(48).
a5(48).
a6(48).
%
a3(51).
%
a4(54).
a5(54).
a6(54).
%
a4(57).
a5(57).
%
a4(60).
%
a3(63).
a4(63).
a6(63).
%
a3(66).
a4(66).
a6(66).
%
a3(69).
a4(69).
a6(69).
%
a2(72).
a3(72).
a4(72).
a5(72).
a6(72).
%
%
a3(78).
a4(78).
a6(78).
%
%
a2(84).
a3(84).
a4(84).
a5(84).
a6(84).
%
%
a2(90).
a3(90).
a4(90).
a5(90).
a6(90).
%
a2(93).
a3(93).
a4(93).
a5(93).
a6(93).
%
a2(96).
a3(96).
a5(96).
%
a2(99).
a3(99).
a4(99).
a5(99).
%
a2(102).
a3(102).
a4(102).
a5(102).
a6(102).
%
a3(105).
a4(105).
a6(105).
%
%
a2(111).
a3(111).
a4(111).
a5(111).
a6(111).
%
a3(114).
a4(114).
a6(114).
%
%
a3(120).
a4(120).
a6(120).
%
% no. positive ex.: 21
% no. negative ex.: 19
% query: 
% aba_asp(acute.pp.csv.pl,[acute(9),acute(18),acute(21),acute(24),acute(27),acute(30),acute(36),acute(39),acute(45),acute(48),acute(54),acute(57),acute(60),acute(66),acute(72),acute(84),acute(90),acute(93),acute(99),acute(102),acute(111)],[acute(3),acute(6),acute(12),acute(15),acute(33),acute(42),acute(51),acute(63),acute(69),acute(75),acute(78),acute(81),acute(87),acute(96),acute(105),acute(108),acute(114),acute(117),acute(120)]).

#modeh(acute(var(t1))).
#modeb(alpha_20(var(t1))).
#modeb(c_alpha_20(var(t1))).
#modeb(alpha_21(var(t1))).
#modeb(c_alpha_21(var(t1))).
#modeb(a2(var(t1))).
#modeb(a3(var(t1))).
#modeb(a4(var(t1))).
#modeb(a5(var(t1))).
#modeb(a6(var(t1))).
#modeb(acute(var(t1))).

#constant(t1, 3).
#constant(t1, 6).
#constant(t1, 9).
#constant(t1, 12).
#constant(t1, 15).
#constant(t1, 18).
#constant(t1, 21).
#constant(t1, 24).
#constant(t1, 27).
#constant(t1, 30).
#constant(t1, 33).
#constant(t1, 36).
#constant(t1, 39).
#constant(t1, 42).
#constant(t1, 45).
#constant(t1, 48).
#constant(t1, 51).
#constant(t1, 54).
#constant(t1, 57).
#constant(t1, 60).
#constant(t1, 63).
#constant(t1, 66).
#constant(t1, 69).
#constant(t1, 72).
#constant(t1, 75).
#constant(t1, 78).
#constant(t1, 81).
#constant(t1, 84).
#constant(t1, 87).
#constant(t1, 90).
#constant(t1, 93).
#constant(t1, 96).
#constant(t1, 99).
#constant(t1, 102).
#constant(t1, 105).
#constant(t1, 108).
#constant(t1, 111).
#constant(t1, 114).
#constant(t1, 117).
#constant(t1, 120).


%E=#pos(E+,E-).
#pos({acute(9),acute(18),acute(21),acute(24),acute(27),acute(30),acute(36),acute(39),acute(45),acute(48),
      acute(54),acute(57),acute(60),acute(66),acute(72),acute(84),acute(90),acute(93),acute(99),acute(102),
      acute(111)},
     {acute(3),acute(6),acute(12),acute(15),acute(33),acute(42),acute(51),acute(63),acute(69),acute(75),
      acute(78),acute(81),acute(87),acute(96),acute(105),acute(108),acute(114),acute(117),acute(120)}).
