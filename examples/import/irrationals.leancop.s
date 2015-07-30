% SZS status Theorem for simple.leancop
%Start of proof for simple.leancop
%-----------------------------------------------------
fof(f, conjecture, ? [_13346, _13349] : (~ i(exp(_13346, _13349)) & i(_13346) & i(_13349)), file('simple.leancop', f)).
fof(a, axiom, i(sr2), file('simple.leancop', a)).
fof(b, axiom, ~ i(two), file('simple.leancop', b)).
fof(c, axiom, times(sr2, sr2) = two, file('simple.leancop', c)).
fof(d, axiom, ! [_13671, _13674] : exp(exp(_13671, _13674), _13689) = exp(_13671, times(_13674, _13689)), file('simple.leancop', d)).
fof(e, axiom, ! [_13850] : exp(_13850, two) = times(_13850, _13850), file('simple.leancop', e)).

cnf(1, plain, [-(i(exp(_7203, _7257))), i(_7203), i(_7257)], clausify(f)).
cnf(2, plain, [-(i(sr2))], clausify(a)).
cnf(3, plain, [i(two)], clausify(b)).
cnf(4, plain, [-(times(sr2, sr2) = two)], clausify(c)).
cnf(5, plain, [-(exp(exp(_6497, _6548), _6564) = exp(_6497, times(_6548, _6564)))], clausify(d)).
cnf(6, plain, [-(exp(_6883, two) = times(_6883, _6883))], clausify(e)).
cnf(7, plain, [-(exp(_4798, _4931) = exp(_4865, _4996)), _4798 = _4865, _4931 = _4996], theory(equality)).
cnf(8, plain, [-(i(_4503)), _4454 = _4503, i(_4454)], theory(equality)).
cnf(9, plain, [-(_3556 = _3556)], theory(equality)).

cnf('1',plain,[i(two)],start(3)).
cnf('1.1',plain,[-(i(two)), times(sr2, sr2) = two, i(times(sr2, sr2))],extension(8,bind([[_4503, _4454], [two, times(sr2, sr2)]]))).
cnf('1.1.1',plain,[-(times(sr2, sr2) = two)],extension(4)).
cnf('1.1.2',plain,[-(i(times(sr2, sr2))), exp(sr2, two) = times(sr2, sr2), i(exp(sr2, two))],extension(8,bind([[_4503, _4454], [times(sr2, sr2), exp(sr2, two)]]))).
cnf('1.1.2.1',plain,[-(exp(sr2, two) = times(sr2, sr2))],extension(6,bind([[_6883], [sr2]]))).
cnf('1.1.2.2',plain,[-(i(exp(sr2, two))), exp(sr2, times(sr2, sr2)) = exp(sr2, two), i(exp(sr2, times(sr2, sr2)))],extension(8,bind([[_4503, _4454], [exp(sr2, two), exp(sr2, times(sr2, sr2))]]))).
cnf('1.1.2.2.1',plain,[-(exp(sr2, times(sr2, sr2)) = exp(sr2, two)), sr2 = sr2, times(sr2, sr2) = two],extension(7,bind([[_4798, _4865, _4931, _4996], [sr2, sr2, times(sr2, sr2), two]]))).
cnf('1.1.2.2.1.1',plain,[-(sr2 = sr2)],extension(9,bind([[_3556], [sr2]]))).
cnf('1.1.2.2.1.2',plain,[-(times(sr2, sr2) = two)],extension(4)).
cnf('1.1.2.2.2',plain,[-(i(exp(sr2, times(sr2, sr2)))), exp(exp(sr2, sr2), sr2) = exp(sr2, times(sr2, sr2)), i(exp(exp(sr2, sr2), sr2))],extension(8,bind([[_4503, _4454], [exp(sr2, times(sr2, sr2)), exp(exp(sr2, sr2), sr2)]]))).
cnf('1.1.2.2.2.1',plain,[-(exp(exp(sr2, sr2), sr2) = exp(sr2, times(sr2, sr2)))],extension(5,bind([[_6497, _6548, _6564], [sr2, sr2, sr2]]))).
cnf('1.1.2.2.2.2',plain,[-(i(exp(exp(sr2, sr2), sr2))), i(exp(sr2, sr2)), i(sr2)],extension(1,bind([[_7203, _7257], [exp(sr2, sr2), sr2]]))).
cnf('1.1.2.2.2.2.1',plain,[-(i(exp(sr2, sr2))), i(sr2), i(sr2)],extension(1,bind([[_7203, _7257], [sr2, sr2]]))).
cnf('1.1.2.2.2.2.1.1',plain,[-(i(sr2))],extension(2)).
cnf('1.1.2.2.2.2.1.2',plain,[-(i(sr2))],extension(2)).
cnf('1.1.2.2.2.2.2',plain,[-(i(sr2))],extension(2)).
%-----------------------------------------------------
%End of proof for simple.leancop
