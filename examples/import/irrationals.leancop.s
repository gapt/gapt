fof(f, conjecture, ? [_13459, _13462] : (~ i(exp(_13459, _13462)) & i(_13459) & i(_13462)), file('samples/irrationals.p', f)).
fof(a, axiom, i(sr2), file('samples/irrationals.p', a)).
fof(b, axiom, ~ i(two), file('samples/irrationals.p', b)).
fof(c, axiom, times(sr2, sr2) = two, file('samples/irrationals.p', c)).
fof(d, axiom, ! [_13784, _13787, _13790] : exp(exp(_13784, _13787), _13790) = exp(_13784, times(_13787, _13790)), file('samples/irrationals.p', d)).
fof(e, axiom, ! [_13973] : exp(_13973, two) = times(_13973, _13973), file('samples/irrationals.p', e)).

cnf(1, plain, [-(i(exp(_7304, _7358))), i(_7304), i(_7358)], clausify(f)).
cnf(2, plain, [-(i(sr2))], clausify(a)).
cnf(3, plain, [i(two)], clausify(b)).
cnf(4, plain, [-(times(sr2, sr2) = two)], clausify(c)).
cnf(5, plain, [-(exp(exp(_6527, _6583), _6638) = exp(_6527, times(_6583, _6638)))], clausify(d)).
cnf(6, plain, [-(exp(_6984, two) = times(_6984, _6984))], clausify(e)).
cnf(7, plain, [-(exp(_4828, _4961) = exp(_4895, _5026)), _4828 = _4895, _4961 = _5026], theory(equality)).
cnf(8, plain, [-(i(_4533)), _4484 = _4533, i(_4484)], theory(equality)).
cnf(9, plain, [-(_3586 = _3586)], theory(equality)).

cnf('1',plain,[i(two)],start(3)).
cnf('1.1',plain,[-(i(two)), times(sr2, sr2) = two, i(times(sr2, sr2))],extension(8,bind([[_4533, _4484], [two, times(sr2, sr2)]]))).
cnf('1.1.1',plain,[-(times(sr2, sr2) = two)],extension(4)).
cnf('1.1.2',plain,[-(i(times(sr2, sr2))), exp(sr2, two) = times(sr2, sr2), i(exp(sr2, two))],extension(8,bind([[_4533, _4484], [times(sr2, sr2), exp(sr2, two)]]))).
cnf('1.1.2.1',plain,[-(exp(sr2, two) = times(sr2, sr2))],extension(6,bind([[_6984], [sr2]]))).
cnf('1.1.2.2',plain,[-(i(exp(sr2, two))), exp(sr2, times(sr2, sr2)) = exp(sr2, two), i(exp(sr2, times(sr2, sr2)))],extension(8,bind([[_4533, _4484], [exp(sr2, two), exp(sr2, times(sr2, sr2))]]))).
cnf('1.1.2.2.1',plain,[-(exp(sr2, times(sr2, sr2)) = exp(sr2, two)), sr2 = sr2, times(sr2, sr2) = two],extension(7,bind([[_4828, _4895, _4961, _5026], [sr2, sr2, times(sr2, sr2), two]]))).
cnf('1.1.2.2.1.1',plain,[-(sr2 = sr2)],extension(9,bind([[_3586], [sr2]]))).
cnf('1.1.2.2.1.2',plain,[-(times(sr2, sr2) = two)],extension(4)).
cnf('1.1.2.2.2',plain,[-(i(exp(sr2, times(sr2, sr2)))), exp(exp(sr2, sr2), sr2) = exp(sr2, times(sr2, sr2)), i(exp(exp(sr2, sr2), sr2))],extension(8,bind([[_4533, _4484], [exp(sr2, times(sr2, sr2)), exp(exp(sr2, sr2), sr2)]]))).
cnf('1.1.2.2.2.1',plain,[-(exp(exp(sr2, sr2), sr2) = exp(sr2, times(sr2, sr2)))],extension(5,bind([[_6527, _6583, _6638], [sr2, sr2, sr2]]))).
cnf('1.1.2.2.2.2',plain,[-(i(exp(exp(sr2, sr2), sr2))), i(exp(sr2, sr2)), i(sr2)],extension(1,bind([[_7304, _7358], [exp(sr2, sr2), sr2]]))).
cnf('1.1.2.2.2.2.1',plain,[-(i(exp(sr2, sr2))), i(sr2), i(sr2)],extension(1,bind([[_7304, _7358], [sr2, sr2]]))).
cnf('1.1.2.2.2.2.1.1',plain,[-(i(sr2))],extension(2)).
cnf('1.1.2.2.2.2.1.2',plain,[-(i(sr2))],extension(2)).
cnf('1.1.2.2.2.2.2',plain,[-(i(sr2))],extension(2)).
